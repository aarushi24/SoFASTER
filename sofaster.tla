------------------------------ MODULE sofaster ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Source, Target, Zookeeper, SourceSessions, TargetSessions, NULL, PrepareToSample, Sampling, PrepareForTransfer, TransferingOwnership, WaitForPending, MoveDataToTarget, PrepareForMigration, ReceivingData, WaitForCheckpoint, Checkpointing, 2PCCommit, 2PCPrepare, 2PCAbort, SourceKeys, TargetKeys, KeysToMigrate 

Servers == {Source, Target}

Ownership(kvset, view) == [kv \in kvset |-> view]

SetServerState(ServerElements) == [s \in ServerElements |-> NULL]

SetViewNumber(ServerElements) == [s \in ServerElements |-> 0]

SetServerVote == [s \in Servers |-> FALSE]

(*--algorithm sofaster
variables
    \* Spec state
    StateInit = FALSE,
    ServerState = SetServerState(SourceSessions \union TargetSessions),
    TransferComplete = FALSE,
    SourceAbort = FALSE,
    TargetAbort = FALSE,
    \* Server state 
    SViewNumber = SetViewNumber(SourceSessions),
    TViewNumber = SetViewNumber(TargetSessions),
    \* Protocol RPCs
    PrepForTransferRPC = FALSE,
    UpdateSourceOwnership = FALSE,
    UpdateTargetOwnership = FALSE,
    TakeOwnershipRPC = FALSE,
    TransferCompleteRPC = FALSE,
    ACKTransferCompleteRPC = FALSE,
    SourceACK = NULL,
    TargetACK = NULL,
    \* Public Zookeeper State and RPCs
    AllServerRanges = SetServerState(Servers),
    AllServerViewNumbers = SetViewNumber(Servers),
    MigrationServers = <<>>,
    MigrationViewNumbers = <<>>,
    MigrationRange = NULL,
    ServerVote = SetServerVote,
    Start2PC = FALSE,    
    SourcePrepare2PC = FALSE,
    TargetPrepare2PC = FALSE,
    Decision2PC = FALSE;
    
define \* invariants
    \* Migration is atomic - source, target and coordinator are in agreement about result of migration
    MigrationSuccess == (\E s \in SourceSessions: ServerState[s] = 2PCCommit /\ \E t \in TargetSessions: ServerState[t] = 2PCCommit) ~> <>[](ServerVote[Source] /\ ServerVote[Target])
    MigrationFailure == (\E s \in SourceSessions: ServerState[s] = 2PCAbort /\ \E t \in TargetSessions: ServerState[t] = 2PCAbort) ~> <>[] (~ServerVote[Source] /\ ~ServerVote[Target])
    \* Views and their actions are linearizable
    \* No server can process requests it doesn't own
    \* Each client eventually gets the correct server
    \* No key is lost - before migration the source owns KeysToMigrate and after KeysToMigrate is owned by either owned by Source or Target
    \* No key has overlapping ownership - KeysToMigrate are never owned by both Source and Target
end define;

macro UpdateZookeeperState()
  begin
    with s \in Servers do
        if ~ServerVote[s] then
            AllServerRanges[Head(MigrationServers)] := AllServerRanges[Head(MigrationServers)] \union {MigrationRange} 
            || AllServerRanges[Head(Tail(MigrationServers))] := AllServerRanges[Head(Tail(MigrationServers))] \ {MigrationRange};
            AllServerViewNumbers[Head(MigrationServers)] := Head(MigrationViewNumbers) 
            || AllServerViewNumbers[Head(Tail(MigrationServers))] := Head(Tail(MigrationViewNumbers));
        end if;
    end with;
end macro;

macro CheckZookeeper(CurKV, ServerNode, CViewNumber)
  begin
    if CurKV \in AllServerRanges[Source] then
        ServerNode[CurKV] := Source;
        CViewNumber[CurKV] := AllServerViewNumbers[Source];
    elsif CurKV \in AllServerRanges[Target] then
        ServerNode[CurKV] := Target;
        CViewNumber[CurKV] := AllServerViewNumbers[Target];
    end if;
end macro;

\* Not at a per session level!!!
procedure MakeRequest(Server, KVRange, ViewNumber, OpComp)
  begin
    CheckServerRange:
        if ViewNumber /= AllServerViewNumbers[Server] \/ KVRange \notin AllServerRanges[Server] then 
            OpComp := FALSE;
        else
            OpComp := TRUE;
        end if;
    ProcReturn:
        return;
end procedure;

\* All local view numbers start at the last CPR checkpoint (0)

\* remove fair to check crashed states
fair process SourceProcess \in SourceSessions
    variable SKVRanges = {SourceKeys, KeysToMigrate}, SKVOwner = Ownership(SKVRanges, 0);
  begin
    InitMigrationSource: 
        \* Shared latch on mutable records 
        ServerState[self] := PrepareToSample;
    SampleRecords:
        \* Copy hot records to the tail
        \* Exclusive latch on records in the mutable region
        ServerState[self] := Sampling;
    ViewChange:
        \* Change view from v to v+1
        ServerState[self] := PrepareForTransfer;
        SViewNumber[self] := SViewNumber[self] + 1;
        SKVOwner := Ownership(SKVRanges \ {KeysToMigrate}, SViewNumber[self]);
        if ~PrepForTransferRPC then
            \* Inform target about migrating ranges
            MigrationRange := KeysToMigrate;
            PrepForTransferRPC := TRUE;
        end if;
    SetZookeerperStateSource:
        if ~UpdateSourceOwnership then
            UpdateSourceOwnership := TRUE;    
            with sessions \in SourceSessions \ {self} do
                    await ServerState[sessions] = PrepareForTransfer
            end with;
            MigrationServers := Append(MigrationServers, Source);
            MigrationViewNumbers := Append(MigrationViewNumbers, SViewNumber[self]);    
        end if;
    TransferOwnership:
        ServerState[self] := TransferingOwnership;
    CompleteRequests:
        \* Wait for pending requests to complete
        ServerState[self] := WaitForPending;
        if ~TakeOwnershipRPC then
            with sessions \in SourceSessions \ {self} do
                await ServerState[sessions] = TransferingOwnership
            end with;
            TakeOwnershipRPC := TRUE;
        end if;
    MoveData:
        \* Send records
        SKVRanges := SKVRanges \ {KeysToMigrate};
        ServerState[self] := MoveDataToTarget;
        if ~TransferComplete then
            with sessions \in SourceSessions \ {self} do
                await ServerState[sessions] = WaitForPending
            end with;
            TransferComplete := TRUE;
        end if;
    WaitForDecisionSource: 
        await SourceAbort \/ Decision2PC;
        if SourceAbort then
            ServerState[self] := 2PCAbort;
        else
            if ServerVote[Source] /\ ServerVote[Target] then
                ServerState[self] := 2PCCommit;
            else 
                ServerState[self] := 2PCAbort;
            end if;
        end if;
    (*UpdateStateSource: \* In case of recovery
        if ServerState[self] = 2PCAbort then
            SKVRanges := SKVRanges \union {KeysToMigrate};*)
end process;

fair process SourceServer = Source
  begin
    \* Checkpointing
    CompleteMigration:
        await TransferComplete;
        with s \in SourceSessions do
            ServerState[s] := WaitForCheckpoint
        end with;
        TransferCompleteRPC := TRUE;
    StartCommit:
        await ACKTransferCompleteRPC;
        Start2PC := TRUE;
    \* 2PC
    WaitForPrepare:
        await SourcePrepare2PC;
        either 
            SourceACK := TRUE;
            with s \in SourceSessions do 
                ServerState[s] := 2PCPrepare
            end with;
        or
            SourceACK := FALSE;
            SourceAbort := TRUE;
        end either;
end process;

fair process TargetProcess \in TargetSessions
    variable TKVRanges = {TargetKeys}, TKVOwner = Ownership(TKVRanges, 0);
  begin
    InitMigrationTarget:        
        await PrepForTransferRPC;
        \* TODO: Buffer requests for migrating ranges
        ServerState[self] := PrepareForMigration;
        TKVRanges := TKVRanges \union {MigrationRange};
        TViewNumber[self] := TViewNumber[self] + 1;
        TKVOwner := Ownership(TKVRanges, TViewNumber[self]);
    SetZookeerperStateTarget:
        await UpdateSourceOwnership;
        if ~UpdateTargetOwnership then
            UpdateTargetOwnership := TRUE;    
            with sessions \in TargetSessions \ {self} do
                    await ServerState[sessions] = PrepareForMigration
            end with;
            MigrationServers := Append(MigrationServers, Target);
            MigrationViewNumbers := Append(MigrationViewNumbers, TViewNumber[self]);    
        end if;
    TakeOwnership:
        await TakeOwnershipRPC;
        ServerState[self] := ReceivingData;
    WaitForDecisionTarget: \* In case of recovery
        await TargetAbort \/ Decision2PC;
        if TargetAbort then
            ServerState[self] := 2PCAbort;
        else
            if ServerVote[Source] /\ ServerVote[Target] then
                ServerState[self] := 2PCCommit;
            else 
                ServerState[self] := 2PCAbort;
            end if;
        end if;
end process;

fair process TargetServer = Target
  begin
    \* Checkpointing
    StartCheckpointing:
        await TransferCompleteRPC;
        with s \in TargetSessions do
            ServerState[s] := Checkpointing
        end with;
        ACKTransferCompleteRPC := TRUE;
    \* 2PC - need to check if other server has voted?
    WaitFor2PC:
        await TargetPrepare2PC;
        either 
            TargetACK := TRUE;
            with s \in TargetSessions do
                ServerState[s] := 2PCPrepare
            end with;
        or
            TargetACK := FALSE;
            TargetAbort := TRUE;
        end either;
end process;

fair process CoordinatorProcess = Zookeeper
  begin
    InitState:
        AllServerRanges[Source] := {SourceKeys, KeysToMigrate} || AllServerRanges[Target] := {TargetKeys};
        StateInit := TRUE;
    SetMigrationSourceState:
        await UpdateSourceOwnership;
        AllServerRanges[Head(MigrationServers)] := AllServerRanges[Head(MigrationServers)] \ {MigrationRange};
        AllServerViewNumbers[Head(MigrationServers)] := Head(MigrationViewNumbers);
    SetMigrationTargetState:
        await UpdateTargetOwnership;
        AllServerRanges[Head(Tail(MigrationServers))] := AllServerRanges[Head(Tail(MigrationServers))] \union {MigrationRange};
        AllServerViewNumbers[Head(Tail(MigrationServers))] := Head(Tail(MigrationViewNumbers));
    Init2PC:
        await Start2PC;
        SourcePrepare2PC := TRUE;
        TargetPrepare2PC := TRUE;
    CompletionDecision:
        await SourceACK \in BOOLEAN \/ TargetACK \in BOOLEAN;
        either 
            await SourceACK \in BOOLEAN /\ TargetACK \in BOOLEAN;
            if ~SourceACK \/ ~TargetACK then
                ServerVote[Source] := FALSE || ServerVote[Target] := FALSE;
            elsif SourceACK /\ TargetACK then
                ServerVote[Source] := TRUE || ServerVote[Target] := TRUE;
            end if;
        or
            \* another server aborts 
            if SourceACK /= TRUE \/ TargetACK /= TRUE then
                ServerVote[Source] := FALSE || ServerVote[Target] := FALSE;
            else
                await SourceACK \in BOOLEAN /\ TargetACK \in BOOLEAN;
                if ~SourceACK \/ ~TargetACK then
                    ServerVote[Source] := FALSE || ServerVote[Target] := FALSE;
                elsif SourceACK /\ TargetACK then
                    ServerVote[Source] := TRUE || ServerVote[Target] := TRUE;
                end if;
            end if;
        end either;
    CommitMigration:
        Decision2PC := TRUE; 
        UpdateZookeeperState();
end process;

fair process Clients = "Client"
    variable KVRanges = {SourceKeys, KeysToMigrate, TargetKeys}, CViewNumbers = SetViewNumber(KVRanges), ServerNode = [s \in KVRanges |-> Source], OpCompleted = FALSE, CurKV = NULL;
  begin 
    InitClient:
        await StateInit;
    ServerInteraction:
        while ~Decision2PC do
            RequestOp:
                with kv \in KVRanges do
                    CurKV := kv;
                    call MakeRequest(ServerNode[kv], kv, CViewNumbers[kv], OpCompleted);
                end with;
                UpdateClientState:
                    if ~OpCompleted then
                        CheckZookeeper(CurKV, ServerNode, CViewNumbers);
                    end if;
        end while;
end process; 

end algorithm; *)

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES StateInit, ServerState, TransferComplete, SourceAbort, TargetAbort, 
          SViewNumber, TViewNumber, PrepForTransferRPC, UpdateSourceOwnership, 
          UpdateTargetOwnership, TakeOwnershipRPC, TransferCompleteRPC, 
          ACKTransferCompleteRPC, SourceACK, TargetACK, AllServerRanges, 
          AllServerViewNumbers, MigrationServers, MigrationViewNumbers, 
          MigrationRange, ServerVote, Start2PC, SourcePrepare2PC, 
          TargetPrepare2PC, Decision2PC, pc, stack

(* define statement *)
MigrationSuccess == (\E s \in SourceSessions: ServerState[s] = 2PCCommit /\ \E t \in TargetSessions: ServerState[t] = 2PCCommit) ~> <>[](ServerVote[Source] /\ ServerVote[Target])
MigrationFailure == (\E s \in SourceSessions: ServerState[s] = 2PCAbort /\ \E t \in TargetSessions: ServerState[t] = 2PCAbort) ~> <>[] (~ServerVote[Source] /\ ~ServerVote[Target])

VARIABLES Server, KVRange, ViewNumber, OpComp, SKVRanges, SKVOwner, TKVRanges, 
          TKVOwner, KVRanges, CViewNumbers, ServerNode, OpCompleted, CurKV

vars == << StateInit, ServerState, TransferComplete, SourceAbort, TargetAbort, 
           SViewNumber, TViewNumber, PrepForTransferRPC, 
           UpdateSourceOwnership, UpdateTargetOwnership, TakeOwnershipRPC, 
           TransferCompleteRPC, ACKTransferCompleteRPC, SourceACK, TargetACK, 
           AllServerRanges, AllServerViewNumbers, MigrationServers, 
           MigrationViewNumbers, MigrationRange, ServerVote, Start2PC, 
           SourcePrepare2PC, TargetPrepare2PC, Decision2PC, pc, stack, Server, 
           KVRange, ViewNumber, OpComp, SKVRanges, SKVOwner, TKVRanges, 
           TKVOwner, KVRanges, CViewNumbers, ServerNode, OpCompleted, CurKV
        >>

ProcSet == (SourceSessions) \cup {Source} \cup (TargetSessions) \cup {Target} \cup {Zookeeper} \cup {"Client"}

Init == (* Global variables *)
        /\ StateInit = FALSE
        /\ ServerState = SetServerState(SourceSessions \union TargetSessions)
        /\ TransferComplete = FALSE
        /\ SourceAbort = FALSE
        /\ TargetAbort = FALSE
        /\ SViewNumber = SetViewNumber(SourceSessions)
        /\ TViewNumber = SetViewNumber(TargetSessions)
        /\ PrepForTransferRPC = FALSE
        /\ UpdateSourceOwnership = FALSE
        /\ UpdateTargetOwnership = FALSE
        /\ TakeOwnershipRPC = FALSE
        /\ TransferCompleteRPC = FALSE
        /\ ACKTransferCompleteRPC = FALSE
        /\ SourceACK = NULL
        /\ TargetACK = NULL
        /\ AllServerRanges = SetServerState(Servers)
        /\ AllServerViewNumbers = SetViewNumber(Servers)
        /\ MigrationServers = <<>>
        /\ MigrationViewNumbers = <<>>
        /\ MigrationRange = NULL
        /\ ServerVote = SetServerVote
        /\ Start2PC = FALSE
        /\ SourcePrepare2PC = FALSE
        /\ TargetPrepare2PC = FALSE
        /\ Decision2PC = FALSE
        (* Procedure MakeRequest *)
        /\ Server = [ self \in ProcSet |-> defaultInitValue]
        /\ KVRange = [ self \in ProcSet |-> defaultInitValue]
        /\ ViewNumber = [ self \in ProcSet |-> defaultInitValue]
        /\ OpComp = [ self \in ProcSet |-> defaultInitValue]
        (* Process SourceProcess *)
        /\ SKVRanges = [self \in SourceSessions |-> {SourceKeys, KeysToMigrate}]
        /\ SKVOwner = [self \in SourceSessions |-> Ownership(SKVRanges[self], 0)]
        (* Process TargetProcess *)
        /\ TKVRanges = [self \in TargetSessions |-> {TargetKeys}]
        /\ TKVOwner = [self \in TargetSessions |-> Ownership(TKVRanges[self], 0)]
        (* Process Clients *)
        /\ KVRanges = {SourceKeys, KeysToMigrate, TargetKeys}
        /\ CViewNumbers = SetViewNumber(KVRanges)
        /\ ServerNode = [s \in KVRanges |-> Source]
        /\ OpCompleted = FALSE
        /\ CurKV = NULL
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in SourceSessions -> "InitMigrationSource"
                                        [] self = Source -> "CompleteMigration"
                                        [] self \in TargetSessions -> "InitMigrationTarget"
                                        [] self = Target -> "StartCheckpointing"
                                        [] self = Zookeeper -> "InitState"
                                        [] self = "Client" -> "InitClient"]

CheckServerRange(self) == /\ pc[self] = "CheckServerRange"
                          /\ IF ViewNumber[self] /= AllServerViewNumbers[Server[self]] \/ KVRange[self] \notin AllServerRanges[Server[self]]
                                THEN /\ OpComp' = [OpComp EXCEPT ![self] = FALSE]
                                ELSE /\ OpComp' = [OpComp EXCEPT ![self] = TRUE]
                          /\ pc' = [pc EXCEPT ![self] = "ProcReturn"]
                          /\ UNCHANGED << StateInit, ServerState, 
                                          TransferComplete, SourceAbort, 
                                          TargetAbort, SViewNumber, 
                                          TViewNumber, PrepForTransferRPC, 
                                          UpdateSourceOwnership, 
                                          UpdateTargetOwnership, 
                                          TakeOwnershipRPC, 
                                          TransferCompleteRPC, 
                                          ACKTransferCompleteRPC, SourceACK, 
                                          TargetACK, AllServerRanges, 
                                          AllServerViewNumbers, 
                                          MigrationServers, 
                                          MigrationViewNumbers, MigrationRange, 
                                          ServerVote, Start2PC, 
                                          SourcePrepare2PC, TargetPrepare2PC, 
                                          Decision2PC, stack, Server, KVRange, 
                                          ViewNumber, SKVRanges, SKVOwner, 
                                          TKVRanges, TKVOwner, KVRanges, 
                                          CViewNumbers, ServerNode, 
                                          OpCompleted, CurKV >>

ProcReturn(self) == /\ pc[self] = "ProcReturn"
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ Server' = [Server EXCEPT ![self] = Head(stack[self]).Server]
                    /\ KVRange' = [KVRange EXCEPT ![self] = Head(stack[self]).KVRange]
                    /\ ViewNumber' = [ViewNumber EXCEPT ![self] = Head(stack[self]).ViewNumber]
                    /\ OpComp' = [OpComp EXCEPT ![self] = Head(stack[self]).OpComp]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << StateInit, ServerState, TransferComplete, 
                                    SourceAbort, TargetAbort, SViewNumber, 
                                    TViewNumber, PrepForTransferRPC, 
                                    UpdateSourceOwnership, 
                                    UpdateTargetOwnership, TakeOwnershipRPC, 
                                    TransferCompleteRPC, 
                                    ACKTransferCompleteRPC, SourceACK, 
                                    TargetACK, AllServerRanges, 
                                    AllServerViewNumbers, MigrationServers, 
                                    MigrationViewNumbers, MigrationRange, 
                                    ServerVote, Start2PC, SourcePrepare2PC, 
                                    TargetPrepare2PC, Decision2PC, SKVRanges, 
                                    SKVOwner, TKVRanges, TKVOwner, KVRanges, 
                                    CViewNumbers, ServerNode, OpCompleted, 
                                    CurKV >>

MakeRequest(self) == CheckServerRange(self) \/ ProcReturn(self)

InitMigrationSource(self) == /\ pc[self] = "InitMigrationSource"
                             /\ ServerState' = [ServerState EXCEPT ![self] = PrepareToSample]
                             /\ pc' = [pc EXCEPT ![self] = "SampleRecords"]
                             /\ UNCHANGED << StateInit, TransferComplete, 
                                             SourceAbort, TargetAbort, 
                                             SViewNumber, TViewNumber, 
                                             PrepForTransferRPC, 
                                             UpdateSourceOwnership, 
                                             UpdateTargetOwnership, 
                                             TakeOwnershipRPC, 
                                             TransferCompleteRPC, 
                                             ACKTransferCompleteRPC, SourceACK, 
                                             TargetACK, AllServerRanges, 
                                             AllServerViewNumbers, 
                                             MigrationServers, 
                                             MigrationViewNumbers, 
                                             MigrationRange, ServerVote, 
                                             Start2PC, SourcePrepare2PC, 
                                             TargetPrepare2PC, Decision2PC, 
                                             stack, Server, KVRange, 
                                             ViewNumber, OpComp, SKVRanges, 
                                             SKVOwner, TKVRanges, TKVOwner, 
                                             KVRanges, CViewNumbers, 
                                             ServerNode, OpCompleted, CurKV >>

SampleRecords(self) == /\ pc[self] = "SampleRecords"
                       /\ ServerState' = [ServerState EXCEPT ![self] = Sampling]
                       /\ pc' = [pc EXCEPT ![self] = "ViewChange"]
                       /\ UNCHANGED << StateInit, TransferComplete, 
                                       SourceAbort, TargetAbort, SViewNumber, 
                                       TViewNumber, PrepForTransferRPC, 
                                       UpdateSourceOwnership, 
                                       UpdateTargetOwnership, TakeOwnershipRPC, 
                                       TransferCompleteRPC, 
                                       ACKTransferCompleteRPC, SourceACK, 
                                       TargetACK, AllServerRanges, 
                                       AllServerViewNumbers, MigrationServers, 
                                       MigrationViewNumbers, MigrationRange, 
                                       ServerVote, Start2PC, SourcePrepare2PC, 
                                       TargetPrepare2PC, Decision2PC, stack, 
                                       Server, KVRange, ViewNumber, OpComp, 
                                       SKVRanges, SKVOwner, TKVRanges, 
                                       TKVOwner, KVRanges, CViewNumbers, 
                                       ServerNode, OpCompleted, CurKV >>

ViewChange(self) == /\ pc[self] = "ViewChange"
                    /\ ServerState' = [ServerState EXCEPT ![self] = PrepareForTransfer]
                    /\ SViewNumber' = [SViewNumber EXCEPT ![self] = SViewNumber[self] + 1]
                    /\ SKVOwner' = [SKVOwner EXCEPT ![self] = Ownership(SKVRanges[self] \ {KeysToMigrate}, SViewNumber'[self])]
                    /\ IF ~PrepForTransferRPC
                          THEN /\ MigrationRange' = KeysToMigrate
                               /\ PrepForTransferRPC' = TRUE
                          ELSE /\ TRUE
                               /\ UNCHANGED << PrepForTransferRPC, 
                                               MigrationRange >>
                    /\ pc' = [pc EXCEPT ![self] = "SetZookeerperStateSource"]
                    /\ UNCHANGED << StateInit, TransferComplete, SourceAbort, 
                                    TargetAbort, TViewNumber, 
                                    UpdateSourceOwnership, 
                                    UpdateTargetOwnership, TakeOwnershipRPC, 
                                    TransferCompleteRPC, 
                                    ACKTransferCompleteRPC, SourceACK, 
                                    TargetACK, AllServerRanges, 
                                    AllServerViewNumbers, MigrationServers, 
                                    MigrationViewNumbers, ServerVote, Start2PC, 
                                    SourcePrepare2PC, TargetPrepare2PC, 
                                    Decision2PC, stack, Server, KVRange, 
                                    ViewNumber, OpComp, SKVRanges, TKVRanges, 
                                    TKVOwner, KVRanges, CViewNumbers, 
                                    ServerNode, OpCompleted, CurKV >>

SetZookeerperStateSource(self) == /\ pc[self] = "SetZookeerperStateSource"
                                  /\ IF ~UpdateSourceOwnership
                                        THEN /\ UpdateSourceOwnership' = TRUE
                                             /\ \E sessions \in SourceSessions \ {self}:
                                                  ServerState[sessions] = PrepareForTransfer
                                             /\ MigrationServers' = Append(MigrationServers, Source)
                                             /\ MigrationViewNumbers' = Append(MigrationViewNumbers, SViewNumber[self])
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << UpdateSourceOwnership, 
                                                             MigrationServers, 
                                                             MigrationViewNumbers >>
                                  /\ pc' = [pc EXCEPT ![self] = "TransferOwnership"]
                                  /\ UNCHANGED << StateInit, ServerState, 
                                                  TransferComplete, 
                                                  SourceAbort, TargetAbort, 
                                                  SViewNumber, TViewNumber, 
                                                  PrepForTransferRPC, 
                                                  UpdateTargetOwnership, 
                                                  TakeOwnershipRPC, 
                                                  TransferCompleteRPC, 
                                                  ACKTransferCompleteRPC, 
                                                  SourceACK, TargetACK, 
                                                  AllServerRanges, 
                                                  AllServerViewNumbers, 
                                                  MigrationRange, ServerVote, 
                                                  Start2PC, SourcePrepare2PC, 
                                                  TargetPrepare2PC, 
                                                  Decision2PC, stack, Server, 
                                                  KVRange, ViewNumber, OpComp, 
                                                  SKVRanges, SKVOwner, 
                                                  TKVRanges, TKVOwner, 
                                                  KVRanges, CViewNumbers, 
                                                  ServerNode, OpCompleted, 
                                                  CurKV >>

TransferOwnership(self) == /\ pc[self] = "TransferOwnership"
                           /\ ServerState' = [ServerState EXCEPT ![self] = TransferingOwnership]
                           /\ pc' = [pc EXCEPT ![self] = "CompleteRequests"]
                           /\ UNCHANGED << StateInit, TransferComplete, 
                                           SourceAbort, TargetAbort, 
                                           SViewNumber, TViewNumber, 
                                           PrepForTransferRPC, 
                                           UpdateSourceOwnership, 
                                           UpdateTargetOwnership, 
                                           TakeOwnershipRPC, 
                                           TransferCompleteRPC, 
                                           ACKTransferCompleteRPC, SourceACK, 
                                           TargetACK, AllServerRanges, 
                                           AllServerViewNumbers, 
                                           MigrationServers, 
                                           MigrationViewNumbers, 
                                           MigrationRange, ServerVote, 
                                           Start2PC, SourcePrepare2PC, 
                                           TargetPrepare2PC, Decision2PC, 
                                           stack, Server, KVRange, ViewNumber, 
                                           OpComp, SKVRanges, SKVOwner, 
                                           TKVRanges, TKVOwner, KVRanges, 
                                           CViewNumbers, ServerNode, 
                                           OpCompleted, CurKV >>

CompleteRequests(self) == /\ pc[self] = "CompleteRequests"
                          /\ ServerState' = [ServerState EXCEPT ![self] = WaitForPending]
                          /\ IF ~TakeOwnershipRPC
                                THEN /\ \E sessions \in SourceSessions \ {self}:
                                          ServerState'[sessions] = TransferingOwnership
                                     /\ TakeOwnershipRPC' = TRUE
                                ELSE /\ TRUE
                                     /\ UNCHANGED TakeOwnershipRPC
                          /\ pc' = [pc EXCEPT ![self] = "MoveData"]
                          /\ UNCHANGED << StateInit, TransferComplete, 
                                          SourceAbort, TargetAbort, 
                                          SViewNumber, TViewNumber, 
                                          PrepForTransferRPC, 
                                          UpdateSourceOwnership, 
                                          UpdateTargetOwnership, 
                                          TransferCompleteRPC, 
                                          ACKTransferCompleteRPC, SourceACK, 
                                          TargetACK, AllServerRanges, 
                                          AllServerViewNumbers, 
                                          MigrationServers, 
                                          MigrationViewNumbers, MigrationRange, 
                                          ServerVote, Start2PC, 
                                          SourcePrepare2PC, TargetPrepare2PC, 
                                          Decision2PC, stack, Server, KVRange, 
                                          ViewNumber, OpComp, SKVRanges, 
                                          SKVOwner, TKVRanges, TKVOwner, 
                                          KVRanges, CViewNumbers, ServerNode, 
                                          OpCompleted, CurKV >>

MoveData(self) == /\ pc[self] = "MoveData"
                  /\ SKVRanges' = [SKVRanges EXCEPT ![self] = SKVRanges[self] \ {KeysToMigrate}]
                  /\ ServerState' = [ServerState EXCEPT ![self] = MoveDataToTarget]
                  /\ IF ~TransferComplete
                        THEN /\ \E sessions \in SourceSessions \ {self}:
                                  ServerState'[sessions] = WaitForPending
                             /\ TransferComplete' = TRUE
                        ELSE /\ TRUE
                             /\ UNCHANGED TransferComplete
                  /\ pc' = [pc EXCEPT ![self] = "WaitForDecisionSource"]
                  /\ UNCHANGED << StateInit, SourceAbort, TargetAbort, 
                                  SViewNumber, TViewNumber, PrepForTransferRPC, 
                                  UpdateSourceOwnership, UpdateTargetOwnership, 
                                  TakeOwnershipRPC, TransferCompleteRPC, 
                                  ACKTransferCompleteRPC, SourceACK, TargetACK, 
                                  AllServerRanges, AllServerViewNumbers, 
                                  MigrationServers, MigrationViewNumbers, 
                                  MigrationRange, ServerVote, Start2PC, 
                                  SourcePrepare2PC, TargetPrepare2PC, 
                                  Decision2PC, stack, Server, KVRange, 
                                  ViewNumber, OpComp, SKVOwner, TKVRanges, 
                                  TKVOwner, KVRanges, CViewNumbers, ServerNode, 
                                  OpCompleted, CurKV >>

WaitForDecisionSource(self) == /\ pc[self] = "WaitForDecisionSource"
                               /\ SourceAbort \/ Decision2PC
                               /\ IF SourceAbort
                                     THEN /\ ServerState' = [ServerState EXCEPT ![self] = 2PCAbort]
                                     ELSE /\ IF ServerVote[Source] /\ ServerVote[Target]
                                                THEN /\ ServerState' = [ServerState EXCEPT ![self] = 2PCCommit]
                                                ELSE /\ ServerState' = [ServerState EXCEPT ![self] = 2PCAbort]
                               /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << StateInit, TransferComplete, 
                                               SourceAbort, TargetAbort, 
                                               SViewNumber, TViewNumber, 
                                               PrepForTransferRPC, 
                                               UpdateSourceOwnership, 
                                               UpdateTargetOwnership, 
                                               TakeOwnershipRPC, 
                                               TransferCompleteRPC, 
                                               ACKTransferCompleteRPC, 
                                               SourceACK, TargetACK, 
                                               AllServerRanges, 
                                               AllServerViewNumbers, 
                                               MigrationServers, 
                                               MigrationViewNumbers, 
                                               MigrationRange, ServerVote, 
                                               Start2PC, SourcePrepare2PC, 
                                               TargetPrepare2PC, Decision2PC, 
                                               stack, Server, KVRange, 
                                               ViewNumber, OpComp, SKVRanges, 
                                               SKVOwner, TKVRanges, TKVOwner, 
                                               KVRanges, CViewNumbers, 
                                               ServerNode, OpCompleted, CurKV >>

SourceProcess(self) == InitMigrationSource(self) \/ SampleRecords(self)
                          \/ ViewChange(self)
                          \/ SetZookeerperStateSource(self)
                          \/ TransferOwnership(self)
                          \/ CompleteRequests(self) \/ MoveData(self)
                          \/ WaitForDecisionSource(self)

CompleteMigration == /\ pc[Source] = "CompleteMigration"
                     /\ TransferComplete
                     /\ \E s \in SourceSessions:
                          ServerState' = [ServerState EXCEPT ![s] = WaitForCheckpoint]
                     /\ TransferCompleteRPC' = TRUE
                     /\ pc' = [pc EXCEPT ![Source] = "StartCommit"]
                     /\ UNCHANGED << StateInit, TransferComplete, SourceAbort, 
                                     TargetAbort, SViewNumber, TViewNumber, 
                                     PrepForTransferRPC, UpdateSourceOwnership, 
                                     UpdateTargetOwnership, TakeOwnershipRPC, 
                                     ACKTransferCompleteRPC, SourceACK, 
                                     TargetACK, AllServerRanges, 
                                     AllServerViewNumbers, MigrationServers, 
                                     MigrationViewNumbers, MigrationRange, 
                                     ServerVote, Start2PC, SourcePrepare2PC, 
                                     TargetPrepare2PC, Decision2PC, stack, 
                                     Server, KVRange, ViewNumber, OpComp, 
                                     SKVRanges, SKVOwner, TKVRanges, TKVOwner, 
                                     KVRanges, CViewNumbers, ServerNode, 
                                     OpCompleted, CurKV >>

StartCommit == /\ pc[Source] = "StartCommit"
               /\ ACKTransferCompleteRPC
               /\ Start2PC' = TRUE
               /\ pc' = [pc EXCEPT ![Source] = "WaitForPrepare"]
               /\ UNCHANGED << StateInit, ServerState, TransferComplete, 
                               SourceAbort, TargetAbort, SViewNumber, 
                               TViewNumber, PrepForTransferRPC, 
                               UpdateSourceOwnership, UpdateTargetOwnership, 
                               TakeOwnershipRPC, TransferCompleteRPC, 
                               ACKTransferCompleteRPC, SourceACK, TargetACK, 
                               AllServerRanges, AllServerViewNumbers, 
                               MigrationServers, MigrationViewNumbers, 
                               MigrationRange, ServerVote, SourcePrepare2PC, 
                               TargetPrepare2PC, Decision2PC, stack, Server, 
                               KVRange, ViewNumber, OpComp, SKVRanges, 
                               SKVOwner, TKVRanges, TKVOwner, KVRanges, 
                               CViewNumbers, ServerNode, OpCompleted, CurKV >>

WaitForPrepare == /\ pc[Source] = "WaitForPrepare"
                  /\ SourcePrepare2PC
                  /\ \/ /\ SourceACK' = TRUE
                        /\ \E s \in SourceSessions:
                             ServerState' = [ServerState EXCEPT ![s] = 2PCPrepare]
                        /\ UNCHANGED SourceAbort
                     \/ /\ SourceACK' = FALSE
                        /\ SourceAbort' = TRUE
                        /\ UNCHANGED ServerState
                  /\ pc' = [pc EXCEPT ![Source] = "Done"]
                  /\ UNCHANGED << StateInit, TransferComplete, TargetAbort, 
                                  SViewNumber, TViewNumber, PrepForTransferRPC, 
                                  UpdateSourceOwnership, UpdateTargetOwnership, 
                                  TakeOwnershipRPC, TransferCompleteRPC, 
                                  ACKTransferCompleteRPC, TargetACK, 
                                  AllServerRanges, AllServerViewNumbers, 
                                  MigrationServers, MigrationViewNumbers, 
                                  MigrationRange, ServerVote, Start2PC, 
                                  SourcePrepare2PC, TargetPrepare2PC, 
                                  Decision2PC, stack, Server, KVRange, 
                                  ViewNumber, OpComp, SKVRanges, SKVOwner, 
                                  TKVRanges, TKVOwner, KVRanges, CViewNumbers, 
                                  ServerNode, OpCompleted, CurKV >>

SourceServer == CompleteMigration \/ StartCommit \/ WaitForPrepare

InitMigrationTarget(self) == /\ pc[self] = "InitMigrationTarget"
                             /\ PrepForTransferRPC
                             /\ ServerState' = [ServerState EXCEPT ![self] = PrepareForMigration]
                             /\ TKVRanges' = [TKVRanges EXCEPT ![self] = TKVRanges[self] \union {MigrationRange}]
                             /\ TViewNumber' = [TViewNumber EXCEPT ![self] = TViewNumber[self] + 1]
                             /\ TKVOwner' = [TKVOwner EXCEPT ![self] = Ownership(TKVRanges'[self], TViewNumber'[self])]
                             /\ pc' = [pc EXCEPT ![self] = "SetZookeerperStateTarget"]
                             /\ UNCHANGED << StateInit, TransferComplete, 
                                             SourceAbort, TargetAbort, 
                                             SViewNumber, PrepForTransferRPC, 
                                             UpdateSourceOwnership, 
                                             UpdateTargetOwnership, 
                                             TakeOwnershipRPC, 
                                             TransferCompleteRPC, 
                                             ACKTransferCompleteRPC, SourceACK, 
                                             TargetACK, AllServerRanges, 
                                             AllServerViewNumbers, 
                                             MigrationServers, 
                                             MigrationViewNumbers, 
                                             MigrationRange, ServerVote, 
                                             Start2PC, SourcePrepare2PC, 
                                             TargetPrepare2PC, Decision2PC, 
                                             stack, Server, KVRange, 
                                             ViewNumber, OpComp, SKVRanges, 
                                             SKVOwner, KVRanges, CViewNumbers, 
                                             ServerNode, OpCompleted, CurKV >>

SetZookeerperStateTarget(self) == /\ pc[self] = "SetZookeerperStateTarget"
                                  /\ UpdateSourceOwnership
                                  /\ IF ~UpdateTargetOwnership
                                        THEN /\ UpdateTargetOwnership' = TRUE
                                             /\ \E sessions \in TargetSessions \ {self}:
                                                  ServerState[sessions] = PrepareForMigration
                                             /\ MigrationServers' = Append(MigrationServers, Target)
                                             /\ MigrationViewNumbers' = Append(MigrationViewNumbers, TViewNumber[self])
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << UpdateTargetOwnership, 
                                                             MigrationServers, 
                                                             MigrationViewNumbers >>
                                  /\ pc' = [pc EXCEPT ![self] = "TakeOwnership"]
                                  /\ UNCHANGED << StateInit, ServerState, 
                                                  TransferComplete, 
                                                  SourceAbort, TargetAbort, 
                                                  SViewNumber, TViewNumber, 
                                                  PrepForTransferRPC, 
                                                  UpdateSourceOwnership, 
                                                  TakeOwnershipRPC, 
                                                  TransferCompleteRPC, 
                                                  ACKTransferCompleteRPC, 
                                                  SourceACK, TargetACK, 
                                                  AllServerRanges, 
                                                  AllServerViewNumbers, 
                                                  MigrationRange, ServerVote, 
                                                  Start2PC, SourcePrepare2PC, 
                                                  TargetPrepare2PC, 
                                                  Decision2PC, stack, Server, 
                                                  KVRange, ViewNumber, OpComp, 
                                                  SKVRanges, SKVOwner, 
                                                  TKVRanges, TKVOwner, 
                                                  KVRanges, CViewNumbers, 
                                                  ServerNode, OpCompleted, 
                                                  CurKV >>

TakeOwnership(self) == /\ pc[self] = "TakeOwnership"
                       /\ TakeOwnershipRPC
                       /\ ServerState' = [ServerState EXCEPT ![self] = ReceivingData]
                       /\ pc' = [pc EXCEPT ![self] = "WaitForDecisionTarget"]
                       /\ UNCHANGED << StateInit, TransferComplete, 
                                       SourceAbort, TargetAbort, SViewNumber, 
                                       TViewNumber, PrepForTransferRPC, 
                                       UpdateSourceOwnership, 
                                       UpdateTargetOwnership, TakeOwnershipRPC, 
                                       TransferCompleteRPC, 
                                       ACKTransferCompleteRPC, SourceACK, 
                                       TargetACK, AllServerRanges, 
                                       AllServerViewNumbers, MigrationServers, 
                                       MigrationViewNumbers, MigrationRange, 
                                       ServerVote, Start2PC, SourcePrepare2PC, 
                                       TargetPrepare2PC, Decision2PC, stack, 
                                       Server, KVRange, ViewNumber, OpComp, 
                                       SKVRanges, SKVOwner, TKVRanges, 
                                       TKVOwner, KVRanges, CViewNumbers, 
                                       ServerNode, OpCompleted, CurKV >>

WaitForDecisionTarget(self) == /\ pc[self] = "WaitForDecisionTarget"
                               /\ TargetAbort \/ Decision2PC
                               /\ IF TargetAbort
                                     THEN /\ ServerState' = [ServerState EXCEPT ![self] = 2PCAbort]
                                     ELSE /\ IF ServerVote[Source] /\ ServerVote[Target]
                                                THEN /\ ServerState' = [ServerState EXCEPT ![self] = 2PCCommit]
                                                ELSE /\ ServerState' = [ServerState EXCEPT ![self] = 2PCAbort]
                               /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << StateInit, TransferComplete, 
                                               SourceAbort, TargetAbort, 
                                               SViewNumber, TViewNumber, 
                                               PrepForTransferRPC, 
                                               UpdateSourceOwnership, 
                                               UpdateTargetOwnership, 
                                               TakeOwnershipRPC, 
                                               TransferCompleteRPC, 
                                               ACKTransferCompleteRPC, 
                                               SourceACK, TargetACK, 
                                               AllServerRanges, 
                                               AllServerViewNumbers, 
                                               MigrationServers, 
                                               MigrationViewNumbers, 
                                               MigrationRange, ServerVote, 
                                               Start2PC, SourcePrepare2PC, 
                                               TargetPrepare2PC, Decision2PC, 
                                               stack, Server, KVRange, 
                                               ViewNumber, OpComp, SKVRanges, 
                                               SKVOwner, TKVRanges, TKVOwner, 
                                               KVRanges, CViewNumbers, 
                                               ServerNode, OpCompleted, CurKV >>

TargetProcess(self) == InitMigrationTarget(self)
                          \/ SetZookeerperStateTarget(self)
                          \/ TakeOwnership(self)
                          \/ WaitForDecisionTarget(self)

StartCheckpointing == /\ pc[Target] = "StartCheckpointing"
                      /\ TransferCompleteRPC
                      /\ \E s \in TargetSessions:
                           ServerState' = [ServerState EXCEPT ![s] = Checkpointing]
                      /\ ACKTransferCompleteRPC' = TRUE
                      /\ pc' = [pc EXCEPT ![Target] = "WaitFor2PC"]
                      /\ UNCHANGED << StateInit, TransferComplete, SourceAbort, 
                                      TargetAbort, SViewNumber, TViewNumber, 
                                      PrepForTransferRPC, 
                                      UpdateSourceOwnership, 
                                      UpdateTargetOwnership, TakeOwnershipRPC, 
                                      TransferCompleteRPC, SourceACK, 
                                      TargetACK, AllServerRanges, 
                                      AllServerViewNumbers, MigrationServers, 
                                      MigrationViewNumbers, MigrationRange, 
                                      ServerVote, Start2PC, SourcePrepare2PC, 
                                      TargetPrepare2PC, Decision2PC, stack, 
                                      Server, KVRange, ViewNumber, OpComp, 
                                      SKVRanges, SKVOwner, TKVRanges, TKVOwner, 
                                      KVRanges, CViewNumbers, ServerNode, 
                                      OpCompleted, CurKV >>

WaitFor2PC == /\ pc[Target] = "WaitFor2PC"
              /\ TargetPrepare2PC
              /\ \/ /\ TargetACK' = TRUE
                    /\ \E s \in TargetSessions:
                         ServerState' = [ServerState EXCEPT ![s] = 2PCPrepare]
                    /\ UNCHANGED TargetAbort
                 \/ /\ TargetACK' = FALSE
                    /\ TargetAbort' = TRUE
                    /\ UNCHANGED ServerState
              /\ pc' = [pc EXCEPT ![Target] = "Done"]
              /\ UNCHANGED << StateInit, TransferComplete, SourceAbort, 
                              SViewNumber, TViewNumber, PrepForTransferRPC, 
                              UpdateSourceOwnership, UpdateTargetOwnership, 
                              TakeOwnershipRPC, TransferCompleteRPC, 
                              ACKTransferCompleteRPC, SourceACK, 
                              AllServerRanges, AllServerViewNumbers, 
                              MigrationServers, MigrationViewNumbers, 
                              MigrationRange, ServerVote, Start2PC, 
                              SourcePrepare2PC, TargetPrepare2PC, Decision2PC, 
                              stack, Server, KVRange, ViewNumber, OpComp, 
                              SKVRanges, SKVOwner, TKVRanges, TKVOwner, 
                              KVRanges, CViewNumbers, ServerNode, OpCompleted, 
                              CurKV >>

TargetServer == StartCheckpointing \/ WaitFor2PC

InitState == /\ pc[Zookeeper] = "InitState"
             /\ AllServerRanges' = [AllServerRanges EXCEPT ![Source] = {SourceKeys, KeysToMigrate},
                                                           ![Target] = {TargetKeys}]
             /\ StateInit' = TRUE
             /\ pc' = [pc EXCEPT ![Zookeeper] = "SetMigrationSourceState"]
             /\ UNCHANGED << ServerState, TransferComplete, SourceAbort, 
                             TargetAbort, SViewNumber, TViewNumber, 
                             PrepForTransferRPC, UpdateSourceOwnership, 
                             UpdateTargetOwnership, TakeOwnershipRPC, 
                             TransferCompleteRPC, ACKTransferCompleteRPC, 
                             SourceACK, TargetACK, AllServerViewNumbers, 
                             MigrationServers, MigrationViewNumbers, 
                             MigrationRange, ServerVote, Start2PC, 
                             SourcePrepare2PC, TargetPrepare2PC, Decision2PC, 
                             stack, Server, KVRange, ViewNumber, OpComp, 
                             SKVRanges, SKVOwner, TKVRanges, TKVOwner, 
                             KVRanges, CViewNumbers, ServerNode, OpCompleted, 
                             CurKV >>

SetMigrationSourceState == /\ pc[Zookeeper] = "SetMigrationSourceState"
                           /\ UpdateSourceOwnership
                           /\ AllServerRanges' = [AllServerRanges EXCEPT ![Head(MigrationServers)] = AllServerRanges[Head(MigrationServers)] \ {MigrationRange}]
                           /\ AllServerViewNumbers' = [AllServerViewNumbers EXCEPT ![Head(MigrationServers)] = Head(MigrationViewNumbers)]
                           /\ pc' = [pc EXCEPT ![Zookeeper] = "SetMigrationTargetState"]
                           /\ UNCHANGED << StateInit, ServerState, 
                                           TransferComplete, SourceAbort, 
                                           TargetAbort, SViewNumber, 
                                           TViewNumber, PrepForTransferRPC, 
                                           UpdateSourceOwnership, 
                                           UpdateTargetOwnership, 
                                           TakeOwnershipRPC, 
                                           TransferCompleteRPC, 
                                           ACKTransferCompleteRPC, SourceACK, 
                                           TargetACK, MigrationServers, 
                                           MigrationViewNumbers, 
                                           MigrationRange, ServerVote, 
                                           Start2PC, SourcePrepare2PC, 
                                           TargetPrepare2PC, Decision2PC, 
                                           stack, Server, KVRange, ViewNumber, 
                                           OpComp, SKVRanges, SKVOwner, 
                                           TKVRanges, TKVOwner, KVRanges, 
                                           CViewNumbers, ServerNode, 
                                           OpCompleted, CurKV >>

SetMigrationTargetState == /\ pc[Zookeeper] = "SetMigrationTargetState"
                           /\ UpdateTargetOwnership
                           /\ AllServerRanges' = [AllServerRanges EXCEPT ![Head(Tail(MigrationServers))] = AllServerRanges[Head(Tail(MigrationServers))] \union {MigrationRange}]
                           /\ AllServerViewNumbers' = [AllServerViewNumbers EXCEPT ![Head(Tail(MigrationServers))] = Head(Tail(MigrationViewNumbers))]
                           /\ pc' = [pc EXCEPT ![Zookeeper] = "Init2PC"]
                           /\ UNCHANGED << StateInit, ServerState, 
                                           TransferComplete, SourceAbort, 
                                           TargetAbort, SViewNumber, 
                                           TViewNumber, PrepForTransferRPC, 
                                           UpdateSourceOwnership, 
                                           UpdateTargetOwnership, 
                                           TakeOwnershipRPC, 
                                           TransferCompleteRPC, 
                                           ACKTransferCompleteRPC, SourceACK, 
                                           TargetACK, MigrationServers, 
                                           MigrationViewNumbers, 
                                           MigrationRange, ServerVote, 
                                           Start2PC, SourcePrepare2PC, 
                                           TargetPrepare2PC, Decision2PC, 
                                           stack, Server, KVRange, ViewNumber, 
                                           OpComp, SKVRanges, SKVOwner, 
                                           TKVRanges, TKVOwner, KVRanges, 
                                           CViewNumbers, ServerNode, 
                                           OpCompleted, CurKV >>

Init2PC == /\ pc[Zookeeper] = "Init2PC"
           /\ Start2PC
           /\ SourcePrepare2PC' = TRUE
           /\ TargetPrepare2PC' = TRUE
           /\ pc' = [pc EXCEPT ![Zookeeper] = "CompletionDecision"]
           /\ UNCHANGED << StateInit, ServerState, TransferComplete, 
                           SourceAbort, TargetAbort, SViewNumber, TViewNumber, 
                           PrepForTransferRPC, UpdateSourceOwnership, 
                           UpdateTargetOwnership, TakeOwnershipRPC, 
                           TransferCompleteRPC, ACKTransferCompleteRPC, 
                           SourceACK, TargetACK, AllServerRanges, 
                           AllServerViewNumbers, MigrationServers, 
                           MigrationViewNumbers, MigrationRange, ServerVote, 
                           Start2PC, Decision2PC, stack, Server, KVRange, 
                           ViewNumber, OpComp, SKVRanges, SKVOwner, TKVRanges, 
                           TKVOwner, KVRanges, CViewNumbers, ServerNode, 
                           OpCompleted, CurKV >>

CompletionDecision == /\ pc[Zookeeper] = "CompletionDecision"
                      /\ SourceACK \in BOOLEAN \/ TargetACK \in BOOLEAN
                      /\ \/ /\ SourceACK \in BOOLEAN /\ TargetACK \in BOOLEAN
                            /\ IF ~SourceACK \/ ~TargetACK
                                  THEN /\ ServerVote' = [ServerVote EXCEPT ![Source] = FALSE,
                                                                           ![Target] = FALSE]
                                  ELSE /\ IF SourceACK /\ TargetACK
                                             THEN /\ ServerVote' = [ServerVote EXCEPT ![Source] = TRUE,
                                                                                      ![Target] = TRUE]
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED ServerVote
                         \/ /\ IF SourceACK /= TRUE \/ TargetACK /= TRUE
                                  THEN /\ ServerVote' = [ServerVote EXCEPT ![Source] = FALSE,
                                                                           ![Target] = FALSE]
                                  ELSE /\ SourceACK \in BOOLEAN /\ TargetACK \in BOOLEAN
                                       /\ IF ~SourceACK \/ ~TargetACK
                                             THEN /\ ServerVote' = [ServerVote EXCEPT ![Source] = FALSE,
                                                                                      ![Target] = FALSE]
                                             ELSE /\ IF SourceACK /\ TargetACK
                                                        THEN /\ ServerVote' = [ServerVote EXCEPT ![Source] = TRUE,
                                                                                                 ![Target] = TRUE]
                                                        ELSE /\ TRUE
                                                             /\ UNCHANGED ServerVote
                      /\ pc' = [pc EXCEPT ![Zookeeper] = "CommitMigration"]
                      /\ UNCHANGED << StateInit, ServerState, TransferComplete, 
                                      SourceAbort, TargetAbort, SViewNumber, 
                                      TViewNumber, PrepForTransferRPC, 
                                      UpdateSourceOwnership, 
                                      UpdateTargetOwnership, TakeOwnershipRPC, 
                                      TransferCompleteRPC, 
                                      ACKTransferCompleteRPC, SourceACK, 
                                      TargetACK, AllServerRanges, 
                                      AllServerViewNumbers, MigrationServers, 
                                      MigrationViewNumbers, MigrationRange, 
                                      Start2PC, SourcePrepare2PC, 
                                      TargetPrepare2PC, Decision2PC, stack, 
                                      Server, KVRange, ViewNumber, OpComp, 
                                      SKVRanges, SKVOwner, TKVRanges, TKVOwner, 
                                      KVRanges, CViewNumbers, ServerNode, 
                                      OpCompleted, CurKV >>

CommitMigration == /\ pc[Zookeeper] = "CommitMigration"
                   /\ Decision2PC' = TRUE
                   /\ \E s \in Servers:
                        IF ~ServerVote[s]
                           THEN /\ AllServerRanges' = [AllServerRanges EXCEPT ![Head(MigrationServers)] = AllServerRanges[Head(MigrationServers)] \union {MigrationRange},
                                                                              ![Head(Tail(MigrationServers))] = AllServerRanges[Head(Tail(MigrationServers))] \ {MigrationRange}]
                                /\ AllServerViewNumbers' = [AllServerViewNumbers EXCEPT ![Head(MigrationServers)] = Head(MigrationViewNumbers),
                                                                                        ![Head(Tail(MigrationServers))] = Head(Tail(MigrationViewNumbers))]
                           ELSE /\ TRUE
                                /\ UNCHANGED << AllServerRanges, 
                                                AllServerViewNumbers >>
                   /\ pc' = [pc EXCEPT ![Zookeeper] = "Done"]
                   /\ UNCHANGED << StateInit, ServerState, TransferComplete, 
                                   SourceAbort, TargetAbort, SViewNumber, 
                                   TViewNumber, PrepForTransferRPC, 
                                   UpdateSourceOwnership, 
                                   UpdateTargetOwnership, TakeOwnershipRPC, 
                                   TransferCompleteRPC, ACKTransferCompleteRPC, 
                                   SourceACK, TargetACK, MigrationServers, 
                                   MigrationViewNumbers, MigrationRange, 
                                   ServerVote, Start2PC, SourcePrepare2PC, 
                                   TargetPrepare2PC, stack, Server, KVRange, 
                                   ViewNumber, OpComp, SKVRanges, SKVOwner, 
                                   TKVRanges, TKVOwner, KVRanges, CViewNumbers, 
                                   ServerNode, OpCompleted, CurKV >>

CoordinatorProcess == InitState \/ SetMigrationSourceState
                         \/ SetMigrationTargetState \/ Init2PC
                         \/ CompletionDecision \/ CommitMigration

InitClient == /\ pc["Client"] = "InitClient"
              /\ StateInit
              /\ pc' = [pc EXCEPT !["Client"] = "ServerInteraction"]
              /\ UNCHANGED << StateInit, ServerState, TransferComplete, 
                              SourceAbort, TargetAbort, SViewNumber, 
                              TViewNumber, PrepForTransferRPC, 
                              UpdateSourceOwnership, UpdateTargetOwnership, 
                              TakeOwnershipRPC, TransferCompleteRPC, 
                              ACKTransferCompleteRPC, SourceACK, TargetACK, 
                              AllServerRanges, AllServerViewNumbers, 
                              MigrationServers, MigrationViewNumbers, 
                              MigrationRange, ServerVote, Start2PC, 
                              SourcePrepare2PC, TargetPrepare2PC, Decision2PC, 
                              stack, Server, KVRange, ViewNumber, OpComp, 
                              SKVRanges, SKVOwner, TKVRanges, TKVOwner, 
                              KVRanges, CViewNumbers, ServerNode, OpCompleted, 
                              CurKV >>

ServerInteraction == /\ pc["Client"] = "ServerInteraction"
                     /\ IF ~Decision2PC
                           THEN /\ pc' = [pc EXCEPT !["Client"] = "RequestOp"]
                           ELSE /\ pc' = [pc EXCEPT !["Client"] = "Done"]
                     /\ UNCHANGED << StateInit, ServerState, TransferComplete, 
                                     SourceAbort, TargetAbort, SViewNumber, 
                                     TViewNumber, PrepForTransferRPC, 
                                     UpdateSourceOwnership, 
                                     UpdateTargetOwnership, TakeOwnershipRPC, 
                                     TransferCompleteRPC, 
                                     ACKTransferCompleteRPC, SourceACK, 
                                     TargetACK, AllServerRanges, 
                                     AllServerViewNumbers, MigrationServers, 
                                     MigrationViewNumbers, MigrationRange, 
                                     ServerVote, Start2PC, SourcePrepare2PC, 
                                     TargetPrepare2PC, Decision2PC, stack, 
                                     Server, KVRange, ViewNumber, OpComp, 
                                     SKVRanges, SKVOwner, TKVRanges, TKVOwner, 
                                     KVRanges, CViewNumbers, ServerNode, 
                                     OpCompleted, CurKV >>

RequestOp == /\ pc["Client"] = "RequestOp"
             /\ \E kv \in KVRanges:
                  /\ CurKV' = kv
                  /\ /\ KVRange' = [KVRange EXCEPT !["Client"] = kv]
                     /\ OpComp' = [OpComp EXCEPT !["Client"] = OpCompleted]
                     /\ Server' = [Server EXCEPT !["Client"] = ServerNode[kv]]
                     /\ ViewNumber' = [ViewNumber EXCEPT !["Client"] = CViewNumbers[kv]]
                     /\ stack' = [stack EXCEPT !["Client"] = << [ procedure |->  "MakeRequest",
                                                                  pc        |->  "UpdateClientState",
                                                                  Server    |->  Server["Client"],
                                                                  KVRange   |->  KVRange["Client"],
                                                                  ViewNumber |->  ViewNumber["Client"],
                                                                  OpComp    |->  OpComp["Client"] ] >>
                                                              \o stack["Client"]]
                  /\ pc' = [pc EXCEPT !["Client"] = "CheckServerRange"]
             /\ UNCHANGED << StateInit, ServerState, TransferComplete, 
                             SourceAbort, TargetAbort, SViewNumber, 
                             TViewNumber, PrepForTransferRPC, 
                             UpdateSourceOwnership, UpdateTargetOwnership, 
                             TakeOwnershipRPC, TransferCompleteRPC, 
                             ACKTransferCompleteRPC, SourceACK, TargetACK, 
                             AllServerRanges, AllServerViewNumbers, 
                             MigrationServers, MigrationViewNumbers, 
                             MigrationRange, ServerVote, Start2PC, 
                             SourcePrepare2PC, TargetPrepare2PC, Decision2PC, 
                             SKVRanges, SKVOwner, TKVRanges, TKVOwner, 
                             KVRanges, CViewNumbers, ServerNode, OpCompleted >>

UpdateClientState == /\ pc["Client"] = "UpdateClientState"
                     /\ IF ~OpCompleted
                           THEN /\ IF CurKV \in AllServerRanges[Source]
                                      THEN /\ ServerNode' = [ServerNode EXCEPT ![CurKV] = Source]
                                           /\ CViewNumbers' = [CViewNumbers EXCEPT ![CurKV] = AllServerViewNumbers[Source]]
                                      ELSE /\ IF CurKV \in AllServerRanges[Target]
                                                 THEN /\ ServerNode' = [ServerNode EXCEPT ![CurKV] = Target]
                                                      /\ CViewNumbers' = [CViewNumbers EXCEPT ![CurKV] = AllServerViewNumbers[Target]]
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED << CViewNumbers, 
                                                                      ServerNode >>
                           ELSE /\ TRUE
                                /\ UNCHANGED << CViewNumbers, ServerNode >>
                     /\ pc' = [pc EXCEPT !["Client"] = "ServerInteraction"]
                     /\ UNCHANGED << StateInit, ServerState, TransferComplete, 
                                     SourceAbort, TargetAbort, SViewNumber, 
                                     TViewNumber, PrepForTransferRPC, 
                                     UpdateSourceOwnership, 
                                     UpdateTargetOwnership, TakeOwnershipRPC, 
                                     TransferCompleteRPC, 
                                     ACKTransferCompleteRPC, SourceACK, 
                                     TargetACK, AllServerRanges, 
                                     AllServerViewNumbers, MigrationServers, 
                                     MigrationViewNumbers, MigrationRange, 
                                     ServerVote, Start2PC, SourcePrepare2PC, 
                                     TargetPrepare2PC, Decision2PC, stack, 
                                     Server, KVRange, ViewNumber, OpComp, 
                                     SKVRanges, SKVOwner, TKVRanges, TKVOwner, 
                                     KVRanges, OpCompleted, CurKV >>

Clients == InitClient \/ ServerInteraction \/ RequestOp
              \/ UpdateClientState

Next == SourceServer \/ TargetServer \/ CoordinatorProcess \/ Clients
           \/ (\E self \in ProcSet: MakeRequest(self))
           \/ (\E self \in SourceSessions: SourceProcess(self))
           \/ (\E self \in TargetSessions: TargetProcess(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in SourceSessions : WF_vars(SourceProcess(self))
        /\ WF_vars(SourceServer)
        /\ \A self \in TargetSessions : WF_vars(TargetProcess(self))
        /\ WF_vars(TargetServer)
        /\ WF_vars(CoordinatorProcess)
        /\ WF_vars(Clients) /\ WF_vars(MakeRequest("Client"))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Tue Feb 26 20:00:51 MST 2019 by aarushi
\* Created Thu Jan 17 10:53:34 MST 2019 by aarushi
