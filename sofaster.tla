------------------------------ MODULE sofaster ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Source, Target, Zookeeper, SourceSessions, TargetSessions, NULL, PrepareToSample, Sampling, PrepareForTransfer, TransferingOwnership, WaitForPending, MoveDataToTarget, PrepareForMigration, ReceivingData, WaitForCheckpoint, Checkpointing, 2PCCommit, 2PCPrepare, 2PCAbort, SourceKeys, TargetKeys, KeysToMigrate 

Servers == {Source, Target}

Ownership(kvset, view) == [kv \in kvset |-> view]

SetServerState == [s \in SourceSessions \union TargetSessions |-> NULL]

SetViewNumber(ServerSessions) == [s \in ServerSessions |-> 0]

SetServerVote == [s \in Servers |-> FALSE]

(*--algorithm sofaster
variables
    \* Spec state
    ServerState = SetServerState,
    TransferComplete = FALSE,
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

\* All local view numbers start at the last CPR checkpoint (0)
\* Keep history of views from the last checkpoint? [key -> [view ranges, client sessions]]; This will be on a per thread basis?

\* remove fair to check crashed states?
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
            \* inform target about migrating ranges
            MigrationRange := KeysToMigrate;
            MigrationServers := Append(MigrationServers, Source);
            MigrationViewNumbers := Append(MigrationViewNumbers, SViewNumber[self]);
            PrepForTransferRPC := TRUE;
        end if;
    TransferOwnership:
        \* TODO: Inform all clients
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
            \*UpdateZookeeper(Source, SViewNumber[self], SKVRanges);
        end if;
end process;

fair process SourceServer = Source
    variable SourceDecision = FALSE;
  begin
    \* Checkpointing
    CompleteMigration:
        await TransferComplete;
        \*UpdateZookeeper(Source, SViewNumber[self], SKVRanges);
        with s \in SourceSessions do
            ServerState[s] := WaitForCheckpoint
        end with;
        TransferCompleteRPC := TRUE;
    StartCommit:
        await ACKTransferCompleteRPC;
        Start2PC := TRUE;
    \* 2PC - need to check if other server has voted?
    WaitForPrepare:
        await SourcePrepare2PC;
        either 
            SourceACK := TRUE;
            with s \in SourceSessions do 
                ServerState[s] := 2PCPrepare
            end with;
        or
            SourceACK := FALSE;
            with s \in SourceSessions do 
                ServerState[s] := 2PCAbort
            end with;
            SourceDecision := TRUE;
        end either;
    WaitForDecisionSource:
        if ~SourceDecision then
            await Decision2PC; 
            if ServerVote[Target] then 
                with s \in SourceSessions do
                    ServerState[s] := 2PCCommit
                end with;
            else 
                with s \in SourceSessions do
                    ServerState[s] := 2PCAbort
                end with;
            end if;
        end if;
end process;

fair process TargetProcess \in TargetSessions
    variable TKVRanges = {TargetKeys}, MigratingRanges = NULL, TKVOwner = Ownership(TKVRanges, 0);
  begin
    InitMigrationTarget:
        await PrepForTransferRPC;
        \* TODO: Buffer requests for migrating ranges
        ServerState[self] := PrepareForMigration;
        TViewNumber[self] := TViewNumber[self] + 1;
        MigrationServers := Append(MigrationServers, Target);
        MigrationViewNumbers := Append(MigrationViewNumbers, TViewNumber[self]);
        MigratingRanges := MigrationRange;
        TKVRanges := TKVRanges \union {MigratingRanges};
        TKVOwner := Ownership(TKVRanges, TViewNumber[self]);
    TakeOwnership:
        await TakeOwnershipRPC;
        \* Enter received records
        ServerState[self] := ReceivingData;
        \*UpdateZookeeper(Target, TViewNumber[self], TKVRanges);
        \* TODO: Start executing requests
end process;

fair process TargetServer = Target
    variable TargetDecision = FALSE;
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
            with s \in TargetSessions do
                ServerState[s] := 2PCAbort
            end with;
            TargetDecision := TRUE;
        end either;
    WaitForDecisionTarget:
        if ~TargetDecision then
            await Decision2PC;
            if ServerVote[Source] then 
                with s \in TargetSessions do
                    ServerState[s] := 2PCCommit
                end with;
            else
                with s \in TargetSessions do
                    ServerState[s] := 2PCAbort
                end with;
            end if;
        end if;
end process;

\* Model for client with an active session involved in migration
(*process Clients = ClientSession
    variable CViewNumbers = SetViewNumber, ServerNode = [s \in KVRanges |-> Source], KVRanges = {SourceKeys, KeysToMigrate, TargetKeys};
  begin 
    ServerInteraction:
        while TRUE do
            \* call proc that checks if ServerNode owns the 
        end while;
end process;*)

\* TODO: Model timeouts and crashes - when third server is needed
fair process CoordinatorProcess = Zookeeper
  begin
    Init2PC:
        await Start2PC;
        SourcePrepare2PC := TRUE;
        TargetPrepare2PC := TRUE;
    CompletionDecision:
        await SourceACK \in BOOLEAN \/ TargetACK \in BOOLEAN;
        either 
            await SourceACK \in BOOLEAN /\ TargetACK \in BOOLEAN;
            \* one of the servers voted false - is this needed?
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
                \* one of the servers voted false - is this needed?
                if ~SourceACK \/ ~TargetACK then
                    ServerVote[Source] := FALSE || ServerVote[Target] := FALSE;
                elsif SourceACK /\ TargetACK then
                    ServerVote[Source] := TRUE || ServerVote[Target] := TRUE;
                end if;
            end if;
        end either;
        Decision2PC := TRUE;
end process; 

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES ServerState, TransferComplete, SViewNumber, TViewNumber, 
          PrepForTransferRPC, UpdateSourceOwnership, UpdateTargetOwnership, 
          TakeOwnershipRPC, TransferCompleteRPC, ACKTransferCompleteRPC, 
          SourceACK, TargetACK, MigrationServers, MigrationViewNumbers, 
          MigrationRange, ServerVote, Start2PC, SourcePrepare2PC, 
          TargetPrepare2PC, Decision2PC, pc

(* define statement *)
MigrationSuccess == (\E s \in SourceSessions: ServerState[s] = 2PCCommit /\ \E t \in TargetSessions: ServerState[t] = 2PCCommit) ~> <>[](ServerVote[Source] /\ ServerVote[Target])
MigrationFailure == (\E s \in SourceSessions: ServerState[s] = 2PCAbort /\ \E t \in TargetSessions: ServerState[t] = 2PCAbort) ~> <>[] (~ServerVote[Source] /\ ~ServerVote[Target])

VARIABLES SKVRanges, SKVOwner, SourceDecision, TKVRanges, MigratingRanges, 
          TKVOwner, TargetDecision

vars == << ServerState, TransferComplete, SViewNumber, TViewNumber, 
           PrepForTransferRPC, UpdateSourceOwnership, UpdateTargetOwnership, 
           TakeOwnershipRPC, TransferCompleteRPC, ACKTransferCompleteRPC, 
           SourceACK, TargetACK, MigrationServers, MigrationViewNumbers, 
           MigrationRange, ServerVote, Start2PC, SourcePrepare2PC, 
           TargetPrepare2PC, Decision2PC, pc, SKVRanges, SKVOwner, 
           SourceDecision, TKVRanges, MigratingRanges, TKVOwner, 
           TargetDecision >>

ProcSet == (SourceSessions) \cup {Source} \cup (TargetSessions) \cup {Target} \cup {Zookeeper}

Init == (* Global variables *)
        /\ ServerState = SetServerState
        /\ TransferComplete = FALSE
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
        /\ MigrationServers = <<>>
        /\ MigrationViewNumbers = <<>>
        /\ MigrationRange = NULL
        /\ ServerVote = SetServerVote
        /\ Start2PC = FALSE
        /\ SourcePrepare2PC = FALSE
        /\ TargetPrepare2PC = FALSE
        /\ Decision2PC = FALSE
        (* Process SourceProcess *)
        /\ SKVRanges = [self \in SourceSessions |-> {SourceKeys, KeysToMigrate}]
        /\ SKVOwner = [self \in SourceSessions |-> Ownership(SKVRanges[self], 0)]
        (* Process SourceServer *)
        /\ SourceDecision = FALSE
        (* Process TargetProcess *)
        /\ TKVRanges = [self \in TargetSessions |-> {TargetKeys}]
        /\ MigratingRanges = [self \in TargetSessions |-> NULL]
        /\ TKVOwner = [self \in TargetSessions |-> Ownership(TKVRanges[self], 0)]
        (* Process TargetServer *)
        /\ TargetDecision = FALSE
        /\ pc = [self \in ProcSet |-> CASE self \in SourceSessions -> "InitMigrationSource"
                                        [] self = Source -> "CompleteMigration"
                                        [] self \in TargetSessions -> "InitMigrationTarget"
                                        [] self = Target -> "StartCheckpointing"
                                        [] self = Zookeeper -> "Init2PC"]

InitMigrationSource(self) == /\ pc[self] = "InitMigrationSource"
                             /\ ServerState' = [ServerState EXCEPT ![self] = PrepareToSample]
                             /\ pc' = [pc EXCEPT ![self] = "SampleRecords"]
                             /\ UNCHANGED << TransferComplete, SViewNumber, 
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
                                             SKVRanges, SKVOwner, 
                                             SourceDecision, TKVRanges, 
                                             MigratingRanges, TKVOwner, 
                                             TargetDecision >>

SampleRecords(self) == /\ pc[self] = "SampleRecords"
                       /\ ServerState' = [ServerState EXCEPT ![self] = Sampling]
                       /\ pc' = [pc EXCEPT ![self] = "ViewChange"]
                       /\ UNCHANGED << TransferComplete, SViewNumber, 
                                       TViewNumber, PrepForTransferRPC, 
                                       UpdateSourceOwnership, 
                                       UpdateTargetOwnership, TakeOwnershipRPC, 
                                       TransferCompleteRPC, 
                                       ACKTransferCompleteRPC, SourceACK, 
                                       TargetACK, MigrationServers, 
                                       MigrationViewNumbers, MigrationRange, 
                                       ServerVote, Start2PC, SourcePrepare2PC, 
                                       TargetPrepare2PC, Decision2PC, 
                                       SKVRanges, SKVOwner, SourceDecision, 
                                       TKVRanges, MigratingRanges, TKVOwner, 
                                       TargetDecision >>

ViewChange(self) == /\ pc[self] = "ViewChange"
                    /\ ServerState' = [ServerState EXCEPT ![self] = PrepareForTransfer]
                    /\ SViewNumber' = [SViewNumber EXCEPT ![self] = SViewNumber[self] + 1]
                    /\ SKVOwner' = [SKVOwner EXCEPT ![self] = Ownership(SKVRanges[self] \ {KeysToMigrate}, SViewNumber'[self])]
                    /\ IF ~PrepForTransferRPC
                          THEN /\ MigrationRange' = KeysToMigrate
                               /\ MigrationServers' = Append(MigrationServers, Source)
                               /\ MigrationViewNumbers' = Append(MigrationViewNumbers, SViewNumber'[self])
                               /\ PrepForTransferRPC' = TRUE
                          ELSE /\ TRUE
                               /\ UNCHANGED << PrepForTransferRPC, 
                                               MigrationServers, 
                                               MigrationViewNumbers, 
                                               MigrationRange >>
                    /\ pc' = [pc EXCEPT ![self] = "TransferOwnership"]
                    /\ UNCHANGED << TransferComplete, TViewNumber, 
                                    UpdateSourceOwnership, 
                                    UpdateTargetOwnership, TakeOwnershipRPC, 
                                    TransferCompleteRPC, 
                                    ACKTransferCompleteRPC, SourceACK, 
                                    TargetACK, ServerVote, Start2PC, 
                                    SourcePrepare2PC, TargetPrepare2PC, 
                                    Decision2PC, SKVRanges, SourceDecision, 
                                    TKVRanges, MigratingRanges, TKVOwner, 
                                    TargetDecision >>

TransferOwnership(self) == /\ pc[self] = "TransferOwnership"
                           /\ ServerState' = [ServerState EXCEPT ![self] = TransferingOwnership]
                           /\ pc' = [pc EXCEPT ![self] = "CompleteRequests"]
                           /\ UNCHANGED << TransferComplete, SViewNumber, 
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
                                           SKVRanges, SKVOwner, SourceDecision, 
                                           TKVRanges, MigratingRanges, 
                                           TKVOwner, TargetDecision >>

CompleteRequests(self) == /\ pc[self] = "CompleteRequests"
                          /\ ServerState' = [ServerState EXCEPT ![self] = WaitForPending]
                          /\ IF ~TakeOwnershipRPC
                                THEN /\ \E sessions \in SourceSessions \ {self}:
                                          ServerState'[sessions] = TransferingOwnership
                                     /\ TakeOwnershipRPC' = TRUE
                                ELSE /\ TRUE
                                     /\ UNCHANGED TakeOwnershipRPC
                          /\ pc' = [pc EXCEPT ![self] = "MoveData"]
                          /\ UNCHANGED << TransferComplete, SViewNumber, 
                                          TViewNumber, PrepForTransferRPC, 
                                          UpdateSourceOwnership, 
                                          UpdateTargetOwnership, 
                                          TransferCompleteRPC, 
                                          ACKTransferCompleteRPC, SourceACK, 
                                          TargetACK, MigrationServers, 
                                          MigrationViewNumbers, MigrationRange, 
                                          ServerVote, Start2PC, 
                                          SourcePrepare2PC, TargetPrepare2PC, 
                                          Decision2PC, SKVRanges, SKVOwner, 
                                          SourceDecision, TKVRanges, 
                                          MigratingRanges, TKVOwner, 
                                          TargetDecision >>

MoveData(self) == /\ pc[self] = "MoveData"
                  /\ SKVRanges' = [SKVRanges EXCEPT ![self] = SKVRanges[self] \ {KeysToMigrate}]
                  /\ ServerState' = [ServerState EXCEPT ![self] = MoveDataToTarget]
                  /\ IF ~TransferComplete
                        THEN /\ \E sessions \in SourceSessions \ {self}:
                                  ServerState'[sessions] = WaitForPending
                             /\ TransferComplete' = TRUE
                        ELSE /\ TRUE
                             /\ UNCHANGED TransferComplete
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << SViewNumber, TViewNumber, PrepForTransferRPC, 
                                  UpdateSourceOwnership, UpdateTargetOwnership, 
                                  TakeOwnershipRPC, TransferCompleteRPC, 
                                  ACKTransferCompleteRPC, SourceACK, TargetACK, 
                                  MigrationServers, MigrationViewNumbers, 
                                  MigrationRange, ServerVote, Start2PC, 
                                  SourcePrepare2PC, TargetPrepare2PC, 
                                  Decision2PC, SKVOwner, SourceDecision, 
                                  TKVRanges, MigratingRanges, TKVOwner, 
                                  TargetDecision >>

SourceProcess(self) == InitMigrationSource(self) \/ SampleRecords(self)
                          \/ ViewChange(self) \/ TransferOwnership(self)
                          \/ CompleteRequests(self) \/ MoveData(self)

CompleteMigration == /\ pc[Source] = "CompleteMigration"
                     /\ TransferComplete
                     /\ \E s \in SourceSessions:
                          ServerState' = [ServerState EXCEPT ![s] = WaitForCheckpoint]
                     /\ TransferCompleteRPC' = TRUE
                     /\ pc' = [pc EXCEPT ![Source] = "StartCommit"]
                     /\ UNCHANGED << TransferComplete, SViewNumber, 
                                     TViewNumber, PrepForTransferRPC, 
                                     UpdateSourceOwnership, 
                                     UpdateTargetOwnership, TakeOwnershipRPC, 
                                     ACKTransferCompleteRPC, SourceACK, 
                                     TargetACK, MigrationServers, 
                                     MigrationViewNumbers, MigrationRange, 
                                     ServerVote, Start2PC, SourcePrepare2PC, 
                                     TargetPrepare2PC, Decision2PC, SKVRanges, 
                                     SKVOwner, SourceDecision, TKVRanges, 
                                     MigratingRanges, TKVOwner, TargetDecision >>

StartCommit == /\ pc[Source] = "StartCommit"
               /\ ACKTransferCompleteRPC
               /\ Start2PC' = TRUE
               /\ pc' = [pc EXCEPT ![Source] = "WaitForPrepare"]
               /\ UNCHANGED << ServerState, TransferComplete, SViewNumber, 
                               TViewNumber, PrepForTransferRPC, 
                               UpdateSourceOwnership, UpdateTargetOwnership, 
                               TakeOwnershipRPC, TransferCompleteRPC, 
                               ACKTransferCompleteRPC, SourceACK, TargetACK, 
                               MigrationServers, MigrationViewNumbers, 
                               MigrationRange, ServerVote, SourcePrepare2PC, 
                               TargetPrepare2PC, Decision2PC, SKVRanges, 
                               SKVOwner, SourceDecision, TKVRanges, 
                               MigratingRanges, TKVOwner, TargetDecision >>

WaitForPrepare == /\ pc[Source] = "WaitForPrepare"
                  /\ SourcePrepare2PC
                  /\ \/ /\ SourceACK' = TRUE
                        /\ \E s \in SourceSessions:
                             ServerState' = [ServerState EXCEPT ![s] = 2PCPrepare]
                        /\ UNCHANGED SourceDecision
                     \/ /\ SourceACK' = FALSE
                        /\ \E s \in SourceSessions:
                             ServerState' = [ServerState EXCEPT ![s] = 2PCAbort]
                        /\ SourceDecision' = TRUE
                  /\ pc' = [pc EXCEPT ![Source] = "WaitForDecisionSource"]
                  /\ UNCHANGED << TransferComplete, SViewNumber, TViewNumber, 
                                  PrepForTransferRPC, UpdateSourceOwnership, 
                                  UpdateTargetOwnership, TakeOwnershipRPC, 
                                  TransferCompleteRPC, ACKTransferCompleteRPC, 
                                  TargetACK, MigrationServers, 
                                  MigrationViewNumbers, MigrationRange, 
                                  ServerVote, Start2PC, SourcePrepare2PC, 
                                  TargetPrepare2PC, Decision2PC, SKVRanges, 
                                  SKVOwner, TKVRanges, MigratingRanges, 
                                  TKVOwner, TargetDecision >>

WaitForDecisionSource == /\ pc[Source] = "WaitForDecisionSource"
                         /\ IF ~SourceDecision
                               THEN /\ Decision2PC
                                    /\ IF ServerVote[Target]
                                          THEN /\ \E s \in SourceSessions:
                                                    ServerState' = [ServerState EXCEPT ![s] = 2PCCommit]
                                          ELSE /\ \E s \in SourceSessions:
                                                    ServerState' = [ServerState EXCEPT ![s] = 2PCAbort]
                               ELSE /\ TRUE
                                    /\ UNCHANGED ServerState
                         /\ pc' = [pc EXCEPT ![Source] = "Done"]
                         /\ UNCHANGED << TransferComplete, SViewNumber, 
                                         TViewNumber, PrepForTransferRPC, 
                                         UpdateSourceOwnership, 
                                         UpdateTargetOwnership, 
                                         TakeOwnershipRPC, TransferCompleteRPC, 
                                         ACKTransferCompleteRPC, SourceACK, 
                                         TargetACK, MigrationServers, 
                                         MigrationViewNumbers, MigrationRange, 
                                         ServerVote, Start2PC, 
                                         SourcePrepare2PC, TargetPrepare2PC, 
                                         Decision2PC, SKVRanges, SKVOwner, 
                                         SourceDecision, TKVRanges, 
                                         MigratingRanges, TKVOwner, 
                                         TargetDecision >>

SourceServer == CompleteMigration \/ StartCommit \/ WaitForPrepare
                   \/ WaitForDecisionSource

InitMigrationTarget(self) == /\ pc[self] = "InitMigrationTarget"
                             /\ PrepForTransferRPC
                             /\ ServerState' = [ServerState EXCEPT ![self] = PrepareForMigration]
                             /\ TViewNumber' = [TViewNumber EXCEPT ![self] = TViewNumber[self] + 1]
                             /\ MigrationServers' = Append(MigrationServers, Target)
                             /\ MigrationViewNumbers' = Append(MigrationViewNumbers, TViewNumber'[self])
                             /\ MigratingRanges' = [MigratingRanges EXCEPT ![self] = MigrationRange]
                             /\ TKVRanges' = [TKVRanges EXCEPT ![self] = TKVRanges[self] \union {MigratingRanges'[self]}]
                             /\ TKVOwner' = [TKVOwner EXCEPT ![self] = Ownership(TKVRanges'[self], TViewNumber'[self])]
                             /\ pc' = [pc EXCEPT ![self] = "TakeOwnership"]
                             /\ UNCHANGED << TransferComplete, SViewNumber, 
                                             PrepForTransferRPC, 
                                             UpdateSourceOwnership, 
                                             UpdateTargetOwnership, 
                                             TakeOwnershipRPC, 
                                             TransferCompleteRPC, 
                                             ACKTransferCompleteRPC, SourceACK, 
                                             TargetACK, MigrationRange, 
                                             ServerVote, Start2PC, 
                                             SourcePrepare2PC, 
                                             TargetPrepare2PC, Decision2PC, 
                                             SKVRanges, SKVOwner, 
                                             SourceDecision, TargetDecision >>

TakeOwnership(self) == /\ pc[self] = "TakeOwnership"
                       /\ TakeOwnershipRPC
                       /\ ServerState' = [ServerState EXCEPT ![self] = ReceivingData]
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << TransferComplete, SViewNumber, 
                                       TViewNumber, PrepForTransferRPC, 
                                       UpdateSourceOwnership, 
                                       UpdateTargetOwnership, TakeOwnershipRPC, 
                                       TransferCompleteRPC, 
                                       ACKTransferCompleteRPC, SourceACK, 
                                       TargetACK, MigrationServers, 
                                       MigrationViewNumbers, MigrationRange, 
                                       ServerVote, Start2PC, SourcePrepare2PC, 
                                       TargetPrepare2PC, Decision2PC, 
                                       SKVRanges, SKVOwner, SourceDecision, 
                                       TKVRanges, MigratingRanges, TKVOwner, 
                                       TargetDecision >>

TargetProcess(self) == InitMigrationTarget(self) \/ TakeOwnership(self)

StartCheckpointing == /\ pc[Target] = "StartCheckpointing"
                      /\ TransferCompleteRPC
                      /\ \E s \in TargetSessions:
                           ServerState' = [ServerState EXCEPT ![s] = Checkpointing]
                      /\ ACKTransferCompleteRPC' = TRUE
                      /\ pc' = [pc EXCEPT ![Target] = "WaitFor2PC"]
                      /\ UNCHANGED << TransferComplete, SViewNumber, 
                                      TViewNumber, PrepForTransferRPC, 
                                      UpdateSourceOwnership, 
                                      UpdateTargetOwnership, TakeOwnershipRPC, 
                                      TransferCompleteRPC, SourceACK, 
                                      TargetACK, MigrationServers, 
                                      MigrationViewNumbers, MigrationRange, 
                                      ServerVote, Start2PC, SourcePrepare2PC, 
                                      TargetPrepare2PC, Decision2PC, SKVRanges, 
                                      SKVOwner, SourceDecision, TKVRanges, 
                                      MigratingRanges, TKVOwner, 
                                      TargetDecision >>

WaitFor2PC == /\ pc[Target] = "WaitFor2PC"
              /\ TargetPrepare2PC
              /\ \/ /\ TargetACK' = TRUE
                    /\ \E s \in TargetSessions:
                         ServerState' = [ServerState EXCEPT ![s] = 2PCPrepare]
                    /\ UNCHANGED TargetDecision
                 \/ /\ TargetACK' = FALSE
                    /\ \E s \in TargetSessions:
                         ServerState' = [ServerState EXCEPT ![s] = 2PCAbort]
                    /\ TargetDecision' = TRUE
              /\ pc' = [pc EXCEPT ![Target] = "WaitForDecisionTarget"]
              /\ UNCHANGED << TransferComplete, SViewNumber, TViewNumber, 
                              PrepForTransferRPC, UpdateSourceOwnership, 
                              UpdateTargetOwnership, TakeOwnershipRPC, 
                              TransferCompleteRPC, ACKTransferCompleteRPC, 
                              SourceACK, MigrationServers, 
                              MigrationViewNumbers, MigrationRange, ServerVote, 
                              Start2PC, SourcePrepare2PC, TargetPrepare2PC, 
                              Decision2PC, SKVRanges, SKVOwner, SourceDecision, 
                              TKVRanges, MigratingRanges, TKVOwner >>

WaitForDecisionTarget == /\ pc[Target] = "WaitForDecisionTarget"
                         /\ IF ~TargetDecision
                               THEN /\ Decision2PC
                                    /\ IF ServerVote[Source]
                                          THEN /\ \E s \in TargetSessions:
                                                    ServerState' = [ServerState EXCEPT ![s] = 2PCCommit]
                                          ELSE /\ \E s \in TargetSessions:
                                                    ServerState' = [ServerState EXCEPT ![s] = 2PCAbort]
                               ELSE /\ TRUE
                                    /\ UNCHANGED ServerState
                         /\ pc' = [pc EXCEPT ![Target] = "Done"]
                         /\ UNCHANGED << TransferComplete, SViewNumber, 
                                         TViewNumber, PrepForTransferRPC, 
                                         UpdateSourceOwnership, 
                                         UpdateTargetOwnership, 
                                         TakeOwnershipRPC, TransferCompleteRPC, 
                                         ACKTransferCompleteRPC, SourceACK, 
                                         TargetACK, MigrationServers, 
                                         MigrationViewNumbers, MigrationRange, 
                                         ServerVote, Start2PC, 
                                         SourcePrepare2PC, TargetPrepare2PC, 
                                         Decision2PC, SKVRanges, SKVOwner, 
                                         SourceDecision, TKVRanges, 
                                         MigratingRanges, TKVOwner, 
                                         TargetDecision >>

TargetServer == StartCheckpointing \/ WaitFor2PC \/ WaitForDecisionTarget

Init2PC == /\ pc[Zookeeper] = "Init2PC"
           /\ Start2PC
           /\ SourcePrepare2PC' = TRUE
           /\ TargetPrepare2PC' = TRUE
           /\ pc' = [pc EXCEPT ![Zookeeper] = "CompletionDecision"]
           /\ UNCHANGED << ServerState, TransferComplete, SViewNumber, 
                           TViewNumber, PrepForTransferRPC, 
                           UpdateSourceOwnership, UpdateTargetOwnership, 
                           TakeOwnershipRPC, TransferCompleteRPC, 
                           ACKTransferCompleteRPC, SourceACK, TargetACK, 
                           MigrationServers, MigrationViewNumbers, 
                           MigrationRange, ServerVote, Start2PC, Decision2PC, 
                           SKVRanges, SKVOwner, SourceDecision, TKVRanges, 
                           MigratingRanges, TKVOwner, TargetDecision >>

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
                      /\ Decision2PC' = TRUE
                      /\ pc' = [pc EXCEPT ![Zookeeper] = "Done"]
                      /\ UNCHANGED << ServerState, TransferComplete, 
                                      SViewNumber, TViewNumber, 
                                      PrepForTransferRPC, 
                                      UpdateSourceOwnership, 
                                      UpdateTargetOwnership, TakeOwnershipRPC, 
                                      TransferCompleteRPC, 
                                      ACKTransferCompleteRPC, SourceACK, 
                                      TargetACK, MigrationServers, 
                                      MigrationViewNumbers, MigrationRange, 
                                      Start2PC, SourcePrepare2PC, 
                                      TargetPrepare2PC, SKVRanges, SKVOwner, 
                                      SourceDecision, TKVRanges, 
                                      MigratingRanges, TKVOwner, 
                                      TargetDecision >>

CoordinatorProcess == Init2PC \/ CompletionDecision

Next == SourceServer \/ TargetServer \/ CoordinatorProcess
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

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Thu Feb 21 14:53:09 MST 2019 by aarushi
\* Created Thu Jan 17 10:53:34 MST 2019 by aarushi
