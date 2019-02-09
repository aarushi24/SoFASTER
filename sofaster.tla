------------------------------ MODULE sofaster ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Source, Target, Zookeeper, SourceSessions, TargetSessions, NULL, PrepareToSample, Sampling, PrepareForTransfer, TransferingOwnership, WaitForPending, MoveDataToTarget, PrepareForMigration, ReceivingData, WaitForCheckpoint, Checkpointing, 2PCCommit, 2PCPrepare, 2PCAbort, SourceKeys, TargetKeys, KeysToMigrate 

Ownership(kvset, view) == [kv \in kvset |-> view]

SetServerState == [s \in SourceSessions \union TargetSessions |-> NULL]

SetViewNumber(ServerSessions) == [s \in ServerSessions |-> 0]

(*--algorithm sofaster
variables
    ServerState = SetServerState,
    SViewNumber = SetViewNumber(SourceSessions),
    TViewNumber = SetViewNumber(TargetSessions),
    \*OwnershipInfo = [Source |-> {0, {SourceKeys, KeysToMigrate}}, Target |-> {0, {TargetKeys}}], \* Zookeeper state
    ServerVote = [Source |-> NULL, Target |-> NULL], \* Vote recorded at Zookeeper
    MigrationRange = NULL,
    TransferComplete = FALSE,
    PrepForTransferRPC = FALSE,
    TakeOwnershipRPC = FALSE,
    TransferCompleteRPC = FALSE,
    ACKTransferCompleteRPC = FALSE,
    Start2PC = FALSE,
    SourcePrepare2PC = FALSE,
    TargetPrepare2PC = FALSE,
    \*SourceACK = FALSE,
    \*TargetACK = FALSE,
    \*SourceCommit = FALSE,
    \*TargetCommit = FALSE;

(*define \* invariants
    \* Views and their actions are linearizable
    \* No server can process requests it doesn't own
    \* Each client eventually gets the correct server
    \* No key is lost - before migration the source owns KeysToMigrate and after KeysToMigrate is owned by either owned by Source or Target
    \* No key has overlapping ownership - KeysToMigrate are never owned by both Source and Target
end define;*)

(*macro UpdateZookeeper(server, viewnum, kvrange) begin
    OwnershipInfo[server] := {viewnum, kvrange};
end macro;
*)
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
        if ~PrepForTransferRPC then
            \* inform target about migrating ranges
            MigrationRange := KeysToMigrate;
            PrepForTransferRPC := TRUE;
        end if;
    TransferOwnership:
        \* TODO: Inform all clients
        ServerState[self] := TransferingOwnership;
    CompleteRequests:
        \* Wait for pending requests to complete
        ServerState[self] := WaitForPending;
        with sessions \in SourceSessions do
            await ServerState[sessions] = WaitForPending
        end with;
        if ~TakeOwnershipRPC then
            TakeOwnershipRPC := TRUE;
        end if;
    MoveData:
        \* Send records
        SKVRanges := SKVRanges \ {KeysToMigrate};
        ServerState[self] := MoveDataToTarget;
        with sessions \in SourceSessions do
            await ServerState[sessions] = MoveDataToTarget
        end with;
        SKVOwner := Ownership(SKVRanges, SViewNumber[self]); \* Which view are the remaining records in?
        if ~TransferComplete then
            TransferComplete := TRUE;
            \*UpdateZookeeper(Source, SViewNumber[self], SKVRanges);
        end if;
end process;

fair process SourceServer = Source
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
            ServerVote[Source] := TRUE;
            with s \in SourceSessions do
                ServerState[s] := 2PCPrepare
            end with;
        or
            ServerVote[Source] := FALSE;
            with s \in SourceSessions do
                ServerState[s] := 2PCAbort
            end with;
            goto SourceAbortMigration;
        end either;
    WaitForDecisionSource:
        await ServerVote[Target] /= NULL;
        if ServerVote[Target] then 
            with s \in SourceSessions do
                ServerState[s] := 2PCCommit
            end with;
        else 
            with s \in SourceSessions do
                ServerState[s] := 2PCAbort
            end with;
        end if;
    SourceAbortMigration:
        skip; 
end process;

fair process TargetProcess \in TargetSessions
    variable TKVRanges = {TargetKeys}, MigratingRanges = NULL, TKVOwner = Ownership(TKVRanges, 0);
  begin
    InitMigrationTarget:
        await PrepForTransferRPC;
        \* TODO: Buffer requests for migrating ranges
        ServerState[self] := PrepareForMigration;
        MigratingRanges := MigrationRange;
        TViewNumber[self] := TViewNumber[self] + 1;
    TakeOwnership:
        await TakeOwnershipRPC;
        \* Enter received records
        TKVRanges := TKVRanges \union {MigratingRanges};
        ServerState[self] := ReceivingData;
        TKVOwner := Ownership(TKVRanges, TViewNumber[self]);
        \*UpdateZookeeper(Target, TViewNumber[self], TKVRanges);
        \* TODO: Start executing requests
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
            ServerVote[Target] := TRUE;
            with s \in TargetSessions do
                ServerState[s] := 2PCPrepare
            end with;
        or
            ServerVote[Target] := FALSE;
            with s \in TargetSessions do
                ServerState[s] := 2PCAbort
            end with;
            goto TargetAbortMigration;
        end either;
    WaitForDecisionTarget:
        await ServerVote[Source] /= NULL;
        if ServerVote[Source] then 
            with s \in TargetSessions do
                ServerState[s] := 2PCCommit
            end with;
        else
            with s \in TargetSessions do
                ServerState[s] := 2PCAbort
            end with;
        end if;
    TargetAbortMigration:
        skip;
end process;

\* Model for client with an active session involved in migration
(*process Clients = ClientSession
    variable CViewNumber;
  begin 
end process;*)

\* TODO: Model timeouts and crashes - when third server is needed
fair process CoordinatorProcess = Zookeeper
    \*variable ;
  begin
    Init2PC:
        await Start2PC;
        SourcePrepare2PC := TRUE;
        TargetPrepare2PC := TRUE;
    CompletionDecision:
        (*await SourceACK \in BOOLEAN /\ TargetACK \in BOOLEAN;
        if SourceACK /\ TargetACK then
            SourceCommit := TRUE;
            TargetCommit := TRUE;
        else
            SourceCommit := FALSE;
            TargetCommit := FALSE;
        end if;
        ServerVote[Source] := SourceCommit || ServerVote[Target] := TargetCommit;
        *)
        either 
            \* one of the servers voted false - is this needed?
            if ServerVote[Source] = FALSE \/ ServerVote[Target] = FALSE then
                ServerVote[Source] := FALSE || ServerVote[Target] := FALSE;
            end if;
        or
            \* another server aborts 
            if ServerVote[Source] /= TRUE \/ ServerVote[Target] /= TRUE then
                ServerVote[Source] := FALSE || ServerVote[Target] := FALSE;
            else
                skip;
            end if;
        end either;
end process; 

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES ServerState, SViewNumber, TViewNumber, ServerVote, MigrationRange, 
          TransferComplete, PrepForTransferRPC, TakeOwnershipRPC, 
          TransferCompleteRPC, ACKTransferCompleteRPC, Start2PC, 
          SourcePrepare2PC, TargetPrepare2PC, pc, SKVRanges, SKVOwner, 
          TKVRanges, MigratingRanges, TKVOwner

vars == << ServerState, SViewNumber, TViewNumber, ServerVote, MigrationRange, 
           TransferComplete, PrepForTransferRPC, TakeOwnershipRPC, 
           TransferCompleteRPC, ACKTransferCompleteRPC, Start2PC, 
           SourcePrepare2PC, TargetPrepare2PC, pc, SKVRanges, SKVOwner, 
           TKVRanges, MigratingRanges, TKVOwner >>

ProcSet == (SourceSessions) \cup {Source} \cup (TargetSessions) \cup {Target} \cup {Zookeeper}

Init == (* Global variables *)
        /\ ServerState = SetServerState
        /\ SViewNumber = SetViewNumber(SourceSessions)
        /\ TViewNumber = SetViewNumber(TargetSessions)
        /\ ServerVote = [Source |-> NULL, Target |-> NULL]
        /\ MigrationRange = NULL
        /\ TransferComplete = FALSE
        /\ PrepForTransferRPC = FALSE
        /\ TakeOwnershipRPC = FALSE
        /\ TransferCompleteRPC = FALSE
        /\ ACKTransferCompleteRPC = FALSE
        /\ Start2PC = FALSE
        /\ SourcePrepare2PC = FALSE
        /\ TargetPrepare2PC = FALSE
        (* Process SourceProcess *)
        /\ SKVRanges = [self \in SourceSessions |-> {SourceKeys, KeysToMigrate}]
        /\ SKVOwner = [self \in SourceSessions |-> Ownership(SKVRanges[self], 0)]
        (* Process TargetProcess *)
        /\ TKVRanges = [self \in TargetSessions |-> {TargetKeys}]
        /\ MigratingRanges = [self \in TargetSessions |-> NULL]
        /\ TKVOwner = [self \in TargetSessions |-> Ownership(TKVRanges[self], 0)]
        /\ pc = [self \in ProcSet |-> CASE self \in SourceSessions -> "InitMigrationSource"
                                        [] self = Source -> "CompleteMigration"
                                        [] self \in TargetSessions -> "InitMigrationTarget"
                                        [] self = Target -> "StartCheckpointing"
                                        [] self = Zookeeper -> "Init2PC"]

InitMigrationSource(self) == /\ pc[self] = "InitMigrationSource"
                             /\ ServerState' = [ServerState EXCEPT ![self] = PrepareToSample]
                             /\ pc' = [pc EXCEPT ![self] = "SampleRecords"]
                             /\ UNCHANGED << SViewNumber, TViewNumber, 
                                             ServerVote, MigrationRange, 
                                             TransferComplete, 
                                             PrepForTransferRPC, 
                                             TakeOwnershipRPC, 
                                             TransferCompleteRPC, 
                                             ACKTransferCompleteRPC, Start2PC, 
                                             SourcePrepare2PC, 
                                             TargetPrepare2PC, SKVRanges, 
                                             SKVOwner, TKVRanges, 
                                             MigratingRanges, TKVOwner >>

SampleRecords(self) == /\ pc[self] = "SampleRecords"
                       /\ ServerState' = [ServerState EXCEPT ![self] = Sampling]
                       /\ pc' = [pc EXCEPT ![self] = "ViewChange"]
                       /\ UNCHANGED << SViewNumber, TViewNumber, ServerVote, 
                                       MigrationRange, TransferComplete, 
                                       PrepForTransferRPC, TakeOwnershipRPC, 
                                       TransferCompleteRPC, 
                                       ACKTransferCompleteRPC, Start2PC, 
                                       SourcePrepare2PC, TargetPrepare2PC, 
                                       SKVRanges, SKVOwner, TKVRanges, 
                                       MigratingRanges, TKVOwner >>

ViewChange(self) == /\ pc[self] = "ViewChange"
                    /\ ServerState' = [ServerState EXCEPT ![self] = PrepareForTransfer]
                    /\ SViewNumber' = [SViewNumber EXCEPT ![self] = SViewNumber[self] + 1]
                    /\ IF ~PrepForTransferRPC
                          THEN /\ MigrationRange' = KeysToMigrate
                               /\ PrepForTransferRPC' = TRUE
                          ELSE /\ TRUE
                               /\ UNCHANGED << MigrationRange, 
                                               PrepForTransferRPC >>
                    /\ pc' = [pc EXCEPT ![self] = "TransferOwnership"]
                    /\ UNCHANGED << TViewNumber, ServerVote, TransferComplete, 
                                    TakeOwnershipRPC, TransferCompleteRPC, 
                                    ACKTransferCompleteRPC, Start2PC, 
                                    SourcePrepare2PC, TargetPrepare2PC, 
                                    SKVRanges, SKVOwner, TKVRanges, 
                                    MigratingRanges, TKVOwner >>

TransferOwnership(self) == /\ pc[self] = "TransferOwnership"
                           /\ ServerState' = [ServerState EXCEPT ![self] = TransferingOwnership]
                           /\ pc' = [pc EXCEPT ![self] = "CompleteRequests"]
                           /\ UNCHANGED << SViewNumber, TViewNumber, 
                                           ServerVote, MigrationRange, 
                                           TransferComplete, 
                                           PrepForTransferRPC, 
                                           TakeOwnershipRPC, 
                                           TransferCompleteRPC, 
                                           ACKTransferCompleteRPC, Start2PC, 
                                           SourcePrepare2PC, TargetPrepare2PC, 
                                           SKVRanges, SKVOwner, TKVRanges, 
                                           MigratingRanges, TKVOwner >>

CompleteRequests(self) == /\ pc[self] = "CompleteRequests"
                          /\ ServerState' = [ServerState EXCEPT ![self] = WaitForPending]
                          /\ \E sessions \in SourceSessions:
                               ServerState'[sessions] = WaitForPending
                          /\ IF ~TakeOwnershipRPC
                                THEN /\ TakeOwnershipRPC' = TRUE
                                ELSE /\ TRUE
                                     /\ UNCHANGED TakeOwnershipRPC
                          /\ pc' = [pc EXCEPT ![self] = "MoveData"]
                          /\ UNCHANGED << SViewNumber, TViewNumber, ServerVote, 
                                          MigrationRange, TransferComplete, 
                                          PrepForTransferRPC, 
                                          TransferCompleteRPC, 
                                          ACKTransferCompleteRPC, Start2PC, 
                                          SourcePrepare2PC, TargetPrepare2PC, 
                                          SKVRanges, SKVOwner, TKVRanges, 
                                          MigratingRanges, TKVOwner >>

MoveData(self) == /\ pc[self] = "MoveData"
                  /\ SKVRanges' = [SKVRanges EXCEPT ![self] = SKVRanges[self] \ {KeysToMigrate}]
                  /\ ServerState' = [ServerState EXCEPT ![self] = MoveDataToTarget]
                  /\ \E sessions \in SourceSessions:
                       ServerState'[sessions] = MoveDataToTarget
                  /\ SKVOwner' = [SKVOwner EXCEPT ![self] = Ownership(SKVRanges'[self], SViewNumber[self])]
                  /\ IF ~TransferComplete
                        THEN /\ TransferComplete' = TRUE
                        ELSE /\ TRUE
                             /\ UNCHANGED TransferComplete
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << SViewNumber, TViewNumber, ServerVote, 
                                  MigrationRange, PrepForTransferRPC, 
                                  TakeOwnershipRPC, TransferCompleteRPC, 
                                  ACKTransferCompleteRPC, Start2PC, 
                                  SourcePrepare2PC, TargetPrepare2PC, 
                                  TKVRanges, MigratingRanges, TKVOwner >>

SourceProcess(self) == InitMigrationSource(self) \/ SampleRecords(self)
                          \/ ViewChange(self) \/ TransferOwnership(self)
                          \/ CompleteRequests(self) \/ MoveData(self)

CompleteMigration == /\ pc[Source] = "CompleteMigration"
                     /\ TransferComplete
                     /\ \E s \in SourceSessions:
                          ServerState' = [ServerState EXCEPT ![s] = WaitForCheckpoint]
                     /\ TransferCompleteRPC' = TRUE
                     /\ pc' = [pc EXCEPT ![Source] = "StartCommit"]
                     /\ UNCHANGED << SViewNumber, TViewNumber, ServerVote, 
                                     MigrationRange, TransferComplete, 
                                     PrepForTransferRPC, TakeOwnershipRPC, 
                                     ACKTransferCompleteRPC, Start2PC, 
                                     SourcePrepare2PC, TargetPrepare2PC, 
                                     SKVRanges, SKVOwner, TKVRanges, 
                                     MigratingRanges, TKVOwner >>

StartCommit == /\ pc[Source] = "StartCommit"
               /\ ACKTransferCompleteRPC
               /\ Start2PC' = TRUE
               /\ pc' = [pc EXCEPT ![Source] = "WaitForPrepare"]
               /\ UNCHANGED << ServerState, SViewNumber, TViewNumber, 
                               ServerVote, MigrationRange, TransferComplete, 
                               PrepForTransferRPC, TakeOwnershipRPC, 
                               TransferCompleteRPC, ACKTransferCompleteRPC, 
                               SourcePrepare2PC, TargetPrepare2PC, SKVRanges, 
                               SKVOwner, TKVRanges, MigratingRanges, TKVOwner >>

WaitForPrepare == /\ pc[Source] = "WaitForPrepare"
                  /\ SourcePrepare2PC
                  /\ \/ /\ ServerVote' = [ServerVote EXCEPT ![Source] = TRUE]
                        /\ \E s \in SourceSessions:
                             ServerState' = [ServerState EXCEPT ![s] = 2PCPrepare]
                        /\ pc' = [pc EXCEPT ![Source] = "WaitForDecisionSource"]
                     \/ /\ ServerVote' = [ServerVote EXCEPT ![Source] = FALSE]
                        /\ \E s \in SourceSessions:
                             ServerState' = [ServerState EXCEPT ![s] = 2PCAbort]
                        /\ pc' = [pc EXCEPT ![Source] = "SourceAbortMigration"]
                  /\ UNCHANGED << SViewNumber, TViewNumber, MigrationRange, 
                                  TransferComplete, PrepForTransferRPC, 
                                  TakeOwnershipRPC, TransferCompleteRPC, 
                                  ACKTransferCompleteRPC, Start2PC, 
                                  SourcePrepare2PC, TargetPrepare2PC, 
                                  SKVRanges, SKVOwner, TKVRanges, 
                                  MigratingRanges, TKVOwner >>

WaitForDecisionSource == /\ pc[Source] = "WaitForDecisionSource"
                         /\ ServerVote[Target] /= NULL
                         /\ IF ServerVote[Target]
                               THEN /\ \E s \in SourceSessions:
                                         ServerState' = [ServerState EXCEPT ![s] = 2PCCommit]
                               ELSE /\ \E s \in SourceSessions:
                                         ServerState' = [ServerState EXCEPT ![s] = 2PCAbort]
                         /\ pc' = [pc EXCEPT ![Source] = "SourceAbortMigration"]
                         /\ UNCHANGED << SViewNumber, TViewNumber, ServerVote, 
                                         MigrationRange, TransferComplete, 
                                         PrepForTransferRPC, TakeOwnershipRPC, 
                                         TransferCompleteRPC, 
                                         ACKTransferCompleteRPC, Start2PC, 
                                         SourcePrepare2PC, TargetPrepare2PC, 
                                         SKVRanges, SKVOwner, TKVRanges, 
                                         MigratingRanges, TKVOwner >>

SourceAbortMigration == /\ pc[Source] = "SourceAbortMigration"
                        /\ TRUE
                        /\ pc' = [pc EXCEPT ![Source] = "Done"]
                        /\ UNCHANGED << ServerState, SViewNumber, TViewNumber, 
                                        ServerVote, MigrationRange, 
                                        TransferComplete, PrepForTransferRPC, 
                                        TakeOwnershipRPC, TransferCompleteRPC, 
                                        ACKTransferCompleteRPC, Start2PC, 
                                        SourcePrepare2PC, TargetPrepare2PC, 
                                        SKVRanges, SKVOwner, TKVRanges, 
                                        MigratingRanges, TKVOwner >>

SourceServer == CompleteMigration \/ StartCommit \/ WaitForPrepare
                   \/ WaitForDecisionSource \/ SourceAbortMigration

InitMigrationTarget(self) == /\ pc[self] = "InitMigrationTarget"
                             /\ PrepForTransferRPC
                             /\ ServerState' = [ServerState EXCEPT ![self] = PrepareForMigration]
                             /\ MigratingRanges' = [MigratingRanges EXCEPT ![self] = MigrationRange]
                             /\ TViewNumber' = [TViewNumber EXCEPT ![self] = TViewNumber[self] + 1]
                             /\ pc' = [pc EXCEPT ![self] = "TakeOwnership"]
                             /\ UNCHANGED << SViewNumber, ServerVote, 
                                             MigrationRange, TransferComplete, 
                                             PrepForTransferRPC, 
                                             TakeOwnershipRPC, 
                                             TransferCompleteRPC, 
                                             ACKTransferCompleteRPC, Start2PC, 
                                             SourcePrepare2PC, 
                                             TargetPrepare2PC, SKVRanges, 
                                             SKVOwner, TKVRanges, TKVOwner >>

TakeOwnership(self) == /\ pc[self] = "TakeOwnership"
                       /\ TakeOwnershipRPC
                       /\ TKVRanges' = [TKVRanges EXCEPT ![self] = TKVRanges[self] \union {MigratingRanges[self]}]
                       /\ ServerState' = [ServerState EXCEPT ![self] = ReceivingData]
                       /\ TKVOwner' = [TKVOwner EXCEPT ![self] = Ownership(TKVRanges'[self], TViewNumber[self])]
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << SViewNumber, TViewNumber, ServerVote, 
                                       MigrationRange, TransferComplete, 
                                       PrepForTransferRPC, TakeOwnershipRPC, 
                                       TransferCompleteRPC, 
                                       ACKTransferCompleteRPC, Start2PC, 
                                       SourcePrepare2PC, TargetPrepare2PC, 
                                       SKVRanges, SKVOwner, MigratingRanges >>

TargetProcess(self) == InitMigrationTarget(self) \/ TakeOwnership(self)

StartCheckpointing == /\ pc[Target] = "StartCheckpointing"
                      /\ TransferCompleteRPC
                      /\ \E s \in TargetSessions:
                           ServerState' = [ServerState EXCEPT ![s] = Checkpointing]
                      /\ ACKTransferCompleteRPC' = TRUE
                      /\ pc' = [pc EXCEPT ![Target] = "WaitFor2PC"]
                      /\ UNCHANGED << SViewNumber, TViewNumber, ServerVote, 
                                      MigrationRange, TransferComplete, 
                                      PrepForTransferRPC, TakeOwnershipRPC, 
                                      TransferCompleteRPC, Start2PC, 
                                      SourcePrepare2PC, TargetPrepare2PC, 
                                      SKVRanges, SKVOwner, TKVRanges, 
                                      MigratingRanges, TKVOwner >>

WaitFor2PC == /\ pc[Target] = "WaitFor2PC"
              /\ TargetPrepare2PC
              /\ \/ /\ ServerVote' = [ServerVote EXCEPT ![Target] = TRUE]
                    /\ \E s \in TargetSessions:
                         ServerState' = [ServerState EXCEPT ![s] = 2PCPrepare]
                    /\ pc' = [pc EXCEPT ![Target] = "WaitForDecisionTarget"]
                 \/ /\ ServerVote' = [ServerVote EXCEPT ![Target] = FALSE]
                    /\ \E s \in TargetSessions:
                         ServerState' = [ServerState EXCEPT ![s] = 2PCAbort]
                    /\ pc' = [pc EXCEPT ![Target] = "TargetAbortMigration"]
              /\ UNCHANGED << SViewNumber, TViewNumber, MigrationRange, 
                              TransferComplete, PrepForTransferRPC, 
                              TakeOwnershipRPC, TransferCompleteRPC, 
                              ACKTransferCompleteRPC, Start2PC, 
                              SourcePrepare2PC, TargetPrepare2PC, SKVRanges, 
                              SKVOwner, TKVRanges, MigratingRanges, TKVOwner >>

WaitForDecisionTarget == /\ pc[Target] = "WaitForDecisionTarget"
                         /\ ServerVote[Source] /= NULL
                         /\ IF ServerVote[Source]
                               THEN /\ \E s \in TargetSessions:
                                         ServerState' = [ServerState EXCEPT ![s] = 2PCCommit]
                               ELSE /\ \E s \in TargetSessions:
                                         ServerState' = [ServerState EXCEPT ![s] = 2PCAbort]
                         /\ pc' = [pc EXCEPT ![Target] = "TargetAbortMigration"]
                         /\ UNCHANGED << SViewNumber, TViewNumber, ServerVote, 
                                         MigrationRange, TransferComplete, 
                                         PrepForTransferRPC, TakeOwnershipRPC, 
                                         TransferCompleteRPC, 
                                         ACKTransferCompleteRPC, Start2PC, 
                                         SourcePrepare2PC, TargetPrepare2PC, 
                                         SKVRanges, SKVOwner, TKVRanges, 
                                         MigratingRanges, TKVOwner >>

TargetAbortMigration == /\ pc[Target] = "TargetAbortMigration"
                        /\ TRUE
                        /\ pc' = [pc EXCEPT ![Target] = "Done"]
                        /\ UNCHANGED << ServerState, SViewNumber, TViewNumber, 
                                        ServerVote, MigrationRange, 
                                        TransferComplete, PrepForTransferRPC, 
                                        TakeOwnershipRPC, TransferCompleteRPC, 
                                        ACKTransferCompleteRPC, Start2PC, 
                                        SourcePrepare2PC, TargetPrepare2PC, 
                                        SKVRanges, SKVOwner, TKVRanges, 
                                        MigratingRanges, TKVOwner >>

TargetServer == StartCheckpointing \/ WaitFor2PC \/ WaitForDecisionTarget
                   \/ TargetAbortMigration

Init2PC == /\ pc[Zookeeper] = "Init2PC"
           /\ Start2PC
           /\ SourcePrepare2PC' = TRUE
           /\ TargetPrepare2PC' = TRUE
           /\ pc' = [pc EXCEPT ![Zookeeper] = "CompletionDecision"]
           /\ UNCHANGED << ServerState, SViewNumber, TViewNumber, ServerVote, 
                           MigrationRange, TransferComplete, 
                           PrepForTransferRPC, TakeOwnershipRPC, 
                           TransferCompleteRPC, ACKTransferCompleteRPC, 
                           Start2PC, SKVRanges, SKVOwner, TKVRanges, 
                           MigratingRanges, TKVOwner >>

CompletionDecision == /\ pc[Zookeeper] = "CompletionDecision"
                      /\ \/ /\ IF ServerVote[Source] = FALSE \/ ServerVote[Target] = FALSE
                                  THEN /\ ServerVote' = [ServerVote EXCEPT ![Source] = FALSE,
                                                                           ![Target] = FALSE]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED ServerVote
                         \/ /\ IF ServerVote[Source] /= TRUE \/ ServerVote[Target] /= TRUE
                                  THEN /\ ServerVote' = [ServerVote EXCEPT ![Source] = FALSE,
                                                                           ![Target] = FALSE]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED ServerVote
                      /\ pc' = [pc EXCEPT ![Zookeeper] = "Done"]
                      /\ UNCHANGED << ServerState, SViewNumber, TViewNumber, 
                                      MigrationRange, TransferComplete, 
                                      PrepForTransferRPC, TakeOwnershipRPC, 
                                      TransferCompleteRPC, 
                                      ACKTransferCompleteRPC, Start2PC, 
                                      SourcePrepare2PC, TargetPrepare2PC, 
                                      SKVRanges, SKVOwner, TKVRanges, 
                                      MigratingRanges, TKVOwner >>

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

\* Migration is atomic - source, target and coordinator are in agreement about result of migration
AtomicMigration ==
    \A s \in SourceSessions \union TargetSessions: <>[](
        \/ 
            /\ ServerState[s] = 2PCCommit 
            /\ ServerVote[Source] 
            /\ ServerVote[Target] 
        \/ 
            /\ ServerState[s] = 2PCAbort 
            /\ ~ServerVote[Source] 
            /\ ~ServerVote[Target]
        )

=============================================================================
\* Modification History
\* Last modified Fri Feb 08 18:19:21 MST 2019 by aarushi
\* Created Thu Jan 17 10:53:34 MST 2019 by aarushi
