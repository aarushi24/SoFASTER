------------------------------ MODULE sofaster ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Zookeeper, SourceSessions, TargetSessions, NULL, PrepareToSample, Sampling, PrepareForTransfer, TransferingOwnership, WaitForPending, MoveDataToTarget, PrepareForMigration, ReceivingData, WaitForCheckpoint, Checkpointing, 2PCCommit, 2PCPrepare, SourceKeys, TargetKeys, KeysToMigrate 

(*--algorithm sofaster
variables
    \*Servers = {Source, Target},
    ServerState = [SourceSessions |-> NULL, TargetSessions |-> NULL],
    SViewNumber = [SourceSessions |-> 0],
    TViewNumber = [TargetSessions |-> 0],
    MigrationRange = NULL,
    PrepForTransferRPC = FALSE,
    TakeOwnershipRPC = FALSE,
    TransferCompleteRPC = FALSE,
    ACKTransferCompleteRPC = FALSE,
    Start2PC = FALSE,
    ServerPrepare2PC = FALSE,
    TargetPrepare2PC = FALSE,
    ServerACK = FALSE,
    TargetACK = FALSE,
    ServerCommit = FALSE,
    TargetCommit = FALSE;
    \*MigrationResult = FALSE;

(*define \* invariants
    \* Migration is atomic - source, target and coordinator are in agreement about result of migration
    \* Views and their actions are linearizable
    \* No server can process requests it doesn't own
    \* Each client eventually gets the correct server
    \* No key is lost - before migration the source owns KeysToMigrate and after KeysToMigrate is owned by either owned by Source or Target
    \* No key has overlapping ownership - KeysToMigrate are never owned by both Source and Target
end define;

*)

\* All local view numbers start at the last CPR checkpoint (0)
\* Keep history of views from the last checkpoint? [key -> [view ranges, client sessions]]; This will be on a per thread basis?

\* remove fair to check crashed states?
fair process SourceProcess \in SourceSessions
    variable SKVRanges = {SourceKeys, KeysToMigrate}, TransferComplete = FALSE;
  begin
    InitMigrationSource: 
        \* Shared latech on mutable records
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
            PrepForTransferRPC := TRUE; \* inform target about migrating ranges
            MigrationRange := KeysToMigrate;
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
        if ~TransferComplete then
            TransferComplete := TRUE;
        end if;
    \* 2PC
    CompleteMigration:
        await TransferComplete;
        ServerState[self] := WaitForCheckpoint;
    StartCommit:
        await ACKTransferCompleteRPC;
        Start2PC := TRUE;
    WaitForPrepare:
        await ServerPrepare2PC;
        ServerACK := TRUE;
        ServerState[self] := 2PCPrepare;
    WaitForDecisionSource:
        await ServerCommit;
        ServerState[self] := 2PCCommit; 
end process;

fair process TargetProcess \in TargetSessions
    variable TKVRanges = {TargetKeys}, MigratingRanges = NULL;
  begin
    InitMigrationTarget:
        await PrepForTransferRPC;
        \* TODO: Buffer requests for migrating ranges
        ServerState[self] := PrepareForMigration;
        MigratingRanges := MigrationRange;
    TakeOwnership:
        await TakeOwnershipRPC;
        \* Enter received records
        TKVRanges := TKVRanges \union {MigratingRanges};
        ServerState[self] := ReceivingData;
        \* TODO: Start executing requests
    \* Checkpointing and 2PC
    StartCheckpointing:
        await TransferCompleteRPC;
        ServerState[self] := Checkpointing;
        ACKTransferCompleteRPC := TRUE;
    WaitFor2PC:
        await TargetPrepare2PC;
        TargetACK := TRUE;
        ServerState[self] := 2PCPrepare;
    WaitForDecisionTarget:
        await TargetCommit;
        ServerState[self] := 2PCCommit;
end process;

(*process Clients
    variable CViewNumber;
  begin 
end process;*)

\* TODO: Model timeouts and crashes
fair process CoordinatorProcess = Zookeeper
    variable ServerReply = [Source |-> NULL, Target |-> NULL];
  begin
    Init2PC:
        await Start2PC;
        ServerPrepare2PC := TRUE;
        TargetPrepare2PC := TRUE;
    CompletionDecision:
        await ServerACK /\ TargetACK;
        ServerCommit := TRUE;
        TargetCommit := TRUE;
        \*MigrationResult := TRUE;
end process; 

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES ServerState, SViewNumber, TViewNumber, MigrationRange, 
          PrepForTransferRPC, TakeOwnershipRPC, TransferCompleteRPC, 
          ACKTransferCompleteRPC, Start2PC, ServerPrepare2PC, 
          TargetPrepare2PC, ServerACK, TargetACK, ServerCommit, TargetCommit, 
          pc, SKVRanges, TransferComplete, TKVRanges, MigratingRanges, 
          ServerReply

vars == << ServerState, SViewNumber, TViewNumber, MigrationRange, 
           PrepForTransferRPC, TakeOwnershipRPC, TransferCompleteRPC, 
           ACKTransferCompleteRPC, Start2PC, ServerPrepare2PC, 
           TargetPrepare2PC, ServerACK, TargetACK, ServerCommit, TargetCommit, 
           pc, SKVRanges, TransferComplete, TKVRanges, MigratingRanges, 
           ServerReply >>

ProcSet == (SourceSessions) \cup (TargetSessions) \cup {Zookeeper}

Init == (* Global variables *)
        /\ ServerState = [SourceSessions |-> NULL, TargetSessions |-> NULL]
        /\ SViewNumber = [SourceSessions |-> 0]
        /\ TViewNumber = [TargetSessions |-> 0]
        /\ MigrationRange = NULL
        /\ PrepForTransferRPC = FALSE
        /\ TakeOwnershipRPC = FALSE
        /\ TransferCompleteRPC = FALSE
        /\ ACKTransferCompleteRPC = FALSE
        /\ Start2PC = FALSE
        /\ ServerPrepare2PC = FALSE
        /\ TargetPrepare2PC = FALSE
        /\ ServerACK = FALSE
        /\ TargetACK = FALSE
        /\ ServerCommit = FALSE
        /\ TargetCommit = FALSE
        (* Process SourceProcess *)
        /\ SKVRanges = [self \in SourceSessions |-> {SourceKeys, KeysToMigrate}]
        /\ TransferComplete = [self \in SourceSessions |-> FALSE]
        (* Process TargetProcess *)
        /\ TKVRanges = [self \in TargetSessions |-> {TargetKeys}]
        /\ MigratingRanges = [self \in TargetSessions |-> NULL]
        (* Process CoordinatorProcess *)
        /\ ServerReply = [Source |-> NULL, Target |-> NULL]
        /\ pc = [self \in ProcSet |-> CASE self \in SourceSessions -> "InitMigrationSource"
                                        [] self \in TargetSessions -> "InitMigrationTarget"
                                        [] self = Zookeeper -> "Init2PC"]

InitMigrationSource(self) == /\ pc[self] = "InitMigrationSource"
                             /\ ServerState' = [ServerState EXCEPT ![self] = PrepareToSample]
                             /\ pc' = [pc EXCEPT ![self] = "SampleRecords"]
                             /\ UNCHANGED << SViewNumber, TViewNumber, 
                                             MigrationRange, 
                                             PrepForTransferRPC, 
                                             TakeOwnershipRPC, 
                                             TransferCompleteRPC, 
                                             ACKTransferCompleteRPC, Start2PC, 
                                             ServerPrepare2PC, 
                                             TargetPrepare2PC, ServerACK, 
                                             TargetACK, ServerCommit, 
                                             TargetCommit, SKVRanges, 
                                             TransferComplete, TKVRanges, 
                                             MigratingRanges, ServerReply >>

SampleRecords(self) == /\ pc[self] = "SampleRecords"
                       /\ ServerState' = [ServerState EXCEPT ![self] = Sampling]
                       /\ pc' = [pc EXCEPT ![self] = "ViewChange"]
                       /\ UNCHANGED << SViewNumber, TViewNumber, 
                                       MigrationRange, PrepForTransferRPC, 
                                       TakeOwnershipRPC, TransferCompleteRPC, 
                                       ACKTransferCompleteRPC, Start2PC, 
                                       ServerPrepare2PC, TargetPrepare2PC, 
                                       ServerACK, TargetACK, ServerCommit, 
                                       TargetCommit, SKVRanges, 
                                       TransferComplete, TKVRanges, 
                                       MigratingRanges, ServerReply >>

ViewChange(self) == /\ pc[self] = "ViewChange"
                    /\ ServerState' = [ServerState EXCEPT ![self] = PrepareForTransfer]
                    /\ SViewNumber' = [SViewNumber EXCEPT ![self] = SViewNumber[self] + 1]
                    /\ IF ~PrepForTransferRPC
                          THEN /\ PrepForTransferRPC' = TRUE
                               /\ MigrationRange' = KeysToMigrate
                          ELSE /\ TRUE
                               /\ UNCHANGED << MigrationRange, 
                                               PrepForTransferRPC >>
                    /\ pc' = [pc EXCEPT ![self] = "TransferOwnership"]
                    /\ UNCHANGED << TViewNumber, TakeOwnershipRPC, 
                                    TransferCompleteRPC, 
                                    ACKTransferCompleteRPC, Start2PC, 
                                    ServerPrepare2PC, TargetPrepare2PC, 
                                    ServerACK, TargetACK, ServerCommit, 
                                    TargetCommit, SKVRanges, TransferComplete, 
                                    TKVRanges, MigratingRanges, ServerReply >>

TransferOwnership(self) == /\ pc[self] = "TransferOwnership"
                           /\ ServerState' = [ServerState EXCEPT ![self] = TransferingOwnership]
                           /\ pc' = [pc EXCEPT ![self] = "CompleteRequests"]
                           /\ UNCHANGED << SViewNumber, TViewNumber, 
                                           MigrationRange, PrepForTransferRPC, 
                                           TakeOwnershipRPC, 
                                           TransferCompleteRPC, 
                                           ACKTransferCompleteRPC, Start2PC, 
                                           ServerPrepare2PC, TargetPrepare2PC, 
                                           ServerACK, TargetACK, ServerCommit, 
                                           TargetCommit, SKVRanges, 
                                           TransferComplete, TKVRanges, 
                                           MigratingRanges, ServerReply >>

CompleteRequests(self) == /\ pc[self] = "CompleteRequests"
                          /\ ServerState' = [ServerState EXCEPT ![self] = WaitForPending]
                          /\ \E sessions \in SourceSessions:
                               ServerState'[sessions] = WaitForPending
                          /\ IF ~TakeOwnershipRPC
                                THEN /\ TakeOwnershipRPC' = TRUE
                                ELSE /\ TRUE
                                     /\ UNCHANGED TakeOwnershipRPC
                          /\ pc' = [pc EXCEPT ![self] = "MoveData"]
                          /\ UNCHANGED << SViewNumber, TViewNumber, 
                                          MigrationRange, PrepForTransferRPC, 
                                          TransferCompleteRPC, 
                                          ACKTransferCompleteRPC, Start2PC, 
                                          ServerPrepare2PC, TargetPrepare2PC, 
                                          ServerACK, TargetACK, ServerCommit, 
                                          TargetCommit, SKVRanges, 
                                          TransferComplete, TKVRanges, 
                                          MigratingRanges, ServerReply >>

MoveData(self) == /\ pc[self] = "MoveData"
                  /\ SKVRanges' = [SKVRanges EXCEPT ![self] = SKVRanges[self] \ {KeysToMigrate}]
                  /\ ServerState' = [ServerState EXCEPT ![self] = MoveDataToTarget]
                  /\ \E sessions \in SourceSessions:
                       ServerState'[sessions] = MoveDataToTarget
                  /\ IF ~TransferComplete[self]
                        THEN /\ TransferComplete' = [TransferComplete EXCEPT ![self] = TRUE]
                        ELSE /\ TRUE
                             /\ UNCHANGED TransferComplete
                  /\ pc' = [pc EXCEPT ![self] = "CompleteMigration"]
                  /\ UNCHANGED << SViewNumber, TViewNumber, MigrationRange, 
                                  PrepForTransferRPC, TakeOwnershipRPC, 
                                  TransferCompleteRPC, ACKTransferCompleteRPC, 
                                  Start2PC, ServerPrepare2PC, TargetPrepare2PC, 
                                  ServerACK, TargetACK, ServerCommit, 
                                  TargetCommit, TKVRanges, MigratingRanges, 
                                  ServerReply >>

CompleteMigration(self) == /\ pc[self] = "CompleteMigration"
                           /\ TransferComplete[self]
                           /\ ServerState' = [ServerState EXCEPT ![self] = WaitForCheckpoint]
                           /\ pc' = [pc EXCEPT ![self] = "StartCommit"]
                           /\ UNCHANGED << SViewNumber, TViewNumber, 
                                           MigrationRange, PrepForTransferRPC, 
                                           TakeOwnershipRPC, 
                                           TransferCompleteRPC, 
                                           ACKTransferCompleteRPC, Start2PC, 
                                           ServerPrepare2PC, TargetPrepare2PC, 
                                           ServerACK, TargetACK, ServerCommit, 
                                           TargetCommit, SKVRanges, 
                                           TransferComplete, TKVRanges, 
                                           MigratingRanges, ServerReply >>

StartCommit(self) == /\ pc[self] = "StartCommit"
                     /\ ACKTransferCompleteRPC
                     /\ Start2PC' = TRUE
                     /\ pc' = [pc EXCEPT ![self] = "WaitForPrepare"]
                     /\ UNCHANGED << ServerState, SViewNumber, TViewNumber, 
                                     MigrationRange, PrepForTransferRPC, 
                                     TakeOwnershipRPC, TransferCompleteRPC, 
                                     ACKTransferCompleteRPC, ServerPrepare2PC, 
                                     TargetPrepare2PC, ServerACK, TargetACK, 
                                     ServerCommit, TargetCommit, SKVRanges, 
                                     TransferComplete, TKVRanges, 
                                     MigratingRanges, ServerReply >>

WaitForPrepare(self) == /\ pc[self] = "WaitForPrepare"
                        /\ ServerPrepare2PC
                        /\ ServerACK' = TRUE
                        /\ ServerState' = [ServerState EXCEPT ![self] = 2PCPrepare]
                        /\ pc' = [pc EXCEPT ![self] = "WaitForDecisionSource"]
                        /\ UNCHANGED << SViewNumber, TViewNumber, 
                                        MigrationRange, PrepForTransferRPC, 
                                        TakeOwnershipRPC, TransferCompleteRPC, 
                                        ACKTransferCompleteRPC, Start2PC, 
                                        ServerPrepare2PC, TargetPrepare2PC, 
                                        TargetACK, ServerCommit, TargetCommit, 
                                        SKVRanges, TransferComplete, TKVRanges, 
                                        MigratingRanges, ServerReply >>

WaitForDecisionSource(self) == /\ pc[self] = "WaitForDecisionSource"
                               /\ ServerCommit
                               /\ ServerState' = [ServerState EXCEPT ![self] = 2PCCommit]
                               /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << SViewNumber, TViewNumber, 
                                               MigrationRange, 
                                               PrepForTransferRPC, 
                                               TakeOwnershipRPC, 
                                               TransferCompleteRPC, 
                                               ACKTransferCompleteRPC, 
                                               Start2PC, ServerPrepare2PC, 
                                               TargetPrepare2PC, ServerACK, 
                                               TargetACK, ServerCommit, 
                                               TargetCommit, SKVRanges, 
                                               TransferComplete, TKVRanges, 
                                               MigratingRanges, ServerReply >>

SourceProcess(self) == InitMigrationSource(self) \/ SampleRecords(self)
                          \/ ViewChange(self) \/ TransferOwnership(self)
                          \/ CompleteRequests(self) \/ MoveData(self)
                          \/ CompleteMigration(self) \/ StartCommit(self)
                          \/ WaitForPrepare(self)
                          \/ WaitForDecisionSource(self)

InitMigrationTarget(self) == /\ pc[self] = "InitMigrationTarget"
                             /\ PrepForTransferRPC
                             /\ ServerState' = [ServerState EXCEPT ![self] = PrepareForMigration]
                             /\ MigratingRanges' = [MigratingRanges EXCEPT ![self] = MigrationRange]
                             /\ pc' = [pc EXCEPT ![self] = "TakeOwnership"]
                             /\ UNCHANGED << SViewNumber, TViewNumber, 
                                             MigrationRange, 
                                             PrepForTransferRPC, 
                                             TakeOwnershipRPC, 
                                             TransferCompleteRPC, 
                                             ACKTransferCompleteRPC, Start2PC, 
                                             ServerPrepare2PC, 
                                             TargetPrepare2PC, ServerACK, 
                                             TargetACK, ServerCommit, 
                                             TargetCommit, SKVRanges, 
                                             TransferComplete, TKVRanges, 
                                             ServerReply >>

TakeOwnership(self) == /\ pc[self] = "TakeOwnership"
                       /\ TakeOwnershipRPC
                       /\ TKVRanges' = [TKVRanges EXCEPT ![self] = TKVRanges[self] \union {MigratingRanges[self]}]
                       /\ ServerState' = [ServerState EXCEPT ![self] = ReceivingData]
                       /\ pc' = [pc EXCEPT ![self] = "StartCheckpointing"]
                       /\ UNCHANGED << SViewNumber, TViewNumber, 
                                       MigrationRange, PrepForTransferRPC, 
                                       TakeOwnershipRPC, TransferCompleteRPC, 
                                       ACKTransferCompleteRPC, Start2PC, 
                                       ServerPrepare2PC, TargetPrepare2PC, 
                                       ServerACK, TargetACK, ServerCommit, 
                                       TargetCommit, SKVRanges, 
                                       TransferComplete, MigratingRanges, 
                                       ServerReply >>

StartCheckpointing(self) == /\ pc[self] = "StartCheckpointing"
                            /\ TransferCompleteRPC
                            /\ ServerState' = [ServerState EXCEPT ![self] = Checkpointing]
                            /\ ACKTransferCompleteRPC' = TRUE
                            /\ pc' = [pc EXCEPT ![self] = "WaitFor2PC"]
                            /\ UNCHANGED << SViewNumber, TViewNumber, 
                                            MigrationRange, PrepForTransferRPC, 
                                            TakeOwnershipRPC, 
                                            TransferCompleteRPC, Start2PC, 
                                            ServerPrepare2PC, TargetPrepare2PC, 
                                            ServerACK, TargetACK, ServerCommit, 
                                            TargetCommit, SKVRanges, 
                                            TransferComplete, TKVRanges, 
                                            MigratingRanges, ServerReply >>

WaitFor2PC(self) == /\ pc[self] = "WaitFor2PC"
                    /\ TargetPrepare2PC
                    /\ TargetACK' = TRUE
                    /\ ServerState' = [ServerState EXCEPT ![self] = 2PCPrepare]
                    /\ pc' = [pc EXCEPT ![self] = "WaitForDecisionTarget"]
                    /\ UNCHANGED << SViewNumber, TViewNumber, MigrationRange, 
                                    PrepForTransferRPC, TakeOwnershipRPC, 
                                    TransferCompleteRPC, 
                                    ACKTransferCompleteRPC, Start2PC, 
                                    ServerPrepare2PC, TargetPrepare2PC, 
                                    ServerACK, ServerCommit, TargetCommit, 
                                    SKVRanges, TransferComplete, TKVRanges, 
                                    MigratingRanges, ServerReply >>

WaitForDecisionTarget(self) == /\ pc[self] = "WaitForDecisionTarget"
                               /\ TargetCommit
                               /\ ServerState' = [ServerState EXCEPT ![self] = 2PCCommit]
                               /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << SViewNumber, TViewNumber, 
                                               MigrationRange, 
                                               PrepForTransferRPC, 
                                               TakeOwnershipRPC, 
                                               TransferCompleteRPC, 
                                               ACKTransferCompleteRPC, 
                                               Start2PC, ServerPrepare2PC, 
                                               TargetPrepare2PC, ServerACK, 
                                               TargetACK, ServerCommit, 
                                               TargetCommit, SKVRanges, 
                                               TransferComplete, TKVRanges, 
                                               MigratingRanges, ServerReply >>

TargetProcess(self) == InitMigrationTarget(self) \/ TakeOwnership(self)
                          \/ StartCheckpointing(self) \/ WaitFor2PC(self)
                          \/ WaitForDecisionTarget(self)

Init2PC == /\ pc[Zookeeper] = "Init2PC"
           /\ Start2PC
           /\ ServerPrepare2PC' = TRUE
           /\ TargetPrepare2PC' = TRUE
           /\ pc' = [pc EXCEPT ![Zookeeper] = "CompletionDecision"]
           /\ UNCHANGED << ServerState, SViewNumber, TViewNumber, 
                           MigrationRange, PrepForTransferRPC, 
                           TakeOwnershipRPC, TransferCompleteRPC, 
                           ACKTransferCompleteRPC, Start2PC, ServerACK, 
                           TargetACK, ServerCommit, TargetCommit, SKVRanges, 
                           TransferComplete, TKVRanges, MigratingRanges, 
                           ServerReply >>

CompletionDecision == /\ pc[Zookeeper] = "CompletionDecision"
                      /\ ServerACK /\ TargetACK
                      /\ ServerCommit' = TRUE
                      /\ TargetCommit' = TRUE
                      /\ pc' = [pc EXCEPT ![Zookeeper] = "Done"]
                      /\ UNCHANGED << ServerState, SViewNumber, TViewNumber, 
                                      MigrationRange, PrepForTransferRPC, 
                                      TakeOwnershipRPC, TransferCompleteRPC, 
                                      ACKTransferCompleteRPC, Start2PC, 
                                      ServerPrepare2PC, TargetPrepare2PC, 
                                      ServerACK, TargetACK, SKVRanges, 
                                      TransferComplete, TKVRanges, 
                                      MigratingRanges, ServerReply >>

CoordinatorProcess == Init2PC \/ CompletionDecision

Next == CoordinatorProcess
           \/ (\E self \in SourceSessions: SourceProcess(self))
           \/ (\E self \in TargetSessions: TargetProcess(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in SourceSessions : WF_vars(SourceProcess(self))
        /\ \A self \in TargetSessions : WF_vars(TargetProcess(self))
        /\ WF_vars(CoordinatorProcess)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Feb 04 16:19:40 MST 2019 by aarushi
\* Created Thu Jan 17 10:53:34 MST 2019 by aarushi
