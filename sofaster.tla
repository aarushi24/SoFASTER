------------------------------ MODULE sofaster ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Source, Target, Zookeeper, SourceSessions, TargetSessions, NULL, PrepareToSample, Sampling, PrepareForTransfer, TransferingOwnership, WaitForPending, MoveDataToTarget, PrepareForMigration, ReceivingData, WaitForCheckpoint, Checkpointing, 2PCCommit, 2PCPrepare, SourceKeys, TargetKeys, KeysToMigrate 

Ownership(kvset, view) == [kv \in kvset |-> view]

(*--algorithm sofaster
variables
    ServerState = [SourceSessions |-> NULL, TargetSessions |-> NULL],
    SViewNumber = [SourceSessions |-> 0],
    TViewNumber = [TargetSessions |-> 0],
    MigrationRange = NULL,
    PrepForTransferRPC = FALSE,
    TakeOwnershipRPC = FALSE,
    TransferCompleteRPC = FALSE,
    ACKTransferCompleteRPC = FALSE,
    Start2PC = FALSE,
    SourcePrepare2PC = FALSE,
    TargetPrepare2PC = FALSE,
    SourceACK = FALSE,
    TargetACK = FALSE,
    SourceCommit = FALSE,
    TargetCommit = FALSE;

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
    variable SKVRanges = {SourceKeys, KeysToMigrate}, TransferComplete = FALSE, SKVOwner = Ownership(SKVRanges, 0);
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
        end if;
    \* 2PC
    CompleteMigration:
        await TransferComplete;
        ServerState[self] := WaitForCheckpoint;
    StartCommit:
        await ACKTransferCompleteRPC;
        Start2PC := TRUE;
    WaitForPrepare:
        await SourcePrepare2PC;
        SourceACK := TRUE;
        ServerState[self] := 2PCPrepare;
    WaitForDecisionSource:
        await SourceCommit;
        ServerState[self] := 2PCCommit; 
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

\* Model for client with an active session involved in migration
(*process Clients = ClientSession
    variable CViewNumber;
  begin 
end process;*)

\* TODO: Model timeouts and crashes
fair process CoordinatorProcess = Zookeeper
    variable ServerVote = [Source |-> NULL, Target |-> NULL]; \* {NULL, TRUE, FALSE}
  begin
    Init2PC:
        await Start2PC;
        SourcePrepare2PC := TRUE;
        TargetPrepare2PC := TRUE;
    CompletionDecision:
        await SourceACK /\ TargetACK;
        SourceCommit := TRUE;
        TargetCommit := TRUE;
        ServerVote[Source] := SourceCommit || ServerVote[Target] := TargetCommit;
end process; 

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES ServerState, SViewNumber, TViewNumber, MigrationRange, 
          PrepForTransferRPC, TakeOwnershipRPC, TransferCompleteRPC, 
          ACKTransferCompleteRPC, Start2PC, SourcePrepare2PC, 
          TargetPrepare2PC, SourceACK, TargetACK, SourceCommit, TargetCommit, 
          pc, SKVRanges, TransferComplete, SKVOwner, TKVRanges, 
          MigratingRanges, TKVOwner, ServerVote

vars == << ServerState, SViewNumber, TViewNumber, MigrationRange, 
           PrepForTransferRPC, TakeOwnershipRPC, TransferCompleteRPC, 
           ACKTransferCompleteRPC, Start2PC, SourcePrepare2PC, 
           TargetPrepare2PC, SourceACK, TargetACK, SourceCommit, TargetCommit, 
           pc, SKVRanges, TransferComplete, SKVOwner, TKVRanges, 
           MigratingRanges, TKVOwner, ServerVote >>

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
        /\ SourcePrepare2PC = FALSE
        /\ TargetPrepare2PC = FALSE
        /\ SourceACK = FALSE
        /\ TargetACK = FALSE
        /\ SourceCommit = FALSE
        /\ TargetCommit = FALSE
        (* Process SourceProcess *)
        /\ SKVRanges = [self \in SourceSessions |-> {SourceKeys, KeysToMigrate}]
        /\ TransferComplete = [self \in SourceSessions |-> FALSE]
        /\ SKVOwner = [self \in SourceSessions |-> Ownership(SKVRanges[self], 0)]
        (* Process TargetProcess *)
        /\ TKVRanges = [self \in TargetSessions |-> {TargetKeys}]
        /\ MigratingRanges = [self \in TargetSessions |-> NULL]
        /\ TKVOwner = [self \in TargetSessions |-> Ownership(TKVRanges[self], 0)]
        (* Process CoordinatorProcess *)
        /\ ServerVote = [Source |-> NULL, Target |-> NULL]
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
                                             SourcePrepare2PC, 
                                             TargetPrepare2PC, SourceACK, 
                                             TargetACK, SourceCommit, 
                                             TargetCommit, SKVRanges, 
                                             TransferComplete, SKVOwner, 
                                             TKVRanges, MigratingRanges, 
                                             TKVOwner, ServerVote >>

SampleRecords(self) == /\ pc[self] = "SampleRecords"
                       /\ ServerState' = [ServerState EXCEPT ![self] = Sampling]
                       /\ pc' = [pc EXCEPT ![self] = "ViewChange"]
                       /\ UNCHANGED << SViewNumber, TViewNumber, 
                                       MigrationRange, PrepForTransferRPC, 
                                       TakeOwnershipRPC, TransferCompleteRPC, 
                                       ACKTransferCompleteRPC, Start2PC, 
                                       SourcePrepare2PC, TargetPrepare2PC, 
                                       SourceACK, TargetACK, SourceCommit, 
                                       TargetCommit, SKVRanges, 
                                       TransferComplete, SKVOwner, TKVRanges, 
                                       MigratingRanges, TKVOwner, ServerVote >>

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
                    /\ UNCHANGED << TViewNumber, TakeOwnershipRPC, 
                                    TransferCompleteRPC, 
                                    ACKTransferCompleteRPC, Start2PC, 
                                    SourcePrepare2PC, TargetPrepare2PC, 
                                    SourceACK, TargetACK, SourceCommit, 
                                    TargetCommit, SKVRanges, TransferComplete, 
                                    SKVOwner, TKVRanges, MigratingRanges, 
                                    TKVOwner, ServerVote >>

TransferOwnership(self) == /\ pc[self] = "TransferOwnership"
                           /\ ServerState' = [ServerState EXCEPT ![self] = TransferingOwnership]
                           /\ pc' = [pc EXCEPT ![self] = "CompleteRequests"]
                           /\ UNCHANGED << SViewNumber, TViewNumber, 
                                           MigrationRange, PrepForTransferRPC, 
                                           TakeOwnershipRPC, 
                                           TransferCompleteRPC, 
                                           ACKTransferCompleteRPC, Start2PC, 
                                           SourcePrepare2PC, TargetPrepare2PC, 
                                           SourceACK, TargetACK, SourceCommit, 
                                           TargetCommit, SKVRanges, 
                                           TransferComplete, SKVOwner, 
                                           TKVRanges, MigratingRanges, 
                                           TKVOwner, ServerVote >>

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
                                          SourcePrepare2PC, TargetPrepare2PC, 
                                          SourceACK, TargetACK, SourceCommit, 
                                          TargetCommit, SKVRanges, 
                                          TransferComplete, SKVOwner, 
                                          TKVRanges, MigratingRanges, TKVOwner, 
                                          ServerVote >>

MoveData(self) == /\ pc[self] = "MoveData"
                  /\ SKVRanges' = [SKVRanges EXCEPT ![self] = SKVRanges[self] \ {KeysToMigrate}]
                  /\ ServerState' = [ServerState EXCEPT ![self] = MoveDataToTarget]
                  /\ \E sessions \in SourceSessions:
                       ServerState'[sessions] = MoveDataToTarget
                  /\ SKVOwner' = [SKVOwner EXCEPT ![self] = Ownership(SKVRanges'[self], SViewNumber[self])]
                  /\ IF ~TransferComplete[self]
                        THEN /\ TransferComplete' = [TransferComplete EXCEPT ![self] = TRUE]
                        ELSE /\ TRUE
                             /\ UNCHANGED TransferComplete
                  /\ pc' = [pc EXCEPT ![self] = "CompleteMigration"]
                  /\ UNCHANGED << SViewNumber, TViewNumber, MigrationRange, 
                                  PrepForTransferRPC, TakeOwnershipRPC, 
                                  TransferCompleteRPC, ACKTransferCompleteRPC, 
                                  Start2PC, SourcePrepare2PC, TargetPrepare2PC, 
                                  SourceACK, TargetACK, SourceCommit, 
                                  TargetCommit, TKVRanges, MigratingRanges, 
                                  TKVOwner, ServerVote >>

CompleteMigration(self) == /\ pc[self] = "CompleteMigration"
                           /\ TransferComplete[self]
                           /\ ServerState' = [ServerState EXCEPT ![self] = WaitForCheckpoint]
                           /\ pc' = [pc EXCEPT ![self] = "StartCommit"]
                           /\ UNCHANGED << SViewNumber, TViewNumber, 
                                           MigrationRange, PrepForTransferRPC, 
                                           TakeOwnershipRPC, 
                                           TransferCompleteRPC, 
                                           ACKTransferCompleteRPC, Start2PC, 
                                           SourcePrepare2PC, TargetPrepare2PC, 
                                           SourceACK, TargetACK, SourceCommit, 
                                           TargetCommit, SKVRanges, 
                                           TransferComplete, SKVOwner, 
                                           TKVRanges, MigratingRanges, 
                                           TKVOwner, ServerVote >>

StartCommit(self) == /\ pc[self] = "StartCommit"
                     /\ ACKTransferCompleteRPC
                     /\ Start2PC' = TRUE
                     /\ pc' = [pc EXCEPT ![self] = "WaitForPrepare"]
                     /\ UNCHANGED << ServerState, SViewNumber, TViewNumber, 
                                     MigrationRange, PrepForTransferRPC, 
                                     TakeOwnershipRPC, TransferCompleteRPC, 
                                     ACKTransferCompleteRPC, SourcePrepare2PC, 
                                     TargetPrepare2PC, SourceACK, TargetACK, 
                                     SourceCommit, TargetCommit, SKVRanges, 
                                     TransferComplete, SKVOwner, TKVRanges, 
                                     MigratingRanges, TKVOwner, ServerVote >>

WaitForPrepare(self) == /\ pc[self] = "WaitForPrepare"
                        /\ SourcePrepare2PC
                        /\ SourceACK' = TRUE
                        /\ ServerState' = [ServerState EXCEPT ![self] = 2PCPrepare]
                        /\ pc' = [pc EXCEPT ![self] = "WaitForDecisionSource"]
                        /\ UNCHANGED << SViewNumber, TViewNumber, 
                                        MigrationRange, PrepForTransferRPC, 
                                        TakeOwnershipRPC, TransferCompleteRPC, 
                                        ACKTransferCompleteRPC, Start2PC, 
                                        SourcePrepare2PC, TargetPrepare2PC, 
                                        TargetACK, SourceCommit, TargetCommit, 
                                        SKVRanges, TransferComplete, SKVOwner, 
                                        TKVRanges, MigratingRanges, TKVOwner, 
                                        ServerVote >>

WaitForDecisionSource(self) == /\ pc[self] = "WaitForDecisionSource"
                               /\ SourceCommit
                               /\ ServerState' = [ServerState EXCEPT ![self] = 2PCCommit]
                               /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ UNCHANGED << SViewNumber, TViewNumber, 
                                               MigrationRange, 
                                               PrepForTransferRPC, 
                                               TakeOwnershipRPC, 
                                               TransferCompleteRPC, 
                                               ACKTransferCompleteRPC, 
                                               Start2PC, SourcePrepare2PC, 
                                               TargetPrepare2PC, SourceACK, 
                                               TargetACK, SourceCommit, 
                                               TargetCommit, SKVRanges, 
                                               TransferComplete, SKVOwner, 
                                               TKVRanges, MigratingRanges, 
                                               TKVOwner, ServerVote >>

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
                             /\ TViewNumber' = [TViewNumber EXCEPT ![self] = TViewNumber[self] + 1]
                             /\ pc' = [pc EXCEPT ![self] = "TakeOwnership"]
                             /\ UNCHANGED << SViewNumber, MigrationRange, 
                                             PrepForTransferRPC, 
                                             TakeOwnershipRPC, 
                                             TransferCompleteRPC, 
                                             ACKTransferCompleteRPC, Start2PC, 
                                             SourcePrepare2PC, 
                                             TargetPrepare2PC, SourceACK, 
                                             TargetACK, SourceCommit, 
                                             TargetCommit, SKVRanges, 
                                             TransferComplete, SKVOwner, 
                                             TKVRanges, TKVOwner, ServerVote >>

TakeOwnership(self) == /\ pc[self] = "TakeOwnership"
                       /\ TakeOwnershipRPC
                       /\ TKVRanges' = [TKVRanges EXCEPT ![self] = TKVRanges[self] \union {MigratingRanges[self]}]
                       /\ ServerState' = [ServerState EXCEPT ![self] = ReceivingData]
                       /\ TKVOwner' = [TKVOwner EXCEPT ![self] = Ownership(TKVRanges'[self], TViewNumber[self])]
                       /\ pc' = [pc EXCEPT ![self] = "StartCheckpointing"]
                       /\ UNCHANGED << SViewNumber, TViewNumber, 
                                       MigrationRange, PrepForTransferRPC, 
                                       TakeOwnershipRPC, TransferCompleteRPC, 
                                       ACKTransferCompleteRPC, Start2PC, 
                                       SourcePrepare2PC, TargetPrepare2PC, 
                                       SourceACK, TargetACK, SourceCommit, 
                                       TargetCommit, SKVRanges, 
                                       TransferComplete, SKVOwner, 
                                       MigratingRanges, ServerVote >>

StartCheckpointing(self) == /\ pc[self] = "StartCheckpointing"
                            /\ TransferCompleteRPC
                            /\ ServerState' = [ServerState EXCEPT ![self] = Checkpointing]
                            /\ ACKTransferCompleteRPC' = TRUE
                            /\ pc' = [pc EXCEPT ![self] = "WaitFor2PC"]
                            /\ UNCHANGED << SViewNumber, TViewNumber, 
                                            MigrationRange, PrepForTransferRPC, 
                                            TakeOwnershipRPC, 
                                            TransferCompleteRPC, Start2PC, 
                                            SourcePrepare2PC, TargetPrepare2PC, 
                                            SourceACK, TargetACK, SourceCommit, 
                                            TargetCommit, SKVRanges, 
                                            TransferComplete, SKVOwner, 
                                            TKVRanges, MigratingRanges, 
                                            TKVOwner, ServerVote >>

WaitFor2PC(self) == /\ pc[self] = "WaitFor2PC"
                    /\ TargetPrepare2PC
                    /\ TargetACK' = TRUE
                    /\ ServerState' = [ServerState EXCEPT ![self] = 2PCPrepare]
                    /\ pc' = [pc EXCEPT ![self] = "WaitForDecisionTarget"]
                    /\ UNCHANGED << SViewNumber, TViewNumber, MigrationRange, 
                                    PrepForTransferRPC, TakeOwnershipRPC, 
                                    TransferCompleteRPC, 
                                    ACKTransferCompleteRPC, Start2PC, 
                                    SourcePrepare2PC, TargetPrepare2PC, 
                                    SourceACK, SourceCommit, TargetCommit, 
                                    SKVRanges, TransferComplete, SKVOwner, 
                                    TKVRanges, MigratingRanges, TKVOwner, 
                                    ServerVote >>

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
                                               Start2PC, SourcePrepare2PC, 
                                               TargetPrepare2PC, SourceACK, 
                                               TargetACK, SourceCommit, 
                                               TargetCommit, SKVRanges, 
                                               TransferComplete, SKVOwner, 
                                               TKVRanges, MigratingRanges, 
                                               TKVOwner, ServerVote >>

TargetProcess(self) == InitMigrationTarget(self) \/ TakeOwnership(self)
                          \/ StartCheckpointing(self) \/ WaitFor2PC(self)
                          \/ WaitForDecisionTarget(self)

Init2PC == /\ pc[Zookeeper] = "Init2PC"
           /\ Start2PC
           /\ SourcePrepare2PC' = TRUE
           /\ TargetPrepare2PC' = TRUE
           /\ pc' = [pc EXCEPT ![Zookeeper] = "CompletionDecision"]
           /\ UNCHANGED << ServerState, SViewNumber, TViewNumber, 
                           MigrationRange, PrepForTransferRPC, 
                           TakeOwnershipRPC, TransferCompleteRPC, 
                           ACKTransferCompleteRPC, Start2PC, SourceACK, 
                           TargetACK, SourceCommit, TargetCommit, SKVRanges, 
                           TransferComplete, SKVOwner, TKVRanges, 
                           MigratingRanges, TKVOwner, ServerVote >>

CompletionDecision == /\ pc[Zookeeper] = "CompletionDecision"
                      /\ SourceACK /\ TargetACK
                      /\ SourceCommit' = TRUE
                      /\ TargetCommit' = TRUE
                      /\ ServerVote' = [ServerVote EXCEPT ![Source] = SourceCommit',
                                                          ![Target] = TargetCommit']
                      /\ pc' = [pc EXCEPT ![Zookeeper] = "Done"]
                      /\ UNCHANGED << ServerState, SViewNumber, TViewNumber, 
                                      MigrationRange, PrepForTransferRPC, 
                                      TakeOwnershipRPC, TransferCompleteRPC, 
                                      ACKTransferCompleteRPC, Start2PC, 
                                      SourcePrepare2PC, TargetPrepare2PC, 
                                      SourceACK, TargetACK, SKVRanges, 
                                      TransferComplete, SKVOwner, TKVRanges, 
                                      MigratingRanges, TKVOwner >>

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
\* Last modified Tue Feb 05 15:31:09 MST 2019 by aarushi
\* Created Thu Jan 17 10:53:34 MST 2019 by aarushi
