------------------------------ MODULE sofaster ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Source, Target, Coordinator, NULL, PrepareToSample, Sampling, PrepareForTransfer, TransferingOwnership, WaitForPending, MoveDataToTarget, PrepareForMigration, ReceivingData, WaitForCheckpoint, Checkpointing, 2PCCommit, 2PCPrepare, SourceKeys, TargetKeys, KeysToMigrate 

(*--algorithm sofaster
variables
    Servers = {Source, Target},
    ServerState = [Source |-> NULL, Target |-> NULL],
    SKVRanges = {SourceKeys, KeysToMigrate},
    TKVRanges = {TargetKeys},
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

macro SendData()
  begin
    SKVRanges := SKVRanges \ {KeysToMigrate};
    TKVRanges := TKVRanges \union {KeysToMigrate};
end macro;

\* All local view numbers start at the last CPR checkpoint (0)
\* Keep history of views from the last checkpoint? [key -> [view ranges, client sessions]]; This will be on a per thread basis?

process SourceProcess = Source
    variable SViewNumber = 0, TransferComplete = FALSE;
  begin
    InitMigrationSource: 
        \* Shared latech on mutable records
        ServerState[Source] := PrepareToSample;
    SampleRecords:
        \* Copy hot records to the tail
        \* Exclusive latch on records in the mutable region
        ServerState[Source] := Sampling;
    ViewChange:
        \* Change view from v to v+1
        ServerState[Source] := PrepareForTransfer;
        PrepForTransferRPC := TRUE; \* also inform target about migrating ranges
    TransferOwnership:
        \* Inform all clients
        ServerState[Source] := TransferingOwnership;
    CompleteRequests:
        \* Wait for pending requests to complete - Is this required even when there is no version change?
        ServerState[Source] := WaitForPending;
        TakeOwnershipRPC := TRUE;
    MoveData:
        \* Send records
        ServerState[Source] := MoveDataToTarget;
        
        TransferComplete := TRUE;
    CompleteMigration:
        await TransferComplete;
        ServerState[Source] := WaitForCheckpoint;
    StartCommit:
        await ACKTransferCompleteRPC;
        Start2PC := TRUE;
    WaitForPrepare:
        await ServerPrepare2PC;
        ServerACK := TRUE;
        ServerState[Source] := 2PCPrepare;
    WaitForDecisionSource:
        await ServerCommit;
        ServerState[Source] := 2PCCommit; 
end process;

process TargetProcess = Target
    variable TViewNumber = 0; MigratingRanges;
  begin
    InitMigrationTarget:
        await PrepForTransferRPC;
        \* Buffer requests for migrating ranges
        ServerState[Target] := PrepareForMigration;
    TakeOwnership:
        await TakeOwnershipRPC;
        \* Enter received records
        \* Start executing requests
        ServerState[Target] := ReceivingData;
    StartCheckpointing:
        await TransferCompleteRPC;
        ServerState[Target] := Checkpointing;
        ACKTransferCompleteRPC := TRUE;
    WaitFor2PC:
        await TargetPrepare2PC;
        TargetACK := TRUE;
        ServerState[Target] := 2PCPrepare;
    WaitForDecisionTarget:
        await TargetCommit;
        ServerState[Target] := 2PCCommit;
end process;

(*process Clients
    variable CViewNumber;
  begin 
end process;*)

\* TODO: Model timeouts and crashes -> use more than boolean
process CoordinatorProcess = Coordinator
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
CONSTANT defaultInitValue
VARIABLES Servers, ServerState, SKVRanges, TKVRanges, PrepForTransferRPC, 
          TakeOwnershipRPC, TransferCompleteRPC, ACKTransferCompleteRPC, 
          Start2PC, ServerPrepare2PC, TargetPrepare2PC, ServerACK, TargetACK, 
          ServerCommit, TargetCommit, pc, SViewNumber, TransferComplete, 
          TViewNumber, MigratingRanges, ServerReply

vars == << Servers, ServerState, SKVRanges, TKVRanges, PrepForTransferRPC, 
           TakeOwnershipRPC, TransferCompleteRPC, ACKTransferCompleteRPC, 
           Start2PC, ServerPrepare2PC, TargetPrepare2PC, ServerACK, TargetACK, 
           ServerCommit, TargetCommit, pc, SViewNumber, TransferComplete, 
           TViewNumber, MigratingRanges, ServerReply >>

ProcSet == {Source} \cup {Target} \cup {Coordinator}

Init == (* Global variables *)
        /\ Servers = {Source, Target}
        /\ ServerState = [Source |-> NULL, Target |-> NULL]
        /\ SKVRanges = {SourceKeys, KeysToMigrate}
        /\ TKVRanges = {TargetKeys}
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
        /\ SViewNumber = 0
        /\ TransferComplete = FALSE
        (* Process TargetProcess *)
        /\ TViewNumber = 0
        /\ MigratingRanges = defaultInitValue
        (* Process CoordinatorProcess *)
        /\ ServerReply = [Source |-> NULL, Target |-> NULL]
        /\ pc = [self \in ProcSet |-> CASE self = Source -> "InitMigrationSource"
                                        [] self = Target -> "InitMigrationTarget"
                                        [] self = Coordinator -> "Init2PC"]

InitMigrationSource == /\ pc[Source] = "InitMigrationSource"
                       /\ ServerState' = [ServerState EXCEPT ![Source] = PrepareToSample]
                       /\ pc' = [pc EXCEPT ![Source] = "SampleRecords"]
                       /\ UNCHANGED << Servers, SKVRanges, TKVRanges, 
                                       PrepForTransferRPC, TakeOwnershipRPC, 
                                       TransferCompleteRPC, 
                                       ACKTransferCompleteRPC, Start2PC, 
                                       ServerPrepare2PC, TargetPrepare2PC, 
                                       ServerACK, TargetACK, ServerCommit, 
                                       TargetCommit, SViewNumber, 
                                       TransferComplete, TViewNumber, 
                                       MigratingRanges, ServerReply >>

SampleRecords == /\ pc[Source] = "SampleRecords"
                 /\ ServerState' = [ServerState EXCEPT ![Source] = Sampling]
                 /\ pc' = [pc EXCEPT ![Source] = "ViewChange"]
                 /\ UNCHANGED << Servers, SKVRanges, TKVRanges, 
                                 PrepForTransferRPC, TakeOwnershipRPC, 
                                 TransferCompleteRPC, ACKTransferCompleteRPC, 
                                 Start2PC, ServerPrepare2PC, TargetPrepare2PC, 
                                 ServerACK, TargetACK, ServerCommit, 
                                 TargetCommit, SViewNumber, TransferComplete, 
                                 TViewNumber, MigratingRanges, ServerReply >>

ViewChange == /\ pc[Source] = "ViewChange"
              /\ ServerState' = [ServerState EXCEPT ![Source] = PrepareForTransfer]
              /\ PrepForTransferRPC' = TRUE
              /\ pc' = [pc EXCEPT ![Source] = "TransferOwnership"]
              /\ UNCHANGED << Servers, SKVRanges, TKVRanges, TakeOwnershipRPC, 
                              TransferCompleteRPC, ACKTransferCompleteRPC, 
                              Start2PC, ServerPrepare2PC, TargetPrepare2PC, 
                              ServerACK, TargetACK, ServerCommit, TargetCommit, 
                              SViewNumber, TransferComplete, TViewNumber, 
                              MigratingRanges, ServerReply >>

TransferOwnership == /\ pc[Source] = "TransferOwnership"
                     /\ ServerState' = [ServerState EXCEPT ![Source] = TransferingOwnership]
                     /\ pc' = [pc EXCEPT ![Source] = "CompleteRequests"]
                     /\ UNCHANGED << Servers, SKVRanges, TKVRanges, 
                                     PrepForTransferRPC, TakeOwnershipRPC, 
                                     TransferCompleteRPC, 
                                     ACKTransferCompleteRPC, Start2PC, 
                                     ServerPrepare2PC, TargetPrepare2PC, 
                                     ServerACK, TargetACK, ServerCommit, 
                                     TargetCommit, SViewNumber, 
                                     TransferComplete, TViewNumber, 
                                     MigratingRanges, ServerReply >>

CompleteRequests == /\ pc[Source] = "CompleteRequests"
                    /\ ServerState' = [ServerState EXCEPT ![Source] = WaitForPending]
                    /\ TakeOwnershipRPC' = TRUE
                    /\ pc' = [pc EXCEPT ![Source] = "MoveData"]
                    /\ UNCHANGED << Servers, SKVRanges, TKVRanges, 
                                    PrepForTransferRPC, TransferCompleteRPC, 
                                    ACKTransferCompleteRPC, Start2PC, 
                                    ServerPrepare2PC, TargetPrepare2PC, 
                                    ServerACK, TargetACK, ServerCommit, 
                                    TargetCommit, SViewNumber, 
                                    TransferComplete, TViewNumber, 
                                    MigratingRanges, ServerReply >>

MoveData == /\ pc[Source] = "MoveData"
            /\ ServerState' = [ServerState EXCEPT ![Source] = MoveDataToTarget]
            /\ TransferComplete' = TRUE
            /\ pc' = [pc EXCEPT ![Source] = "CompleteMigration"]
            /\ UNCHANGED << Servers, SKVRanges, TKVRanges, PrepForTransferRPC, 
                            TakeOwnershipRPC, TransferCompleteRPC, 
                            ACKTransferCompleteRPC, Start2PC, ServerPrepare2PC, 
                            TargetPrepare2PC, ServerACK, TargetACK, 
                            ServerCommit, TargetCommit, SViewNumber, 
                            TViewNumber, MigratingRanges, ServerReply >>

CompleteMigration == /\ pc[Source] = "CompleteMigration"
                     /\ TransferComplete
                     /\ ServerState' = [ServerState EXCEPT ![Source] = WaitForCheckpoint]
                     /\ pc' = [pc EXCEPT ![Source] = "StartCommit"]
                     /\ UNCHANGED << Servers, SKVRanges, TKVRanges, 
                                     PrepForTransferRPC, TakeOwnershipRPC, 
                                     TransferCompleteRPC, 
                                     ACKTransferCompleteRPC, Start2PC, 
                                     ServerPrepare2PC, TargetPrepare2PC, 
                                     ServerACK, TargetACK, ServerCommit, 
                                     TargetCommit, SViewNumber, 
                                     TransferComplete, TViewNumber, 
                                     MigratingRanges, ServerReply >>

StartCommit == /\ pc[Source] = "StartCommit"
               /\ ACKTransferCompleteRPC
               /\ Start2PC' = TRUE
               /\ pc' = [pc EXCEPT ![Source] = "WaitForPrepare"]
               /\ UNCHANGED << Servers, ServerState, SKVRanges, TKVRanges, 
                               PrepForTransferRPC, TakeOwnershipRPC, 
                               TransferCompleteRPC, ACKTransferCompleteRPC, 
                               ServerPrepare2PC, TargetPrepare2PC, ServerACK, 
                               TargetACK, ServerCommit, TargetCommit, 
                               SViewNumber, TransferComplete, TViewNumber, 
                               MigratingRanges, ServerReply >>

WaitForPrepare == /\ pc[Source] = "WaitForPrepare"
                  /\ ServerPrepare2PC
                  /\ ServerACK' = TRUE
                  /\ ServerState' = [ServerState EXCEPT ![Source] = 2PCPrepare]
                  /\ pc' = [pc EXCEPT ![Source] = "WaitForDecisionSource"]
                  /\ UNCHANGED << Servers, SKVRanges, TKVRanges, 
                                  PrepForTransferRPC, TakeOwnershipRPC, 
                                  TransferCompleteRPC, ACKTransferCompleteRPC, 
                                  Start2PC, ServerPrepare2PC, TargetPrepare2PC, 
                                  TargetACK, ServerCommit, TargetCommit, 
                                  SViewNumber, TransferComplete, TViewNumber, 
                                  MigratingRanges, ServerReply >>

WaitForDecisionSource == /\ pc[Source] = "WaitForDecisionSource"
                         /\ ServerCommit
                         /\ ServerState' = [ServerState EXCEPT ![Source] = 2PCCommit]
                         /\ pc' = [pc EXCEPT ![Source] = "Done"]
                         /\ UNCHANGED << Servers, SKVRanges, TKVRanges, 
                                         PrepForTransferRPC, TakeOwnershipRPC, 
                                         TransferCompleteRPC, 
                                         ACKTransferCompleteRPC, Start2PC, 
                                         ServerPrepare2PC, TargetPrepare2PC, 
                                         ServerACK, TargetACK, ServerCommit, 
                                         TargetCommit, SViewNumber, 
                                         TransferComplete, TViewNumber, 
                                         MigratingRanges, ServerReply >>

SourceProcess == InitMigrationSource \/ SampleRecords \/ ViewChange
                    \/ TransferOwnership \/ CompleteRequests \/ MoveData
                    \/ CompleteMigration \/ StartCommit \/ WaitForPrepare
                    \/ WaitForDecisionSource

InitMigrationTarget == /\ pc[Target] = "InitMigrationTarget"
                       /\ PrepForTransferRPC
                       /\ ServerState' = [ServerState EXCEPT ![Target] = PrepareForMigration]
                       /\ pc' = [pc EXCEPT ![Target] = "TakeOwnership"]
                       /\ UNCHANGED << Servers, SKVRanges, TKVRanges, 
                                       PrepForTransferRPC, TakeOwnershipRPC, 
                                       TransferCompleteRPC, 
                                       ACKTransferCompleteRPC, Start2PC, 
                                       ServerPrepare2PC, TargetPrepare2PC, 
                                       ServerACK, TargetACK, ServerCommit, 
                                       TargetCommit, SViewNumber, 
                                       TransferComplete, TViewNumber, 
                                       MigratingRanges, ServerReply >>

TakeOwnership == /\ pc[Target] = "TakeOwnership"
                 /\ TakeOwnershipRPC
                 /\ ServerState' = [ServerState EXCEPT ![Target] = ReceivingData]
                 /\ pc' = [pc EXCEPT ![Target] = "StartCheckpointing"]
                 /\ UNCHANGED << Servers, SKVRanges, TKVRanges, 
                                 PrepForTransferRPC, TakeOwnershipRPC, 
                                 TransferCompleteRPC, ACKTransferCompleteRPC, 
                                 Start2PC, ServerPrepare2PC, TargetPrepare2PC, 
                                 ServerACK, TargetACK, ServerCommit, 
                                 TargetCommit, SViewNumber, TransferComplete, 
                                 TViewNumber, MigratingRanges, ServerReply >>

StartCheckpointing == /\ pc[Target] = "StartCheckpointing"
                      /\ TransferCompleteRPC
                      /\ ServerState' = [ServerState EXCEPT ![Target] = Checkpointing]
                      /\ ACKTransferCompleteRPC' = TRUE
                      /\ pc' = [pc EXCEPT ![Target] = "WaitFor2PC"]
                      /\ UNCHANGED << Servers, SKVRanges, TKVRanges, 
                                      PrepForTransferRPC, TakeOwnershipRPC, 
                                      TransferCompleteRPC, Start2PC, 
                                      ServerPrepare2PC, TargetPrepare2PC, 
                                      ServerACK, TargetACK, ServerCommit, 
                                      TargetCommit, SViewNumber, 
                                      TransferComplete, TViewNumber, 
                                      MigratingRanges, ServerReply >>

WaitFor2PC == /\ pc[Target] = "WaitFor2PC"
              /\ TargetPrepare2PC
              /\ TargetACK' = TRUE
              /\ ServerState' = [ServerState EXCEPT ![Target] = 2PCPrepare]
              /\ pc' = [pc EXCEPT ![Target] = "WaitForDecisionTarget"]
              /\ UNCHANGED << Servers, SKVRanges, TKVRanges, 
                              PrepForTransferRPC, TakeOwnershipRPC, 
                              TransferCompleteRPC, ACKTransferCompleteRPC, 
                              Start2PC, ServerPrepare2PC, TargetPrepare2PC, 
                              ServerACK, ServerCommit, TargetCommit, 
                              SViewNumber, TransferComplete, TViewNumber, 
                              MigratingRanges, ServerReply >>

WaitForDecisionTarget == /\ pc[Target] = "WaitForDecisionTarget"
                         /\ TargetCommit
                         /\ ServerState' = [ServerState EXCEPT ![Target] = 2PCCommit]
                         /\ pc' = [pc EXCEPT ![Target] = "Done"]
                         /\ UNCHANGED << Servers, SKVRanges, TKVRanges, 
                                         PrepForTransferRPC, TakeOwnershipRPC, 
                                         TransferCompleteRPC, 
                                         ACKTransferCompleteRPC, Start2PC, 
                                         ServerPrepare2PC, TargetPrepare2PC, 
                                         ServerACK, TargetACK, ServerCommit, 
                                         TargetCommit, SViewNumber, 
                                         TransferComplete, TViewNumber, 
                                         MigratingRanges, ServerReply >>

TargetProcess == InitMigrationTarget \/ TakeOwnership \/ StartCheckpointing
                    \/ WaitFor2PC \/ WaitForDecisionTarget

Init2PC == /\ pc[Coordinator] = "Init2PC"
           /\ Start2PC
           /\ ServerPrepare2PC' = TRUE
           /\ TargetPrepare2PC' = TRUE
           /\ pc' = [pc EXCEPT ![Coordinator] = "CompletionDecision"]
           /\ UNCHANGED << Servers, ServerState, SKVRanges, TKVRanges, 
                           PrepForTransferRPC, TakeOwnershipRPC, 
                           TransferCompleteRPC, ACKTransferCompleteRPC, 
                           Start2PC, ServerACK, TargetACK, ServerCommit, 
                           TargetCommit, SViewNumber, TransferComplete, 
                           TViewNumber, MigratingRanges, ServerReply >>

CompletionDecision == /\ pc[Coordinator] = "CompletionDecision"
                      /\ ServerACK /\ TargetACK
                      /\ ServerCommit' = TRUE
                      /\ TargetCommit' = TRUE
                      /\ pc' = [pc EXCEPT ![Coordinator] = "Done"]
                      /\ UNCHANGED << Servers, ServerState, SKVRanges, 
                                      TKVRanges, PrepForTransferRPC, 
                                      TakeOwnershipRPC, TransferCompleteRPC, 
                                      ACKTransferCompleteRPC, Start2PC, 
                                      ServerPrepare2PC, TargetPrepare2PC, 
                                      ServerACK, TargetACK, SViewNumber, 
                                      TransferComplete, TViewNumber, 
                                      MigratingRanges, ServerReply >>

CoordinatorProcess == Init2PC \/ CompletionDecision

Next == SourceProcess \/ TargetProcess \/ CoordinatorProcess
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Wed Jan 23 14:45:36 MST 2019 by aarushi
\* Created Thu Jan 17 10:53:34 MST 2019 by aarushi
