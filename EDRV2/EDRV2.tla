------------------------ MODULE EDRV2 ------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
  GPUs,                     \* Set of all GPUs
  Marketplaces,             \* Set of all marketplaces
  MaxConcurrentJobs         \* Maximum number of concurrent Nomad jobs

VARIABLES
  gpuStatus,                \* Map from (marketplace, gpu) to status
  jobQueue,                 \* Queue of jobs waiting to be scheduled
  activeJobs,               \* Set of currently running jobs
  jobResults                \* Map from job ID to result (success/failure)

\* Job statuses
JobResult == {"success", "failure"}

\* Possible statuses for a GPU
Status == {"healthy", "error_detected", "resolution_requested", "resolved", "escalated"}

\* Type invariant to ensure variables maintain correct types
TypeInvariant ==
  /\ gpuStatus \in [Marketplaces -> [GPUs -> Status]]
  /\ jobQueue \in Seq([marketplace: Marketplaces, gpu: GPUs])
  /\ activeJobs \subseteq [id: Nat, marketplace: Marketplaces, gpu: GPUs]
  /\ \A id \in DOMAIN jobResults: jobResults[id] \in JobResult
  /\ Cardinality(activeJobs) <= MaxConcurrentJobs

\* Initialize all GPUs to healthy, with empty job queue and no active jobs
Init ==
  /\ gpuStatus = [m \in Marketplaces |-> [g \in GPUs |-> "healthy"]]
  /\ jobQueue = << >>
  /\ activeJobs = {}
  /\ jobResults = [id \in {} |-> "success"]  \* Empty map

\* Define actions that can occur in the system

\* A healthy GPU encounters an error
DetectError(m, g) ==
  /\ m \in Marketplaces
  /\ g \in GPUs
  /\ gpuStatus[m][g] = "healthy"
  /\ gpuStatus' = [gpuStatus EXCEPT ![m][g] = "error_detected"]
  /\ UNCHANGED <<jobQueue, activeJobs, jobResults>>

\* Request resolution for a GPU with detected error - add to job queue
RequestResolution(m, g) ==
  /\ m \in Marketplaces
  /\ g \in GPUs
  /\ gpuStatus[m][g] = "error_detected"
  /\ gpuStatus' = [gpuStatus EXCEPT ![m][g] = "resolution_requested"]
  /\ jobQueue' = Append(jobQueue, [marketplace |-> m, gpu |-> g])
  /\ UNCHANGED <<activeJobs, jobResults>>

\* Schedule a job from the queue if there's capacity
ScheduleJob ==
  /\ jobQueue /= << >>  \* Queue is not empty
  /\ Cardinality(activeJobs) < MaxConcurrentJobs  \* We have capacity
  /\ LET nextJob == Head(jobQueue)
         jobId == Cardinality(activeJobs) + 1
     IN
       /\ activeJobs' = activeJobs \union {[id |-> jobId, 
                                            marketplace |-> nextJob.marketplace, 
                                            gpu |-> nextJob.gpu]}
       /\ jobQueue' = Tail(jobQueue)
  /\ UNCHANGED <<gpuStatus, jobResults>>

\* Complete a job with success
CompleteJobSuccess ==
  /\ activeJobs /= {}
  /\ \E job \in activeJobs:
       /\ gpuStatus[job.marketplace][job.gpu] = "resolution_requested"
       /\ gpuStatus' = [gpuStatus EXCEPT ![job.marketplace][job.gpu] = "resolved"]
       /\ jobResults' = jobResults @@ (job.id :> "success")
       /\ activeJobs' = activeJobs \ {job}
       /\ UNCHANGED jobQueue

\* Complete a job with failure (escalation)
CompleteJobFailure ==
  /\ activeJobs /= {}
  /\ \E job \in activeJobs:
       /\ gpuStatus[job.marketplace][job.gpu] = "resolution_requested"
       /\ gpuStatus' = [gpuStatus EXCEPT ![job.marketplace][job.gpu] = "escalated"]
       /\ jobResults' = jobResults @@ (job.id :> "failure")
       /\ activeJobs' = activeJobs \ {job}
       /\ UNCHANGED jobQueue

\* Resolved GPU returns to healthy
RecoverToHealthy(m, g) ==
  /\ m \in Marketplaces
  /\ g \in GPUs
  /\ gpuStatus[m][g] = "resolved"
  /\ gpuStatus' = [gpuStatus EXCEPT ![m][g] = "healthy"]
  /\ UNCHANGED <<jobQueue, activeJobs, jobResults>>

\* Escalated GPU gets manually fixed and becomes resolved
ManualIntervention(m, g) ==
  /\ m \in Marketplaces
  /\ g \in GPUs
  /\ gpuStatus[m][g] = "escalated"
  /\ gpuStatus' = [gpuStatus EXCEPT ![m][g] = "resolved"]
  /\ UNCHANGED <<jobQueue, activeJobs, jobResults>>

\* Define the next-state relation
Next ==
  \/ \E m \in Marketplaces, g \in GPUs:
       \/ DetectError(m, g)
       \/ RequestResolution(m, g)
       \/ RecoverToHealthy(m, g)
       \/ ManualIntervention(m, g)
  \/ ScheduleJob
  \/ CompleteJobSuccess
  \/ CompleteJobFailure

\* Safety Property: Only allow valid state transitions
SafeTransitions == [][
  \A m \in Marketplaces:
    \A g \in GPUs:
      LET old == gpuStatus[m][g]
          new == gpuStatus'[m][g]
      IN
        \/ old = new  \* No change is always valid
        \/ /\ old = "healthy"
           /\ new = "error_detected"
        \/ /\ old = "error_detected"
           /\ new = "resolution_requested"
        \/ /\ old = "resolution_requested"
           /\ new \in {"resolved", "escalated"}
        \/ /\ old = "resolved"
           /\ new = "healthy"
        \/ /\ old = "escalated"
           /\ new = "resolved"
]_<<gpuStatus, jobQueue, activeJobs, jobResults>>

\* Resource Constraint Safety Property
ResourceConstraintInv == Cardinality(activeJobs) <= MaxConcurrentJobs
ResourceConstraint == [](Cardinality(activeJobs) <= MaxConcurrentJobs)

\* Define a reasonable upper bound for queue length
MaxQueueSize == 2 * Cardinality(Marketplaces) * Cardinality(GPUs)

\* No Starvation Property: Jobs eventually get processed (with finite bound)
NoJobStarvation ==
  \A i \in 1..MaxQueueSize:
    [](jobQueue /= << >> /\ Len(jobQueue) = i => 
       <>(Len(jobQueue) < i \/ jobQueue = << >>))

\* Liveness Property: Every detected error eventually gets resolved
ErrorEventuallyResolved ==
  \A m \in Marketplaces:
    \A g \in GPUs:
      (gpuStatus[m][g] = "error_detected") ~>
        (gpuStatus[m][g] = "resolved" \/ gpuStatus[m][g] = "escalated" \/ gpuStatus[m][g] = "healthy")

\* Liveness Property: Every escalated error eventually gets manually resolved
EscalatedEventuallyResolved ==
  \A m \in Marketplaces:
    \A g \in GPUs:
      (gpuStatus[m][g] = "escalated") ~> (gpuStatus[m][g] = "resolved" \/ gpuStatus[m][g] = "healthy")

\* Add fairness conditions for liveness properties to hold
Fairness ==
  /\ \A m \in Marketplaces, g \in GPUs:
      /\ SF_<<gpuStatus, jobQueue, activeJobs, jobResults>>(RequestResolution(m, g))
      /\ SF_<<gpuStatus, jobQueue, activeJobs, jobResults>>(RecoverToHealthy(m, g))
      /\ SF_<<gpuStatus, jobQueue, activeJobs, jobResults>>(ManualIntervention(m, g))
  /\ SF_<<gpuStatus, jobQueue, activeJobs, jobResults>>(ScheduleJob)
  /\ SF_<<gpuStatus, jobQueue, activeJobs, jobResults>>(CompleteJobSuccess)
  /\ SF_<<gpuStatus, jobQueue, activeJobs, jobResults>>(CompleteJobFailure)

\* Complete specification
Spec ==
  /\ Init
  /\ [][Next]_<<gpuStatus, jobQueue, activeJobs, jobResults>>
  /\ Fairness

\* Invariants and properties to check
THEOREM Spec => []TypeInvariant
THEOREM Spec => []SafeTransitions
THEOREM Spec => []ResourceConstraint
THEOREM Spec => ErrorEventuallyResolved
THEOREM Spec => EscalatedEventuallyResolved
THEOREM Spec => NoJobStarvation

=============================================================================