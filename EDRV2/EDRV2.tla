------------------------ MODULE EDRV2 ------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

\*  Declarations 
CONSTANTS
  GPUs,            \* Set of all GPUs
  Marketplaces,    \* Set of all marketplaces
  MaxConcurrentJobs \* Constant defined by number of concurrent jobs handled by Nomad Server

\* Each job is just a record with (marketplace, gpu).
\* We'll manage them purely via FIFO queues, no numeric ID.
VARIABLES
  gpuStatus,      \* [marketplace \in Marketplaces -> [gpu \in GPUs -> Status]]
  waitingJobs,    \* Seq of { [marketplace: Marketplaces, gpu: GPUs] }
  activeJobs,     \* Seq of { [marketplace: Marketplaces, gpu: GPUs] }
  jobResults      \* Seq({"success", "failure"}) tracking job outcomes

\* Possible statuses for a GPU
Status == {"healthy", "error_detected", "resolution_requested", "resolved", "escalated"}

\* Type invariant 

TypeInvariant ==
  /\ gpuStatus \in [Marketplaces -> [GPUs -> Status]]
  /\ waitingJobs \in Seq([marketplace: Marketplaces, gpu: GPUs])
  /\ activeJobs \in Seq([marketplace: Marketplaces, gpu: GPUs])
  /\ jobResults \in Seq({"success", "failure"})
  /\ Len(activeJobs) <= MaxConcurrentJobs


\* Iniitalization

Init ==
  /\ gpuStatus = [ m \in Marketplaces |-> [ g \in GPUs |-> "healthy" ] ]
  /\ waitingJobs = << >>
  /\ activeJobs = << >>
  /\ jobResults = << >>

\* Actions / State Transitions

\* A healthy GPU encounters an error
DetectError(m, g) ==
  /\ m \in Marketplaces
  /\ g \in GPUs
  /\ gpuStatus[m][g] = "healthy"
  /\ gpuStatus' = [gpuStatus EXCEPT ![m][g] = "error_detected"]
  /\ UNCHANGED <<waitingJobs, activeJobs, jobResults>>

\* Request resolution for a GPU with detected error: just add job to waiting queue
RequestResolution(m, g) ==
  /\ m \in Marketplaces
  /\ g \in GPUs
  /\ gpuStatus[m][g] = "error_detected"
  /\ gpuStatus' = [gpuStatus EXCEPT ![m][g] = "resolution_requested"]
  /\ waitingJobs' = Append(waitingJobs, [marketplace |-> m, gpu |-> g])
  /\ UNCHANGED <<activeJobs, jobResults>>

\* Schedule a job from waitingJobs if there's capacity
ScheduleJob ==
  /\ waitingJobs /= << >>
  /\ Len(activeJobs) < MaxConcurrentJobs
  /\ LET job == Head(waitingJobs) IN
         /\ activeJobs' = Append(activeJobs, job)
         /\ waitingJobs' = Tail(waitingJobs)
  /\ UNCHANGED <<gpuStatus, jobResults>>

\* Complete a job with success from the head of activeJobs
CompleteJobSuccess ==
  /\ activeJobs /= << >>
  /\ LET job == Head(activeJobs) IN
         /\ gpuStatus[job.marketplace][job.gpu] = "resolution_requested"
         /\ gpuStatus' = [gpuStatus EXCEPT ![job.marketplace][job.gpu] = "resolved"]
         /\ activeJobs' = Tail(activeJobs)
         /\ jobResults' = Append(jobResults, "success")
  /\ UNCHANGED waitingJobs

\* Complete a job with failure (escalation)
CompleteJobFailure ==
  /\ activeJobs /= << >>
  /\ LET job == Head(activeJobs) IN
         /\ gpuStatus[job.marketplace][job.gpu] = "resolution_requested"
         /\ gpuStatus' = [gpuStatus EXCEPT ![job.marketplace][job.gpu] = "escalated"]
         /\ activeJobs' = Tail(activeJobs)
         /\ jobResults' = Append(jobResults, "failure")
  /\ UNCHANGED waitingJobs

\* Resolved GPU returns to healthy
RecoverToHealthy(m, g) ==
  /\ m \in Marketplaces
  /\ g \in GPUs
  /\ gpuStatus[m][g] = "resolved"
  /\ gpuStatus' = [gpuStatus EXCEPT ![m][g] = "healthy"]
  /\ UNCHANGED <<waitingJobs, activeJobs, jobResults>>

\* Escalated GPU gets manually fixed and becomes resolved
ManualIntervention(m, g) ==
  /\ m \in Marketplaces
  /\ g \in GPUs
  /\ gpuStatus[m][g] = "escalated"
  /\ gpuStatus' = [gpuStatus EXCEPT ![m][g] = "resolved"]
  /\ UNCHANGED <<waitingJobs, activeJobs, jobResults>>

\* Next-State Relation                               


Next ==
  \/ \E m \in Marketplaces, g \in GPUs:
         \/ DetectError(m, g)
         \/ RequestResolution(m, g)
         \/ RecoverToHealthy(m, g)
         \/ ManualIntervention(m, g)
  \/ ScheduleJob
  \/ CompleteJobSuccess
  \/ CompleteJobFailure

\* Safety & Resource Constraints                   


\* Only allow valid GPU transitions
SafeTransitions ==
  [][
    \A m \in Marketplaces:
      \A g \in GPUs:
        LET old == gpuStatus[m][g]
            new == gpuStatus'[m][g]
        IN
          \/ old = new
          \/ /\ old = "healthy" /\ new = "error_detected"
          \/ /\ old = "error_detected" /\ new = "resolution_requested"
          \/ /\ old = "resolution_requested" /\ new \in {"resolved","escalated"}
          \/ /\ old = "resolved" /\ new = "healthy"
          \/ /\ old = "escalated" /\ new = "resolved"
  ]_<<gpuStatus, waitingJobs, activeJobs, jobResults>>

\* Basic resource constraint: never exceed maximum concurrency
ResourceConstraintInv == Len(activeJobs) <= MaxConcurrentJobs
JobResultsBound == Len(jobResults) <= 10
WaitingJobsBound == Len(waitingJobs) <= 10
MaxQueueSize == 2 * Cardinality(Marketplaces) * Cardinality(GPUs)

\* Liveness & Fairness 

\* No Starvation: eventually waiting jobs are scheduled
NoJobStarvation ==
  \A i \in 1..MaxQueueSize:
    [](waitingJobs /= << >> /\ Len(waitingJobs) = i =>
         <>(Len(waitingJobs) < i \/ waitingJobs = << >>))

\* Every detected error eventually transitions out of "error_detected"
ErrorEventuallyResolved ==
  \A m \in Marketplaces:
    \A g \in GPUs:
      (gpuStatus[m][g] = "error_detected")
        ~> (gpuStatus[m][g] \in {"resolved","escalated","healthy"})

\* Every escalated error eventually becomes resolved or healthy
EscalatedEventuallyResolved ==
  \A m \in Marketplaces:
    \A g \in GPUs:
      (gpuStatus[m][g] = "escalated")
        ~> (gpuStatus[m][g] \in {"resolved","healthy"})

\* Fairness ensures infinite concurrency changes can happen
Fairness ==
  /\ \A m \in Marketplaces, g \in GPUs:
         /\ WF_<<gpuStatus, waitingJobs, activeJobs, jobResults>>(RequestResolution(m, g))
         /\ WF_<<gpuStatus, waitingJobs, activeJobs, jobResults>>(RecoverToHealthy(m, g))
         /\ WF_<<gpuStatus, waitingJobs, activeJobs, jobResults>>(ManualIntervention(m, g))
  /\ WF_<<gpuStatus, waitingJobs, activeJobs, jobResults>>(ScheduleJob)
  /\ WF_<<gpuStatus, waitingJobs, activeJobs, jobResults>>(CompleteJobSuccess)
  /\ WF_<<gpuStatus, waitingJobs, activeJobs, jobResults>>(CompleteJobFailure)

\* Complete Specification & Properties           
Spec ==
  /\ Init
  /\ [][Next]_<<gpuStatus, waitingJobs, activeJobs, jobResults>>
  /\ Fairness

\* Check that states remain valid
THEOREM Spec => []TypeInvariant

\* Check concurrency safety
THEOREM Spec => []ResourceConstraintInv

\* Check transitions are safe
THEOREM Spec => []SafeTransitions

\* Check liveness
THEOREM Spec => ErrorEventuallyResolved
THEOREM Spec => EscalatedEventuallyResolved
THEOREM Spec => NoJobStarvation

================================================================