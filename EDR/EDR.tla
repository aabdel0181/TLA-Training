----------------------------- MODULE EDR -----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
    ConstMarketplaces,   \* Set of all marketplaces
    ConstcGPUs           \* Set of all cGPUs

VARIABLES
    gpuStatus  \* Map from (marketplace, gpu) to status


\* Possible statuses for a cGPU 
Status == {"healthy", "error_detected", "resolution_requested", "resolved", "escalated"}

\* Initialize all GPUs to healthy 
Init ==
    /\ gpuStatus = [m \in ConstMarketplaces |-> [g \in ConstcGPUs |-> "healthy"]]

\* Actions 

DetectError(m, g) ==
    /\ m \in ConstMarketplaces
    /\ g \in ConstcGPUs
    /\ gpuStatus[m][g] = "healthy"
    /\ gpuStatus' = [gpuStatus EXCEPT ![m][g] = "error_detected"]

RequestResolution(m, g) ==
    /\ m \in ConstMarketplaces
    /\ g \in ConstcGPUs
    /\ gpuStatus[m][g] = "error_detected"
    /\ gpuStatus' = [gpuStatus EXCEPT ![m][g] = "resolution_requested"]

ResolveError(m, g) ==
    /\ m \in ConstMarketplaces
    /\ g \in ConstcGPUs
    /\ gpuStatus[m][g] = "resolution_requested"
    /\ gpuStatus' = [gpuStatus EXCEPT ![m][g] = "resolved"]

ResolvedUpdateHealth(m,g) == 
    /\ m \in ConstMarketplaces
    /\ g \in ConstcGPUs
    /\ gpuStatus[m][g] = "resolved"
    /\ gpuStatus' = [gpuStatus EXCEPT ![m][g] = "healthy"]

EscalateError(m, g) ==
    /\ m \in ConstMarketplaces
    /\ g \in ConstcGPUs
    /\ gpuStatus[m][g] = "resolution_requested"
    /\ gpuStatus' = [gpuStatus EXCEPT ![m][g] = "escalated"]

\* For the Next-state, we should nondeterministically pick one enabled action
Next ==
    \E m \in ConstMarketplaces:
      \E g \in ConstcGPUs:
         DetectError(m, g) \/ RequestResolution(m, g) \/ ResolveError(m, g) \/ EscalateError(m, g)

\* Safety Property: Only allow valid state transitions 
\* NOTE: This rn is a little basic, need to add constant GPU errors (after resolved -> healthy and so-on
SafeTransitions == [][
        \A m \in ConstMarketplaces:
            \A g \in ConstcGPUs:
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
                \/ /\ old \in {"resolved", "escalated"}
                   /\ new = old  \* Terminal states can't change yet 
    ]_gpuStatus

\* Liveness Property: Every detected error eventually is resolved or escalated
Liveness ==
    \A m \in ConstMarketplaces:
        \A g \in ConstcGPUs:
            (gpuStatus[m][g] = "error_detected") ~> 
                (gpuStatus[m][g] = "resolved" \/ gpuStatus[m][g] = "escalated")


\* Fairness: Ensure that enabled actions eventually happen 
\* NOTE: This is a part of our Specification, not just a property to be checked 
Fairness ==
    /\ \A m \in ConstMarketplaces:
        \A g \in ConstcGPUs:
            /\ WF_gpuStatus(DetectError(m, g))
            /\ WF_gpuStatus(RequestResolution(m, g))
            /\ WF_gpuStatus(ResolveError(m, g))
            /\ WF_gpuStatus(EscalateError(m, g))

Spec ==
    Init /\ [][Next]_<<gpuStatus>> /\ Fairness


THEOREM Spec => [](SafeTransitions)

=============================================================================