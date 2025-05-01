----------------------------- MODULE EDR -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    ConstMarketplaces,   \* Set of all marketplaces (clients)
    ConstHosts,          \* Set of infrastructure providers
    ConstcGPUs           \* Set of all cGPUs

VARIABLES
    gpuStatus,          \* Map from (marketplace, gpu) to status
    gpuHost,            \* Map from GPU to its host (one host per GPU)
    gpuAllocations      \* Map from marketplace to set of GPUs they can use

Status == {"healthy", "error_detected"}

TypeInvariant ==
    /\ gpuStatus \in [ConstMarketplaces -> [ConstcGPUs -> Status]]
    /\ gpuHost \in [ConstcGPUs -> ConstHosts]  \* Each GPU maps to exactly one host
    /\ gpuAllocations \in [ConstMarketplaces -> SUBSET ConstcGPUs]  \* Each marketplace has a set of GPUs

Init ==
    /\ gpuStatus = [m \in ConstMarketplaces |-> [g \in ConstcGPUs |-> "healthy"]]
    /\ gpuHost \in [ConstcGPUs -> ConstHosts]
    \* NEW: Ensure each marketplace has at least one GPU
    /\ gpuAllocations \in 
        {alloc \in [ConstMarketplaces -> SUBSET ConstcGPUs] : 
            \A m \in ConstMarketplaces : alloc[m] # {}}
\* Rest of actions updated to check allocations from marketplace perspective
DetectError(m, g) ==
    /\ m \in ConstMarketplaces
    /\ g \in ConstcGPUs
    /\ g \in gpuAllocations[m]  \* Check if marketplace has this GPU
    /\ gpuStatus[m][g] = "healthy"
    /\ gpuStatus' = [gpuStatus EXCEPT ![m][g] = "error_detected"]
    /\ UNCHANGED <<gpuHost, gpuAllocations>>

ResolveError(m, g) ==
    /\ m \in ConstMarketplaces
    /\ g \in ConstcGPUs
    /\ g \in gpuAllocations[m]  \* Check if marketplace has this GPU
    /\ gpuStatus[m][g] = "error_detected"
    /\ gpuStatus' = [gpuStatus EXCEPT ![m][g] = "healthy"]
    /\ UNCHANGED <<gpuHost, gpuAllocations>>

Next ==
    \E m \in ConstMarketplaces:
        \E g \in ConstcGPUs:
            \/ DetectError(m, g)
            \/ ResolveError(m, g)

SafeTransitions ==
    [][
        /\ \A m \in ConstMarketplaces:
            \A g \in ConstcGPUs:
                LET old == gpuStatus[m][g]
                    new == gpuStatus'[m][g]
                IN
                \/ old = new
                \/ /\ old = "healthy"
                   /\ new = "error_detected"
                   /\ g \in gpuAllocations[m]
                \/ /\ old = "error_detected"
                   /\ new = "healthy"
                   /\ g \in gpuAllocations[m]
        /\ UNCHANGED gpuAllocations
    ]_<<gpuStatus, gpuHost, gpuAllocations>>

StateConstraint ==
    TRUE

Spec == Init /\ [][Next]_<<gpuStatus, gpuHost, gpuAllocations>>

=============================================================================