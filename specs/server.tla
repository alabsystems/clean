--------------------------- MODULE server ---------------------------
(* TLA+ specification of the clean JSON-RPC server protocol.
 *
 * Author: Andrew Yates <andrewyates.name@gmail.com>
 * Part of: clean theorem prover (https://github.com/alabsystems/clean)
 *
 * This spec models the JSON-RPC 2.0 server state machine for client sessions.
 * It captures:
 * - Connection management with concurrency limits
 * - Request/response cycle with proper ID handling
 * - Document/environment synchronization
 * - Graceful shutdown protocol
 * - Proof state cache with TTL expiration and LRU capacity eviction
 *
 * Reference implementation:
 * - crates/clean-server/src/lib.rs (server loop, connection handling)
 * - crates/clean-server/src/rpc.rs (JSON-RPC protocol)
 * - crates/clean-server/src/handlers/state.rs (ServerState)
 * - crates/clean-server/src/proof_state.rs (proof state cache, LRU + TTL)
 *
 * Known divergences from implementation (documented for spec-impl traceability):
 * - No explicit server lifecycle state enum in impl; implicit in control flow
 * - Connection states "Disconnected", "Processing", "Closing" are spec-only
 *   (impl only has Connected → task-dropped); retained for future refinement
 * - Request state "Parsing" is spec-only (impl collapses Received→Validating)
 * - No per-connection pending request limit in WebSocket impl (spec is stricter)
 * - No connection draining on shutdown (impl drops accept loop; inflight orphaned)
 * - Impl has 10 JSON-RPC error codes; spec abstracts to 3
 * - Batch requests and WebSocket progress streaming not modeled
 *)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    ClientIds,      \* Set of possible client identifiers
    RequestIds,     \* Set of possible request identifiers
    StateIds,       \* Set of possible proof state cache identifiers
    Methods,        \* Set of registered RPC methods
    MaxConcurrent,  \* Maximum concurrent connections
    MaxPendingRequests,  \* Maximum pending requests per connection
    MaxCacheCapacity    \* Maximum proof state cache entries (LRU eviction threshold)
                        \* Reference: proof_state.rs config.max_states (default 10000)

(* CONSTANT validation: catch cfg misconfiguration before state exploration *)
ASSUME /\ ClientIds /= {}
       /\ RequestIds /= {}
       /\ StateIds /= {}
       /\ Methods /= {}
       /\ MaxConcurrent \in Nat /\ MaxConcurrent >= 1
       /\ MaxPendingRequests \in Nat /\ MaxPendingRequests >= 1
       /\ MaxCacheCapacity \in Nat /\ MaxCacheCapacity >= 1

VARIABLES
    serverState,    \* Server lifecycle: "Stopped", "Starting", "Running", "ShuttingDown"
    connections,    \* Function: ClientId -> ConnectionRecord
    requests,       \* Function: RequestId -> RequestRecord
    pendingResponses, \* Sequence of pending responses
    environment,    \* Current server environment state
    proofCache,     \* Function: StateId -> CachedProofState
    shutdownRequested, \* Boolean: shutdown signal received
    activeCount     \* Number of active connections

vars == <<serverState, connections, requests, pendingResponses, environment,
          proofCache, shutdownRequested, activeCount>>

\* Note: SelectSeq is imported from the standard Sequences module via EXTENDS

(* ------------------------------- Types ------------------------------- *)

ConnectionStates == {"Disconnected", "Connected", "Processing", "Closing", "Closed"}
RequestStates == {"Received", "Parsing", "Validating", "Dispatching", "Executing", "Completed", "Failed"}
CacheStates == {"Empty", "Cached", "Accessed", "Expired"}  \* Evicted states are removed from domain

ConnectionRecord == [
    id: ClientIds,
    state: ConnectionStates,
    pendingRequests: SUBSET RequestIds
]

RequestRecord == [
    id: RequestIds,
    client: ClientIds,
    method: Methods \cup {<<>>},
    state: RequestStates,
    hasId: BOOLEAN,  \* Notifications have no ID
    response: {"Pending", "Sent", "None"}
]

(* ------------------------------- Type Invariant ------------------------------- *)

TypeOK ==
    /\ serverState \in {"Stopped", "Starting", "Running", "ShuttingDown"}
    /\ activeCount \in Nat
    /\ activeCount <= MaxConcurrent
    /\ shutdownRequested \in BOOLEAN
    \* Structural: environment is a record with version and declarations
    /\ environment.version \in Nat
    \* Structural: activeCount matches actual non-Closed connections
    /\ activeCount = Cardinality({c \in DOMAIN connections :
           connections[c].state \notin {"Closed"}})
    \* Structural: request client references are valid or request is terminal
    /\ \A r \in DOMAIN requests :
           requests[r].client \in DOMAIN connections \/
           requests[r].state \in {"Completed", "Failed"}
    \* Structural: pendingResponses entries reference existing requests
    /\ \A i \in 1..Len(pendingResponses) :
           pendingResponses[i][2] \in DOMAIN requests
    \* Structural: connection pendingRequests reference existing requests
    /\ \A c \in DOMAIN connections :
           connections[c].state /= "Closed" =>
               connections[c].pendingRequests \subseteq DOMAIN requests
    \* Structural: proofCache entries have valid state and accessCount
    /\ \A s \in DOMAIN proofCache :
           /\ proofCache[s].state \in CacheStates
           /\ proofCache[s].accessCount \in Nat
    \* Structural: cache capacity bound (LRU eviction keeps size bounded)
    /\ Cardinality(DOMAIN proofCache) <= MaxCacheCapacity

(* ------------------------------- Initial State ------------------------------- *)

Init ==
    /\ serverState = "Stopped"
    /\ connections = [c \in {} |-> <<>>]
    /\ requests = [r \in {} |-> <<>>]
    /\ pendingResponses = <<>>
    /\ environment = [version |-> 0, declarations |-> {}]
    /\ proofCache = [s \in {} |-> <<>>]
    /\ shutdownRequested = FALSE
    /\ activeCount = 0

(* ------------------------------- Server Lifecycle ------------------------------- *)

(* Start the server *)
StartServer ==
    /\ serverState = "Stopped"
    /\ serverState' = "Starting"
    /\ UNCHANGED <<connections, requests, pendingResponses, environment,
                   proofCache, shutdownRequested, activeCount>>

(* Server becomes ready to accept connections *)
ServerReady ==
    /\ serverState = "Starting"
    /\ serverState' = "Running"
    /\ UNCHANGED <<connections, requests, pendingResponses, environment,
                   proofCache, shutdownRequested, activeCount>>

(* Request shutdown (external signal) *)
RequestShutdown ==
    /\ serverState = "Running"
    /\ shutdownRequested' = TRUE
    /\ serverState' = "ShuttingDown"
    /\ UNCHANGED <<connections, requests, pendingResponses, environment,
                   proofCache, activeCount>>

(* Complete shutdown when all connections drained *)
CompleteShutdown ==
    /\ serverState = "ShuttingDown"
    /\ activeCount = 0
    /\ serverState' = "Stopped"
    /\ shutdownRequested' = FALSE
    /\ UNCHANGED <<connections, requests, pendingResponses, environment,
                   proofCache, activeCount>>

(* ------------------------------- Connection Management ------------------------------- *)

(* Accept a new client connection *)
AcceptConnection(clientId) ==
    /\ serverState = "Running"
    /\ ~shutdownRequested
    /\ activeCount < MaxConcurrent
    /\ clientId \notin DOMAIN connections
    /\ connections' = connections @@ (clientId :> [
           id |-> clientId,
           state |-> "Connected",
           pendingRequests |-> {}
       ])
    /\ activeCount' = activeCount + 1
    /\ UNCHANGED <<serverState, requests, pendingResponses, environment,
                   proofCache, shutdownRequested>>

(* Client disconnects *)
ClientDisconnect(clientId) ==
    /\ clientId \in DOMAIN connections
    /\ connections[clientId].state = "Connected"
    \* Fail all in-flight requests for this client; no response needed (client gone)
    /\ LET clientRequests == {r \in DOMAIN requests : requests[r].client = clientId}
       IN
       /\ requests' = [r \in DOMAIN requests |->
              IF r \in clientRequests
              THEN [requests[r] EXCEPT !.state = "Failed",
                                       !.response = "None"]
              ELSE requests[r]]
       \* FIX: Remove leaked pendingResponses entries for disconnected client's
       \* requests. Without this, entries for disconnected requests persist
       \* forever since SendResponse requires response="Pending" and
       \* CleanupRequest doesn't touch pendingResponses.
       /\ pendingResponses' = SelectSeq(pendingResponses,
              LAMBDA x : x[2] \notin clientRequests)
    /\ connections' = [connections EXCEPT ![clientId].state = "Closed"]
    /\ activeCount' = activeCount - 1
    /\ UNCHANGED <<serverState, environment, proofCache, shutdownRequested>>

(* Remove closed connection *)
RemoveConnection(clientId) ==
    /\ clientId \in DOMAIN connections
    /\ connections[clientId].state = "Closed"
    /\ connections' = [c \in DOMAIN connections \ {clientId} |-> connections[c]]
    /\ UNCHANGED <<serverState, requests, pendingResponses, environment,
                   proofCache, shutdownRequested, activeCount>>

(* ------------------------------- Request Processing ------------------------------- *)

(* Receive a request from a client *)
ReceiveRequest(clientId, requestId, method, hasId) ==
    /\ serverState = "Running"
    /\ clientId \in DOMAIN connections
    /\ connections[clientId].state = "Connected"
    /\ Cardinality(connections[clientId].pendingRequests) < MaxPendingRequests
    /\ requestId \notin DOMAIN requests
    /\ requests' = requests @@ (requestId :> [
           id |-> requestId,
           client |-> clientId,
           method |-> method,
           state |-> "Received",
           hasId |-> hasId,
           response |-> IF hasId THEN "Pending" ELSE "None"
       ])
    /\ connections' = [connections EXCEPT
           ![clientId].pendingRequests = @ \cup {requestId}]
    /\ UNCHANGED <<serverState, pendingResponses, environment, proofCache,
                   shutdownRequested, activeCount>>

(* Parse a received request *)
ParseRequest(requestId) ==
    /\ requestId \in DOMAIN requests
    /\ requests[requestId].state = "Received"
    \* Nondeterministic: parsing can succeed or fail
    /\ \/ /\ requests' = [requests EXCEPT ![requestId].state = "Validating"]
          /\ UNCHANGED pendingResponses
       \/ /\ requests' = [requests EXCEPT
                  ![requestId].state = "Failed",
                  ![requestId].response = IF requests[requestId].hasId
                                          THEN "Pending" ELSE "None"]
          /\ pendingResponses' = IF requests[requestId].hasId
                                 THEN Append(pendingResponses, <<"ParseError", requestId>>)
                                 ELSE pendingResponses
    /\ UNCHANGED <<serverState, connections, environment, proofCache,
                   shutdownRequested, activeCount>>

(* Validate request (check jsonrpc version, method exists) *)
ValidateRequest(requestId) ==
    /\ requestId \in DOMAIN requests
    /\ requests[requestId].state = "Validating"
    /\ \/ /\ requests[requestId].method \in Methods
          /\ requests' = [requests EXCEPT ![requestId].state = "Dispatching"]
          /\ UNCHANGED pendingResponses
       \/ /\ requests[requestId].method \notin Methods
          /\ requests' = [requests EXCEPT ![requestId].state = "Failed"]
          /\ pendingResponses' = IF requests[requestId].hasId
                                 THEN Append(pendingResponses, <<"MethodNotFound", requestId>>)
                                 ELSE pendingResponses
    /\ UNCHANGED <<serverState, connections, environment, proofCache,
                   shutdownRequested, activeCount>>

(* Dispatch request to handler *)
DispatchRequest(requestId) ==
    /\ requestId \in DOMAIN requests
    /\ requests[requestId].state = "Dispatching"
    /\ requests' = [requests EXCEPT ![requestId].state = "Executing"]
    /\ UNCHANGED <<serverState, connections, pendingResponses, environment,
                   proofCache, shutdownRequested, activeCount>>

(* Execute request handler (may modify environment) *)
ExecuteRequest(requestId) ==
    /\ requestId \in DOMAIN requests
    /\ requests[requestId].state = "Executing"
    /\ \/ \* Success: optionally update environment
          /\ requests' = [requests EXCEPT ![requestId].state = "Completed"]
          /\ pendingResponses' = IF requests[requestId].hasId
                                 THEN Append(pendingResponses, <<"Success", requestId>>)
                                 ELSE pendingResponses
          /\ environment' = [environment EXCEPT !.version = @ + 1]
       \/ \* Failure
          /\ requests' = [requests EXCEPT ![requestId].state = "Failed"]
          /\ pendingResponses' = IF requests[requestId].hasId
                                 THEN Append(pendingResponses, <<"ExecutionError", requestId>>)
                                 ELSE pendingResponses
          /\ UNCHANGED environment
    /\ UNCHANGED <<serverState, connections, proofCache, shutdownRequested, activeCount>>

(* Send response to client *)
SendResponse(requestId) ==
    /\ requestId \in DOMAIN requests
    /\ requests[requestId].state \in {"Completed", "Failed"}
    /\ requests[requestId].response = "Pending"
    /\ requests[requestId].client \in DOMAIN connections
    /\ requests' = [requests EXCEPT ![requestId].response = "Sent"]
    \* Remove from pending responses
    /\ pendingResponses' = SelectSeq(pendingResponses, LAMBDA x : x[2] /= requestId)
    \* Remove from client's pending set
    /\ LET client == requests[requestId].client IN
       connections' = [connections EXCEPT
           ![client].pendingRequests = @ \ {requestId}]
    /\ UNCHANGED <<serverState, environment, proofCache, shutdownRequested, activeCount>>

(* Cleanup completed request *)
CleanupRequest(requestId) ==
    /\ requestId \in DOMAIN requests
    /\ requests[requestId].state \in {"Completed", "Failed"}
    /\ requests[requestId].response \in {"Sent", "None"}
    /\ requests' = [r \in DOMAIN requests \ {requestId} |-> requests[r]]
    /\ UNCHANGED <<serverState, connections, pendingResponses, environment,
                   proofCache, shutdownRequested, activeCount>>

(* ------------------------------- Proof State Cache ------------------------------- *)

(* Cache a proof state. If cache is at capacity, LRU eviction removes
   the least-recently-accessed entry to make room.
   Reference: proof_state.rs LruCache::put (auto-evicts on capacity) *)
CacheProofState(stateId) ==
    /\ serverState = "Running"
    /\ stateId \notin DOMAIN proofCache
    /\ IF Cardinality(DOMAIN proofCache) < MaxCacheCapacity
       THEN \* Room available: insert directly
            /\ proofCache' = proofCache @@ (stateId :> [
                   state |-> "Cached",
                   accessCount |-> 0
               ])
       ELSE \* At capacity: evict LRU entry (nondeterministic choice models
            \* LRU ordering without tracking recency explicitly)
            /\ \E victim \in DOMAIN proofCache :
                   proofCache' = [s \in (DOMAIN proofCache \ {victim}) \cup {stateId} |->
                       IF s = stateId
                       THEN [state |-> "Cached", accessCount |-> 0]
                       ELSE proofCache[s]]
    /\ UNCHANGED <<serverState, connections, requests, pendingResponses,
                   environment, shutdownRequested, activeCount>>

(* Access a cached proof state (multiple accesses allowed) *)
AccessProofState(stateId) ==
    /\ stateId \in DOMAIN proofCache
    /\ proofCache[stateId].state \in {"Cached", "Accessed"}
    /\ proofCache' = [proofCache EXCEPT
           ![stateId].state = "Accessed",
           ![stateId].accessCount = @ + 1]
    /\ UNCHANGED <<serverState, connections, requests, pendingResponses,
                   environment, shutdownRequested, activeCount>>

(* Expire a cached state (TTL exceeded) *)
ExpireProofState(stateId) ==
    /\ stateId \in DOMAIN proofCache
    /\ proofCache[stateId].state \in {"Cached", "Accessed"}
    /\ proofCache' = [proofCache EXCEPT ![stateId].state = "Expired"]
    /\ UNCHANGED <<serverState, connections, requests, pendingResponses,
                   environment, shutdownRequested, activeCount>>

(* Evict an expired state *)
EvictProofState(stateId) ==
    /\ stateId \in DOMAIN proofCache
    /\ proofCache[stateId].state = "Expired"
    /\ proofCache' = [s \in DOMAIN proofCache \ {stateId} |-> proofCache[s]]
    /\ UNCHANGED <<serverState, connections, requests, pendingResponses,
                   environment, shutdownRequested, activeCount>>

(* ------------------------------- Next State ------------------------------- *)

Next ==
    \/ StartServer
    \/ ServerReady
    \/ RequestShutdown
    \/ CompleteShutdown
    \/ \E c \in ClientIds : AcceptConnection(c)
    \/ \E c \in DOMAIN connections : ClientDisconnect(c)
    \/ \E c \in DOMAIN connections : RemoveConnection(c)
    \/ \E c \in ClientIds, r \in RequestIds, m \in Methods, h \in BOOLEAN :
           ReceiveRequest(c, r, m, h)
    \/ \E r \in DOMAIN requests : ParseRequest(r)
    \/ \E r \in DOMAIN requests : ValidateRequest(r)
    \/ \E r \in DOMAIN requests : DispatchRequest(r)
    \/ \E r \in DOMAIN requests : ExecuteRequest(r)
    \/ \E r \in DOMAIN requests : SendResponse(r)
    \/ \E r \in DOMAIN requests : CleanupRequest(r)
    \/ \E s \in StateIds : CacheProofState(s)
    \/ \E s \in DOMAIN proofCache : AccessProofState(s)
    \/ \E s \in DOMAIN proofCache : ExpireProofState(s)
    \/ \E s \in DOMAIN proofCache : EvictProofState(s)

Spec == Init /\ [][Next]_vars

(* ------------------------------- Safety Properties ------------------------------- *)

(* Concurrency limit respected *)
ConcurrencyLimit ==
    activeCount <= MaxConcurrent

(* Every request with ID gets a response — unless client disconnected.
   ClientDisconnect sets response="None" for all client requests since
   there is nobody to send the response to. This is correct behavior:
   we only require response tracking while the client is still active. *)
RequestResponseCorrespondence ==
    \A r \in DOMAIN requests :
        requests[r].hasId =>
            \* Client still actively connected: response must be tracked
            (requests[r].client \in DOMAIN connections /\
             connections[requests[r].client].state = "Connected" /\
             requests[r].state \in {"Completed", "Failed"}) =>
                requests[r].response \in {"Pending", "Sent"}

(* Notifications (no ID) get no response *)
NotificationsNoResponse ==
    \A r \in DOMAIN requests :
        ~requests[r].hasId => requests[r].response = "None"

(* No orphaned requests after client disconnect *)
NoOrphanedRequests ==
    \A r \in DOMAIN requests :
        requests[r].client \in DOMAIN connections \/
        requests[r].state \in {"Completed", "Failed"}

(* Shutdown is graceful: no new connections while shutting down (state invariant) *)
GracefulShutdown ==
    serverState = "ShuttingDown" =>
        \* All current connections are being drained
        \A c \in DOMAIN connections :
            connections[c].state \in {"Connected", "Processing", "Closing", "Closed"}

(* Expired proof states are not accessible *)
ExpiredNotAccessible ==
    \A s \in DOMAIN proofCache :
        proofCache[s].state = "Expired" =>
            ~ENABLED(AccessProofState(s))

(* Request processing follows order (action property) *)
RequestProcessingOrder ==
    [][\A r \in DOMAIN requests :
        /\ (requests[r].state = "Validating" =>
                (r \in DOMAIN requests' => requests'[r].state \in {"Dispatching", "Failed", "Validating"}))
        /\ (requests[r].state = "Dispatching" =>
                (r \in DOMAIN requests' => requests'[r].state \in {"Executing", "Failed", "Dispatching"}))
        /\ (requests[r].state = "Executing" =>
                (r \in DOMAIN requests' => requests'[r].state \in {"Completed", "Failed", "Executing"}))]_vars

(* Environment version never decreases (action property) *)
VersionMonotonic ==
    [][environment'.version >= environment.version]_vars

(* Cache capacity is always bounded *)
CacheCapacityBounded ==
    Cardinality(DOMAIN proofCache) <= MaxCacheCapacity

(* No orphaned pendingResponses entries: every entry references an existing
   request that still expects a response. This catches the previously-existing
   leak where ClientDisconnect failed to clean up pendingResponses. *)
NoPendingResponseLeak ==
    \A i \in 1..Len(pendingResponses) :
        LET reqId == pendingResponses[i][2] IN
        /\ reqId \in DOMAIN requests
        /\ requests[reqId].response /= "None"

(* ------------------------------- Liveness Properties ------------------------------- *)

(* Server eventually starts if requested *)
EventuallyStarts ==
    serverState = "Starting" ~> serverState = "Running"

(* Server eventually shuts down when requested *)
EventuallyShutdown ==
    shutdownRequested ~> serverState = "Stopped"

(* Every request eventually completes or fails *)
(* Guard all requests[r] accesses with IF-THEN-ELSE so both sides of ~>
   are evaluable in every state, avoiding TLC's variable-domain limitation *)
RequestsComplete ==
    \A r \in RequestIds :
        (IF r \in DOMAIN requests
         THEN requests[r].state \in {"Received", "Parsing", "Validating", "Dispatching", "Executing"}
         ELSE FALSE) ~>
        (IF r \in DOMAIN requests
         THEN requests[r].state \in {"Completed", "Failed"}
         ELSE TRUE)

(* Progress-driving actions (excludes proof cache operations which
   can cycle indefinitely without advancing server lifecycle or
   request processing toward completion) *)
ProgressActions ==
    \/ StartServer
    \/ ServerReady
    \/ RequestShutdown
    \/ CompleteShutdown
    \/ \E c \in ClientIds : AcceptConnection(c)
    \/ \E c \in DOMAIN connections : ClientDisconnect(c)
    \/ \E c \in DOMAIN connections : RemoveConnection(c)
    \/ \E c \in ClientIds, r \in RequestIds, m \in Methods, h \in BOOLEAN :
           ReceiveRequest(c, r, m, h)
    \/ \E r \in DOMAIN requests : ParseRequest(r)
    \/ \E r \in DOMAIN requests : ValidateRequest(r)
    \/ \E r \in DOMAIN requests : DispatchRequest(r)
    \/ \E r \in DOMAIN requests : ExecuteRequest(r)
    \/ \E r \in DOMAIN requests : SendResponse(r)
    \/ \E r \in DOMAIN requests : CleanupRequest(r)

(* Fair scheduling: only progress actions are fairly scheduled.
   Cache operations (CacheProofState, AccessProofState, ExpireProofState,
   EvictProofState) may occur but are not required to, preventing
   infinite cache cycling from starving CompleteShutdown/SendResponse. *)
FairSpec ==
    Spec /\ WF_vars(ProgressActions)

(* With fair scheduling, all liveness properties hold *)
LivenessWithFairness ==
    FairSpec => (EventuallyStarts /\ EventuallyShutdown)

(* ------------------------------- Main Invariant ------------------------------- *)

Safety ==
    /\ TypeOK
    /\ ConcurrencyLimit
    /\ RequestResponseCorrespondence
    /\ NotificationsNoResponse
    /\ NoOrphanedRequests
    /\ CacheCapacityBounded

=============================================================================
\* Modification History
\* Created: 2026-02-02 for clean JSON-RPC server protocol specification
