/-!
LabTrust trace event ordering and hash-chain obligations (v0.1 simulation profile).
See `services/labtrust-adapter` for the executable checker.
-/

structure LabTrustEvent where
  eventId : String
  action : String
  actorRole : String
  policyDecision : String
  deriving Repr

def successfulQc (e : LabTrustEvent) : Bool :=
  e.action == "perform_qc" && e.policyDecision == "allow"
