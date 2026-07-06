import MaleyLean.Papers.ClaimStandingAndLegitimacy.PaperStatements

namespace MaleyLean
namespace Papers
namespace ClaimStandingAndLegitimacy
namespace Surface

/-- Summary theorem exposing the current UEAP paper-facing theorem surface. -/
theorem SummaryStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (pass : CompletedValidatorPass A c) :
    Verbatim.resultTitle Verbatim.ResultTag.ueapCertificationTheorem =
      "UEAP Certification Theorem" /\
    ValidatorOutput A c := by
  exact And.intro
    Verbatim.manuscriptHasUEAPCertificationEntry
    (PaperUEAPCertificationStatement A c pass)

/-- Summary theorem connecting UEAP conditions to the existing AASC bridge. -/
theorem GovernanceBridgeSummaryStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (h_gate : A.domainLedgerDeclared /\ A.carrierStandardDeclared)
    (h_redescription : forall c : Claim, A.meaningFixed c)
    (h_scope : forall c : Claim, A.scopeFixed c)
    (h_failClosed : forall c : Claim, A.reportPreserving c) :
    BivalenceNonDegenerateReasoning.AASCClass (governanceSystemOfUEAP A) := by
  exact
    PaperUEAPGovernanceBivalenceBridgeStatement
      A
      h_gate
      h_redescription
      h_scope
      h_failClosed

/-- Summary theorem exposing semantic status soundness for registry rows. -/
theorem RegistryStatusSoundnessSummaryStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (row : RegistryRow)
    (h_sound : SemanticallySoundRegistry A c row) :
    AuditStatusMeaning A c row.strongest /\ ValidatorOutput A c := by
  exact PaperSoundRegistryStrongestStatusStatement A c row h_sound

/-- Summary theorem exposing same-act non-repair for claim standing. -/
theorem ClaimStandingNoRepairSummaryStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (T : Redescription Claim Claim)
    (c : Claim)
    (h_fail : Not (PreliminaryStanding A c))
    (h_repair : PreliminaryStanding A (T c) -> c = T c) :
    Not (PreliminaryStanding A (T c)) := by
  exact PaperClaimStandingNoSameActRepairStatement A T c h_fail h_repair

/-- Summary theorem exposing conservation of claim standing under reuse stability. -/
theorem ClaimStandingConservationSummaryStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (licensed_same_scope_continuation : Redescription Claim Claim -> Prop)
    (preserves_relevant_invariants : Claim -> Redescription Claim Claim -> Prop) :
    forall c : Claim,
      Not (PreliminaryStanding A c) ->
      Not
        (reuse_stably_admissible
          (fun x => PreliminaryStanding A x)
          licensed_same_scope_continuation
          preserves_relevant_invariants
          c) := by
  exact
    PaperClaimStandingConservationStatement
      A
      licensed_same_scope_continuation
      preserves_relevant_invariants

end Surface
end ClaimStandingAndLegitimacy
end Papers
end MaleyLean
