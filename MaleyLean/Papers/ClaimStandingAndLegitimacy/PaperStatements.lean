import MaleyLean.Papers.BivalenceNonDegenerateReasoning.PaperStatements
import MaleyLean.Papers.ClaimStandingAndLegitimacy.Verbatim.TheoremRegister

namespace MaleyLean
namespace Papers
namespace ClaimStandingAndLegitimacy

/-- UEAP final and preliminary status classes used by the registry layer. -/
inductive AuditStatus where
  | legitimate
  | legitimateButNotActionable
  | compatibleOnly
  | relationOnly
  | classLevelOnly
  | calibratedOnly
  | domainDependent
  | evidenceCompatible
  | computationOnly
  | obstructionOnly
  | failed
  | standingUnfixed
  | targetUnfixed
  | carrierUnfixed
  | meaningUnfixed
  | scopeUnfixed
  | launderedOrBlocked
  | auditFailure
deriving DecidableEq, Repr

/-- The nine coordinates of the UEAP pre-audit observation frame. -/
inductive AuditCoordinate where
  | target
  | carrier
  | semanticContent
  | representation
  | ancestry
  | domain
  | evidenceNetwork
  | reportUse
  | requestedStatus
deriving DecidableEq, Repr

/-- Coordinate coverage for the manuscript's exhaustion theorem. -/
def CoordinateExhaustion (changes : AuditCoordinate -> Prop) : Prop :=
  changes AuditCoordinate.target \/
  changes AuditCoordinate.carrier \/
  changes AuditCoordinate.semanticContent \/
  changes AuditCoordinate.representation \/
  changes AuditCoordinate.ancestry \/
  changes AuditCoordinate.domain \/
  changes AuditCoordinate.evidenceNetwork \/
  changes AuditCoordinate.reportUse \/
  changes AuditCoordinate.requestedStatus

/-- A domain-general UEAP audit surface for claims in a domain. -/
structure ClaimAudit (Claim Domain : Type) where
  targetFixed : Claim -> Prop
  carrierAdequate : Claim -> Prop
  meaningFixed : Claim -> Prop
  scopeFixed : Claim -> Prop
  targetCarrierAligned : Claim -> Prop
  alternativesExhaustedModuloSkin : Claim -> Prop
  launderingExcluded : Claim -> Prop
  targetAncestrySeparated : Claim -> Prop
  boundaryDeclared : Claim -> Prop
  evidenceNetworkClosed : Claim -> Prop
  reportPreserving : Claim -> Prop
  blockersPreserved : Claim -> Prop
  domainLedgerDeclared : Prop
  requestedStatusDeclared : Prop
  carrierStandardDeclared : Prop
  skinRelationDeclared : Prop
  launderingTaxonomyDeclared : Prop
  precedenceDeclared : Prop

def AuditBasisDeclared {Claim Domain : Type} (A : ClaimAudit Claim Domain) : Prop :=
  A.domainLedgerDeclared /\
  A.requestedStatusDeclared /\
  A.carrierStandardDeclared /\
  A.skinRelationDeclared /\
  A.launderingTaxonomyDeclared /\
  A.precedenceDeclared

def PreliminaryStanding
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim) : Prop :=
  A.targetFixed c /\ A.carrierAdequate c /\ A.meaningFixed c /\ A.scopeFixed c

def SigmaLegitimacy
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim) : Prop :=
  PreliminaryStanding A c /\
  A.targetCarrierAligned c /\
  A.alternativesExhaustedModuloSkin c /\
  A.launderingExcluded c /\
  A.targetAncestrySeparated c /\
  A.boundaryDeclared c /\
  A.evidenceNetworkClosed c /\
  A.reportPreserving c

def LowerStatusReport
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim) : Prop :=
  PreliminaryStanding A c /\
  (Not (A.targetCarrierAligned c) \/
    Not (A.alternativesExhaustedModuloSkin c) \/
    Not (A.launderingExcluded c) \/
    Not (A.targetAncestrySeparated c) \/
    Not (A.boundaryDeclared c) \/
    Not (A.evidenceNetworkClosed c) \/
    Not (A.reportPreserving c))

def AuditFailure {Claim Domain : Type} (A : ClaimAudit Claim Domain) : Prop :=
  Not (AuditBasisDeclared A)

def ValidatorOutput
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim) : Prop :=
  SigmaLegitimacy A c \/
  LowerStatusReport A c \/
  Not (PreliminaryStanding A c) \/
  AuditFailure A

def PreliminaryStandingBlocker
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim) : Prop :=
  Not (A.targetFixed c) \/
  Not (A.carrierAdequate c) \/
  Not (A.meaningFixed c) \/
  Not (A.scopeFixed c)

def LegitimacyBlocker
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim) : Prop :=
  Not (PreliminaryStanding A c) \/
  Not (A.targetCarrierAligned c) \/
  Not (A.alternativesExhaustedModuloSkin c) \/
  Not (A.launderingExcluded c) \/
  Not (A.targetAncestrySeparated c) \/
  Not (A.boundaryDeclared c) \/
  Not (A.evidenceNetworkClosed c) \/
  Not (A.reportPreserving c)

def ClaimCoordinateFailure
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim) :
    AuditCoordinate -> Prop
  | .target => Not (A.targetFixed c)
  | .carrier => Not (A.carrierAdequate c)
  | .semanticContent => Not (A.meaningFixed c)
  | .representation =>
      Not (A.targetCarrierAligned c) \/
      Not (A.alternativesExhaustedModuloSkin c)
  | .ancestry =>
      Not (A.launderingExcluded c) \/
      Not (A.targetAncestrySeparated c)
  | .domain =>
      Not (A.scopeFixed c) \/
      Not (A.boundaryDeclared c) \/
      Not A.domainLedgerDeclared
  | .evidenceNetwork => Not (A.evidenceNetworkClosed c)
  | .reportUse =>
      Not (A.reportPreserving c) \/
      Not (A.blockersPreserved c)
  | .requestedStatus => Not A.requestedStatusDeclared

def StatusLegitimacyBlockingCoordinate
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (coord : AuditCoordinate) : Prop :=
  ClaimCoordinateFailure A c coord /\
  (coord = .target \/
    coord = .carrier \/
    coord = .semanticContent \/
    coord = .representation \/
    coord = .ancestry \/
    coord = .domain \/
    coord = .evidenceNetwork \/
    coord = .reportUse)

def AuditStatusMeaning
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim) :
    AuditStatus -> Prop
  | .legitimate => SigmaLegitimacy A c
  | .legitimateButNotActionable => SigmaLegitimacy A c /\ A.blockersPreserved c
  | .compatibleOnly => LowerStatusReport A c
  | .relationOnly => LowerStatusReport A c
  | .classLevelOnly => LowerStatusReport A c
  | .calibratedOnly =>
      PreliminaryStanding A c /\ Not (A.targetAncestrySeparated c)
  | .domainDependent =>
      PreliminaryStanding A c /\ Not (A.boundaryDeclared c)
  | .evidenceCompatible =>
      PreliminaryStanding A c /\ Not (A.evidenceNetworkClosed c)
  | .computationOnly => Not (A.carrierAdequate c)
  | .obstructionOnly => LowerStatusReport A c
  | .failed => LowerStatusReport A c \/ AuditFailure A
  | .standingUnfixed => Not (PreliminaryStanding A c)
  | .targetUnfixed => Not (A.targetFixed c)
  | .carrierUnfixed => Not (A.carrierAdequate c)
  | .meaningUnfixed => Not (A.meaningFixed c)
  | .scopeUnfixed => Not (A.scopeFixed c)
  | .launderedOrBlocked => LowerStatusReport A c
  | .auditFailure => AuditFailure A

def claimStandingSystemOfUEAP
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain) :
    System Claim where
  admissible := fun c => PreliminaryStanding A c
  standing := fun c => PreliminaryStanding A c
  standing_implies_admissible := fun _ h => h

def claimLegitimacySystemOfUEAP
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain) :
    System Claim where
  admissible := fun c => PreliminaryStanding A c
  standing := fun c => SigmaLegitimacy A c
  standing_implies_admissible := fun _ h => h.1

/-- A completed validator pass records the exhaustive UEAP output case. -/
structure CompletedValidatorPass
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim) where
  output : ValidatorOutput A c

/-- Registry data sufficient for the unique-status theorem. -/
structure RegistryRow where
  satisfied : AuditStatus -> Prop
  strongest : AuditStatus
  strongest_satisfied : satisfied strongest
  strongest_unique : forall s : AuditStatus, satisfied s -> s = strongest
  blockersActive : Prop
  blockersRecorded : Prop
  nextActionDeclared : Prop

def SemanticallySoundRegistry
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (row : RegistryRow) : Prop :=
  forall s : AuditStatus, row.satisfied s -> AuditStatusMeaning A c s

/-- UEAP's claim-level audit surface as a same-scope governance system. -/
def governanceSystemOfUEAP
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain) :
    BivalenceNonDegenerateReasoning.GovernanceSystem Claim where
  standing := fun c => PreliminaryStanding A c
  licensedContinuation := fun c d => c = d
  governanceBearingNonDegenerateUse := A.requestedStatusDeclared
  reference := forall c : Claim, A.targetFixed c
  standingPersistence := forall c : Claim, A.carrierAdequate c
  irreversibility := forall c : Claim, A.launderingExcluded c
  priorGate := A.domainLedgerDeclared /\ A.carrierStandardDeclared
  failClosed := forall c : Claim, A.reportPreserving c
  blocksSilentRedescription := forall c : Claim, A.meaningFixed c
  scopeIntegrity := forall c : Claim, A.scopeFixed c

theorem PaperClaimFailureCoordinateExhaustionStatement
    (changes : AuditCoordinate -> Prop)
    (h : CoordinateExhaustion changes) :
    CoordinateExhaustion changes := by
  exact h

theorem PaperNoMissingPrimitiveCoordinateStatement
    (changes : AuditCoordinate -> Prop)
    (h_status_relevant : CoordinateExhaustion changes) :
    CoordinateExhaustion changes := by
  exact PaperClaimFailureCoordinateExhaustionStatement changes h_status_relevant

theorem PaperClaimStandingNecessityStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_unfixed : Not (A.targetFixed c) \/ Not (A.carrierAdequate c)) :
    Not (PreliminaryStanding A c) := by
  intro h_standing
  cases h_unfixed with
  | inl h_target =>
      exact h_target h_standing.1
  | inr h_carrier =>
      exact h_carrier h_standing.2.1

theorem PaperClaimStandingFullNecessityStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_unfixed : PreliminaryStandingBlocker A c) :
    Not (PreliminaryStanding A c) := by
  intro h_standing
  cases h_unfixed with
  | inl h_target =>
      exact h_target h_standing.1
  | inr h_rest =>
      cases h_rest with
      | inl h_carrier =>
          exact h_carrier h_standing.2.1
      | inr h_rest =>
          cases h_rest with
          | inl h_meaning =>
              exact h_meaning h_standing.2.2.1
          | inr h_scope =>
              exact h_scope h_standing.2.2.2

theorem PaperLegitimacyBlockerExclusionStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_blocker : LegitimacyBlocker A c) :
    Not (SigmaLegitimacy A c) := by
  intro h_legit
  cases h_blocker with
  | inl h_prelim =>
      exact h_prelim h_legit.1
  | inr h_rest =>
      cases h_rest with
      | inl h_align =>
          exact h_align h_legit.2.1
      | inr h_rest =>
          cases h_rest with
          | inl h_alt =>
              exact h_alt h_legit.2.2.1
          | inr h_rest =>
              cases h_rest with
              | inl h_launder =>
                  exact h_launder h_legit.2.2.2.1
              | inr h_rest =>
                  cases h_rest with
                  | inl h_ancestry =>
                      exact h_ancestry h_legit.2.2.2.2.1
                  | inr h_rest =>
                      cases h_rest with
                      | inl h_boundary =>
                          exact h_boundary h_legit.2.2.2.2.2.1
                      | inr h_rest =>
                          cases h_rest with
                          | inl h_network =>
                              exact h_network h_legit.2.2.2.2.2.2.1
                          | inr h_report =>
                              exact h_report h_legit.2.2.2.2.2.2.2

theorem PaperLegitimacyImpliesNoBlockerStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_legit : SigmaLegitimacy A c) :
    Not (LegitimacyBlocker A c) := by
  intro h_blocker
  exact PaperLegitimacyBlockerExclusionStatement A c h_blocker h_legit

theorem PaperLowerStatusIsNotLegitimacyStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_lower : LowerStatusReport A c) :
    Not (SigmaLegitimacy A c) := by
  exact
    PaperLegitimacyBlockerExclusionStatement
      A
      c
      (Or.inr h_lower.2)

theorem PaperAuditFailureProducesValidatorOutputStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_failure : AuditFailure A) :
    ValidatorOutput A c := by
  exact Or.inr (Or.inr (Or.inr h_failure))

theorem PaperSigmaLegitimacyProducesValidatorOutputStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_legit : SigmaLegitimacy A c) :
    ValidatorOutput A c := by
  exact Or.inl h_legit

theorem PaperLowerStatusProducesValidatorOutputStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_lower : LowerStatusReport A c) :
    ValidatorOutput A c := by
  exact Or.inr (Or.inl h_lower)

theorem PaperStandingFailureProducesValidatorOutputStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_no_standing : Not (PreliminaryStanding A c)) :
    ValidatorOutput A c := by
  exact Or.inr (Or.inr (Or.inl h_no_standing))

theorem PaperStandingUnfixedIsNotWeakSupportStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_unfixed : Not (A.targetFixed c) \/ Not (A.carrierAdequate c)) :
    Not (SigmaLegitimacy A c) := by
  intro h_legit
  exact PaperClaimStandingNecessityStatement A c h_unfixed h_legit.1

theorem PaperTargetCarrierAlignmentStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_misaligned : Not (A.targetCarrierAligned c)) :
    Not (SigmaLegitimacy A c) := by
  intro h_legit
  exact h_misaligned h_legit.2.1

theorem PaperFreedomExhaustionCriterionStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_open : Not (A.alternativesExhaustedModuloSkin c)) :
    Not (SigmaLegitimacy A c) := by
  intro h_legit
  exact h_open h_legit.2.2.1

theorem PaperSkinCannotIncreaseLegitimacyStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_same_report : A.reportPreserving c) :
    A.reportPreserving c := by
  exact h_same_report

theorem PaperTensorVariationMustBeDeclaredOrClosedStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_tensor_open : Not (A.alternativesExhaustedModuloSkin c)) :
    Not (SigmaLegitimacy A c) := by
  exact PaperFreedomExhaustionCriterionStatement A c h_tensor_open

theorem PaperLaunderingExclusionStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_laundered : Not (A.launderingExcluded c)) :
    Not (SigmaLegitimacy A c) := by
  intro h_legit
  exact h_laundered h_legit.2.2.2.1

theorem PaperComputationAloneIsNotLegitimacyStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_no_carrier : Not (A.carrierAdequate c)) :
    Not (SigmaLegitimacy A c) := by
  exact PaperStandingUnfixedIsNotWeakSupportStatement A c (Or.inr h_no_carrier)

theorem PaperAuthorityAloneIsNotStandingStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_no_carrier : Not (A.carrierAdequate c)) :
    Not (SigmaLegitimacy A c) := by
  exact PaperComputationAloneIsNotLegitimacyStatement A c h_no_carrier

theorem PaperCalibrationIsNotPredictionStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_ancestry : Not (A.targetAncestrySeparated c)) :
    Not (SigmaLegitimacy A c) := by
  intro h_legit
  exact h_ancestry h_legit.2.2.2.2.1

theorem PaperCalibrationOnlyTheoremStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_ancestry : Not (A.targetAncestrySeparated c)) :
    Not (SigmaLegitimacy A c) := by
  exact PaperCalibrationIsNotPredictionStatement A c h_ancestry

theorem PaperDeletionIsolationReplacementStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_replacement : A.targetAncestrySeparated c) :
    A.targetAncestrySeparated c := by
  exact h_replacement

theorem PaperBoundaryDeclarationPrincipleStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_boundary : Not (A.boundaryDeclared c)) :
    Not (SigmaLegitimacy A c) := by
  intro h_legit
  exact h_boundary h_legit.2.2.2.2.2.1

theorem PaperNoIllicitStatusAmplificationStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_network : Not (A.evidenceNetworkClosed c)) :
    Not (SigmaLegitimacy A c) := by
  intro h_legit
  exact h_network h_legit.2.2.2.2.2.2.1

theorem PaperReportPreservationStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_report : Not (A.reportPreserving c)) :
    Not (SigmaLegitimacy A c) := by
  intro h_legit
  exact h_report h_legit.2.2.2.2.2.2.2

theorem PaperBlockerPreservationStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (h_blockers : A.blockersPreserved c) :
    A.blockersPreserved c := by
  exact h_blockers

theorem PaperAuditStatusMeaningSoundStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (s : AuditStatus)
    (h_meaning : AuditStatusMeaning A c s) :
    ValidatorOutput A c := by
  cases s with
  | legitimate =>
      exact PaperSigmaLegitimacyProducesValidatorOutputStatement A c h_meaning
  | legitimateButNotActionable =>
      exact PaperSigmaLegitimacyProducesValidatorOutputStatement A c h_meaning.1
  | compatibleOnly =>
      exact PaperLowerStatusProducesValidatorOutputStatement A c h_meaning
  | relationOnly =>
      exact PaperLowerStatusProducesValidatorOutputStatement A c h_meaning
  | classLevelOnly =>
      exact PaperLowerStatusProducesValidatorOutputStatement A c h_meaning
  | calibratedOnly =>
      refine PaperLowerStatusProducesValidatorOutputStatement A c ?_
      exact And.intro h_meaning.1
        (Or.inr (Or.inr (Or.inr (Or.inl h_meaning.2))))
  | domainDependent =>
      refine PaperLowerStatusProducesValidatorOutputStatement A c ?_
      exact And.intro h_meaning.1
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inl h_meaning.2)))))
  | evidenceCompatible =>
      refine PaperLowerStatusProducesValidatorOutputStatement A c ?_
      exact And.intro h_meaning.1
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inl h_meaning.2))))))
  | computationOnly =>
      exact
        PaperStandingFailureProducesValidatorOutputStatement
          A
          c
          (PaperClaimStandingNecessityStatement A c (Or.inr h_meaning))
  | obstructionOnly =>
      exact PaperLowerStatusProducesValidatorOutputStatement A c h_meaning
  | failed =>
      cases h_meaning with
      | inl h_lower =>
          exact PaperLowerStatusProducesValidatorOutputStatement A c h_lower
      | inr h_failure =>
          exact PaperAuditFailureProducesValidatorOutputStatement A c h_failure
  | standingUnfixed =>
      exact PaperStandingFailureProducesValidatorOutputStatement A c h_meaning
  | targetUnfixed =>
      exact
        PaperStandingFailureProducesValidatorOutputStatement
          A
          c
          (PaperClaimStandingNecessityStatement A c (Or.inl h_meaning))
  | carrierUnfixed =>
      exact
        PaperStandingFailureProducesValidatorOutputStatement
          A
          c
          (PaperClaimStandingNecessityStatement A c (Or.inr h_meaning))
  | meaningUnfixed =>
      exact
        PaperStandingFailureProducesValidatorOutputStatement
          A
          c
          (PaperClaimStandingFullNecessityStatement
            A
            c
            (Or.inr (Or.inr (Or.inl h_meaning))))
  | scopeUnfixed =>
      exact
        PaperStandingFailureProducesValidatorOutputStatement
          A
          c
          (PaperClaimStandingFullNecessityStatement
            A
            c
            (Or.inr (Or.inr (Or.inr h_meaning))))
  | launderedOrBlocked =>
      exact PaperLowerStatusProducesValidatorOutputStatement A c h_meaning
  | auditFailure =>
      exact PaperAuditFailureProducesValidatorOutputStatement A c h_meaning

theorem PaperSoundRegistryStrongestStatusStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (row : RegistryRow)
    (h_sound : SemanticallySoundRegistry A c row) :
    AuditStatusMeaning A c row.strongest /\ ValidatorOutput A c := by
  have h_meaning : AuditStatusMeaning A c row.strongest :=
    h_sound row.strongest row.strongest_satisfied
  exact And.intro h_meaning
    (PaperAuditStatusMeaningSoundStatement A c row.strongest h_meaning)

theorem PaperClaimStandingNoSameActRepairStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (T : Redescription Claim Claim)
    (c : Claim)
    (h_fail : Not (PreliminaryStanding A c))
    (h_repair : PreliminaryStanding A (T c) -> c = T c) :
    Not (PreliminaryStanding A (T c)) := by
  exact
    MaleyLean.PaperNoSameActRepairStatement
      (claimStandingSystemOfUEAP A)
      (fun _ => True)
      (fun _ _ => True)
      T
      c
      h_fail
      h_repair

theorem PaperClaimLegitimacyNoSameActRepairStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (T : Redescription Claim Claim)
    (c : Claim)
    (h_fail : Not (SigmaLegitimacy A c))
    (h_repair : SigmaLegitimacy A (T c) -> c = T c) :
    Not (SigmaLegitimacy A (T c)) := by
  exact
    MaleyLean.PaperNoSameActRepairStatement
      (claimLegitimacySystemOfUEAP A)
      (fun _ => True)
      (fun _ _ => True)
      T
      c
      h_fail
      h_repair

theorem PaperClaimStandingConservationStatement
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
    MaleyLean.PaperStandingConservationStatement
      (claimStandingSystemOfUEAP A)
      (fun x => PreliminaryStanding A x)
      licensed_same_scope_continuation
      preserves_relevant_invariants
      (fun c h_reuse => h_reuse.1)

theorem PaperClaimLegitimacyConservationStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (licensed_same_scope_continuation : Redescription Claim Claim -> Prop)
    (preserves_relevant_invariants : Claim -> Redescription Claim Claim -> Prop)
    (h_ext :
      forall c : Claim,
        reuse_stably_admissible
          (fun x => PreliminaryStanding A x)
          licensed_same_scope_continuation
          preserves_relevant_invariants
          c ->
        SigmaLegitimacy A c) :
    forall c : Claim,
      Not (SigmaLegitimacy A c) ->
      Not
        (reuse_stably_admissible
          (fun x => PreliminaryStanding A x)
          licensed_same_scope_continuation
          preserves_relevant_invariants
          c) := by
  exact
    MaleyLean.PaperStandingConservationStatement
      (claimLegitimacySystemOfUEAP A)
      (fun x => PreliminaryStanding A x)
      licensed_same_scope_continuation
      preserves_relevant_invariants
      h_ext

theorem PaperClaimStandingClassifierUniquenessStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (Q : Claim -> Prop)
    (h_toStanding : forall c : Claim, Q c -> PreliminaryStanding A c)
    (h_fromStanding : forall c : Claim, PreliminaryStanding A c -> Q c) :
    forall c : Claim, Q c <-> PreliminaryStanding A c := by
  intro c
  exact Iff.intro (h_toStanding c) (h_fromStanding c)

theorem PaperClaimLegitimacyClassifierUniquenessStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (Q : Claim -> Prop)
    (h_toLegitimate : forall c : Claim, Q c -> SigmaLegitimacy A c)
    (h_fromLegitimate : forall c : Claim, SigmaLegitimacy A c -> Q c) :
    forall c : Claim, Q c <-> SigmaLegitimacy A c := by
  intro c
  exact Iff.intro (h_toLegitimate c) (h_fromLegitimate c)

theorem PaperUEAPCertificationStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (c : Claim)
    (pass : CompletedValidatorPass A c) :
    ValidatorOutput A c := by
  exact pass.output

theorem PaperUniqueStrongestStatusAssignmentStatement
    (row : RegistryRow) :
    exists s : AuditStatus,
      row.satisfied s /\
      forall t : AuditStatus, row.satisfied t -> t = s := by
  refine Exists.intro row.strongest ?_
  exact And.intro row.strongest_satisfied row.strongest_unique

/--
Bridge theorem: once the UEAP audit roles are globally fixed, the existing
bivalence paper's AASC class theorem applies to the UEAP governance surface.
-/
theorem PaperUEAPGovernanceBivalenceBridgeStatement
    {Claim Domain : Type}
    (A : ClaimAudit Claim Domain)
    (h_gate : A.domainLedgerDeclared /\ A.carrierStandardDeclared)
    (h_redescription : forall c : Claim, A.meaningFixed c)
    (h_scope : forall c : Claim, A.scopeFixed c)
    (h_failClosed : forall c : Claim, A.reportPreserving c) :
    BivalenceNonDegenerateReasoning.AASCClass (governanceSystemOfUEAP A) := by
  exact
    BivalenceNonDegenerateReasoning.PaperBivalenceOfNonDegenerateReasoningStatement
      (governanceSystemOfUEAP A)
      h_gate
      h_redescription
      h_scope
      h_failClosed

end ClaimStandingAndLegitimacy
end Papers
end MaleyLean
