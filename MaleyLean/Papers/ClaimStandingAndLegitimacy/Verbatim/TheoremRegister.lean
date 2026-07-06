namespace MaleyLean
namespace Papers
namespace ClaimStandingAndLegitimacy
namespace Verbatim

/-- Verbatim manuscript title extracted from the supplied UEAP source bundle. -/
def manuscriptTitle : String :=
  "Claim Standing and Legitimacy: A Universal Audit Protocol for Laundering Exclusion and Reportable Output"

/-- Main section spine extracted from the manuscript. -/
inductive SectionTag where
  | introductionClaimLegitimacyProblem
  | fromExactnessToClaimStanding
  | proofStatusAndProtocolLayers
  | auditObjectsAndStanding
  | freedomLedgersAndSkinTensorSeparation
  | launderingTaxonomyAndExclusion
  | calibrationProxyAndAncestryGraphs
  | domainScopeAndBoundaryClosure
  | evidenceNetworksAndNoAmplification
  | reportabilityAndActionability
  | validatorProtocolAndRegistry
  | pilotAuditsAndDeploymentManuals
deriving DecidableEq, Repr

def sectionTitle : SectionTag -> String
  | .introductionClaimLegitimacyProblem =>
      "Introduction: the claim-legitimacy problem"
  | .fromExactnessToClaimStanding =>
      "From exactness to claim standing"
  | .proofStatusAndProtocolLayers =>
      "Proof status and protocol layers"
  | .auditObjectsAndStanding =>
      "Audit objects and claim standing"
  | .freedomLedgersAndSkinTensorSeparation =>
      "Freedom ledgers and skin/tensor separation"
  | .launderingTaxonomyAndExclusion =>
      "Laundering taxonomy and exclusion"
  | .calibrationProxyAndAncestryGraphs =>
      "Calibration, proxy, and ancestry graphs"
  | .domainScopeAndBoundaryClosure =>
      "Domain, scope, and boundary closure"
  | .evidenceNetworksAndNoAmplification =>
      "Evidence networks and no illicit status-amplification"
  | .reportabilityAndActionability =>
      "Reportability and actionability"
  | .validatorProtocolAndRegistry =>
      "Validator protocol and registry"
  | .pilotAuditsAndDeploymentManuals =>
      "Pilot audits and deployment manuals"

/-- Paper-facing theorem/proposition spine extracted from the UEAP manuscript. -/
inductive ResultTag where
  | claimFailureCoordinateExhaustion
  | noMissingPrimitiveCoordinate
  | claimStandingNecessity
  | standingUnfixedIsNotWeakSupport
  | targetCarrierAlignment
  | freedomExhaustionCriterion
  | skinCannotIncreaseLegitimacy
  | tensorVariationMustBeDeclaredOrClosed
  | launderingExclusion
  | computationAloneIsNotLegitimacy
  | authorityAloneIsNotStanding
  | calibrationIsNotPrediction
  | calibrationOnlyTheorem
  | deletionIsolationReplacement
  | boundaryDeclarationPrinciple
  | noIllicitStatusAmplification
  | reportPreservation
  | blockerPreservation
  | ueapCertificationTheorem
  | uniqueStrongestStatusAssignment
  | auditStatusMeaningSoundness
  | soundRegistryStrongestStatus
  | claimStandingNoSameActRepair
  | claimLegitimacyNoSameActRepair
  | claimStandingConservation
  | claimLegitimacyConservation
  | claimStandingClassifierUniqueness
  | claimLegitimacyClassifierUniqueness
deriving DecidableEq, Repr

def resultTitle : ResultTag -> String
  | .claimFailureCoordinateExhaustion =>
      "Claim-Failure Coordinate Exhaustion"
  | .noMissingPrimitiveCoordinate =>
      "No missing primitive coordinate"
  | .claimStandingNecessity =>
      "Claim Standing Necessity"
  | .standingUnfixedIsNotWeakSupport =>
      "Standing-unfixed is not weak support"
  | .targetCarrierAlignment =>
      "Target-carrier alignment"
  | .freedomExhaustionCriterion =>
      "Freedom Exhaustion Criterion"
  | .skinCannotIncreaseLegitimacy =>
      "Skin cannot increase legitimacy"
  | .tensorVariationMustBeDeclaredOrClosed =>
      "Tensor variation must be declared or closed"
  | .launderingExclusion =>
      "Laundering Exclusion"
  | .computationAloneIsNotLegitimacy =>
      "Computation alone is not legitimacy"
  | .authorityAloneIsNotStanding =>
      "Authority alone is not standing"
  | .calibrationIsNotPrediction =>
      "Calibration is not prediction"
  | .calibrationOnlyTheorem =>
      "Calibration-Only Theorem"
  | .deletionIsolationReplacement =>
      "Deletion, isolation, replacement"
  | .boundaryDeclarationPrinciple =>
      "Boundary Declaration Principle"
  | .noIllicitStatusAmplification =>
      "No Illicit Status-Amplification Theorem"
  | .reportPreservation =>
      "Report Preservation Theorem"
  | .blockerPreservation =>
      "Blocker preservation"
  | .ueapCertificationTheorem =>
      "UEAP Certification Theorem"
  | .uniqueStrongestStatusAssignment =>
      "Unique Strongest Status Assignment"
  | .auditStatusMeaningSoundness =>
      "Audit Status Meaning Soundness"
  | .soundRegistryStrongestStatus =>
      "Sound Registry Strongest Status"
  | .claimStandingNoSameActRepair =>
      "Claim Standing No Same-Act Repair"
  | .claimLegitimacyNoSameActRepair =>
      "Claim Legitimacy No Same-Act Repair"
  | .claimStandingConservation =>
      "Claim Standing Conservation"
  | .claimLegitimacyConservation =>
      "Claim Legitimacy Conservation"
  | .claimStandingClassifierUniqueness =>
      "Claim Standing Classifier Uniqueness"
  | .claimLegitimacyClassifierUniqueness =>
      "Claim Legitimacy Classifier Uniqueness"

theorem manuscriptHasRegisteredTitle :
    manuscriptTitle =
      "Claim Standing and Legitimacy: A Universal Audit Protocol for Laundering Exclusion and Reportable Output" := by
  rfl

theorem manuscriptHasUEAPCertificationEntry :
    resultTitle .ueapCertificationTheorem =
      "UEAP Certification Theorem" := by
  rfl

end Verbatim
end ClaimStandingAndLegitimacy
end Papers
end MaleyLean
