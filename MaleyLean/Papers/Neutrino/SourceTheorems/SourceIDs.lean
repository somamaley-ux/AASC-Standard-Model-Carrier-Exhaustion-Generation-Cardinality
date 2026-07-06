import MaleyLean.Papers.Neutrino.SourceTheorems.Rows

namespace MaleyLean

namespace Neutrino

/--
Rows supplied by the MR3 shape-source theorem.

All seven MR3 frontier fields share the same primary source ID:
`AASCNNR8CoreSourceID.mr3ShapeSourceTheorem`.
-/
structure MR3ShapeSourceRows
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) where
  sourceCertified :
    AASCPrimarySourceBackedProof .mr3_sourceCertified M.sourceCertified
  standingSpectralCarrier :
    AASCPrimarySourceBackedProof
      .mr3_standingSpectralCarrier
      M.standingSpectralCarrier
  quotientStable :
    AASCPrimarySourceBackedProof .mr3_quotientStable M.quotientStable
  transportClosed :
    AASCPrimarySourceBackedProof .mr3_transportClosed M.transportClosed
  calibrationFree :
    AASCPrimarySourceBackedProof .mr3_calibrationFree M.calibrationFree
  extractionCertified :
    AASCPrimarySourceBackedProof .mr3_extractionCertified M.extractionCertified
  sourceInducesShapeMap :
    AASCPrimarySourceBackedProof
      .mr3_sourceInducesShapeMap
      M.sourceInducesShapeMap

/-- Rows supplied by the EX8 overconstraint-legitimacy source. -/
structure EX8OverconstraintRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M) where
  crossTargetAligned :
    AASCPrimarySourceBackedProof .h_crossTargetAligned H.crossTargetAligned

/-- Rows supplied by the NOAR universal oscillation quotient source. -/
structure NOARUniversalOscillationRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M) where
  crossTransportCoherent :
    AASCPrimarySourceBackedProof
      .h_crossTransportCoherent
      H.crossTransportCoherent
  crossNoOvercounting :
    AASCPrimarySourceBackedProof .h_crossNoOvercounting H.crossNoOvercounting

/-- Rows supplied by the UEAP source family. -/
structure UEAPSourceRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (audit :
    MaleyLean.Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit) where
  crossCalibrationFree :
    AASCPrimarySourceBackedProof
      .h_crossCalibrationFree
      H.crossCalibrationFree
  crossNoHiddenSelector :
    AASCPrimarySourceBackedProof .h_crossNoHiddenSelector H.crossNoHiddenSelector
  jointSurvivorUEAPLegitimacy :
    AASCPrimarySourceBackedProof
      .operational_jointSurvivorUEAPLegitimacy
      (forall r : C.Ratio,
        C.inMinimalInterval r ->
          H.modular.ModularRestriction r ->
            H.spectral.spectralRestriction r ->
              H.scoto.scotoRestriction r ->
                MaleyLean.Papers.ClaimStandingAndLegitimacy.SigmaLegitimacy
                  audit
                  (routeCarrierDraftClass (N.carrierOf r)))

/-- Rows supplied by the CS6C same-scope and scope-extension sources. -/
structure CS6CSourceRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  noUncarriedSameTargetConstraint :
    AASCPrimarySourceBackedProof
      .n_noUncarriedSameTargetConstraint
      N.noUncarriedSameTargetConstraint
  noLegacyTheoryOutsideCensus :
    AASCPrimarySourceBackedProof
      .n_noLegacyTheoryOutsideCensus
      N.noLegacyTheoryOutsideCensus
  noScopeChangingRouteCountsSameScope :
    AASCPrimarySourceBackedProof
      .n_noScopeChangingRouteCountsSameScope
      N.noScopeChangingRouteCountsSameScope

/-- Rows supplied by the CS7 PMNS value-promotion/deferred-value sources. -/
structure CS7SourceRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  noExperimentalMethodOutsideCensus :
    AASCPrimarySourceBackedProof
      .n_noExperimentalMethodOutsideCensus
      N.noExperimentalMethodOutsideCensus
  noEmpiricalValueImportAsRoute :
    AASCPrimarySourceBackedProof
      .n_noEmpiricalValueImportAsRoute
      N.noEmpiricalValueImportAsRoute

/-- Rows supplied by the ROC role-occupancy/lawful-route sources. -/
structure ROCSourceRows
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (audit :
    MaleyLean.Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit) where
  currentPointIdentification :
    AASCPrimarySourceBackedProof
      .operational_currentPointIdentification
      (forall r : C.Ratio,
        C.inMinimalInterval r ->
          H.modular.ModularRestriction r ->
            H.spectral.spectralRestriction r ->
              H.scoto.scotoRestriction r ->
                routeCarrierDraftClass (N.carrierOf r) =
                  NeutrinoDraftCandidateIndex.currentStandingRatio ->
                  r = C.ratio)
  kernelForcedUEAPFailure :
    AASCPrimarySourceBackedProof
      .operational_kernelForcedUEAPFailure
      (forall i : NeutrinoDraftCandidateIndex,
        forall hne :
          Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio),
          AASCUEAPLegitimacyFailureHolds
            audit
            i
            (defaultUEAPFailureKindForNoncurrentBranch i hne))

structure AASCNNR8PrimarySourceIDModules
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  audit :
    MaleyLean.Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit
  mr3 : MR3ShapeSourceRows M
  ex8 : EX8OverconstraintRows H
  noar : NOARUniversalOscillationRows H
  ueap : UEAPSourceRows (C := C) (M := M) (H := H) (N := N) audit
  cs6c : CS6CSourceRows N
  cs7 : CS7SourceRows N
  roc : ROCSourceRows C M H N audit

end Neutrino

end MaleyLean
