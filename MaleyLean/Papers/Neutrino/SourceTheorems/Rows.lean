import MaleyLean.Papers.Neutrino.RatioBlocker

namespace MaleyLean

namespace Neutrino

/--
MR3 obligations at the primary-source-row level.

Each field is tied to the canonical source row assigned by
`primarySourceForCoreFrontierField`.
-/
structure MR3PrimaryRowTheorems
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

/-- Hybrid cross-obligations at the primary-source-row level. -/
structure HybridPrimaryRowTheorems
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M) where
  crossTargetAligned :
    AASCPrimarySourceBackedProof .h_crossTargetAligned H.crossTargetAligned
  crossTransportCoherent :
    AASCPrimarySourceBackedProof
      .h_crossTransportCoherent
      H.crossTransportCoherent
  crossNoOvercounting :
    AASCPrimarySourceBackedProof .h_crossNoOvercounting H.crossNoOvercounting
  crossCalibrationFree :
    AASCPrimarySourceBackedProof
      .h_crossCalibrationFree
      H.crossCalibrationFree
  crossNoHiddenSelector :
    AASCPrimarySourceBackedProof .h_crossNoHiddenSelector H.crossNoHiddenSelector

/-- No-eleventh-route obligations at the primary-source-row level. -/
structure CensusPrimaryRowTheorems
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
  noExperimentalMethodOutsideCensus :
    AASCPrimarySourceBackedProof
      .n_noExperimentalMethodOutsideCensus
      N.noExperimentalMethodOutsideCensus
  noScopeChangingRouteCountsSameScope :
    AASCPrimarySourceBackedProof
      .n_noScopeChangingRouteCountsSameScope
      N.noScopeChangingRouteCountsSameScope
  noEmpiricalValueImportAsRoute :
    AASCPrimarySourceBackedProof
      .n_noEmpiricalValueImportAsRoute
      N.noEmpiricalValueImportAsRoute

/-- Operational UEAP/kernel obligations at the primary-source-row level. -/
structure OperationalPrimaryRowTheorems
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  audit :
    MaleyLean.Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit
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

end Neutrino

end MaleyLean
