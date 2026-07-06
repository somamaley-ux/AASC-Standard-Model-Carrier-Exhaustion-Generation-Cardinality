import MaleyLean.Papers.Neutrino.SourceTheorems.Core

namespace MaleyLean

namespace Neutrino

/--
Raw MR3 proof terms.

This is the interface a future formalized MR3 module should target: it proves
ordinary propositions, and this file handles the source-row wrapping.
-/
structure MR3ShapeSourceProofTerms
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) where
  sourceCertified : M.sourceCertified
  standingSpectralCarrier : M.standingSpectralCarrier
  quotientStable : M.quotientStable
  transportClosed : M.transportClosed
  calibrationFree : M.calibrationFree
  extractionCertified : M.extractionCertified
  sourceInducesShapeMap : M.sourceInducesShapeMap

def MR3ShapeSourceProofTerms.asSourceRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (T : MR3ShapeSourceProofTerms M) :
  MR3ShapeSourceRows M :=
  { sourceCertified := { proof := T.sourceCertified }
    standingSpectralCarrier := { proof := T.standingSpectralCarrier }
    quotientStable := { proof := T.quotientStable }
    transportClosed := { proof := T.transportClosed }
    calibrationFree := { proof := T.calibrationFree }
    extractionCertified := { proof := T.extractionCertified }
    sourceInducesShapeMap := { proof := T.sourceInducesShapeMap } }

structure EX8OverconstraintProofTerms
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M) where
  crossTargetAligned : H.crossTargetAligned

def EX8OverconstraintProofTerms.asSourceRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (T : EX8OverconstraintProofTerms H) :
  EX8OverconstraintRows H :=
  { crossTargetAligned := { proof := T.crossTargetAligned } }

structure NOARUniversalOscillationProofTerms
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M) where
  crossTransportCoherent : H.crossTransportCoherent
  crossNoOvercounting : H.crossNoOvercounting

def NOARUniversalOscillationProofTerms.asSourceRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (T : NOARUniversalOscillationProofTerms H) :
  NOARUniversalOscillationRows H :=
  { crossTransportCoherent := { proof := T.crossTransportCoherent }
    crossNoOvercounting := { proof := T.crossNoOvercounting } }

structure UEAPSourceProofTerms
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (audit :
    MaleyLean.Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit) where
  crossCalibrationFree : H.crossCalibrationFree
  crossNoHiddenSelector : H.crossNoHiddenSelector
  jointSurvivorUEAPLegitimacy :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              MaleyLean.Papers.ClaimStandingAndLegitimacy.SigmaLegitimacy
                audit
                (routeCarrierDraftClass (N.carrierOf r))

def UEAPSourceProofTerms.asSourceRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  {audit :
    MaleyLean.Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit}
  (T : UEAPSourceProofTerms (C := C) (M := M) (H := H) (N := N) audit) :
  UEAPSourceRows (C := C) (M := M) (H := H) (N := N) audit :=
  { crossCalibrationFree := { proof := T.crossCalibrationFree }
    crossNoHiddenSelector := { proof := T.crossNoHiddenSelector }
    jointSurvivorUEAPLegitimacy :=
      { proof := T.jointSurvivorUEAPLegitimacy } }

structure CS6CSourceProofTerms
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  noUncarriedSameTargetConstraint :
    N.noUncarriedSameTargetConstraint
  noLegacyTheoryOutsideCensus :
    N.noLegacyTheoryOutsideCensus
  noScopeChangingRouteCountsSameScope :
    N.noScopeChangingRouteCountsSameScope

def CS6CSourceProofTerms.asSourceRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (T : CS6CSourceProofTerms N) :
  CS6CSourceRows N :=
  { noUncarriedSameTargetConstraint :=
      { proof := T.noUncarriedSameTargetConstraint }
    noLegacyTheoryOutsideCensus :=
      { proof := T.noLegacyTheoryOutsideCensus }
    noScopeChangingRouteCountsSameScope :=
      { proof := T.noScopeChangingRouteCountsSameScope } }

structure CS7SourceProofTerms
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  noExperimentalMethodOutsideCensus :
    N.noExperimentalMethodOutsideCensus
  noEmpiricalValueImportAsRoute :
    N.noEmpiricalValueImportAsRoute

def CS7SourceProofTerms.asSourceRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (T : CS7SourceProofTerms N) :
  CS7SourceRows N :=
  { noExperimentalMethodOutsideCensus :=
      { proof := T.noExperimentalMethodOutsideCensus }
    noEmpiricalValueImportAsRoute :=
      { proof := T.noEmpiricalValueImportAsRoute } }

structure ROCSourceProofTerms
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (audit :
    MaleyLean.Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit) where
  currentPointIdentification :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio
  kernelForcedUEAPFailure :
    forall i : NeutrinoDraftCandidateIndex,
      forall hne :
        Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio),
        AASCUEAPLegitimacyFailureHolds
          audit
          i
          (defaultUEAPFailureKindForNoncurrentBranch i hne)

def ROCSourceProofTerms.asSourceRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  {audit :
    MaleyLean.Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit}
  (T : ROCSourceProofTerms C M H N audit) :
  ROCSourceRows C M H N audit :=
  { currentPointIdentification :=
      { proof := T.currentPointIdentification }
    kernelForcedUEAPFailure :=
      { proof := T.kernelForcedUEAPFailure } }

/--
Raw proof-term package for all source IDs supporting the NNR8 endpoint.

This is the smallest practical Lean target for the next clearing pass.
-/
structure AASCNNR8RawSourceProofTerms
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  audit :
    MaleyLean.Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit
  mr3 : MR3ShapeSourceProofTerms M
  ex8 : EX8OverconstraintProofTerms H
  noar : NOARUniversalOscillationProofTerms H
  ueap : UEAPSourceProofTerms (C := C) (M := M) (H := H) (N := N) audit
  cs6c : CS6CSourceProofTerms N
  cs7 : CS7SourceProofTerms N
  roc : ROCSourceProofTerms C M H N audit

def rawSourceProofTermsAsPrimarySourceIDModules
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (T : AASCNNR8RawSourceProofTerms C M H N) :
  AASCNNR8PrimarySourceIDModules C M H N :=
  { audit := T.audit
    mr3 := T.mr3.asSourceRows
    ex8 := T.ex8.asSourceRows
    noar := T.noar.asSourceRows
    ueap := T.ueap.asSourceRows
    cs6c := T.cs6c.asSourceRows
    cs7 := T.cs7.asSourceRows
    roc := T.roc.asSourceRows }

theorem rawSourceProofTermsGiveEndpointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (T : AASCNNR8RawSourceProofTerms C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    primarySourceIDModulesGiveEndpointSingleton
      C
      M
      H
      N
      S
      (rawSourceProofTermsAsPrimarySourceIDModules C M H N T)

theorem rawSourceProofTermsRuleOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (T : AASCNNR8RawSourceProofTerms C M H N) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    primarySourceIDModulesRuleOutSecondPoint
      C
      M
      H
      N
      S
      (rawSourceProofTermsAsPrimarySourceIDModules C M H N T)

end Neutrino

end MaleyLean
