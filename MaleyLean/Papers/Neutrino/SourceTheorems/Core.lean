import MaleyLean.Papers.Neutrino.SourceTheorems.Census
import MaleyLean.Papers.Neutrino.SourceTheorems.Hybrid
import MaleyLean.Papers.Neutrino.SourceTheorems.MR3
import MaleyLean.Papers.Neutrino.SourceTheorems.OperationalKernel
import MaleyLean.Papers.Neutrino.SourceTheorems.SourceIDs

namespace MaleyLean

namespace Neutrino

/--
Imported source theorem interface for the NNR8 endpoint upgrade.

This is the formal "more comprehensive Lean layer" for the remaining corpus
sources. Each field is the exact proposition needed by
`AASCNNR8PrimarySemanticExtractionCertificate`, with the source-row assignment
fixed by `primarySourceForCoreFrontierField` in `RatioBlocker.lean`.

The intended implementation path is to replace fields of this structure by
theorems imported from formalized MR3, CS6C, CS7, ROC, NOAR, UEAP, EX8, and
MR5 modules as those modules are added.
-/
structure AASCNNR8ImportedSourceTheorems
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C) where
  audit :
    MaleyLean.Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit

  mr3_sourceCertified : M.sourceCertified
  mr3_standingSpectralCarrier : M.standingSpectralCarrier
  mr3_quotientStable : M.quotientStable
  mr3_transportClosed : M.transportClosed
  mr3_calibrationFree : M.calibrationFree
  mr3_extractionCertified : M.extractionCertified
  mr3_sourceInducesShapeMap : M.sourceInducesShapeMap

  h_crossTargetAligned : H.crossTargetAligned
  h_crossTransportCoherent : H.crossTransportCoherent
  h_crossNoOvercounting : H.crossNoOvercounting
  h_crossCalibrationFree : H.crossCalibrationFree
  h_crossNoHiddenSelector : H.crossNoHiddenSelector

  n_noUncarriedSameTargetConstraint :
    N.noUncarriedSameTargetConstraint
  n_noLegacyTheoryOutsideCensus :
    N.noLegacyTheoryOutsideCensus
  n_noExperimentalMethodOutsideCensus :
    N.noExperimentalMethodOutsideCensus
  n_noScopeChangingRouteCountsSameScope :
    N.noScopeChangingRouteCountsSameScope
  n_noEmpiricalValueImportAsRoute :
    N.noEmpiricalValueImportAsRoute

  currentPointIdentification :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio

  jointSurvivorUEAPLegitimacy :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              MaleyLean.Papers.ClaimStandingAndLegitimacy.SigmaLegitimacy
                audit
                (routeCarrierDraftClass (N.carrierOf r))

  kernelForcedUEAPFailure :
    forall i : NeutrinoDraftCandidateIndex,
      forall hne :
        Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio),
        AASCUEAPLegitimacyFailureHolds
          audit
          i
          (defaultUEAPFailureKindForNoncurrentBranch i hne)

def importedSourceTheoremsAsPrimarySemanticExtraction
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (T : AASCNNR8ImportedSourceTheorems C M H N S) :
  AASCNNR8PrimarySemanticExtractionCertificate C M H N S :=
  { audit := T.audit
    mr3_sourceCertified :=
      { proof := T.mr3_sourceCertified }
    mr3_standingSpectralCarrier :=
      { proof := T.mr3_standingSpectralCarrier }
    mr3_quotientStable :=
      { proof := T.mr3_quotientStable }
    mr3_transportClosed :=
      { proof := T.mr3_transportClosed }
    mr3_calibrationFree :=
      { proof := T.mr3_calibrationFree }
    mr3_extractionCertified :=
      { proof := T.mr3_extractionCertified }
    mr3_sourceInducesShapeMap :=
      { proof := T.mr3_sourceInducesShapeMap }

    h_crossTargetAligned :=
      { proof := T.h_crossTargetAligned }
    h_crossTransportCoherent :=
      { proof := T.h_crossTransportCoherent }
    h_crossNoOvercounting :=
      { proof := T.h_crossNoOvercounting }
    h_crossCalibrationFree :=
      { proof := T.h_crossCalibrationFree }
    h_crossNoHiddenSelector :=
      { proof := T.h_crossNoHiddenSelector }

    n_noUncarriedSameTargetConstraint :=
      { proof := T.n_noUncarriedSameTargetConstraint }
    n_noLegacyTheoryOutsideCensus :=
      { proof := T.n_noLegacyTheoryOutsideCensus }
    n_noExperimentalMethodOutsideCensus :=
      { proof := T.n_noExperimentalMethodOutsideCensus }
    n_noScopeChangingRouteCountsSameScope :=
      { proof := T.n_noScopeChangingRouteCountsSameScope }
    n_noEmpiricalValueImportAsRoute :=
      { proof := T.n_noEmpiricalValueImportAsRoute }

    currentPointIdentification :=
      { proof := T.currentPointIdentification }
    jointSurvivorUEAPLegitimacy :=
      { proof := T.jointSurvivorUEAPLegitimacy }
    kernelForcedUEAPFailure :=
      { proof := T.kernelForcedUEAPFailure } }

/--
Corpus-module assembly object.

This is one step deeper than `AASCNNR8ImportedSourceTheorems`: instead of a
flat list of endpoint obligations, it records which source family supplies
which part of the proof.
-/
structure AASCNNR8CorpusSourceModules
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  mr3 : MR3CorpusTheorems M
  hybrid : HybridCorpusTheorems H
  census : NoEleventhRouteCorpusTheorems N
  operational : OperationalKernelCorpusTheorems C M H N

/--
Primary-row assembly object.

This is the narrowest current interface: each obligation is backed by its
canonical primary source row, and the row proofs assemble into the source-family
modules above.
-/
structure AASCNNR8PrimaryRowModules
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  mr3 : MR3PrimaryRowTheorems M
  hybrid : HybridPrimaryRowTheorems H
  census : CensusPrimaryRowTheorems N
  operational : OperationalPrimaryRowTheorems C M H N

def primaryRowModulesAsCorpusSourceModules
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (R : AASCNNR8PrimaryRowModules C M H N) :
  AASCNNR8CorpusSourceModules C M H N :=
  { mr3 := R.mr3.asCorpusTheorems
    hybrid := R.hybrid.asCorpusTheorems
    census := R.census.asCorpusTheorems
    operational := R.operational.asCorpusTheorems }

def primarySourceIDModulesAsPrimaryRowModules
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCNNR8PrimarySourceIDModules C M H N) :
  AASCNNR8PrimaryRowModules C M H N :=
  { mr3 :=
      { sourceCertified := S.mr3.sourceCertified
        standingSpectralCarrier := S.mr3.standingSpectralCarrier
        quotientStable := S.mr3.quotientStable
        transportClosed := S.mr3.transportClosed
        calibrationFree := S.mr3.calibrationFree
        extractionCertified := S.mr3.extractionCertified
        sourceInducesShapeMap := S.mr3.sourceInducesShapeMap }
    hybrid :=
      { crossTargetAligned := S.ex8.crossTargetAligned
        crossTransportCoherent := S.noar.crossTransportCoherent
        crossNoOvercounting := S.noar.crossNoOvercounting
        crossCalibrationFree := S.ueap.crossCalibrationFree
        crossNoHiddenSelector := S.ueap.crossNoHiddenSelector }
    census :=
      { noUncarriedSameTargetConstraint :=
          S.cs6c.noUncarriedSameTargetConstraint
        noLegacyTheoryOutsideCensus :=
          S.cs6c.noLegacyTheoryOutsideCensus
        noExperimentalMethodOutsideCensus :=
          S.cs7.noExperimentalMethodOutsideCensus
        noScopeChangingRouteCountsSameScope :=
          S.cs6c.noScopeChangingRouteCountsSameScope
        noEmpiricalValueImportAsRoute :=
          S.cs7.noEmpiricalValueImportAsRoute }
    operational :=
      { audit := S.audit
        currentPointIdentification :=
          S.roc.currentPointIdentification
        jointSurvivorUEAPLegitimacy :=
          S.ueap.jointSurvivorUEAPLegitimacy
        kernelForcedUEAPFailure :=
          S.roc.kernelForcedUEAPFailure } }

def corpusSourceModulesAsImportedSourceTheorems
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (T : AASCNNR8CorpusSourceModules C M H N) :
  AASCNNR8ImportedSourceTheorems C M H N S :=
  { audit := T.operational.audit
    mr3_sourceCertified := T.mr3.sourceCertified
    mr3_standingSpectralCarrier := T.mr3.standingSpectralCarrier
    mr3_quotientStable := T.mr3.quotientStable
    mr3_transportClosed := T.mr3.transportClosed
    mr3_calibrationFree := T.mr3.calibrationFree
    mr3_extractionCertified := T.mr3.extractionCertified
    mr3_sourceInducesShapeMap := T.mr3.sourceInducesShapeMap

    h_crossTargetAligned := T.hybrid.crossTargetAligned
    h_crossTransportCoherent := T.hybrid.crossTransportCoherent
    h_crossNoOvercounting := T.hybrid.crossNoOvercounting
    h_crossCalibrationFree := T.hybrid.crossCalibrationFree
    h_crossNoHiddenSelector := T.hybrid.crossNoHiddenSelector

    n_noUncarriedSameTargetConstraint :=
      T.census.noUncarriedSameTargetConstraint
    n_noLegacyTheoryOutsideCensus :=
      T.census.noLegacyTheoryOutsideCensus
    n_noExperimentalMethodOutsideCensus :=
      T.census.noExperimentalMethodOutsideCensus
    n_noScopeChangingRouteCountsSameScope :=
      T.census.noScopeChangingRouteCountsSameScope
    n_noEmpiricalValueImportAsRoute :=
      T.census.noEmpiricalValueImportAsRoute

    currentPointIdentification :=
      T.operational.currentPointIdentification
    jointSurvivorUEAPLegitimacy :=
      T.operational.jointSurvivorUEAPLegitimacy
    kernelForcedUEAPFailure :=
      T.operational.kernelForcedUEAPFailure }

theorem corpusSourceModulesGiveEndpointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (T : AASCNNR8CorpusSourceModules C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    primarySemanticExtractionGivesEndpointSingleton
      C
      M
      H
      N
      S
      (importedSourceTheoremsAsPrimarySemanticExtraction
        C
        M
        H
        N
        S
        (corpusSourceModulesAsImportedSourceTheorems C M H N S T))

theorem corpusSourceModulesRuleOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (T : AASCNNR8CorpusSourceModules C M H N) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    primarySemanticExtractionRulesOutSecondPoint
      C
      M
      H
      N
      S
      (importedSourceTheoremsAsPrimarySemanticExtraction
        C
        M
        H
        N
        S
        (corpusSourceModulesAsImportedSourceTheorems C M H N S T))

theorem primaryRowModulesGiveEndpointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (R : AASCNNR8PrimaryRowModules C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    corpusSourceModulesGiveEndpointSingleton
      C
      M
      H
      N
      S
      (primaryRowModulesAsCorpusSourceModules C M H N R)

theorem primaryRowModulesRuleOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (R : AASCNNR8PrimaryRowModules C M H N) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    corpusSourceModulesRuleOutSecondPoint
      C
      M
      H
      N
      S
      (primaryRowModulesAsCorpusSourceModules C M H N R)

theorem primarySourceIDModulesGiveEndpointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (I : AASCNNR8PrimarySourceIDModules C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    primaryRowModulesGiveEndpointSingleton
      C
      M
      H
      N
      S
      (primarySourceIDModulesAsPrimaryRowModules C M H N I)

theorem primarySourceIDModulesRuleOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (I : AASCNNR8PrimarySourceIDModules C M H N) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    primaryRowModulesRuleOutSecondPoint
      C
      M
      H
      N
      S
      (primarySourceIDModulesAsPrimaryRowModules C M H N I)

theorem importedSourceTheoremsGiveEndpointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (T : AASCNNR8ImportedSourceTheorems C M H N S) :
  HybridJointRestrictionSingleton H := by
  exact
    primarySemanticExtractionGivesEndpointSingleton
      C
      M
      H
      N
      S
      (importedSourceTheoremsAsPrimarySemanticExtraction C M H N S T)

theorem importedSourceTheoremsRuleOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (T : AASCNNR8ImportedSourceTheorems C M H N S) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    primarySemanticExtractionRulesOutSecondPoint
      C
      M
      H
      N
      S
      (importedSourceTheoremsAsPrimarySemanticExtraction C M H N S T)

end Neutrino

end MaleyLean
