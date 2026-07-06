import MaleyLean.Papers.Neutrino.SourceTheorems.PaperAssembly

namespace MaleyLean

namespace Neutrino

/--
Close the MR3 paper target from the proof-carrying MR3 admission witness.
-/
def mr3PaperTargetFromWitness
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (WM : MR3SpectralSourceAdmissionWitness M) :
  MR3ShapeSourcePaperTarget M :=
  { proofTerms :=
      { sourceCertified := WM.sourceCertified_proof
        standingSpectralCarrier := WM.standingSpectralCarrier_proof
        quotientStable := WM.quotientStable_proof
        transportClosed := WM.transportClosed_proof
        calibrationFree := WM.calibrationFree_proof
        extractionCertified := WM.extractionCertified_proof
        sourceInducesShapeMap := WM.sourceInducesShapeMap_proof } }

/--
Close the EX8 paper target from the hybrid same-scope witness.
-/
def ex8PaperTargetFromHybridWitness
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (WH : AASCHybridSameScopeAdmissionWitness C M H) :
  EX8OverconstraintPaperTarget H :=
  { proofTerms :=
      { crossTargetAligned := WH.crossTargetAligned_proof } }

/--
Close the NOAR paper target from the hybrid same-scope witness.
-/
def noarPaperTargetFromHybridWitness
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (WH : AASCHybridSameScopeAdmissionWitness C M H) :
  NOARUniversalOscillationPaperTarget H :=
  { proofTerms :=
      { crossTransportCoherent := WH.crossTransportCoherent_proof
        crossNoOvercounting := WH.crossNoOvercounting_proof } }

/--
Close the UEAP paper target from the hybrid witness and the operationalized
nondegenerate UEAP kernel.
-/
def ueapPaperTargetFromKernelOperationalization
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  {S : AASCCorpusBranchSupportLedger C}
  (WH : AASCHybridSameScopeAdmissionWitness C M H)
  (K : AASCNondegenerateUEAPKernelOperationalization C M H N S) :
  UEAPPaperTarget (C := C) (M := M) (H := H) (N := N) K.audit :=
  { proofTerms :=
      { crossCalibrationFree := WH.crossCalibrationFree_proof
        crossNoHiddenSelector := WH.crossNoHiddenSelector_proof
        jointSurvivorUEAPLegitimacy :=
          K.jointSurvivorClaimsUEAPLegitimacy } }

/--
Close the CS6C paper target from the no-eleventh-route census witness.
-/
def cs6cPaperTargetFromCensusWitness
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (WN : AASCNoEleventhRouteCensusWitness C M H N) :
  CS6CPaperTarget N :=
  { proofTerms :=
      { noUncarriedSameTargetConstraint :=
          WN.noUncarriedSameTargetConstraint_proof
        noLegacyTheoryOutsideCensus :=
          WN.noLegacyTheoryOutsideCensus_proof
        noScopeChangingRouteCountsSameScope :=
          WN.noScopeChangingRouteCountsSameScope_proof } }

/--
Close the CS7 paper target from the no-eleventh-route census witness.
-/
def cs7PaperTargetFromCensusWitness
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (WN : AASCNoEleventhRouteCensusWitness C M H N) :
  CS7PaperTarget N :=
  { proofTerms :=
      { noExperimentalMethodOutsideCensus :=
          WN.noExperimentalMethodOutsideCensus_proof
        noEmpiricalValueImportAsRoute :=
          WN.noEmpiricalValueImportAsRoute_proof } }

/--
Close the ROC paper target from the operationalized nondegenerate UEAP kernel.
-/
def rocPaperTargetFromKernelOperationalization
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  {S : AASCCorpusBranchSupportLedger C}
  (K : AASCNondegenerateUEAPKernelOperationalization C M H N S) :
  ROCPaperTarget C M H N K.audit :=
  { proofTerms :=
      { currentPointIdentification :=
          K.kernelAdmission.nondegenerateCurrentClassOccupiesUniqueInterior
        kernelForcedUEAPFailure :=
          K.kernelForcesAssignedUEAPFailure } }

/--
The seven source-paper targets are closed by the already proof-carrying MR3,
hybrid, census, and nondegenerate UEAP-kernel witnesses.
-/
def closedPaperTargetBundleFromWitnesses
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (WM : MR3SpectralSourceAdmissionWitness M)
  (WH : AASCHybridSameScopeAdmissionWitness C M H)
  (WN : AASCNoEleventhRouteCensusWitness C M H N)
  (K : AASCNondegenerateUEAPKernelOperationalization C M H N S) :
  AASCNNR8PaperTargetBundle C M H N :=
  individualPaperTargetsAsBundle
    C
    M
    H
    N
    K.audit
    (mr3PaperTargetFromWitness WM)
    (ex8PaperTargetFromHybridWitness WH)
    (noarPaperTargetFromHybridWitness WH)
    (ueapPaperTargetFromKernelOperationalization WH K)
    (cs6cPaperTargetFromCensusWitness WN)
    (cs7PaperTargetFromCensusWitness WN)
    (rocPaperTargetFromKernelOperationalization K)

theorem closedWitnessesGiveEndpointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (WM : MR3SpectralSourceAdmissionWitness M)
  (WH : AASCHybridSameScopeAdmissionWitness C M H)
  (WN : AASCNoEleventhRouteCensusWitness C M H N)
  (K : AASCNondegenerateUEAPKernelOperationalization C M H N S) :
  HybridJointRestrictionSingleton H := by
  exact
    paperTargetBundleGiveEndpointSingleton
      C
      M
      H
      N
      S
      (closedPaperTargetBundleFromWitnesses C M H N S WM WH WN K)

theorem closedWitnessesRuleOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (WM : MR3SpectralSourceAdmissionWitness M)
  (WH : AASCHybridSameScopeAdmissionWitness C M H)
  (WN : AASCNoEleventhRouteCensusWitness C M H N)
  (K : AASCNondegenerateUEAPKernelOperationalization C M H N S) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    paperTargetBundleRulesOutSecondPoint
      C
      M
      H
      N
      S
      (closedPaperTargetBundleFromWitnesses C M H N S WM WH WN K)

end Neutrino

end MaleyLean
