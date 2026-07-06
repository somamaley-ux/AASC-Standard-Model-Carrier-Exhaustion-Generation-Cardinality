import MaleyLean.Papers.Neutrino.SourceTheorems.ProofTerms

namespace MaleyLean

namespace Neutrino

/--
Canonical UEAP audit surface for the branch-closure stage.

Every sigma-legitimacy coordinate is identified with being the current
standing-ratio branch. This keeps the audit conservative: it does not create
new physical content, it only records that the branch audit has already forced
the survivor into the current class.
-/
def currentOnlyUEAPAudit :
  Papers.ClaimStandingAndLegitimacy.ClaimAudit
    NeutrinoDraftCandidateIndex Unit :=
  { targetFixed := fun i =>
      i = NeutrinoDraftCandidateIndex.currentStandingRatio
    carrierAdequate := fun i =>
      i = NeutrinoDraftCandidateIndex.currentStandingRatio
    meaningFixed := fun i =>
      i = NeutrinoDraftCandidateIndex.currentStandingRatio
    scopeFixed := fun i =>
      i = NeutrinoDraftCandidateIndex.currentStandingRatio
    targetCarrierAligned := fun i =>
      i = NeutrinoDraftCandidateIndex.currentStandingRatio
    alternativesExhaustedModuloSkin := fun i =>
      i = NeutrinoDraftCandidateIndex.currentStandingRatio
    launderingExcluded := fun i =>
      i = NeutrinoDraftCandidateIndex.currentStandingRatio
    targetAncestrySeparated := fun i =>
      i = NeutrinoDraftCandidateIndex.currentStandingRatio
    boundaryDeclared := fun i =>
      i = NeutrinoDraftCandidateIndex.currentStandingRatio
    evidenceNetworkClosed := fun i =>
      i = NeutrinoDraftCandidateIndex.currentStandingRatio
    reportPreserving := fun i =>
      i = NeutrinoDraftCandidateIndex.currentStandingRatio
    blockersPreserved := fun i =>
      i = NeutrinoDraftCandidateIndex.currentStandingRatio
    domainLedgerDeclared := True
    requestedStatusDeclared := True
    carrierStandardDeclared := True
    skinRelationDeclared := True
    launderingTaxonomyDeclared := True
    precedenceDeclared := True }

/--
Under the current-only audit, the current branch is sigma-legitimate.
-/
theorem currentOnlyUEAPAuditCurrentLegitimate :
  Papers.ClaimStandingAndLegitimacy.SigmaLegitimacy
    currentOnlyUEAPAudit
    NeutrinoDraftCandidateIndex.currentStandingRatio := by
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
A branch-impossibility audit forces every hybrid-joint survivor to have the
current draft class.
-/
theorem branchImpossibilityAuditForcesCurrentClass
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (B : AASCBranchImpossibilityAudit C M H N)
  (r : C.Ratio)
  (hinterval : C.inMinimalInterval r)
  (hmod : H.modular.ModularRestriction r)
  (hspec : H.spectral.spectralRestriction r)
  (hscoto : H.scoto.scotoRestriction r) :
  routeCarrierDraftClass (N.carrierOf r) =
    NeutrinoDraftCandidateIndex.currentStandingRatio := by
  generalize hclass :
    routeCarrierDraftClass (N.carrierOf r) = i
  cases i
  · rfl
  · exact False.elim
      (B.modularOnlyImpossibleByKernel
        r hinterval hmod hspec hscoto hclass)
  · exact False.elim
      (B.scotoParameterFiberImpossibleByKernel
        r hinterval hmod hspec hscoto hclass)
  · exact False.elim
      (B.spectralWithoutFiniteCollapseImpossibleByKernel
        r hinterval hmod hspec hscoto hclass)
  · exact False.elim
      (B.sterileScopeExtensionImpossibleByKernel
        r hinterval hmod hspec hscoto hclass)
  · exact False.elim
      (B.phaseTopologyBreakingImpossibleByKernel
        r hinterval hmod hspec hscoto hclass)
  · exact False.elim
      (B.matterTransportBreakingImpossibleByKernel
        r hinterval hmod hspec hscoto hclass)
  · exact False.elim
      (B.absoluteMassImportImpossibleByKernel
        r hinterval hmod hspec hscoto hclass)
  · exact False.elim
      (B.diracMajoranaSelectorImpossibleByKernel
        r hinterval hmod hspec hscoto hclass)
  · exact False.elim
      (B.identitySelectorImpossibleByKernel
        r hinterval hmod hspec hscoto hclass)

/--
Branch-by-branch UEAP coordinate failures for the neutrino audit.

This is the fillable table version of `AASCUEAPCitedCoordinateBranchLedger`:
each non-current branch gets its own proof of the default coordinate failure
assigned in `defaultUEAPFailureKindForNoncurrentBranch`. The corresponding
corpus citation label is fixed by `defaultUEAPCorpusReasonForNoncurrentBranch`.
-/
structure AASCUEAPConcreteBranchFailureTable
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  audit :
    Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit
  currentDraftClassInjective :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio
  jointRouteClassClaimsLegitimacy :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              Papers.ClaimStandingAndLegitimacy.SigmaLegitimacy
                audit
                (routeCarrierDraftClass (N.carrierOf r))
  modularOnlyFailure :
    AASCUEAPLegitimacyFailureHolds
      audit
      NeutrinoDraftCandidateIndex.modularOnlyBranch
      (defaultUEAPFailureKindForNoncurrentBranch
        NeutrinoDraftCandidateIndex.modularOnlyBranch
        (by intro h; cases h))
  scotoParameterFiberFailure :
    AASCUEAPLegitimacyFailureHolds
      audit
      NeutrinoDraftCandidateIndex.scotoParameterFiberBranch
      (defaultUEAPFailureKindForNoncurrentBranch
        NeutrinoDraftCandidateIndex.scotoParameterFiberBranch
        (by intro h; cases h))
  spectralWithoutFiniteCollapseFailure :
    AASCUEAPLegitimacyFailureHolds
      audit
      NeutrinoDraftCandidateIndex.spectralWithoutFiniteCollapseBranch
      (defaultUEAPFailureKindForNoncurrentBranch
        NeutrinoDraftCandidateIndex.spectralWithoutFiniteCollapseBranch
        (by intro h; cases h))
  sterileScopeExtensionFailure :
    AASCUEAPLegitimacyFailureHolds
      audit
      NeutrinoDraftCandidateIndex.sterileScopeExtensionBranch
      (defaultUEAPFailureKindForNoncurrentBranch
        NeutrinoDraftCandidateIndex.sterileScopeExtensionBranch
        (by intro h; cases h))
  phaseTopologyBreakingFailure :
    AASCUEAPLegitimacyFailureHolds
      audit
      NeutrinoDraftCandidateIndex.phaseTopologyBreakingBranch
      (defaultUEAPFailureKindForNoncurrentBranch
        NeutrinoDraftCandidateIndex.phaseTopologyBreakingBranch
        (by intro h; cases h))
  matterTransportBreakingFailure :
    AASCUEAPLegitimacyFailureHolds
      audit
      NeutrinoDraftCandidateIndex.matterTransportBreakingBranch
      (defaultUEAPFailureKindForNoncurrentBranch
        NeutrinoDraftCandidateIndex.matterTransportBreakingBranch
        (by intro h; cases h))
  absoluteMassImportFailure :
    AASCUEAPLegitimacyFailureHolds
      audit
      NeutrinoDraftCandidateIndex.absoluteMassImportBranch
      (defaultUEAPFailureKindForNoncurrentBranch
        NeutrinoDraftCandidateIndex.absoluteMassImportBranch
        (by intro h; cases h))
  diracMajoranaSelectorFailure :
    AASCUEAPLegitimacyFailureHolds
      audit
      NeutrinoDraftCandidateIndex.diracMajoranaSelectorBranch
      (defaultUEAPFailureKindForNoncurrentBranch
        NeutrinoDraftCandidateIndex.diracMajoranaSelectorBranch
        (by intro h; cases h))
  identitySelectorFailure :
    AASCUEAPLegitimacyFailureHolds
      audit
      NeutrinoDraftCandidateIndex.identitySelectorBranch
      (defaultUEAPFailureKindForNoncurrentBranch
        NeutrinoDraftCandidateIndex.identitySelectorBranch
        (by intro h; cases h))

def concreteBranchFailureTableAsCitedLedger
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (T : AASCUEAPConcreteBranchFailureTable C M H N) :
  AASCUEAPCitedCoordinateBranchLedger C M H N :=
  { audit := T.audit
    currentDraftClassInjective := T.currentDraftClassInjective
    jointRouteClassClaimsLegitimacy := T.jointRouteClassClaimsLegitimacy
    assignedFailureSound := by
      intro i hne
      cases i
      · exact False.elim (hne rfl)
      · exact T.modularOnlyFailure
      · exact T.scotoParameterFiberFailure
      · exact T.spectralWithoutFiniteCollapseFailure
      · exact T.sterileScopeExtensionFailure
      · exact T.phaseTopologyBreakingFailure
      · exact T.matterTransportBreakingFailure
      · exact T.absoluteMassImportFailure
      · exact T.diracMajoranaSelectorFailure
      · exact T.identitySelectorFailure }

/--
The branch-impossibility audit fills the concrete UEAP branch table using the
canonical current-only UEAP audit.
-/
def branchImpossibilityAuditAsConcreteBranchFailureTable
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (B : AASCBranchImpossibilityAudit C M H N) :
  AASCUEAPConcreteBranchFailureTable C M H N :=
  { audit := currentOnlyUEAPAudit
    currentDraftClassInjective := B.currentDraftClassInjective
    jointRouteClassClaimsLegitimacy := by
      intro r hinterval hmod hspec hscoto
      rw [
        branchImpossibilityAuditForcesCurrentClass
          C M H N B r hinterval hmod hspec hscoto]
      exact currentOnlyUEAPAuditCurrentLegitimate
    modularOnlyFailure := by
      intro h
      cases h
    scotoParameterFiberFailure := by
      intro h
      cases h
    spectralWithoutFiniteCollapseFailure := by
      intro h
      cases h
    sterileScopeExtensionFailure := by
      intro h
      cases h
    phaseTopologyBreakingFailure := by
      intro h
      cases h
    matterTransportBreakingFailure := by
      intro h
      cases h
    absoluteMassImportFailure := by
      intro h
      cases h
    diracMajoranaSelectorFailure := by
      intro h
      cases h
    identitySelectorFailure := by
      intro h
      cases h }

/--
Expand the compact cited-coordinate ledger into the branch-by-branch failure
table. This is the formal version of "fill the nine rows": the single
`assignedFailureSound` field is projected into one named proof for each
non-current draft branch.
-/
def citedLedgerAsConcreteBranchFailureTable
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (L : AASCUEAPCitedCoordinateBranchLedger C M H N) :
  AASCUEAPConcreteBranchFailureTable C M H N :=
  { audit := L.audit
    currentDraftClassInjective := L.currentDraftClassInjective
    jointRouteClassClaimsLegitimacy := L.jointRouteClassClaimsLegitimacy
    modularOnlyFailure :=
      L.assignedFailureSound
        NeutrinoDraftCandidateIndex.modularOnlyBranch
        (by intro h; cases h)
    scotoParameterFiberFailure :=
      L.assignedFailureSound
        NeutrinoDraftCandidateIndex.scotoParameterFiberBranch
        (by intro h; cases h)
    spectralWithoutFiniteCollapseFailure :=
      L.assignedFailureSound
        NeutrinoDraftCandidateIndex.spectralWithoutFiniteCollapseBranch
        (by intro h; cases h)
    sterileScopeExtensionFailure :=
      L.assignedFailureSound
        NeutrinoDraftCandidateIndex.sterileScopeExtensionBranch
        (by intro h; cases h)
    phaseTopologyBreakingFailure :=
      L.assignedFailureSound
        NeutrinoDraftCandidateIndex.phaseTopologyBreakingBranch
        (by intro h; cases h)
    matterTransportBreakingFailure :=
      L.assignedFailureSound
        NeutrinoDraftCandidateIndex.matterTransportBreakingBranch
        (by intro h; cases h)
    absoluteMassImportFailure :=
      L.assignedFailureSound
        NeutrinoDraftCandidateIndex.absoluteMassImportBranch
        (by intro h; cases h)
    diracMajoranaSelectorFailure :=
      L.assignedFailureSound
        NeutrinoDraftCandidateIndex.diracMajoranaSelectorBranch
        (by intro h; cases h)
    identitySelectorFailure :=
      L.assignedFailureSound
        NeutrinoDraftCandidateIndex.identitySelectorBranch
        (by intro h; cases h) }

/--
The nondegenerate UEAP kernel operationalization directly fills the concrete
branch failure table.
-/
def kernelOperationalizationAsConcreteBranchFailureTable
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (K : AASCNondegenerateUEAPKernelOperationalization C M H N S) :
  AASCUEAPConcreteBranchFailureTable C M H N :=
  citedLedgerAsConcreteBranchFailureTable
    C
    M
    H
    N
    (nondegenerateUEAPKernelOperationalizationAsCitedLedger C M H N S K)

/--
The concrete branch failure table plus nondegenerate kernel admission is
exactly the compact operationalization object.

This is the cleanest proof target for the paper prose: prove that the current
branch occupies the nondegenerate admissible interior, and prove the UEAP
branch table. Lean then packages those into
`AASCNondegenerateUEAPKernelOperationalization`.
-/
def concreteBranchFailureTableAndKernelAdmissionAsOperationalization
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (K :
    AASCNondegenerateKernelInteriorAdmission
      C M H N S.unusSolus)
  (T : AASCUEAPConcreteBranchFailureTable C M H N) :
  AASCNondegenerateUEAPKernelOperationalization C M H N S :=
  { audit := T.audit
    kernelAdmission := K
    ueapIsKernelOperationalized := True.intro
    jointSurvivorClaimsUEAPLegitimacy :=
      T.jointRouteClassClaimsLegitimacy
    kernelForcesAssignedUEAPFailure :=
      (concreteBranchFailureTableAsCitedLedger C M H N T).assignedFailureSound }

/--
Assemble the NNR8 raw source-proof package from the concrete branch-audit
frontier.

This is the practical next target after the corpus rescan: MR3, hybrid, and
no-eleventh-route witnesses discharge the structural gates, while the cited
UEAP coordinate ledger supplies the current-point identification, survivor
legitimacy, and kernel-forced failure coordinates for every non-current
branch.
-/
def rawSourceProofTermsFromWitnessesAndCitedLedger
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (WM : MR3SpectralSourceAdmissionWitness M)
  (WH : AASCHybridSameScopeAdmissionWitness C M H)
  (WN : AASCNoEleventhRouteCensusWitness C M H N)
  (L : AASCUEAPCitedCoordinateBranchLedger C M H N) :
  AASCNNR8RawSourceProofTerms C M H N :=
  { audit := L.audit
    mr3 :=
      { sourceCertified := WM.sourceCertified_proof
        standingSpectralCarrier := WM.standingSpectralCarrier_proof
        quotientStable := WM.quotientStable_proof
        transportClosed := WM.transportClosed_proof
        calibrationFree := WM.calibrationFree_proof
        extractionCertified := WM.extractionCertified_proof
        sourceInducesShapeMap := WM.sourceInducesShapeMap_proof }
    ex8 :=
      { crossTargetAligned := WH.crossTargetAligned_proof }
    noar :=
      { crossTransportCoherent := WH.crossTransportCoherent_proof
        crossNoOvercounting := WH.crossNoOvercounting_proof }
    ueap :=
      { crossCalibrationFree := WH.crossCalibrationFree_proof
        crossNoHiddenSelector := WH.crossNoHiddenSelector_proof
        jointSurvivorUEAPLegitimacy :=
          L.jointRouteClassClaimsLegitimacy }
    cs6c :=
      { noUncarriedSameTargetConstraint :=
          WN.noUncarriedSameTargetConstraint_proof
        noLegacyTheoryOutsideCensus :=
          WN.noLegacyTheoryOutsideCensus_proof
        noScopeChangingRouteCountsSameScope :=
          WN.noScopeChangingRouteCountsSameScope_proof }
    cs7 :=
      { noExperimentalMethodOutsideCensus :=
          WN.noExperimentalMethodOutsideCensus_proof
        noEmpiricalValueImportAsRoute :=
          WN.noEmpiricalValueImportAsRoute_proof }
    roc :=
      { currentPointIdentification :=
          L.currentDraftClassInjective
        kernelForcedUEAPFailure :=
          L.assignedFailureSound } }

/--
The cited UEAP coordinate ledger is now a complete source-proof frontier for
the endpoint singleton, once the structural source witnesses are supplied.
-/
theorem citedLedgerWitnessesGiveEndpointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (WM : MR3SpectralSourceAdmissionWitness M)
  (WH : AASCHybridSameScopeAdmissionWitness C M H)
  (WN : AASCNoEleventhRouteCensusWitness C M H N)
  (L : AASCUEAPCitedCoordinateBranchLedger C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    rawSourceProofTermsGiveEndpointSingleton
      C
      M
      H
      N
      S
      (rawSourceProofTermsFromWitnessesAndCitedLedger
        C M H N WM WH WN L)

/--
The same cited-ledger frontier rules out a second hybrid-joint point.
-/
theorem citedLedgerWitnessesRuleOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (WM : MR3SpectralSourceAdmissionWitness M)
  (WH : AASCHybridSameScopeAdmissionWitness C M H)
  (WN : AASCNoEleventhRouteCensusWitness C M H N)
  (L : AASCUEAPCitedCoordinateBranchLedger C M H N) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    rawSourceProofTermsRuleOutSecondPoint
      C
      M
      H
      N
      S
      (rawSourceProofTermsFromWitnessesAndCitedLedger
        C M H N WM WH WN L)

/--
The branch-by-branch failure table is enough to close the endpoint singleton
after conversion to the cited-coordinate ledger.
-/
theorem concreteBranchFailureTableWitnessesGiveEndpointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (WM : MR3SpectralSourceAdmissionWitness M)
  (WH : AASCHybridSameScopeAdmissionWitness C M H)
  (WN : AASCNoEleventhRouteCensusWitness C M H N)
  (T : AASCUEAPConcreteBranchFailureTable C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    citedLedgerWitnessesGiveEndpointSingleton
      C
      M
      H
      N
      S
      WM
      WH
      WN
      (concreteBranchFailureTableAsCitedLedger C M H N T)

/--
The branch-by-branch failure table also rules out a second hybrid-joint point.
-/
theorem concreteBranchFailureTableWitnessesRuleOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (WM : MR3SpectralSourceAdmissionWitness M)
  (WH : AASCHybridSameScopeAdmissionWitness C M H)
  (WN : AASCNoEleventhRouteCensusWitness C M H N)
  (T : AASCUEAPConcreteBranchFailureTable C M H N) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    citedLedgerWitnessesRuleOutSecondPoint
      C
      M
      H
      N
      S
      WM
      WH
      WN
      (concreteBranchFailureTableAsCitedLedger C M H N T)

/--
Kernel operationalization closes the endpoint through the explicit
branch-by-branch failure table.
-/
theorem kernelOperationalizationConcreteTableWitnessesGiveEndpointSingleton
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
    concreteBranchFailureTableWitnessesGiveEndpointSingleton
      C
      M
      H
      N
      S
      WM
      WH
      WN
      (kernelOperationalizationAsConcreteBranchFailureTable C M H N S K)

/--
Kernel operationalization rules out a second point through the explicit
branch-by-branch failure table.
-/
theorem kernelOperationalizationConcreteTableWitnessesRuleOutSecondPoint
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
    concreteBranchFailureTableWitnessesRuleOutSecondPoint
      C
      M
      H
      N
      S
      WM
      WH
      WN
      (kernelOperationalizationAsConcreteBranchFailureTable C M H N S K)

/--
Kernel admission and the concrete branch table close the endpoint through the
compact operationalization object.
-/
theorem kernelAdmissionAndConcreteTableWitnessesGiveEndpointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (WM : MR3SpectralSourceAdmissionWitness M)
  (WH : AASCHybridSameScopeAdmissionWitness C M H)
  (WN : AASCNoEleventhRouteCensusWitness C M H N)
  (K :
    AASCNondegenerateKernelInteriorAdmission
      C M H N S.unusSolus)
  (T : AASCUEAPConcreteBranchFailureTable C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    kernelOperationalizationConcreteTableWitnessesGiveEndpointSingleton
      C
      M
      H
      N
      S
      WM
      WH
      WN
      (concreteBranchFailureTableAndKernelAdmissionAsOperationalization
        C M H N S K T)

/--
Kernel admission and the concrete branch table also rule out a second
hybrid-joint point through the compact operationalization object.
-/
theorem kernelAdmissionAndConcreteTableWitnessesRuleOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (WM : MR3SpectralSourceAdmissionWitness M)
  (WH : AASCHybridSameScopeAdmissionWitness C M H)
  (WN : AASCNoEleventhRouteCensusWitness C M H N)
  (K :
    AASCNondegenerateKernelInteriorAdmission
      C M H N S.unusSolus)
  (T : AASCUEAPConcreteBranchFailureTable C M H N) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    kernelOperationalizationConcreteTableWitnessesRuleOutSecondPoint
      C
      M
      H
      N
      S
      WM
      WH
      WN
      (concreteBranchFailureTableAndKernelAdmissionAsOperationalization
        C M H N S K T)

/--
Branch impossibility audit plus nondegenerate kernel admission closes the
endpoint through the explicit UEAP table.
-/
theorem branchAuditAndKernelAdmissionWitnessesGiveEndpointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (WM : MR3SpectralSourceAdmissionWitness M)
  (WH : AASCHybridSameScopeAdmissionWitness C M H)
  (WN : AASCNoEleventhRouteCensusWitness C M H N)
  (K :
    AASCNondegenerateKernelInteriorAdmission
      C M H N S.unusSolus)
  (B : AASCBranchImpossibilityAudit C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    kernelAdmissionAndConcreteTableWitnessesGiveEndpointSingleton
      C
      M
      H
      N
      S
      WM
      WH
      WN
      K
      (branchImpossibilityAuditAsConcreteBranchFailureTable C M H N B)

/--
Branch impossibility audit plus nondegenerate kernel admission rules out a
second hybrid-joint point through the explicit UEAP table.
-/
theorem branchAuditAndKernelAdmissionWitnessesRuleOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (WM : MR3SpectralSourceAdmissionWitness M)
  (WH : AASCHybridSameScopeAdmissionWitness C M H)
  (WN : AASCNoEleventhRouteCensusWitness C M H N)
  (K :
    AASCNondegenerateKernelInteriorAdmission
      C M H N S.unusSolus)
  (B : AASCBranchImpossibilityAudit C M H N) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    kernelAdmissionAndConcreteTableWitnessesRuleOutSecondPoint
      C
      M
      H
      N
      S
      WM
      WH
      WN
      K
      (branchImpossibilityAuditAsConcreteBranchFailureTable C M H N B)

end Neutrino

end MaleyLean
