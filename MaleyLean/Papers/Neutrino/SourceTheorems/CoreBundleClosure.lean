import MaleyLean.Papers.Neutrino.SourceTheorems.WitnessClosure

namespace MaleyLean

namespace Neutrino

/--
Recover the nondegenerate UEAP-kernel operationalization from the core source
proof bundle.

This discharges the `K` witness used by `WitnessClosure.lean` from the three
operational proof fields already carried by `AASCNNR8CoreSourceProofBundle`.
-/
def kernelOperationalizationFromCoreBundle
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (B : AASCNNR8CoreSourceProofBundle C M H N S) :
  AASCNondegenerateUEAPKernelOperationalization C M H N S :=
  coreSourceProofBundleAsOperationalization C M H N S B

/--
The core source proof bundle closes the seven paper targets.

This is the promised discharge of `WM`, `WH`, `WN`, and `K`: the first three
are fields of the bundle, and `K` is constructed from the bundle's operational
proofs.
-/
def closedPaperTargetBundleFromCoreBundle
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (B : AASCNNR8CoreSourceProofBundle C M H N S) :
  AASCNNR8PaperTargetBundle C M H N :=
  closedPaperTargetBundleFromWitnesses
    C
    M
    H
    N
    S
    B.mr3Witness
    B.hybridWitness
    B.noEleventhWitness
    (kernelOperationalizationFromCoreBundle C M H N S B)

theorem coreBundleGivesEndpointSingletonViaPaperTargets
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (B : AASCNNR8CoreSourceProofBundle C M H N S) :
  HybridJointRestrictionSingleton H := by
  exact
    paperTargetBundleGiveEndpointSingleton
      C
      M
      H
      N
      S
      (closedPaperTargetBundleFromCoreBundle C M H N S B)

theorem coreBundleRulesOutSecondPointViaPaperTargets
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (B : AASCNNR8CoreSourceProofBundle C M H N S) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    paperTargetBundleRulesOutSecondPoint
      C
      M
      H
      N
      S
      (closedPaperTargetBundleFromCoreBundle C M H N S B)

/--
The paper-target route agrees in endpoint strength with the original core
source bundle theorem.
-/
theorem coreBundlePaperTargetRouteMatchesCoreRoute
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (B : AASCNNR8CoreSourceProofBundle C M H N S) :
  coreBundleGivesEndpointSingletonViaPaperTargets C M H N S B =
    coreSourceProofBundleGivesEndpointSingleton C M H N S B := by
  rfl

end Neutrino

end MaleyLean
