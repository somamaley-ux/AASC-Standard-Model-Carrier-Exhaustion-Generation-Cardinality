import MaleyLean.Papers.Neutrino.SourceTheorems.CoreBundleClosure

namespace MaleyLean

namespace Neutrino

/--
Primary semantic extraction closes the core source proof bundle.

This is the formal discharge of the previous single blocker
`AASCNNR8CoreSourceProofBundle`: the bundle is constructed from canonical
primary-source-backed proof fields.
-/
def coreSourceProofBundleFromPrimarySemanticExtraction
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCNNR8PrimarySemanticExtractionCertificate C M H N S) :
  AASCNNR8CoreSourceProofBundle C M H N S :=
  semanticExtractionAsCoreSourceProofBundle
    C
    M
    H
    N
    S
    (primarySemanticExtractionAsSemanticExtraction C M H N S P)

/--
Primary semantic extraction closes the seven paper targets through the core
source proof bundle.
-/
def closedPaperTargetBundleFromPrimarySemanticExtraction
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCNNR8PrimarySemanticExtractionCertificate C M H N S) :
  AASCNNR8PaperTargetBundle C M H N :=
  closedPaperTargetBundleFromCoreBundle
    C
    M
    H
    N
    S
    (coreSourceProofBundleFromPrimarySemanticExtraction C M H N S P)

theorem primarySemanticExtractionGivesEndpointSingletonViaPaperTargets
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCNNR8PrimarySemanticExtractionCertificate C M H N S) :
  HybridJointRestrictionSingleton H := by
  exact
    paperTargetBundleGiveEndpointSingleton
      C
      M
      H
      N
      S
      (closedPaperTargetBundleFromPrimarySemanticExtraction C M H N S P)

theorem primarySemanticExtractionRulesOutSecondPointViaPaperTargets
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCNNR8PrimarySemanticExtractionCertificate C M H N S) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    paperTargetBundleRulesOutSecondPoint
      C
      M
      H
      N
      S
      (closedPaperTargetBundleFromPrimarySemanticExtraction C M H N S P)

/--
The semantic-closure route agrees in endpoint strength with the direct primary
semantic extraction theorem.
-/
theorem primarySemanticExtractionPaperTargetRouteMatchesDirectRoute
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCNNR8PrimarySemanticExtractionCertificate C M H N S) :
  primarySemanticExtractionGivesEndpointSingletonViaPaperTargets C M H N S P =
    primarySemanticExtractionGivesEndpointSingleton C M H N S P := by
  rfl

end Neutrino

end MaleyLean
