import MaleyLean.Papers.Neutrino.SourceTheorems.SemanticClosure

namespace MaleyLean

namespace Neutrino

/--
Imported source theorems instantiate the canonical primary semantic extraction
certificate.

This names the last semantic step explicitly: plain imported theorem fields
are wrapped as primary-source-backed proof fields using the canonical source
row assignment from `RatioBlocker.lean`.
-/
def primarySemanticExtractionFromImportedSourceTheorems
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (T : AASCNNR8ImportedSourceTheorems C M H N S) :
  AASCNNR8PrimarySemanticExtractionCertificate C M H N S :=
  importedSourceTheoremsAsPrimarySemanticExtraction C M H N S T

theorem importedSourceTheoremsGiveEndpointSingletonViaSemanticClosure
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (T : AASCNNR8ImportedSourceTheorems C M H N S) :
  HybridJointRestrictionSingleton H := by
  exact
    primarySemanticExtractionGivesEndpointSingletonViaPaperTargets
      C
      M
      H
      N
      S
      (primarySemanticExtractionFromImportedSourceTheorems C M H N S T)

theorem importedSourceTheoremsRuleOutSecondPointViaSemanticClosure
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (T : AASCNNR8ImportedSourceTheorems C M H N S) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    primarySemanticExtractionRulesOutSecondPointViaPaperTargets
      C
      M
      H
      N
      S
      (primarySemanticExtractionFromImportedSourceTheorems C M H N S T)

/-- Source-family modules instantiate primary semantic extraction. -/
def primarySemanticExtractionFromCorpusSourceModules
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (T : AASCNNR8CorpusSourceModules C M H N) :
  AASCNNR8PrimarySemanticExtractionCertificate C M H N S :=
  primarySemanticExtractionFromImportedSourceTheorems
    C
    M
    H
    N
    S
    (corpusSourceModulesAsImportedSourceTheorems C M H N S T)

/-- Primary-row modules instantiate primary semantic extraction. -/
def primarySemanticExtractionFromPrimaryRowModules
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (R : AASCNNR8PrimaryRowModules C M H N) :
  AASCNNR8PrimarySemanticExtractionCertificate C M H N S :=
  primarySemanticExtractionFromCorpusSourceModules
    C
    M
    H
    N
    S
    (primaryRowModulesAsCorpusSourceModules C M H N R)

/-- Primary source-ID modules instantiate primary semantic extraction. -/
def primarySemanticExtractionFromPrimarySourceIDModules
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (I : AASCNNR8PrimarySourceIDModules C M H N) :
  AASCNNR8PrimarySemanticExtractionCertificate C M H N S :=
  primarySemanticExtractionFromPrimaryRowModules
    C
    M
    H
    N
    S
    (primarySourceIDModulesAsPrimaryRowModules C M H N I)

/-- Raw source proof terms instantiate primary semantic extraction. -/
def primarySemanticExtractionFromRawSourceProofTerms
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (T : AASCNNR8RawSourceProofTerms C M H N) :
  AASCNNR8PrimarySemanticExtractionCertificate C M H N S :=
  primarySemanticExtractionFromPrimarySourceIDModules
    C
    M
    H
    N
    S
    (rawSourceProofTermsAsPrimarySourceIDModules C M H N T)

/-- Paper target bundles instantiate primary semantic extraction. -/
def primarySemanticExtractionFromPaperTargetBundle
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCNNR8PaperTargetBundle C M H N) :
  AASCNNR8PrimarySemanticExtractionCertificate C M H N S :=
  primarySemanticExtractionFromRawSourceProofTerms
    C
    M
    H
    N
    S
    (paperTargetBundleAsRawSourceProofTerms C M H N P)

theorem paperTargetBundleGivesEndpointSingletonViaPrimarySemanticExtraction
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCNNR8PaperTargetBundle C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    primarySemanticExtractionGivesEndpointSingletonViaPaperTargets
      C
      M
      H
      N
      S
      (primarySemanticExtractionFromPaperTargetBundle C M H N S P)

theorem rawSourceProofTermsGiveEndpointSingletonViaPrimarySemanticExtraction
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (T : AASCNNR8RawSourceProofTerms C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    primarySemanticExtractionGivesEndpointSingletonViaPaperTargets
      C
      M
      H
      N
      S
      (primarySemanticExtractionFromRawSourceProofTerms C M H N S T)

/--
The imported-theorem semantic route agrees with the direct imported-theorem
endpoint route.
-/
theorem importedSemanticRouteMatchesDirectImportedRoute
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (T : AASCNNR8ImportedSourceTheorems C M H N S) :
  importedSourceTheoremsGiveEndpointSingletonViaSemanticClosure C M H N S T =
    importedSourceTheoremsGiveEndpointSingleton C M H N S T := by
  rfl

end Neutrino

end MaleyLean
