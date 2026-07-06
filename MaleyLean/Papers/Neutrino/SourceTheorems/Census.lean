import MaleyLean.Papers.Neutrino.SourceTheorems.Rows

namespace MaleyLean

namespace Neutrino

/--
No-eleventh-route census theorem bundle.

This is the corpus-side completeness pressure: every rival route must either
be carried by the joint restriction or fail as a scope/value/import move.
-/
structure NoEleventhRouteCorpusTheorems
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  noUncarriedSameTargetConstraint :
    N.noUncarriedSameTargetConstraint
  noLegacyTheoryOutsideCensus :
    N.noLegacyTheoryOutsideCensus
  noExperimentalMethodOutsideCensus :
    N.noExperimentalMethodOutsideCensus
  noScopeChangingRouteCountsSameScope :
    N.noScopeChangingRouteCountsSameScope
  noEmpiricalValueImportAsRoute :
    N.noEmpiricalValueImportAsRoute

theorem NoEleventhRouteCorpusTheorems.censusPackage
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (T : NoEleventhRouteCorpusTheorems N) :
  N.noUncarriedSameTargetConstraint /\
    N.noLegacyTheoryOutsideCensus /\
      N.noExperimentalMethodOutsideCensus /\
        N.noScopeChangingRouteCountsSameScope /\
          N.noEmpiricalValueImportAsRoute := by
  exact
    ⟨T.noUncarriedSameTargetConstraint,
      T.noLegacyTheoryOutsideCensus,
      T.noExperimentalMethodOutsideCensus,
      T.noScopeChangingRouteCountsSameScope,
      T.noEmpiricalValueImportAsRoute⟩

def CensusPrimaryRowTheorems.asCorpusTheorems
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (R : CensusPrimaryRowTheorems N) :
  NoEleventhRouteCorpusTheorems N :=
  { noUncarriedSameTargetConstraint :=
      R.noUncarriedSameTargetConstraint.proof
    noLegacyTheoryOutsideCensus :=
      R.noLegacyTheoryOutsideCensus.proof
    noExperimentalMethodOutsideCensus :=
      R.noExperimentalMethodOutsideCensus.proof
    noScopeChangingRouteCountsSameScope :=
      R.noScopeChangingRouteCountsSameScope.proof
    noEmpiricalValueImportAsRoute :=
      R.noEmpiricalValueImportAsRoute.proof }

end Neutrino

end MaleyLean
