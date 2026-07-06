import MaleyLean.Papers.Neutrino.SourceTheorems.Rows

namespace MaleyLean

namespace Neutrino

/--
Hybrid modular/spectral/scoto source bundle.

These are the cross-translation obligations needed by the endpoint proof:
same target, coherent transport, no overcounting, no calibration import, and no
hidden selector.
-/
structure HybridCorpusTheorems
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M) where
  crossTargetAligned : H.crossTargetAligned
  crossTransportCoherent : H.crossTransportCoherent
  crossNoOvercounting : H.crossNoOvercounting
  crossCalibrationFree : H.crossCalibrationFree
  crossNoHiddenSelector : H.crossNoHiddenSelector

theorem HybridCorpusTheorems.crossPackage
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (T : HybridCorpusTheorems H) :
  H.crossTargetAligned /\
    H.crossTransportCoherent /\
      H.crossNoOvercounting /\
        H.crossCalibrationFree /\
          H.crossNoHiddenSelector := by
  exact
    ⟨T.crossTargetAligned,
      T.crossTransportCoherent,
      T.crossNoOvercounting,
      T.crossCalibrationFree,
      T.crossNoHiddenSelector⟩

def HybridPrimaryRowTheorems.asCorpusTheorems
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : HybridPrimaryRowTheorems H) :
  HybridCorpusTheorems H :=
  { crossTargetAligned := R.crossTargetAligned.proof
    crossTransportCoherent := R.crossTransportCoherent.proof
    crossNoOvercounting := R.crossNoOvercounting.proof
    crossCalibrationFree := R.crossCalibrationFree.proof
    crossNoHiddenSelector := R.crossNoHiddenSelector.proof }

end Neutrino

end MaleyLean
