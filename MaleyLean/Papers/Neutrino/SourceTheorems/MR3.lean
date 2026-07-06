import MaleyLean.Papers.Neutrino.SourceTheorems.Rows

namespace MaleyLean

namespace Neutrino

/--
MR3 source-admission theorem bundle for the NNR8 endpoint upgrade.

This module is intentionally thin: it gives stable Lean names to the MR3
source obligations that were extracted from the corpus. Later, these fields
can be discharged by importing a fully formalized MR3 paper module without
changing the neutrino endpoint proof.
-/
structure MR3CorpusTheorems
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) where
  sourceCertified : M.sourceCertified
  standingSpectralCarrier : M.standingSpectralCarrier
  quotientStable : M.quotientStable
  transportClosed : M.transportClosed
  calibrationFree : M.calibrationFree
  extractionCertified : M.extractionCertified
  sourceInducesShapeMap : M.sourceInducesShapeMap

def MR3CorpusTheorems.asWitness
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (T : MR3CorpusTheorems M) :
  MR3SpectralSourceAdmissionWitness M :=
  { sourceCertified_proof := T.sourceCertified
    standingSpectralCarrier_proof := T.standingSpectralCarrier
    quotientStable_proof := T.quotientStable
    transportClosed_proof := T.transportClosed
    calibrationFree_proof := T.calibrationFree
    extractionCertified_proof := T.extractionCertified
    sourceInducesShapeMap_proof := T.sourceInducesShapeMap }

theorem MR3CorpusTheorems.admitsSource
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (T : MR3CorpusTheorems M) :
  MR3SpectralSourceAdmissionAdmitted M := by
  exact mr3SpectralSourceAdmissionWitnessClearsM M T.asWitness

def MR3PrimaryRowTheorems.asCorpusTheorems
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : MR3PrimaryRowTheorems M) :
  MR3CorpusTheorems M :=
  { sourceCertified := R.sourceCertified.proof
    standingSpectralCarrier := R.standingSpectralCarrier.proof
    quotientStable := R.quotientStable.proof
    transportClosed := R.transportClosed.proof
    calibrationFree := R.calibrationFree.proof
    extractionCertified := R.extractionCertified.proof
    sourceInducesShapeMap := R.sourceInducesShapeMap.proof }

end Neutrino

end MaleyLean
