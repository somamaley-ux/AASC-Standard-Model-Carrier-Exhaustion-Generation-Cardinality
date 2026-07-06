import MaleyLean.Papers.Neutrino.SourceTheorems.ProofTerms

namespace MaleyLean

namespace Neutrino

/--
Formalization target for the MR3 shape-source paper.

Once MR3 is formalized as its own Lean module, it should export a theorem
producing this object for the selected spectral-source admission package.
-/
structure MR3ShapeSourcePaperTarget
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) where
  proofTerms : MR3ShapeSourceProofTerms M

/-- Formalization target for the EX8 overconstraint-legitimacy paper. -/
structure EX8OverconstraintPaperTarget
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M) where
  proofTerms : EX8OverconstraintProofTerms H

/-- Formalization target for the NOAR universal oscillation quotient paper. -/
structure NOARUniversalOscillationPaperTarget
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M) where
  proofTerms : NOARUniversalOscillationProofTerms H

/-- Formalization target for the UEAP paper family. -/
structure UEAPPaperTarget
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (audit :
    MaleyLean.Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit) where
  proofTerms :
    UEAPSourceProofTerms (C := C) (M := M) (H := H) (N := N) audit

/-- Formalization target for the CS6C same-scope/scope-extension source. -/
structure CS6CPaperTarget
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  proofTerms : CS6CSourceProofTerms N

/-- Formalization target for the CS7 PMNS value discipline source. -/
structure CS7PaperTarget
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  proofTerms : CS7SourceProofTerms N

/-- Formalization target for ROC role-occupancy closure. -/
structure ROCPaperTarget
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (audit :
    MaleyLean.Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit) where
  proofTerms : ROCSourceProofTerms C M H N audit

/--
All paper-local formalization targets needed by the NNR8 endpoint.

This object no longer asks source papers to know about the neutrino endpoint
assembly. Each paper proves its local target; this file performs the assembly.
-/
structure AASCNNR8PaperTargetBundle
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  audit :
    MaleyLean.Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit
  mr3 : MR3ShapeSourcePaperTarget M
  ex8 : EX8OverconstraintPaperTarget H
  noar : NOARUniversalOscillationPaperTarget H
  ueap : UEAPPaperTarget (C := C) (M := M) (H := H) (N := N) audit
  cs6c : CS6CPaperTarget N
  cs7 : CS7PaperTarget N
  roc : ROCPaperTarget C M H N audit

def paperTargetBundleAsRawSourceProofTerms
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (P : AASCNNR8PaperTargetBundle C M H N) :
  AASCNNR8RawSourceProofTerms C M H N :=
  { audit := P.audit
    mr3 := P.mr3.proofTerms
    ex8 := P.ex8.proofTerms
    noar := P.noar.proofTerms
    ueap := P.ueap.proofTerms
    cs6c := P.cs6c.proofTerms
    cs7 := P.cs7.proofTerms
    roc := P.roc.proofTerms }

theorem paperTargetBundleGiveEndpointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCNNR8PaperTargetBundle C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    rawSourceProofTermsGiveEndpointSingleton
      C
      M
      H
      N
      S
      (paperTargetBundleAsRawSourceProofTerms C M H N P)

theorem paperTargetBundleRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCNNR8PaperTargetBundle C M H N) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    rawSourceProofTermsRuleOutSecondPoint
      C
      M
      H
      N
      S
      (paperTargetBundleAsRawSourceProofTerms C M H N P)

end Neutrino

end MaleyLean
