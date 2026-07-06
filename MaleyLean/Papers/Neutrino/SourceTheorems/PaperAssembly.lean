import MaleyLean.Papers.Neutrino.SourceTheorems.PaperTargets

namespace MaleyLean

namespace Neutrino

/--
Assemble the seven independently formalized source-paper targets into the
single NNR8 endpoint target bundle.

This is the handoff point for future paper modules: MR3, EX8, NOAR, UEAP,
CS6C, CS7, and ROC can be proven independently, then combined here without
knowing anything about the downstream endpoint proof.
-/
def individualPaperTargetsAsBundle
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (audit :
    MaleyLean.Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit)
  (mr3 : MR3ShapeSourcePaperTarget M)
  (ex8 : EX8OverconstraintPaperTarget H)
  (noar : NOARUniversalOscillationPaperTarget H)
  (ueap : UEAPPaperTarget (C := C) (M := M) (H := H) (N := N) audit)
  (cs6c : CS6CPaperTarget N)
  (cs7 : CS7PaperTarget N)
  (roc : ROCPaperTarget C M H N audit) :
  AASCNNR8PaperTargetBundle C M H N :=
  { audit := audit
    mr3 := mr3
    ex8 := ex8
    noar := noar
    ueap := ueap
    cs6c := cs6c
    cs7 := cs7
    roc := roc }

theorem individualPaperTargetsGiveEndpointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (audit :
    MaleyLean.Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit)
  (mr3 : MR3ShapeSourcePaperTarget M)
  (ex8 : EX8OverconstraintPaperTarget H)
  (noar : NOARUniversalOscillationPaperTarget H)
  (ueap : UEAPPaperTarget (C := C) (M := M) (H := H) (N := N) audit)
  (cs6c : CS6CPaperTarget N)
  (cs7 : CS7PaperTarget N)
  (roc : ROCPaperTarget C M H N audit) :
  HybridJointRestrictionSingleton H := by
  exact
    paperTargetBundleGiveEndpointSingleton
      C
      M
      H
      N
      S
      (individualPaperTargetsAsBundle
        C M H N audit mr3 ex8 noar ueap cs6c cs7 roc)

theorem individualPaperTargetsRuleOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (audit :
    MaleyLean.Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit)
  (mr3 : MR3ShapeSourcePaperTarget M)
  (ex8 : EX8OverconstraintPaperTarget H)
  (noar : NOARUniversalOscillationPaperTarget H)
  (ueap : UEAPPaperTarget (C := C) (M := M) (H := H) (N := N) audit)
  (cs6c : CS6CPaperTarget N)
  (cs7 : CS7PaperTarget N)
  (roc : ROCPaperTarget C M H N audit) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    paperTargetBundleRulesOutSecondPoint
      C
      M
      H
      N
      S
      (individualPaperTargetsAsBundle
        C M H N audit mr3 ex8 noar ueap cs6c cs7 roc)

end Neutrino

end MaleyLean
