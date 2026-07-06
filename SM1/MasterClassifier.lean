import SM1.ComponentNormalForm

namespace SM1

structure ClassifierStageCertificate (x : ComponentClaim Arena) where
  targetStage : Prop
  carrierStage : Prop
  descentStage : Prop
  predictionStage : Prop
  burdenStage : Prop
  failureStage : Prop
  targetStage_holds : targetStage
  carrierStage_holds : carrierStage
  descentStage_holds : descentStage
  predictionStage_holds : predictionStage
  burdenStage_holds : burdenStage
  failureStage_holds : failureStage

structure MasterClassifier (Arena : StandardModelArena) where
  grammar : FixedGrammarStatusCoverage Arena
  noPromotionRules : ClassifierNoPromotionRules Arena
  classify : (x : ComponentClaim Arena) -> StatusAssignment x
  stageCertificate : (x : ComponentClaim Arena) -> ClassifierStageCertificate x

theorem classifier_well_formed
    (C : MasterClassifier Arena)
    (x : ComponentClaim Arena) :
    NormalFormExists x :=
  fixed_grammar_status_coverage C.grammar x

theorem classifier_determinacy
    (C : MasterClassifier Arena)
    (x : ComponentClaim Arena) :
    Exists (fun S : StatusAssignment x => S = C.classify x) := by
  exact Exists.intro (C.classify x) rfl

end SM1
