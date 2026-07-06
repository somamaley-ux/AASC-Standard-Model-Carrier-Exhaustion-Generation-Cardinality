import SM1.SkinIdentification

namespace SM1

structure ComponentNormalForm (x : ComponentClaim Arena) where
  fixedArena : StandardModelArena
  carrier : Type
  role : Type
  representative : Type
  measurementWitness : Type
  transportLedger : Type
  routeStatus : Type
  mixingStatus : Type
  projectionDisplay : Type
  extensionDisposition : Type
  certificate : Type
  finalStatus : SMStatus
  predictionRegisterEntry : Type

structure StatusAssignment (x : ComponentClaim Arena) where
  status : SMStatus
  normalForm : ComponentNormalForm x

def NormalFormExists (x : ComponentClaim Arena) : Prop :=
  Exists (fun _R : ComponentNormalForm x => True)

structure FixedGrammarStatusCoverage (Arena : StandardModelArena) where
  assign : (x : ComponentClaim Arena) -> StatusAssignment x

theorem fixed_grammar_status_coverage
    (G : FixedGrammarStatusCoverage Arena)
    (x : ComponentClaim Arena) :
    NormalFormExists x := by
  exact Exists.intro (G.assign x).normalForm True.intro

end SM1
