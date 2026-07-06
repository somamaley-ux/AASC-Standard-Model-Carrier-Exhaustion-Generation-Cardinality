import SM2.PaperRecognition

namespace SM2

structure SM2ScopeBoundary where
  localGaugeClosureClaimed : Prop
  globalSM6ClosureNotClaimed : Prop
  numericalCouplingClosureNotClaimed : Prop
  electroweakPoleValueClosureNotClaimed : Prop
  modelByModelBSMCatalogueNotClaimed : Prop
  sm4PositiveRGTheoryDeferred : Prop
  localGaugeClosureClaimed_holds : localGaugeClosureClaimed
  globalSM6ClosureNotClaimed_holds : globalSM6ClosureNotClaimed
  numericalCouplingClosureNotClaimed_holds : numericalCouplingClosureNotClaimed
  electroweakPoleValueClosureNotClaimed_holds : electroweakPoleValueClosureNotClaimed
  modelByModelBSMCatalogueNotClaimed_holds : modelByModelBSMCatalogueNotClaimed
  sm4PositiveRGTheoryDeferred_holds : sm4PositiveRGTheoryDeferred

def SM2ScopeBoundary.manuscriptFaithful (B : SM2ScopeBoundary) : Prop :=
  B.localGaugeClosureClaimed /\
  B.globalSM6ClosureNotClaimed /\
  B.numericalCouplingClosureNotClaimed /\
  B.electroweakPoleValueClosureNotClaimed /\
  B.modelByModelBSMCatalogueNotClaimed /\
  B.sm4PositiveRGTheoryDeferred

theorem sm2_scope_boundary
    (B : SM2ScopeBoundary) :
    B.manuscriptFaithful := by
  constructor
  · exact B.localGaugeClosureClaimed_holds
  constructor
  · exact B.globalSM6ClosureNotClaimed_holds
  constructor
  · exact B.numericalCouplingClosureNotClaimed_holds
  constructor
  · exact B.electroweakPoleValueClosureNotClaimed_holds
  constructor
  · exact B.modelByModelBSMCatalogueNotClaimed_holds
  · exact B.sm4PositiveRGTheoryDeferred_holds

end SM2
