import SM5.PaperRecognition

namespace SM5

structure SM5ScopeBoundary where
  localFlavorClosureClaimed : Prop
  globalSM6ClosureNotClaimed : Prop
  numericalMixingDerivationNotClaimed : Prop
  internalGenerationCountNotClaimed : Prop
  openGenerationCardinalityEndpointSuppliesN3 : Prop
  modelByModelBSMNotClaimed : Prop
  localFlavorClosureClaimed_holds : localFlavorClosureClaimed
  globalSM6ClosureNotClaimed_holds : globalSM6ClosureNotClaimed
  numericalMixingDerivationNotClaimed_holds : numericalMixingDerivationNotClaimed
  internalGenerationCountNotClaimed_holds : internalGenerationCountNotClaimed
  openGenerationCardinalityEndpointSuppliesN3_holds : openGenerationCardinalityEndpointSuppliesN3
  modelByModelBSMNotClaimed_holds : modelByModelBSMNotClaimed

def SM5ScopeBoundary.manuscriptFaithful (B : SM5ScopeBoundary) : Prop :=
  B.localFlavorClosureClaimed /\ B.globalSM6ClosureNotClaimed /\
  B.numericalMixingDerivationNotClaimed /\ B.internalGenerationCountNotClaimed /\
  B.openGenerationCardinalityEndpointSuppliesN3 /\ B.modelByModelBSMNotClaimed

theorem sm5_scope_boundary
    (B : SM5ScopeBoundary) :
    B.manuscriptFaithful := by
  constructor
  · exact B.localFlavorClosureClaimed_holds
  constructor
  · exact B.globalSM6ClosureNotClaimed_holds
  constructor
  · exact B.numericalMixingDerivationNotClaimed_holds
  constructor
  · exact B.internalGenerationCountNotClaimed_holds
  constructor
  · exact B.openGenerationCardinalityEndpointSuppliesN3_holds
  · exact B.modelByModelBSMNotClaimed_holds

end SM5
