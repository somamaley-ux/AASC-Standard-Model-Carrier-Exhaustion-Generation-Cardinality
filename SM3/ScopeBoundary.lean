import SM3.PaperRecognition

namespace SM3

structure SM3ScopeBoundary where
  localMatterClosureClaimed : Prop
  globalSM6ClosureNotClaimed : Prop
  numericalMassYukawaClosureNotClaimed : Prop
  flavorMixingClosureDeferredToSM5 : Prop
  generationCardinalityClosureDeferred : Prop
  namedBSMModelInstantiationNotClaimed : Prop
  localMatterClosureClaimed_holds : localMatterClosureClaimed
  globalSM6ClosureNotClaimed_holds : globalSM6ClosureNotClaimed
  numericalMassYukawaClosureNotClaimed_holds : numericalMassYukawaClosureNotClaimed
  flavorMixingClosureDeferredToSM5_holds : flavorMixingClosureDeferredToSM5
  generationCardinalityClosureDeferred_holds : generationCardinalityClosureDeferred
  namedBSMModelInstantiationNotClaimed_holds : namedBSMModelInstantiationNotClaimed

def SM3ScopeBoundary.manuscriptFaithful (B : SM3ScopeBoundary) : Prop :=
  B.localMatterClosureClaimed /\
  B.globalSM6ClosureNotClaimed /\
  B.numericalMassYukawaClosureNotClaimed /\
  B.flavorMixingClosureDeferredToSM5 /\
  B.generationCardinalityClosureDeferred /\
  B.namedBSMModelInstantiationNotClaimed

theorem sm3_scope_boundary
    (B : SM3ScopeBoundary) :
    B.manuscriptFaithful := by
  constructor
  · exact B.localMatterClosureClaimed_holds
  constructor
  · exact B.globalSM6ClosureNotClaimed_holds
  constructor
  · exact B.numericalMassYukawaClosureNotClaimed_holds
  constructor
  · exact B.flavorMixingClosureDeferredToSM5_holds
  constructor
  · exact B.generationCardinalityClosureDeferred_holds
  · exact B.namedBSMModelInstantiationNotClaimed_holds

end SM3
