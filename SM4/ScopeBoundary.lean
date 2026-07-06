import SM4.PaperRecognition

namespace SM4

structure SM4ScopeBoundary where
  localCCRClosureClaimed : Prop
  globalSM6ClosureNotClaimed : Prop
  numericalCouplingDerivationNotClaimed : Prop
  flavorGenerationClosureDeferredToSM5 : Prop
  modelByModelBSMNotClaimed : Prop
  localCCRClosureClaimed_holds : localCCRClosureClaimed
  globalSM6ClosureNotClaimed_holds : globalSM6ClosureNotClaimed
  numericalCouplingDerivationNotClaimed_holds : numericalCouplingDerivationNotClaimed
  flavorGenerationClosureDeferredToSM5_holds : flavorGenerationClosureDeferredToSM5
  modelByModelBSMNotClaimed_holds : modelByModelBSMNotClaimed

def SM4ScopeBoundary.manuscriptFaithful (B : SM4ScopeBoundary) : Prop :=
  B.localCCRClosureClaimed /\ B.globalSM6ClosureNotClaimed /\
  B.numericalCouplingDerivationNotClaimed /\ B.flavorGenerationClosureDeferredToSM5 /\
  B.modelByModelBSMNotClaimed

theorem sm4_scope_boundary
    (B : SM4ScopeBoundary) :
    B.manuscriptFaithful := by
  constructor
  · exact B.localCCRClosureClaimed_holds
  constructor
  · exact B.globalSM6ClosureNotClaimed_holds
  constructor
  · exact B.numericalCouplingDerivationNotClaimed_holds
  constructor
  · exact B.flavorGenerationClosureDeferredToSM5_holds
  · exact B.modelByModelBSMNotClaimed_holds

end SM4
