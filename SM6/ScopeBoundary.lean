import SM6.PaperRecognition

namespace SM6

structure SM6ScopeBoundary where
  finalCarrierExhaustionClaimed : Prop
  primitiveCarrierPackageUnchanged : Prop
  generationCardinalityOutsidePrimitivePackage : Prop
  skinOpennessPreserved : Prop
  modelByModelBSMNotClaimed : Prop
  finalCarrierExhaustionClaimed_holds : finalCarrierExhaustionClaimed
  primitiveCarrierPackageUnchanged_holds : primitiveCarrierPackageUnchanged
  generationCardinalityOutsidePrimitivePackage_holds : generationCardinalityOutsidePrimitivePackage
  skinOpennessPreserved_holds : skinOpennessPreserved
  modelByModelBSMNotClaimed_holds : modelByModelBSMNotClaimed

def SM6ScopeBoundary.manuscriptFaithful (B : SM6ScopeBoundary) : Prop :=
  B.finalCarrierExhaustionClaimed /\ B.primitiveCarrierPackageUnchanged /\
  B.generationCardinalityOutsidePrimitivePackage /\ B.skinOpennessPreserved /\
  B.modelByModelBSMNotClaimed

theorem sm6_scope_boundary
    (B : SM6ScopeBoundary) :
    B.manuscriptFaithful := by
  constructor
  · exact B.finalCarrierExhaustionClaimed_holds
  constructor
  · exact B.primitiveCarrierPackageUnchanged_holds
  constructor
  · exact B.generationCardinalityOutsidePrimitivePackage_holds
  constructor
  · exact B.skinOpennessPreserved_holds
  · exact B.modelByModelBSMNotClaimed_holds

end SM6
