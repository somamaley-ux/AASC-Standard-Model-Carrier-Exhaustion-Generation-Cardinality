import GenerationCardinality.PaperRecognition

namespace GenerationCardinality

structure CardinalityScopeBoundary where
  extensionEndpointClaimed : Prop
  sm6PrimitivePackageNotChanged : Prop
  noNumericalMixingValueClaim : Prop
  noUntypedImportClaim : Prop
  bsmPhenomenologyNotClaimed : Prop
  extensionEndpointClaimed_holds : extensionEndpointClaimed
  sm6PrimitivePackageNotChanged_holds : sm6PrimitivePackageNotChanged
  noNumericalMixingValueClaim_holds : noNumericalMixingValueClaim
  noUntypedImportClaim_holds : noUntypedImportClaim
  bsmPhenomenologyNotClaimed_holds : bsmPhenomenologyNotClaimed

def CardinalityScopeBoundary.manuscriptFaithful
    (B : CardinalityScopeBoundary) : Prop :=
  B.extensionEndpointClaimed /\ B.sm6PrimitivePackageNotChanged /\
  B.noNumericalMixingValueClaim /\ B.noUntypedImportClaim /\ B.bsmPhenomenologyNotClaimed

theorem generation_cardinality_scope_boundary
    (B : CardinalityScopeBoundary) :
    B.manuscriptFaithful := by
  constructor
  · exact B.extensionEndpointClaimed_holds
  constructor
  · exact B.sm6PrimitivePackageNotChanged_holds
  constructor
  · exact B.noNumericalMixingValueClaim_holds
  constructor
  · exact B.noUntypedImportClaim_holds
  · exact B.bsmPhenomenologyNotClaimed_holds

end GenerationCardinality
