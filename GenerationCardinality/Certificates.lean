import GenerationCardinality.Arena

namespace GenerationCardinality

structure CardinalityEndpointCertificate (Arena : OpenGenerationArena) where
  openArenaLift : Prop
  noGenerationByPresentation : Prop
  noSelector : Prop
  pairwiseCompletenessForced : Prop
  firstExactCircuitRank : Prop
  cycleQuotientClosed : Prop
  roleIncidenceLiveness : Prop
  rankOnePrimitiveTarget : Prop
  lowerCardinalityEliminated : Prop
  threeRolePositive : Prop
  noHigherGenerationClosure : Prop
  arcHandoffClosed : Prop
  openArenaLift_holds : openArenaLift
  noGenerationByPresentation_holds : noGenerationByPresentation
  noSelector_holds : noSelector
  pairwiseCompletenessForced_holds : pairwiseCompletenessForced
  firstExactCircuitRank_holds : firstExactCircuitRank
  cycleQuotientClosed_holds : cycleQuotientClosed
  roleIncidenceLiveness_holds : roleIncidenceLiveness
  rankOnePrimitiveTarget_holds : rankOnePrimitiveTarget
  lowerCardinalityEliminated_holds : lowerCardinalityEliminated
  threeRolePositive_holds : threeRolePositive
  noHigherGenerationClosure_holds : noHigherGenerationClosure
  arcHandoffClosed_holds : arcHandoffClosed

def CardinalityEndpointCertificate.closed
    (cert : CardinalityEndpointCertificate Arena) : Prop :=
  cert.openArenaLift /\ cert.noGenerationByPresentation /\ cert.noSelector /\
  cert.pairwiseCompletenessForced /\ cert.firstExactCircuitRank /\
  cert.cycleQuotientClosed /\ cert.roleIncidenceLiveness /\
  cert.rankOnePrimitiveTarget /\ cert.lowerCardinalityEliminated /\
  cert.threeRolePositive /\ cert.noHigherGenerationClosure /\ cert.arcHandoffClosed

theorem cardinality_endpoint_certificate_closure
    (cert : CardinalityEndpointCertificate Arena) :
    cert.closed := by
  constructor
  · exact cert.openArenaLift_holds
  constructor
  · exact cert.noGenerationByPresentation_holds
  constructor
  · exact cert.noSelector_holds
  constructor
  · exact cert.pairwiseCompletenessForced_holds
  constructor
  · exact cert.firstExactCircuitRank_holds
  constructor
  · exact cert.cycleQuotientClosed_holds
  constructor
  · exact cert.roleIncidenceLiveness_holds
  constructor
  · exact cert.rankOnePrimitiveTarget_holds
  constructor
  · exact cert.lowerCardinalityEliminated_holds
  constructor
  · exact cert.threeRolePositive_holds
  constructor
  · exact cert.noHigherGenerationClosure_holds
  · exact cert.arcHandoffClosed_holds

theorem generation_role_certificate_closure
    (cert : GenerationRoleCertificate C) :
    cert.closed := by
  constructor
  · exact cert.liveTransitionRankMatch_holds
  constructor
  · exact cert.roleIncidenceLive_holds
  constructor
  · exact cert.primitiveCarrierNonvacuous_holds
  · exact cert.rankMatching_holds

end GenerationCardinality
