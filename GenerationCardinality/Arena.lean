import SM6

namespace GenerationCardinality

structure OpenGenerationArena where
  sm6Arena : SM6.StandardModelCarrierArena
  generationDomain : Type
  transitionEdges : Type
  roleOccupancy : Type
  quotientResidue : Type

structure CandidateCardinalityArena (Arena : OpenGenerationArena) where
  n : Nat
  hasOpenGenerationComparison : Prop
  completeCoComparability : Prop
  rankOnePrimitiveTarget : Prop
  closedGenerationCertificate : Prop

def KernelPreserved (C : CandidateCardinalityArena Arena) : Prop :=
  C.hasOpenGenerationComparison

structure GenerationRoleCertificate (C : CandidateCardinalityArena Arena) where
  liveTransitionRankMatch : Prop
  roleIncidenceLive : Prop
  primitiveCarrierNonvacuous : Prop
  rankMatching : Prop
  liveTransitionRankMatch_holds : liveTransitionRankMatch
  roleIncidenceLive_holds : roleIncidenceLive
  primitiveCarrierNonvacuous_holds : primitiveCarrierNonvacuous
  rankMatching_holds : rankMatching

def GenerationRoleCertificate.closed
    (cert : GenerationRoleCertificate C) : Prop :=
  cert.liveTransitionRankMatch /\ cert.roleIncidenceLive /\
  cert.primitiveCarrierNonvacuous /\ cert.rankMatching

structure GenerationTransitionGraph (C : CandidateCardinalityArena Arena) where
  pairwiseComplete : Prop
  completeGraphNormalForm : Prop
  circuitRank : Nat
  pairwiseComplete_holds : pairwiseComplete
  completeGraphNormalForm_holds : completeGraphNormalForm

structure CycleSpaceResidue (C : CandidateCardinalityArena Arena) where
  rephasingDeleted : Prop
  quotientRank : Nat
  hasPrimitiveResidue : Prop
  rephasingDeleted_holds : rephasingDeleted
  hasPrimitiveResidue_holds : hasPrimitiveResidue

structure GenerationHolonomyArena (C : CandidateCardinalityArena Arena) where
  localFixedDomain : Prop
  typedImportOnly : Prop
  liveRank : Nat
  primitiveRank : Nat
  localFixedDomain_holds : localFixedDomain
  typedImportOnly_holds : typedImportOnly

structure SurplusResidue (C : CandidateCardinalityArena Arena) where
  hasSurplusPrimitiveRegister : Prop
  forcesHigherGenerationTargetUpdate : Prop

def ClosedGenCert (n : Nat) : Prop := n = 3

end GenerationCardinality
