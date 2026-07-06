import GenerationCardinality.MainTheorems

namespace GenerationCardinality

structure CardinalityFalsificationProtocol (Arena : OpenGenerationArena) where
  preservesOpenGenerationScope : Prop
  preservesKernel : Prop
  defeatsRankOneTarget : Prop
  suppliesClosedGenerationCertificate : Prop

def CardinalityFalsificationProtocol.clears
    (P : CardinalityFalsificationProtocol Arena) : Prop :=
  P.preservesOpenGenerationScope /\ P.preservesKernel /\
  P.defeatsRankOneTarget /\ P.suppliesClosedGenerationCertificate

theorem reality_contact_for_generation_cardinality
    (P : CardinalityFalsificationProtocol Arena)
    (h : P.clears) :
    P.preservesOpenGenerationScope /\ P.preservesKernel /\
    P.defeatsRankOneTarget /\ P.suppliesClosedGenerationCertificate := h

end GenerationCardinality
