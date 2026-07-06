import SM6.MainTheorems

namespace SM6

structure SM6FalsificationProtocol (Arena : StandardModelCarrierArena) where
  preservesSameScope : (x : SM6Claim Arena) -> Prop
  preservesKernel : (x : SM6Claim Arena) -> Prop
  defeatsConstructorPartition : (x : SM6Claim Arena) -> Prop
  suppliesValidHostileCertificate : (x : SM6Claim Arena) -> Prop

def ClearsSM6FalsificationProtocol
    (P : SM6FalsificationProtocol Arena)
    (x : SM6Claim Arena) : Prop :=
  P.preservesSameScope x /\ P.preservesKernel x /\ P.defeatsConstructorPartition x /\
  P.suppliesValidHostileCertificate x

theorem reality_contact_discipline
    (P : SM6FalsificationProtocol Arena)
    (x : SM6Claim Arena)
    (h : ClearsSM6FalsificationProtocol P x) :
    P.preservesSameScope x /\ P.preservesKernel x /\ P.defeatsConstructorPartition x /\
    P.suppliesValidHostileCertificate x := h

end SM6
