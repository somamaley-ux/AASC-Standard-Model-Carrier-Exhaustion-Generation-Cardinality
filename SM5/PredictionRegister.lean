import SM5.MainTheorems

namespace SM5

structure FlavorFalsificationProtocol (Arena : FlavorArena) where
  preservesFlavorScope : (x : FlavorClaim Arena) -> Prop
  defeatsCoordinateOrSkinReading : (x : FlavorClaim Arena) -> Prop
  suppliesClosedCarrierCertificate : (x : FlavorClaim Arena) -> Prop
  respectsGenerationCardinalityBoundary : (x : FlavorClaim Arena) -> Prop

def ClearsFlavorFalsificationProtocol
    (P : FlavorFalsificationProtocol Arena)
    (x : FlavorClaim Arena) : Prop :=
  P.preservesFlavorScope x /\ P.defeatsCoordinateOrSkinReading x /\
  P.suppliesClosedCarrierCertificate x /\ P.respectsGenerationCardinalityBoundary x

theorem reality_contact_discipline_for_flavor_predictions
    (P : FlavorFalsificationProtocol Arena)
    (x : FlavorClaim Arena)
    (h : ClearsFlavorFalsificationProtocol P x) :
    P.preservesFlavorScope x /\ P.defeatsCoordinateOrSkinReading x /\
    P.suppliesClosedCarrierCertificate x /\ P.respectsGenerationCardinalityBoundary x := h

end SM5
