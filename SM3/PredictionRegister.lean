import SM3.MainTheorems

namespace SM3

structure MatterFalsificationProtocol (Arena : MatterSectorArena) where
  preservesMatterScope : (x : MatterClaim Arena) -> Prop
  defeatsDerivativeStatuses : (x : MatterClaim Arena) -> Prop
  suppliesClosedCarrierCertificate : (x : MatterClaim Arena) -> Prop

def ClearsMatterFalsificationProtocol
    (P : MatterFalsificationProtocol Arena)
    (x : MatterClaim Arena) : Prop :=
  P.preservesMatterScope x /\
  P.defeatsDerivativeStatuses x /\
  P.suppliesClosedCarrierCertificate x

theorem reality_contact_discipline_for_matter_predictions
    (P : MatterFalsificationProtocol Arena)
    (x : MatterClaim Arena)
    (h : ClearsMatterFalsificationProtocol P x) :
    P.preservesMatterScope x /\ P.defeatsDerivativeStatuses x /\ P.suppliesClosedCarrierCertificate x := h

end SM3
