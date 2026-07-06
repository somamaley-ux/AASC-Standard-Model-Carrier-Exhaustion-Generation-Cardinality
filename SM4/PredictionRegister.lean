import SM4.MainTheorems

namespace SM4

structure CCRFalsificationProtocol (Arena : CCRArena) where
  preservesCCRScope : (x : CCRClaim Arena) -> Prop
  defeatsTransportProjectionCalibration : (x : CCRClaim Arena) -> Prop
  suppliesClosedCarrierCertificate : (x : CCRClaim Arena) -> Prop

def ClearsCCRFalsificationProtocol
    (P : CCRFalsificationProtocol Arena)
    (x : CCRClaim Arena) : Prop :=
  P.preservesCCRScope x /\ P.defeatsTransportProjectionCalibration x /\ P.suppliesClosedCarrierCertificate x

theorem reality_contact_discipline_for_ccr_predictions
    (P : CCRFalsificationProtocol Arena)
    (x : CCRClaim Arena)
    (h : ClearsCCRFalsificationProtocol P x) :
    P.preservesCCRScope x /\ P.defeatsTransportProjectionCalibration x /\ P.suppliesClosedCarrierCertificate x := h

end SM4
