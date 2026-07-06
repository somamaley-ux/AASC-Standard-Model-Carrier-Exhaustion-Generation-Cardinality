import SM2.MainTheorems

namespace SM2

inductive GaugePredictionClass where
  | carrierPrediction
  | branchPrediction
  | falsifier
  | handoff
  deriving DecidableEq, Repr

structure GaugePredictionRow (Arena : GaugeSectorArena) where
  id : String
  claimType : String
  expectedDisposition : GaugeStatus
  excludedStatus : String
  falsifier : String
  currentStatus : String

structure GaugeFalsificationProtocol (Arena : GaugeSectorArena) where
  preservesGaugeScope : (x : GaugeClaim Arena) -> Prop
  defeatsDerivativeStatuses : (x : GaugeClaim Arena) -> Prop
  suppliesClosedCarrierCertificate : (x : GaugeClaim Arena) -> Prop

def ClearsGaugeFalsificationProtocol
    (P : GaugeFalsificationProtocol Arena)
    (x : GaugeClaim Arena) : Prop :=
  P.preservesGaugeScope x /\
  P.defeatsDerivativeStatuses x /\
  P.suppliesClosedCarrierCertificate x

theorem reality_contact_discipline_for_gauge_predictions
    (P : GaugeFalsificationProtocol Arena)
    (x : GaugeClaim Arena)
    (h : ClearsGaugeFalsificationProtocol P x) :
    P.preservesGaugeScope x /\ P.defeatsDerivativeStatuses x /\ P.suppliesClosedCarrierCertificate x := h

end SM2
