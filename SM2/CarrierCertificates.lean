import SM2.GaugeArena

namespace SM2

structure GaugeCarrierCertificate (x : GaugeClaim Arena) where
  roleClosure : Prop
  redescriptionInvariance : Prop
  licensingProof : Prop
  descentExclusion : Prop
  noHiddenSelector : Prop
  gaugeSectorClosure : Prop
  roleClosure_holds : roleClosure
  redescriptionInvariance_holds : redescriptionInvariance
  licensingProof_holds : licensingProof
  descentExclusion_holds : descentExclusion
  noHiddenSelector_holds : noHiddenSelector
  gaugeSectorClosure_holds : gaugeSectorClosure

def GaugeCarrierCertificate.closed (cert : GaugeCarrierCertificate x) : Prop :=
  cert.roleClosure /\
  cert.redescriptionInvariance /\
  cert.licensingProof /\
  cert.descentExclusion /\
  cert.noHiddenSelector /\
  cert.gaugeSectorClosure

theorem gauge_carrier_certificate_suffices
    (cert : GaugeCarrierCertificate x) :
    cert.closed := by
  constructor
  · exact cert.roleClosure_holds
  constructor
  · exact cert.redescriptionInvariance_holds
  constructor
  · exact cert.licensingProof_holds
  constructor
  · exact cert.descentExclusion_holds
  constructor
  · exact cert.noHiddenSelector_holds
  · exact cert.gaugeSectorClosure_holds

structure GaugeCarrierNetworkCertificate (Arena : GaugeSectorArena) where
  gaugeOrderClosed : Prop
  transportClosed : Prop
  curvatureHolonomyClosed : Prop
  chargeResponseClosed : Prop
  colorTransportClosed : Prop
  weakChiralClosed : Prop
  anomalyClosed : Prop
  gaugeVacuumClosed : Prop
  gaugeOrderClosed_holds : gaugeOrderClosed
  transportClosed_holds : transportClosed
  curvatureHolonomyClosed_holds : curvatureHolonomyClosed
  chargeResponseClosed_holds : chargeResponseClosed
  colorTransportClosed_holds : colorTransportClosed
  weakChiralClosed_holds : weakChiralClosed
  anomalyClosed_holds : anomalyClosed
  gaugeVacuumClosed_holds : gaugeVacuumClosed

def GaugeCarrierNetworkCertificate.closed (cert : GaugeCarrierNetworkCertificate Arena) : Prop :=
  cert.gaugeOrderClosed /\
  cert.transportClosed /\
  cert.curvatureHolonomyClosed /\
  cert.chargeResponseClosed /\
  cert.colorTransportClosed /\
  cert.weakChiralClosed /\
  cert.anomalyClosed /\
  cert.gaugeVacuumClosed

theorem gauge_carrier_certificate_closure
    (cert : GaugeCarrierNetworkCertificate Arena) :
    cert.closed := by
  constructor
  · exact cert.gaugeOrderClosed_holds
  constructor
  · exact cert.transportClosed_holds
  constructor
  · exact cert.curvatureHolonomyClosed_holds
  constructor
  · exact cert.chargeResponseClosed_holds
  constructor
  · exact cert.colorTransportClosed_holds
  constructor
  · exact cert.weakChiralClosed_holds
  constructor
  · exact cert.anomalyClosed_holds
  · exact cert.gaugeVacuumClosed_holds

structure GaugeSkinEvidence (x : GaugeClaim Arena) where
  gaugeDependent : Prop
  routeDependent : Prop
  projectionDependent : Prop
  couplingOrParameterDisplay : Prop
  fieldLabelDisplay : Prop
  lacksClosedCarrierCertificate : Prop

def GaugeSkinEligible (x : GaugeClaim Arena) (E : GaugeSkinEvidence x) : Prop :=
  E.gaugeDependent \/
  E.routeDependent \/
  E.projectionDependent \/
  E.couplingOrParameterDisplay \/
  E.fieldLabelDisplay \/
  E.lacksClosedCarrierCertificate

structure GaugeNoPromotionRules (Arena : GaugeSectorArena) where
  skinNoPromotion :
    (x : GaugeClaim Arena) ->
      (E : GaugeSkinEvidence x) ->
      GaugeSkinEligible x E ->
      Not (PrimitiveGauge x)
  couplingNotCarrier :
    (x : GaugeClaim Arena) ->
      x.kind = GaugeClaimKind.couplingValue ->
      Not (PrimitiveGauge x)

theorem gauge_skin_non_promotion
    (R : GaugeNoPromotionRules Arena)
    {x : GaugeClaim Arena}
    {E : GaugeSkinEvidence x}
    (h : GaugeSkinEligible x E) :
    Not (PrimitiveGauge x) :=
  R.skinNoPromotion x E h

end SM2
