import SM3.MatterArena

namespace SM3

structure MatterCarrierCertificate (x : MatterClaim Arena) where
  roleClosure : Prop
  redescriptionInvariance : Prop
  licensingProof : Prop
  gaugeCompatibility : Prop
  noHiddenSelector : Prop
  matterSectorClosure : Prop
  roleClosure_holds : roleClosure
  redescriptionInvariance_holds : redescriptionInvariance
  licensingProof_holds : licensingProof
  gaugeCompatibility_holds : gaugeCompatibility
  noHiddenSelector_holds : noHiddenSelector
  matterSectorClosure_holds : matterSectorClosure

def MatterCarrierCertificate.closed (cert : MatterCarrierCertificate x) : Prop :=
  cert.roleClosure /\
  cert.redescriptionInvariance /\
  cert.licensingProof /\
  cert.gaugeCompatibility /\
  cert.noHiddenSelector /\
  cert.matterSectorClosure

theorem matter_carrier_certificate_suffices
    (cert : MatterCarrierCertificate x) :
    cert.closed := by
  constructor
  · exact cert.roleClosure_holds
  constructor
  · exact cert.redescriptionInvariance_holds
  constructor
  · exact cert.licensingProof_holds
  constructor
  · exact cert.gaugeCompatibility_holds
  constructor
  · exact cert.noHiddenSelector_holds
  · exact cert.matterSectorClosure_holds

structure MatterCarrierNetworkCertificate (Arena : MatterSectorArena) where
  matterRepresentationClosed : Prop
  colorBearingMatterClosed : Prop
  colorlessChargedMatterClosed : Prop
  neutralWeakMatterClosed : Prop
  massResponseSlotClosed : Prop
  coverageClosed : Prop
  hostileResidualGuardClosed : Prop
  matterRepresentationClosed_holds : matterRepresentationClosed
  colorBearingMatterClosed_holds : colorBearingMatterClosed
  colorlessChargedMatterClosed_holds : colorlessChargedMatterClosed
  neutralWeakMatterClosed_holds : neutralWeakMatterClosed
  massResponseSlotClosed_holds : massResponseSlotClosed
  coverageClosed_holds : coverageClosed
  hostileResidualGuardClosed_holds : hostileResidualGuardClosed

def MatterCarrierNetworkCertificate.closed (cert : MatterCarrierNetworkCertificate Arena) : Prop :=
  cert.matterRepresentationClosed /\
  cert.colorBearingMatterClosed /\
  cert.colorlessChargedMatterClosed /\
  cert.neutralWeakMatterClosed /\
  cert.massResponseSlotClosed /\
  cert.coverageClosed /\
  cert.hostileResidualGuardClosed

theorem matter_carrier_package_closure
    (cert : MatterCarrierNetworkCertificate Arena) :
    cert.closed := by
  constructor
  · exact cert.matterRepresentationClosed_holds
  constructor
  · exact cert.colorBearingMatterClosed_holds
  constructor
  · exact cert.colorlessChargedMatterClosed_holds
  constructor
  · exact cert.neutralWeakMatterClosed_holds
  constructor
  · exact cert.massResponseSlotClosed_holds
  constructor
  · exact cert.coverageClosed_holds
  · exact cert.hostileResidualGuardClosed_holds

structure MatterSkinEvidence (x : MatterClaim Arena) where
  fieldNotation : Prop
  representationLabel : Prop
  massOrYukawaCoordinate : Prop
  generationLabel : Prop
  detectorRoute : Prop
  flavorRoute : Prop

def MatterSkinEligible (x : MatterClaim Arena) (E : MatterSkinEvidence x) : Prop :=
  E.fieldNotation \/ E.representationLabel \/ E.massOrYukawaCoordinate \/
  E.generationLabel \/ E.detectorRoute \/ E.flavorRoute

structure MatterNoPromotionRules (Arena : MatterSectorArena) where
  skinNoPromotion :
    (x : MatterClaim Arena) ->
      (E : MatterSkinEvidence x) ->
      MatterSkinEligible x E ->
      Not (PrimitiveMatter x)
  massYukawaNoPromotion :
    (x : MatterClaim Arena) ->
      (x.kind = MatterClaimKind.massValue \/ x.kind = MatterClaimKind.yukawaEntry) ->
      Not (PrimitiveMatter x)

theorem matter_skin_non_promotion
    (R : MatterNoPromotionRules Arena)
    {x : MatterClaim Arena}
    {E : MatterSkinEvidence x}
    (h : MatterSkinEligible x E) :
    Not (PrimitiveMatter x) :=
  R.skinNoPromotion x E h

end SM3
