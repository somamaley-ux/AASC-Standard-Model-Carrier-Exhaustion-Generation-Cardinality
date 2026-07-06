import SM2.CarrierCertificates

namespace SM2

def GaugeDisposition (x : GaugeClaim Arena) : Prop :=
  DescendsToClosedGaugeCarrier x \/
  RegisteredDerivative x \/
  TargetUpdateGauge x \/
  CounterexampleBurdenGauge x \/
  FailedPrimitive x

structure GaugeClassificationRules (Arena : GaugeSectorArena) where
  classifySameScope : (x : GaugeClaim Arena) -> SameScopeGauge x -> GaugeDisposition x
  targetUpdateWhenNotSameScope : (x : GaugeClaim Arena) -> Not (SameScopeGauge x) -> TargetUpdateGauge x
  certificateToDeletion : GaugeCarrierNetworkCertificate Arena -> Not (Exists (fun x : GaugeClaim Arena => PrimitiveGauge x /\ SameScopeGauge x /\ Not (GaugeDisposition x)))

theorem certificate_to_primitive_status_deletion_form
    (R : GaugeClassificationRules Arena)
    (cert : GaugeCarrierNetworkCertificate Arena) :
    Not (Exists (fun x : GaugeClaim Arena => PrimitiveGauge x /\ SameScopeGauge x /\ Not (GaugeDisposition x))) :=
  R.certificateToDeletion cert

theorem scoped_gauge_sector_primitive_status_deletion
    (R : GaugeClassificationRules Arena)
    (cert : GaugeCarrierNetworkCertificate Arena) :
    Not (Exists (fun x : GaugeClaim Arena => PrimitiveGauge x /\ SameScopeGauge x /\ Not (GaugeDisposition x))) :=
  certificate_to_primitive_status_deletion_form R cert

theorem photon_charge_response_carrier
    (R : GaugeClassificationRules Arena)
    (x : GaugeClaim Arena)
    (hKind : x.kind = GaugeClaimKind.photon)
    (hScope : SameScopeGauge x) :
    GaugeDisposition x := by
  have _kindCheck : x.kind = GaugeClaimKind.photon := hKind
  exact R.classifySameScope x hScope

theorem gluon_color_transport_carrier_closure
    (R : GaugeClassificationRules Arena)
    (x : GaugeClaim Arena)
    (hKind : x.kind = GaugeClaimKind.gluon)
    (hScope : SameScopeGauge x) :
    GaugeDisposition x := by
  have _kindCheck : x.kind = GaugeClaimKind.gluon := hKind
  exact R.classifySameScope x hScope

theorem weak_boson_weak_chiral_carrier_closure
    (R : GaugeClassificationRules Arena)
    (x : GaugeClaim Arena)
    (hKind : x.kind = GaugeClaimKind.weakBoson)
    (hScope : SameScopeGauge x) :
    GaugeDisposition x := by
  have _kindCheck : x.kind = GaugeClaimKind.weakBoson := hKind
  exact R.classifySameScope x hScope

theorem gauge_coupling_not_carrier
    (R : GaugeNoPromotionRules Arena)
    (x : GaugeClaim Arena)
    (hKind : x.kind = GaugeClaimKind.couplingValue) :
    Not (PrimitiveGauge x) :=
  R.couplingNotCarrier x hKind

theorem gauge_bsm_branch_certificate
    (R : GaugeClassificationRules Arena)
    (x : GaugeClaim Arena)
    (hScope : SameScopeGauge x) :
    GaugeDisposition x :=
  R.classifySameScope x hScope

theorem gauge_sector_classification
    (R : GaugeClassificationRules Arena)
    (x : GaugeClaim Arena)
    (hScope : SameScopeGauge x) :
    GaugeDisposition x :=
  R.classifySameScope x hScope

theorem no_primitive_gauge_boson_skin_escape
    (R : GaugeNoPromotionRules Arena)
    {x : GaugeClaim Arena}
    {E : GaugeSkinEvidence x}
    (hSkin : GaugeSkinEligible x E) :
    Not (PrimitiveGauge x) :=
  gauge_skin_non_promotion R hSkin

end SM2
