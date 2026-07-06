import SM3.CarrierCertificates

namespace SM3

def MatterDisposition (x : MatterClaim Arena) : Prop :=
  DescendsToClosedMatterCarrier x \/
  RegisteredDerivative x \/
  TargetUpdateMatter x \/
  CounterexampleBurdenMatter x \/
  FailedPrimitive x \/
  HostileResidual x

structure MatterClassificationRules (Arena : MatterSectorArena) where
  classifySameScope : (x : MatterClaim Arena) -> SameScopeMatter x -> MatterDisposition x
  certificateToDeletion :
    MatterCarrierNetworkCertificate Arena ->
      Not (Exists (fun x : MatterClaim Arena => PrimitiveMatter x /\ SameScopeMatter x /\ Not (MatterDisposition x)))

theorem quark_color_bearing_matter_carrier
    (R : MatterClassificationRules Arena)
    (x : MatterClaim Arena)
    (hKind : x.kind = MatterClaimKind.quark)
    (hScope : SameScopeMatter x) :
    MatterDisposition x := by
  have _kindCheck : x.kind = MatterClaimKind.quark := hKind
  exact R.classifySameScope x hScope

theorem charged_lepton_colorless_charged_matter_carrier
    (R : MatterClassificationRules Arena)
    (x : MatterClaim Arena)
    (hKind : x.kind = MatterClaimKind.chargedLepton)
    (hScope : SameScopeMatter x) :
    MatterDisposition x := by
  have _kindCheck : x.kind = MatterClaimKind.chargedLepton := hKind
  exact R.classifySameScope x hScope

theorem neutrino_neutral_weak_matter_carrier
    (R : MatterClassificationRules Arena)
    (x : MatterClaim Arena)
    (hKind : x.kind = MatterClaimKind.neutrino)
    (hScope : SameScopeMatter x) :
    MatterDisposition x := by
  have _kindCheck : x.kind = MatterClaimKind.neutrino := hKind
  exact R.classifySameScope x hScope

theorem mass_yukawa_coordinate_non_promotion
    (R : MatterNoPromotionRules Arena)
    (x : MatterClaim Arena)
    (hKind : x.kind = MatterClaimKind.massValue \/ x.kind = MatterClaimKind.yukawaEntry) :
    Not (PrimitiveMatter x) :=
  R.massYukawaNoPromotion x hKind

theorem matter_bsm_branch_certificate
    (R : MatterClassificationRules Arena)
    (x : MatterClaim Arena)
    (hScope : SameScopeMatter x) :
    MatterDisposition x :=
  R.classifySameScope x hScope

theorem matter_sector_classification
    (R : MatterClassificationRules Arena)
    (x : MatterClaim Arena)
    (hScope : SameScopeMatter x) :
    MatterDisposition x :=
  R.classifySameScope x hScope

theorem no_primitive_matter_skin_escape
    (R : MatterNoPromotionRules Arena)
    {x : MatterClaim Arena}
    {E : MatterSkinEvidence x}
    (hSkin : MatterSkinEligible x E) :
    Not (PrimitiveMatter x) :=
  matter_skin_non_promotion R hSkin

theorem matter_coverage_theorem
    (cert : MatterCarrierNetworkCertificate Arena) :
    cert.coverageClosed :=
  cert.coverageClosed_holds

theorem scoped_matter_sector_primitive_status_deletion
    (R : MatterClassificationRules Arena)
    (cert : MatterCarrierNetworkCertificate Arena) :
    Not (Exists (fun x : MatterClaim Arena => PrimitiveMatter x /\ SameScopeMatter x /\ Not (MatterDisposition x))) :=
  R.certificateToDeletion cert

end SM3
