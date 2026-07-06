import SM4.PackageCertificates

namespace SM4

structure CCRClassificationRules (Arena : CCRArena) where
  classifySameScope : (x : CCRClaim Arena) -> SameScopeCCR x -> CCRDisposition x
  certificateToDeletion :
    CCRPackageCertificate Arena ->
      Not (Exists (fun x : CCRClaim Arena => PrimitiveCCR x /\ SameScopeCCR x /\ Not (CCRDisposition x)))

theorem charge_number_non_promotion
    (R : CCRNoPromotionRules Arena)
    (x : CCRClaim Arena)
    (hKind : x.kind = CCRClaimKind.chargeNumber) :
    Not (PrimitiveCCR x) := by
  have _kindCheck : x.kind = CCRClaimKind.chargeNumber := hKind
  let E : CCRSkinEvidence x :=
    { numericDisplay := True, transportDisplay := False, projectionDisplay := False,
      normalizationConvention := False, calibrationDisplay := False }
  have hSkin : CCRSkinEligible x E := Or.inl True.intro
  exact R.skinNoPromotion x E hSkin

theorem coupling_value_non_primitivity
    (R : CCRNoPromotionRules Arena)
    (x : CCRClaim Arena)
    (hKind : x.kind = CCRClaimKind.couplingValue) :
    Not (PrimitiveCCR x) :=
  R.couplingValueNoPromotion x hKind

theorem rg_transport_non_generation
    (R : CCRNoPromotionRules Arena)
    (x : CCRClaim Arena)
    (hKind : x.kind = CCRClaimKind.rgFlow) :
    Not (PrimitiveCCR x) :=
  R.rgNonGeneration x hKind

theorem ccr_bsm_branch_theorem
    (R : CCRClassificationRules Arena)
    (x : CCRClaim Arena)
    (hScope : SameScopeCCR x) :
    CCRDisposition x :=
  R.classifySameScope x hScope

theorem ccr_coverage_theorem
    (cert : CCRPackageCertificate Arena) :
    cert.coverageClosed :=
  cert.coverageClosed_holds

theorem scoped_ccr_primitive_status_deletion
    (R : CCRClassificationRules Arena)
    (cert : CCRPackageCertificate Arena) :
    Not (Exists (fun x : CCRClaim Arena => PrimitiveCCR x /\ SameScopeCCR x /\ Not (CCRDisposition x))) :=
  R.certificateToDeletion cert

end SM4
