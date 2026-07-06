import SM1.MasterClassifier

namespace SM1

theorem sm_carrier_normal_form_theorem
    (C : MasterClassifier Arena)
    (x : ComponentClaim Arena)
    (_hSameScope : SameScopePreserved x) :
    NormalFormExists x :=
  classifier_well_formed C x

theorem measurement_witness_non_promotion
    (C : MasterClassifier Arena)
    (x : ComponentClaim Arena)
    (h : x.kind = SMClaimKind.measurement) :
    Not (PrimitiveStanding x) :=
  C.noPromotionRules.measurementNoPromotion x h

theorem transport_non_generation
    (C : MasterClassifier Arena)
    (x : ComponentClaim Arena)
    (h : x.kind = SMClaimKind.route) :
    Not (PrimitiveStanding x) :=
  C.noPromotionRules.transportNoGeneration x h

structure TargetUpdateRules (Arena : StandardModelArena) where
  nonSameScopeImpliesUpdate :
    (x : ComponentClaim Arena) -> Not (SameScopePreserved x) -> TargetUpdateStatus x
  updateImpliesNotSameScopeSurvivor :
    (x : ComponentClaim Arena) -> TargetUpdateStatus x -> Not (SameScopePreserved x)

theorem target_update_separation
    (R : TargetUpdateRules Arena)
    (x : ComponentClaim Arena)
    (h : Not (SameScopePreserved x)) :
    TargetUpdateStatus x :=
  R.nonSameScopeImpliesUpdate x h

theorem future_claim_classifiability
    (C : MasterClassifier Arena)
    (y : FutureSMClaim Arena) :
    Exists (fun S : StatusAssignment y => S = C.classify y) :=
  classifier_determinacy C y

structure SectorClosurePremise (Arena : StandardModelArena) where
  closesCarrierNetwork : (x : ComponentClaim Arena) -> Prop
  closedClaimsAreNotResidualPrimitive :
    (x : ComponentClaim Arena) -> closesCarrierNetwork x -> Not (PrimitiveStanding x)

theorem no_same_scope_primitive_escape_schema
    (P : SectorClosurePremise Arena)
    (y : FutureSMClaim Arena)
    (hLocal : P.closesCarrierNetwork y) :
    Not (PrimitiveStanding y) :=
  P.closedClaimsAreNotResidualPrimitive y hLocal

structure BSMAuditRules (Arena : StandardModelArena) where
  sameScopeDisposition :
    (b : BSMClaim Arena) ->
      SameScopePreserved b ->
      DerivativeStatus b \/ BurdenStatus b \/ Not (PrimitiveStanding b)
  nonSameScopeIsTargetUpdate :
    (b : BSMClaim Arena) -> Not (SameScopePreserved b) -> TargetUpdateStatus b

theorem bsm_audit_closure_same_scope
    (R : BSMAuditRules Arena)
    (b : BSMClaim Arena)
    (h : SameScopePreserved b) :
    DerivativeStatus b \/ BurdenStatus b \/ Not (PrimitiveStanding b) :=
  R.sameScopeDisposition b h

theorem counterexample_burden_is_not_survivor
    {x : ComponentClaim Arena}
    (hBurden : BurdenStatus x)
    (hRule : BurdenStatus x -> Not (PrimitiveStanding x)) :
    Not (PrimitiveStanding x) :=
  hRule hBurden

end SM1
