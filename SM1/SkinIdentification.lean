import SM1.CarrierAdmission

namespace SM1

structure SkinEvidence (x : ComponentClaim Arena) where
  gaugeDependent : Prop
  basisDependent : Prop
  schemeDependent : Prop
  normalizationDependent : Prop
  measurementRouteDependent : Prop
  projectionDependent : Prop
  modelNameDependent : Prop
  eftCoordinateDependent : Prop
  downstreamParameterLevel : Prop
  lacksInvariantRolePreservation : Prop

def SkinEligible (x : ComponentClaim Arena) (E : SkinEvidence x) : Prop :=
  E.gaugeDependent \/
  E.basisDependent \/
  E.schemeDependent \/
  E.normalizationDependent \/
  E.measurementRouteDependent \/
  E.projectionDependent \/
  E.modelNameDependent \/
  E.eftCoordinateDependent \/
  E.downstreamParameterLevel \/
  E.lacksInvariantRolePreservation

structure ClassifierNoPromotionRules (Arena : StandardModelArena) where
  skinNoPromotion :
    (x : ComponentClaim Arena) ->
      (E : SkinEvidence x) ->
      SkinEligible x E ->
      Not (CarrierCertified x) ->
      Not (PrimitiveStanding x)
  measurementNoPromotion :
    (x : ComponentClaim Arena) -> x.kind = SMClaimKind.measurement -> Not (PrimitiveStanding x)
  transportNoGeneration :
    (x : ComponentClaim Arena) -> x.kind = SMClaimKind.route -> Not (PrimitiveStanding x)

theorem skin_identification_lemma
    {x : ComponentClaim Arena} {E : SkinEvidence x}
    (h : SkinEligible x E) :
    SkinEligible x E := h

theorem non_circular_no_promotion_form
    {x : ComponentClaim Arena} {E : SkinEvidence x}
    (R : ClassifierNoPromotionRules Arena)
    (hSkin : SkinEligible x E)
    (hNoCert : Not (CarrierCertified x)) :
    Not (PrimitiveStanding x) :=
  R.skinNoPromotion x E hSkin hNoCert

end SM1
