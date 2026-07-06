import SM5.FlavorArena

namespace SM5

structure PrimitiveFlavorCarrierPackageCertificate (Arena : FlavorArena) where
  transitionCarrierClosed : Prop
  cpHolonomyResidueClosed : Prop
  oscillationRouteClosed : Prop
  transitionCarrierClosed_holds : transitionCarrierClosed
  cpHolonomyResidueClosed_holds : cpHolonomyResidueClosed
  oscillationRouteClosed_holds : oscillationRouteClosed

def PrimitiveFlavorCarrierPackageCertificate.closed
    (cert : PrimitiveFlavorCarrierPackageCertificate Arena) : Prop :=
  cert.transitionCarrierClosed /\ cert.cpHolonomyResidueClosed /\ cert.oscillationRouteClosed

theorem primitive_flavor_carrier_package_closure
    (cert : PrimitiveFlavorCarrierPackageCertificate Arena) :
    cert.closed := by
  constructor
  · exact cert.transitionCarrierClosed_holds
  constructor
  · exact cert.cpHolonomyResidueClosed_holds
  · exact cert.oscillationRouteClosed_holds

structure RegisteredFlavorStatusPackageCertificate (Arena : FlavorArena) where
  ckmEntryClosed : Prop
  pmnsEntryClosed : Prop
  mixingAngleClosed : Prop
  matrixCoordinateClosed : Prop
  basisDiagonalizationClosed : Prop
  rephasingClosed : Prop
  rawPhaseClosed : Prop
  eigenstructureClosed : Prop
  fcncClosed : Prop
  generationLabelClosed : Prop
  fieldDuplicationClosed : Prop
  ckmEntryClosed_holds : ckmEntryClosed
  pmnsEntryClosed_holds : pmnsEntryClosed
  mixingAngleClosed_holds : mixingAngleClosed
  matrixCoordinateClosed_holds : matrixCoordinateClosed
  basisDiagonalizationClosed_holds : basisDiagonalizationClosed
  rephasingClosed_holds : rephasingClosed
  rawPhaseClosed_holds : rawPhaseClosed
  eigenstructureClosed_holds : eigenstructureClosed
  fcncClosed_holds : fcncClosed
  generationLabelClosed_holds : generationLabelClosed
  fieldDuplicationClosed_holds : fieldDuplicationClosed

def RegisteredFlavorStatusPackageCertificate.closed
    (cert : RegisteredFlavorStatusPackageCertificate Arena) : Prop :=
  cert.ckmEntryClosed /\ cert.pmnsEntryClosed /\ cert.mixingAngleClosed /\
  cert.matrixCoordinateClosed /\ cert.basisDiagonalizationClosed /\ cert.rephasingClosed /\
  cert.rawPhaseClosed /\ cert.eigenstructureClosed /\ cert.fcncClosed /\
  cert.generationLabelClosed /\ cert.fieldDuplicationClosed

theorem registered_flavor_status_package_closure
    (cert : RegisteredFlavorStatusPackageCertificate Arena) :
    cert.closed := by
  constructor
  · exact cert.ckmEntryClosed_holds
  constructor
  · exact cert.pmnsEntryClosed_holds
  constructor
  · exact cert.mixingAngleClosed_holds
  constructor
  · exact cert.matrixCoordinateClosed_holds
  constructor
  · exact cert.basisDiagonalizationClosed_holds
  constructor
  · exact cert.rephasingClosed_holds
  constructor
  · exact cert.rawPhaseClosed_holds
  constructor
  · exact cert.eigenstructureClosed_holds
  constructor
  · exact cert.fcncClosed_holds
  constructor
  · exact cert.generationLabelClosed_holds
  · exact cert.fieldDuplicationClosed_holds

structure GenerationGovernanceCertificate (Arena : FlavorArena) where
  fixedFamilyEnvelopeClosed : Prop
  generationCardinalityDeferred : Prop
  changedLoadBranchClosed : Prop
  fourthGenerationBranchClosed : Prop
  fixedFamilyEnvelopeClosed_holds : fixedFamilyEnvelopeClosed
  generationCardinalityDeferred_holds : generationCardinalityDeferred
  changedLoadBranchClosed_holds : changedLoadBranchClosed
  fourthGenerationBranchClosed_holds : fourthGenerationBranchClosed

def GenerationGovernanceCertificate.closed
    (cert : GenerationGovernanceCertificate Arena) : Prop :=
  cert.fixedFamilyEnvelopeClosed /\ cert.generationCardinalityDeferred /\
  cert.changedLoadBranchClosed /\ cert.fourthGenerationBranchClosed

theorem fixed_generation_governance_closure
    (cert : GenerationGovernanceCertificate Arena) :
    cert.closed := by
  constructor
  · exact cert.fixedFamilyEnvelopeClosed_holds
  constructor
  · exact cert.generationCardinalityDeferred_holds
  constructor
  · exact cert.changedLoadBranchClosed_holds
  · exact cert.fourthGenerationBranchClosed_holds

structure FlavorPackageCertificate (Arena : FlavorArena) where
  primitivePackage : PrimitiveFlavorCarrierPackageCertificate Arena
  statusPackage : RegisteredFlavorStatusPackageCertificate Arena
  generationPackage : GenerationGovernanceCertificate Arena
  coverageClosed : Prop
  hostileGuardClosed : Prop
  coverageClosed_holds : coverageClosed
  hostileGuardClosed_holds : hostileGuardClosed

def FlavorPackageCertificate.closed (cert : FlavorPackageCertificate Arena) : Prop :=
  cert.primitivePackage.closed /\ cert.statusPackage.closed /\ cert.generationPackage.closed /\
  cert.coverageClosed /\ cert.hostileGuardClosed

theorem flavor_package_closure
    (cert : FlavorPackageCertificate Arena) :
    cert.closed := by
  constructor
  · exact primitive_flavor_carrier_package_closure cert.primitivePackage
  constructor
  · exact registered_flavor_status_package_closure cert.statusPackage
  constructor
  · exact fixed_generation_governance_closure cert.generationPackage
  constructor
  · exact cert.coverageClosed_holds
  · exact cert.hostileGuardClosed_holds

structure FlavorSkinEvidence (x : FlavorClaim Arena) where
  numericDisplay : Prop
  matrixCoordinateDisplay : Prop
  basisChoiceDisplay : Prop
  phaseCoordinateDisplay : Prop
  generationLabelDisplay : Prop

def FlavorSkinEligible (x : FlavorClaim Arena) (E : FlavorSkinEvidence x) : Prop :=
  E.numericDisplay \/ E.matrixCoordinateDisplay \/ E.basisChoiceDisplay \/
  E.phaseCoordinateDisplay \/ E.generationLabelDisplay

structure FlavorNoPromotionRules (Arena : FlavorArena) where
  skinNoPromotion :
    (x : FlavorClaim Arena) -> (E : FlavorSkinEvidence x) ->
      FlavorSkinEligible x E -> Not (PrimitiveFlavor x)
  rawPhaseCoordinateNoPromotion :
    (x : FlavorClaim Arena) -> x.kind = FlavorClaimKind.rawPhaseCoordinate ->
      Not (PrimitiveFlavor x)
  ckmEntryNoPromotion :
    (x : FlavorClaim Arena) -> x.kind = FlavorClaimKind.ckmEntry ->
      Not (PrimitiveFlavor x)
  pmnsEntryNoPromotion :
    (x : FlavorClaim Arena) -> x.kind = FlavorClaimKind.pmnsEntry ->
      Not (PrimitiveFlavor x)
  generationLabelNoPromotion :
    (x : FlavorClaim Arena) -> x.kind = FlavorClaimKind.generationLabel ->
      Not (PrimitiveFlavor x)
  fieldDuplicationNoPromotion :
    (x : FlavorClaim Arena) -> x.kind = FlavorClaimKind.fieldDuplication ->
      Not (PrimitiveFlavor x)

theorem flavor_skin_non_promotion
    (R : FlavorNoPromotionRules Arena)
    {x : FlavorClaim Arena}
    {E : FlavorSkinEvidence x}
    (h : FlavorSkinEligible x E) :
    Not (PrimitiveFlavor x) :=
  R.skinNoPromotion x E h

end SM5
