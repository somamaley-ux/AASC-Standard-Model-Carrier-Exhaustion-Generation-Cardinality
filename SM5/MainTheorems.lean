import SM5.PackageCertificates

namespace SM5

structure FlavorClassificationRules (Arena : FlavorArena) where
  classifySameScope : (x : FlavorClaim Arena) -> SameScopeFlavor x -> FlavorDisposition x
  changedLoadTargetUpdate :
    (L : ChangedFlavorLoad Arena) -> RequiresFlavorTargetUpdate L -> L.changesPrimitiveLoad
  certifiedChangedLoadFixedEvaluation :
    (L : ChangedFlavorLoad Arena) -> AdmitsFixedLoadEvaluation L -> L.certifiedInFixedEnvelope
  certificateToDeletion :
    FlavorPackageCertificate Arena ->
      Not (Exists (fun x : FlavorClaim Arena =>
        PrimitiveFlavor x /\ SameScopeFlavor x /\ Not (FlavorDisposition x)))

theorem raw_phase_coordinate_non_promotion
    (R : FlavorNoPromotionRules Arena)
    (x : FlavorClaim Arena)
    (hKind : x.kind = FlavorClaimKind.rawPhaseCoordinate) :
    Not (PrimitiveFlavor x) :=
  R.rawPhaseCoordinateNoPromotion x hKind

theorem holonomy_residue_not_raw_phase_primitive
    (R : FlavorNoPromotionRules Arena)
    (x : FlavorClaim Arena)
    (hKind : x.kind = FlavorClaimKind.rawPhaseCoordinate) :
    Not (PrimitiveFlavor x) :=
  raw_phase_coordinate_non_promotion R x hKind

theorem ckm_entry_non_primitivity
    (R : FlavorNoPromotionRules Arena)
    (x : FlavorClaim Arena)
    (hKind : x.kind = FlavorClaimKind.ckmEntry) :
    Not (PrimitiveFlavor x) :=
  R.ckmEntryNoPromotion x hKind

theorem pmns_entry_non_primitivity
    (R : FlavorNoPromotionRules Arena)
    (x : FlavorClaim Arena)
    (hKind : x.kind = FlavorClaimKind.pmnsEntry) :
    Not (PrimitiveFlavor x) :=
  R.pmnsEntryNoPromotion x hKind

theorem mixing_angles_as_redescription_coordinates
    (cert : RegisteredFlavorStatusPackageCertificate Arena) :
    cert.mixingAngleClosed :=
  cert.mixingAngleClosed_holds

theorem matrix_coordinate_classification
    (cert : RegisteredFlavorStatusPackageCertificate Arena) :
    cert.matrixCoordinateClosed :=
  cert.matrixCoordinateClosed_holds

theorem basis_and_diagonalization_non_promotion
    (cert : RegisteredFlavorStatusPackageCertificate Arena) :
    cert.basisDiagonalizationClosed :=
  cert.basisDiagonalizationClosed_holds

theorem rephasing_redundancy_exhaustion
    (cert : RegisteredFlavorStatusPackageCertificate Arena) :
    cert.rephasingClosed :=
  cert.rephasingClosed_holds

theorem raw_phase_non_primitivity
    (cert : RegisteredFlavorStatusPackageCertificate Arena) :
    cert.rawPhaseClosed :=
  cert.rawPhaseClosed_holds

theorem cp_phase_classification
    (cert : PrimitiveFlavorCarrierPackageCertificate Arena) :
    cert.cpHolonomyResidueClosed :=
  cert.cpHolonomyResidueClosed_holds

theorem eigenstructure_non_primitivity
    (cert : RegisteredFlavorStatusPackageCertificate Arena) :
    cert.eigenstructureClosed :=
  cert.eigenstructureClosed_holds

theorem oscillation_route_status
    (cert : PrimitiveFlavorCarrierPackageCertificate Arena) :
    cert.oscillationRouteClosed :=
  cert.oscillationRouteClosed_holds

theorem pmns_boundary_reconstruction_theorem
    (cert : RegisteredFlavorStatusPackageCertificate Arena) :
    cert.pmnsEntryClosed :=
  cert.pmnsEntryClosed_holds

theorem fixed_load_fcnc_discipline
    (cert : RegisteredFlavorStatusPackageCertificate Arena) :
    cert.fcncClosed :=
  cert.fcncClosed_holds

theorem fcnc_primitive_non_promotion
    (cert : RegisteredFlavorStatusPackageCertificate Arena) :
    cert.fcncClosed :=
  cert.fcncClosed_holds

theorem generation_label_non_promotion
    (R : FlavorNoPromotionRules Arena)
    (x : FlavorClaim Arena)
    (hKind : x.kind = FlavorClaimKind.generationLabel) :
    Not (PrimitiveFlavor x) :=
  R.generationLabelNoPromotion x hKind

theorem field_duplication_non_promotion
    (R : FlavorNoPromotionRules Arena)
    (x : FlavorClaim Arena)
    (hKind : x.kind = FlavorClaimKind.fieldDuplication) :
    Not (PrimitiveFlavor x) :=
  R.fieldDuplicationNoPromotion x hKind

theorem generation_alteration_branch
    (L : ChangedFlavorLoad Arena)
    (h : L.changesPrimitiveLoad) :
    L.changesPrimitiveLoad := h

theorem target_update_for_uncertified_changed_flavor_load
    (R : FlavorClassificationRules Arena)
    (L : ChangedFlavorLoad Arena)
    (h : RequiresFlavorTargetUpdate L) :
    L.changesPrimitiveLoad :=
  R.changedLoadTargetUpdate L h

theorem fixed_load_evaluation_for_certified_changed_flavor_load
    (R : FlavorClassificationRules Arena)
    (L : ChangedFlavorLoad Arena)
    (h : AdmitsFixedLoadEvaluation L) :
    L.certifiedInFixedEnvelope :=
  R.certifiedChangedLoadFixedEvaluation L h

theorem flavor_bsm_branch_theorem
    (R : FlavorClassificationRules Arena)
    (x : FlavorClaim Arena)
    (hScope : SameScopeFlavor x) :
    FlavorDisposition x :=
  R.classifySameScope x hScope

theorem fourth_generation_fixed_envelope_branch
    (cert : GenerationGovernanceCertificate Arena) :
    cert.fourthGenerationBranchClosed :=
  cert.fourthGenerationBranchClosed_holds

theorem flavor_coverage_theorem
    (cert : FlavorPackageCertificate Arena) :
    cert.coverageClosed :=
  cert.coverageClosed_holds

theorem scoped_flavor_sector_primitive_status_deletion
    (R : FlavorClassificationRules Arena)
    (cert : FlavorPackageCertificate Arena) :
    Not (Exists (fun x : FlavorClaim Arena =>
      PrimitiveFlavor x /\ SameScopeFlavor x /\ Not (FlavorDisposition x))) :=
  R.certificateToDeletion cert

end SM5
