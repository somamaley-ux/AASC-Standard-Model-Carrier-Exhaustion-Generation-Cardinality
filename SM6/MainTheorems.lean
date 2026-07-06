import SM6.PackageCertificates

namespace SM6

structure SM6ClassificationRules (Arena : StandardModelCarrierArena) where
  classifySameScope : (x : SM6Claim Arena) -> SameScopeSM x -> SM6Disposition x
  noRegisteredToPrimitiveLeakage :
    (x : SM6Claim Arena) -> RegisteredStatus x -> Not (PrimitiveSurvivor x)
  governanceNoLeakage :
    (x : SM6Claim Arena) -> GenerationGovernance x -> Not (PrimitiveSurvivor x)
  burdenFailureNoLeakage :
    (x : SM6Claim Arena) -> (CounterexampleBurden x \/ FailedPrimitive x) -> Not (PrimitiveSurvivor x)
  targetUpdateNoLeakage :
    (x : SM6Claim Arena) -> TargetUpdate x -> Not (PrimitiveSurvivor x)
  carrierExhaustion :
    SM6ClosureCertificate Arena ->
      Not (Exists (fun x : SM6Claim Arena => PrimitiveSurvivor x))

theorem no_registered_status_promotion
    (cert : RegisteredStatusAtlasCertificate Arena) :
    cert.noRegisteredPromotion :=
  cert.noRegisteredPromotion_holds

theorem generation_governance_separation
    (cert : RegisteredStatusAtlasCertificate Arena) :
    cert.generationSeparation :=
  cert.generationSeparation_holds

theorem carrier_architecture_coherence
    (cert : GlobalPrimitiveCarrierPackage Arena) :
    cert.sharedRoleCoherent :=
  cert.sharedRoleCoherent_holds

theorem eft_display_classification
    (cert : RegisteredStatusAtlasCertificate Arena) :
    cert.projectionEFTClosed :=
  cert.projectionEFTClosed_holds

theorem numerical_availability_does_not_confer_primitive_standing
    (cert : RegisteredStatusAtlasCertificate Arena) :
    cert.numericalAvailabilityNoPromotion :=
  cert.numericalAvailabilityNoPromotion_holds

theorem measurement_nonpromotion
    (cert : RegisteredStatusAtlasCertificate Arena) :
    cert.measurementNonpromotion :=
  cert.measurementNonpromotion_holds

theorem same_scope_bsm_exhaustion
    (R : SM6ClassificationRules Arena)
    (x : SM6Claim Arena)
    (hScope : SameScopeSM x) :
    SM6Disposition x :=
  R.classifySameScope x hScope

theorem hostile_certificate_nonabsorption
    (cert : HostileBranchCertificate Arena) :
    cert.noValidSameScopeHostileCertificate :=
  cert.noValidSameScopeHostileCertificate_holds

theorem sm6_normal_form
    (R : SM6ClassificationRules Arena)
    (x : SM6Claim Arena)
    (hScope : SameScopeSM x) :
    SM6Disposition x :=
  R.classifySameScope x hScope

theorem residual_survivor_deletion_test
    (cert : SM6ClosureCertificate Arena) :
    cert.residualSurvivorDeleted :=
  cert.residualSurvivorDeleted_holds

theorem global_same_scope_coverage
    (cert : SM6ClosureCertificate Arena) :
    cert.globalSameScopeCoverage :=
  cert.globalSameScopeCoverage_holds

theorem no_registered_to_primitive_leakage
    (R : SM6ClassificationRules Arena)
    (x : SM6Claim Arena)
    (h : RegisteredStatus x) :
    Not (PrimitiveSurvivor x) :=
  R.noRegisteredToPrimitiveLeakage x h

theorem governance_no_leakage
    (R : SM6ClassificationRules Arena)
    (x : SM6Claim Arena)
    (h : GenerationGovernance x) :
    Not (PrimitiveSurvivor x) :=
  R.governanceNoLeakage x h

theorem burden_and_failure_no_leakage
    (R : SM6ClassificationRules Arena)
    (x : SM6Claim Arena)
    (h : CounterexampleBurden x \/ FailedPrimitive x) :
    Not (PrimitiveSurvivor x) :=
  R.burdenFailureNoLeakage x h

theorem target_update_no_leakage
    (R : SM6ClassificationRules Arena)
    (x : SM6Claim Arena)
    (h : TargetUpdate x) :
    Not (PrimitiveSurvivor x) :=
  R.targetUpdateNoLeakage x h

theorem role_necessity_exhaustion_inside_dsm
    (cert : SM6ClosureCertificate Arena) :
    cert.roleNecessityExhaustion :=
  cert.roleNecessityExhaustion_holds

theorem standard_model_carrier_exhaustion_closure
    (R : SM6ClassificationRules Arena)
    (cert : SM6ClosureCertificate Arena) :
    Not (Exists (fun x : SM6Claim Arena => PrimitiveSurvivor x)) :=
  R.carrierExhaustion cert

theorem primitive_closure_skin_openness
    (cert : SM6ClosureCertificate Arena) :
    cert.primitivePackage.closed /\ cert.statusAtlas.closed :=
  And.intro
    (global_primitive_carrier_package_closure cert.primitivePackage)
    (global_status_registration cert.statusAtlas)

end SM6
