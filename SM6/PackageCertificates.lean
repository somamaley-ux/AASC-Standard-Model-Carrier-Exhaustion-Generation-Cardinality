import SM6.CarrierArena

namespace SM6

structure GlobalPrimitiveCarrierPackage (Arena : StandardModelCarrierArena) where
  gaugeClosed : Prop
  matterClosed : Prop
  ccrClosed : Prop
  flavorClosed : Prop
  higgsClosed : Prop
  sharedRoleCoherent : Prop
  gaugeClosed_holds : gaugeClosed
  matterClosed_holds : matterClosed
  ccrClosed_holds : ccrClosed
  flavorClosed_holds : flavorClosed
  higgsClosed_holds : higgsClosed
  sharedRoleCoherent_holds : sharedRoleCoherent

def GlobalPrimitiveCarrierPackage.closed (cert : GlobalPrimitiveCarrierPackage Arena) : Prop :=
  cert.gaugeClosed /\ cert.matterClosed /\ cert.ccrClosed /\ cert.flavorClosed /\
  cert.higgsClosed /\ cert.sharedRoleCoherent

theorem global_primitive_carrier_package_closure
    (cert : GlobalPrimitiveCarrierPackage Arena) :
    cert.closed := by
  constructor
  · exact cert.gaugeClosed_holds
  constructor
  · exact cert.matterClosed_holds
  constructor
  · exact cert.ccrClosed_holds
  constructor
  · exact cert.flavorClosed_holds
  constructor
  · exact cert.higgsClosed_holds
  · exact cert.sharedRoleCoherent_holds

structure RegisteredStatusAtlasCertificate (Arena : StandardModelCarrierArena) where
  globalStatusRegistered : Prop
  noRegisteredPromotion : Prop
  generationSeparation : Prop
  projectionEFTClosed : Prop
  measurementNonpromotion : Prop
  numericalAvailabilityNoPromotion : Prop
  globalStatusRegistered_holds : globalStatusRegistered
  noRegisteredPromotion_holds : noRegisteredPromotion
  generationSeparation_holds : generationSeparation
  projectionEFTClosed_holds : projectionEFTClosed
  measurementNonpromotion_holds : measurementNonpromotion
  numericalAvailabilityNoPromotion_holds : numericalAvailabilityNoPromotion

def RegisteredStatusAtlasCertificate.closed
    (cert : RegisteredStatusAtlasCertificate Arena) : Prop :=
  cert.globalStatusRegistered /\ cert.noRegisteredPromotion /\ cert.generationSeparation /\
  cert.projectionEFTClosed /\ cert.measurementNonpromotion /\ cert.numericalAvailabilityNoPromotion

theorem global_status_registration
    (cert : RegisteredStatusAtlasCertificate Arena) :
    cert.closed := by
  constructor
  · exact cert.globalStatusRegistered_holds
  constructor
  · exact cert.noRegisteredPromotion_holds
  constructor
  · exact cert.generationSeparation_holds
  constructor
  · exact cert.projectionEFTClosed_holds
  constructor
  · exact cert.measurementNonpromotion_holds
  · exact cert.numericalAvailabilityNoPromotion_holds

structure ConstructorPartitionCertificate (Arena : StandardModelCarrierArena) where
  constructorExhaustion : Prop
  constructorAdequacy : Prop
  officialTargetAdequacy : Prop
  overlapNoPromotion : Prop
  survivorNormalForm : Prop
  constructorExhaustion_holds : constructorExhaustion
  constructorAdequacy_holds : constructorAdequacy
  officialTargetAdequacy_holds : officialTargetAdequacy
  overlapNoPromotion_holds : overlapNoPromotion
  survivorNormalForm_holds : survivorNormalForm

def ConstructorPartitionCertificate.closed
    (cert : ConstructorPartitionCertificate Arena) : Prop :=
  cert.constructorExhaustion /\ cert.constructorAdequacy /\ cert.officialTargetAdequacy /\
  cert.overlapNoPromotion /\ cert.survivorNormalForm

theorem constructor_partition_theorem
    (cert : ConstructorPartitionCertificate Arena) :
    cert.closed := by
  constructor
  · exact cert.constructorExhaustion_holds
  constructor
  · exact cert.constructorAdequacy_holds
  constructor
  · exact cert.officialTargetAdequacy_holds
  constructor
  · exact cert.overlapNoPromotion_holds
  · exact cert.survivorNormalForm_holds

structure HostileBranchCertificate (Arena : StandardModelCarrierArena) where
  sectorCertificateFailure : Prop
  registeredCertificateFailure : Prop
  projectionEFTCertificateFailure : Prop
  bsmAnomalyCertificateFailure : Prop
  interfaceOverlapCertificateFailure : Prop
  noValidSameScopeHostileCertificate : Prop
  sectorCertificateFailure_holds : sectorCertificateFailure
  registeredCertificateFailure_holds : registeredCertificateFailure
  projectionEFTCertificateFailure_holds : projectionEFTCertificateFailure
  bsmAnomalyCertificateFailure_holds : bsmAnomalyCertificateFailure
  interfaceOverlapCertificateFailure_holds : interfaceOverlapCertificateFailure
  noValidSameScopeHostileCertificate_holds : noValidSameScopeHostileCertificate

def HostileBranchCertificate.closed
    (cert : HostileBranchCertificate Arena) : Prop :=
  cert.sectorCertificateFailure /\ cert.registeredCertificateFailure /\
  cert.projectionEFTCertificateFailure /\ cert.bsmAnomalyCertificateFailure /\
  cert.interfaceOverlapCertificateFailure /\ cert.noValidSameScopeHostileCertificate

theorem no_valid_same_scope_hostile_certificate
    (cert : HostileBranchCertificate Arena) :
    cert.closed := by
  constructor
  · exact cert.sectorCertificateFailure_holds
  constructor
  · exact cert.registeredCertificateFailure_holds
  constructor
  · exact cert.projectionEFTCertificateFailure_holds
  constructor
  · exact cert.bsmAnomalyCertificateFailure_holds
  constructor
  · exact cert.interfaceOverlapCertificateFailure_holds
  · exact cert.noValidSameScopeHostileCertificate_holds

structure SM6ClosureCertificate (Arena : StandardModelCarrierArena) where
  primitivePackage : GlobalPrimitiveCarrierPackage Arena
  statusAtlas : RegisteredStatusAtlasCertificate Arena
  constructorPartition : ConstructorPartitionCertificate Arena
  hostileBranch : HostileBranchCertificate Arena
  globalSameScopeCoverage : Prop
  roleNecessityExhaustion : Prop
  residualSurvivorDeleted : Prop
  globalSameScopeCoverage_holds : globalSameScopeCoverage
  roleNecessityExhaustion_holds : roleNecessityExhaustion
  residualSurvivorDeleted_holds : residualSurvivorDeleted

def SM6ClosureCertificate.closed (cert : SM6ClosureCertificate Arena) : Prop :=
  cert.primitivePackage.closed /\ cert.statusAtlas.closed /\ cert.constructorPartition.closed /\
  cert.hostileBranch.closed /\ cert.globalSameScopeCoverage /\
  cert.roleNecessityExhaustion /\ cert.residualSurvivorDeleted

theorem sm6_closure_certificate_closed
    (cert : SM6ClosureCertificate Arena) :
    cert.closed := by
  constructor
  · exact global_primitive_carrier_package_closure cert.primitivePackage
  constructor
  · exact global_status_registration cert.statusAtlas
  constructor
  · exact constructor_partition_theorem cert.constructorPartition
  constructor
  · exact no_valid_same_scope_hostile_certificate cert.hostileBranch
  constructor
  · exact cert.globalSameScopeCoverage_holds
  constructor
  · exact cert.roleNecessityExhaustion_holds
  · exact cert.residualSurvivorDeleted_holds

end SM6
