import SM4.CCRArena

namespace SM4

structure PrimitiveCarrierPackageCertificate (Arena : CCRArena) where
  chargeResponseClosed : Prop
  chargeWitnessClosed : Prop
  chargeLatticeClosed : Prop
  chargeResponseClosed_holds : chargeResponseClosed
  chargeWitnessClosed_holds : chargeWitnessClosed
  chargeLatticeClosed_holds : chargeLatticeClosed

def PrimitiveCarrierPackageCertificate.closed (cert : PrimitiveCarrierPackageCertificate Arena) : Prop :=
  cert.chargeResponseClosed /\ cert.chargeWitnessClosed /\ cert.chargeLatticeClosed

theorem primitive_charge_carrier_package_closure
    (cert : PrimitiveCarrierPackageCertificate Arena) :
    cert.closed := by
  constructor
  · exact cert.chargeResponseClosed_holds
  constructor
  · exact cert.chargeWitnessClosed_holds
  · exact cert.chargeLatticeClosed_holds

structure RegisteredStatusPackageCertificate (Arena : CCRArena) where
  couplingModulusClosed : Prop
  spctClosed : Prop
  rgTransportClosed : Prop
  schemeMatchingClosed : Prop
  calibrationClosed : Prop
  ewemBookkeepingClosed : Prop
  eftProjectionClosed : Prop
  couplingModulusClosed_holds : couplingModulusClosed
  spctClosed_holds : spctClosed
  rgTransportClosed_holds : rgTransportClosed
  schemeMatchingClosed_holds : schemeMatchingClosed
  calibrationClosed_holds : calibrationClosed
  ewemBookkeepingClosed_holds : ewemBookkeepingClosed
  eftProjectionClosed_holds : eftProjectionClosed

def RegisteredStatusPackageCertificate.closed (cert : RegisteredStatusPackageCertificate Arena) : Prop :=
  cert.couplingModulusClosed /\ cert.spctClosed /\ cert.rgTransportClosed /\
  cert.schemeMatchingClosed /\ cert.calibrationClosed /\ cert.ewemBookkeepingClosed /\
  cert.eftProjectionClosed

theorem registered_ccr_status_package_closure
    (cert : RegisteredStatusPackageCertificate Arena) :
    cert.closed := by
  constructor
  · exact cert.couplingModulusClosed_holds
  constructor
  · exact cert.spctClosed_holds
  constructor
  · exact cert.rgTransportClosed_holds
  constructor
  · exact cert.schemeMatchingClosed_holds
  constructor
  · exact cert.calibrationClosed_holds
  constructor
  · exact cert.ewemBookkeepingClosed_holds
  · exact cert.eftProjectionClosed_holds

structure CCRPackageCertificate (Arena : CCRArena) where
  primitivePackage : PrimitiveCarrierPackageCertificate Arena
  statusPackage : RegisteredStatusPackageCertificate Arena
  coverageClosed : Prop
  hostileGuardClosed : Prop
  coverageClosed_holds : coverageClosed
  hostileGuardClosed_holds : hostileGuardClosed

def CCRPackageCertificate.closed (cert : CCRPackageCertificate Arena) : Prop :=
  cert.primitivePackage.closed /\ cert.statusPackage.closed /\ cert.coverageClosed /\ cert.hostileGuardClosed

theorem ccr_package_closure
    (cert : CCRPackageCertificate Arena) :
    cert.closed := by
  constructor
  · exact primitive_charge_carrier_package_closure cert.primitivePackage
  constructor
  · exact registered_ccr_status_package_closure cert.statusPackage
  constructor
  · exact cert.coverageClosed_holds
  · exact cert.hostileGuardClosed_holds

structure CCRSkinEvidence (x : CCRClaim Arena) where
  numericDisplay : Prop
  transportDisplay : Prop
  projectionDisplay : Prop
  normalizationConvention : Prop
  calibrationDisplay : Prop

def CCRSkinEligible (x : CCRClaim Arena) (E : CCRSkinEvidence x) : Prop :=
  E.numericDisplay \/ E.transportDisplay \/ E.projectionDisplay \/
  E.normalizationConvention \/ E.calibrationDisplay

structure CCRNoPromotionRules (Arena : CCRArena) where
  skinNoPromotion :
    (x : CCRClaim Arena) -> (E : CCRSkinEvidence x) -> CCRSkinEligible x E -> Not (PrimitiveCCR x)
  couplingValueNoPromotion :
    (x : CCRClaim Arena) -> x.kind = CCRClaimKind.couplingValue -> Not (PrimitiveCCR x)
  rgNonGeneration :
    (x : CCRClaim Arena) -> x.kind = CCRClaimKind.rgFlow -> Not (PrimitiveCCR x)

theorem ccr_skin_non_promotion
    (R : CCRNoPromotionRules Arena)
    {x : CCRClaim Arena}
    {E : CCRSkinEvidence x}
    (h : CCRSkinEligible x E) :
    Not (PrimitiveCCR x) :=
  R.skinNoPromotion x E h

end SM4
