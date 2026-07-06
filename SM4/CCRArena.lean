import SM3

namespace SM4

inductive CCRClaimKind where
  | chargeNumber | hypercharge | normalization | couplingValue | couplingModulus
  | spctEnvelope | rgFlow | schemeCoordinate | matchingCondition | eftCoefficient
  | constantRole | calibration | bsmCCRClaim | targetUpdatingDiscovery
  deriving DecidableEq, Repr

inductive CCRStatus where
  | primitiveCarrier | registeredStatus | skin | transport | projection
  | calibration | targetUpdate | burden | failedPrimitive | hostile
  deriving DecidableEq, Repr

structure CCRArena where
  sm1Arena : SM1.StandardModelArena
  gaugeArena : SM2.GaugeSectorArena
  matterArena : SM3.MatterSectorArena
  ccrScope : Type
  primitiveCarrierPackage : Type
  registeredStatusPackage : Type
  dependencyLedger : Type

structure CCRClaim (Arena : CCRArena) where
  kind : CCRClaimKind
  sameScopeCCR : Prop
  primitiveCCRStanding : Prop
  descendsToPrimitiveCarrier : Prop
  registeredCCRStatus : Prop
  targetUpdateCCR : Prop
  burdenCCR : Prop
  failedPrimitive : Prop
  hostileBranch : Prop

def SameScopeCCR (x : CCRClaim Arena) : Prop := x.sameScopeCCR
def PrimitiveCCR (x : CCRClaim Arena) : Prop := x.primitiveCCRStanding
def CCRDisposition (x : CCRClaim Arena) : Prop :=
  x.descendsToPrimitiveCarrier \/ x.registeredCCRStatus \/ x.targetUpdateCCR \/
  x.burdenCCR \/ x.failedPrimitive \/ x.hostileBranch

end SM4
