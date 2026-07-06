import SM4

namespace SM5

inductive FlavorClaimKind where
  | flavorTransition | cpHolonomyResidue | rawPhaseCoordinate | ckmEntry | pmnsEntry
  | mixingAngle | matrixCoordinate | basisChoice | diagonalizationCoordinate
  | rephasingRedundancy | rawPhase | cpPhase | eigenstructure | oscillationRoute
  | pmnsBoundary | fcnc | generationLabel | fieldDuplication | generationAlteration
  | changedFlavorLoad | fourthGeneration | registeredFlavorStatus | hostileBranch
  | targetUpdatingDiscovery
  deriving DecidableEq, Repr

inductive FlavorStatus where
  | primitiveCarrier | registeredStatus | skin | coordinate | transport
  | fixedLoad | targetUpdate | burden | failedPrimitive | hostile
  deriving DecidableEq, Repr

structure FlavorArena where
  sm1Arena : SM1.StandardModelArena
  gaugeArena : SM2.GaugeSectorArena
  matterArena : SM3.MatterSectorArena
  ccrArena : SM4.CCRArena
  flavorScope : Type
  primitiveFlavorPackage : Type
  registeredFlavorStatusPackage : Type
  generationGovernancePackage : Type
  dependencyLedger : Type

structure FlavorClaim (Arena : FlavorArena) where
  kind : FlavorClaimKind
  sameScopeFlavor : Prop
  primitiveFlavorStanding : Prop
  descendsToPrimitiveCarrier : Prop
  registeredFlavorStatus : Prop
  fixedLoadEvaluation : Prop
  targetUpdateFlavor : Prop
  burdenFlavor : Prop
  failedPrimitive : Prop
  hostileBranch : Prop

def SameScopeFlavor (x : FlavorClaim Arena) : Prop := x.sameScopeFlavor
def PrimitiveFlavor (x : FlavorClaim Arena) : Prop := x.primitiveFlavorStanding
def FlavorDisposition (x : FlavorClaim Arena) : Prop :=
  x.descendsToPrimitiveCarrier \/ x.registeredFlavorStatus \/ x.fixedLoadEvaluation \/
  x.targetUpdateFlavor \/ x.burdenFlavor \/ x.failedPrimitive \/ x.hostileBranch

structure ChangedFlavorLoad (Arena : FlavorArena) where
  changesPrimitiveLoad : Prop
  certifiedInFixedEnvelope : Prop

def RequiresFlavorTargetUpdate (L : ChangedFlavorLoad Arena) : Prop :=
  L.changesPrimitiveLoad /\ Not L.certifiedInFixedEnvelope

def AdmitsFixedLoadEvaluation (L : ChangedFlavorLoad Arena) : Prop :=
  L.changesPrimitiveLoad /\ L.certifiedInFixedEnvelope

end SM5
