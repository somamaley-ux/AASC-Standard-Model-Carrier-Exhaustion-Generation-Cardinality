import SM5

namespace SM6

inductive ConstructorKind where
  | gauge | matter | ccr | flavor | higgs | projection | eft | interface
  | registeredStatus | generationGovernance | measurement | bsm | anomaly
  | targetUpdate | hostile | overlap | residualSurvivor
  deriving DecidableEq, Repr

inductive SM6Status where
  | primitiveCarrier | registeredNonprimitive | governed | burden
  | failedPrimitive | targetUpdate | hostileCertificate | noPromotion
  deriving DecidableEq, Repr

structure StandardModelCarrierArena where
  sm1Arena : SM1.StandardModelArena
  gaugeArena : SM2.GaugeSectorArena
  matterArena : SM3.MatterSectorArena
  ccrArena : SM4.CCRArena
  flavorArena : SM5.FlavorArena
  carrierUniverse : Type
  constructorPartition : Type
  registeredStatusAtlas : Type
  hostileCertificateLedger : Type

structure SM6Claim (Arena : StandardModelCarrierArena) where
  kind : ConstructorKind
  sameScopeSM : Prop
  kernelPreserved : Prop
  primitiveStanding : Prop
  descendsToPrimitiveCarrier : Prop
  registeredNonprimitive : Prop
  generationGoverned : Prop
  counterexampleBurden : Prop
  failedPrimitive : Prop
  targetUpdate : Prop
  hostileCertificate : Prop

def SameScopeSM (x : SM6Claim Arena) : Prop := x.sameScopeSM
def KernelPreserved (x : SM6Claim Arena) : Prop := x.kernelPreserved
def PrimitiveStanding (x : SM6Claim Arena) : Prop := x.primitiveStanding
def RegisteredStatus (x : SM6Claim Arena) : Prop := x.registeredNonprimitive
def GenerationGovernance (x : SM6Claim Arena) : Prop := x.generationGoverned
def CounterexampleBurden (x : SM6Claim Arena) : Prop := x.counterexampleBurden
def FailedPrimitive (x : SM6Claim Arena) : Prop := x.failedPrimitive
def TargetUpdate (x : SM6Claim Arena) : Prop := x.targetUpdate
def HostileCertificateBranch (x : SM6Claim Arena) : Prop := x.hostileCertificate

def SM6Disposition (x : SM6Claim Arena) : Prop :=
  x.descendsToPrimitiveCarrier \/ x.registeredNonprimitive \/ x.generationGoverned \/
  x.counterexampleBurden \/ x.failedPrimitive \/ x.targetUpdate \/ x.hostileCertificate

def PrimitiveSurvivor (x : SM6Claim Arena) : Prop :=
  PrimitiveStanding x /\ SameScopeSM x /\ Not (SM6Disposition x)

structure CrossSectorHostileCertificate (Arena : StandardModelCarrierArena) where
  sameScope : Prop
  defeatsConstructorPartition : Prop
  suppliesPrimitiveWitness : Prop

def ValidHostileCertificate (C : CrossSectorHostileCertificate Arena) : Prop :=
  C.sameScope /\ C.defeatsConstructorPartition /\ C.suppliesPrimitiveWitness

end SM6
