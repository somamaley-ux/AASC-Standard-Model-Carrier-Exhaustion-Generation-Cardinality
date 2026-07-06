import SM1.KernelStatus

namespace SM1

inductive SMClaimKind where
  | fieldSymbol
  | particleLabel
  | massValue
  | couplingValue
  | matrixEntry
  | gaugeChoice
  | measurement
  | anomaly
  | eftTerm
  | route
  | projection
  | modelName
  | carrierAssertion
  | targetUpdatingDiscovery
  deriving DecidableEq, Repr

inductive SMStatus where
  | carrier
  | licensedRepresentative
  | measurementWitness
  | transportLedger
  | routeStatus
  | mixingStatus
  | projectionDisplay
  | extensionDisposition
  | targetUpdate
  | burden
  | failedPrimitive
  deriving DecidableEq, Repr

inductive SMSector where
  | sm1Classifier
  | sm2Gauge
  | sm3Matter
  | sm4ChargeCouplingRG
  | sm5FlavorMixingGeneration
  | sm6Synthesis
  deriving DecidableEq, Repr

/-- The fixed same-scope arena D_SM received by the classifier paper. -/
structure StandardModelArena where
  structuralTuple : Type
  scope : Type
  invariantBundle : Type
  roleBundle : Type
  boundary : Type
  transportDiscipline : Type
  admissibilityDiscipline : Type

structure ComponentClaim (Arena : StandardModelArena) where
  carrierCandidate : Type
  role : Type
  representative : Type
  measurement : Type
  transport : Type
  route : Type
  projection : Type
  kind : SMClaimKind
  sameScope : Prop
  primitiveStanding : Prop
  carrierCertified : Prop
  derivative : Prop
  burdened : Prop
  targetUpdate : Prop

def FutureSMClaim (Arena : StandardModelArena) :=
  ComponentClaim Arena

def BSMClaim (Arena : StandardModelArena) :=
  ComponentClaim Arena

def SameScopePreserved (x : ComponentClaim Arena) : Prop := x.sameScope
def PrimitiveStanding (x : ComponentClaim Arena) : Prop := x.primitiveStanding
def CarrierCertified (x : ComponentClaim Arena) : Prop := x.carrierCertified
def DerivativeStatus (x : ComponentClaim Arena) : Prop := x.derivative
def BurdenStatus (x : ComponentClaim Arena) : Prop := x.burdened
def TargetUpdateStatus (x : ComponentClaim Arena) : Prop := x.targetUpdate

end SM1
