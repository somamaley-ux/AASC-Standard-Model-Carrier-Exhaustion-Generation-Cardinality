import SM2

namespace SM3

inductive MatterClaimKind where
  | spinorField
  | representationLabel
  | chiralLabel
  | quark
  | chargedLepton
  | neutrino
  | massValue
  | yukawaEntry
  | generationLabel
  | detectorTrack
  | oscillationRoute
  | bsmMatterLabel
  | targetUpdatingDiscovery
  deriving DecidableEq, Repr

inductive MatterStatus where
  | closedCarrier
  | representative
  | measurement
  | route
  | projection
  | extension
  | targetUpdate
  | burden
  | failedPrimitive
  deriving DecidableEq, Repr

inductive MatterCarrier where
  | matterRepresentation
  | colorBearingMatter
  | colorlessChargedMatter
  | neutralWeakMatter
  | massResponseSlot
  | neutrinoFlavorRouteInterface
  deriving DecidableEq, Repr

structure MatterSectorArena where
  sm1Arena : SM1.StandardModelArena
  gaugeArena : SM2.GaugeSectorArena
  matterScope : Type
  familyEnvelope : Type
  carrierNetwork : Type
  skinAtlas : Type
  predictionRegister : Type
  dependencyLedger : Type

structure MatterClaim (Arena : MatterSectorArena) where
  kind : MatterClaimKind
  sameScopeMatter : Prop
  primitiveMatterStanding : Prop
  descendsToClosedMatterCarrier : Prop
  registeredDerivative : Prop
  targetUpdateMatter : Prop
  counterexampleBurdenMatter : Prop
  failedPrimitive : Prop
  hostileResidual : Prop

def SameScopeMatter (x : MatterClaim Arena) : Prop := x.sameScopeMatter
def PrimitiveMatter (x : MatterClaim Arena) : Prop := x.primitiveMatterStanding
def DescendsToClosedMatterCarrier (x : MatterClaim Arena) : Prop := x.descendsToClosedMatterCarrier
def RegisteredDerivative (x : MatterClaim Arena) : Prop := x.registeredDerivative
def TargetUpdateMatter (x : MatterClaim Arena) : Prop := x.targetUpdateMatter
def CounterexampleBurdenMatter (x : MatterClaim Arena) : Prop := x.counterexampleBurdenMatter
def FailedPrimitive (x : MatterClaim Arena) : Prop := x.failedPrimitive
def HostileResidual (x : MatterClaim Arena) : Prop := x.hostileResidual

end SM3
