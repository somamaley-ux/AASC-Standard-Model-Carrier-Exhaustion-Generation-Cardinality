import SM1

namespace SM2

inductive GaugeClaimKind where
  | gaugePotential
  | transitionFunction
  | connectionTransport
  | curvatureHolonomy
  | photon
  | gluon
  | weakBoson
  | chargeNumber
  | couplingValue
  | anomaly
  | eftDisplay
  | bsmGaugeLabel
  | targetUpdatingDiscovery
  deriving DecidableEq, Repr

inductive GaugeStatus where
  | closedCarrier
  | licensedRepresentative
  | transportLedger
  | routeStatus
  | projectionDisplay
  | targetUpdate
  | burden
  | failedPrimitive
  deriving DecidableEq, Repr

inductive GaugeCarrier where
  | gaugeOrder
  | transport
  | curvatureHolonomy
  | chargeResponse
  | colorTransport
  | weakChiral
  | anomaly
  | gaugeVacuum
  deriving DecidableEq, Repr

structure GaugeSectorArena where
  sm1Arena : SM1.StandardModelArena
  gaugeScope : Type
  carrierNetwork : Type
  skinAtlas : Type
  predictionRegister : Type
  dependencyLedger : Type

structure GaugeClaim (Arena : GaugeSectorArena) where
  kind : GaugeClaimKind
  sameScopeGauge : Prop
  primitiveGaugeStanding : Prop
  descendsToClosedGaugeCarrier : Prop
  registeredDerivative : Prop
  targetUpdateGauge : Prop
  counterexampleBurdenGauge : Prop
  failedPrimitive : Prop

def SameScopeGauge (x : GaugeClaim Arena) : Prop := x.sameScopeGauge
def PrimitiveGauge (x : GaugeClaim Arena) : Prop := x.primitiveGaugeStanding
def DescendsToClosedGaugeCarrier (x : GaugeClaim Arena) : Prop := x.descendsToClosedGaugeCarrier
def RegisteredDerivative (x : GaugeClaim Arena) : Prop := x.registeredDerivative
def TargetUpdateGauge (x : GaugeClaim Arena) : Prop := x.targetUpdateGauge
def CounterexampleBurdenGauge (x : GaugeClaim Arena) : Prop := x.counterexampleBurdenGauge
def FailedPrimitive (x : GaugeClaim Arena) : Prop := x.failedPrimitive

end SM2
