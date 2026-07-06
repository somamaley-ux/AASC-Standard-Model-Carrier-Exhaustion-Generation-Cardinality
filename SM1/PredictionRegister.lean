import SM1.DependencyLedger

namespace SM1

inductive PredictionClass where
  | classifierPrediction
  | sectorPrediction
  | falsifier
  deriving DecidableEq, Repr

structure PredictionRegisterRow (Arena : StandardModelArena) where
  label : String
  predictionClass : PredictionClass
  claim : ComponentClaim Arena
  expectedClassifierVerdict : SMStatus
  falsifierDescription : String
  sectorStatus : SMSector

structure FalsificationProtocol (Arena : StandardModelArena) where
  targetPreservingFailure : (x : ComponentClaim Arena) -> Prop
  excludesDerivativeStatuses : (x : ComponentClaim Arena) -> Prop
  suppliesPrimitiveCertificate : (x : ComponentClaim Arena) -> Prop

def ClearsFalsificationProtocol
    (P : FalsificationProtocol Arena)
    (x : ComponentClaim Arena) : Prop :=
  P.targetPreservingFailure x /\
  P.excludesDerivativeStatuses x /\
  P.suppliesPrimitiveCertificate x

end SM1
