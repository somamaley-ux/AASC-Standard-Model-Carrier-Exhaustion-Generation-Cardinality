namespace SM1

/--
Kernel-preserved claimhood is the upstream AASC condition used by SM-1.
The fields are intentionally classifier-level: SM-1 receives these conditions
from the AASC kernel rather than deriving Standard Model physics from scratch.
-/
structure KernelPreserved (Claim : Type u) where
  targetPreserved : Claim -> Prop
  comparisonClassPreserved : Claim -> Prop
  referenceStanding : Claim -> Prop
  admissibilityPreserved : Claim -> Prop

def NonDegenerateClaim (K : KernelPreserved Claim) (x : Claim) : Prop :=
  K.targetPreserved x /\
  K.comparisonClassPreserved x /\
  K.referenceStanding x /\
  K.admissibilityPreserved x

def PredictionClaim (K : KernelPreserved Claim) (x : Claim) : Prop :=
  K.targetPreserved x /\ K.comparisonClassPreserved x /\ K.referenceStanding x

def FalsificationClaim (K : KernelPreserved Claim) (x : Claim) : Prop :=
  K.targetPreserved x /\ K.comparisonClassPreserved x /\ K.referenceStanding x

theorem prediction_requires_non_degenerate_reference
    {K : KernelPreserved Claim} {x : Claim}
    (h : PredictionClaim K x) :
    K.targetPreserved x /\ K.comparisonClassPreserved x /\ K.referenceStanding x := h

theorem falsification_requires_non_degenerate_reference
    {K : KernelPreserved Claim} {x : Claim}
    (h : FalsificationClaim K x) :
    K.targetPreserved x /\ K.comparisonClassPreserved x /\ K.referenceStanding x := h

structure KernelDenialBurden (Claim : Type u) where
  recoverSameness : Claim -> Prop
  recoverStanding : Claim -> Prop
  recoverReference : Claim -> Prop
  recoverFalsification : Claim -> Prop

def KernelDenialClears (B : KernelDenialBurden Claim) (x : Claim) : Prop :=
  B.recoverSameness x /\ B.recoverStanding x /\ B.recoverReference x /\ B.recoverFalsification x

end SM1
