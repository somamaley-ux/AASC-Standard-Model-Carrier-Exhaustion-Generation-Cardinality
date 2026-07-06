namespace MaleyLean
namespace Papers
namespace FormalizationSmokeTest

/--
A minimal paper-facing system for checking that new formalization modules can
be added, imported, and built in this standalone repository.
-/
structure SmokeSystem (Act : Type) where
  standing : Act -> Prop
  evaluated : Act -> Prop

/--
An act is locally stable when same-act redescriptions preserve its standing
classification.
-/
def LocallyStable {Act : Type} (S : SmokeSystem Act) : Prop :=
  forall a b : Act, a = b -> (S.standing a <-> S.standing b)

/--
A failed evaluated act cannot be repaired by a redescription that is provably
the same act.
-/
def NoSameActRepair {Act : Type} (S : SmokeSystem Act) : Prop :=
  forall a b : Act,
    S.evaluated a ->
    Not (S.standing a) ->
    a = b ->
    Not (S.standing b)

/--
The basic same-act no-repair theorem for the smoke-test paper.
-/
theorem PaperNoSameActRepairStatement
    {Act : Type}
    (S : SmokeSystem Act) :
    NoSameActRepair S := by
  intro a b _h_eval h_not_standing h_same h_standing_b
  exact h_not_standing (h_same ▸ h_standing_b)

/--
Same-act equality is enough to transfer standing both ways.
-/
theorem PaperLocalStabilityStatement
    {Act : Type}
    (S : SmokeSystem Act) :
    LocallyStable S := by
  intro a b h_same
  subst h_same
  exact Iff.rfl

/--
Compact theorem surface for the smoke-test paper.
-/
theorem PaperSmokeTestCoreStatement
    {Act : Type}
    (S : SmokeSystem Act) :
    LocallyStable S /\ NoSameActRepair S := by
  exact And.intro
    (PaperLocalStabilityStatement S)
    (PaperNoSameActRepairStatement S)

end FormalizationSmokeTest
end Papers
end MaleyLean
