# NNR9 Evaluation Frontier

## Current Readout Status

This file began as the post-singleton evaluation frontier.  The early sections
below are retained as a record of the blocker that existed before the readout
pipeline was inhabited.

The current endpoint is stronger:

```text
AASC standing source-row admission
  -> same-scope NNR9 numerical readout
  -> rational windows for rho, R31, and R3ell
  -> one-anchor atmospheric-gap mass display when an external gap anchor is admitted
```

The current ratio readout is:

```text
rho_nu = 0.0299486814926011...
R31    = 33.3904516045907...
R3ell  = 32.8904516045907...
```

For a worked metric display, the draft uses the external normal-ordering
atmospheric-gap anchor

```text
Delta m^2_31 = 2.513e-3 eV^2
```

cited from:

```text
Esteban, Gonzalez-Garcia, Maltoni, Martinez-Soler, Pinheiro, Schwetz,
"NuFit-6.0: updated global analysis of three-flavor neutrino oscillations",
JHEP 2024, 216 (2024), DOI: 10.1007/JHEP12(2024)216.
NuFIT v6.0 results page: https://www.nu-fit.org/?q=node/294
```

Together with the AASC projective levels

```text
L1 = 1.0120134524368151586
L3 = 159.3652713329476282194
L5 = 5288.4988071409118531250
```

this gives the display

```text
m1 = 0.000693529181010968 eV
m2 = 0.00870298910236135  eV
m3 = 0.0501346285787071   eV
sum m_i = 0.0595311468620794 eV
```

This is a one-anchor display theorem, not an AASC zero-anchor derivation of
absolute mass.  The anchor source belongs in the provenance layer; the AASC
contribution is the same-scope readout, source-row admission, audit guarding,
and Lean-checked transport from the ratio to the anchored spectrum.

## Current Classification

The UEAP singleton endpoint changes the problem from branch selection to branch
evaluation:

```text
B_rho_adm = { rho_nu_current }
```

In the current Lean formalization, `rho_nu_current` is represented by
`C.ratio : C.Ratio`, where `C.Ratio` is an abstract type in
`StandingRatioCertificate`. It carries no built-in real, rational, algebraic,
finite, or computable projection.

Therefore the current survivor is opaque at numerical readout strength unless
a lawful evaluator is added.

## New Blocker

The old broad blocker:

```text
NoAdmissibleMagnitudeCompressingLaw
```

has been superseded for branch selection by UEAP singleton closure. The new
post-singleton blocker is:

```lean
NoNumericalEvaluatorForCurrentStandingBranch C
```

equivalently:

```lean
CurrentStandingRatioOpaqueToNumericReadout C
```

## New Lean Module

The NNR9 scaffold is implemented in:

```text
MaleyLean/Papers/Neutrino/SourceTheorems/EvaluationFrontier.lean
```

It introduces:

```lean
CanonicalEvaluatorForCurrentStandingRatio
CurrentStandingRatioEvaluation
HasCurrentRatioEvaluatorAtStrength
NoCurrentRatioEvaluatorAtStrength
AASCReadoutSourceAudit
ReadoutSourceAuditPasses
AASCReadoutProjection
NoNumericalEvaluatorForCurrentStandingBranch
CurrentStandingRatioOpaqueToNumericReadout
```

It also connects the existing normal-form route:

```lean
normalFormSourceAsCurrentEvaluator
singletonWithNormalFormSourceGivesCurrentEvaluation
normalFormSourceGivesNormalFormStrengthEvaluator
```

and the existing finite residual-output route:

```lean
finiteSourceAsCurrentEvaluator
finiteSourceCurrentEvaluatorAdmissible
singletonWithFiniteSourceGivesCurrentEvaluation
finiteSourceCurrentEvaluationSuppliesResidualOutput
finiteSourceGivesFiniteClassStrengthEvaluator
```

The finite route is an evaluator at `finiteClass` strength. It is stronger than
an unevaluated branch singleton, but it is still not a numerical value theorem.

The module also defines the stronger source-theorem slots:

```lean
AASCAlgebraicRatioClassSourceTheorem
AASCClosedExpressionRatioSourceTheorem
AASCExactRatioValueSourceTheorem
```

with corresponding evaluator theorems:

```lean
algebraicSourceGivesAlgebraicClassStrengthEvaluator
closedExpressionSourceGivesClosedExpressionStrengthEvaluator
exactValueSourceGivesExactValueStrengthEvaluator
```

These are theorem targets, not yet inhabited by the present corpus scan.

The module also includes the safe downgrade/projection adapter:

```lean
evaluatorProjectionGivesTargetStrengthEvaluator
```

This prevents an exact, expression, or algebraic readout from being silently
relabelled as a weaker output. A projection to the weaker output domain must
itself pass the readout audit.

It also includes explicit non-promotion blocker interfaces:

```lean
AASCExactValueReadoutBlocker
AASCClosedExpressionReadoutBlocker
AASCAlgebraicClassReadoutBlocker
```

and theorem names such as:

```lean
finiteReadoutDoesNotPromoteToExactValue
normalFormReadoutDoesNotPromoteToExactValue
algebraicReadoutDoesNotPromoteToExactValue
expressionReadoutDoesNotPromoteToExactValue
finiteReadoutDoesNotPromoteToClosedExpression
normalFormReadoutDoesNotPromoteToClosedExpression
algebraicReadoutDoesNotPromoteToClosedExpression
finiteReadoutDoesNotPromoteToAlgebraicClass
normalFormReadoutDoesNotPromoteToAlgebraicClass
```

These are not negative discoveries by themselves; they are the formal shape of
the audit result once the manuscript/corpus supplies the relevant no-promotion
ledger.

Finally, the module packages the possible NNR9 endpoint states:

```lean
AASCNNR9NormalFormFrontier
AASCNNR9FiniteClassFrontier
AASCNNR9AlgebraicClassFrontier
AASCNNR9ClosedExpressionFrontier
AASCNNR9ExactValueFrontier
```

with constructors:

```lean
normalFormSourceAndBlockersGiveNormalFormFrontier
finiteSourceAndBlockersGiveFiniteClassFrontier
algebraicSourceAndBlockersGiveAlgebraicClassFrontier
closedExpressionSourceAndBlockerGiveClosedExpressionFrontier
exactValueSourceGivesExactValueFrontier
```

These are the clean manuscript endpoints: each one states the strongest
available readout and, where relevant, the stronger readouts that remain
blocked.

## Algebraic And Exact Tracks

The two deeper tracks now have separate construction interfaces.

For algebraic readout:

```lean
AASCAlgebraicReadoutRequirements
AASCAlgebraicReadoutConstruction
algebraicConstructionAsSourceTheorem
algebraicConstructionGivesAlgebraicClassFrontier
```

The focused MR3-style target is:

```lean
AASCCharacteristicPolynomialReadout
CharacteristicPolynomialReadoutPasses
characteristicPolynomialReadoutGivesAlgebraicClassStrengthEvaluator
characteristicPolynomialReadoutGivesAlgebraicClassFrontier
NeedsCharacteristicPolynomialReadout
```

This is now the cleanest next object to inhabit. It represents a certified
standing characteristic/polynomial invariant class for the current neutrino
ratio target, with readback but without root selection.

This route requires:

```text
characteristic/polynomial invariant
standing carrier for that invariant
same-target ratio readback
quotient-stable readback
scale-status control
calibration-free readout
no root selector
no empirical fit import
```

The corpus scan makes this the plausible next positive target: MR1 supplies
ratio-invariance and scale-status guardrails, while MR3 supplies
characteristic-invariant discipline. What is not yet supplied is the actual
admitted algebraic output map for the current neutrino branch.

In Lean terms, the missing positive witness is:

```lean
exists P : AASCCharacteristicPolynomialReadout C,
  CharacteristicPolynomialReadoutPasses P
```

The MR3 adapter now isolates this further:

```lean
MR3CharacteristicPolynomialReadoutWitness
mr3CharacteristicWitnessAsReadout
mr3CharacteristicWitnessReadoutPasses
mr3CharacteristicWitnessGivesAlgebraicClassStrengthEvaluator
mr3CharacteristicWitnessGivesAlgebraicClassFrontier
mr3CorpusTheoremsAsCharacteristicWitness
mr3CorpusTheoremsGiveCharacteristicInterpretation
mr3CorpusCharacteristicInterpretationGivesAlgebraicClassFrontier
mr3CorpusTheoremsGiveAlgebraicClassFrontier
```

MR3 already supplies the shape map and most guardrails. The remaining
paper-level assertion is that the MR3 shape output is being used as a certified
characteristic/polynomial invariant class for the ratio target, rather than as a
generic shape label.

In the current Lean abstraction, that interpretation proposition is:

```lean
MR3ShapeOutputIsCharacteristicPolynomialInvariant M
```

and it is discharged from:

```lean
T.sourceCertified
T.sourceInducesShapeMap
```

for `T : MR3CorpusTheorems M`. This keeps the algebraic endpoint at the
MR3-shape/class level; it does not expand the class into explicit polynomial
syntax or select a root.

## Next Blocker: Explicit Polynomial Syntax

After the MR3 algebraic-class frontier, the next strengthening is not yet a
value. It is an explicit polynomial/readout object:

```lean
AASCExplicitPolynomialReadout
ExplicitPolynomialReadoutPasses
explicitPolynomialReadoutGivesAlgebraicClassFrontier
NeedsExplicitPolynomialSyntax
```

This layer requires:

```text
Polynomial type
RootClass type
polynomialOf : C.Ratio -> Polynomial
rootClassOf : C.Ratio -> RootClass
satisfaction relation
current branch satisfies its polynomial/root-class pair
standing-carrier derivation
same-target readback
quotient stability
scale-status control
calibration freedom
no root selector
no empirical fit import
```

This is stronger than the current MR3 `Shape` abstraction because it exposes
the algebraic syntax and satisfaction relation. It is still weaker than a
closed expression or exact value because it does not select a root.

The MR3-specialized version is:

```lean
MR3ExplicitPolynomialPresentation
MR3ExplicitPolynomialPresentationPasses
mr3ExplicitPolynomialPresentationAsReadout
mr3ExplicitPolynomialPresentationGivesAlgebraicClassFrontier
NeedsMR3ExplicitPolynomialPresentation
```

This version keeps the root class equal to `M.Shape`, so the explicit
polynomial syntax refines the existing MR3 algebraic class instead of swapping
in an unrelated algebraic target.

The next refinement identifies where the polynomial comes from:

```lean
MR3OperatorCharacteristicPolynomialPackage
MR3OperatorCharacteristicPackagePasses
operatorCharacteristicPackageAsMR3PolynomialPresentation
operatorCharacteristicPackageGivesAlgebraicClassFrontier
NeedsOperatorCharacteristicPolynomialPackage
```

This requires an admitted standing operator/carrier object, an operator-to-
characteristic-polynomial map, and a proof that the current ratio satisfies the
resulting characteristic class with root class `M.shapeOfRatio C.ratio`.

For exact-value readout:

```lean
AASCExactValueReadoutRequirements
AASCExactValueReadoutConstruction
exactValueConstructionAsSourceTheorem
exactValueConstructionGivesExactValueFrontier
```

This route requires:

```text
raw value universe
exact value map
representative branch collapse modulo skin
all unresolved freedoms discharged
calibration priority
transport neutrality or discharge
scale status fixed
no hidden numerical selector
no empirical fit import
```

The corpus scan supports the blocker here. EX1/EX2 rows repeatedly state that
quotient singleton, finite collapse, notation, dimensionless form, solver
existence, and approximate/empirical agreement do not promote to raw exactness.
Exact value therefore remains blocked unless the exact-value requirement bundle
is constructed.

The combined assessment object is:

```lean
AASCAlgebraicAndExactReadoutAssessment
```

with:

```lean
assessmentBlocksExactValueFrontier
```

So the current deeper status is:

```text
algebraic-class readout: live construction target
exact-value readout: blocked until raw-value exactness requirements are met
```

## Evaluation Target

The next theorem target should be:

```text
Current Standing Ratio Evaluation Theorem
```

or, more explicitly:

```text
Singleton-to-Value Extraction Theorem
```

The required new object is a lawful evaluator:

```lean
CanonicalEvaluatorForCurrentStandingRatio C
```

with admissibility:

```lean
CanonicalEvaluatorAdmissible E
```

## Possible Output Strengths

| Evaluator output | Endpoint |
| --- | --- |
| exact real/rational value | `RatioValueLocked` |
| closed expression | `RatioExpressionLocked` |
| polynomial/algebraic relation | `AlgebraicRatioClassLocked` |
| finite root/output class | `FiniteRatioClassLocked` |
| proper subinterval | `NontrivialRatioIntervalLocked` |
| normal form only | `CurrentStandingRatioEvaluation` at `normalFormOnly` strength |
| no evaluator | `BranchSingletonNotNumericallyEvaluated` |

## Strongest Honest Next Step

The current formal upgrade is:

```text
singleton + audited finite source -> finite-class current evaluation
singleton + audited normal-form source -> normal-form current evaluation
```

In Lean theorem form:

```lean
finiteSourceGivesFiniteClassStrengthEvaluator
normalFormSourceGivesNormalFormStrengthEvaluator
```

The strongest still-open upgrade is one of:

```lean
AASCAlgebraicRatioClassSourceTheorem C
AASCClosedExpressionRatioSourceTheorem C
AASCExactRatioValueSourceTheorem C
```

Supplying any one of those, together with its audit pass, immediately gives the
matching evaluator-strength theorem. The present work has built the lawful
readout slots; it has not yet supplied an inhabited algebraic, expression, or
exact-value source theorem.

If a future stronger readout needs to be reported in a weaker domain, the
required additional object is:

```lean
AASCReadoutProjection
```

with:

```lean
ReadoutSourceAuditPasses projection.audit
```

If a weaker readout is all that is available, promotion to a stronger endpoint
requires a source theorem or projection. Otherwise the corresponding
`AASC...ReadoutBlocker` keeps the endpoint at its actual strength.

If no such evaluator can be constructed, the correct NNR9 endpoint is:

```text
Branch singleton locked; current standing ratio not numerically evaluated.
```

## Build Status

Verified locally:

```text
lake build MaleyLean.Papers.Neutrino
```

completed successfully with 95 jobs after adding the NNR9 evaluation frontier.
