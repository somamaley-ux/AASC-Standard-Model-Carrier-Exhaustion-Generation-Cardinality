# NNR9 MR3 Characteristic Readback Audit

## Target

The algebraic readout witness is:

```lean
MR3CharacteristicPolynomialReadoutWitness M
```

The interpretation proposition is:

```lean
MR3ShapeOutputIsCharacteristicPolynomialInvariant M
```

In the current Lean abstraction this is discharged by the MR3 source being
certified and by the source-induced shape map being available:

```lean
M.sourceCertified /\ M.sourceInducesShapeMap
```

It supports:

```lean
mr3CharacteristicWitnessGivesAlgebraicClassStrengthEvaluator
mr3CharacteristicWitnessGivesAlgebraicClassFrontier
mr3CorpusTheoremsGiveAlgebraicClassFrontier
```

## Required Claim

The MR3 shape output is not merely a generic shape label. It is a certified
characteristic/polynomial invariant class for the neutrino splitting-ratio
target, with same-target readback and no root/value selection.

## Corpus Mapping

| Lean witness field | Corpus support | Role |
| --- | --- | --- |
| `characteristicPolynomialInterpretation` | `AASC-MR3-THM-004`, characteristic-invariant constraint theorem | Licenses determinant/trace/rank/characteristic-polynomial sources only under standing and scale-status control. |
| `standingCarrier` | MR3 source admission rows; `AASC-MR3-THM-004`; `MGN5-DEF-001` | Keeps the polynomial/invariant attached to an admitted mass-response witness, not a fitted matrix texture. |
| `quotientStable` | MR3 source admission rows; `AASC-MR1-LEM-002` | Ensures the readout is invariant under common-scale/quotient presentation. |
| `scaleStatusControlled` | `AASC-MR1-DEF-005`; `AASC-MR1-LEM-002`; MR3 transport closure | Prevents dimensionless ratio notation from becoming automatic exact value. |
| `calibrationFree` | MR3 calibration-free row; `MGN7-THM-001` | Prevents empirical or target-recovering calibration from entering the algebraic class. |
| `noRootSelector` | MR3 extraction/no-hidden-selector row; `MGN5-THM-001` | Blocks selection of a root, fitted texture, or numerical representative. |
| `noEmpiricalFitImport` | MR3 calibration-free row; `MGN5-THM-001`; `MGN7-THM-001` | Keeps the output symbolic/algebraic rather than empirical. |

## Endpoint

If the above fields are supplied, Lean yields:

```lean
HasCurrentRatioEvaluatorAtStrength C .algebraicClass
```

and with expression/exact-value blockers:

```lean
AASCNNR9AlgebraicClassFrontier C
```

## Boundary

This does not compute a numerical value and does not select a polynomial root.
The output is an algebraic/characteristic invariant class for the unique
surviving standing ratio branch. In the present Lean model the class is the MR3
`Shape` output; expanding that object into explicit polynomial syntax is a
separate strengthening task.

## Next Strengthening

The next target after this audit is:

```lean
AASCExplicitPolynomialReadout
```

For the MR3 route specifically, the refined target is:

```lean
MR3ExplicitPolynomialPresentation
```

That object must supply a polynomial type, root-class type, polynomial map,
root-class map, satisfaction relation, and a proof that the current branch
satisfies its polynomial/root-class pair. It must also preserve the same AASC
guards: standing carrier, same-target readback, quotient stability,
scale-status control, calibration freedom, no root selector, and no empirical
fit import.

In the MR3-specialized target the root class is fixed to `M.Shape`, so the
presentation expands the existing MR3 class into polynomial syntax rather than
changing the target.

The next operator-level target is:

```lean
MR3OperatorCharacteristicPolynomialPackage
```

This package must identify the admitted standing operator/carrier, define the
operator-to-characteristic-polynomial map, and prove that the current ratio
satisfies the resulting characteristic class with root class
`M.shapeOfRatio C.ratio`.

## Native Operator Exhaustion Bridge

The corpus also contains fixed-base/operator-exhaustion machinery. In Lean this
is represented on the neutrino side by:

```lean
AASCFixedBaseOperatorAudit
AASCNativeOperatorExhaustionReadoutSupport
NativeOperatorExhaustionCompletesPackage
nativeOperatorExhaustionCompletesOperatorPackagePasses
nativeOperatorExhaustionPackageGivesAlgebraicClassFrontier
```

This bridge is important but deliberately limited. It uses native AASC operator
exhaustion to discharge the operator-readout guardrails:

| Package field | Native operator-exhaustion role |
| --- | --- |
| `operatorAdmitted` | The operator lives on the fixed admitted base. |
| `standingOperatorCarrier` | The operator is attached to the standing carrier, not a new route. |
| `sameTargetReadback` | Fixed-base conservative/endpoint status preserves the ratio target. |
| `quotientStableReadback` | Same-scope operator readback respects quotient presentation. |
| `scaleStatusControlled` | Fixed-base status prevents scale promotion into value selection. |
| `calibrationFreeReadout` | External datum status is inadmissible on the joint restriction. |
| `noRootSelector` | Invariant endpoint status is not a free selector. |
| `noEmpiricalFitImport` | Empirical import is excluded as an external datum. |

It does not by itself define the operator type, the characteristic-polynomial
map, or the characteristic satisfaction relation. Those are exactly the
remaining constructive fields of:

```lean
MR3OperatorCharacteristicPolynomialPackage
```

The package has now been split into two clearer components:

```lean
MR3OperatorCharacteristicConstructiveSyntax
MR3OperatorCharacteristicGuardrails
AASCNativeOperatorExhaustionGuardrailSupport
```

The constructive syntax object is the genuine next mathematical target. It
must provide:

| Constructive syntax field | Meaning |
| --- | --- |
| `Operator` | The admitted operator/carrier universe for the standing branch. |
| `Polynomial` | The characteristic-polynomial or polynomial-invariant universe. |
| `operatorOf` | The assignment from ratio candidates to operators. |
| `characteristicPolynomialOfOperator` | The operator-to-polynomial map. |
| `satisfiesCharacteristicClass` | The relation linking a ratio, polynomial, and MR3 shape/root class. |
| `currentSatisfiesCharacteristicClass` | The proof that the current standing ratio satisfies its characteristic class. |
| `characteristicPolynomialCertified` | Certification that this is a lawful characteristic/polynomial invariant. |
| `sourceShapeIsCharacteristicClass` | Certification that the MR3 shape output is the corresponding characteristic class. |

The guardrail object is where native operator exhaustion acts. Once syntax and
guardrails are both supplied, Lean gives:

```lean
operatorCharacteristicSyntaxAndGuardrailsGiveAlgebraicClassFrontier
```

More sharply, if the guardrails come specifically from the native fixed-base
operator audit, Lean gives:

```lean
nativeOperatorExhaustionGuardrailsAndSyntaxGiveAlgebraicClassFrontier
```

So the current blocker can be stated without ambiguity:

```lean
NeedsMR3OperatorCharacteristicConstructiveSyntax
```

That means the remaining work is not another branch audit and not another
operator-exhaustion argument. It is the construction of the characteristic
syntax object itself.

## Minimal Constructive Syntax Now Available

The first conservative syntax object has been constructed:

```lean
mr3ShapeMapAsConstructiveSyntax
mr3ShapeMapConstructiveSyntaxCertified
mr3ShapeMapAndNativeOperatorExhaustionGiveAlgebraicClassFrontier
```

This construction uses:

| Syntax component | Minimal MR3 realization |
| --- | --- |
| `Operator` | The standing ratio carrier `C.Ratio`. |
| `Polynomial` | The MR3 shape/class output `M.Shape`. |
| `operatorOf` | Identity on ratio candidates. |
| `characteristicPolynomialOfOperator` | The MR3 map `M.shapeOfRatio`. |
| `satisfiesCharacteristicClass` | Equality between the produced shape and the reported MR3 class. |
| `currentSatisfiesCharacteristicClass` | Reflexive satisfaction for `C.ratio`. |

This closes an algebraic/shape-class readout when paired with native operator
exhaustion guardrails and expression/exact-value blockers. It should be stated
honestly: it is a carrier-level MR3 shape-class evaluator, not an explicit
matrix/operator characteristic polynomial and not a numerical value.

The stronger still-open refinement is:

```lean
ExplicitOperatorCharacteristicPolynomialSyntax
```

in prose: replace the minimal carrier-as-operator syntax with a genuine
standing operator universe and a genuine characteristic-polynomial map.

Lean now records that stronger refinement explicitly:

```lean
ExplicitOperatorCharacteristicPolynomialSyntax
ExplicitOperatorCharacteristicPolynomialSyntaxCertified
NeedsExplicitOperatorCharacteristicPolynomialSyntax
explicitOperatorSyntaxAndNativeExhaustionGiveAlgebraicClassFrontier
```

The certification requirements are:

| Stronger syntax gate | Meaning |
| --- | --- |
| `operatorCarrierIsStanding` | The operator universe is the admitted standing operator carrier. |
| `operatorCarrierNotMerelyRatioLabel` | The operator carrier is not just the ratio type renamed. |
| `characteristicPolynomialMapGenuine` | The readout map is a genuine characteristic-polynomial map. |
| `characteristicPolynomialCertified` | The characteristic-polynomial object is AASC certified. |
| `sourceShapeIsCharacteristicClass` | The MR3 shape is the characteristic class of that operator polynomial. |

If those gates are supplied, native operator exhaustion again supplies the
guardrails and Lean derives the algebraic frontier. This is a stronger
provenance path than `mr3ShapeMapAsConstructiveSyntax`, but it is not required
for the already-closed shape-class evaluator.

## Viability Audit for the Stronger Route

A corpus rescan shows that the stronger operator-characteristic route is
plausible but not already completed. Lean now records the support as:

```lean
ExplicitOperatorCharacteristicCorpusSupport
ExplicitOperatorCharacteristicViabilityAudit
explicitOperatorViabilityWithConstructedSyntaxGivesFrontier
```

The support loci are:

| Support field | Corpus locus |
| --- | --- |
| `mr3CharacteristicInvariantGate` | `AASC-MR3-THM-004`, characteristic-invariant constraint theorem. |
| `mgn5MassMatrixEigenstructureVocabulary` | `AASC-MGN5-DEF-5-2`, mass-matrix/eigenstructure numerical occurrence vocabulary. |
| `fixedBaseQuantumOperatorBaseAvailable` | Hardened self-adjoint/operator rows, quantum operator base. |
| `fixedBaseConstraintForOperatorFrameworks` | Hardened self-adjoint/operator row, fixed-base constraint for quantum operator frameworks. |
| `domainExtensionConstraintAvailable` | Hardened self-adjoint/operator row, domain-extension constraint. |
| `friedrichsEndpointCharacterizationAvailable` | Hardened self-adjoint/operator row, Friedrichs endpoint characterization constraint. |
| `endpointBoundaryExactnessControl` | EX6 endpoint/boundary exactness closure and prediction-failure principles. |
| `calibrationAndRawValueFirewall` | EX1/EX5 exactness and de-calibration firewall rows. |
| `noFreeRootOrEndpointSelector` | MR3 no-hidden-selector discipline plus fixed-base endpoint-selection discipline. |

Interpretation: these rows make the stronger construction a legitimate
AASC-native target. They do not yet supply the actual operator universe,
operator assignment, characteristic-polynomial map, or current-branch
satisfaction proof.

## Standing Operator Presentation Target

The stronger construction has now been sharpened to a presentation object:

```lean
NeutrinoStandingOperatorCharacteristicPresentation
NeutrinoStandingOperatorPresentationPasses
NeedsNeutrinoStandingOperatorCharacteristicPresentation
standingOperatorPresentationAndNativeExhaustionGiveAlgebraicClassFrontier
```

This is the object a genuine physics/matrix formalization should inhabit. It
asks for:

| Presentation field | Meaning |
| --- | --- |
| `Operator` | The standing mass/spectral operator carrier. |
| `CharacteristicInvariant` | The characteristic-polynomial-like invariant class. |
| `standingOperatorOf` | Assignment from ratio candidates to standing operators. |
| `characteristicInvariantOf` | Operator-to-characteristic-invariant map. |
| `shapeClassReadback` | Relation between ratio, invariant, and MR3 shape class. |
| `currentReadback` | Proof that the current standing ratio reads back to its MR3 shape. |
| `operatorCarrierIsStanding` | The operator carrier is admitted as standing. |
| `operatorCarrierNotMerelyRatioLabel` | The operator carrier is not just `C.Ratio` renamed. |
| `characteristicInvariantIsPolynomialLike` | The invariant has characteristic-polynomial/eigenstructure status. |
| `characteristicMapGenuine` | The map is genuinely operator-derived. |
| `sameTargetShapeReadback` | Readback is to the same neutrino ratio target. |
| `noRootOrEigenvalueSelector` | No eigenvalue/root representative is selected. |
| `noEmpiricalSpectrumImport` | No observed spectrum or fitted matrix is imported. |
| `characteristicInvariantCertified` | The invariant is certified by the source ledger. |

This is stronger than `mr3ShapeMapAsConstructiveSyntax` because the operator
carrier and characteristic invariant are independent components, not simply the
ratio carrier and MR3 shape map renamed.

## Mass/Spectral Operator Candidate Layer

The next physics-facing witness slot is now:

```lean
NeutrinoMassSpectralOperatorCandidate
NeutrinoMassSpectralOperatorCandidatePasses
NeedsNeutrinoMassSpectralOperatorCandidate
massSpectralOperatorCandidateAndNativeExhaustionGiveAlgebraicClassFrontier
```

This layer is designed for the actual new construction. It asks for a genuine
mass/spectral operator candidate and its characteristic class, with the
following gates:

| Candidate gate | Purpose |
| --- | --- |
| `massOperatorCarrierAdmitted` | The operator carrier is admitted in the AASC ledger. |
| `massOperatorStanding` | The operator carries standing, not just notation. |
| `spectralSourceCompatible` | The operator is compatible with the MR3 spectral source. |
| `characteristicClassPolynomialLike` | The output is characteristic-polynomial/eigenstructure-like. |
| `characteristicClassOperatorDerived` | The class comes from the operator, not from target relabeling. |
| `sameTargetAsStandingRatio` | The readback is to the same neutrino ratio target. |
| `quotientStableReadback` | The readback is quotient-stable. |
| `scaleStatusControlled` | Scale status is controlled. |
| `noFittedMassMatrixImport` | No fitted mass matrix is imported. |
| `noObservedSpectrumImport` | No observed spectrum is imported. |
| `noEigenvalueOrRootSelection` | No eigenvalue/root representative is selected. |
| `notMerelyMR3ShapeRelabel` | The construction is not just the MR3 shape map renamed. |

If this candidate passes, it produces a standing-operator presentation, then
explicit operator syntax, then the stronger algebraic frontier under native
operator exhaustion.

## Three-Flavor Mass-Squared Spectral Data

The candidate has been made still more concrete by introducing:

```lean
ThreeFlavorMassSquaredSpectralOperatorData
ThreeFlavorMassSquaredSpectralOperatorDataPasses
NeedsThreeFlavorMassSquaredSpectralOperatorData
threeFlavorDataAndNativeExhaustionGiveAlgebraicClassFrontier
```

This is the current best landing pad for the new construction. It requires:

| Data field cluster | Meaning |
| --- | --- |
| three mass states | A three-flavor mass-state carrier. |
| mass-squared levels | A mass-squared level assignment. |
| splitting class | A solar/atmospheric splitting-pair class. |
| standing mass operator | A ratio-indexed standing mass/spectral operator. |
| characteristic class | A characteristic-polynomial-like class derived from that operator. |
| MR3 readback | Proof that the current characteristic class reads back to `M.shapeOfRatio C.ratio`. |
| no absolute mass import | The construction uses splitting/ratio structure, not absolute mass scale. |
| no fitted texture/imported spectrum | No fitted mass matrix or observed spectrum enters. |
| no root selection | The output is a class, not a chosen eigenvalue/root. |
| not shape-map relabel | The operator/invariant are independent of merely renaming `M.shapeOfRatio`. |

If such data is supplied and passes, Lean carries it through every later layer:

```text
ThreeFlavorMassSquaredSpectralOperatorData
→ NeutrinoMassSpectralOperatorCandidate
→ NeutrinoStandingOperatorCharacteristicPresentation
→ ExplicitOperatorCharacteristicPolynomialSyntax
→ AASCNNR9AlgebraicClassFrontier
```

## Source-Theorem Interface

The data layer has also been wrapped as a source-theorem interface:

```lean
ThreeFlavorMassSquaredSpectralSourceTheorem
ThreeFlavorMassSquaredSpectralSourceTheoremPasses
NeedsThreeFlavorMassSquaredSpectralSourceTheorem
threeFlavorSourceTheoremAndNativeExhaustionGiveAlgebraicClassFrontier
```

This is the object a new NNR9/NNR10 construction paper should aim to export.
It must supply the carrier/map choices and the proof terms listed in the
three-flavor data audit. Once exported, the existing Lean chain turns it into
the stronger algebraic-class frontier without another branch audit.

For direct formal export, the proof-carrying target is:

```lean
ThreeFlavorMassSquaredSpectralSourceProofBundle
buildThreeFlavorMassSquaredSpectralProofBundle
threeFlavorProofBundleSourceTheoremPasses
NeedsThreeFlavorMassSquaredSpectralProofBundle
threeFlavorProofBundleAndNativeExhaustionGiveAlgebraicClassFrontier
```

This is the cleanest downstream interface: the construction paper supplies one
bundle containing the carriers, maps, readback relation, and proof terms. Lean
then builds the source theorem and derives the frontier automatically.

The constructor `buildThreeFlavorMassSquaredSpectralProofBundle` is deliberately
not a shortcut: every physics/AASC gate must be supplied with a proof term. It
does not fill unresolved gates with `True`.

## Mathlib-Backed Operator Layer

Mathlib has now been added to the project, and the first genuine linear-algebra
layer is formalized in:

```lean
MaleyLean.Papers.Neutrino.SourceTheorems.MathlibSpectralOperator
```

It supplies:

```lean
ThreeFlavorMassSquaredMatrix
diagonalThreeFlavorMassSquaredOperator
threeFlavorCharacteristicPolynomial
diagonalThreeFlavorCharacteristicPolynomial_eq_prod
ThreeFlavorDiagonalMathlibSpectralProofData
threeFlavorDiagonalMathlibDataAndNativeExhaustionGiveAlgebraicClassFrontier
ThreeFlavorMathlibSpectralProofData
threeFlavorMathlibDataAsProofBundle
threeFlavorMathlibDataAndNativeExhaustionGiveAlgebraicClassFrontier
```

The mathematical carrier is now concrete:

```lean
Matrix (Fin 3) (Fin 3) R
Polynomial R
Matrix.diagonal
Matrix.charpoly
```

This is a real upgrade over the abstract socket. The remaining proof terms are
the AASC/physics gates: standing, quotient stability, scale control, no fitted
matrix import, no observed spectrum import, no root selection, and readback to
the MR3 shape class.

For the diagonal three-flavor mass-squared operator, Lean now records the
product-form characteristic polynomial:

```lean
threeFlavorCharacteristicPolynomial
  (diagonalThreeFlavorMassSquaredOperator m2)
= ∏ i : Fin 3, (Polynomial.X - Polynomial.C (m2 i))
```

This keeps the invariant symbolic and class-level: it exposes the three
mass-squared levels as formal diagonal entries without selecting numerical
values, fitted textures, or individual roots.

## Gap-Ratio Algebra

The next bridge is now formalized:

```lean
threeFlavorSolarGap
threeFlavorAtmosphericGap
threeFlavorGapRatio
ThreeFlavorGapRatioAlgebra
gapRatioAlgebraAndNativeExhaustionGiveAlgebraicClassFrontier
```

The symbolic expression is:

```lean
threeFlavorGapRatio m2
= (m2 1 - m2 0) / (m2 2 - m2 0)
```

Lean also proves invariance under common additive shifts and nonzero common
scaling:

```lean
threeFlavorGapRatio_shift
threeFlavorGapRatio_scale
```

So the current readout has moved from an abstract algebraic class to a symbolic
rational gap expression, still without empirical masses, fitted ordering,
absolute scale, or root selection.

Once those constructive fields are supplied, native operator exhaustion plus
the two characteristic syntax facts:

```lean
P.characteristicPolynomialCertified
P.sourceShapeIsCharacteristicClass
```

is enough to obtain:

```lean
AASCNNR9AlgebraicClassFrontier C
```

## Closed-Expression Readout

The gap-ratio algebra now also exports a lawful closed-expression evaluator:

```lean
gapRatioAlgebraAsClosedExpressionSource
gapRatioAlgebraGivesClosedExpressionEvaluator
gapRatioAlgebraSingletonGivesCurrentClosedExpressionEvaluation
gapRatioAlgebraAndExactBlockerGiveClosedExpressionFrontier
```

The expression domain is the coefficient field `R`, and the expression assigned
to the current standing branch is:

```lean
threeFlavorGapRatio A.massSquaredLevelOf
```

Equivalently, in manuscript notation:

```text
rho_current = (m2_1 - m2_0) / (m2_2 - m2_0)
```

This upgrades the endpoint from algebraic-class readout to closed symbolic
expression readout whenever `ThreeFlavorGapRatioAlgebraPasses A` is supplied.
It does not claim an exact numerical value.  The exact-value endpoint remains
blocked unless a separate lawful numerical value map is supplied:

```lean
AASCExactValueReadoutBlocker C
```

Thus the current honest NNR9 endpoint is:

```lean
AASCNNR9ClosedExpressionFrontier C
```

not:

```lean
AASCNNR9ExactValueFrontier C
```

## Exact-Value Map Socket

The lawful numerical-value route is now formalized conditionally:

```lean
ThreeFlavorGapRatioNumericalValueMap
gapRatioNumericalValueMapAsExactConstruction
gapRatioNumericalValueMapAsExactSource
gapRatioNumericalValueMapGivesExactValueEvaluator
gapRatioNumericalValueMapAndSingletonGiveCurrentExactEvaluation
gapRatioNumericalValueMapGivesExactValueFrontier
```

This is not a claim that a numerical value has been derived.  It says exactly
what must be supplied to make that claim:

```lean
Value
valueOfExpression : R -> Value
rawValueUniverseAvailable
exactValueMapAvailable
representativeBranchCollapsedModuloSkin
allUnresolvedFreedomsDischarged
calibrationPrior
transportNeutralOrDischarged
scaleStatusFixed
noHiddenNumericalSelector
noEmpiricalFitImport
```

If those proof fields are supplied, Lean upgrades the endpoint to:

```lean
AASCNNR9ExactValueFrontier C
```

Without that witness, the endpoint remains the closed-expression frontier.

## Internal Gap-Shape Anchor

To avoid a one-anchor empirical import, the exact-value route now has an
internal anchor socket:

```lean
ThreeFlavorInternalGapShapeAnchor
internalGapShapeAnchorValue
internalGapShapeAnchorValue_eq_gapRatio
internalGapShapeAnchorAsNumericalValueMap
internalGapShapeAnchorGivesExactValueEvaluator
internalGapShapeAnchorAndSingletonGiveCurrentExactEvaluation
internalGapShapeAnchorGivesExactValueFrontier
```

This object is the formal target for the next construction step.  It must
derive a canonical ratio from the admitted three-level shape itself and prove:

```lean
canonicalRatio = threeFlavorGapRatio A.massSquaredLevelOf
```

It also carries the non-import gates:

```lean
noOneAnchorImport
noEmpiricalFitImport
noHiddenNumericalSelector
scaleStatusFixed
transportNeutralOrDischarged
allUnresolvedFreedomsDischarged
representativeBranchCollapsedModuloSkin
```

If such an internal shape anchor is supplied, Lean promotes the endpoint to:

```lean
AASCNNR9ExactValueFrontier C
```

The remaining mathematical problem is therefore sharp: construct the internal
gap-shape anchor from AASC/MR3/operator exhaustion, not from observed mass or
gap input.

## Normalized Shape Constructor

The first constructive route to the internal anchor is now formalized:

```lean
ThreeFlavorNormalizedGapShape
normalizedGapShape_ratio_eq_gapRatio
normalizedGapShapeAsInternalAnchor
normalizedGapShapeGivesExactValueEvaluator
normalizedGapShapeAndSingletonGiveCurrentExactEvaluation
normalizedGapShapeGivesExactValueFrontier
```

It requires the admitted three-level mass-squared shape to normalize as:

```lean
A.massSquaredLevelOf 0 = 0
A.massSquaredLevelOf 1 = normalizedRatio
A.massSquaredLevelOf 2 = 1
```

Lean then proves:

```lean
normalizedRatio = threeFlavorGapRatio A.massSquaredLevelOf
```

and the endpoint upgrades to:

```lean
AASCNNR9ExactValueFrontier C
```

provided the same audit object also carries the required non-import gates:
internal shape determination, no one-anchor import, no empirical fit, no hidden
selector, fixed scale status, discharged transport, discharged residual
freedoms, and representative collapse modulo skin.

## Affine-Normalized Shape Constructor

The more realistic invariant constructor is now formalized:

```lean
ThreeFlavorAffineNormalizedGapShape
affineNormalizedGapShape_ratio_eq_gapRatio
affineNormalizedGapShapeAsInternalAnchor
affineNormalizedGapShapeGivesExactValueEvaluator
affineNormalizedGapShapeAndSingletonGiveCurrentExactEvaluation
affineNormalizedGapShapeGivesExactValueFrontier
```

Instead of requiring the admitted levels themselves to be `(0, r, 1)`, this
requires an internally certified affine normalization:

```lean
scale * A.massSquaredLevelOf 0 + shift = 0
scale * A.massSquaredLevelOf 1 + shift = normalizedRatio
scale * A.massSquaredLevelOf 2 + shift = 1
scale != 0
```

Lean then uses the previously proved shift and nonzero-scale invariance of
`threeFlavorGapRatio` to prove:

```lean
normalizedRatio = threeFlavorGapRatio A.massSquaredLevelOf
```

This is the preferred next manuscript target, because it matches the quotient
nature of the ratio: the exact ratio can be fixed by internal relative shape
without fixing an absolute mass or importing an observed gap.

## Canonical Affine Normalization

The affine normalization can now be constructed directly from the gap algebra:

```lean
ThreeFlavorCanonicalAffineNormalizationAudit
canonicalAffineScale
canonicalAffineShift
canonicalAffineScale_ne_zero
canonicalAffine_level0_eq_zero
canonicalAffine_level1_eq_ratio
canonicalAffine_level2_eq_one
canonicalAffineNormalizedGapShape
```

The construction uses:

```lean
scale = (m2_2 - m2_0)^(-1)
shift = -scale * m2_0
normalizedRatio = (m2_1 - m2_0) / (m2_2 - m2_0)
```

Lean proves that this sends the current standing levels to:

```lean
0, normalizedRatio, 1
```

So the affine normalization itself is no longer the blocker.  The remaining
frontier is whether `normalizedRatio` can be identified with a further
internally derived numeral/expression that is not merely the symbolic quotient.

## Closed-Constant and Polynomial Anchor

The next readout socket is now formalized:

```lean
ThreeFlavorInternalClosedRatioConstant
closedRatioConstantAsInternalAnchor
closedRatioConstantGivesExactValueEvaluator
closedRatioConstantGivesExactValueFrontier
```

This is the direct closed-constant route: provide an internally derived
`closedRatio : R` and prove:

```lean
closedRatio = threeFlavorGapRatio A.massSquaredLevelOf
```

There is also a polynomial unique-root route:

```lean
ThreeFlavorInternalPolynomialRatioAnchor
polynomialRatioAnchor_closedRatio_eq_gapRatio
polynomialRatioAnchorAsClosedConstant
polynomialRatioAnchorGivesExactValueEvaluator
polynomialRatioAnchorGivesExactValueFrontier
```

The polynomial route requires:

```lean
polynomial.eval rho = 0
AdmissibleRoot rho
polynomial.eval closedRatio = 0
AdmissibleRoot closedRatio
forall x, polynomial.eval x = 0 -> AdmissibleRoot x -> x = closedRatio
```

where:

```lean
rho = threeFlavorGapRatio A.massSquaredLevelOf
```

Lean then proves:

```lean
closedRatio = rho
```

and promotes the exact-value frontier.  This is the cleanest non-empirical
target for a future construction paper: derive an internal polynomial law and
a unique admissible root, rather than importing a measured value.

## AASC Root-Uniqueness Adapter

The polynomial route is now split into two independently auditable parts:

```lean
AASCAdmissiblePolynomialRootUniquenessCertificate
ThreeFlavorInternalPolynomialRatioLaw
polynomialLawAndAASCUniquenessAsPolynomialAnchor
polynomialLawAndAASCUniquenessGiveExactValueEvaluator
polynomialLawAndAASCUniquenessGiveExactValueFrontier
```

The law object supplies:

```lean
polynomial.eval rho = 0
AdmissibleRoot rho
```

The AASC uniqueness object supplies:

```lean
closedRatio
polynomial.eval closedRatio = 0
AdmissibleRoot closedRatio
forall x, polynomial.eval x = 0 -> AdmissibleRoot x -> x = closedRatio
```

plus the provenance gates:

```lean
uniquenessFromAASC
sameScopeRootPredicate
noExtraRootSelector
```

Together these objects instantiate the earlier polynomial anchor and yield:

```lean
AASCNNR9ExactValueFrontier C
```

This is the intended use of the corpus uniqueness machinery in the evaluator
chain: uniqueness is not hardcoded into the polynomial law; it is imported
through an explicit AASC root-uniqueness certificate.

## Unique-Interior Root Ledger

The AASC uniqueness route now has a native interior-occupancy form:

```lean
AASCPolynomialRootUniqueInteriorLedger
rootUniqueInteriorLedger_uniqueAdmissibleRoot
rootUniqueInteriorLedgerAsUniquenessCertificate
polynomialLawAndRootInteriorLedgerGiveExactValueEvaluator
polynomialLawAndRootInteriorLedgerGiveExactValueFrontier
```

This avoids treating uniqueness as a raw root selector.  The ledger provides:

```lean
RootInterior
rootOfInterior
currentInterior
admissibleRootOccupiesInterior
uniqueAdmissibleInterior
```

Lean then derives:

```lean
forall x, polynomial.eval x = 0 -> AdmissibleRoot x -> x = closedRatio
```

and feeds that derived theorem into the polynomial exact-value route.  This is
the most AASC-native form of the value extraction chain so far:

```text
polynomial law for rho
  + every admissible root occupies the unique interior
  + current interior root is closedRatio
  => closedRatio = rho
  => exact-value frontier
```

## Hybrid-Singleton Root Realization

The value-extraction chain can now reuse the existing NNR8/UEAP branch
singleton directly:

```lean
AASCPolynomialRootHybridSingletonRealization
rootHybridSingletonRealization_uniqueAdmissibleRoot
rootHybridSingletonRealizationAsUniquenessCertificate
polynomialLawAndHybridSingletonRealizationGiveExactValueEvaluator
polynomialLawAndHybridSingletonRealizationGiveExactValueFrontier
```

This adapter requires each admissible polynomial root to be realized by a
same-scope hybrid-joint ratio point:

```lean
rootRatioOf x hx hAdm : C.Ratio
C.inMinimalInterval (rootRatioOf x hx hAdm)
H.modular.ModularRestriction (rootRatioOf x hx hAdm)
H.spectral.spectralRestriction (rootRatioOf x hx hAdm)
H.scoto.scotoRestriction (rootRatioOf x hx hAdm)
valueOfRatio (rootRatioOf x hx hAdm) = x
```

Then the existing:

```lean
HybridJointRestrictionSingleton H
```

forces:

```lean
rootRatioOf x hx hAdm = C.ratio
```

and therefore:

```lean
x = closedRatio
```

This is the tightest bridge so far between the branch-closure theorem and
numerical value extraction.  The remaining construction target is a root
realization theorem: admissible roots of the internal polynomial must be shown
to correspond to same-scope hybrid-joint ratio points.

## Root-Realization Theorem Socket

The root-realization target is now separated into its own construction object:

```lean
AASCPolynomialRootRealizationTheorem
polynomialRootRealizationAsHybridSingletonRealization
polynomialLawAndRootRealizationGiveExactValueEvaluator
polynomialLawAndRootRealizationGiveExactValueFrontier
```

This object must supply a lift from admissible polynomial roots back into the
same-scope ratio domain:

```lean
liftRootToRatio :
  forall x, polynomial.eval x = 0 -> AdmissibleRoot x -> C.Ratio
```

with proof that the lifted ratio is in the hybrid joint restriction and reads
back to the root:

```lean
valueOfRatio (liftRootToRatio x hx hAdm) = x
C.inMinimalInterval (liftRootToRatio x hx hAdm)
H.modular.ModularRestriction (liftRootToRatio x hx hAdm)
H.spectral.spectralRestriction (liftRootToRatio x hx hAdm)
H.scoto.scotoRestriction (liftRootToRatio x hx hAdm)
```

It also carries the audit gates:

```lean
rootRealizationSameScope
rootRealizationExhaustive
rootReadbackLawful
noEmpiricalRootImport
noExtraRootSelector
```

Once this object, the polynomial law, and the already-proved hybrid singleton
are supplied, Lean derives the exact-value frontier.

## Existential Same-Scope Root Predicate

The root-realization target has been weakened to a more paper-friendly form:

```lean
AASCSameScopePolynomialRootPredicateTheorem
sameScopeRootPredicateAsRootRealizationTheorem
polynomialLawAndSameScopeRootPredicateGiveExactValueEvaluator
polynomialLawAndSameScopeRootPredicateGiveExactValueFrontier
```

Instead of supplying an explicit lift function first, the construction paper may
prove:

```lean
forall x, polynomial.eval x = 0 -> AdmissibleRoot x ->
  exists r : C.Ratio,
    C.inMinimalInterval r /\
    H.modular.ModularRestriction r /\
    H.spectral.spectralRestriction r /\
    H.scoto.scotoRestriction r /\
    valueOfRatio r = x
```

Lean then chooses the witness ratio and builds the explicit root-realization
theorem automatically.  So the next target can be stated semantically:
admissible roots are exactly roots that have same-scope hybrid-joint ratio
realizations with lawful readback.

## Definition-Level Same-Scope Root Admissibility

The same-scope root predicate can now be made canonical:

```lean
SameScopeHybridRootRealized
AASCSameScopeRootPredicateDefinition
sameScopeRootPredicateDefinitionAsPredicateTheorem
polynomialLawAndSameScopeRootPredicateDefinitionGiveExactValueEvaluator
polynomialLawAndSameScopeRootPredicateDefinitionGiveExactValueFrontier
```

Here admissibility is defined as:

```lean
SameScopeHybridRootRealized H R valueOfRatio x
```

meaning:

```lean
exists r : C.Ratio,
  C.inMinimalInterval r /\
  H.modular.ModularRestriction r /\
  H.spectral.spectralRestriction r /\
  H.scoto.scotoRestriction r /\
  valueOfRatio r = x
```

With this definition, root realization is automatic.  The construction paper
must still supply the polynomial law and prove the current standing ratio is in
the joint restriction, but it no longer needs a separate lift theorem.

## Same-Scope Polynomial Numerical Prediction Package

The numerical-prediction route is now bundled as a single Lean target:

```lean
AASCSameScopePolynomialNumericalPredictionPackage
sameScopeNumericalPredictionClosedValue
sameScopeNumericalPredictionClosedValue_eq_gapRatio
sameScopeNumericalPredictionExactValueFrontier
sameScopeNumericalPredictionGivesExactValueEvaluator
NeedsSameScopePolynomialNumericalPredictionPackage
```

This is the most rational next endpoint for value extraction.  It packages:

| Package field | Meaning |
| --- | --- |
| `sameScopePredicate` | The canonical same-scope root-admissibility definition. |
| `branchSingleton` | The inherited hybrid joint restriction singleton. |
| `polynomialLaw` | The internal polynomial law showing that the gap ratio is an admissible root. |

Once these are supplied, Lean exposes a closed value:

```lean
sameScopeNumericalPredictionClosedValue P : R
```

and proves:

```lean
sameScopeNumericalPredictionClosedValue P =
  threeFlavorGapRatio A.massSquaredLevelOf
```

It also derives:

```lean
HasCurrentRatioEvaluatorAtStrength C .exactValue
AASCNNR9ExactValueFrontier C
```

This does not manufacture a number.  It identifies the exact remaining
mathematical construction needed for a numerical prediction: build the
same-scope polynomial numerical prediction package, especially its internal
polynomial law.  The branch singleton and same-scope root-realization machinery
are already wired into the package.

## Internal Same-Scope Polynomial Law Constructor

The internal polynomial-law step has now been isolated and constructed as:

```lean
AASCInternalSameScopePolynomialLawAudit
sameScopePredicateClosedRootAsPolynomialLaw
sameScopePredicateClosedRootAsNumericalPredictionPackage
```

This means the law can be produced from four ingredients:

| Ingredient | Role |
| --- | --- |
| `AASCSameScopeRootPredicateDefinition` | Defines admissible roots as same-scope hybrid-joint realized roots. |
| `HybridJointRestrictionSingleton H` | Supplies uniqueness of the same-scope branch. |
| `closedRoot_eq_gapRatio` | The mathematical payload: the closed root equals the internal gap-ratio expression. |
| `AASCInternalSameScopePolynomialLawAudit` | Records non-import, no-selector, calibration, transport, scale, and residual-freedom gates. |

Lean then builds:

```lean
ThreeFlavorInternalPolynomialRatioLaw
```

and packages it into:

```lean
AASCSameScopePolynomialNumericalPredictionPackage
```

So the blocker has narrowed again.  We no longer need an abstract polynomial-law
object from nowhere.  We need the closed-root equality:

```lean
D.closedRatio = threeFlavorGapRatio A.massSquaredLevelOf
```

plus the audit gates certifying that this equality is internally derived rather
than imported from a fitted or empirical value.

## Closed Constant to Same-Scope Polynomial Package

The closed-constant route now feeds the same-scope polynomial route:

```lean
AASCCurrentHybridJointWitness
closedRatioConstantAsSameScopeRootPredicateDefinition
closedRatioConstantAsPolynomialLawAudit
closedRatioConstantAsSameScopeNumericalPredictionPackage
```

This bridge uses the linear polynomial:

```lean
Polynomial.X - Polynomial.C K.closedRatio
```

as a value-polynomial wrapper around an already internally certified closed
constant.  This is deliberately not presented as the final characteristic
polynomial of the neutrino operator.  Its role is narrower: if the corpus has
already supplied an internal closed ratio constant

```lean
K : ThreeFlavorInternalClosedRatioConstant R A
```

and the current ratio is witnessed inside the hybrid joint restriction, then
Lean can package that closed constant as a same-scope polynomial numerical
prediction.

The remaining mathematical payload is therefore one level lower:

```lean
ThreeFlavorInternalClosedRatioConstant R A
```

namely an internally derived `closedRatio` together with:

```lean
closedRatio = threeFlavorGapRatio A.massSquaredLevelOf
```

and the no-import/no-selector exactness audit gates.

## Closed Constant Blocker Cleared by Internal Normalization

The closed-constant object is now constructible from the existing internal
normalization machinery:

```lean
internalGapShapeAnchorAsClosedRatioConstant
canonicalAffineNormalizationAsClosedRatioConstant
canonicalAffineNormalizationAsSameScopeNumericalPredictionPackage
canonicalAffineNormalizationGivesExactValueEvaluator
canonicalAffineNormalizationGivesExactValueFrontier
```

The formal route is:

```text
ThreeFlavorCanonicalAffineNormalizationAudit
  -> ThreeFlavorAffineNormalizedGapShape
  -> ThreeFlavorInternalGapShapeAnchor
  -> ThreeFlavorInternalClosedRatioConstant
  -> AASCSameScopePolynomialNumericalPredictionPackage
  -> AASCNNR9ExactValueFrontier
```

This clears the previous blocker:

```lean
ThreeFlavorInternalClosedRatioConstant R A
```

provided the canonical affine normalization audit and current hybrid-joint
witness are supplied.  The exact readout is lawful because the closed ratio is
derived internally from the affine-normalized three-level shape and Lean proves
that it equals:

```lean
threeFlavorGapRatio A.massSquaredLevelOf
```

This should still be stated with care.  The endpoint is an exact evaluator in
the coefficient field `R`, not yet a concrete decimal or named algebraic
number.  To obtain a displayed numerical prediction, the next theorem must
identify the canonical affine normalized ratio with a specific closed numeral,
closed expression, or algebraic root representation.

## Displayed Value Presentation Layer

The final readout gap is now named as a presentation problem:

```lean
ThreeFlavorDisplayedRatioPresentation
displayedRatioPresentationAsClosedRatioConstant
displayedRatioPresentationAsNumericalPredictionPackage
displayedRatioPresentationGivesExactValueFrontier
NeedsThreeFlavorDisplayedRatioPresentation
```

This object separates the semantic exact value from its reportable form.  It
requires:

| Field | Meaning |
| --- | --- |
| `Presentation` | The syntax/type of the displayed value, such as a numeral, expression, or algebraic-root certificate. |
| `displayed` | The actual displayed object. |
| `denote` | The denotation map into the coefficient field `R`. |
| `displayed_denotes_gapRatio` | Proof that the displayed object denotes the canonical gap ratio. |
| audit gates | Internal derivation, no one-anchor import, no hidden selector, no empirical/fitted import, fixed scale, discharged transport and residual freedoms. |

Once this presentation is supplied, Lean converts it to:

```lean
ThreeFlavorInternalClosedRatioConstant R A
```

and then through the already-built chain to:

```lean
AASCNNR9ExactValueFrontier C
```

Thus the current best next theorem target is not another singleton theorem. It
is:

```lean
ThreeFlavorDisplayedRatioPresentation R A
```

In plain terms: produce the actual reportable expression, numeral, or algebraic
root certificate, and prove that its denotation is the internally normalized
three-flavor gap ratio.

## Concrete Displayed-Value Routes

The abstract displayed presentation now has two concrete subroutes.

Algebraic-root route:

```lean
ThreeFlavorAlgebraicRootDisplayedPresentation
AlgebraicRootPresentationSyntax
algebraicRootDisplayedPresentationAsDisplayed
algebraicRootDisplayedPresentationGivesExactValueFrontier
NeedsThreeFlavorAlgebraicRootDisplayedPresentation
```

This route asks for a polynomial, a distinguished root, proof that the root is
a root, and proof that the root denotes the canonical gap ratio:

```lean
root_eq_gapRatio :
  root = threeFlavorGapRatio A.massSquaredLevelOf
```

It also carries root-class certification and uniqueness-in-admissible-class
gates, so the root is not a hidden selector.

Closed-expression route:

```lean
ThreeFlavorClosedExpressionDisplayedPresentation
closedExpressionDisplayedPresentationAsDisplayed
closedExpressionDisplayedPresentationGivesExactValueFrontier
NeedsThreeFlavorClosedExpressionDisplayedPresentation
```

This route asks for a closed expression syntax, its denotation map, and proof
that the expression denotes the canonical gap ratio:

```lean
expression_denotes_gapRatio :
  denoteExpression expression = threeFlavorGapRatio A.massSquaredLevelOf
```

It also carries expression-normal-form certification, so the displayed
expression is not merely a relabeling of the target value.

The two honest next targets are therefore:

```lean
ThreeFlavorAlgebraicRootDisplayedPresentation R A
```

or:

```lean
ThreeFlavorClosedExpressionDisplayedPresentation R A
```

The algebraic route is likely better if AASC/operator exhaustion yields a
unique admissible root.  The closed-expression route is better if the corpus can
derive a canonical symbolic formula directly.

## Canonical Interior-Ratio Law Target

The missing internal anchor is now named directly:

```lean
ThreeFlavorCanonicalInteriorRatioLaw
canonicalInteriorRatioLawAsAlgebraicRootPresentation
canonicalInteriorRatioLawGivesExactValueFrontier
NeedsThreeFlavorCanonicalInteriorRatioLaw
```

This is the theorem a modular fixed-point argument, flavor-symmetry sum rule,
or AASC-native role-occupancy/endpoint argument must supply.  It requires:

| Field | Meaning |
| --- | --- |
| `polynomial` | The internally derived polynomial law for the normalized interior coordinate. |
| `canonicalRoot` | The distinguished internally derived root. |
| `canonicalRoot_is_root` | The root satisfies the polynomial. |
| `canonicalRoot_eq_gapRatio` | The root is the three-flavor gap ratio. |
| `sourceKind` / `source` | The provenance of the law, such as modular fixed point, flavor symmetry, or AASC occupancy. |
| `rootUniqueInAdmissibleClass` | No second admissible root survives. |
| `sameScopeInteriorLaw` | The law applies to the same normalized neutrino ratio target. |
| `notEmpiricalFit`, `notParameterTuning`, `noHiddenRootSelector` | The value is not fitted, tuned, or selected by hand. |

Once supplied, Lean converts it into:

```lean
ThreeFlavorAlgebraicRootDisplayedPresentation R A
```

and then to:

```lean
AASCNNR9ExactValueFrontier C
```

This is the most precise current anchor target.  It does not assert that such a
law has already been found; it states exactly what must be proved to collapse
the symbolic middle coordinate to a named algebraic/root value.

## Nontrivial Internal Coordinate Anchor

The canonical interior-ratio law now has a stricter source object:

```lean
AASCInteriorAnchorSourceKind
ThreeFlavorInternalCoordinateAnchor
internalCoordinateAnchorAsCanonicalInteriorRatioLaw
internalCoordinateAnchorGivesExactValueFrontier
NeedsThreeFlavorInternalCoordinateAnchor
```

This is the object that actually fixes the normalized middle coordinate.  It is
stronger than the symbolic quotient and stronger than branch singleton closure.
It requires:

| Field | Meaning |
| --- | --- |
| `kind` | Provenance family: modular fixed point, flavor sum rule, role-occupancy endpoint, operator spectral invariant, quotient normal form, or another AASC source. |
| `polynomial` | The source-derived polynomial for the interior coordinate. |
| `root` | The source-derived canonical root. |
| `root_is_root` | The root satisfies the polynomial. |
| `root_eq_gapRatio` | The root equals the three-flavor gap ratio. |
| `notDefinedByGapQuotient` | Blocks the vacuous move of defining the anchor to be the quotient itself. |
| `rootUniqueInAdmissibleClass` | Ensures the root is not a hidden selector. |
| `noEmpiricalFitImport`, `noParameterTuning`, `noOneAnchorImport` | Keeps the anchor internal rather than fitted or imported. |

Once this object is supplied, Lean derives:

```lean
ThreeFlavorCanonicalInteriorRatioLaw R A
AASCNNR9ExactValueFrontier C
```

So the true remaining construction is:

```lean
ThreeFlavorInternalCoordinateAnchor R A
```

That is the clean target for corpus work or a new theorem: find an internal
source that gives a polynomial and canonical root, and prove that root is the
normalized neutrino splitting ratio without defining it by the quotient.

The current source scan is recorded separately in:

```text
NNR9_Coordinate_Anchor_Search_Audit.md
```

That audit did not find an already-admitted coordinate anchor in the present
corpus scan.  It did find strong guardrails against fake anchors and identifies
the best positive source families to develop next.

## Canonical Gap-Quotient Formula

The closed-expression route now has a concrete displayed formula:

```lean
ThreeFlavorGapQuotientExpression
ThreeFlavorGapQuotientExpression.denote
canonicalGapQuotientExpression
canonicalGapQuotientExpression_denotes_gapRatio
gapQuotientExpressionAsClosedExpressionDisplayedPresentation
gapQuotientExpressionGivesExactValueFrontier
```

The displayed syntax is the three-level quotient:

```text
(m2_1 - m2_0) / (m2_2 - m2_0)
```

Lean proves that its denotation is exactly:

```lean
threeFlavorGapRatio A.massSquaredLevelOf
```

This is a meaningful endpoint upgrade: the reportable value is now a concrete
closed expression, not merely an abstract element of the coefficient field.
It remains non-numerical in the decimal/algebraic-constant sense.  A further
theorem would still be required to identify this expression with a named
number or unique algebraic root independent of the three symbolic levels.
