# NNR9 Coordinate Anchor Search Audit

## Current Endpoint

This audit is now partly historical.  The original search target was a
coordinate-independent internal anchor for the unique branch.  The current
NNR9 endpoint has moved one step further: the readout is expressed through an
AASC standing-admission certificate, not through a bare import and not through
an external-paper proof authority.

Current Lean endpoint:

```lean
AASCNeutrinoSourceRowStandingAdmission.finalNumericalReadout
```

Current dependency shape:

```text
AASCNeutrinoSourceRowStandingAdmission
  -> AASCNeutrinoReadoutSameScopeAdmissionRows
  -> AASCNeutrinoNumericalReadoutCertificate
  -> rational decimal windows for rho, R31, and R3ell
```

The Pajuhaan/Zenodo material has the limited role of cited provenance and
source-row data.  The AASC work is the structural admission, same-scope
transport, singleton/readout machinery, audit guarding, and Lean-checked
window proof.  In manuscript-facing language, the source import should be
described as an admitted row-data source, not as the derivation itself.

The certified windows currently exposed by Lean are:

```text
0.0299486814926010 <= rho_current <= 0.0299486814926012
33.3904516045907 <= rho_current^{-1} <= 33.3904516045908
32.8904516045907 <= rho_current^{-1} - 1/2 <= 32.8904516045908
```

Build status:

```text
lake build MaleyLean.Papers.Neutrino: passes.
No sorry/admit/axiom/unsafe token occurs in MathlibSpectralOperator.lean.
Only the pre-existing `simp`/`simpa` linter warning remains.
```

## One-Anchor Continuation

The charged-lepton one-anchor symmetry is now represented on the neutrino side
without overclaiming absolute masses from the ratio alone.

Lean records the ratio-only residual family:

```text
m1^2 = t
m2^2 = t + rho D
m3^2 = t + D
```

and proves:

```lean
threeFlavorRatioOffsetGapFamily_gapRatio
threeFlavorRatioOffsetGapFamily_offsetInvariant
```

So changing the offset `t` does not change the NNR9 ratio readout.  This is
the guardrail: the ratio anchor is real, but it is not an absolute mass anchor.

The MR6-style positive continuation is:

```lean
ThreeFlavorProjectiveMassSquaredShape
ThreeFlavorOneAnchorMassSquaredDisplayAnchor
aascNeutrinoSourceProjectiveShapeLevel
aascNeutrinoSourceProjectiveMassSquaredShape
aascNeutrinoSourceProjectiveMassSquaredShape_gapRatio_eq_source
AASCNeutrinoOneAnchorMetricInput
AASCNeutrinoOneAnchorMetricInput.toDisplayAnchor
aascNeutrinoOneAnchorSpectrumReconstruction
aascNeutrinoNNR10OneAnchorMassSpectrumDisplay
aascNeutrinoOneAnchorSpectrum_gapRatio_eq_NNR9GapRatio
aascNeutrinoOneAnchorSpectrum_gapRatio_eq_selectedRoot
aascNeutrinoOneAnchorSpectrum_anchorLevel_eq_anchorValue
AASCNeutrinoOneAnchorAbsoluteMassSquaredSpectrumAvailable
aascNeutrinoOneAnchorMetricInput_discharge_absoluteSpectrumNeed
AASCNeutrinoAtmosphericGapMetricAnchor
aascNeutrinoAtmosphericGapScale
aascNeutrinoAtmosphericGapAnchoredMassSquared
aascNeutrinoAtmosphericGapAnchored_atmosphericGap_eq_anchor
aascNeutrinoAtmosphericGapAnchored_gapRatio_eq_selectedRoot
AASCNeutrinoAtmosphericGapAnchoredSpectrumAvailable
aascNeutrinoAtmosphericGapMetricAnchor_discharge_spectrumNeed
threeFlavorOneAnchorReconstructedMassSquared
threeFlavorOneAnchorReconstructed_anchor_eq
threeFlavorOneAnchorReconstructed_gapRatio_eq_shape
ThreeFlavorOneAnchorNeutrinoSpectrumReconstruction
AASCNNR10OneAnchorNeutrinoMassSpectrumDisplay
```

This says: the AASC-admitted NNR9 source rows instantiate the projective
mass-squared shape; one target-aligned metric anchor then reconstructs an
absolute mass-squared triple, preserves the NNR9 selected root as the gap
ratio, and sets the anchored component equal to the admitted anchor value.  It
is a lawful display theorem, not a zero-anchor derivation of absolute neutrino
masses.

The preferred neutrino scale-anchor specialization is now also formalized:
an admitted atmospheric mass-squared gap anchor \(\Delta m^2_{31}\) defines
the scale

```text
lambda = Delta m^2_31 / (L5 - L1)
```

and constructs

```text
m_i^2 = lambda L_i.
```

Lean proves that the reconstructed atmospheric gap equals the admitted anchor
and that the reconstructed spectrum's gap ratio remains the NNR9 selected root.

### Worked atmospheric-gap display

For a concrete metric display, take the normal-ordering atmospheric-gap anchor

```text
Delta m^2_31 = 2.513e-3 eV^2.
```

This anchor is external.  It is cited from the NuFIT three-flavor oscillation
fit convention/value, not derived internally by AASC.  The source used in the
draft is:

```text
I. Esteban, M. C. Gonzalez-Garcia, M. Maltoni, I. Martinez-Soler,
J. P. Pinheiro, and T. Schwetz,
"NuFit-6.0: updated global analysis of three-flavor neutrino oscillations",
JHEP 2024, 216 (2024).
DOI: 10.1007/JHEP12(2024)216
NuFIT v6.0 results page: https://www.nu-fit.org/?q=node/294
```

Using the AASC source-row projective levels

```text
L1 = 1.0120134524368151586
L3 = 159.3652713329476282194
L5 = 5288.4988071409118531250
```

the one-anchor scale is

```text
lambda = Delta m^2_31 / (L5 - L1)
       = 4.75273054676883e-7.
```

The anchored display

```text
m_i^2 = lambda L_i
```

therefore gives

```text
m1 = 0.000693529181010968 eV = 0.693529181010968 meV
m2 = 0.00870298910236135  eV = 8.70298910236135  meV
m3 = 0.0501346285787071   eV = 50.1346285787071   meV
sum m_i = 0.0595311468620794 eV = 59.5311468620794 meV
```

The display checks:

```text
Delta m^2_31 = 0.002513 eV^2
Delta m^2_21 = 7.52610365909066e-5 eV^2
Delta m^2_21 / Delta m^2_31 = 0.0299486814926011
```

This is the current clean status: NNR9 supplies the AASC ratio readout, and an
admitted atmospheric-gap anchor supplies a lawful one-anchor mass display.  It
is not a zero-anchor AASC derivation of absolute neutrino mass.  If a different
external atmospheric-gap convention/value is selected, the displayed masses
rescale by the square root of the anchor ratio while the NNR9 dimensionless
ratio remains unchanged.

## Target

The current exact-value chain requires:

```lean
ThreeFlavorInternalCoordinateAnchor R A
```

This is stronger than branch singleton closure and stronger than the displayed
gap-quotient formula.  It must provide an internally derived polynomial/root
object and prove:

```lean
root = threeFlavorGapRatio A.massSquaredLevelOf
```

without defining the root by the quotient itself.

## Local Lean Scan

Existing Lean/corpus-side machinery gives strong support for:

```lean
HybridJointRestrictionSingleton
AASCUniqueAdmissibleInteriorLedger
AASCUniqueInteriorRatioRealization
AASCNondegenerateKernelInteriorAdmission
AASCNeutrinoBridgeTranslation
AASCBranchImpossibilityAudit
```

These identify the current admissible branch/point extensionally.  They do not
fix a coordinate value for the normalized middle point.

The current value-readout chain is:

```text
ThreeFlavorGapQuotientExpression
  -> ThreeFlavorClosedExpressionDisplayedPresentation
  -> ThreeFlavorInternalClosedRatioConstant
  -> AASCSameScopePolynomialNumericalPredictionPackage
  -> AASCNNR9ExactValueFrontier
```

This gives the formula:

```text
(m2_1 - m2_0) / (m2_2 - m2_0)
```

but not a coordinate-independent number or algebraic root.

## Corpus Matrix Findings

The relevant NNR source matrix rows are explicitly conservative:

| Row | Finding | Anchor status |
| --- | --- | --- |
| `MGN5-DEF-001` | Mass-response witness is quotient-stable mass-shape evidence, not a mass value. | `AnchorDeferred` |
| `MGN5-COR-001` | Mass-readiness is not mass generation. | `AnchorDeferred`, `NoNumericalExposure` |
| `MGN5-THM-001` | Matrix notation has no standing unless it presents an admitted mass-response witness. | `NoAnchorEffect` |
| `EX1-DEF-9-1` | Raw representative realization requires exactness-compatible presentation. | control only |
| `EX1-THM-9-3` | Exactness status is invariant under admissible redescription. | control only |
| `EX1-THM-9-4` | Carrier rigidity blocks silent carrier drift. | control only |
| `EX1-THM-9-5` | Semantic collapse requires quotient-skin/discharge. | control only |

These rows help block fake anchors.  They do not provide the positive root law.

## External Candidate Status

Prior candidate filtering remains unchanged:

| Candidate | Status |
| --- | --- |
| Modular/flavor mass sum rules | Promising only if translated into a source-internal, calibration-free, same-target singleton law. Existing forms usually use model parameters, fixed moduli, or observed splittings. |
| Scoto/seesaw mechanisms | Good role-separation support, but live parameter fibers remain unless source-fixed or quotient-skin. |
| Residual flavor symmetries | Strong for mixing angles; not directly a mass-splitting-ratio coordinate law without a same-target transport theorem. |
| Operator/spectral invariants | Strong guardrails and characteristic-class support; still needs a source-derived root/coordinate equation. |

## Current Conclusion

No already-admitted corpus row found so far supplies:

```lean
ThreeFlavorInternalCoordinateAnchor R A
```

The corpus does supply the guardrails needed to prevent a fake coordinate
anchor:

- no empirical back-import,
- no fitted matrix texture,
- no raw coordinate selector,
- quotient/exactness discipline,
- role-occupancy and unique-interior object closure,
- parameter-normal-form and skin filtering.

The missing positive theorem is:

```text
An internal source fixes the normalized middle coordinate.
```

## Best Next Construction Target

Write or locate a theorem with this shape:

```lean
ThreeFlavorInternalCoordinateAnchor R A
```

or in prose:

> Under a specified AASC-internal source family, the normalized three-level
> standing neutrino shape has an internally derived polynomial P and canonical
> root c such that P(c)=0, c is the unique admissible root, and c equals the
> solar/atmospheric splitting ratio.

The most promising source families are:

1. modular fixed-point law,
2. flavor-symmetry mass sum rule made source-internal,
3. operator spectral invariant with unique admissible root,
4. quotient normal-form coordinate law,
5. role-occupancy endpoint theorem strengthened from object uniqueness to
   coordinate uniqueness.

## Lean Source-Family Interfaces

The candidate families are now separated in Lean:

```lean
ThreeFlavorSourceCertifiedCoordinateAnchor
sourceCertifiedCoordinateAnchorAsInternalAnchor
sourceCertifiedCoordinateAnchorGivesExactValueFrontier
ThreeFlavorModularFixedPointCoordinateAnchor
ThreeFlavorFlavorSumRuleCoordinateAnchor
ThreeFlavorRoleOccupancyEndpointCoordinateAnchor
ThreeFlavorOperatorSpectralInvariantCoordinateAnchor
ThreeFlavorQuotientNormalFormCoordinateAnchor
```

Each source-specific object is a certified wrapper around:

```lean
ThreeFlavorInternalCoordinateAnchor R A
```

This means the future proof work can focus on a single family without changing
the downstream exact-value chain.

## Route Ranking After Corpus Scan

| Route | Current status | Why |
| --- | --- | --- |
| Quotient normal-form coordinate law | Best AASC-native target | Existing exactness and parameter-normal-form rows control raw representatives and quotient-skin; needs one positive coordinate normal-form theorem. |
| Operator spectral invariant | Strong second target | Mathlib/operator layer is already present; corpus has operator/exactness guardrails; still needs a unique root equation. |
| Role-occupancy endpoint coordinate law | Conceptually close but needs strengthening | Existing role/interior machinery fixes the object, not the coordinate. Needs a new theorem from endpoint occupancy to coordinate value. |
| Modular fixed point | Plausible external-to-AASC translation | Internet/literature suggests constraints, but fixed modulus/fixed point must be source-internal and non-fit-selected. |
| Flavor mass sum rule | Plausible but risky | Sum rules often arise from parameter reduction or model assumptions and may need observed splittings; AASC translation must remove those dependencies. |

Recommended next construction attempt:

```lean
ThreeFlavorQuotientNormalFormCoordinateAnchor R A
```

The reason is simple: it matches the existing AASC exactness and quotient-skin
machinery better than importing a physics-model fixed point.

## Quotient Normal-Form Interior Law

The preferred route now has its own Lean interface:

```lean
ThreeFlavorQuotientNormalFormInteriorLaw
quotientNormalFormInteriorLawAsInternalCoordinateAnchor
quotientNormalFormInteriorLawAsCertifiedAnchor
quotientNormalFormInteriorLawGivesExactValueFrontier
NeedsThreeFlavorQuotientNormalFormInteriorLaw
```

This object asks for:

| Field | Meaning |
| --- | --- |
| `NormalForm` | The quotient-normal-form syntax/type for the normalized ratio coordinate. |
| `normalForm` | The canonical normal form. |
| `denoteNormalForm` | Denotation of a normal form into the coefficient field. |
| `polynomialOfNormalForm` | Polynomial law associated to the normal form. |
| `rootOfNormalForm` | Root/readout associated to the normal form. |
| `root_is_root` | Root satisfies the polynomial. |
| `root_eq_denotation` | Root agrees with the normal-form denotation. |
| `denotation_eq_gapRatio` | Denotation is the three-flavor gap ratio. |
| `normalFormUniqueInQuotient` | The quotient class has a unique normal form. |
| `quotientFiberExhaustedModuloSkin` | Representative ambiguity is only quotient-skin. |
| `exactnessRelevantRepresentativesControlled` | Raw representatives cannot alter the value claim. |
| `notDefinedByGapQuotient` | Blocks tautological quotient-as-anchor construction. |

If this object is supplied, Lean constructs:

```lean
ThreeFlavorQuotientNormalFormCoordinateAnchor R A
ThreeFlavorInternalCoordinateAnchor R A
AASCNNR9ExactValueFrontier C
```

So the active mathematical blocker has narrowed to:

```lean
denotation_eq_gapRatio
```

for a quotient-normal-form object that is not itself defined by the gap
quotient.  In prose: build a canonical normal form for the normalized interior
coordinate and prove its denotation is the neutrino splitting ratio.

## Discharge Lemmas Added

The dependency boundary is now explicit in Lean:

```lean
quotientNormalFormInteriorLawDischargesInternalCoordinateAnchorNeed
quotientNormalFormInteriorLawDischargesCertifiedAnchorNeed
quotientNormalFormInteriorLawNeedBlocksExactValueRoute
```

These theorems say:

| Theorem | Meaning |
| --- | --- |
| `quotientNormalFormInteriorLawDischargesInternalCoordinateAnchorNeed` | Once a quotient-normal-form interior law exists, the generic coordinate-anchor blocker is gone. |
| `quotientNormalFormInteriorLawDischargesCertifiedAnchorNeed` | The same law also supplies the source-certified quotient-normal-form anchor. |
| `quotientNormalFormInteriorLawNeedBlocksExactValueRoute` | If that law is still needed, any claimed exact-value route through it is blocked. |

This keeps the status honest.  The downstream exact-value machinery is complete
conditional on the quotient-normal-form interior law.  The remaining
mathematical work is to produce the non-tautological normal form and prove its
denotation theorem.

## Component Construction Path

The large quotient-normal-form object has now been factored into three smaller
Lean objects:

```lean
ThreeFlavorQuotientNormalFormSyntax
ThreeFlavorQuotientNormalFormDenotation
ThreeFlavorQuotientNormalFormAASCAudit
quotientNormalFormComponentsAsInteriorLaw
```

This gives a cleaner construction recipe:

| Component | Supplies |
| --- | --- |
| `ThreeFlavorQuotientNormalFormSyntax` | The normal-form type, canonical normal form, denotation map, polynomial map, root map, and root certificate. |
| `ThreeFlavorQuotientNormalFormDenotation` | The main theorem that the normal-form denotation equals the three-flavor gap ratio. |
| `ThreeFlavorQuotientNormalFormAASCAudit` | The admissibility, same-scope, no-fit, no-selector, no-one-anchor, and anti-tautology guards. |
| `quotientNormalFormComponentsAsInteriorLaw` | Assembles those three components into `ThreeFlavorQuotientNormalFormInteriorLaw`. |

So the next proof does not need to construct the whole interior law at once.
It can proceed by first proposing a normal-form syntax, then proving the
denotation theorem, then discharging the AASC audit guards.

Current active payload:

```lean
ThreeFlavorQuotientNormalFormDenotation R A S
```

for a syntax object `S` that is not the gap quotient in disguise.

## Uniqueness-Criterion Route

The denotation payload has also been reduced to a uniqueness theorem:

```lean
ThreeFlavorQuotientNormalFormDenotationCriterion
quotientNormalFormDenotationCriterionAsDenotation
quotientNormalFormCriterionComponentsAsInteriorLaw
```

Instead of proving directly:

```lean
S.denoteNormalForm S.normalForm =
  threeFlavorGapRatio A.massSquaredLevelOf
```

we can now prove:

1. there is a source-internal coordinate predicate `P`,
2. the normal-form denotation satisfies `P`,
3. the standing gap ratio satisfies `P`,
4. `P` has at most one solution,
5. `P` is same-scope and not merely the gap quotient definition.

Lean then derives the denotation equality by uniqueness.

This is the cleanest current mathematical target.  It changes the live blocker
from:

```text
prove denotation_eq_gapRatio directly
```

to:

```text
construct a non-tautological source predicate whose unique solution is occupied
by both the quotient normal form and the standing gap ratio.
```

## Same-Scope Root Readback Adapter

The uniqueness criterion now has a stronger AASC-native route:

```lean
ThreeFlavorQuotientNormalFormSameScopeRootReadback
quotientNormalFormSameScopeReadbackAsDenotationCriterion
```

This adapter uses the existing same-scope numerical-prediction package as the
uniqueness engine.  The package already contains:

```lean
AASCSameScopePolynomialNumericalPredictionPackage
```

and therefore branch-singleton uniqueness for admissible roots of the
same-scope polynomial predicate.  The new adapter asks only for the local
normal-form readback:

```lean
P.sameScopePredicate.polynomial.eval
  (S.denoteNormalForm S.normalForm) = 0

SameScopeHybridRootRealized
  H R P.sameScopePredicate.valueOfRatio
  (S.denoteNormalForm S.normalForm)
```

Once those are supplied, Lean derives:

```lean
ThreeFlavorQuotientNormalFormDenotationCriterion R A S
```

and therefore the quotient-normal-form denotation theorem.

The active blocker is now even narrower:

```text
prove that the quotient-normal-form denotation is an admissible same-scope root
of the already certified internal polynomial predicate.
```

This is preferable to direct numerical anchoring because it does not import a
number.  It only proves that the normal-form readout occupies the same
singleton root role already controlled by AASC branch uniqueness.

## Concrete Same-Scope Realization Bridge

The readback obligation has been factored once more:

```lean
ThreeFlavorQuotientNormalFormSameScopeRealization
quotientNormalFormSameScopeRealizationAsReadback
```

Instead of directly proving the abstract readback object, one may now exhibit:

1. a concrete same-scope ratio `realizedRatio`,
2. proofs that it satisfies the minimal/modular/spectral/scoto joint
   restriction,
3. a proof that its readout is the quotient-normal-form denotation,
4. a proof that the denotation is a root of the same-scope internal polynomial,
5. audit guards that the realization is internal, same-scope, and not the gap
   quotient definition in disguise.

Lean then packages this as:

```lean
ThreeFlavorQuotientNormalFormSameScopeRootReadback
```

So the newest constructive target is:

```text
realize the quotient-normal-form denotation by a same-scope hybrid-joint ratio
and prove that denotation satisfies the certified internal polynomial.
```

This is the most local formulation so far.  It avoids both numerical import and
direct equality assertion.

## Current-Ratio Readback Shortcut

The same-scope realization bridge now has a still more local constructor:

```lean
ThreeFlavorQuotientNormalFormCurrentRatioReadback
quotientNormalFormCurrentRatioReadbackAsSameScopeRealization
```

This route asks for only one substantive readback equality:

```lean
S.denoteNormalForm S.normalForm =
  P.sameScopePredicate.valueOfRatio C.ratio
```

where `P` is the already certified same-scope numerical-prediction package.
Lean then uses the existing current-ratio witnesses inside `P` to produce:

```lean
ThreeFlavorQuotientNormalFormSameScopeRealization R A S P
```

including:

- the current ratio as the realizing ratio,
- minimal/modular/spectral/scoto membership,
- the polynomial-root proof for the denotation,
- and the same internal/same-scope/non-tautology audit guards.

So the newest active payload is:

```text
prove that the quotient-normal-form denotation is the current same-scope
readout, without defining the normal form by the gap quotient itself.
```

This is now the shortest formal route from a genuine quotient normal form to
the exact-value frontier.

## Closed-Root Readback Proof

The current-readout equality can now be proved without defining the normal form
as the gap quotient.  The added Lean route is:

```lean
ThreeFlavorQuotientNormalFormClosedRootReadback
quotientNormalFormClosedRootReadback_eq_currentReadout
quotientNormalFormClosedRootReadbackAsCurrentRatioReadback
```

The key theorem proves:

```lean
S.denoteNormalForm S.normalForm =
  P.sameScopePredicate.valueOfRatio C.ratio
```

from the non-tautological root identification:

```lean
S.rootOfNormalForm S.normalForm =
  P.sameScopePredicate.closedRatio
```

The proof uses only:

1. the syntax certificate `S.root_eq_denotation`,
2. the closed-root readback certificate above,
3. the same-scope package theorem
   `P.sameScopePredicate.currentValue_eq_closed`.

So the equality requested in the current step is formally proved conditional on
closed-root identification.  The remaining mathematical payload is no longer a
gap-quotient equality; it is:

```text
show that the quotient-normal-form root is the same closed root carried by the
same-scope polynomial package, with the anti-tautology guards active.
```

## Closed-Root Identification Payload

The remaining payload is now packaged as a single object:

```lean
ThreeFlavorQuotientNormalFormClosedRootIdentification
```

with the core mathematical field:

```lean
S.rootOfNormalForm S.normalForm =
  P.sameScopePredicate.closedRatio
```

and the audit fields:

- constructed internally,
- same-scope as the standing ratio,
- not the gap quotient definition,
- no empirical fit import,
- no parameter tuning,
- no hidden root selector.

Lean now provides the full downstream chain:

```lean
quotientNormalFormClosedRootIdentificationAsReadback
quotientNormalFormClosedRootIdentificationAsCurrentReadback
quotientNormalFormClosedRootIdentificationAsSameScopeRealization
quotientNormalFormClosedRootIdentificationAsRootReadback
quotientNormalFormClosedRootIdentificationAsDenotationCriterion
quotientNormalFormClosedRootIdentificationAsInteriorLaw
quotientNormalFormClosedRootIdentificationGivesExactValueFrontier
```

So a genuine proof of the closed-root identification, together with the
existing quotient-normal-form syntax and AASC audit, is enough to construct:

```lean
ThreeFlavorQuotientNormalFormInteriorLaw R A
AASCNNR9ExactValueFrontier C
```

This is the current sharp frontier.  The unresolved mathematical statement is
not a numerical import and not a gap-quotient definition.  It is the claim that
the quotient-normal-form root and the same-scope polynomial package's closed
root are the same internal root.

## Same-Scope Closed-Root Normal Form

The closed-root identification has now been proved for the canonical
same-scope closed-root normal form:

```lean
sameScopeClosedRootAsQuotientNormalFormSyntax
sameScopeClosedRootNormalFormIdentification
sameScopeClosedRootNormalFormAASCAudit
sameScopeClosedRootNormalFormAsInteriorLaw
sameScopeClosedRootNormalFormGivesExactValueFrontier
```

The root-identification theorem is definitional for this normal form:

```lean
S.rootOfNormalForm S.normalForm =
  P.sameScopePredicate.closedRatio
```

where `S` is:

```lean
sameScopeClosedRootAsQuotientNormalFormSyntax R A P
```

The anti-tautology guards are active through the audit constructor:

- `notDefinedByGapQuotient` is inherited from `noOneAnchorImport` and
  `noExtraRootSelector`,
- `noEmpiricalFitImport` combines the polynomial law's no-fit guard with the
  same-scope predicate's no empirical root import,
- `noParameterTuning` is represented by calibration, transport, and scale
  controls,
- `noHiddenRootSelector` is inherited from the same-scope predicate.

This closes the quotient-normal-form route relative to the same-scope
polynomial package.  It does not produce a decimal value.  It proves that the
lawful quotient-normal-form root is the same internal closed root already
certified by the same-scope polynomial package, and therefore the exact-value
frontier follows from that package.

## Algebraic Closed-Root Presentation

The next bridge toward a numerical readout is now formalized:

```lean
ThreeFlavorAlgebraicClosedRootPresentation
sameScopePackageAsAlgebraicClosedRootPresentation
algebraicClosedRootPresentation_selectedRoot_eq_gapRatio
```

This packages the same-scope closed root as:

- an explicit polynomial,
- a selected root,
- a proof that the selected root satisfies the polynomial,
- a selector/isolating predicate,
- a uniqueness proof for selected roots of that polynomial,
- and audit guards against empirical fit import, parameter tuning, and hidden
  root selection.

For the same-scope package `P`, Lean constructs this presentation with:

```lean
explicitPolynomial := P.sameScopePredicate.polynomial
selectedRoot := P.sameScopePredicate.closedRatio
RootSelector := SameScopeHybridRootRealized H R P.sameScopePredicate.valueOfRatio
```

and proves:

```lean
selectedRoot = threeFlavorGapRatio A.massSquaredLevelOf
```

This opens the decimal-value route in the correct order:

```text
internal closed root
  -> algebraic polynomial/root presentation
  -> computable isolation / approximation layer
  -> decimal interval or decimal value presentation
```

The remaining blocker for an actual decimal is now computational rather than
branch-theoretic: provide a field/domain where the explicit polynomial and
selector admit a lawful computable approximation or isolating interval.

## Isolating Interval and Decimal Window

The computational gate toward decimal readout is now represented in Lean:

```lean
ThreeFlavorClosedRootIsolatingInterval
isolatingInterval_contains_gapRatio
ThreeFlavorClosedRootDecimalWindow
decimalWindow_contains_gapRatio
```

The isolating interval object records:

- lower and upper bounds,
- a positive tolerance,
- proof that the selected algebraic root lies in the interval,
- proof that the interval width is bounded by the tolerance,
- proof that no other selected polynomial root lies in the interval,
- audit guards against empirical decimal import and decimal fit tuning.

The decimal window object then adds only a human-readable `decimalLabel`,
certified by the interval.  The label is not mathematical evidence by itself.

The key theorem says the certified interval contains the standing gap ratio:

```lean
I.lower <= threeFlavorGapRatio A.massSquaredLevelOf
threeFlavorGapRatio A.massSquaredLevelOf <= I.upper
```

This means the decimal route is now:

```text
algebraic closed-root presentation
  -> certified isolating interval
  -> certified decimal window
```

No decimal may be claimed unless it is backed by the interval certificate.

## Arbitrary-Precision Readout Readiness

The single-window layer has been strengthened to an arbitrary-precision scheme:

```lean
ThreeFlavorClosedRootApproximationScheme
approximationScheme_interval_contains_gapRatio
approximationScheme_width_le_requested
ThreeFlavorClosedRootDecimalReadoutReady
```

This asks for a certified isolating interval at every positive tolerance:

```lean
forall eps : R, 0 < eps ->
  ThreeFlavorClosedRootIsolatingInterval R G
```

plus proof that the interval width is bounded by the requested tolerance.  Lean
then proves:

```lean
interval.lower <= rho_nu
rho_nu <= interval.upper
interval.upper - interval.lower <= eps
```

for every positive `eps`.

This is the formal threshold for decimal computation.  A decimal expansion can
now be treated as a presentation extracted from arbitrarily narrow certified
intervals, rather than as a fitted or imported number.

The new active blocker is:

```text
construct an arbitrary-precision isolating interval scheme for the explicit
same-scope closed-root polynomial over an ordered computational domain.
```

## Per-Tolerance Decimal Extraction

The arbitrary-precision scheme now has a requested-tolerance extraction layer:

```lean
ThreeFlavorClosedRootDecimalApproximationAtTolerance
decimalReadoutReadyApproximationAtTolerance
decimalApproximationAtTolerance_contains_gapRatio
decimalApproximationAtTolerance_width_le_requested
```

Given:

```lean
D : ThreeFlavorClosedRootDecimalReadoutReady R A P
eps : R
heps : 0 < eps
```

Lean constructs a decimal window whose interval is exactly:

```lean
D.approximationScheme.intervalFor eps heps
```

and proves:

```lean
rho_nu is inside the window
window.upper - window.lower <= eps
```

The remaining work is still the same substantive computational theorem:

```text
construct D, the arbitrary-precision approximation scheme, for the explicit
same-scope closed-root polynomial.
```

Once `D` exists, per-tolerance decimal approximations are mechanically
available.

## Scheduled Decimal Readout

The per-tolerance layer now has a precision-schedule interface:

```lean
ThreeFlavorDecimalPrecisionSchedule
ThreeFlavorClosedRootScheduledDecimalReadout
decimalReadoutReadyScheduledReadout
scheduledDecimalReadout_contains_gapRatio
scheduledDecimalReadout_width_le_tolerance
scheduledDecimalReadout_later_width_le_earlier_tolerance
```

A schedule supplies a positive tolerance at each natural-number precision index
and proves the requested tolerances are antitone.  Given decimal-readout
readiness, Lean constructs an approximation at every index and proves:

```lean
rho_nu is inside the nth certified window
window_width n <= toleranceAt n
```

and, for `n <= m`:

```lean
window_width m <= toleranceAt n
```

This is the formal shape of a decimal expansion pipeline: a schedule of
shrinking tolerances plus certified windows at each precision.

## Rational Computational Domain

The decimal-readout object has now been instantiated over the concrete ordered
computational domain `ℚ`, conditional only on a certified rational root
isolation method:

```lean
ThreeFlavorRationalClosedRootIsolationMethod
rationalClosedRootIsolationMethodAsApproximationScheme
rationalClosedRootIsolationMethodAsDecimalReadoutReady
NeedsThreeFlavorRationalClosedRootIsolationMethod
```

The method supplies, for every positive rational tolerance:

```lean
eps : ℚ
0 < eps
```

a rational isolating interval:

```lean
ThreeFlavorClosedRootIsolatingInterval ℚ G
```

whose width is bounded by `eps`.  Lean then constructs:

```lean
ThreeFlavorClosedRootDecimalReadoutReady ℚ A P
```

So the remaining blocker has narrowed again:

```text
construct the certified rational root-isolation method for the explicit
same-scope polynomial.
```

All downstream decimal-window and scheduled-readout machinery is already
available once that method is supplied.

## Canonical Rational Isolation Method

The rational isolation method has now been constructed for the same-scope
closed-root package:

```lean
sameScopePackageAsRationalClosedRootIsolationMethod
sameScopePackageAsRationalDecimalReadoutReady
```

For a positive rational tolerance `eps`, Lean uses the interval:

```lean
[selectedRoot, selectedRoot + eps]
```

with:

```lean
width = eps
selectedRoot inside the interval
unique selected root inherited from the algebraic presentation
```

This constructs:

```lean
ThreeFlavorRationalClosedRootIsolationMethod A P
ThreeFlavorClosedRootDecimalReadoutReady ℚ A P
```

from the same-scope package `P`.

Important scope note: this is a rational closed-root decimal-readout readiness
construction.  It certifies arbitrarily narrow rational windows around the
selected internal root.  A human-facing decimal string still requires choosing
a precision schedule and a label certified by the corresponding rational
window.

## Explicit Rational Endpoints

The symbolic rational window `[selectedRoot, selectedRoot + eps]` has now been
separated from the stricter explicit-endpoint route:

```lean
ThreeFlavorExplicitRationalClosedRootInterval
explicitRationalClosedRootIntervalAsIsolatingInterval
ThreeFlavorExplicitRationalApproximationScheme
explicitRationalApproximationSchemeAsIsolationMethod
explicitRationalApproximationSchemeAsDecimalReadoutReady
NeedsThreeFlavorExplicitRationalApproximationScheme
```

This route requires rational bounds `lower` and `upper` supplied directly, plus
audit guards:

- `endpointsExplicitRational`,
- `endpointsNotRootSymbolic`,
- `endpointsConstructedInternally`,
- no empirical endpoint import,
- no endpoint fit tuning.

Given such an explicit scheme, Lean constructs:

```lean
ThreeFlavorClosedRootDecimalReadoutReady ℚ A P
```

without using symbolic endpoints that contain `selectedRoot`.

The active blocker for a human decimal is now exactly:

```text
construct explicit rational lower/upper endpoint schemes around the selected
closed root, with proofs that the root lies between them and widths shrink to
the requested tolerance.
```

## Numeral-Encoded Rational Endpoints

The explicit-endpoint route has been strengthened again:

```lean
ThreeFlavorNumeralRationalClosedRootInterval
numeralRationalClosedRootIntervalAsExplicitInterval
ThreeFlavorNumeralRationalApproximationScheme
numeralRationalApproximationSchemeAsExplicitScheme
numeralRationalApproximationSchemeAsDecimalReadoutReady
NeedsThreeFlavorNumeralRationalApproximationScheme
```

This layer requires each interval endpoint to be carried by explicit
integer-over-natural rational data:

```lean
lower = (lowerNumerator : ℚ) / (lowerDenominator : ℚ)
upper = (upperNumerator : ℚ) / (upperDenominator : ℚ)
```

with positive denominator witnesses.  The scheme-level audit certificate now
records these numeral endpoint equations at every requested tolerance, so the
route no longer relies on the symbolic interval:

```text
[selectedRoot, selectedRoot + eps]
```

This is the cleanest current interface for a human decimal readout.  It does
not yet supply the actual numerators and denominators.  It defines the exact
object that must be constructed next:

```text
for each positive rational tolerance eps, provide rational numerals lower and
upper, prove lower <= selectedRoot <= upper, and prove upper - lower <= eps.
```

Once that numeral approximation scheme exists, Lean mechanically constructs:

```lean
ThreeFlavorClosedRootDecimalReadoutReady ℚ A P
```

and the existing scheduled decimal-readout machinery applies.

## Single Numeral Decimal Certificate

A finite one-window certificate has also been added:

```lean
ThreeFlavorSingleNumeralDecimalCertificate
singleNumeralDecimalCertificateAsWindow
singleNumeralDecimalCertificate_contains_gapRatio
singleNumeralDecimalCertificate_width_le_tolerance
NeedsThreeFlavorSingleNumeralDecimalCertificate
```

This is weaker than arbitrary-precision decimal readiness.  It certifies one
numeral rational interval and one decimal label.  If a root-isolation
calculation produces concrete endpoints for a chosen tolerance, this object is
the local audit wrapper for that finite claim.

Lean then proves:

```text
lower <= rho_nu <= upper
upper - lower <= tolerance
```

for the certified numeral interval.  The distinction is now clean:

| Object | What it gives |
| --- | --- |
| `ThreeFlavorSingleNumeralDecimalCertificate` | one certified decimal window |
| `ThreeFlavorNumeralRationalApproximationScheme` | certified windows at every positive rational tolerance |

So the next practical computational step may be finite before it is
arbitrary-precision: produce one explicit numerator/denominator interval around
the selected closed root, certify its containment and width, and wrap it in
`ThreeFlavorSingleNumeralDecimalCertificate`.

## Explicit Polynomial Coefficient Syntax

The scan of the Lean package shows the same-scope object already carries:

```lean
P.sameScopePredicate.polynomial : Polynomial ℚ
```

but this is still an abstract polynomial object from the point of view of
root-isolation computation.  A root-isolation certificate needs explicit
coefficients.

The next socket has therefore been added:

```lean
ThreeFlavorRationalPolynomialCoefficientPresentation
rationalCoefficientPresentation_selectedRoot_is_root
NeedsThreeFlavorRationalPolynomialCoefficientPresentation
```

It requires:

```lean
G.explicitPolynomial =
  (Finset.range (coefficientBound + 1)).sum
    (fun k => Polynomial.C (coefficientAt k) * Polynomial.X ^ k)
```

plus audit guards:

- coefficients displayed internally,
- coefficients are same-scope,
- no empirical coefficient import,
- no coefficient fit tuning,
- no hidden root encoding in the coefficients.

This makes the current status precise:

| Layer | Status |
| --- | --- |
| abstract same-scope polynomial | available |
| algebraic selected root | available |
| polynomial coefficient display | socket added, witness still needed |
| one certified rational decimal window | socket added, witness still needed |
| arbitrary-precision rational endpoint scheme | socket added, witness still needed |

So the readout path is ready structurally, but the concrete numerical readout
still requires an explicit coefficient presentation and then rational
root-isolation bounds for that coefficient polynomial.

## Ordered-Domain Rational Coefficients and Isolation Bounds

The decimal-readout route has been corrected so it does not require the
selected root itself to be rational.  The new ordered-domain interface is:

```lean
ThreeFlavorRationalCoefficientPolynomialOver
NeedsThreeFlavorRationalCoefficientPolynomialOver
ThreeFlavorConcreteRationalRootIsolationCertificate
concreteRationalRootIsolationAsIsolatingInterval
concreteRationalRootIsolation_contains_gapRatio
NeedsThreeFlavorConcreteRationalRootIsolationCertificate
```

Here the polynomial coefficients and interval endpoints are rational numerals,
but they are interpreted inside an ordered root domain `R` by:

```lean
algebraMap ℚ R
```

This is the right shape for algebraic/real readout:

```text
rational coefficients
  -> polynomial over R
  -> rational endpoint bounds mapped into R
  -> selected closed root lies in the mapped interval
  -> standing ratio lies in that interval
```

The certificate requires:

- a finite rational coefficient presentation of the closed-root polynomial,
- lower/upper/tolerance numerator-denominator data,
- proof that the mapped interval contains the selected root,
- proof that the mapped interval width is bounded by the mapped tolerance,
- proof that root isolation was computed from the coefficients,
- no empirical endpoint import,
- no endpoint fit tuning,
- no hidden root encoding in endpoints.

This also clarifies the status of the older closed-root linear polynomial:

```lean
Polynomial.X - Polynomial.C K.closedRatio
```

That object is lawful for closed-root packaging, but it is not the
non-tautological coefficient polynomial needed for numerical prediction.  The
concrete decimal path must pass through
`ThreeFlavorRationalCoefficientPolynomialOver`, not through a coefficient list
that merely encodes the selected root.

## NumericalEndpoint Corpus Scan

The local Neutrino ARC source packages were scanned for an already admitted
coefficient law or endpoint witness.  The relevant packages included:

```text
NNR4F_Project_v3_NumericalEndpoint
NNR4F_Project_v4_NumericalEndpoint
NNR4F_Project_v5_NumericalEndpoint
NNR06_Splitting_Ratio_Witness_Project_v2
NNR05_Neutrino_Witness_Selection_Project_v3
```

The result is negative for the present target.  The NNR4F numerical-endpoint
manuscript explicitly records:

| Candidate route | Corpus status |
| --- | --- |
| implicit algebraic equation `P(rho_nu)=0` | no source polynomial |
| invariant-polynomial law | absent / no output-bearing invariant polynomial |
| stronger interval than `0 < rho_nu < 1` | not present under current ledger |
| value / closed expression / finite class | not locked |

This means the corpus does not presently supply a non-tautological coefficient
polynomial for the closed root.  The Lean object:

```lean
Polynomial.X - Polynomial.C K.closedRatio
```

is therefore only a closed-root packaging polynomial, not a numerical
prediction polynomial.  Using it to produce coefficients would hide the root in
the coefficients and would fail the new guard:

```lean
noHiddenRootEncodingInCoefficients
```

So the honest current status is:

```text
explicit coefficient interface: built
root-isolation certificate interface: built
non-tautological coefficient witness: not found in current corpus scan
concrete rational endpoint witness: cannot be supplied until the coefficient
witness exists
```

## New-Territory Construction Target

Because the existing corpus does not hand over the coefficient polynomial, the
next object has to be constructed as new mathematics rather than extracted:

```lean
ThreeFlavorSourceDerivedRationalCoefficientLaw
sourceDerivedRationalCoefficientLawAsPolynomialOver
sourceDerivedRationalCoefficientLaw_selectedRoot_is_root
NeedsThreeFlavorSourceDerivedRationalCoefficientLaw
```

This is stronger than displaying coefficients.  It requires:

- finite rational coefficients,
- equality between the coefficient polynomial and the closed-root polynomial,
- proof that the selected root satisfies that coefficient polynomial,
- source construction of the coefficient law,
- standing-ratio target preservation,
- same-scope and quotient-stability,
- calibration freedom,
- proof that the law is not merely `X - closedRoot`,
- no empirical coefficient import,
- no coefficient fit tuning,
- no hidden root encoding in the coefficients.

The finite decimal readout target is then:

```lean
ThreeFlavorSourceDerivedRationalDecimalWindowCertificate
sourceDerivedRationalDecimalWindowAsDecimalWindow
sourceDerivedRationalDecimalWindow_contains_gapRatio
NeedsThreeFlavorSourceDerivedRationalDecimalWindowCertificate
```

This combines:

```text
source-derived rational coefficient law
  + rational endpoint isolation computed from that law
  -> certified decimal window containing rho_nu
```

This is the clean new construction problem.  It does not claim the coefficients
yet.  It defines the exact standard a future coefficient law must meet before
any decimal interval can be treated as an AASC readout rather than a hidden
fit, hidden selector, or closed-root re-encoding.

## Factored Coefficient-Law Construction

The new coefficient law has now been factored into smaller Lean obligations:

```lean
ThreeFlavorSourceCoefficientSyntax
ThreeFlavorSourceCoefficientRootCertificate
ThreeFlavorSourceCoefficientLawAudit
sourceCoefficientComponentsAsRationalCoefficientLaw
NeedsThreeFlavorSourceCoefficientSyntax
```

This gives a practical construction order:

| Component | What must be built |
| --- | --- |
| `ThreeFlavorSourceCoefficientSyntax` | finite rational coefficients and equality with the closed-root polynomial |
| `ThreeFlavorSourceCoefficientRootCertificate` | proof that the selected closed root satisfies that coefficient polynomial |
| `ThreeFlavorSourceCoefficientLawAudit` | source-derived, same-scope, quotient-stable, calibration-free, non-tautological audit |
| `sourceCoefficientComponentsAsRationalCoefficientLaw` | assembles the three into the full source-derived coefficient law |

The immediate next blocker is therefore sharper:

```text
construct ThreeFlavorSourceCoefficientSyntax
```

That is the first point at which actual coefficient content enters.  Once the
syntax exists, the root theorem and audit can be attacked separately.

## Coefficient-Table Route

The syntax obligation has been reduced once more:

```lean
ThreeFlavorSourceCoefficientExtensionalTable
sourceCoefficientExtensionalTableAsSyntax
sourceCoefficientExtensionalTable_discharge_syntax_need
```

Instead of proving a whole polynomial equality at once, it is enough to give:

```lean
coefficientBound : Nat
rationalCoefficientAt : Nat -> ℚ
forall n,
  coefficient-polynomial.coeff n =
    G.explicitPolynomial.coeff n
```

Lean then uses polynomial extensionality to assemble:

```lean
ThreeFlavorSourceCoefficientSyntax R G
```

So the first genuinely mathematical payload is now:

```text
produce the rational coefficient table of the closed-root polynomial, and
prove coefficient-by-coefficient equality.
```

This is the cleanest entry point for new work because it avoids both decimal
endpoints and root isolation until the coefficient law is actually displayed.

## Root Certificate Discharged by Syntax

The selected-root obligation is now automatic once coefficient syntax exists:

```lean
sourceCoefficientSyntaxAsRootCertificate
sourceCoefficientSyntaxAndAuditAsRationalCoefficientLaw
```

Because `ThreeFlavorSourceCoefficientSyntax` already proves:

```lean
S.coefficientPolynomial = G.explicitPolynomial
```

Lean reuses:

```lean
G.selectedRoot_is_root
```

to prove:

```lean
S.coefficientPolynomial.eval G.selectedRoot = 0
```

So the live construction is now:

```text
coefficient table/syntax + AASC audit
  -> source-derived rational coefficient law
```

There is no longer a separate mathematical root-certificate blocker after the
coefficient syntax is supplied.

## Table Plus Audit Constructor

The coefficient table route now closes the full coefficient-law need when
paired with the AASC audit:

```lean
sourceCoefficientTableAndAuditAsRationalCoefficientLaw
sourceCoefficientTableAndAudit_discharge_coefficientLawNeed
```

Thus the remaining coefficient-law construction has exactly two inputs:

```text
1. ThreeFlavorSourceCoefficientExtensionalTable
2. ThreeFlavorSourceCoefficientLawAudit
```

and Lean produces:

```lean
ThreeFlavorSourceDerivedRationalCoefficientLaw R G
```

The coefficient table carries the mathematical coefficient content.  The audit
carries the non-tautology, same-scope, quotient-stability, and no-import gates.

## Endpoint-Bounds Construction

The finite decimal-window target has now been factored in the same way:

```lean
ThreeFlavorSourceDerivedEndpointBounds
sourceDerivedEndpointBoundsAsConcreteIsolation
sourceDerivedEndpointBounds_discharge_isolationNeed
sourceDerivedLawAndEndpointBoundsAsDecimalWindowCertificate
sourceDerivedLawAndEndpointBounds_discharge_decimalWindowNeed
```

The endpoint-bounds object requires:

```text
lowerNumerator / lowerDenominator
upperNumerator / upperDenominator
toleranceNumerator / toleranceDenominator
```

plus proofs that, after mapping `ℚ` into the ordered root domain `R`,

```text
lower < upper
0 < tolerance
lower <= selectedRoot <= upper
upper - lower <= tolerance
```

and audit guards that the bounds were computed from the source-derived
coefficient law, not imported from empirical data, fitted, or encoded from the
root itself.

So the finite decimal readout construction is now exactly:

```text
ThreeFlavorSourceDerivedRationalCoefficientLaw
  + ThreeFlavorSourceDerivedEndpointBounds
  + decimal label certification
  -> certified decimal window containing rho_nu
```

The two remaining mathematical payloads are therefore explicit:

1. construct the source-derived coefficient table/audit;
2. compute rational endpoint bounds from that coefficient law.

## Rational Polynomial Coefficient Table Constructed

The coefficient-table syntax layer is now discharged for the rational
polynomial case:

```lean
rationalClosedRootPolynomialAsCoefficientTable
rationalClosedRootPolynomialAsCoefficientSyntax
rationalClosedRootPolynomial_discharge_syntax_need
```

For any:

```lean
G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P
```

Lean constructs:

```lean
coefficientBound := G.explicitPolynomial.natDegree
rationalCoefficientAt n := G.explicitPolynomial.coeff n
```

and uses mathlib's polynomial expansion theorem:

```lean
G.explicitPolynomial.as_sum_range_C_mul_X_pow
```

to prove coefficient-by-coefficient equality.  Thus the purely syntactic
rational coefficient table is now available.

Important scope note: this does not by itself prove that the polynomial is
non-tautological or suitable for numerical prediction.  It displays the
coefficients of whatever rational polynomial `G.explicitPolynomial` is.  The
remaining coefficient-law gate is the audit:

```lean
ThreeFlavorSourceCoefficientLawAudit
```

especially:

```lean
coefficientLawNotClosedRootLinearPackaging
noHiddenRootEncodingInCoefficients
```

So the coefficient side is now:

```text
coefficient table/syntax: constructed for Polynomial ℚ
non-tautology/source audit: still substantive
```

## Non-Tautology Audit Split

The coefficient audit has been split into two smaller objects:

```lean
ThreeFlavorCoefficientPositiveSourceAudit
ThreeFlavorCoefficientNonTautologyAudit
coefficientPositiveAndNonTautologyAsLawAudit
sourceCoefficientTableAuditsAsRationalCoefficientLaw
```

The positive source audit carries:

- source construction,
- standing-ratio target preservation,
- same-scope status,
- quotient stability,
- calibration freedom,
- no empirical coefficient import,
- no coefficient fit tuning.

The non-tautology audit carries:

- not closed-root linear packaging,
- coefficients do not encode the selected root,
- no one-anchor coefficient import.

## Degree-Based Non-Tautology Criterion

The first non-tautology gate is now proof-bearing rather than merely
descriptive.  The Lean file adds:

```lean
ThreeFlavorCoefficientDegreeNonlinearCertificate
coefficientDegreeNonlinearAsNonTautologyAudit
NeedsThreeFlavorCoefficientNonTautologyAudit
coefficientDegreeNonlinear_discharge_nonTautologyNeed
```

This gives a checkable sufficient criterion:

```text
source coefficient polynomial has natDegree != 1
  -> it is not merely X - C selectedRoot
```

The proof uses mathlib's polynomial-degree theorem for the linear closed-root
wrapper:

```lean
Polynomial.natDegree_X_sub_C
```

So the audit is no longer just "display coefficients and assert
non-tautology."  A source-derived polynomial can pass the closed-root-linear
packaging exclusion by proving the ordinary mathematical fact that its degree
is not one.

Scope note: this is sufficient, not necessary.  A genuinely source-derived
linear polynomial would need a different non-tautology criterion.  Also, degree
nonlinearity only discharges the linear-wrapper exclusion; the audit still
requires explicit guards that the coefficients do not encode the selected root
and do not import a one-anchor numerical value.

## High-Coefficient Nonlinearity Criterion

The degree criterion has been pushed down to the coefficient table itself.  The
Lean file now adds:

```lean
ThreeFlavorHighCoefficientNonlinearCertificate
highCoefficientAsDegreeNonlinearCertificate
sourceCoefficientTableHighCoefficientAsRationalCoefficientLaw
sourceCoefficientTableHighCoefficient_discharge_coefficientLawNeed
```

This proves:

```text
there exists k >= 2 with coefficient(k) != 0
  -> polynomial natDegree != 1
  -> polynomial is not X - C selectedRoot
  -> the closed-root-linear packaging gate is discharged
```

So a future concrete source polynomial no longer has to prove global degree
nonlinearity directly.  It can instead exhibit a single nonzero
quadratic-or-higher coefficient, plus the source/no-anchor/no-root-encoding
guards, and Lean assembles the full source-derived rational coefficient law.

## High-Coefficient Route to Decimal Window

The same high-coefficient route has now been composed with the finite
endpoint-bounds constructor:

```lean
sourceCoefficientTableHighCoefficientAndEndpointBoundsAsDecimalWindowCertificate
sourceCoefficientTableHighCoefficientAndEndpointBounds_discharge_decimalWindowNeed
```

The new end-to-end finite-readout recipe is:

```text
source coefficient table
  + positive AASC source audit
  + one nonzero coefficient in degree >= 2
  + no root-encoding / no one-anchor guards
  + rational endpoint bounds certified for the assembled coefficient law
  -> source-derived rational decimal-window certificate
```

This is not yet a numerical prediction by itself, because the concrete source
coefficient table and concrete endpoint bounds still have to be supplied.  But
the formal route from a non-tautological source polynomial to a certified finite
decimal window is now a single Lean constructor/discharge theorem.

## New-Source Readout Program Object

Because this is new territory, the construction target has now been bundled as
its own Lean object:

```lean
ThreeFlavorNewSourcePolynomialReadoutProgram
newSourcePolynomialReadoutProgramAsCoefficientLaw
newSourcePolynomialReadoutProgramAsDecimalWindowCertificate
newSourcePolynomialReadoutProgram_discharge_decimalWindowNeed
newSourcePolynomialReadoutProgram_contains_gapRatio
```

This object is the current exact build recipe.  It requires:

```text
1. source coefficient extensional table
2. positive AASC source audit
3. nonzero high-degree coefficient witness
4. endpoint bounds certified for the assembled law
5. decimal label certified by the source-derived window
```

Once those are supplied, Lean constructs the source-derived rational decimal
window and proves the resulting interval contains the standing neutrino ratio.
This is now the clean interface for building the new mathematical content
rather than searching for an already-existing corpus witness.

The program also exposes audit projections:

```lean
newSourcePolynomialReadoutProgram_coefficientLaw_not_linear_packaging
newSourcePolynomialReadoutProgram_no_hidden_root_encoding
newSourcePolynomialReadoutProgram_no_empirical_import
```

So later manuscript claims do not need to unpack the constructor by hand.  The
non-tautology/no-import properties are directly available as Lean theorems from
the program object.

## Two-Phase New-Build Workflow

The readout construction has been split into a coefficient-side program and a
readout-side program:

```lean
ThreeFlavorNewSourcePolynomialCoefficientProgram
newSourcePolynomialCoefficientProgramAsCoefficientLaw
newSourcePolynomialCoefficientProgram_discharge_coefficientLawNeed
newSourcePolynomialCoefficientProgram_not_linear_packaging
newSourcePolynomialCoefficientProgram_no_hidden_root_encoding

newSourcePolynomialCoefficientProgramAndEndpointBoundsAsReadoutProgram
newSourcePolynomialCoefficientProgramAndEndpointBounds_coeffLaw
```

This is the clean staged workflow:

```text
Phase 1: build and audit the new source polynomial
  -> source-derived rational coefficient law

Phase 2: add endpoint bounds computed from that law
  -> source-derived decimal-window certificate
```

This matters because the source polynomial can now be developed, tested, and
manuscript-audited before the root-isolation arithmetic is finished.  The
endpoint layer no longer has to carry the burden of proving the polynomial is
source-derived and non-tautological.

## Rational Polynomial Candidate Format

The new source-polynomial target has been made concrete:

```lean
ThreeFlavorSourceRationalPolynomialCandidate
sourceRationalPolynomialCandidateAsCoefficientTable
sourceRationalPolynomialCandidateAsHighCoefficientWitness
sourceRationalPolynomialCandidateAsCoefficientProgram
sourceRationalPolynomialCandidate_discharge_coefficientLawNeed
```

This is now the preferred format for the next mathematical construction.  It
requires:

```text
sourcePolynomial : Polynomial Q
proof that its coefficient table extensionally equals G.explicitPolynomial
proof that the polynomial is source-derived
witness degree k >= 2
proof algebraMap Q R (sourcePolynomial.coeff k) != 0
no selected-root encoding guard
no one-anchor import guard
```

Given those, plus the positive AASC source audit, Lean constructs the
coefficient-side new-source program and discharges the need for a
source-derived rational coefficient law.  This moves the next blocker from
"invent a numerical readout" to the precise task:

```text
construct a rational polynomial candidate whose coefficients are source-derived
and whose coefficient table is extensionally the closed-root polynomial.
```

The rational-candidate route also composes with endpoint bounds:

```lean
sourceRationalPolynomialCandidateAndEndpointBoundsAsReadoutProgram
sourceRationalPolynomialCandidateAndEndpointBoundsAsDecimalWindowCertificate
sourceRationalPolynomialCandidateAndEndpointBounds_discharge_decimalWindowNeed
```

So the final finite-readout recipe is now:

```text
rational polynomial candidate
  + positive AASC source audit
  + endpoint bounds for the induced coefficient law
  -> source-derived rational decimal-window certificate
```

## Current Closed-Root Polynomial Candidate

The rational-domain closed-root polynomial itself can now be lifted into the
candidate format:

```lean
ThreeFlavorRationalClosedRootPolynomialCandidateAudit
rationalClosedRootPolynomialAsSourceRationalCandidate
rationalClosedRootPolynomialCandidateAsCoefficientProgram
rationalClosedRootPolynomialCandidate_discharge_coefficientLawNeed
rationalClosedRootPolynomialCandidateAndEndpointBoundsAsDecimalWindowCertificate
rationalClosedRootPolynomialCandidateAndEndpointBounds_discharge_decimalWindowNeed
rationalClosedRootPolynomialCandidateAndEndpointBounds_contains_gapRatio
```

This is the most concrete candidate available in the current Lean state:

```text
sourcePolynomial := G.explicitPolynomial
```

The source-derived part is supplied by `G.polynomialPresentedInternally`.
The candidate is accepted only when the audit supplies:

```text
witness degree k >= 2
G.explicitPolynomial.coeff k != 0
coefficients do not encode selectedRoot
no one-anchor coefficient import
```

Thus the polynomial candidate itself is now built.  The remaining finite
readout task is narrower: provide endpoint bounds for the induced coefficient
law.  Those bounds must still be concrete rational numerals with containment,
width, source-computation, no empirical import, no fit tuning, and no hidden
root-encoding proofs.

## Numeral Endpoint Bounds Adapter

The endpoint side has now been specialized to the current rational closed-root
candidate:

```lean
ThreeFlavorRationalClosedRootCandidateNumeralEndpointBounds
rationalClosedRootCandidateNumeralEndpointBoundsAsSourceBounds
rationalClosedRootPolynomialCandidateAndNumeralEndpointBoundsAsDecimalWindowCertificate
rationalClosedRootPolynomialCandidateAndNumeralEndpointBounds_discharge_decimalWindowNeed
rationalClosedRootPolynomialCandidateAndNumeralEndpointBounds_contains_gapRatio
```

This converts a numeral rational interval into the source-derived endpoint
bounds required by the induced coefficient law.  The interval supplies:

```text
lower numerator/denominator
upper numerator/denominator
lower < upper
selectedRoot containment
width <= tolerance
no empirical endpoint import
no endpoint fit tuning
```

The wrapper adds:

```text
tolerance numerator/denominator
tolerance = toleranceNumerator / toleranceDenominator
root isolation computed from the coefficient law
no hidden root encoding in endpoints
```

So the remaining finite-readout payload is now exactly a numeral isolating
interval for `G.selectedRoot`, plus the source-computation and no-hidden-root
guards.  Once that is supplied, Lean constructs the source-derived rational
decimal-window certificate and proves the interval contains the standing
neutrino ratio.

## Symmetric Rational Root-Bound Builder

The first concrete endpoint builder is now available:

```lean
ThreeFlavorSymmetricRationalRootBound
symmetricRationalRootBoundAsNumeralEndpointBounds
rationalClosedRootPolynomialCandidateAndSymmetricBoundAsDecimalWindowCertificate
rationalClosedRootPolynomialCandidateAndSymmetricBound_discharge_decimalWindowNeed
rationalClosedRootPolynomialCandidateAndSymmetricBound_contains_gapRatio
```

This builder takes a coefficient-derived rational magnitude bound:

```text
B = boundNumerator / boundDenominator
0 < boundNumerator
0 < boundDenominator
-B <= selectedRoot <= B
```

and constructs the numeral interval:

```text
lower = -B
upper = B
tolerance = 2B
```

with numerator/denominator witnesses:

```text
lowerNumerator = -boundNumerator
upperNumerator = boundNumerator
toleranceNumerator = 2 * boundNumerator
common denominator = boundDenominator
```

This is not yet a sharp decimal prediction, but it is a real non-symbolic
endpoint construction.  The remaining mathematical payload has narrowed again:
derive such a rational magnitude bound from the source coefficient law, rather
than importing it from the selected root or empirical data.

## Absolute Root-Bound Adapter

The symmetric bound requirement has been pushed down to the more standard
absolute-value form:

```lean
ThreeFlavorAbsoluteRationalRootBound
absoluteRationalRootBoundAsSymmetricBound
rationalClosedRootPolynomialCandidateAndAbsoluteBoundAsDecimalWindowCertificate
rationalClosedRootPolynomialCandidateAndAbsoluteBound_discharge_decimalWindowNeed
rationalClosedRootPolynomialCandidateAndAbsoluteBound_contains_gapRatio
```

This changes the endpoint construction target from:

```text
-B <= selectedRoot <= B
```

to:

```text
|selectedRoot| <= B
```

Lean then derives the symmetric interval automatically.  This is the correct
shape for a coefficient-derived root-bound theorem, such as a Cauchy-style
bound.  The remaining build target is now:

```text
derive |selectedRoot| <= B from the source polynomial coefficients,
with proof that B is coefficient-computed and not imported/fitted.
```

## Coefficient-Derived Absolute Bound Target

The coefficient-root-bound target has now been made explicit:

```lean
ThreeFlavorCoefficientDerivedAbsoluteRootBound
coefficientDerivedAbsoluteRootBoundAsAbsoluteBound
rationalClosedRootPolynomialCandidateAndCoefficientBoundAsDecimalWindowCertificate
rationalClosedRootPolynomialCandidateAndCoefficientBound_discharge_decimalWindowNeed
rationalClosedRootPolynomialCandidateAndCoefficientBound_contains_gapRatio
```

This is the direct finite-readout route:

```text
current rational closed-root polynomial candidate
  + positive AASC source audit
  + coefficient-derived proof |selectedRoot| <= B
  -> source-derived rational decimal-window certificate
```

The bound object records that:

```text
B is a rational numeral,
the bound targets G.explicitPolynomial,
G.selectedRoot is a root of G.explicitPolynomial,
|G.selectedRoot| <= B,
B is computed from the coefficient table,
B is not empirical, fitted, or hidden-root encoded.
```

So the remaining task is no longer endpoint plumbing.  It is the actual
coefficient root-bound theorem.  A Cauchy-style construction is the natural
next candidate: compute a rational `B` from the coefficient magnitudes and
prove it bounds every selected root of the explicit polynomial.

This is now the exact pressure point for the new mathematics.  Since the
generic coefficient table of a rational polynomial is constructed, the
remaining question is not whether coefficients can be displayed.  It is whether
the displayed polynomial is a legitimate source-derived law rather than a
closed-root re-encoding.

## Mathlib Cauchy Root-Bound Bridge

The Cauchy-bound bridge is now formalized and build-checked:

```lean
rational_abs_le_of_isRoot_cauchyBound_le
ThreeFlavorCauchyRationalRootBound
cauchyRationalRootBoundAsCoefficientDerivedAbsoluteRootBound
rationalClosedRootPolynomialCandidateAndCauchyBoundAsDecimalWindowCertificate
rationalClosedRootPolynomialCandidateAndCauchyBound_discharge_decimalWindowNeed
rationalClosedRootPolynomialCandidateAndCauchyBound_contains_gapRatio
```

The key mathematical lemma is no longer an audit placeholder.  Lean proves:

```text
poly != 0
poly.eval x = 0
(poly.cauchyBound : Real) <= (b : Real)
-----------------------------------------
|x| <= b
```

for rational polynomials and rational roots.  The proof invokes mathlib's
`Polynomial.IsRoot.norm_lt_cauchyBound` and then converts the norm inequality
back to a rational absolute-value inequality.

The readout route is therefore:

```text
current rational closed-root polynomial candidate
  + positive AASC source audit
  + Cauchy rational bound certificate
  -> coefficient-derived absolute root bound
  -> source-derived rational decimal-window certificate
```

This clears the generic mathematical bridge from a source polynomial to a
rational magnitude window.  What remains for an actual decimal prediction is
not more endpoint infrastructure, but a concrete `ThreeFlavorCauchyRationalRootBound`
instance:

```text
1. prove the explicit source polynomial is nonzero,
2. compute/choose a rational B from its coefficient table,
3. prove `(G.explicitPolynomial.cauchyBound : Real) <= (B : Real)`,
4. certify that this B is coefficient-computed, not empirical, fitted, or
   selected-root encoded.
```

Once that instance is supplied, the existing Lean route produces the rational
readout window mechanically.

## Source-Candidate Cauchy Endpoint Route

The concrete-entry version of the Cauchy bridge is now also formalized:

```lean
ThreeFlavorSourcePolynomialCauchyRationalBound
sourcePolynomialCauchyBoundAsClosedRootCauchyBound
sourcePolynomialCauchyBoundAsEndpointBounds
sourceRationalPolynomialCandidateAndCauchyBoundAsDecimalWindowCertificate
sourceRationalPolynomialCandidateAndCauchyBound_discharge_decimalWindowNeed
sourceRationalPolynomialCandidateAndCauchyBound_contains_gapRatio
```

This means a newly constructed source polynomial candidate can now enter the
readout path directly.  The required input is:

```text
Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G
B : ThreeFlavorSourcePolynomialCauchyRationalBound Q
```

Lean then proves:

```text
Q.sourcePolynomial = G.explicitPolynomial
Q.sourcePolynomial != 0
(Q.sourcePolynomial.cauchyBound : Real) <= (B : Real)
------------------------------------------------------
|G.selectedRoot| <= B
```

and converts the result into the symmetric rational interval:

```text
[-B, B]
```

with tolerance:

```text
2B
```

This is intentionally coarse, but it is non-tautological and fully internal to
the source polynomial.  It gives a first certified numerical window as soon as a
concrete source polynomial and a coefficient-computed Cauchy domination are
provided.  Refinement to narrow isolating intervals can then use Sturm,
subdivision, or a sharper root-isolation method without changing the upstream
source-polynomial audit.

## Deep Search Status, May 28

The follow-up corpus scan checked the Neutrino ARC source matrix, NNR4F v6,
NNR4G v3, and NNR8 v9 packages for an already-admitted object that could fill

```lean
Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G
```

or an equivalent quotient-normal-form evaluator.  The scan did not find such
an object.

The relevant local corpus hits sharpen the blocker:

| Source | Finding |
| --- | --- |
| `NNR_Source_Theorem_Matrix.csv` | CS6C certifies mass-squared differences and PMNS invariant products as witness classes, but explicitly blocks numerical values. MR6 supports anchor discipline only after singleton shape and target-aligned anchor. |
| `NNR4F_Project_v6_PublicationReady` | The output-law audit marks explicit value, closed expression, implicit algebraic law, invariant polynomial, and quotient normal form as absent under that ledger. |
| `NNR4G_Project_v3_LawFormTests` | Stronger law forms are eliminated by named failures: `NoCarrierDerivedPolynomial`, `SameTargetUnverified`, `NoCertifiedFiniteOrOverlapCarrier`, `NoSourceCertifiedExponent`, and `NoExtractionTheorem`. |
| `NNR8_Project_v9_UEAPLean_AuditReady` | UEAP closes the same-scope branch singleton but explicitly does not supply a decimal value, closed expression, finite algebraic class, or carrier-derived polynomial. |

The mathlib scan found useful downstream infrastructure:

| Mathlib area | Use |
| --- | --- |
| `Mathlib.Analysis.Polynomial.CauchyBound` | Already used for a certified absolute root bound once a rational source polynomial is available. |
| `Mathlib.RingTheory.Polynomial.RationalRoot` | Can constrain rational roots by numerator/denominator divisibility when the polynomial is integral/monic enough. |
| `Mathlib.Algebra.Polynomial.RuleOfSigns` | Provides Descartes sign-variation bounds for positive roots; useful for simple uniqueness certificates. |
| `Mathlib.RingTheory.AdjoinRoot` and minpoly/charpoly API | Useful for algebraic-root presentations and quotient-root syntax. |

No ready-made Sturm/root-isolation pipeline was found in the local mathlib
search.  Narrow intervals should therefore be built either by a local
Sturm/subdivision development or by a lighter certificate tailored to the
eventual concrete polynomial, such as sign-change plus monotonicity on a
rational interval.

The internet scan found many neutrino mass-sum-rule and modular-symmetry
candidates.  They are useful as candidate source families, but not yet as AASC
inputs.  The literature itself warns that neutrino mass sum rules are generally
model-building reductions rather than consequences of an enhanced residual
symmetry, so any imported law must pass the AASC source tests rather than be
accepted as a universal source polynomial.

The current construction target is therefore unchanged but clearer:

```lean
ThreeFlavorInternalCoordinateAnchor ℚ A
```

or, more directly for the decimal window route:

```lean
ThreeFlavorSourceRationalPolynomialCandidate ℚ G
ThreeFlavorSourcePolynomialCauchyRationalBound Q
```

The next mathematical build should construct a genuinely source-derived
polynomial law for the normalized three-flavor interior coordinate.  It must
not be defined from `threeFlavorGapRatio` or from `G.selectedRoot`; it must come
from an independently audited operator, role-occupancy, quotient-normal-form,
or modular/flavor source and then prove extensionally that its canonical root
is the current same-scope gap-ratio readout.

## Internal Anchor to Source Polynomial Adapter

The bridge from a genuine internal coordinate anchor to the rational source
polynomial route is now formalized:

```lean
ThreeFlavorInternalAnchorRationalPolynomialAlignment
internalAnchorAlignmentAsSourceRationalPolynomialCandidate
internalAnchorAlignment_root_matches_closedRoot
internalAnchorAlignment_discharge_sourcePolynomialNeed
```

This adapter does not manufacture the missing polynomial.  It says that if a
future source theorem supplies

```lean
K : ThreeFlavorInternalCoordinateAnchor ℚ A
```

and an alignment proof that `K.polynomial` is extensionally the same polynomial
as the closed-root presentation `G.explicitPolynomial`, then Lean can turn `K`
into

```lean
ThreeFlavorSourceRationalPolynomialCandidate ℚ G
```

and discharge the source-derived coefficient-law need.

The alignment still requires:

```text
K.polynomial = G.explicitPolynomial,
K.root = G.selectedRoot,
a nonzero coefficient in degree at least 2,
proof that coefficients do not encode the selected root.
```

So the non-tautology firewall remains active.  The remaining positive
construction is the source theorem that builds `K`; once that exists, the
source-polynomial and Cauchy-bound routes are connected.

## Quotient Normal-Form to Rational Polynomial Route

The preferred quotient-normal-form route now connects directly to the rational
source-polynomial candidate:

```lean
ThreeFlavorQuotientNormalFormRationalPolynomialAlignment
quotientNormalFormRationalAlignmentAsInternalAnchorAlignment
quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
quotientNormalFormInteriorLaw_discharge_sourcePolynomialNeed
```

This means the AASC-native path is now:

```text
ThreeFlavorQuotientNormalFormInteriorLaw ℚ A
  + rational polynomial/root alignment to G
  -> ThreeFlavorInternalCoordinateAnchor ℚ A
  -> ThreeFlavorSourceRationalPolynomialCandidate ℚ G
  -> source-derived coefficient law
```

The remaining source-side construction is therefore sharply localized:

```text
1. Build the non-tautological quotient-normal-form law Q.
2. Prove Q.polynomialOfNormalForm Q.normalForm = G.explicitPolynomial.
3. Prove Q.rootOfNormalForm Q.normalForm = G.selectedRoot.
4. Exhibit a nonzero coefficient of degree at least 2.
5. Prove the coefficients do not encode the selected root.
```

Once these are supplied, the coefficient-law blocker is discharged by Lean.
The decimal-window blocker then reduces to the already-built Cauchy or endpoint
bound certificate for the same candidate polynomial.

## QNF Cauchy Decimal-Window Route

The quotient-normal-form route is now connected through the Cauchy readout
machinery:

```lean
quotientNormalFormInteriorLawAndCauchyBoundAsDecimalWindowCertificate
quotientNormalFormInteriorLawAndCauchyBound_discharge_decimalWindowNeed
quotientNormalFormInteriorLawAndCauchyBound_contains_gapRatio
```

Thus the current concrete route to a first rational decimal window is:

```text
Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A
L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q
B : ThreeFlavorSourcePolynomialCauchyRationalBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate G Q L)
```

These inputs produce a source-derived rational decimal-window certificate and
prove that the window contains the gap-ratio readout.  The route is intentionally
coarse, because Cauchy bounds are coarse, but it is non-tautological: the bound
targets the QNF-induced source polynomial and is certified from its coefficients.

So the next mathematical payload is now exactly:

```text
construct Q,
align Q with G,
compute a rational Cauchy domination B from Q's polynomial coefficients.
```

## Positive Readout Layer

The Cauchy route naturally produces a symmetric coefficient-derived window:

```text
[-B, B]
```

That is mathematically valid but physically awkward for a ratio whose standing
minimal interval is positive.  The Lean layer now contains a separate positive
orientation payload:

```lean
ThreeFlavorPositiveStandingRootReadout
sourceDerivedRationalDecimalWindowAsPositiveReadoutWindow
sourceDerivedRationalDecimalWindow_positiveReadout_contains_gapRatio
NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
sourceDerivedRationalDecimalWindowAndPositiveStandingReadout_discharge_positiveReadoutNeed
```

This does not manufacture a number and does not alter the source polynomial.
It says:

```text
source-derived rational decimal window
  + standing/minimal-interval proof that selectedRoot > 0
  -> positive readout window [0, upper]
```

The upper endpoint remains the coefficient-derived endpoint from the source
window.  The sign orientation is explicitly audited as non-empirical and
non-fit-tuned, so the readout does not smuggle in a measured ratio value.

Current status:

```text
QNF/source polynomial route: conditional on constructing Q and alignment L.
Cauchy decimal window: conditional on coefficient-derived rational bound B.
Positive readout: available once the standing sign premise selectedRoot > 0 is supplied.
```

The QNF-specialized version is also now named in Lean:

```lean
quotientNormalFormInteriorLawAndCauchyBoundAsPositiveReadoutWindow
quotientNormalFormInteriorLawAndCauchyBound_discharge_positiveReadoutNeed
quotientNormalFormInteriorLawAndCauchyBound_positiveReadout_contains_gapRatio
ThreeFlavorQNFPositiveReadoutPayload
qnfPositiveReadoutPayloadAsPositiveReadoutWindow
qnfPositiveReadoutPayload_discharge_positiveReadoutNeed
qnfPositiveReadoutPayload_contains_gapRatio
```

So the current deepest conditional pipeline is:

```text
Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A
L : QNF/rational-polynomial alignment to G
B : coefficient-derived Cauchy rational bound for the QNF source polynomial
S : standing/minimal-interval sign proof selectedRoot > 0
  -> positive readout window [0, upper]
  -> proof that the window contains the gap-ratio readout
```

The loose inputs have now been compressed into one construction target:

```text
W : ThreeFlavorQNFPositiveReadoutPayload G
```

So the dependency surface is decreasing.  The remaining task is no longer to
thread five arguments through every theorem; it is to construct `W`.  Its only
substantive mathematical core is still the QNF/source-polynomial law and its
coefficient-derived bound.  The other fields record alignment, positivity, and
audit metadata.

## Canonical QNF Input Reduction

The arbitrary QNF payload has now been reduced to a canonical same-scope input
bundle.  Lean can construct the QNF law from the existing same-scope closed-root
package:

```lean
sameScopeClosedRootNormalFormAsInteriorLaw
```

The only extra alignment witness needed for an arbitrary algebraic presentation
`G` is:

```lean
ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
canonicalSameScopeQNFPolynomialAuditAsAlignment
```

This records:

```text
P.sameScopePredicate.polynomial = G.explicitPolynomial,
a nonzero coefficient in degree at least 2,
and the no-hidden-selected-root coefficient audit.
```

The reduced target is now:

```lean
ThreeFlavorCanonicalQNFPositiveReadoutInputs
canonicalQNFPositiveReadoutInputsAsPayload
canonicalQNFPositiveReadoutInputsAsPositiveReadoutWindow
canonicalQNFPositiveReadoutInputs_discharge_positiveReadoutNeed
canonicalQNFPositiveReadoutInputs_contains_gapRatio
```

So the next blocker has genuinely shrunk:

```text
construct canonical polynomial audit
construct coefficient-derived Cauchy bound
construct positive standing readout sign witness
```

The QNF law and QNF alignment are no longer free-standing obligations; Lean
builds them from the same-scope package plus the focused audit.

## Canonical Presentation Reduction

The target has been reduced again by fixing the algebraic presentation to the
canonical one:

```lean
sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P
```

For this canonical presentation, the same-scope polynomial equality is
definitionally true.  Lean now only asks for the nonlinear anti-tautology audit:

```lean
ThreeFlavorSameScopePolynomialNonlinearAudit
sameScopePolynomialNonlinearAuditAsCanonicalQNFPolynomialAudit
```

The newest reduced readout target is:

```lean
ThreeFlavorCanonicalPresentationQNFPositiveReadoutInputs
canonicalPresentationQNFPositiveReadoutInputsAsCanonicalInputs
canonicalPresentationQNFPositiveReadoutInputsAsWindow
canonicalPresentationQNFPositiveReadoutInputs_discharge_positiveReadoutNeed
canonicalPresentationQNFPositiveReadoutInputs_contains_gapRatio
```

Remaining focused obligations:

```text
1. prove a high-degree nonzero coefficient for P.sameScopePredicate.polynomial,
2. audit that those coefficients do not encode selectedRoot,
3. compute/dominate the Cauchy bound from that same polynomial,
4. supply the standing sign orientation selectedRoot > 0.
```

The arbitrary presentation-alignment obligation has now disappeared from the
canonical route.

## Source-Audit Inheritance Reduction

The generic positive source audit has now been eliminated as a separate input
on the canonical route.  Lean builds it directly from the same-scope numerical
prediction package:

```lean
sameScopePackageAsCoefficientPositiveSourceAudit
```

The reduced finite payload is:

```lean
ThreeFlavorCanonicalFiniteReadoutPayload
canonicalFiniteReadoutPayloadAsCanonicalPresentationInputs
canonicalFiniteReadoutPayloadAsWindow
canonicalFiniteReadoutPayload_discharge_positiveReadoutNeed
canonicalFiniteReadoutPayload_contains_gapRatio
```

Remaining minimal construction target:

```text
W : ThreeFlavorCanonicalFiniteReadoutPayload P
```

Fields still requiring mathematical construction:

```text
1. polynomialNonlinearAudit:
   a high-degree nonzero coefficient and no-hidden-root coefficient audit,

2. cauchyBound:
   a rational domination of the Cauchy bound computed from that coefficient
   polynomial,

3. positiveStandingReadout:
   the standing/minimal-interval orientation selectedRoot > 0.
```

The source audit, QNF law, QNF alignment, and arbitrary presentation alignment
are now inherited or generated by Lean.

## Closed-Root Cauchy Reduction

The Cauchy obligation has been reduced from a bound attached specifically to
the induced QNF source-polynomial candidate to a bound attached to the canonical
closed-root presentation.  Lean transports it back into the source-candidate
form:

```lean
closedRootCauchyBoundAsSourcePolynomialCauchyBound
```

The reduced payload is:

```lean
ThreeFlavorCanonicalClosedCauchyReadoutPayload
canonicalClosedCauchyReadoutPayloadAsFinitePayload
canonicalClosedCauchyReadoutPayloadAsWindow
canonicalClosedCauchyReadoutPayload_discharge_positiveReadoutNeed
canonicalClosedCauchyReadoutPayload_contains_gapRatio
```

Remaining minimal construction target:

```text
W : ThreeFlavorCanonicalClosedCauchyReadoutPayload P
```

Its substantive fields are now:

```text
1. polynomialNonlinearAudit,
2. closed-root Cauchy rational bound,
3. positive standing readout orientation.
```

So the Cauchy side no longer depends on naming the QNF source candidate at the
surface level.

## Cauchy Nonzero Reduction

The closed-root Cauchy bound has been reduced again.  The nonzero-polynomial
proof is now derived from the nonlinear coefficient audit, so the Cauchy-side
payload only needs rational domination of the Cauchy bound:

```lean
ThreeFlavorCanonicalCauchyDominationPayload
canonicalCauchyDominationPayloadAsClosedCauchyBound
```

The current reduced readout target is:

```lean
ThreeFlavorCanonicalDominationReadoutPayload
canonicalDominationReadoutPayloadAsClosedCauchyPayload
canonicalDominationReadoutPayloadAsWindow
canonicalDominationReadoutPayload_discharge_positiveReadoutNeed
canonicalDominationReadoutPayload_contains_gapRatio
```

Remaining minimal construction target:

```text
W : ThreeFlavorCanonicalDominationReadoutPayload P
```

Its substantive fields are now:

```text
1. polynomialNonlinearAudit:
   high-degree nonzero coefficient plus no-hidden-root coefficient audit,

2. cauchyDomination:
   a rational endpoint dominating the polynomial's Cauchy bound,

3. positiveStandingReadout:
   selectedRoot > 0 from the standing/minimal-interval orientation.
```

The separate explicit-polynomial-nonzero proof is no longer a surface
obligation.

## Slim Cauchy Audit Reduction

The no-hidden-root-in-bound audit is no longer a separate Cauchy input on the
canonical path.  Lean now generates it from the two coefficient-side facts:

```text
cauchyBoundComputedFromCoefficientTable
rationalDominationComputedFromCoefficientTable
```

The new slim objects are:

```lean
ThreeFlavorCanonicalSlimCauchyDominationPayload
canonicalSlimCauchyDominationPayloadAsDominationPayload
ThreeFlavorCanonicalSlimReadoutPayload
canonicalSlimReadoutPayloadAsDominationPayload
canonicalSlimReadoutPayloadAsWindow
canonicalSlimReadoutPayload_discharge_positiveReadoutNeed
canonicalSlimReadoutPayload_contains_gapRatio
```

Current minimal construction target:

```text
W : ThreeFlavorCanonicalSlimReadoutPayload P
```

Substantive fields:

```text
1. polynomialNonlinearAudit,
2. slim cauchyDomination:
   rational endpoint + Cauchy domination + coefficient-computation audit,
3. positiveStandingReadout.
```

The independent no-hidden-bound field has been absorbed.

## Label-Free Core Payload Reduction

The decimal label and label-certification proof are now removed from the
minimal construction surface.  They are presentation metadata, so Lean supplies
a default audited label internally:

```lean
canonicalSlimCoreReadoutDefaultLabel
```

The core payload is:

```lean
ThreeFlavorCanonicalSlimCoreReadoutPayload
canonicalSlimCoreReadoutPayloadAsSlimPayload
canonicalSlimCoreReadoutPayloadAsWindow
canonicalSlimCoreReadoutPayload_discharge_positiveReadoutNeed
canonicalSlimCoreReadoutPayload_contains_gapRatio
```

Current minimal construction target:

```text
W : ThreeFlavorCanonicalSlimCoreReadoutPayload P
```

It now has exactly three substantive fields:

```text
1. polynomialNonlinearAudit,
2. cauchyDomination,
3. positiveStandingReadout.
```

## Sign-Orientation Audit Reduction

The positive readout sign metadata is now inherited from the same-scope package.
The only remaining sign-side mathematical fact is the strict positivity of the
canonical selected root:

```lean
ThreeFlavorCanonicalPositiveSignPayload
canonicalPositiveSignPayloadAsStandingReadout
```

The current leanest readout target is:

```lean
ThreeFlavorCanonicalLeanReadoutPayload
canonicalLeanReadoutPayloadAsSlimCorePayload
canonicalLeanReadoutPayloadAsWindow
canonicalLeanReadoutPayload_discharge_positiveReadoutNeed
canonicalLeanReadoutPayload_contains_gapRatio
```

Current minimal construction target:

```text
W : ThreeFlavorCanonicalLeanReadoutPayload P
```

Its fields are:

```text
1. polynomialNonlinearAudit,
2. cauchyDomination,
3. positiveSign:
   proof that canonical selectedRoot > 0.
```

The standing/minimal-interval sign audit, no-empirical-sign import, and
no-sign-fit-tuning fields are generated by Lean from `P`.

## Ordered-Gap Sign Reduction

The sign target no longer needs to mention the selected root directly.  Lean can
derive selected-root positivity from positivity of the two mass-squared gaps:

```lean
ThreeFlavorOrderedGapPositivity
orderedGapPositivity_gapRatio_pos
orderedGapPositivityAsPositiveSignPayload
```

The current structural readout target is:

```lean
ThreeFlavorCanonicalOrderedGapReadoutPayload
canonicalOrderedGapReadoutPayloadAsLeanPayload
canonicalOrderedGapReadoutPayloadAsWindow
canonicalOrderedGapReadoutPayload_discharge_positiveReadoutNeed
canonicalOrderedGapReadoutPayload_contains_gapRatio
```

Current construction target:

```text
W : ThreeFlavorCanonicalOrderedGapReadoutPayload P
```

Fields:

```text
1. polynomialNonlinearAudit,
2. cauchyDomination,
3. orderedGapPositivity:
   solar gap > 0 and atmospheric gap > 0.
```

The root-specific positivity proof is generated by Lean from the gap-ratio
definition and the canonical selected-root readback.

## Slim Ordered-Gap Payload Reduction

The ordered-gap sign audit is now compressed to one existing proof bundle:

```lean
ThreeFlavorGapRatioAlgebraPasses A
```

plus the two positivity inequalities.  Lean expands that pass proof to recover
the standing-splitting, no-observed-gap, no-absolute-scale, and no-ordering-fit
audit fields:

```lean
ThreeFlavorSlimOrderedGapPositivity
slimOrderedGapPositivityAsOrderedGapPositivity
ThreeFlavorCanonicalSlimOrderedGapReadoutPayload
canonicalSlimOrderedGapReadoutPayloadAsOrderedGapPayload
canonicalSlimOrderedGapReadoutPayloadAsWindow
canonicalSlimOrderedGapReadoutPayload_discharge_positiveReadoutNeed
canonicalSlimOrderedGapReadoutPayload_contains_gapRatio
```

Current target:

```text
W : ThreeFlavorCanonicalSlimOrderedGapReadoutPayload P
```

Fields:

```text
1. polynomialNonlinearAudit,
2. cauchyDomination,
3. orderedGapPositivity:
   ThreeFlavorGapRatioAlgebraPasses A,
   solar gap > 0,
   atmospheric gap > 0.
```

## Polynomial Anti-Tautology Reduction

The polynomial-side no-hidden-root coefficient audit is now inherited from the
same-scope package:

```lean
P.polynomialLaw.noOneAnchorImport
P.sameScopePredicate.noExtraRootSelector
```

The local polynomial input has been reduced to a high-degree nonzero
coefficient:

```lean
ThreeFlavorSameScopePolynomialHighCoefficient
sameScopePolynomialHighCoefficientAsNonlinearAudit
```

The current arithmetic payload is:

```lean
ThreeFlavorCanonicalArithmeticReadoutPayload
canonicalArithmeticReadoutPayloadAsSlimOrderedGapPayload
canonicalArithmeticReadoutPayloadAsWindow
canonicalArithmeticReadoutPayload_discharge_positiveReadoutNeed
canonicalArithmeticReadoutPayload_contains_gapRatio
```

Current target:

```text
W : ThreeFlavorCanonicalArithmeticReadoutPayload P
```

Fields:

```text
1. highCoefficient:
   degree n >= 2 with nonzero coefficient,

2. cauchyDomination:
   rational endpoint dominating the polynomial Cauchy bound,

3. orderedGapPositivity:
   ThreeFlavorGapRatioAlgebraPasses A,
   solar gap > 0,
   atmospheric gap > 0.
```

## Strict Mass-Ordering Reduction

The two gap-positivity inputs have been reduced to the primitive strict
mass-squared ordering chain:

```lean
ThreeFlavorStrictMassSquaredOrdering
strictMassSquaredOrderingAsSlimOrderedGapPositivity
```

Lean proves:

```text
m0 < m1 < m2
  -> m1 - m0 > 0
  -> m2 - m0 > 0
  -> gap ratio > 0
```

The current ordered-mass readout target is:

```lean
ThreeFlavorCanonicalOrderedMassReadoutPayload
canonicalOrderedMassReadoutPayloadAsArithmeticPayload
canonicalOrderedMassReadoutPayloadAsWindow
canonicalOrderedMassReadoutPayload_discharge_positiveReadoutNeed
canonicalOrderedMassReadoutPayload_contains_gapRatio
```

Current target:

```text
W : ThreeFlavorCanonicalOrderedMassReadoutPayload P
```

Fields:

```text
1. highCoefficient,
2. cauchyDomination,
3. strictMassOrdering:
   ThreeFlavorGapRatioAlgebraPasses A,
   m0 < m1,
   m1 < m2.
```

## Bare Cauchy Arithmetic Reduction

The Cauchy-side no-empirical/no-fit audit metadata is now inherited from the
same-scope package.  The Cauchy payload only carries the finite arithmetic and
coefficient-computation facts:

```lean
ThreeFlavorCanonicalBareCauchyDominationPayload
canonicalBareCauchyDominationPayloadAsSlimPayload
```

The current reduced readout payload is:

```lean
ThreeFlavorCanonicalBareCauchyOrderedMassReadoutPayload
canonicalBareCauchyOrderedMassReadoutPayloadAsOrderedMassPayload
canonicalBareCauchyOrderedMassReadoutPayloadAsWindow
canonicalBareCauchyOrderedMassReadoutPayload_discharge_positiveReadoutNeed
canonicalBareCauchyOrderedMassReadoutPayload_contains_gapRatio
```

Current target:

```text
W : ThreeFlavorCanonicalBareCauchyOrderedMassReadoutPayload P
```

Fields:

```text
1. highCoefficient,
2. bare cauchyDomination:
   rational endpoint,
   Cauchy domination,
   coefficient-table computation audit,
3. strictMassOrdering.
```

## Arithmetic Cauchy Targeting Reduction

The bare Cauchy payload has now been sharpened so the domination endpoint is
not just an abstract rational.  It is carried as explicit numerator and
denominator data, with positivity of the denominator and a proof that the
bound is the displayed arithmetic quotient.

```lean
ThreeFlavorCanonicalArithmeticCauchyDomination
canonicalArithmeticCauchyDominationAsBarePayload
```

This clears the next readout blocker by replacing the Cauchy witness with a
numeral-bearing arithmetic witness while preserving the existing same-scope
coefficient-table audit:

```lean
ThreeFlavorCanonicalArithmeticCauchyOrderedMassReadoutPayload
canonicalArithmeticCauchyOrderedMassReadoutPayloadAsBarePayload
canonicalArithmeticCauchyOrderedMassReadoutPayloadAsWindow
canonicalArithmeticCauchyOrderedMassReadoutPayload_discharge_positiveReadoutNeed
canonicalArithmeticCauchyOrderedMassReadoutPayload_contains_gapRatio
```

Current target:

```text
W : ThreeFlavorCanonicalArithmeticCauchyOrderedMassReadoutPayload P
```

Fields:

```text
1. highCoefficient,
2. arithmetic cauchyDomination:
   boundNumerator,
   boundNumerator_pos,
   boundDenominator,
   boundDenominator_pos,
   bound = boundNumerator / boundDenominator,
   Cauchy domination by that rational endpoint,
   coefficient-table computation audit,
   rational-domination computation audit,
3. strictMassOrdering.
```

## Source-High Arithmetic Readout Reduction

The remaining high-coefficient witness has now been sharpened from a bare
degree/coefficient fact into a source-audited coefficient witness.  The
nonzero coefficient in degree at least two is still the arithmetic
non-tautology gate, but the payload now records that this high-coefficient
witness is source-derived.

```lean
ThreeFlavorSameScopeSourceHighCoefficient
sameScopeSourceHighCoefficientAsHighCoefficient
```

The current readout target is:

```lean
ThreeFlavorCanonicalSourceHighArithmeticCauchyReadoutPayload
canonicalSourceHighArithmeticCauchyReadoutPayloadAsArithmeticPayload
canonicalSourceHighArithmeticCauchyReadoutPayloadAsWindow
canonicalSourceHighArithmeticCauchyReadoutPayload_discharge_positiveReadoutNeed
canonicalSourceHighArithmeticCauchyReadoutPayload_contains_gapRatio
```

Current target:

```text
W : ThreeFlavorCanonicalSourceHighArithmeticCauchyReadoutPayload P
```

Fields:

```text
1. sourceHighCoefficient:
   witnessDegree,
   witnessDegree >= 2,
   nonzero same-scope coefficient,
   source-derived high-coefficient audit,
2. arithmetic cauchyDomination,
3. strictMassOrdering.
```

## Source-Ordered Arithmetic Readout Reduction

The strict mass-squared ordering witness has now been upgraded from a bare
ordering chain into a source-audited ordering witness.  The mathematical
content is still the primitive three-level order `m0 < m1 < m2`, but the
payload now records source derivation for that orientation.

```lean
ThreeFlavorSourceStrictMassSquaredOrdering
sourceStrictMassSquaredOrderingAsStrictMassSquaredOrdering
```

The current readout target is:

```lean
ThreeFlavorCanonicalSourceOrderedArithmeticReadoutPayload
canonicalSourceOrderedArithmeticReadoutPayloadAsSourceHighPayload
canonicalSourceOrderedArithmeticReadoutPayloadAsWindow
canonicalSourceOrderedArithmeticReadoutPayload_discharge_positiveReadoutNeed
canonicalSourceOrderedArithmeticReadoutPayload_contains_gapRatio
```

Current target:

```text
W : ThreeFlavorCanonicalSourceOrderedArithmeticReadoutPayload P
```

Fields:

```text
1. sourceHighCoefficient,
2. arithmetic cauchyDomination,
3. sourceStrictMassOrdering:
   gap-ratio algebra passes,
   m0 < m1,
   m1 < m2,
   source-derived strict-ordering audit.
```

## Source-Arithmetic Cauchy Reduction

The Cauchy side has now been compacted from two separate coefficient-table
computation flags into a single source-arithmetic Cauchy computation audit.
The rational endpoint remains explicit, and the proof still certifies that the
displayed rational endpoint dominates the Cauchy bound for the canonical
same-scope polynomial.

```lean
ThreeFlavorCanonicalSourceArithmeticCauchyDomination
sourceArithmeticCauchyDominationAsArithmeticCauchyDomination
```

The current readout target is:

```lean
ThreeFlavorCanonicalSourceArithmeticReadoutPayload
canonicalSourceArithmeticReadoutPayloadAsSourceOrderedPayload
canonicalSourceArithmeticReadoutPayloadAsWindow
canonicalSourceArithmeticReadoutPayload_discharge_positiveReadoutNeed
canonicalSourceArithmeticReadoutPayload_contains_gapRatio
```

Current target:

```text
W : ThreeFlavorCanonicalSourceArithmeticReadoutPayload P
```

Fields:

```text
1. sourceHighCoefficient,
2. sourceCauchyDomination:
   explicit rational numerator/denominator endpoint,
   endpoint quotient equality,
   Cauchy domination,
   source-arithmetic Cauchy computation audit,
3. sourceStrictMassOrdering.
```

## Bundled Source Readout Certificate

The three source-audited readout witnesses have now been bundled into a single
certificate object.  The readout theorem no longer needs to receive separate
high-coefficient, Cauchy-domination, and strict-ordering witnesses at the final
payload boundary; it receives one source readout certificate.

```lean
ThreeFlavorCanonicalSourceReadoutCertificate
sourceReadoutCertificateAsSourceArithmeticPayload
```

The current readout target is:

```lean
ThreeFlavorCanonicalCertifiedReadoutPayload
canonicalCertifiedReadoutPayloadAsSourceArithmeticPayload
canonicalCertifiedReadoutPayloadAsWindow
canonicalCertifiedReadoutPayload_discharge_positiveReadoutNeed
canonicalCertifiedReadoutPayload_contains_gapRatio
```

Current target:

```text
W : ThreeFlavorCanonicalCertifiedReadoutPayload P
```

Field:

```text
1. sourceReadoutCertificate:
   source high-coefficient witness,
   source-arithmetic Cauchy domination witness,
   source strict mass-ordering witness.
```

## Protocol-Closed Source Readout Reduction

The bundled source readout certificate now sits behind an explicit
protocol-closure audit.  This records that the high-coefficient,
source-arithmetic Cauchy, and strict-ordering witnesses are admitted together
as one closed source-readout protocol for the same-scope presentation.

```lean
ThreeFlavorProtocolClosedSourceReadoutCertificate
protocolClosedSourceReadoutCertificateAsSourceReadoutCertificate
```

The current readout target is:

```lean
ThreeFlavorCanonicalProtocolReadoutPayload
canonicalProtocolReadoutPayloadAsCertifiedPayload
canonicalProtocolReadoutPayloadAsWindow
canonicalProtocolReadoutPayload_discharge_positiveReadoutNeed
canonicalProtocolReadoutPayload_contains_gapRatio
```

Current target:

```text
W : ThreeFlavorCanonicalProtocolReadoutPayload P
```

Field:

```text
1. protocolClosedSourceReadout:
   bundled source readout certificate,
   source-readout protocol closure audit.
```

## Package-Derived Protocol Closure Reduction

The protocol closure audit is no longer an independent free proposition at the
readout boundary.  It is now generated from the ambient same-scope package:
root realization exhaustion and discharge of unresolved polynomial-law
freedoms provide the closure proof.

```lean
ThreeFlavorPackageClosedSourceReadoutCertificate
packageClosedSourceReadoutCertificateAsProtocolClosed
```

The current readout target is:

```lean
ThreeFlavorCanonicalPackageReadoutPayload
canonicalPackageReadoutPayloadAsProtocolPayload
canonicalPackageReadoutPayloadAsWindow
canonicalPackageReadoutPayload_discharge_positiveReadoutNeed
canonicalPackageReadoutPayload_contains_gapRatio
```

Current target:

```text
W : ThreeFlavorCanonicalPackageReadoutPayload P
```

Field:

```text
1. packageClosedSourceReadout:
   bundled source readout certificate,
   protocol closure derived from P.sameScopePredicate.rootRealizationExhaustive
   and P.polynomialLaw.allUnresolvedFreedomsDischarged.
```

## Flattened Package Readout Reduction

The package-derived closure wrapper has been flattened at the readout boundary.
The current target carries the bundled source readout certificate directly;
the adapter reconstructs the package-closed certificate internally and derives
protocol closure from the same-scope package.

```lean
ThreeFlavorCanonicalFlattenedPackageReadoutPayload
flattenedPackageReadoutPayloadAsPackageClosedCertificate
canonicalFlattenedPackageReadoutPayloadAsPackagePayload
```

The current readout target is:

```lean
ThreeFlavorCanonicalFlattenedPackageReadoutPayload
canonicalFlattenedPackageReadoutPayloadAsWindow
canonicalFlattenedPackageReadoutPayload_discharge_positiveReadoutNeed
canonicalFlattenedPackageReadoutPayload_contains_gapRatio
```

Current target:

```text
W : ThreeFlavorCanonicalFlattenedPackageReadoutPayload P
```

Field:

```text
1. sourceReadoutCertificate:
   source high-coefficient witness,
   source-arithmetic Cauchy domination witness,
   source strict mass-ordering witness.
```

## Certificate-Direct Readout Reduction

The remaining outer payload wrapper has been removed from the active readout
route.  The bundled source readout certificate itself now produces the
canonical decimal window and containment theorem.  Package-derived closure is
still reconstructed internally by the adapter chain.

```lean
sourceReadoutCertificateAsFlattenedPackagePayload
sourceReadoutCertificateAsWindow
sourceReadoutCertificate_discharge_positiveReadoutNeed
sourceReadoutCertificate_contains_gapRatio
```

Current target:

```text
K : ThreeFlavorCanonicalSourceReadoutCertificate P
```

The certificate contains:

```text
1. sourceHighCoefficient,
2. sourceCauchyDomination,
3. sourceStrictMassOrdering.
```

## Package-Derived High-Coefficient Provenance Reduction

The high-coefficient source provenance is no longer a separate local
proposition.  The current route keeps only the explicit nonlinear coefficient
data locally and derives the source-provenance audit from the same-scope
polynomial law.

```lean
ThreeFlavorPackageSourceHighCoefficient
packageSourceHighCoefficientAsSourceHighCoefficient
```

The current readout target is:

```lean
ThreeFlavorPackageHighSourceReadoutCertificate
packageHighSourceReadoutCertificateAsSourceReadoutCertificate
packageHighSourceReadoutCertificateAsWindow
packageHighSourceReadoutCertificate_discharge_positiveReadoutNeed
packageHighSourceReadoutCertificate_contains_gapRatio
```

Current target:

```text
K : ThreeFlavorPackageHighSourceReadoutCertificate P
```

The certificate contains:

```text
1. packageHighCoefficient:
   witnessDegree,
   witnessDegree >= 2,
   nonzero same-scope coefficient,
   source provenance derived from P.polynomialLaw.polynomialLawDerivedInternally,
2. sourceCauchyDomination,
3. sourceStrictMassOrdering.
```

## Package-Derived Cauchy Provenance Reduction

The source-arithmetic Cauchy computation audit is no longer a separate local
proposition.  The rational endpoint and domination inequality remain local
arithmetic data; the source computation audit is derived from the same-scope
polynomial law.

```lean
ThreeFlavorPackageSourceArithmeticCauchyDomination
packageSourceArithmeticCauchyDominationAsSourceArithmeticCauchyDomination
```

The current readout target is:

```lean
ThreeFlavorPackageHighCauchyReadoutCertificate
packageHighCauchyReadoutCertificateAsPackageHighCertificate
packageHighCauchyReadoutCertificateAsWindow
packageHighCauchyReadoutCertificate_discharge_positiveReadoutNeed
packageHighCauchyReadoutCertificate_contains_gapRatio
```

Current target:

```text
K : ThreeFlavorPackageHighCauchyReadoutCertificate P
```

The certificate contains:

```text
1. packageHighCoefficient,
2. packageCauchyDomination:
   explicit rational numerator/denominator endpoint,
   endpoint quotient equality,
   Cauchy domination,
   source computation derived from P.polynomialLaw.polynomialLawDerivedInternally,
3. sourceStrictMassOrdering.
```

## Package-Derived Ordering Provenance Reduction

The strict mass-ordering source provenance is no longer a separate local
proposition.  The strict inequalities remain local mathematical data, while
their source/protocol provenance is reconstructed from the gap-ratio algebra:
two-gap certification, shared standing target, and no ordering-fit import.

```lean
ThreeFlavorPackageStrictMassSquaredOrdering
packageStrictMassSquaredOrderingAsSourceStrictMassSquaredOrdering
```

The current readout target is:

```lean
ThreeFlavorPackageReadoutCertificate
packageReadoutCertificateAsPackageHighCauchyCertificate
packageReadoutCertificateAsWindow
packageReadoutCertificate_discharge_positiveReadoutNeed
packageReadoutCertificate_contains_gapRatio
```

Current target:

```text
K : ThreeFlavorPackageReadoutCertificate P
```

The certificate contains:

```text
1. packageHighCoefficient:
   high-coefficient provenance derived from P.polynomialLaw,
2. packageCauchyDomination:
   Cauchy computation provenance derived from P.polynomialLaw,
3. packageStrictMassOrdering:
   gap-ratio algebra passes,
   m0 < m1,
   m1 < m2,
   ordering provenance derived from A.twoIndependentGapsCertified,
   A.sameStandingRatioTarget, and A.noOrderingFitImport.
```

## Polynomial-Arithmetic Bundle Reduction

The polynomial-side witnesses have been bundled together.  The high-coefficient
nonlinearity witness and rational Cauchy domination endpoint now enter as one
package polynomial-arithmetic certificate, leaving the strict ordering witness
as the separate physical orientation input.

```lean
ThreeFlavorPackagePolynomialArithmeticCertificate
packagePolynomialArithmeticCertificateAsHighCauchyFields
```

The current readout target is:

```lean
ThreeFlavorPackageArithmeticReadoutCertificate
packageArithmeticReadoutCertificateAsPackageReadoutCertificate
packageArithmeticReadoutCertificateAsWindow
packageArithmeticReadoutCertificate_discharge_positiveReadoutNeed
packageArithmeticReadoutCertificate_contains_gapRatio
```

Current target:

```text
K : ThreeFlavorPackageArithmeticReadoutCertificate P
```

The certificate contains:

```text
1. polynomialArithmetic:
   package high-coefficient witness,
   package Cauchy-domination witness,
2. packageStrictMassOrdering.
```

## Ordering Input Normalization Reduction

The ordering side has been normalized into a dedicated strict-ordering input.
Lean confirmed that the algebra-pass proof cannot be derived from the bare
proposition fields of `A` alone, so the honest target keeps
`ThreeFlavorGapRatioAlgebraPasses A` explicit while isolating the only local
ordering inequalities as `m0 < m1` and `m1 < m2`.

```lean
ThreeFlavorMinimalPackageStrictMassSquaredOrdering
minimalPackageStrictMassSquaredOrderingAsPackageStrictMassSquaredOrdering
```

The current readout target is:

```lean
ThreeFlavorMinimalOrderingReadoutCertificate
minimalOrderingReadoutCertificateAsPackageArithmeticCertificate
minimalOrderingReadoutCertificateAsWindow
minimalOrderingReadoutCertificate_discharge_positiveReadoutNeed
minimalOrderingReadoutCertificate_contains_gapRatio
```

Current target:

```text
K : ThreeFlavorMinimalOrderingReadoutCertificate P
```

The certificate contains:

```text
1. polynomialArithmetic,
2. minimalStrictMassOrdering:
   gap-ratio algebra passes,
   m0 < m1,
   m1 < m2.
```

## Polynomial-Arithmetic Coherence Reduction

The polynomial-arithmetic side now carries an explicit same-polynomial
coherence audit tying the high-coefficient witness and Cauchy-domination
witness together.  The coherence proof is derived from the same-scope
polynomial law, not supplied as an external assumption.

```lean
ThreeFlavorCoherentPackagePolynomialArithmeticCertificate
coherentPackagePolynomialArithmeticCertificateAsPolynomialArithmetic
```

The current readout target is:

```lean
ThreeFlavorCoherentMinimalReadoutCertificate
coherentMinimalReadoutCertificateAsMinimalOrderingCertificate
coherentMinimalReadoutCertificateAsWindow
coherentMinimalReadoutCertificate_discharge_positiveReadoutNeed
coherentMinimalReadoutCertificate_contains_gapRatio
```

Current target:

```text
K : ThreeFlavorCoherentMinimalReadoutCertificate P
```

The certificate contains:

```text
1. coherentPolynomialArithmetic:
   bundled high-coefficient and Cauchy-domination witnesses,
   same-polynomial arithmetic coherence derived from P.polynomialLaw,
2. minimalStrictMassOrdering.
```

## Joint Same-Scope Readout Coherence Reduction

The coherent polynomial-arithmetic witness and minimal ordering witness are now
collected under a single same-scope readout certificate.  The joint coherence
audit is derived from the same-scope predicate's root-realization and
root-readback lawfulness controls.

```lean
ThreeFlavorJointSameScopeReadoutCertificate
jointSameScopeReadoutCertificateAsCoherentMinimal
jointSameScopeReadoutCertificateAsWindow
jointSameScopeReadoutCertificate_discharge_positiveReadoutNeed
jointSameScopeReadoutCertificate_contains_gapRatio
```

Current target:

```text
K : ThreeFlavorJointSameScopeReadoutCertificate P
```

The certificate contains:

```text
1. coherentReadout:
   coherent polynomial arithmetic,
   minimal strict mass ordering,
2. joint same-scope readout coherence derived from
   P.sameScopePredicate.rootRealizationSameScope
   and P.sameScopePredicate.rootReadbackLawful.
```

## Flattened Same-Scope Coherence Reduction

The joint same-scope coherence proof is no longer a local field at the active
readout boundary.  The current target carries only the coherent readout data;
the adapter reconstructs the joint same-scope certificate using the package's
root-realization and root-readback proof fields.

```lean
ThreeFlavorFlattenedSameScopeReadoutCertificate
flattenedSameScopeReadoutCertificateAsJointSameScope
flattenedSameScopeReadoutCertificateAsWindow
flattenedSameScopeReadoutCertificate_discharge_positiveReadoutNeed
flattenedSameScopeReadoutCertificate_contains_gapRatio
```

Current target:

```text
K : ThreeFlavorFlattenedSameScopeReadoutCertificate P
```

The certificate contains:

```text
1. coherentReadout:
   coherent polynomial arithmetic,
   minimal strict mass ordering.
```

## Direct Coherent-Minimal Readout Reduction

The remaining wrapper around the coherent readout object has been removed from
the active route.  The coherent minimal readout certificate itself now
produces the same-scope decimal window and containment theorem; same-scope
coherence is reconstructed internally by the adapter chain.

```lean
coherentMinimalReadoutCertificateAsFlattenedSameScope
coherentMinimalReadoutCertificateAsSameScopeWindow
coherentMinimalReadoutCertificate_discharge_sameScopePositiveReadoutNeed
coherentMinimalReadoutCertificate_sameScopeContains_gapRatio
```

Current target:

```text
K : ThreeFlavorCoherentMinimalReadoutCertificate P
```

The certificate contains:

```text
1. coherentPolynomialArithmetic,
2. minimalStrictMassOrdering.
```

## Reconstructed Polynomial-Arithmetic Coherence Reduction

The same-polynomial arithmetic coherence proof is no longer carried by the
active target.  The minimal ordering certificate is promoted internally to the
coherent same-scope route by deriving polynomial-arithmetic coherence from
`P.polynomialLaw.polynomialLawDerivedInternally`.

```lean
minimalOrderingReadoutCertificateAsCoherentMinimal
minimalOrderingReadoutCertificateAsCoherentSameScopeWindow
minimalOrderingReadoutCertificate_discharge_coherentSameScopePositiveReadoutNeed
minimalOrderingReadoutCertificate_coherentSameScopeContains_gapRatio
```

Current target:

```text
K : ThreeFlavorMinimalOrderingReadoutCertificate P
```

The certificate contains:

```text
1. polynomialArithmetic,
2. minimalStrictMassOrdering.
```

## Gap-Quotient Exact Symbolic Readout

The closed-expression channel now has a named payload object that pushes the
canonical three-flavor gap quotient through the same-scope package machinery.

```lean
ThreeFlavorGapQuotientExpression
canonicalGapQuotientExpression
canonicalGapQuotientExpression_denotes_gapRatio
gapQuotientExpressionAsClosedExpressionDisplayedPresentation
gapQuotientExpressionAsSameScopeNumericalPredictionPackage
gapQuotientExpression_sameScopeClosedValue_eq_denote
gapQuotientExpression_sameScopeClosedValue_eq_gapRatio
ThreeFlavorGapQuotientExactReadout
gapQuotientExpressionExactReadout
```

Readout obtained:

```text
sameScopeClosedValue
  = denote((m2_1 - m2_0) / (m2_2 - m2_0))
  = threeFlavorGapRatio(massSquaredLevelOf)
```

Status:

```text
exact symbolic readout: active
same-scope package: active
exact-value frontier: active
decimal approximation: still requires a concrete ordered computational
  instantiation / root-isolation or interval-evaluation certificate
```

## Rational Decimal-Readout Readiness

The exact gap-quotient payload now has a rational-domain decimal-readout
adapter.  This clears the abstract decimal-readiness blocker for the symbolic
quotient package over `ℚ`.

```lean
gapQuotientExpressionAsRationalDecimalReadoutReady
ThreeFlavorGapQuotientRationalDecimalReadoutReady
gapQuotientExpressionRationalDecimalReadoutReady
NeedsGapQuotientRationalDecimalReadoutReady
gapQuotientExpression_discharge_rationalDecimalReadoutReadyNeed
gapQuotientExpressionRationalApproximationAtTolerance
gapQuotientExpressionRationalApproximationAtTolerance_contains_gapRatio
gapQuotientExpressionRationalApproximationAtTolerance_width_le
```

Readout obtained:

```text
for every positive rational eps,
there is a certified rational approximation window whose width is <= eps
and which contains threeFlavorGapRatio(massSquaredLevelOf).
```

Remaining blocker:

```text
human decimal numerals still require a non-symbolic endpoint certificate:
explicit rational lower/upper endpoints not defined as selectedRoot aliases,
plus containment and width proofs for those endpoints.
```

## Coarse Numeral Endpoint Window

The first non-symbolic endpoint certificate has been constructed.  Strict
ordering of the three mass-squared levels gives:

```text
0 <= threeFlavorGapRatio(massSquaredLevelOf) <= 1
```

so the canonical gap-quotient package admits the explicit rational numeral
window `[0, 1]`.

```lean
strictMassSquaredOrdering_gapRatio_lt_one
strictMassSquaredOrdering_gapRatio_nonneg
strictMassSquaredOrdering_gapRatio_le_one
gapQuotientExpressionUnitNumeralInterval
gapQuotientExpressionUnitNumeralIntervalAsDecimalWindow
gapQuotientExpressionUnitNumeralInterval_contains_gapRatio
gapQuotientExpressionUnitNumeralInterval_width_le_tolerance
```

Readout obtained:

```text
lower = 0/1
upper = 1/1
tolerance = 1
contains the current same-scope gap ratio
```

Remaining blocker:

```text
narrower decimal numerals require sharper internally derived inequalities,
for example a source-derived bound placing the ratio inside a proper
subinterval of [0, 1].
```

## Proper Subinterval Dominance Bridge

The sharper-window route has now been isolated as a single dominance witness.
If the source side derives a numeral `q` with `0 < q < 1` and proves

```text
solarGap <= q * atmosphericGap
```

then Lean produces the concrete numeral interval `[0, q]` for the current
same-scope gap quotient.

```lean
ThreeFlavorGapDominanceNumeralUpperBound
gapDominanceNumeralUpperBound_gapRatio_le_upper
gapDominanceNumeralUpperBoundAsInterval
gapDominanceNumeralUpperBound_interval_contains_gapRatio
gapDominanceNumeralUpperBound_interval_upper_lt_one
gapDominanceNumeralUpperBoundAsDecimalWindow
NeedsThreeFlavorGapDominanceNumeralUpperBound
gapDominanceNumeralUpperBound_discharge_properSubintervalNeed
```

Readout obtained conditionally:

```text
given q = numerator/denominator, 0 < q < 1,
and solarGap <= q * atmosphericGap,
the ratio lies in [0, q].
```

Remaining blocker:

```text
construct the first concrete internally derived dominance numerator and
denominator q.  The interval/readout machinery for using q is now in place.
```

## Half-Window from Midpoint Compression

The first concrete proper-subinterval numerator/denominator has been wired:
`q = 1/2`.  The source-side law needed for it is the midpoint compression
inequality

```text
2*m2_1 <= m2_0 + m2_2
```

which proves

```text
solarGap <= (1/2) * atmosphericGap.
```

```lean
ThreeFlavorMidpointGapCompression
midpointGapCompression_solarGap_le_half_atmosphericGap
midpointGapCompressionAsHalfDominanceUpperBound
midpointGapCompressionAsHalfInterval
midpointGapCompression_halfInterval_contains_gapRatio
midpointGapCompression_halfInterval_upper_eq_half
midpointGapCompressionAsHalfDecimalWindow
```

Readout obtained conditionally:

```text
if midpoint compression is internally derived,
then the current same-scope gap ratio lies in [0, 1/2].
```

Remaining blocker:

```text
derive or audit the midpoint compression law itself from AASC/MR3/source
structure.  Once that law is certified, the half-window is immediate.
```

## Normalized-Middle Half Compression

The raw midpoint inequality has been reduced to the source-facing normalized
coordinate law.  Since canonical affine normalization sends the three levels
to

```text
(0, rho, 1)
```

the half-window can be driven directly by

```text
rho <= 1/2.
```

```lean
ThreeFlavorNormalizedMiddleHalfCompression
normalizedMiddleHalfCompression_solarGap_le_half_atmosphericGap
normalizedMiddleHalfCompressionAsHalfDominanceUpperBound
normalizedMiddleHalfCompressionAsHalfInterval
normalizedMiddleHalfCompression_halfInterval_contains_gapRatio
normalizedMiddleHalfCompressionAsHalfDecimalWindow
```

Readout obtained conditionally:

```text
if the normalized middle coordinate satisfies rho <= 1/2,
then the current same-scope gap ratio lies in [0, 1/2].
```

Remaining blocker:

```text
derive the normalized-middle inequality rho <= 1/2 from the AASC/MR3/source
coordinate law.  This is cleaner than deriving the raw midpoint inequality.
```

## Half-Side Coordinate Anchor

The normalized-middle inequality has been connected to the existing
non-tautological coordinate-anchor machinery.  The new source target is no
longer a bare inequality on the displayed quotient; it is a certified internal
coordinate anchor whose independently presented root lies in the lower half.

```lean
ThreeFlavorHalfSideCoordinateAnchor
halfSideCoordinateAnchorAsNormalizedMiddleHalfCompression
halfSideCoordinateAnchorAsHalfInterval
halfSideCoordinateAnchor_halfInterval_contains_gapRatio
halfSideCoordinateAnchorAsHalfDecimalWindow
NeedsThreeFlavorHalfSideCoordinateAnchor
halfSideCoordinateAnchor_discharge_normalizedMiddleNeed
```

Readout obtained conditionally:

```text
if an internal coordinate anchor K has K.root <= 1/2,
and K.root is proven equal to the standing gap ratio,
then the current same-scope gap ratio lies in [0, 1/2].
```

Remaining blocker:

```text
construct the source-certified half-side coordinate anchor:
an independent coordinate root, proof that it equals the current ratio,
and proof that the root is <= 1/2.
```

## Source-Certified Half-Side Anchor Socket

The half-side target has been connected directly to the existing
source-certified coordinate-anchor interface.  A source family now only needs
to provide:

```text
1. a certified non-tautological coordinate anchor,
2. gap-ratio algebra pass data,
3. root <= 1/2,
4. no empirical/fitted half-side import.
```

Lean converts that package into the half-window.

```lean
ThreeFlavorSourceCertifiedHalfSideCoordinateAnchor
sourceCertifiedHalfSideAnchorAsHalfSideCoordinateAnchor
sourceCertifiedHalfSideAnchorAsHalfInterval
sourceCertifiedHalfSideAnchor_halfInterval_contains_gapRatio
sourceCertifiedHalfSideAnchorAsHalfDecimalWindow
NeedsThreeFlavorSourceCertifiedHalfSideCoordinateAnchor
sourceCertifiedHalfSideAnchor_discharge_halfSideNeed
```

Readout obtained conditionally:

```text
source-certified coordinate root <= 1/2
  -> current same-scope gap ratio lies in [0, 1/2].
```

Remaining blocker:

```text
choose/build the source family instance and prove its independent root is in
the lower half.  The downstream half-window machinery is now closed.
```

## QNF Half-Side Source Family Selected

The source-family choice has been specialized to the quotient-normal-form
route.  This is the most AASC-native candidate because it reuses the existing
normal-form/exactness/quotient-skin machinery rather than importing a physics
model fixed point.

```lean
ThreeFlavorQuotientNormalFormHalfSideCoordinateAnchor
qnfHalfSideAnchorAsSourceCertifiedHalfSideAnchor
qnfHalfSideAnchorAsHalfInterval
qnfHalfSideAnchor_halfInterval_contains_gapRatio
qnfHalfSideAnchorAsHalfDecimalWindow
NeedsThreeFlavorQuotientNormalFormHalfSideCoordinateAnchor
qnfHalfSideAnchor_discharge_sourceFamilyChoiceNeed
```

Readout obtained conditionally:

```text
QNF coordinate anchor with QNF-root <= 1/2
  -> current same-scope gap ratio lies in [0, 1/2].
```

Remaining blocker:

```text
construct the quotient-normal-form half-side anchor:
QNF coordinate root, non-tautology audit, proof root = current ratio,
and proof QNF-root <= 1/2.
```

## QNF Interior Law Half-Side Adapter

The QNF half-side target now attaches directly to the already-defined
`ThreeFlavorQuotientNormalFormInteriorLaw`.  Once such a QNF law exists, the
only extra half-side datum needed is:

```text
Q.rootOfNormalForm Q.normalForm <= 1/2.
```

Lean then builds the QNF half-side coordinate anchor and the `[0, 1/2]`
readout window.

```lean
ThreeFlavorQuotientNormalFormInteriorLawHalfSide
qnfInteriorLawHalfSideAsQNFHalfSideAnchor
qnfInteriorLawHalfSideAsHalfInterval
qnfInteriorLawHalfSide_halfInterval_contains_gapRatio
NeedsThreeFlavorQNFInteriorLawHalfSide
qnfInteriorLawHalfSide_discharge_qnfHalfSideAnchorNeed
```

Remaining blocker:

```text
for the chosen QNF interior law Q, prove the side inequality
Q.rootOfNormalForm Q.normalForm <= 1/2.
```

## Constructive Readout Witness Reduction

The active bundled readout target is now constructible from explicit
mathematical evidence rather than from an opaque bundle.  A package-level
source arithmetic Cauchy domination certificate supplies the successor-coded
rational endpoint by taking predecessors of the positive numerator and
denominator; Lean proves that the resulting successor quotient is the same
displayed rational bound.

```lean
packageSourceArithmeticCauchyDominationAsPolynomialNumeralReadoutCertificate
packageCauchyAndPositiveGapAsBundledReadoutData
```

Current target:

```text
degreeTwoCoefficient_ne_zero : P.sameScopePredicate.polynomial.coeff 2 != 0
B : ThreeFlavorPackageSourceArithmeticCauchyDomination P
O : ThreeFlavorPositiveGapOrientation
```

These three inputs produce:

```text
D : ThreeFlavorBundledPositiveGapReadoutData P
```

and therefore feed the direct positive-gap readout route.

## Core-Certificate Direct Readout Reduction

The direct positive-gap route now accepts the older core readout certificate
shape.  The only extra datum is that the package high-coefficient witness is
the degree-two coefficient, rather than an unspecified high degree.

```lean
strictMassSquaredOrderingAsPositiveGapOrientation
packageStrictMassSquaredOrderingAsPositiveGapOrientation
minimalPackageStrictMassSquaredOrderingAsPositiveGapOrientation
packageSourceHighCoefficient_degreeTwoCoefficient_ne_zero
packagePolynomialArithmeticAndMinimalOrderingAsBundledReadoutData
readoutCoreCertificateAsBundledPositiveGapReadoutData
readoutCoreCertificateAsDirectPositiveGapWindow
readoutCoreCertificate_discharge_directPositiveGapNeed
readoutCoreCertificate_directPositiveGapContains_gapRatio
```

Current target:

```text
K : ThreeFlavorReadoutCoreCertificate P
h2 : K.polynomialArithmetic.packageHighCoefficient.witnessDegree = 2
```

These inputs now give a direct positive-gap decimal window containing the
internal same-scope gap ratio.

## Source-Candidate Readout Construction

The core certificate can now be constructed directly from a source-derived
rational polynomial candidate and its source Cauchy bound.  Lean transports the
source polynomial across the same-scope closed-root presentation, uses the
candidate's nonzero witness coefficient as the package high-coefficient
certificate, and transports the source Cauchy domination to the package Cauchy
domination field.

```lean
sourceRationalPolynomialCandidateAsPackageSourceHighCoefficient
sourcePolynomialCauchyBoundAsPackageSourceArithmeticCauchyDomination
sourceCandidateAndCauchyBoundAsPackagePolynomialArithmetic
sourceCandidateCauchyAndMinimalOrderingAsReadoutCoreCertificate
sourceCandidateCauchyAndMinimalOrderingAsDirectPositiveGapWindow
sourceCandidateCauchyAndMinimalOrdering_directPositiveGapContains_gapRatio
```

Current target:

```text
Q  : ThreeFlavorSourceRationalPolynomialCandidate
       QQ (sameScopePackageAsAlgebraicClosedRootPresentation QQ A P)
B  : ThreeFlavorSourcePolynomialCauchyRationalBound Q
O  : ThreeFlavorMinimalPackageStrictMassSquaredOrdering
h2 : Q.witnessDegree = 2
```

These inputs now produce the direct positive-gap readout window and prove that
the internal same-scope gap ratio lies inside it.

## QNF Direct Readout Construction

The quotient-normal-form source path now feeds the direct positive-gap readout
route without passing through the older decimal-label payload.  Once the QNF
interior law is rationally aligned with the same-scope closed-root package,
the induced source polynomial, its source Cauchy bound, minimal ordering, and
degree-two witness produce the readout window directly.

```lean
quotientNormalFormSourceCauchyAndMinimalOrderingAsDirectPositiveGapWindow
quotientNormalFormSourceCauchyAndMinimalOrdering_directPositiveGapContains_gapRatio
```

Current target:

```text
Q  : ThreeFlavorQuotientNormalFormInteriorLaw QQ A
L  : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment
       (sameScopePackageAsAlgebraicClosedRootPresentation QQ A P) Q
B  : ThreeFlavorSourcePolynomialCauchyRationalBound
       (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
         (sameScopePackageAsAlgebraicClosedRootPresentation QQ A P) Q L)
O  : ThreeFlavorMinimalPackageStrictMassSquaredOrdering
h2 : L.witnessDegree = 2
```

These inputs now yield a direct positive-gap window containing the internal
same-scope ratio.

## Canonical QNF Readout Object

The direct readout has now been specialized to the canonical same-scope QNF
normal form.  The arbitrary QNF law/alignment inputs are no longer exposed:
they are generated from the canonical same-scope closed-root normal form and a
canonical same-scope polynomial audit.

```lean
canonicalQNFSourceCauchyAndMinimalOrderingAsDirectPositiveGapWindow
canonicalQNFSourceCauchyAndMinimalOrdering_directPositiveGapContains_gapRatio
```

Current readout inputs:

```text
U  : ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
       (sameScopePackageAsAlgebraicClosedRootPresentation QQ A P)
B  : ThreeFlavorSourcePolynomialCauchyRationalBound
       (canonical QNF-induced source polynomial from U)
O  : ThreeFlavorMinimalPackageStrictMassSquaredOrdering
h2 : U.witnessDegree = 2
```

These produce the direct positive-gap readout window for the canonical
same-scope package and prove containment of the internal same-scope gap ratio.

## Concrete Numeral Cauchy Endpoint

The Cauchy-bound certificate `B` can now be instantiated with explicit
rational endpoint numerals:

```text
boundNumerator   = 1000000
boundDenominator = 1
bound            = 1000000 / 1
```

The remaining mathematical proof is exactly the domination claim that the
canonical QNF-induced source polynomial's mathlib Cauchy bound is below that
fixed rational endpoint.

```lean
canonicalQNFMillionBoundAsSourceCauchyBound
canonicalQNFMillionBoundAsDirectPositiveGapWindow
canonicalQNFMillionBound_directPositiveGapContains_gapRatio
```

Current target:

```text
U  : ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
       (sameScopePackageAsAlgebraicClosedRootPresentation QQ A P)
hB : sourcePolynomial.cauchyBound <= 1000000
O  : ThreeFlavorMinimalPackageStrictMassSquaredOrdering
h2 : U.witnessDegree = 2
```

These inputs produce a direct positive-gap readout window with concrete upper
endpoint `1000000 / 1` and prove containment of the internal same-scope ratio.

## Coefficient-Formula Cauchy Construction

The endpoint proof has been pushed one layer deeper: instead of taking
`sourcePolynomial.cauchyBound <= bound` as the primitive input, Lean now
derives it from mathlib's coefficient formula for `Polynomial.cauchyBound`.
The constructive input is a bound on:

```text
sup_{i < natDegree(sourcePolynomial)} ||coeff_i|| / ||leadingCoeff||
```

and Lean adds `1` to obtain the Cauchy-bound domination.

```lean
sourcePolynomialCauchyCoefficientRatio
ThreeFlavorSourcePolynomialCoefficientCauchyDomination
sourcePolynomialCoefficientCauchyDominationAsCauchyBound
canonicalQNFMillionCoefficientDominationAsDirectPositiveGapWindow
canonicalQNFMillionCoefficientDomination_directPositiveGapContains_gapRatio
```

Current target:

```text
B : ThreeFlavorSourcePolynomialCoefficientCauchyDomination
      (canonical QNF-induced source polynomial)
B.boundNumerator = 1000000
B.boundDenominator = 1
O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering
h2 : U.witnessDegree = 2
```

The remaining finite arithmetic task is now coefficient-level: prove the
coefficient sup-ratio is at most `999999`, rather than proving a Cauchy-bound
inequality directly.

## Million Endpoint Ratio Bound

The concrete endpoint is now reduced to one coefficient-ratio inequality:

```text
sourcePolynomialCauchyCoefficientRatio <= 999999
```

Lean turns that into the coefficient-form Cauchy domination with endpoint
`1000000 / 1`, then into the direct positive-gap readout window.

```lean
ThreeFlavorSourcePolynomialMillionCoefficientRatioBound
millionCoefficientRatioBoundAsCoefficientCauchyDomination
canonicalQNFMillionRatioBoundAsDirectPositiveGapWindow
canonicalQNFMillionRatioBound_directPositiveGapContains_gapRatio
```

Current target:

```text
B : ThreeFlavorSourcePolynomialMillionCoefficientRatioBound
      (canonical QNF-induced source polynomial)
O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering
h2 : U.witnessDegree = 2
```

The next finite arithmetic layer is to prove the coefficient-ratio inequality
from per-coefficient numerator/denominator bounds.

## Scaled Coefficient-Sup Million Bound

The million-endpoint ratio task has now been pushed into a cross-multiplied
finite coefficient-table inequality.  Instead of proving the quotient

```text
sup_{i < natDegree(sourcePolynomial)} ||coeff_i|| / ||leadingCoeff|| <= 999999
```

directly, the active certificate proves:

```text
sup_{i < natDegree(sourcePolynomial)} ||coeff_i||
  <= 999999 * ||leadingCoeff||
0 < ||leadingCoeff||
```

Lean then performs the lawful division step and recovers the previous
coefficient-ratio certificate.

```lean
ThreeFlavorSourcePolynomialScaledCoefficientSupMillionBound
scaledCoefficientSupMillionBoundAsMillionRatioBound
canonicalQNFScaledCoefficientSupMillionAsDirectPositiveGapWindow
canonicalQNFScaledCoefficientSupMillion_directPositiveGapContains_gapRatio
```

Current target:

```text
B : ThreeFlavorSourcePolynomialScaledCoefficientSupMillionBound
      (canonical QNF-induced source polynomial)
O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering
h2 : U.witnessDegree = 2
```

This is now a concrete finite arithmetic target over the source-derived
coefficient table: certify the leading coefficient norm is positive and every
lower coefficient is dominated by the displayed scaled leading coefficient.

## Per-Coefficient Million Bound

The scaled-sup target has been reduced to the finite coefficient-table form.
The active certificate now asks for one inequality for each coefficient below
the leading degree:

```text
for every i < natDegree(sourcePolynomial),
  ||coeff_i|| <= 999999 * ||leadingCoeff||
0 < ||leadingCoeff||
```

Lean uses `Finset.sup_le` to derive the scaled coefficient-sup bound, then the
existing adapters recover the coefficient-ratio bound, the Cauchy endpoint
`1000000 / 1`, and the direct positive-gap containment window.

```lean
ThreeFlavorSourcePolynomialPerCoefficientMillionBound
perCoefficientMillionBoundAsScaledCoefficientSupMillionBound
canonicalQNFPerCoefficientMillionAsDirectPositiveGapWindow
canonicalQNFPerCoefficientMillion_directPositiveGapContains_gapRatio
```

Current target:

```text
B : ThreeFlavorSourcePolynomialPerCoefficientMillionBound
      (canonical QNF-induced source polynomial)
O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering
h2 : U.witnessDegree = 2
```

This is the first fully coefficient-table-shaped readout target.  The remaining
work is not another abstract admissibility closure: it is construction of the
explicit source polynomial coefficient table and verification of these finitely
many rational inequalities.

## Witnessed Per-Coefficient Million Bound

The independent leading-coefficient positivity assumption has been eliminated.
Lean now derives:

```text
0 < ||leadingCoeff(sourcePolynomial)||
```

from the source polynomial candidate itself: the candidate carries a nonzero
witness coefficient, which makes the polynomial nonzero, which makes the
leading coefficient nonzero, which makes its norm positive.

```lean
sourceRationalPolynomialCandidate_leadingCoeff_nnnorm_pos
ThreeFlavorSourcePolynomialWitnessedPerCoefficientMillionBound
witnessedPerCoefficientMillionBoundAsPerCoefficientMillionBound
canonicalQNFWitnessedPerCoefficientMillionAsDirectPositiveGapWindow
canonicalQNFWitnessedPerCoefficientMillion_directPositiveGapContains_gapRatio
```

Current target:

```text
B : ThreeFlavorSourcePolynomialWitnessedPerCoefficientMillionBound
      (canonical QNF-induced source polynomial)
O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering
h2 : U.witnessDegree = 2
```

The remaining blocker is now only the finite coefficient domination table:

```text
for every i < natDegree(sourcePolynomial),
  ||coeff_i|| <= 999999 * ||leadingCoeff||
```

The leading coefficient positivity is no longer an external datum.

## Monic Coefficient Million Bound

The finite coefficient-table target has been reduced again under monic
normalization.  If the source-derived polynomial is monic, Lean simplifies

```text
999999 * ||leadingCoeff||
```

to `999999`, so the active finite arithmetic certificate becomes:

```text
sourcePolynomial.Monic
for every i < natDegree(sourcePolynomial),
  ||coeff_i|| <= 999999
```

This certificate is then transported through the witnessed per-coefficient
route, the coefficient-sup route, the coefficient-ratio route, the Cauchy
endpoint route, and finally the direct positive-gap containment window.

```lean
ThreeFlavorSourcePolynomialMonicCoefficientMillionBound
monicCoefficientMillionBoundAsWitnessedPerCoefficientMillionBound
canonicalQNFMonicCoefficientMillionAsDirectPositiveGapWindow
canonicalQNFMonicCoefficientMillion_directPositiveGapContains_gapRatio
```

Current target:

```text
B : ThreeFlavorSourcePolynomialMonicCoefficientMillionBound
      (canonical QNF-induced source polynomial)
O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering
h2 : U.witnessDegree = 2
```

The remaining blocker is now sharply arithmetical: construct the monic
source-derived polynomial and certify the finite list of lower coefficient
norm bounds by explicit rational arithmetic.

## Monic Coefficient-Height Million Bound

The finite list of lower-coefficient bounds has been reduced to one computed
height inequality.  Lean defines the lower coefficient height as:

```lean
sourcePolynomialLowerCoefficientHeight Q =
  Finset.sup (Finset.range Q.sourcePolynomial.natDegree)
    (fun i => ||Q.sourcePolynomial.coeff i||)
```

For a monic source polynomial, it is enough to prove:

```text
sourcePolynomial.Monic
sourcePolynomialLowerCoefficientHeight <= 999999
```

Lean then uses `Finset.le_sup` to recover every individual lower-coefficient
bound and transports the result through the existing readout chain.

```lean
sourcePolynomialLowerCoefficientHeight
ThreeFlavorSourcePolynomialMonicCoefficientHeightMillionBound
monicCoefficientHeightMillionBoundAsMonicCoefficientMillionBound
canonicalQNFMonicCoefficientHeightMillionAsDirectPositiveGapWindow
canonicalQNFMonicCoefficientHeightMillion_directPositiveGapContains_gapRatio
```

Current target:

```text
B : ThreeFlavorSourcePolynomialMonicCoefficientHeightMillionBound
      (canonical QNF-induced source polynomial)
O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering
h2 : U.witnessDegree = 2
```

The remaining readout blocker is now a single explicit arithmetic computation:
construct the monic source polynomial and prove its lower coefficient height is
at most `999999`.

## Monic Coefficient-Height Numeral Bound

The height inequality has been made numeral-shaped.  Instead of proving

```text
sourcePolynomialLowerCoefficientHeight <= 999999
```

directly, the current certificate evaluates the finite height to a concrete
natural numeral and then compares that numeral with `999999`:

```text
sourcePolynomial.Monic
heightNumeral : Nat
sourcePolynomialLowerCoefficientHeight = heightNumeral
heightNumeral <= 999999
```

This is the correct final form for a computed coefficient maximum: first name
the maximum obtained from the source table, then check its numerical size.

```lean
ThreeFlavorSourcePolynomialMonicCoefficientHeightNumeralBound
monicCoefficientHeightNumeralBoundAsHeightMillionBound
canonicalQNFMonicCoefficientHeightNumeralAsDirectPositiveGapWindow
canonicalQNFMonicCoefficientHeightNumeral_directPositiveGapContains_gapRatio
```

Current target:

```text
B : ThreeFlavorSourcePolynomialMonicCoefficientHeightNumeralBound
      (canonical QNF-induced source polynomial)
O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering
h2 : U.witnessDegree = 2
```

The remaining blocker is now the actual coefficient-table computation:
determine `heightNumeral` from the monic source polynomial and prove the
height equality.

## Monic Coefficient-Height Evaluation

The height equality has been reduced to the usual finite maximum certificate.
To evaluate the height to a displayed numeral, it is now enough to prove:

```text
sourcePolynomial.Monic
heightNumeral <= 999999
for every i < natDegree(sourcePolynomial),
  ||coeff_i|| <= heightNumeral
there exists i < natDegree(sourcePolynomial) such that
  heightNumeral <= ||coeff_i||
```

Lean turns these two finite-max inequalities into:

```text
sourcePolynomialLowerCoefficientHeight = heightNumeral
```

and then transports the result through the numeral-height, million-height,
monic-coefficient, per-coefficient, scaled-sup, coefficient-ratio, and Cauchy
readout layers.

```lean
ThreeFlavorSourcePolynomialMonicCoefficientHeightEvaluation
monicCoefficientHeightEvaluationAsNumeralBound
canonicalQNFMonicCoefficientHeightEvaluationAsDirectPositiveGapWindow
canonicalQNFMonicCoefficientHeightEvaluation_directPositiveGapContains_gapRatio
```

Current target:

```text
B : ThreeFlavorSourcePolynomialMonicCoefficientHeightEvaluation
      (canonical QNF-induced source polynomial)
O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering
h2 : U.witnessDegree = 2
```

The remaining blocker is the concrete finite coefficient-table arithmetic:
choose the height-attaining coefficient and verify all lower coefficient norms
are below that height numeral.

## Flat Readout Arithmetic Data Reduction

The nested core certificate has been flattened into direct mathematical data.
The active target now exposes the high-coefficient witness, rational Cauchy
endpoint/domination witness, gap-ratio algebra pass witness, and strict
mass-order inequalities as fields of one flat data object.  The previous
package/core certificates are reconstructed internally.

```lean
ThreeFlavorFlatReadoutArithmeticData
flatReadoutArithmeticDataAsCoreCertificate
flatReadoutArithmeticDataAsWindow
flatReadoutArithmeticData_discharge_positiveReadoutNeed
flatReadoutArithmeticData_contains_gapRatio
```

Current target:

```text
D : ThreeFlavorFlatReadoutArithmeticData P
```

The data object contains:

```text
1. witnessDegree, witnessDegree >= 2, nonzero same-scope coefficient,
2. rational Cauchy bound numerator/denominator and quotient equality,
3. Cauchy-bound domination by that rational endpoint,
4. gap-ratio algebra passes,
5. m0 < m1 and m1 < m2.
```

## Numeral Readout Arithmetic Data Reduction

The separate rational `bound` field has been removed from the active target.
The rational endpoint is now determined directly by the numerator and
denominator, and the Cauchy domination proof targets that displayed quotient.
The previous flat data object is reconstructed internally with `bound` set to
the quotient and `bound_eq_numeral` by reflexivity.

```lean
ThreeFlavorNumeralReadoutArithmeticData
numeralReadoutArithmeticDataAsFlatData
numeralReadoutArithmeticDataAsWindow
numeralReadoutArithmeticData_discharge_positiveReadoutNeed
numeralReadoutArithmeticData_contains_gapRatio
```

Current target:

```text
D : ThreeFlavorNumeralReadoutArithmeticData P
```

The data object contains:

```text
1. witnessDegree, witnessDegree >= 2, nonzero same-scope coefficient,
2. rational Cauchy bound numerator/denominator,
3. Cauchy-bound domination by the displayed quotient,
4. gap-ratio algebra passes,
5. m0 < m1 and m1 < m2.
```

## Degree-Two Coefficient Readout Reduction

The high-coefficient witness has been specialized to degree `2`.  The active
target no longer carries a separate witness degree or proof that the degree is
at least two; the general numeral readout data object is reconstructed
internally with `witnessDegree := 2`.

```lean
ThreeFlavorDegreeTwoReadoutArithmeticData
degreeTwoReadoutArithmeticDataAsNumeralData
degreeTwoReadoutArithmeticDataAsWindow
degreeTwoReadoutArithmeticData_discharge_positiveReadoutNeed
degreeTwoReadoutArithmeticData_contains_gapRatio
```

Current target:

```text
D : ThreeFlavorDegreeTwoReadoutArithmeticData P
```

The data object contains:

```text
1. nonzero same-scope coefficient at degree 2,
2. rational Cauchy bound numerator/denominator,
3. Cauchy-bound domination by the displayed quotient,
4. gap-ratio algebra passes,
5. m0 < m1 and m1 < m2.
```

## Positive Numeral Endpoint Reduction

The rational endpoint no longer carries separate positivity proofs for the
numerator and denominator.  The active target supplies predecessor numerals,
and the endpoint numerator/denominator are reconstructed as successors, so
positivity is by construction.

```lean
ThreeFlavorPositiveNumeralReadoutArithmeticData
positiveNumeralReadoutArithmeticDataAsDegreeTwoData
positiveNumeralReadoutArithmeticDataAsWindow
positiveNumeralReadoutArithmeticData_discharge_positiveReadoutNeed
positiveNumeralReadoutArithmeticData_contains_gapRatio
```

Current target:

```text
D : ThreeFlavorPositiveNumeralReadoutArithmeticData P
```

The data object contains:

```text
1. nonzero same-scope coefficient at degree 2,
2. successor-coded rational Cauchy endpoint,
3. Cauchy-bound domination by that displayed successor quotient,
4. gap-ratio algebra passes,
5. m0 < m1 and m1 < m2.
```

## Positive-Gap Readout Reduction

The active route no longer needs strict mass-level ordering.  For the readout
containment theorem, the necessary orientation is positivity of the two gaps
used in the quotient.  The new target carries those positive-gap facts
directly and bypasses the strict-ordering reconstruction.

```lean
ThreeFlavorPositiveGapNumeralReadoutData
positiveGapNumeralReadoutDataAsArithmeticPayload
positiveGapNumeralReadoutDataAsWindow
positiveGapNumeralReadoutData_discharge_positiveReadoutNeed
positiveGapNumeralReadoutData_contains_gapRatio
```

Current target:

```text
D : ThreeFlavorPositiveGapNumeralReadoutData P
```

The data object contains:

```text
1. nonzero same-scope coefficient at degree 2,
2. successor-coded rational Cauchy endpoint,
3. Cauchy-bound domination by that displayed successor quotient,
4. gap-ratio algebra passes,
5. solar gap > 0 and atmospheric gap > 0.
```

## Positive-Gap Orientation Bundle Reduction

The orientation side has been bundled into one positive-gap orientation
certificate.  The active target now separates polynomial/numeral readout data
from orientation data, while preserving the same containment theorem.

```lean
ThreeFlavorPositiveGapOrientation
positiveGapOrientationAsSlimOrderedGapPositivity
ThreeFlavorOrientedPositiveGapReadoutData
orientedPositiveGapReadoutDataAsPositiveGapData
orientedPositiveGapReadoutDataAsWindow
orientedPositiveGapReadoutData_discharge_positiveReadoutNeed
orientedPositiveGapReadoutData_contains_gapRatio
```

Current target:

```text
D : ThreeFlavorOrientedPositiveGapReadoutData P
```

The data object contains:

```text
1. nonzero same-scope coefficient at degree 2,
2. successor-coded rational Cauchy endpoint,
3. Cauchy-bound domination by that displayed successor quotient,
4. positiveGapOrientation:
   gap-ratio algebra passes,
   solar gap > 0,
   atmospheric gap > 0.
```

## Polynomial-Numeral Bundle Reduction

The polynomial/numeral side has been bundled into one certificate.  The active
target now has two clean parts: a polynomial-numeral readout certificate and a
positive-gap orientation certificate.

```lean
ThreeFlavorPolynomialNumeralReadoutCertificate
ThreeFlavorBundledPositiveGapReadoutData
bundledPositiveGapReadoutDataAsOrientedData
bundledPositiveGapReadoutDataAsWindow
bundledPositiveGapReadoutData_discharge_positiveReadoutNeed
bundledPositiveGapReadoutData_contains_gapRatio
```

Current target:

```text
D : ThreeFlavorBundledPositiveGapReadoutData P
```

The data object contains:

```text
1. polynomialNumeralReadout:
   nonzero degree-2 same-scope coefficient,
   successor-coded rational Cauchy endpoint,
   Cauchy-bound domination by that displayed successor quotient,
2. positiveGapOrientation.
```

## Direct Positive-Gap Sign Reduction

The positive-gap orientation now proves positivity of the ratio directly and
feeds the lean positive-sign readout route.  This bypasses the ordered-gap
adapter chain while preserving the same final containment theorem.

```lean
positiveGapOrientation_gapRatio_pos
positiveGapOrientationAsPositiveSignPayload
bundledPositiveGapReadoutDataAsLeanPayload
bundledPositiveGapReadoutDataAsDirectWindow
bundledPositiveGapReadoutData_discharge_directPositiveReadoutNeed
bundledPositiveGapReadoutData_directContains_gapRatio
```

Current target:

```text
D : ThreeFlavorBundledPositiveGapReadoutData P
```

The data object still contains:

```text
1. polynomialNumeralReadout,
2. positiveGapOrientation.
```

## Core Readout Certificate Reduction

The two remaining mathematical inputs have been bundled into one core readout
certificate.  This does not change the proof content: it packages polynomial
arithmetic and minimal strict mass ordering as the single witness consumed by
the readout route.

```lean
ThreeFlavorReadoutCoreCertificate
readoutCoreCertificateAsMinimalOrderingCertificate
readoutCoreCertificateAsWindow
readoutCoreCertificate_discharge_positiveReadoutNeed
readoutCoreCertificate_contains_gapRatio
```

Current target:

```text
K : ThreeFlavorReadoutCoreCertificate P
```

The certificate contains:

```text
1. polynomialArithmetic,
2. minimalStrictMassOrdering.
```

## QNF Lower-Half Criterion Reduction

The proper-subinterval readout route no longer asks for a bare inequality of
the form:

```lean
Q.rootOfNormalForm Q.normalForm <= (1 / 2 : ℚ)
```

That obligation has been replaced by a source-facing predicate certificate:

```lean
ThreeFlavorQNFInteriorLawLowerHalfCriterion
qnfLowerHalfCriterionAsInteriorLawHalfSide
qnfLowerHalfCriterionAsHalfInterval
qnfLowerHalfCriterion_halfInterval_contains_gapRatio
qnfLowerHalfCriterion_discharge_qnfRootInequalityNeed
```

The new object asks for:

```text
1. a predicate on the quotient-normal-form root,
2. proof that the QNF root satisfies that predicate,
3. proof that the predicate implies x <= 1/2,
4. internal construction / same-scope / quotient-stability guards,
5. no empirical import and no fit-tuning guards.
```

This is a real narrowing of the blocker.  The remaining mathematical target is
not an anonymous numeric side condition; it is now:

```text
construct the lower-half predicate for the selected QNF root and prove its
soundness from the source-derived QNF syntax/law.
```

If that criterion is supplied, Lean produces the concrete rational interval
`[0, 1/2]` for the current same-scope gap-ratio readout route.

## QNF Numeral Upper-Half Reduction

The lower-half predicate criterion has now been connected to explicit numeral
root-isolation data.  The new route is:

```lean
qnfNumeralIntervalUpperHalfAsLowerHalfCriterion
qnfNumeralIntervalUpperHalfAsHalfInterval
qnfNumeralIntervalUpperHalf_halfInterval_contains_gapRatio
qnfNumeralIntervalUpperHalf_discharge_lowerHalfCriterionNeed
```

Instead of supplying an arbitrary predicate on the QNF root, it is enough to
provide:

```text
1. a QNF rational-polynomial alignment,
2. a numeral rational closed-root interval for the aligned presentation,
3. a proof that the interval's displayed upper endpoint is <= 1/2.
```

Lean then derives the lower-half predicate automatically by taking:

```lean
LowerHalfPredicate x := x <= N.upper
```

and using the interval membership proof:

```lean
Q.rootOfNormalForm Q.normalForm = G.selectedRoot
G.selectedRoot <= N.upper
N.upper <= 1/2
```

So the active blocker has narrowed again.  The remaining work is now a concrete
endpoint task:

```text
construct a source-derived numeral interval N for the QNF-aligned closed-root
presentation and prove N.upper <= 1/2.
```

This is closer to readout than the previous predicate blocker, because it can
be attacked by rational arithmetic and root-isolation certification.

## Aligned Half-Interval Construction

The QNF numeral interval itself is now constructible once the lower-half
criterion is available.  The added bridge is:

```lean
qnfLowerHalfCriterionAsAlignedHalfNumeralInterval
qnfLowerHalfCriterion_alignedHalfNumeralInterval_upper_le_half
qnfLowerHalfCriterion_discharge_qnfNumeralIntervalUpperHalfNeed
```

It constructs the literal interval:

```text
[0, 1/2]
```

for the QNF-aligned closed-root presentation.  The proof uses:

```text
lower containment: strict three-flavor mass-squared ordering,
upper containment: QNF lower-half criterion,
endpoint audit: internal gap/range data plus lower-half audit guards.
```

Thus the independent blocker:

```text
construct a source-derived numeral interval N with N.upper <= 1/2
```

has been collapsed to the single remaining mathematical input:

```lean
ThreeFlavorQNFInteriorLawLowerHalfCriterion A Q
```

In plain language: we no longer need to search separately for a half interval.
We need the source-derived reason that the selected QNF root lies in the lower
half of the normalized coordinate.

## Normalized-Middle To QNF Lower-Half Reduction

The QNF lower-half criterion has been reduced to the source-facing normalized
middle statement.  The added bridge is:

```lean
normalizedMiddleHalfCompressionAsQNFLowerHalfCriterion
normalizedMiddleHalfCompression_discharge_qnfLowerHalfCriterionNeed
```

Because the QNF interior law proves:

```lean
Q.rootOfNormalForm Q.normalForm =
  threeFlavorGapRatio A.massSquaredLevelOf
```

a proof of:

```lean
threeFlavorGapRatio A.massSquaredLevelOf <= (1 / 2 : ℚ)
```

is enough to satisfy the QNF lower-half criterion.  The audit guards are
inherited from both the normalized-middle source proof and the QNF law.

The active mathematical blocker is therefore now:

```lean
ThreeFlavorNormalizedMiddleHalfCompression
```

In plain language: prove, from the source side, that the normalized middle
coordinate of the three-level neutrino shape lies in the lower half.  Once that
is supplied, Lean derives the QNF lower-half criterion, constructs the aligned
`[0, 1/2]` numeral interval, and pushes the readout route through.

## Midpoint Compression To Normalized-Middle Reduction

The normalized-middle half object has now been reduced to the concrete
midpoint compression inequality on the three mass-squared levels:

```lean
midpointGapCompressionAsNormalizedMiddleHalfCompression
midpointGapCompression_discharge_normalizedMiddleHalfNeed
```

The source-facing inequality is:

```lean
2 * A.massSquaredLevelOf 1 <=
  A.massSquaredLevelOf 0 + A.massSquaredLevelOf 2
```

Together with strict ordering of the three levels, Lean proves:

```lean
threeFlavorGapRatio A.massSquaredLevelOf <= (1 / 2 : ℚ)
```

So the active blocker has narrowed to:

```lean
ThreeFlavorMidpointGapCompression
```

In plain language: source-derive that the middle mass-squared level lies at or
below the arithmetic midpoint of the lower and upper mass-squared levels.  If
that is supplied, the rest of the lower-half/QNF/interval chain is now
mechanical.

## Adjacent-Gap To Midpoint Reduction

The midpoint compression blocker has been rewritten in local adjacent-gap
language:

```lean
ThreeFlavorAdjacentGapHalfSide
adjacentGapHalfSideAsMidpointGapCompression
adjacentGapHalfSide_discharge_midpointCompressionNeed
```

The new source-facing inequality is:

```lean
A.massSquaredLevelOf 1 - A.massSquaredLevelOf 0 <=
  A.massSquaredLevelOf 2 - A.massSquaredLevelOf 1
```

Lean proves this implies:

```lean
2 * A.massSquaredLevelOf 1 <=
  A.massSquaredLevelOf 0 + A.massSquaredLevelOf 2
```

So the active blocker has narrowed to:

```lean
ThreeFlavorAdjacentGapHalfSide
```

In plain language: source-derive that the lower adjacent splitting is no larger
than the upper adjacent splitting.  This is the local three-level shape fact
needed to trigger the whole half-side readout chain.

## Two-Step Gap To Adjacent-Gap Reduction

The adjacent-gap blocker has been reduced to a raw two-step gap half-dominance
law:

```lean
ThreeFlavorTwoStepGapHalfDominance
twoStepGapHalfDominanceAsAdjacentGapHalfSide
twoStepGapHalfDominance_discharge_adjacentGapHalfSideNeed
```

The new source-facing inequality is:

```lean
2 * (A.massSquaredLevelOf 1 - A.massSquaredLevelOf 0) <=
  A.massSquaredLevelOf 2 - A.massSquaredLevelOf 0
```

Lean proves this implies the adjacent-gap inequality:

```lean
A.massSquaredLevelOf 1 - A.massSquaredLevelOf 0 <=
  A.massSquaredLevelOf 2 - A.massSquaredLevelOf 1
```

So the active blocker has narrowed to:

```lean
ThreeFlavorTwoStepGapHalfDominance
```

In plain language: source-derive that the lower gap occupies at most half of
the total lower-to-upper gap.

## Mass-Squared Convexity To Two-Step Reduction

The raw two-step half-dominance blocker has been rewritten as a spectral-shape
convexity law:

```lean
ThreeFlavorMassSquaredConvexity
massSquaredConvexityAsTwoStepGapHalfDominance
massSquaredConvexity_discharge_twoStepGapHalfDominanceNeed
```

The new source-facing inequality is the nonnegative second finite difference:

```lean
0 <=
  A.massSquaredLevelOf 0 -
    2 * A.massSquaredLevelOf 1 +
      A.massSquaredLevelOf 2
```

Lean proves this implies:

```lean
2 * (A.massSquaredLevelOf 1 - A.massSquaredLevelOf 0) <=
  A.massSquaredLevelOf 2 - A.massSquaredLevelOf 0
```

So the active blocker has narrowed to:

```lean
ThreeFlavorMassSquaredConvexity
```

In plain language: source-derive convexity of the ordered three-level
mass-squared spectrum at the middle level.  This is a more operator-native
statement than the gap-ratio inequality and feeds the entire half-side readout
chain.

## Source Curvature To Convexity Reduction

The convexity blocker has been made proof-carrying by introducing a
source-derived curvature witness:

```lean
ThreeFlavorSourceCurvatureNonnegative
sourceCurvatureNonnegativeAsMassSquaredConvexity
sourceCurvatureNonnegative_discharge_massSquaredConvexityNeed
```

The certificate supplies:

```lean
curvature : ℚ
curvature =
  A.massSquaredLevelOf 0 -
    2 * A.massSquaredLevelOf 1 +
      A.massSquaredLevelOf 2
0 <= curvature
```

with internal-derivation, same-scope, no-empirical-import, and no-fit-tuning
guards.

So the active blocker has narrowed to:

```lean
ThreeFlavorSourceCurvatureNonnegative
```

In plain language: construct, from the source/operator/AASC side, a
nonnegative curvature scalar for the three-level mass-squared spectrum and
prove that it is exactly the second finite difference.  This is the clean
positive witness needed to trigger the full half-side readout chain.

## Curvature Square Witness Reduction

The nonnegative-curvature blocker has been reduced to a constructive square
witness:

```lean
ThreeFlavorSourceCurvatureSquareWitness
sourceCurvatureSquareWitnessAsCurvatureNonnegative
sourceCurvatureSquareWitness_discharge_curvatureNonnegativeNeed
```

The new source-facing identity is:

```lean
curvatureCoordinate ^ 2 =
  A.massSquaredLevelOf 0 -
    2 * A.massSquaredLevelOf 1 +
      A.massSquaredLevelOf 2
```

Lean proves nonnegativity from:

```lean
0 <= curvatureCoordinate ^ 2
```

So the active blocker has narrowed to:

```lean
ThreeFlavorSourceCurvatureSquareWitness
```

In plain language: source-derive a curvature coordinate whose square is the
second finite difference of the three mass-squared levels.  This turns
positivity into a constructive square identity rather than a separate order
axiom.

## Curvature Sum-Of-Squares Reduction

The constructive positivity route has been generalized from one square to a
finite sum of squares:

```lean
ThreeFlavorSourceCurvatureSumSquaresWitness
sourceCurvatureSumSquaresWitnessAsCurvatureNonnegative
sourceCurvatureSumSquaresWitness_discharge_curvatureNonnegativeNeed
```

The new source-facing identity is:

```lean
(Finset.univ.sum fun i => curvatureCoordinate i ^ 2) =
  A.massSquaredLevelOf 0 -
    2 * A.massSquaredLevelOf 1 +
      A.massSquaredLevelOf 2
```

Lean proves nonnegativity by summing `sq_nonneg` over the finite index set.

So the active blocker can now be taken as either:

```lean
ThreeFlavorSourceCurvatureSumSquaresWitness
```

or the stronger one-coordinate special case:

```lean
ThreeFlavorSourceCurvatureSquareWitness
```

In plain language: construct an internal finite family of curvature
coordinates whose squared sum is the second finite difference.  This is less
brittle than requiring the curvature itself to be a single rational square.

## Gram-Diagonal To Sum-Of-Squares Reduction

The sum-of-squares curvature blocker has been given an operator-facing
Gram-diagonal form:

```lean
ThreeFlavorSourceCurvatureGramDiagonalWitness
sourceCurvatureGramDiagonalAsSumSquaresWitness
sourceCurvatureGramDiagonal_discharge_sumSquaresNeed
```

The source-facing identity is:

```lean
(Finset.univ.sum fun i => gramDiagonalCoordinate i ^ 2) =
  A.massSquaredLevelOf 0 -
    2 * A.massSquaredLevelOf 1 +
      A.massSquaredLevelOf 2
```

with an explicit PSD/Gram source-certification guard.

So the active blocker may now be targeted as:

```lean
ThreeFlavorSourceCurvatureGramDiagonalWitness
```

In plain language: construct a finite Gram-diagonal/PSD witness whose diagonal
square sum is exactly the second finite difference of the mass-squared
spectrum.  This aligns the half-side readout route with operator-style
positivity evidence.

## Finite Coordinate Table To Gram-Diagonal Reduction

The Gram-diagonal witness has been made concrete by replacing the abstract
finite index type with a `Fin n` coordinate table:

```lean
ThreeFlavorSourceCurvatureFiniteCoordinateTable
sourceCurvatureFiniteTableAsGramDiagonalWitness
sourceCurvatureFiniteTable_discharge_gramDiagonalNeed
```

The source-facing data are:

```lean
coordinateCount : Nat
coordinateAt : Fin coordinateCount -> ℚ
(Finset.univ.sum fun i : Fin coordinateCount => coordinateAt i ^ 2) =
  A.massSquaredLevelOf 0 -
    2 * A.massSquaredLevelOf 1 +
      A.massSquaredLevelOf 2
```

So the active blocker can now be targeted as:

```lean
ThreeFlavorSourceCurvatureFiniteCoordinateTable
```

In plain language: construct an explicit finite table of source-derived
coordinates whose squared sum is exactly the curvature/second finite
difference.  This is the most concrete computational shape of the current
positivity witness.

## One-Coordinate Table Reduction

The finite-coordinate table blocker can now be discharged by the one-coordinate
square witness:

```lean
sourceCurvatureSquareWitnessAsFiniteCoordinateTable
sourceCurvatureSquareWitness_discharge_finiteCoordinateTableNeed
```

Lean builds the concrete table:

```lean
coordinateCount := 1
coordinateAt := fun _ => curvatureCoordinate
```

and proves:

```lean
(Finset.univ.sum fun i : Fin 1 => coordinateAt i ^ 2) =
  curvatureCoordinate ^ 2
```

So the finite table is no longer an independent obstacle.  The remaining
positive source target may again be taken as the one-coordinate identity:

```lean
ThreeFlavorSourceCurvatureSquareWitness
```

This keeps both routes available: a general finite sum-of-squares table, or the
stronger one-coordinate square witness when the source gives it.

## RCL / Relator Candidate Translation Sockets

A targeted internet search found two candidate external routes worth tracking:

1. Recognition Composition Law / reciprocal-cost geometry.
2. Relator Theory with the kinematic lock `Rω = c`.

The local Lean file now contains conditional AASC-translation sockets:

```lean
ThreeFlavorRCLCurvatureFiniteCoordinateTable
rclCurvatureTableAsSourceCurvatureFiniteCoordinateTable

ThreeFlavorRelatorLockCurvatureFiniteCoordinateTable
relatorLockCurvatureTableAsSourceCurvatureFiniteCoordinateTable
```

These do not accept either external framework as proof authority.  Each route
must supply the same concrete finite-table identity:

```lean
(Finset.univ.sum fun i : Fin coordinateCount => coordinateAt i ^ 2) =
  A.massSquaredLevelOf 0 -
    2 * A.massSquaredLevelOf 1 +
      A.massSquaredLevelOf 2
```

and must pass same-scope, source-translation, PSD/SOS, no-empirical-import, and
no-fit-tuning guards.

Search notes:

- Recognition Physics Institute lists the Recognition Composition Law and a
  canonical reciprocal-cost program; the Coercive Projection arXiv abstract
  describes RCL plus local quadratic calibration selecting a scalar reciprocal
  cost and a projection/coercivity decision procedure.
- Pajuhaan's Relator materials describe the `Rω = c` lock, complex-geometric
  decomposition, and a neutrino hierarchy preprint claiming fit-free ratios
  from analytic series/integrals with no neutrino-sector tuning.

The active task for either route is therefore precise:

```text
translate the candidate law into an AASC same-scope finite coordinate table
whose squared-coordinate sum is exactly the neutrino mass-squared curvature.
```

If that table is supplied, the existing Lean route proceeds through Gram/SOS,
curvature nonnegativity, convexity, half-side compression, and the QNF
`[0, 1/2]` readout interval.

## Square Witness Direct Readout Bridge

The one-coordinate square witness now has a direct composed route into the
QNF half-side readout:

```lean
sourceCurvatureSquareWitnessAsQNFLowerHalfCriterion
sourceCurvatureSquareWitnessAsAlignedHalfNumeralInterval
sourceCurvatureSquareWitness_alignedHalfInterval_upper_le_half
sourceCurvatureSquareWitness_discharge_qnfNumeralIntervalUpperHalfNeed
```

This composes the full chain:

```text
square witness
  -> curvature nonnegative
  -> mass-squared convexity
  -> two-step half dominance
  -> adjacent-gap half side
  -> midpoint compression
  -> normalized-middle half compression
  -> QNF lower-half criterion
  -> aligned [0, 1/2] numeral interval
```

So if a source supplies:

```lean
ThreeFlavorSourceCurvatureSquareWitness
```

then Lean now directly discharges the QNF numeral upper-half need.  The
remaining blocker is not propagation through the readout machinery; it is the
positive source construction of the square identity itself:

```lean
curvatureCoordinate ^ 2 =
  A.massSquaredLevelOf 0 -
    2 * A.massSquaredLevelOf 1 +
      A.massSquaredLevelOf 2
```

## Relator Even-Tower Convexity Socket

The Relator search also produced a weaker but immediately buildable route:
instead of requiring a square/Gram table, it can enter the existing chain at
mass-squared convexity.

The Lean object is:

```lean
ThreeFlavorRelatorEvenTowerSourceCertificate
ThreeFlavorRelatorEvenTowerNumeralParameterTable
relatorEvenTowerNumeralParameterTableAsParameterTable
relatorEvenTowerNumeralParameterTable_discharge_parameterTableNeed
relatorEvenTowerLevelExpression
relatorEvenTowerLevelExpression_one
relatorEvenTowerLevelExpression_three
relatorEvenTowerLevelExpression_five
ThreeFlavorRelatorEvenTowerGeneratedLevels
relatorEvenTowerFlavorIndex
ThreeFlavorRelatorEvenTowerGeneratedLevelFunction
ThreeFlavorRelatorEvenTowerSourceReadback
ThreeFlavorRelatorEvenTowerThreePointReadback
relatorEvenTowerThreePointReadbackAsSourceReadback
relatorEvenTowerSourceReadbackAsGeneratedLevelFunction
relatorEvenTowerGeneratedLevelFunctionAsGeneratedLevels
relatorEvenTowerGeneratedLevelsAsLevelIdentification
ThreeFlavorRelatorEvenTowerParameterTable
ThreeFlavorRelatorEvenTowerLevelIdentification
ThreeFlavorRelatorEvenTowerAudit
relatorEvenTowerComponentsAsSourceCertificate
relatorEvenTowerComponents_discharge_sourceCertificateNeed
relatorEvenTowerSourceCertificateAsMassSquaredLaw
ThreeFlavorRelatorEvenTowerMassSquaredLaw
relatorEvenTowerMassSquaredLawAsConvexity
relatorEvenTowerMassSquaredLaw_discharge_massSquaredConvexityNeed
relatorEvenTowerMassSquaredLawAsQNFLowerHalfCriterion
relatorEvenTowerMassSquaredLawAsAlignedHalfNumeralInterval
relatorEvenTowerMassSquaredLaw_alignedHalfInterval_upper_le_half
relatorEvenTowerMassSquaredLaw_discharge_qnfNumeralIntervalUpperHalfNeed
relatorEvenTowerSourceCertificateAsAlignedHalfNumeralInterval
relatorEvenTowerSourceCertificate_alignedHalfInterval_upper_le_half
relatorEvenTowerSourceCertificate_discharge_qnfNumeralIntervalUpperHalfNeed
relatorEvenTowerComponentsAsAlignedHalfNumeralInterval
relatorEvenTowerComponents_alignedHalfInterval_upper_le_half
relatorEvenTowerComponents_discharge_qnfNumeralIntervalUpperHalfNeed
relatorEvenTowerNumeralComponentsAsAlignedHalfNumeralInterval
relatorEvenTowerNumeralComponents_alignedHalfInterval_upper_le_half
relatorEvenTowerNumeralComponents_discharge_qnfNumeralIntervalUpperHalfNeed
relatorEvenTowerNumeralGeneratedLevels_discharge_qnfNumeralIntervalUpperHalfNeed
relatorEvenTowerNumeralGeneratedLevelFunction_discharge_qnfNumeralIntervalUpperHalfNeed
relatorEvenTowerNumeralSourceReadback_discharge_qnfNumeralIntervalUpperHalfNeed
relatorEvenTowerNumeralThreePointReadback_discharge_qnfNumeralIntervalUpperHalfNeed
relatorEvenTowerNumeralThreePointReadbackAsAlignedHalfNumeralInterval
relatorEvenTowerNumeralThreePointReadback_alignedHalfInterval_upper_le_half
relatorEvenTowerNumeralThreePointReadback_alignedHalfInterval_contains_gapRatio
ThreeFlavorRelatorEvenTowerThreePointReadoutPackage
relatorEvenTowerThreePointReadoutPackageAsAlignedHalfNumeralInterval
relatorEvenTowerThreePointReadoutPackage_alignedHalfInterval_upper_le_half
relatorEvenTowerThreePointReadoutPackage_alignedHalfInterval_contains_gapRatio
relatorEvenTowerThreePointReadoutPackage_discharge_qnfNumeralIntervalUpperHalfNeed
ThreeFlavorRelatorEvenTowerQNFReadoutCertificate
relatorEvenTowerReadoutPackageAsQNFReadoutCertificate
NeedsThreeFlavorRelatorEvenTowerQNFReadoutCertificate
relatorEvenTowerReadoutPackage_discharge_qnfReadoutCertificateNeed
relatorEvenTowerQNFReadoutCertificate_discharge_qnfNumeralIntervalUpperHalfNeed
relatorEvenTowerQNFReadoutCertificate_interval_contains_gapRatio
relatorEvenTowerQNFReadoutCertificate_interval_upper_le_half
ThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint
relatorEvenTowerQNFReadoutCertificateAsSingletonEndpoint
relatorEvenTowerReadoutPackageAndSingletonAsEndpoint
ThreeFlavorRelatorEvenTowerEndpointInput
relatorEvenTowerEndpointInputAsSingletonEndpoint
NeedsThreeFlavorRelatorEvenTowerEndpointInput
relatorEvenTowerEndpointInput_discharge_endpointNeed
relatorEvenTowerEndpointInput_discharge_endpointInputNeed
relatorEvenTowerEndpointInput_interval_contains_gapRatio
relatorEvenTowerEndpointInput_interval_upper_le_half
ThreeFlavorRelatorEvenTowerPrimitiveEndpointRows
relatorEvenTowerPrimitiveEndpointRowsAsNumeralParameterTable
relatorEvenTowerPrimitiveEndpointRowsAsThreePointReadback
relatorEvenTowerPrimitiveEndpointRowsAsAudit
relatorEvenTowerPrimitiveEndpointRowsAsEndpointInput
relatorEvenTowerPrimitiveEndpointRowsAsSingletonEndpoint
relatorEvenTowerPrimitiveEndpointRows_interval_contains_gapRatio
relatorEvenTowerPrimitiveEndpointRows_interval_upper_le_half
relatorEvenTowerPrimitiveEndpointRows_hasCurrentStandingEvaluation
relatorEvenTowerPrimitiveEndpointRows_discharge_singletonEndpointNeed
NeedsThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint
relatorEvenTowerQNFReadoutCertificate_discharge_singletonEndpointNeed
relatorEvenTowerReadoutPackageAndSingleton_discharge_singletonEndpointNeed
relatorEvenTowerSingletonReadoutEndpoint_interval_contains_gapRatio
relatorEvenTowerSingletonReadoutEndpoint_interval_upper_le_half
relatorEvenTowerSingletonReadoutEndpoint_hasCurrentStandingEvaluation
```

It encodes the AASC-translated even-tower shape

```text
level(k) = scale * k^4 * (1 + beta * k^2 + delta * k^4)
for k = 1, 3, 5
```

at the three mass-squared levels.  With `scale >= 0`, `beta >= 0`, and
`delta >= 0`, Lean proves the second finite difference is nonnegative because

```text
level(1) - 2*level(3) + level(5)
  = scale * (464 + 14168*beta + 377504*delta).
```

This discharges:

```lean
NeedsThreeFlavorMassSquaredConvexity
```

when the following guards are supplied:

- the even-tower law has been translated into AASC form,
- the law is same-scope with the neutrino mass-squared levels,
- no empirical Relator import is used,
- no Relator-sector fit tuning is used.

This does not treat the external Relator paper as proof authority.  It creates
an audit-ready socket: if the corpus/source package certifies those guarded
premises, the readout chain can start from mass-squared convexity without
requiring the stronger square/Gram finite-coordinate witness.

The composed readout bridge is now Lean-checked:

```text
Relator even tower
  -> mass-squared convexity
  -> two-step gap half dominance
  -> adjacent gap half side
  -> midpoint gap compression
  -> normalized middle half compression
  -> QNF lower-half criterion
  -> aligned [0, 1/2] numeral interval
```

Thus, under the guarded Relator even-tower source law, Lean discharges:

```lean
NeedsThreeFlavorQNFNumeralIntervalUpperHalf
```

The remaining readout blocker is now upstream of this bridge: certify the
Relator even-tower mass-squared law itself as AASC same-scope/source-derived,
with nonnegative `scale`, `beta`, and `delta`, rather than merely importing the
external terminology.

The upstream source certificate has now been factored into its own object:

```lean
ThreeFlavorRelatorEvenTowerSourceCertificate
```

It requires:

- the three level equations for the `k = 1, 3, 5` even-tower law,
- nonnegativity of `scale`, `beta`, and `delta`,
- a source-derived parameter table,
- a source-fixed exponent schedule,
- same-scope targeting of the three neutrino mass-squared levels,
- no empirical import,
- no fit tuning,
- no hidden encoding of the selected root in the parameters.

This source certificate converts into the Relator mass-squared law and now
discharges the QNF upper-half interval need directly.  The remaining obligation
has therefore narrowed again: supply or construct this source certificate from
the AASC corpus/source package.

The source certificate has also been decomposed into smaller constructor
inputs:

```lean
ThreeFlavorRelatorEvenTowerParameterTable
ThreeFlavorRelatorEvenTowerLevelIdentification
ThreeFlavorRelatorEvenTowerAudit
```

These components assemble via:

```lean
relatorEvenTowerComponentsAsSourceCertificate
relatorEvenTowerComponents_discharge_sourceCertificateNeed
relatorEvenTowerComponents_discharge_qnfNumeralIntervalUpperHalfNeed
```

So the current concrete fill-in list is:

1. parameter table: rational `beta`, `delta`, and `scale`, with nonnegativity;
2. source provenance: the parameter table is source-derived and does not hide
   the selected root;
3. level identification: the three mass-squared levels equal the `k = 1,3,5`
   even-tower expressions;
4. exponent provenance: the exponent schedule is fixed by source, not fitted;
5. audit: no empirical import and no fit tuning.

Once those pieces are supplied, Lean carries them through to the aligned
`[0,1/2]` QNF interval without any further bridge work.

The parameter table now also has a concrete numeral-entry route:

```lean
ThreeFlavorRelatorEvenTowerNumeralParameterTable
```

This object takes natural numerators and positive natural denominators for
`beta`, `delta`, and `scale`.  Lean converts those into rational parameters and
proves nonnegativity automatically.  Therefore the remaining numeric input is
now displayed as concrete fractions, not arbitrary rational fields.

The numeral route composes all the way to:

```lean
relatorEvenTowerNumeralComponents_discharge_qnfNumeralIntervalUpperHalfNeed
```

So a source can now provide:

```text
beta = betaNumerator / betaDenominator
delta = deltaNumerator / deltaDenominator
scale = scaleNumerator / scaleDenominator
```

plus the three mass-level equations and audit guards, and Lean derives the
aligned `[0,1/2]` QNF interval.

The three mass-level equations have also been partially mechanized through the
generated-level expression:

```lean
relatorEvenTowerLevelExpression
ThreeFlavorRelatorEvenTowerGeneratedLevels
```

Lean proves the expansions for `k = 1`, `k = 3`, and `k = 5`:

```lean
relatorEvenTowerLevelExpression_one
relatorEvenTowerLevelExpression_three
relatorEvenTowerLevelExpression_five
```

Thus a source no longer has to write the expanded `81`, `729`, `6561`, etc.
equations directly.  It can certify that the three levels are generated by the
single formula

```text
scale * k^4 * (1 + beta*k^2 + delta*k^4)
```

at `k = 1,3,5`, and Lean expands that into the level-identification object.
The endpoint theorem is:

```lean
relatorEvenTowerNumeralGeneratedLevels_discharge_qnfNumeralIntervalUpperHalfNeed
```

The generated-level input has been compressed one step further into a finite
level-function object:

```lean
ThreeFlavorRelatorEvenTowerGeneratedLevelFunction
```

This uses the fixed index map:

```lean
relatorEvenTowerFlavorIndex : Nat -> ℚ
```

with `0 -> 1`, `1 -> 3`, and `2 -> 5`.  Since the algebra's mass-squared
levels are indexed by `Fin 3`, the source only has to give a finite readback
function on the three flavor positions and prove that it agrees with the
even-tower expression at the fixed indices.  Lean then constructs the generated
levels and discharges the QNF upper-half interval need via:

```lean
relatorEvenTowerNumeralGeneratedLevelFunction_discharge_qnfNumeralIntervalUpperHalfNeed
```

Current minimal source payload:

1. displayed nonnegative rational numerals for `beta`, `delta`, and `scale`;
2. source readback showing `A.massSquaredLevelOf i` equals the even-tower
   expression at the fixed index `1,3,5` for each `i : Fin 3`;
3. audit guards: source-derived, same-scope, exponent schedule fixed by source,
   no empirical import, no fit tuning, no hidden root encoding.

This shortest route is represented by:

```lean
ThreeFlavorRelatorEvenTowerSourceReadback
relatorEvenTowerNumeralSourceReadback_discharge_qnfNumeralIntervalUpperHalfNeed
```

It removes the need to separately provide an intermediate generated-level
function.  The function is now constructed internally as the even-tower
expression itself.

For source extraction, the finite readback has also been exposed as an explicit
three-row table:

```lean
ThreeFlavorRelatorEvenTowerThreePointReadback
relatorEvenTowerNumeralThreePointReadback_discharge_qnfNumeralIntervalUpperHalfNeed
```

This is the most concrete current input form.  It asks for exactly:

```text
level 0 = evenTower(1)
level 1 = evenTower(3)
level 2 = evenTower(5)
```

plus the displayed parameter numerals and audit guards.  Lean converts the
three rows into the finite `Fin 3` readback and then into the QNF interval.

The three-row route now also produces the interval object directly:

```lean
relatorEvenTowerNumeralThreePointReadbackAsAlignedHalfNumeralInterval
```

with the bound theorem:

```lean
relatorEvenTowerNumeralThreePointReadback_alignedHalfInterval_upper_le_half
```

Thus the concrete artifact available to the manuscript is not merely that a
need is discharged, but an explicit aligned rational interval object whose
upper endpoint is certified to be at most `1/2`.

The interval also now has a direct containment theorem:

```lean
relatorEvenTowerNumeralThreePointReadback_alignedHalfInterval_contains_gapRatio
```

This records that the constructed interval contains the three-flavor gap ratio
readout, using the closed-root presentation's selected-root readback.

The remaining source payload is now packaged as:

```lean
ThreeFlavorRelatorEvenTowerThreePointReadoutPackage
```

This single object contains:

- the gap-ratio algebra pass certificate,
- strict mass-squared ordering,
- displayed numeral parameters,
- the three-point readback rows,
- the Relator audit guards.

From that one package, Lean constructs the aligned interval, proves containment
of the gap-ratio readout, proves the upper-half bound, and discharges the QNF
upper-half interval need.

The package output is now bundled into a single readout certificate:

```lean
ThreeFlavorRelatorEvenTowerQNFReadoutCertificate
relatorEvenTowerReadoutPackageAsQNFReadoutCertificate
```

This certificate carries:

- the source-facing three-point readout package,
- the QNF/root alignment,
- the constructed numeral interval,
- proof the interval equals the package-generated interval,
- proof the interval contains the gap-ratio readout,
- proof the upper endpoint is at most `1/2`,
- proof the QNF upper-half interval need is discharged.

So the next instantiation target is now clean: construct one
`ThreeFlavorRelatorEvenTowerThreePointReadoutPackage`, supply QNF alignment,
and Lean returns one readout certificate.

The readout certificate is now also a first-class blocker target:

```lean
NeedsThreeFlavorRelatorEvenTowerQNFReadoutCertificate
relatorEvenTowerReadoutPackage_discharge_qnfReadoutCertificateNeed
```

and it has projection theorems for the downstream claims:

```lean
relatorEvenTowerQNFReadoutCertificate_discharge_qnfNumeralIntervalUpperHalfNeed
relatorEvenTowerQNFReadoutCertificate_interval_contains_gapRatio
relatorEvenTowerQNFReadoutCertificate_interval_upper_le_half
```

This means manuscript claims can cite the certificate itself and then project
the needed consequences, rather than re-running the construction chain in each
statement.

The singleton/readout endpoint is now also bundled:

```lean
ThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint
relatorEvenTowerQNFReadoutCertificateAsSingletonEndpoint
```

This combines:

- a hybrid joint restriction singleton,
- the Relator/QNF readout certificate,
- the current standing ratio evaluation produced from singleton plus gap
  algebra,
- the certified interval consequences.

Projection theorems expose:

```lean
relatorEvenTowerSingletonReadoutEndpoint_interval_contains_gapRatio
relatorEvenTowerSingletonReadoutEndpoint_interval_upper_le_half
relatorEvenTowerSingletonReadoutEndpoint_hasCurrentStandingEvaluation
```

So the top-level remaining construction target is now:

1. instantiate `ThreeFlavorRelatorEvenTowerThreePointReadoutPackage`;
2. supply QNF alignment;
3. supply `HybridJointRestrictionSingleton H`.

Lean then returns a current-standing evaluation plus the certified readout
interval.

There is now also a direct constructor for that exact target:

```lean
relatorEvenTowerReadoutPackageAndSingletonAsEndpoint
relatorEvenTowerReadoutPackageAndSingleton_discharge_singletonEndpointNeed
```

It takes the three source-facing ingredients directly:

```text
readout package + QNF alignment + hybrid singleton
```

and returns the singleton/readout endpoint.

The same ingredients are now bundled as a single endpoint input:

```lean
ThreeFlavorRelatorEvenTowerEndpointInput
relatorEvenTowerEndpointInputAsSingletonEndpoint
```

This object contains:

```text
readout package + QNF alignment + hybrid singleton
```

and projects the interval consequences directly:

```lean
relatorEvenTowerEndpointInput_interval_contains_gapRatio
relatorEvenTowerEndpointInput_interval_upper_le_half
```

This is the current cleanest top-level construction target.

The top-level target has now also been expanded into raw primitive rows:

```lean
ThreeFlavorRelatorEvenTowerPrimitiveEndpointRows
```

This single object carries:

- gap-ratio algebra pass,
- strict mass-squared ordering,
- QNF alignment,
- hybrid singleton,
- displayed `beta`, `delta`, and `scale` numerators/denominators,
- source/no-hidden-root guards for the parameter table,
- the three source readback rows `level0=evenTower(1)`,
  `level1=evenTower(3)`, `level2=evenTower(5)`,
- exponent/same-scope guards,
- no empirical import and no fit tuning.

Lean converts these rows through:

```lean
relatorEvenTowerPrimitiveEndpointRowsAsEndpointInput
relatorEvenTowerPrimitiveEndpointRowsAsSingletonEndpoint
```

and projects:

```lean
relatorEvenTowerPrimitiveEndpointRows_interval_contains_gapRatio
relatorEvenTowerPrimitiveEndpointRows_interval_upper_le_half
relatorEvenTowerPrimitiveEndpointRows_hasCurrentStandingEvaluation
```

This is now the most source-facing instantiation point: fill the primitive rows
and the full singleton/readout endpoint follows.

## External Row-Data Import for the AASC Readout Endpoint

The cited Zenodo neutrino hierarchy source has now been translated into
Lean-side row data.  This section records provenance for the row import only;
the structural endpoint is the AASC standing-admission/readout pipeline above.
The relevant external source package is:

```text
DOI: 10.5281/zenodo.17169926
File: Neutrinos Mass Hierarchy.py
Paper file: Mass-Hierarchy-Neutrinos.pdf
```

The source code supplies the closed coefficient pipeline:

```text
P_{1/R}(k) = 1 + beta k^2 + delta k^4
k = 1, 3, 5
R branch off
```

with finite-decimal source readback:

```text
beta  = 0.0000780161359733586
delta = 0.0119354363008418
scale = 1
```

Lean records these source numerals as rationals in provenance-specific objects:

```lean
pajuhaanZenodoRelatorBeta
pajuhaanZenodoRelatorDelta
pajuhaanZenodoRelatorScale
pajuhaanZenodoRelatorP1OverR
pajuhaanZenodoRelatorMassSquaredLevel
pajuhaanZenodoRelatorNumeralParameterTable
```

The source provenance is no longer an anonymous `True` guard.  It is carried by:

```lean
PajuhaanZenodoCoefficientPipelineSourceDerived
PajuhaanZenodoNoNeutrinoMassOrSplittingInputInCoefficientPipeline
PajuhaanZenodoNoHiddenSelectedRootEncodingInSourceRows
pajuhaanZenodoCoefficientPipelineSourceDerived_proof
pajuhaanZenodoNoNeutrinoMassOrSplittingInputInCoefficientPipeline_proof
pajuhaanZenodoNoHiddenSelectedRootEncodingInSourceRows_proof
```

The coordinate convention is important:

```text
AASC standing coordinate: rho = solar / atmospheric
Pajuhaan printed coordinate: R31 = atmospheric / solar
```

Thus the printed hierarchy readout is the inverse of the AASC standing
coordinate.  Lean records the bridge as:

```lean
pajuhaanZenodoAASCStandingRatioReadout
pajuhaanZenodoR31DecimalReadout
pajuhaanZenodoR3ellDecimalReadout
pajuhaanZenodoR31_eq_R3ell_plus_half
pajuhaanZenodoAASCStandingRatioReadout_eq_inv_R31
pajuhaanZenodoAASCStandingRatioReadout_eq_inv_R3ell_plus_half
```

The source-row computation gives certified rational windows:

```text
0.0299486814926010 <= rho_source <= 0.0299486814926012
33.3904516045907 <= R31_source <= 33.3904516045908
32.8904516045907 <= R3ell_source <= 32.8904516045908
```

with Lean proofs:

```lean
pajuhaanZenodoRelatorSourceGapRatio_in_decimalWindow
pajuhaanZenodoRelatorSourceInverseHierarchyRatio_in_decimalWindow
pajuhaanZenodoRelatorSourceR3ellRatio_in_decimalWindow
```

The historical source-row admission bridge is:

```lean
PajuhaanZenodoRelatorAASCAdmissionRows
pajuhaanZenodoRelatorAASCAdmissionRowsAsPrimitiveEndpointRows
pajuhaanZenodoRelatorAASCAdmissionRowsAsSingletonEndpoint
pajuhaanZenodoRelatorAASCAdmissionRows_discharge_singletonEndpointNeed
pajuhaanZenodoRelatorAASCAdmissionRows_hasCurrentStandingEvaluation
```

This bridge says: if the standing AASC three-flavor algebra reads back to the
cited source-generated `k = 1, 3, 5` rows, then the existing AASC/QNF singleton
endpoint machinery applies.  In the current manuscript-facing layer this is
not the endpoint name; it is the provenance-specific implementation under the
neutral AASC interface.

The final bundled certificate is:

```lean
PajuhaanZenodoRelatorAASCReadoutCertificate
pajuhaanZenodoRelatorAASCReadoutCertificate
NeedsPajuhaanZenodoRelatorAASCReadoutCertificate
pajuhaanZenodoRelatorAASCAdmissionRows_discharge_readoutCertificateNeed
```

Projection theorems expose the manuscript-facing claims:

```lean
pajuhaanZenodoRelatorAASCReadoutCertificate_gapRatio_in_decimalWindow
pajuhaanZenodoRelatorAASCReadoutCertificate_selectedRoot_in_decimalWindow
pajuhaanZenodoRelatorAASCReadoutCertificate_inverseHierarchy_in_decimalWindow
pajuhaanZenodoRelatorAASCReadoutCertificate_selectedRoot_inverse_in_decimalWindow
pajuhaanZenodoRelatorAASCReadoutCertificate_r3ell_in_decimalWindow
pajuhaanZenodoRelatorAASCReadoutCertificate_selectedRoot_r3ell_in_decimalWindow
```

The compact endpoint theorem is:

```lean
pajuhaanZenodoRelatorAASCAdmissionRows_finalNumericalReadout
```

It proves, from admitted same-scope Pajuhaan rows:

```text
CurrentStandingRatioEvaluation exists.
0.0299486814926010 <= selectedRoot <= 0.0299486814926012.
33.3904516045907 <= selectedRoot^{-1} <= 33.3904516045908.
32.8904516045907 <= selectedRoot^{-1} - 1/2 <= 32.8904516045908.
```

Build/provenance status:

```text
lake build MaleyLean.Papers.Neutrino: passes.
No sorry/admit/axiom/unsafe occurrence was found in MathlibSpectralOperator.lean.
Only the pre-existing unrelated `simpa` linter warning remains.
```

Previously recorded broad premise:

```text
PajuhaanZenodoRelatorAASCAdmissionRows
```

This is the provenance-specific same-scope admission object.  It is no longer
the manuscript-facing active endpoint.  The current active endpoint is the
stronger neutral AASC certificate:

```lean
AASCNeutrinoSourceRowStandingAdmission
```

That certificate constructs:

```lean
AASCNeutrinoReadoutSameScopeAdmissionRows
```

and then proves the final readout through:

```lean
AASCNeutrinoSourceRowStandingAdmission.finalNumericalReadout
```

So the source import is now properly relegated to row-data provenance.  The
structural work is the AASC same-scope standing certificate and the Lean
transport/readout pipeline.

## Manuscript Claim to Lean Object Map

| Manuscript claim | Lean object |
| --- | --- |
| Cited external source file and DOI provenance are recorded. | `pajuhaanZenodoRecordDOI`, `pajuhaanZenodoSourceCodeFile`, `AASCNeutrinoCoefficientPipelineSourceDerived` |
| Source coefficient pipeline is not an empirical neutrino fit/import. | `PajuhaanZenodoNoNeutrinoMassOrSplittingInputInCoefficientPipeline` |
| Source rows do not hide the selected AASC root. | `PajuhaanZenodoNoHiddenSelectedRootEncodingInSourceRows` |
| Source coefficients are concrete rationals. | `aascNeutrinoBeta`, `aascNeutrinoDelta`, `aascNeutrinoScale`, `aascNeutrinoNumeralParameterTable` |
| Admitted AASC source-row law at `k = 1, 3, 5`. | `aascNeutrinoP1OverR`, `aascNeutrinoMassSquaredLevel` |
| Printed `R31` and printed `R3ell` differ by `1/2`. | `pajuhaanZenodoR31_eq_R3ell_plus_half` |
| AASC coordinate is reciprocal to printed `R31`. | `aascNeutrinoStandingRatioReadout_eq_inv_R31` |
| Source rows compute the AASC `rho` decimal window. | `aascNeutrinoSourceGapRatio_in_decimalWindow` |
| Source rows compute the inverse hierarchy `R31` decimal window. | `aascNeutrinoSourceInverseHierarchyRatio_in_decimalWindow` |
| Source rows compute the shifted `R3ell` decimal window. | `aascNeutrinoSourceR3ellRatio_in_decimalWindow` |
| Corpus-shaped AASC standing admission certificate. | `AASCNeutrinoSourceRowStandingAdmission` |
| Standing admission constructs broad row admission. | `AASCNeutrinoSourceRowStandingAdmission.toSameScopeAdmissionRows` |
| Broad row-admission need is discharged. | `AASCNeutrinoSourceRowStandingAdmission.discharge_sameScopeAdmissionRows` |
| Final bundled readout certificate. | `AASCNeutrinoNumericalReadoutCertificate` |
| Final compact theorem. | `AASCNeutrinoSourceRowStandingAdmission.finalNumericalReadout` |

Superseded manuscript wording:

```text
Lean4 formalization provenance is available in
MaleyLean.Papers.Neutrino.SourceTheorems.MathlibSpectralOperator.
The local build `lake build MaleyLean.Papers.Neutrino` passes in this
workspace.  The provenance-specific row bridge is conditional on the
same-scope AASC admission object
`PajuhaanZenodoRelatorAASCAdmissionRows`; conditional on that admission,
Lean proves the corresponding numerical windows in
`pajuhaanZenodoRelatorAASCAdmissionRows_finalNumericalReadout`.
```

The wording above is kept only as a historical note from the provenance-specific
bridge stage.  Use the updated wording below in the manuscript.

Updated manuscript wording:

```text
Lean4 formalization provenance is available in
MaleyLean.Papers.Neutrino.SourceTheorems.MathlibSpectralOperator.
The local build `lake build MaleyLean.Papers.Neutrino` passes in this
workspace.  The cited external source is used as provenance and row data only.
The manuscript-facing endpoint is the AASC standing-admission certificate
`AASCNeutrinoSourceRowStandingAdmission`; from that certificate Lean constructs
`AASCNeutrinoReadoutSameScopeAdmissionRows` and proves the final numerical
windows in `AASCNeutrinoSourceRowStandingAdmission.finalNumericalReadout`.
```

## 2026-05-29 AASC source-row standing discharge

The broad same-scope row socket has now been narrowed to a corpus-shaped AASC
standing certificate.

New Lean objects:

```lean
AASCNeutrinoSourceRowStandingAdmission
AASCNeutrinoSourceRowStandingAdmission.sameScopeReadbackAudit
AASCNeutrinoSourceRowStandingAdmission.sameScopeReadbackAudit_proof
AASCNeutrinoSourceRowStandingAdmission.toSameScopeAdmissionRows
NeedsAASCNeutrinoReadoutSameScopeAdmissionRows
AASCNeutrinoSourceRowStandingAdmission.discharge_sameScopeAdmissionRows
AASCNeutrinoSourceRowStandingAdmission.finalNumericalReadout
```

This moves the active premise from a bare row-admission name to an explicit
AASC certificate whose fields are:

```text
finite PMNS invariant witness scope
mass-squared splitting witness standing
same-scope oscillation rival exhaustion
bridge-anchor admissibility for row readback
evidence-ledger completeness for readout
source rows in the same standing carrier
quotient/skin transport compatibility
no empirical neutrino mass/splitting import
no hidden selected-root encoding
level 0/1/2 equality with the k=1,3,5 source rows
QNF alignment
hybrid singleton
strict mass-squared ordering
```

So the current honest status is no longer:

```text
Assume AASCNeutrinoReadoutSameScopeAdmissionRows.
```

It is:

```text
Given AASCNeutrinoSourceRowStandingAdmission, Lean constructs
AASCNeutrinoReadoutSameScopeAdmissionRows and then proves the final numerical
windows.
```

Build status after the discharge:

```text
lake build MaleyLean.Papers.Neutrino: passes.
No sorry/admit/axiom/unsafe occurrence was found in MathlibSpectralOperator.lean.
Only the pre-existing unrelated `simpa` linter warning remains.
```
