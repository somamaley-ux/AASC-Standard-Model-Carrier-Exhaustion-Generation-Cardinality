# Riemann Hypothesis AASC/Lean Reduction Handoff

This folder contains the AASC-native zero-interior rigidity development for
the Riemann zeta interface.

## Strongest Formal Framing

The Lean development now records the AASC/kernel-forcing route for the Riemann
zeta interface:

1. Canonical standing is definitionally identified with nontrivial analytic
   zeta zerohood, not with critical-line support.
2. A classical off-line zerohood candidate is target-preserving zerohood; it
   cannot simultaneously be a target-leaving object.
3. Target-leaving candidates are degenerate/out of same-regime standing.
4. The kernel paper proves that constructional same-regime use forces the
   kernel, and that no faithful same-regime counterexample can sit strictly
   below a realized kernel.
5. Once the AASC kernel applies, same-domain off-line selector standing is
   blocked, yielding the RH endpoint.

The main new audit theorems are:

```lean
classical_off_line_zerohood_is_target_preserving
classical_zerohood_target_leaving_impossible
constructional_use_forces_kernel_package
no_faithful_same_regime_counterexample_below_kernel
classical_zeta_zerohood_construction_forces_kernel
no_classical_zeta_zerohood_same_regime_counterexample_below_kernel
mathlib_riemannHypothesis_from_target_preserving_aasc
```

The theorem `mathlib_riemannHypothesis_from_target_preserving_aasc` is the
paper-facing closure statement for the AASC reading: if target-preserving
classical zeta zerohood is evaluated as a non-degenerate AASC same-regime
object, then mathlib's `RiemannHypothesis` follows.  The companion
same-regime counterexample theorem shows that a faithful below-kernel
alternative cannot be constructed.

The older reduction theorem is still present for hostile audit:

```lean
remaining_clay_object_iff_mathlib_riemannHypothesis
```

It shows that the raw selector/kernel certificate object has exactly
RH-strength.  The stronger current framing explains why, in the AASC kernel
formalism, faithful target-preserving zerohood is not allowed to remain outside
the kernel.

## Zeta-Specific Bridge Workbench

The file:

```text
MaleyLean/Papers/RiemannHypothesis/BridgeProgram.lean
```

defines the canonical off-line selector:

```lean
canonicalOffLineHorizontalSelector
```

and the canonical fixed-by-invariant-bundle predicate:

```lean
canonicalCriticalLineFixedByInvariantBundle
```

The exact hard sub-obligation is:

```lean
CanonicalSelectorFixednessSubobligation
```

Lean proves:

```lean
canonical_selector_fixedness_iff_mathlib_riemannHypothesis
```

So the next proof target is not merely more generic AASC support.  It is the
zeta-specific theorem that any standing-bearing off-line selected zero is
already invariant-fixed.  That theorem is exactly RH-strength.

If supplied, it constructs the remaining object:

```lean
remaining_clay_object_from_canonical_selector_fixedness
```

The corpus-style standing-collapse extrapolation is isolated as:

```lean
IllicitStandingCollapseExtrapolation
```

It has two substantive fields:

```lean
off_line_selector_is_illicit
illicit_selector_collapses_standing
```

From those fields Lean proves:

```lean
canonical_selector_fixedness_from_illicit_standing_collapse
remaining_clay_object_from_illicit_standing_collapse
mathlib_riemannHypothesis_from_illicit_standing_collapse
```

This is the formal logical extrapolation from the corpus pattern: illicit
coordinate/selector moves collapse standing.  The still-live proof burden is
to justify the two fields for classical zeta without assuming RH.

The matrix also supports the sharper illicit-or-scope-change fork:

```lean
IllicitOrScopeChangeExtrapolation
```

Its substantive fields are:

```lean
off_line_selector_is_illicit_or_scope_change
illicit_selector_collapses_standing
scope_change_cannot_preserve_same_domain_standing
```

From those fields Lean proves:

```lean
canonical_selector_fixedness_from_illicit_or_scope_change
remaining_clay_object_from_illicit_or_scope_change
mathlib_riemannHypothesis_from_illicit_or_scope_change
```

This records the corpus pattern that an off-line selector must either remain a
same-domain move, in which case illicit standing collapse applies, or else be a
scope change, in which case it cannot refute the same-domain zeta/RH endpoint.

The standing-localization layer from "Standing Localization under Realized
Persistence" is isolated as:

```lean
RealizedPersistenceStandingBridge
```

It classifies a standing off-line selector as one of the blocked
localization-failure modes:

```lean
GlobalStandingFailure
DiffuseStandingFailure
TraceOnlyFailure
ExternalRepairFailure
DefaultRepresentativeSelection
```

From the classification and branch eliminators, Lean proves:

```lean
canonical_selector_fixedness_from_realized_persistence_bridge
remaining_clay_object_from_realized_persistence_bridge
mathlib_riemannHypothesis_from_realized_persistence_bridge
```

This records the fixed-domain localization rule: standing-bearing persistence
cannot remain global, diffuse, trace-only, externally repaired, envelope-drifting,
or representative-selected while still serving as a same-domain standing
counterexample.

The same-scope operator-exhaustion layer is isolated as:

```lean
OperatorExhaustionZetaBridge
```

It classifies the off-line zeta selector as an attempted same-scope operator in
one of these cases:

```lean
StandingFixedBookkeepingOperator
ImportedOperatorDatum
SameScopeTotalization
PostHocOperatorRepair
AMetricOperatorSelection
```

From that classification and the branch eliminators, Lean proves:

```lean
canonical_selector_fixedness_from_operator_exhaustion
remaining_clay_object_from_operator_exhaustion
mathlib_riemannHypothesis_from_operator_exhaustion
```

This records the operator-exhaustion rule: standing-fixed same-scope operator
content is bookkeeping/invariant-fixed, while imported data, totalization,
post-hoc repair, and AMetric selection cannot produce same-domain standing.

The Exactness ARC freedom-ledger layer is isolated as:

```lean
ExactnessArcZetaBridge
```

It classifies the off-line zeta readout as carrying one of these unresolved
freedoms:

```lean
RepresentativeFreedom
EndpointBoundaryFreedom
TotalizationFreedom
DomainExtensionFreedom
ExtractionReadoutFreedom
CalibrationProxyFreedom
```

From that classification and the branch eliminators, Lean proves:

```lean
canonical_selector_fixedness_from_exactness_arc
remaining_clay_object_from_exactness_arc
mathlib_riemannHypothesis_from_exactness_arc
```

This records the Exactness ARC rule: representative, endpoint, totalization,
domain-extension, extraction/readout, or calibration/proxy freedom blocks
promotion to a same-domain standing endpoint unless discharged.

The structural AASC endpoint proved from an explicit certificate is:

```lean
aasc_standing_zero_interior_rigidity
```

In a non-degenerate standing-bearing zeta regime, a standing-bearing
nontrivial zero-support cannot remain off the critical line.

The hostile-referee bridge point is discharged by:

```lean
classicalZetaZerohoodStanding
classical_zeta_standing_zerohood_equivalence
aasc_zerohood_endpoint_iff_mathlib_riemannHypothesis
```

`classicalZetaZerohoodStanding` is exactly nontrivial analytic zeta zerohood:

```lean
fun s => ((Not (exists n : Nat, s = -2 * (n + 1))) /\ s ≠ 1) /\
  riemannZeta s = 0
```

The bridge theorem is definitional:

```lean
{ standing_iff_nontrivial_zerohood := fun s => Iff.rfl }
```

Therefore the AASC endpoint for canonical standing-as-zerohood is formally
equivalent to mathlib's `RiemannHypothesis`.  This is an equivalence/reduction
statement, not an unconditional construction of the zeta-specific certificate.

## Faithful Same-Regime Counterexample Test

The current Lean development includes a direct attempt to break the AASC
solution by postulating a faithful same-regime construction below the kernel.
The imported kernel paper blocks this:

```lean
no_classical_zeta_zerohood_same_regime_counterexample_below_kernel
```

In corpus language: a purported off-line classical zerohood counterexample must
either leave the target/regime, in which case it is degenerate and not a
same-regime counterexample, or preserve the target/regime, in which case the
kernel is forced.  A faithful same-regime below-kernel counterexample is not
available.

## Referee Print Packet

Run:

```text
lake env lean Checks\Axiom\RiemannHypothesisBridgePrint.lean
```

Captured output:

```text
Checks/Axiom/RiemannHypothesisBridgePrint.out.txt
```

The output prints:

```lean
#print classicalZetaZerohoodStanding
#print classical_zeta_standing_zerohood_equivalence
#print axioms classical_zeta_standing_zerohood_equivalence
#print aasc_zerohood_endpoint_iff_mathlib_riemannHypothesis
#print axioms aasc_zerohood_endpoint_iff_mathlib_riemannHypothesis
```

The axiom traces list only Lean's standard classical background axioms:
`propext`, `Classical.choice`, and `Quot.sound`.  They do not introduce an
RH-specific axiom, a critical-line axiom, or an axiom asserting
`RiemannHypothesis`.

## Manuscript Draft

The LaTeX handoff draft is:

```text
MaleyLean/Papers/RiemannHypothesis/RH_AASC_ZeroInterior_Solution_Draft.tex
```

It records the AASC kernel instantiation, global uniqueness import, selector
exclusion, canonical standing/zerohood bridge, and verification commands.

## Verification

```text
lake build MaleyLean.Papers.RiemannHypothesis
lake build MaleyLean
lake env lean Checks\Axiom\RiemannHypothesisAxiomCheck.lean
lake env lean Checks\Axiom\RiemannHypothesisBridgePrint.lean
```
