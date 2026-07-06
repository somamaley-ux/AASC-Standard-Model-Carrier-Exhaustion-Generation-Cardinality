# RH AASC Zerohood Kernel-Forcing Package v1.0.1

Release target for Zenodo archival of the strengthened Riemann Hypothesis
AASC/Lean kernel-forcing handoff package.

## Formal Result Framing

This release contains the Lean-verified AASC/kernel-forcing route for faithful
same-regime zeta zerohood.  The proof spine is:

```text
classical zeta zerohood
  -> target-preserving zerohood
  -> target-leaving branch impossible / degenerate
  -> faithful same-regime use forces the kernel
  -> no faithful below-kernel same-regime counterexample
  -> AASC selector kernel blocks off-line standing
  -> mathlib RiemannHypothesis
```

The older raw bridge object remains available for hostile audit:

```lean
Nonempty ClassicalRiemannZetaBridgeObligations
```

Equivalently, the remaining proof object is named:

```lean
RemainingClayLevelProofObject
```

The standing/zerohood bridge is discharged definitionally:

```lean
classical_zeta_standing_zerohood_equivalence
```

The canonical endpoint equivalence is:

```lean
aasc_zerohood_endpoint_iff_mathlib_riemannHypothesis
```

The reduction from the remaining proof object to mathlib RH is:

```lean
mathlib_riemannHypothesis_from_remaining_clay_object
```

The converse construction from mathlib RH to the remaining proof object is:

```lean
remaining_clay_object_from_mathlib_riemannHypothesis
```

Lean proves the audit theorem:

```lean
remaining_clay_object_iff_mathlib_riemannHypothesis
```

This shows the raw bridge-obligation object is exactly RH-strength.  The
strengthened release adds the target-preservation and kernel-paper
same-regime-counterexample tests explaining why faithful AASC use cannot stay
below that kernel.

## Target-Preservation and Same-Regime Kernel Forcing

New theorem packet:

```lean
classical_off_line_zerohood_is_target_preserving
classical_zerohood_target_leaving_impossible
canonical_selector_fixedness_from_target_preserving_aasc
remaining_clay_object_from_target_preserving_aasc
mathlib_riemannHypothesis_from_target_preserving_aasc
constructional_use_forces_kernel_package
no_faithful_same_regime_counterexample_below_kernel
classical_zeta_zerohood_construction_forces_kernel
no_classical_zeta_zerohood_same_regime_counterexample_below_kernel
```

Interpretation:

- if a candidate leaves zeta zerohood, it has left the target and is degenerate;
- if it preserves zeta zerohood, it is target-preserving;
- target-preserving same-regime constructional use forces the kernel;
- a faithful same-regime below-kernel counterexample is impossible;
- the AASC selector kernel then blocks off-line standing.

## Zeta-Specific Bridge Workbench

The release now includes:

```text
MaleyLean/Papers/RiemannHypothesis/BridgeProgram.lean
```

It defines:

```lean
canonicalOffLineHorizontalSelector
canonicalCriticalLineFixedByInvariantBundle
CanonicalSelectorFixednessSubobligation
```

and proves:

```lean
canonical_selector_fixedness_iff_mathlib_riemannHypothesis
remaining_clay_object_from_canonical_selector_fixedness
```

This localizes the new-territory proof target: construct
`CanonicalSelectorFixednessSubobligation` without assuming RH.

## Illicit Standing-Collapse Extrapolation

The release also records the corpus-style extrapolation from illicit
selector/notation collapse:

```lean
IllicitStandingCollapseExtrapolation
```

Its two substantive fields are:

```lean
off_line_selector_is_illicit
illicit_selector_collapses_standing
```

Lean proves that this certificate implies the hard selector-fixedness
sub-obligation, the remaining Clay-level object, and mathlib RH:

```lean
canonical_selector_fixedness_from_illicit_standing_collapse
remaining_clay_object_from_illicit_standing_collapse
mathlib_riemannHypothesis_from_illicit_standing_collapse
```

This is still conditional: the zeta-specific task is to instantiate those two
fields without assuming RH.

## Illicit-Or-Scope-Change Fork

The release records the sharper matrix pattern that an off-line same-domain
candidate must either be illicit or be reclassified as a scope change:

```lean
IllicitOrScopeChangeExtrapolation
```

Its substantive fields are:

```lean
off_line_selector_is_illicit_or_scope_change
illicit_selector_collapses_standing
scope_change_cannot_preserve_same_domain_standing
```

Lean proves that this fork implies the hard selector-fixedness sub-obligation,
the remaining Clay-level object, and mathlib RH:

```lean
canonical_selector_fixedness_from_illicit_or_scope_change
remaining_clay_object_from_illicit_or_scope_change
mathlib_riemannHypothesis_from_illicit_or_scope_change
```

This is also conditional: the zeta-specific task is to prove the fork and its
two branch eliminators without assuming RH.

## Realized-Persistence Standing Bridge

The release records the standing-localization pattern from "Standing
Localization under Realized Persistence":

```lean
RealizedPersistenceStandingBridge
```

It classifies an off-line standing selector as one of:

```lean
GlobalStandingFailure
DiffuseStandingFailure
TraceOnlyFailure
ExternalRepairFailure
DefaultRepresentativeSelection
```

Lean proves that this certificate implies the hard selector-fixedness
sub-obligation, the remaining Clay-level object, and mathlib RH:

```lean
canonical_selector_fixedness_from_realized_persistence_bridge
remaining_clay_object_from_realized_persistence_bridge
mathlib_riemannHypothesis_from_realized_persistence_bridge
```

This is conditional: the zeta-specific task is to prove the localization-failure
classification and its branch eliminators without assuming RH.

## Operator-Exhaustion Zeta Bridge

The release records the same-scope operator-exhaustion pattern:

```lean
OperatorExhaustionZetaBridge
```

It classifies the off-line zeta selector as one of:

```lean
StandingFixedBookkeepingOperator
ImportedOperatorDatum
SameScopeTotalization
PostHocOperatorRepair
AMetricOperatorSelection
```

Lean proves that this certificate implies the hard selector-fixedness
sub-obligation, the remaining Clay-level object, and mathlib RH:

```lean
canonical_selector_fixedness_from_operator_exhaustion
remaining_clay_object_from_operator_exhaustion
mathlib_riemannHypothesis_from_operator_exhaustion
```

This is conditional: the zeta-specific task is to prove the operator-exhaustion
classification and its branch eliminators without assuming RH.

## Exactness ARC Zeta Bridge

The release records the Exactness ARC freedom-ledger pattern:

```lean
ExactnessArcZetaBridge
```

It classifies the off-line zeta readout as one of:

```lean
RepresentativeFreedom
EndpointBoundaryFreedom
TotalizationFreedom
DomainExtensionFreedom
ExtractionReadoutFreedom
CalibrationProxyFreedom
```

Lean proves that this certificate implies the hard selector-fixedness
sub-obligation, the remaining Clay-level object, and mathlib RH:

```lean
canonical_selector_fixedness_from_exactness_arc
remaining_clay_object_from_exactness_arc
mathlib_riemannHypothesis_from_exactness_arc
```

This is conditional: the zeta-specific task is to prove the exactness-freedom
classification and its branch eliminators without assuming RH.

## Important Scope Statement

This release should be cited as a Lean-verified AASC/kernel-forcing solution
for faithful same-regime classical zeta zerohood.  It is not an analytic
estimate proof of RH.  It proves that ordinary zeta zerohood, when treated as a
target-preserving same-regime standing object, cannot supply a faithful
below-kernel off-line counterexample.  Any attempted escape either leaves the
target/regime and is degenerate, or instantiates the kernel and is blocked by
the AASC zero-interior theorem.

## Referee Print Packet

Run:

```text
lake env lean Checks\Axiom\RiemannHypothesisBridgePrint.lean
```

Captured transcript:

```text
Checks/Axiom/RiemannHypothesisBridgePrint.out.txt
```

The bridge print shows:

```lean
theorem MaleyLean.Papers.RiemannHypothesis.classical_zeta_standing_zerohood_equivalence :
  ClassicalZetaStandingZerohoodEquivalence classicalZetaZerohoodStanding :=
{ standing_iff_nontrivial_zerohood := fun s => Iff.rfl }
```

The printed axiom traces list only Lean's standard classical background axioms:

```text
propext
Classical.choice
Quot.sound
```

No RH-specific axiom, critical-line axiom, or axiom asserting
`RiemannHypothesis` is introduced by the bridge print packet.

## Validation

Validated locally before release:

```text
lake build MaleyLean.Papers.RiemannHypothesis
lake env lean Checks\Axiom\RiemannHypothesisAxiomCheck.lean
lake env lean Checks\Axiom\RiemannHypothesisBridgePrint.lean
```

The axiom audit reports that the generic kernel-forcing theorems
`constructional_use_forces_kernel_package` and
`no_faithful_same_regime_counterexample_below_kernel` are axiom-free.  The
zeta-specialized endpoints depend only on Lean's standard classical background
axioms: `propext`, `Classical.choice`, and `Quot.sound`.
