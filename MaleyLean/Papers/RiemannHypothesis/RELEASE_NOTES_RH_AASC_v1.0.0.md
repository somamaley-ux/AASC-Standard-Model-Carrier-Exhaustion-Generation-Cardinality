# RH AASC Zerohood Reduction v1.0.0

Release target for Zenodo archival of the Riemann Hypothesis AASC/Lean
reduction handoff package.

## Citation Target

Repository path:

```text
MaleyLean/Papers/RiemannHypothesis
```

Recommended GitHub URL:

```text
https://github.com/somamaley-ux/AASC-REPOS/tree/main/MaleyLean/Papers/RiemannHypothesis
```

## Formal Result Framing

This release contains a Lean-verified AASC-native reduction of RH to the
explicit construction of:

```lean
Nonempty ClassicalRiemannZetaBridgeObligations
```

Equivalently, this is named:

```lean
RemainingClayLevelProofObject
```

The release includes:

- framework-internality for non-degenerate standing-bearing proof regimes;
- AASC kernel-role instantiation for the zeta interface;
- imported global uniqueness/no-plural-standing-interior consequences;
- same-domain selector exclusion for off-critical-line support;
- canonical standing-as-zerohood bridge for mathlib's `riemannZeta`;
- formal equivalence between the canonical AASC endpoint and mathlib's
  `RiemannHypothesis`;
- hostile-referee print packet with exact Lean output;
- explicit reduction theorem from the remaining object to mathlib RH.

It does not claim that `Nonempty ClassicalRiemannZetaBridgeObligations` is
constructed in this release.

## Key Lean Names

```lean
classicalZetaZerohoodStanding
classical_zeta_standing_zerohood_equivalence
aasc_zerohood_endpoint_iff_mathlib_riemannHypothesis
RemainingClayLevelProofObject
mathlib_riemannHypothesis_from_remaining_clay_object
aasc_standing_zero_interior_rigidity
zeta_global_uniqueness_instantiated
SameDomainSelectorKernel.selector_blocks_standing
```

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

and:

```lean
theorem MaleyLean.Papers.RiemannHypothesis.aasc_zerohood_endpoint_iff_mathlib_riemannHypothesis :
  (classicalRiemannZetaInterface classicalZetaZerohoodStanding).aascStandingCriticalLineSupported <->
  RiemannHypothesis :=
aasc_endpoint_iff_mathlib_riemannHypothesis_under_zerohood_standing
  classical_zeta_standing_zerohood_equivalence
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
lake build MaleyLean
```

`lake build MaleyLean` passes with one pre-existing Neutrino linter warning in:

```text
MaleyLean/Papers/Neutrino/SourceTheorems/MathlibSpectralOperator.lean
```
