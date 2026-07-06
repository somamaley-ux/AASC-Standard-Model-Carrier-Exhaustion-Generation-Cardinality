# RH Corpus Matrix Refresh

Source checked:

`g:\AASC corpus may 7\Core spine\ZZZNew Work\ZSubmission versions\Source theorem matrix\AASC_Corpus_Control_Matrix.csv`

Timestamp observed: `2026-05-27 20:00:39`

Rows observed: `14813`

## RH-Specific Search Result

CSV-aware searches for `Riemann`, `zeta`, `critical line`, `zero-support`,
`zero divisor`, `horizontal selector`, `off-critical`, and related phrases did
not find a dedicated RH/zeta bridge row in the refreshed matrix.

Consequence: the matrix refresh supports the general AASC/kernel provenance for
the RH route, but it does not by itself construct
`ClassicalRiemannZetaBridgeObligations`.

The separate standing/zerohood equivalence bridge is discharged in Lean by
`classical_zeta_standing_zerohood_equivalence`; it is not sourced from a corpus
matrix row and does not assert critical-line support.

## Kernel Rows Mapped

| Lean obligation area | Matrix row |
|---|---|
| AMetric boundary / no pre-admissible selector authority | `AASC4-P01-DEF-017` |
| AMetric boundary forcing | `AASC4-P01-THM-011` |
| Standing conservation | `AASC4-P01-THM-012` |
| No admissibly distinct same-domain rederivation | `AASC4-P01-THM-014` |
| Boundary-crossed standing-conserving uniqueness | `AASC4-P01-COR-003` |
| No solver/transport selector promotion | `AASC-EX3-COR-11-2` |
| Transport fixed locus status | `AASC-EX3-DEF-12-1` |
| Fixed-locus non-promotion | `AASC-EX3-THM-12-2` |
| Endpoint/boundary-selection exclusion | `AASC-EX3-THM-12-3` |

## Lean Status

The source-ID register is recorded in:

`MaleyLean/Papers/RiemannHypothesis/CorpusMatrix.lean`

It intentionally does not claim that the corpus matrix proves RH.  It records
the current provenance split:

```text
refreshed corpus matrix -> general AASC kernel support
standing/zerohood bridge -> discharged by classical_zeta_standing_zerohood_equivalence
selector/kernel package  -> recorded as ClassicalRiemannZetaBridgeObligations
```
