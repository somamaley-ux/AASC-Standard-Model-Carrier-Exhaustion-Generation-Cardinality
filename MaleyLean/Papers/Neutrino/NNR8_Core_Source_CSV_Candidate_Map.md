# NNR8 Core Source CSV Candidate Map

CSV scanned:

```text
g:\AASC corpus may 7\Core spine\ZZZNew Work\ZSubmission versions\Source theorem matrix\UPdating\AASC_Corpus_Control_Matrix_v1_5_New_ERK_May27_Hardened.csv
```

Target Lean object:

```lean
AASCNNR8CoreSourceProofBundle C M H N S
```

This map lists candidate corpus rows that may discharge the remaining source
proof fields.

## MR3 Witness

Lean witness:

```lean
MR3SpectralSourceAdmissionWitness M
```

| Field | Candidate source rows | Why relevant |
| --- | --- | --- |
| `sourceCertified` | `AASC-MR3-DEF-002`, `AASC-MR3-THM-001`, `AASC-MR3-THM-010` | MR3 defines the spectral/hierarchy source certificate and gives the main source-admission theorem. |
| `standingSpectralCarrier` | `AASC-MR3-THM-001`, `AASC-MR3-THM-002`, `AASC-MR3-THM-003` | Spectral carrier admission, eigenvalue/singular-value standing, and relative spectrum source theorem. |
| `quotientStable` | `AASC-MR3-DEF-004`, `AASC-MR3-THM-003`, `AASC-EX1-THM-7-13` | Source equivalence by quotient image and same-domain escape exclusion. |
| `transportClosed` | `AASC-MR3-DEF-003`, `AASC-MR3-THM-010`, `CS6C-THM-004` | Source-induced shape map plus boundary-to-boundary reconstruction support transport of admitted witness data. |
| `calibrationFree` | `AASC-MR3-THM-006`, `AASC-MR3-THM-007`, `UEAP-THM-002`, `CS7-FORB-001` | Blocks exponent fitting, dimensionless notation promotion, calibration-only claims, and PMNS numerical extraction. |
| `extractionCertified` | `AASC-MR3-DEF-003`, `AASC-MR3-THM-010`, `CS7-REG-002` | Source-induced shape map and reportable oscillation invariant witness classes. |
| `sourceInducesShapeMap` | `AASC-MR3-DEF-003`, `AASC-MR3-THM-010` | Directly names source-induced shape mapping and the bundled MR3 source theorem. |

High-value MR3 rows:

| Source ID | Object | Pointer |
| --- | --- | --- |
| `AASC-MR3-DEF-002` | Spectral/hierarchy source certificate | MR3 §4 / Def. 4.1 |
| `AASC-MR3-DEF-003` | Source-induced shape map | MR3 §4 / Def. 4.2 |
| `AASC-MR3-DEF-004` | Source equivalence by quotient image | MR3 §4 / Def. 4.5 / Rem. 4.6 |
| `AASC-MR3-THM-001` | Spectral carrier admission theorem | MR3 §7 / Thm. 7.2 |
| `AASC-MR3-THM-003` | Relative spectrum source theorem | MR3 §9 / Thm. 9.2 |
| `AASC-MR3-THM-010` | Spectral/hierarchy shape-source theorem | MR3 §17 / Thm. 17.1 |

## Hybrid Same-Scope Witness

Lean witness:

```lean
AASCHybridSameScopeAdmissionWitness C M H
```

| Field | Candidate source rows | Why relevant |
| --- | --- | --- |
| `crossTargetAligned` | `ROC-DEF-005`, `CS6C-THM-002`, `CS7-REG-002`, `AASC-EX8-THM-11-2` | Joint compatibility, oscillation invariant witness classes, and overconstraint legitimacy support common standing-bearing target alignment. |
| `crossTransportCoherent` | `CS6C-DEF-002`, `CS6C-THM-004`, `NOAR-THM-003`, `NOAR-THM-004` | Boundary-to-boundary kernel and oscillation realization provide coherent transport form. |
| `crossNoOvercounting` | `AASC-MR3-DEF-004`, `AASC-EX1-THM-7-13`, `NOAR-COR-001`, `ROC-DEF-007` | Quotient image equivalence, same-domain escape exclusion, quotient collapse, and lawful role automorphism control duplicate presentations. |
| `crossCalibrationFree` | `UEAP-THM-002`, `CS7-FORB-001`, `CS7-DEFER-001`, `CS6C-NON-001` | Forbids global-fit values, sensitivities, PMNS numerical values, and numerical derivation from entering the proof. |
| `crossNoHiddenSelector` | `UEAP-THM-001`, `AASC-MR5-PROP-002`, `ROC-NON-001`, `AASC-MR3-THM-006`, `AASC-MR3-THM-007` | Laundering exclusion, effect-status separation, no empirical tie-break, no exponent fitting, no dimensionless notation promotion. |

High-value hybrid rows:

| Source ID | Object | Pointer |
| --- | --- | --- |
| `ROC-DEF-005` | Joint compatibility predicate | Role-Occupancy Closure :: Definition `J_C` |
| `CS6C-THM-004` | Boundary-to-boundary reconstruction | CS6C theorem |
| `NOAR-COR-001` | Universal quotient form of oscillation uniqueness | NOAR corollary |
| `AASC-EX8-THM-11-2` | Overconstraint legitimacy | EX8 Theorem 11.2 |
| `AASC-MR5-PROP-002` | Effect-status separation | MR5 §5 / Prop. 5.3 |

## No-Eleventh Route Census Witness

Lean witness:

```lean
AASCNoEleventhRouteCensusWitness C M H N
```

| Field | Candidate source rows | Why relevant |
| --- | --- | --- |
| `noUncarriedSameTargetConstraint` | `CS6C-THM-006`, `ROC-THM-002`, `AASC-EX1-THM-7-13` | Same-scope rival exhaustion, lawful closure route exhaustion, and same-domain escape exclusion. |
| `noLegacyTheoryOutsideCensus` | `CS6C-THM-006`, `NOAR-LEM-001`, `NOAR-COR-001`, `ROC-THM-002` | Legacy alternatives collapse to boundary-kernel/role-occupancy forms or become non-same-scope. |
| `noExperimentalMethodOutsideCensus` | `CS6C-REG-001` through `CS6C-REG-007`, `CS7-REG-001` through `CS7-REG-004`, `CS7-FORB-001`, `CS7-DEFER-001` | Oscillation, PMNS, absolute-mass, transported-flavor, sterile/BSM, and boundary methods are classified or firewalled. |
| `noScopeChangingRouteCountsSameScope` | `CS6C-REG-007`, `CS6C-THM-006`, `ROC-DEF-004`, `ROC-DEF-006` | Extensions are scope changes; eligible/live residue definitions distinguish same-scope residue. |
| `noEmpiricalValueImportAsRoute` | `UEAP-THM-002`, `CS7-FORB-001`, `CS7-DEFER-001`, `CS6C-NON-001`, `ROC-NON-001` | Calibration-only and forbidden-promotion rows block observed values as derivation routes. |

High-value census rows:

| Source ID | Object | Pointer |
| --- | --- | --- |
| `CS6C-THM-006` | Same-scope oscillation rival exhaustion | CS6C theorem |
| `CS6C-REG-007` | Sterile/decoherence/collapse/BSM extension | CS6C registry OSC-C7 |
| `CS7-FORB-001` | PMNS invariant witness to numerical PMNS values | CS7 forbidden promotions |
| `CS7-DEFER-001` | PMNS values deferred | CS7 deferred target ledger |
| `ROC-THM-002` | Exhaustion of lawful closure routes | Role-Occupancy Closure theorem |

## Operationalization Proofs

Lean fields:

```lean
currentPointIdentification
jointSurvivorUEAPLegitimacy
kernelForcedUEAPFailure
```

| Field | Candidate source rows | Why relevant |
| --- | --- | --- |
| `currentPointIdentification` | `ROC-THM-001`, `NOAR-COR-001`, `AASC-MGN1-LEM-3-10`, `AASC-MGN1-THM-3-11`, `AASC-MGN1-THM-18-1` | Role occupancy, quotient uniqueness, admissible equivalence kernel, and numerical-standing theorem support current-class uniqueness. |
| `jointSurvivorUEAPLegitimacy` | `UEAP-THM-001`, `UEAP-THM-002`, `AASC-EX8-THM-11-2`, `AASC-MR5-PROP-002` | Surviving overconstraint must be legitimate claim-standing, not merely compatible support or calibration. |
| `kernelForcedUEAPFailure` | `UEAP-THM-001`, `ROC-THM-002`, `CS6C-THM-006`, `AASC-EX1-THM-7-13`, `AASC-MR5-PROP-002` | Non-current branches fail by laundering exclusion, route exhaustion, same-domain escape exclusion, or effect-status separation. |

## Strongest Immediate Candidates

These are the rows most likely to clear multiple fields at once:

| Source ID | Why it matters |
| --- | --- |
| `AASC-MR3-THM-010` | Best candidate for most MR3 witness fields. |
| `CS6C-THM-006` | Best candidate for no-eleventh same-scope rival exhaustion. |
| `CS6C-REG-007` | Best candidate for scope-changing route exclusion. |
| `CS7-FORB-001` and `CS7-DEFER-001` | Best candidates for empirical/numerical import firewall. |
| `UEAP-THM-001` and `UEAP-THM-002` | Best candidates for legitimacy/laundering/calibration firewall. |
| `ROC-THM-001` and `ROC-THM-002` | Best candidates for role occupancy and closure-route exhaustion. |
| `NOAR-COR-001` | Best candidate for quotient uniqueness of oscillation reconstruction. |
| `AASC-EX8-THM-11-2` | Best candidate for legitimate overconstraint / hybrid convergence. |
| `AASC-MR5-PROP-002` | Best candidate for not mistaking admitted support for strong constraint. |

## Current Assessment

The CSV contains plausible, high-confidence rows for every field of
`AASCNNR8CoreSourceProofBundle`.

The next step is not more broad search. It is targeted source extraction for
the strongest rows above, especially:

```text
AASC-MR3-THM-010
CS6C-THM-006
ROC-THM-002
UEAP-THM-001
UEAP-THM-002
AASC-EX8-THM-11-2
NOAR-COR-001
CS7-FORB-001
CS7-DEFER-001
```

