# Nondegenerate UEAP Kernel Operationalization Proof

This note supplies the prose proof that the neutrino case inhabits the Lean
object:

```lean
AASCNondegenerateUEAPKernelOperationalization C M H N S
```

The point of the object is not that UEAP is an additional optional screen.
Rather, in a non-degenerate regime, UEAP is the operational presentation of the
AASC admissibility kernel. The kernel says which claim-standing conditions are
forced by non-degenerate admissibility; UEAP records those conditions as
auditable coordinates.

## Proposition

For the standing neutrino splitting-ratio problem, in the admitted
non-degenerate same-scope regime, the UEAP branch audit is forced by the
admissibility kernel. Consequently every non-current draft branch fails a
UEAP legitimacy coordinate, while any route that survives the hybrid joint
restriction must claim UEAP sigma-legitimacy. Hence no non-current branch can
survive the hybrid joint restriction.

Equivalently, the neutrino case inhabits:

```lean
AASCNondegenerateUEAPKernelOperationalization C M H N S
```

and therefore Lean derives:

```lean
nondegenerateUEAPKernelOperationalizationGiveJointSingleton
nondegenerateUEAPKernelOperationalizationRulesOutSecondPoint
```

## Lean4 Provenance

Status phrase for this note:

```text
Lean4 build status reported
```

Reported local check:

```text
lake build MaleyLean.Papers.Neutrino
```

completed successfully on 2026-05-28 in the working repository. This is not
claimed as an independent build audit of a manuscript submission package.
Independent build audit remains a verification task, not a manuscript premise.

Verification answers for the current repository audit:

| Question | Answer |
| --- | --- |
| Does the Lean file compile? | Yes. `lake build MaleyLean.Papers.Neutrino` completed successfully with 94 jobs. |
| Are there any `sorry` placeholders? | No `sorry` or `admit` occurrences were found in the relevant Lean source tree scanned for the neutrino formalization and its immediate paper dependencies. |
| Are there extra axioms? | No `axiom` declarations were found in the relevant scanned Lean source. The only match was prose mentioning “axiom-free bridge theorem names.” |
| Do theorem names map exactly to manuscript claims? | Yes for the current proof note: the singleton claim maps to `HybridJointRestrictionSingleton` and the theorem `branchAuditAndKernelAdmissionWitnessesGiveEndpointSingleton`; the no-second-point claim maps to `HybridJointRestrictionHasSecondPoint` and `branchAuditAndKernelAdmissionWitnessesRuleOutSecondPoint`. |

“Current standing ratio” means current within the admitted AASC standing
ledger and route census. It does not mean the current empirical best-fit ratio
or any imported numerical experimental value.

## Theorem-to-Manuscript Map

| Manuscript claim or dependency | Lean object or theorem |
| --- | --- |
| Standing ratio certificate `C` | `StandingRatioCertificate`; `StandingRatioCertificateAdmitted`; `standingRatioCertificateAdmitted` |
| MR3 spectral-source admission `M` | `MR3SpectralSourceAdmission`; `MR3SpectralSourceAdmissionWitness`; `MR3CorpusTheorems.admitsSource` |
| Hybrid modular/spectral/scoto restriction `H` | `AASCHybridCompressionNetwork`; `AASCHybridSameScopeAdmissionWitness`; `hybridSameScopeAdmissionWitnessClearsH` |
| No-eleventh-route census `N` | `AASCNoEleventhNeutrinoRoute`; `AASCNoEleventhRouteCensusWitness`; `noEleventhRouteCensusWitnessClearsN` |
| Corpus support ledger `S` | `AASCCorpusBranchSupportLedger`; `corpusSupportLedgerAdmitted` |
| Non-degenerate kernel admission | `AASCNondegenerateKernelInteriorAdmission`; `nondegenerateKernelAdmissionFromCurrentPointIdentification` |
| Branch impossibility audit | `AASCBranchImpossibilityAudit`; `branchImpossibilityAuditAsConcreteBranchFailureTable` |
| Admissible ratio branch singleton locked | `HybridJointRestrictionSingleton`; `branchAuditAndKernelAdmissionWitnessesGiveEndpointSingleton` |
| No second admissible branch | `HybridJointRestrictionHasSecondPoint`; `branchAuditAndKernelAdmissionWitnessesRuleOutSecondPoint` |

## Proof

Work inside the standing neutrino splitting-ratio certificate `C`, the MR3
spectral-source admission `M`, the hybrid modular/spectral/scoto compression
network `H`, the no-eleventh-route census `N`, and the corpus support ledger
`S`.

The target is non-degenerate. The ratio under discussion is not a degenerate
placeholder, empty boundary object, pure notation choice, or free parameter
fiber. It is a standing same-target object over two non-collapsed response
roles: the solar and atmospheric splitting roles, with a fixed atmospheric
denominator, fixed common carrier, and fixed subordinate relation. Thus the
neutrino target lies in the regime governed by the kernel papers: meaningful
same-scope competitors must preserve the non-degenerate standing conditions
rather than repair them by importing new domain data, hidden selectors, or
post-hoc calibration.

By the kernel and unique-interior results, non-degenerate standing forces
occupation of the unique admissible interior. In Lean this is the role of
`kernelAdmission : AASCNondegenerateKernelInteriorAdmission C M H N S.unusSolus`.
It supplies the current-class point-identification field: if a ratio is in the
hybrid joint restriction and its exposed draft carrier is the current standing
carrier, then it is extensionally the current standing ratio. This discharges
the current branch of the audit.

It remains to identify what happens to a non-current draft branch. UEAP is the
kernel written as a claim-standing audit. A branch that genuinely survives the
hybrid joint restriction is no longer merely a suggestive motif or compatible
model fragment; it is asserting claim-standing for its draft class. Therefore
every joint survivor must satisfy UEAP sigma-legitimacy for its exposed draft
class. This is the field:

```lean
jointSurvivorClaimsUEAPLegitimacy
```

But a non-current branch is non-current precisely because it attempts to close
the same target through a route not identified with the current standing
carrier. The kernel forbids such a route from becoming a same-scope
ratio-closing claim unless it passes the required UEAP coordinates: fixed
target, adequate carrier, fixed meaning, fixed scope, target-carrier alignment,
exhaustion modulo skin, laundering exclusion, ancestry separation, boundary
declaration, evidence-network closure, and report preservation. For each
non-current branch, one of these coordinates is forced to fail. This is the
field:

```lean
kernelForcesAssignedUEAPFailure
```

The branch-by-branch assignments are as follows.

| Branch | UEAP coordinate failure | Corpus reason |
| --- | --- | --- |
| `modularOnlyBranch` | `alternativesNotExhaustedModuloSkin` | The NNR4G/H magnitude-compression audit blocks promotion from modular motif, texture, or carrier polynomial to the target ratio unless all same-scope alternatives have been exhausted modulo skin. A modular-only route remains a motif/constraint family, not an exhausted target selector. |
| `scotoParameterFiberBranch` | `launderingNotExcluded` | The residual-parameter and scoto/seesaw audits block hidden parameter repair. A live parameter fiber cannot be laundered into first-principles closure unless the fiber is source-fixed, quotient-skin, or forced by the shared locus. |
| `spectralWithoutFiniteCollapseBranch` | `evidenceNetworkNotClosed` | The fixed-domain exhaustion and quotient-fiber exactness results require finite collapse, overlap, or quotient-fiber exhaustion before a spectral quotient can report exact selection. Without that closure, the evidence network remains open. |
| `sterileScopeExtensionBranch` | `scopeUnfixed` | Sterile/gauge-singlet or AdS/transport extensions change the comparison scope unless they project back through the admitted same-scope residual quotient. As an independent selector, the branch has not fixed the same target scope. |
| `phaseTopologyBreakingBranch` | `reportNotPreserving` | Oscillation phase topology gives coherent readback and compatibility, not an independent magnitude selector. A phase-only branch that changes the ratio fails report preservation for the splitting-ratio target. |
| `matterTransportBreakingBranch` | `targetCarrierMisaligned` | Matter-effect or transport behavior is a compatibility discriminator. To move the ratio it would require an operator strengthening not conservative on the fixed base, so the target carrier is misaligned. |
| `absoluteMassImportBranch` | `boundaryNotDeclared` | Absolute mass, beta-decay, or cosmological information is boundary data for a different measurement family. Promoting it to the splitting-ratio selector imports an undeclared boundary. |
| `diracMajoranaSelectorBranch` | `targetAncestryNotSeparated` | Dirac/Majorana status may constrain admissible models, but as a ratio selector it introduces an endpoint or identity branch whose ancestry is not separated from the target derivation. |
| `identitySelectorBranch` | `carrierInadequate` | Identity, normalization, chart, or representation choices are quotient skin or bookkeeping unless they alter standing-bearing content. As a selector they lack an adequate carrier. |

Each row is exactly one instance of the UEAP theorem:

```text
coordinate failure -> legitimacy blocker -> not sigma-legitimate
```

Thus, suppose for contradiction that a non-current branch survives the hybrid
joint restriction. Since it survives the joint restriction, it must claim UEAP
sigma-legitimacy. Since it is non-current, the non-degenerate kernel forces the
assigned UEAP coordinate failure for that branch. By UEAP claim-standing
soundness, that coordinate failure is a legitimacy blocker, and a legitimacy
blocker excludes sigma-legitimacy. Contradiction.

Therefore every non-current draft branch is eliminated. The current branch is
point-identifying by non-degenerate unique-interior occupancy. Hence the hybrid
joint restriction has only the current standing ratio as survivor.

This inhabits:

```lean
AASCNondegenerateUEAPKernelOperationalization C M H N S
```

and the formal closure follows by:

```lean
nondegenerateUEAPKernelOperationalizationGiveJointSingleton
nondegenerateUEAPKernelOperationalizationRulesOutSecondPoint
```

## Citation Handles

The proof uses the following corpus families.

| Role in proof | Corpus source family |
| --- | --- |
| UEAP legitimacy, blockers, and sigma-legitimacy exclusion | `Claim_Standing_and_Legitimacy` |
| Non-degenerate kernel necessity and unique admissible interior | kernel/unique-interior papers, including `Unus_Solus_Possibilis_Est` |
| No partial closure and no hidden repairs | Impossibility Suite and `Septem_Sigilla_Necessitatis` |
| Fixed-domain exhaustion and quotient-fiber discipline | Fixed-Domain Exhaustion, AMetric Boundary, Closure by Exhaustion |
| Operator strengthening and endpoint discipline | Fixed-Base Operator Constraints, Collapse of Operator-Level Strengthening, Invariant Selection and Endpoint Structure |
| Role occupancy and no same-role splitting | Role-Occupancy Closure under Admissibility |
| Skin/bookkeeping separation | ATS and equivalence/quotient exhaustion results |

## Lean Field Map

| Lean field | Proof paragraph |
| --- | --- |
| `audit` | UEAP claim audit specialized to `NeutrinoDraftCandidateIndex`. |
| `kernelAdmission` | Non-degenerate kernel necessity plus unique admissible interior. |
| `ueapIsKernelOperationalized` | UEAP is the operational audit form of the admissibility kernel. |
| `jointSurvivorClaimsUEAPLegitimacy` | A branch surviving the hybrid joint restriction must be a claim-standing route, not merely compatible support. |
| `kernelForcesAssignedUEAPFailure` | The nine branch rows above give the kernel-forced UEAP coordinate failures. |
