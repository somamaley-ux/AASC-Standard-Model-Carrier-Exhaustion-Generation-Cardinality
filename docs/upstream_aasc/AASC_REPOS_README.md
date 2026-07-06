# AASC-REPOS

Lean 4 formalization repository for the AASC paper family.

This repository currently contains paper-facing formalizations for:

- `Minimal Conditions for Admissible Construction`
- `The Bivalence Theorem for Non-Degenerate Reasoning`
- `Claim Standing and Legitimacy: A Universal Audit Protocol for Laundering Exclusion and Reportable Output`
- a small formalization smoke-test module

The central formal theme is AASC: admissibility-and-standing conservation. The
formalization treats standing-bearing governance as a bottom layer for the
target class of non-degenerate reasoning. The point is not that deeper neutral
primitives have not yet been found; it is that standing, legitimacy,
admissibility, reference, and irreversibility cannot be derived from a weaker
same-scope substrate without changing the target class into trace
classification or bookkeeping.

## Minimal Conditions for Admissible Construction

The `Minimal Conditions for Admissible Construction` development is the kernel
paper for the repository. It formalizes the fixed-domain uniqueness result for
the admissibility kernel: admissibility, standing, reference, and irreversibility
are the non-lowerable governance roles for identity-preserving construction.
Nothing same-domain and governance-equivalent can be derived beneath that
kernel; any faithful candidate either carries the kernel already, changes
domain, loses the target phenomenon, imports selector structure, or collapses
to bookkeeping.

The paper-facing files are:

- `MaleyLean/Papers/MinimalConditionsForAdmissibleConstruction/PaperStatements.lean`
- `MaleyLean/Papers/MinimalConditionsForAdmissibleConstruction/Surface/Summary.lean`
- `MaleyLean/Papers/MinimalConditionsForAdmissibleConstruction/Verbatim/TheoremRegister.lean`
- `Checks/Axiom/MinimalConditionsForAdmissibleConstructionAxiomCheck.lean`

The preferred human-readable summary exports are:

- `MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.Surface.SummaryStatement`
- `MaleyLean.Papers.MinimalConditionsForAdmissibleConstruction.Surface.BivalenceBridgeSummaryStatement`

## Claim Standing and Legitimacy

The `Claim Standing and Legitimacy` development is not just a theorem-name
registry. Its current Lean surface includes:

- a domain-general `ClaimAudit` structure;
- preliminary standing and Sigma-legitimacy predicates;
- explicit preliminary-standing and legitimacy blocker predicates;
- coordinate-level claim-failure semantics;
- audit-status meaning semantics;
- validator-output soundness;
- semantically sound registry rows and strongest-status soundness;
- claim-standing and claim-legitimacy `System` instances;
- same-act no-repair theorems for claim standing and claim legitimacy;
- standing-conservation theorems for claim standing and claim legitimacy;
- classifier-uniqueness theorems for standing and legitimacy;
- a bridge from UEAP audit roles into AASC-class governance.

The paper-facing files are:

- `MaleyLean/Papers/ClaimStandingAndLegitimacy/PaperStatements.lean`
- `MaleyLean/Papers/ClaimStandingAndLegitimacy/Surface/Summary.lean`
- `MaleyLean/Papers/ClaimStandingAndLegitimacy/Verbatim/TheoremRegister.lean`
- `Checks/Axiom/ClaimStandingAndLegitimacyAxiomCheck.lean`

The preferred human-readable summary exports are:

- `MaleyLean.Papers.ClaimStandingAndLegitimacy.Surface.SummaryStatement`
- `MaleyLean.Papers.ClaimStandingAndLegitimacy.Surface.GovernanceBridgeSummaryStatement`
- `MaleyLean.Papers.ClaimStandingAndLegitimacy.Surface.RegistryStatusSoundnessSummaryStatement`
- `MaleyLean.Papers.ClaimStandingAndLegitimacy.Surface.ClaimStandingNoRepairSummaryStatement`
- `MaleyLean.Papers.ClaimStandingAndLegitimacy.Surface.ClaimStandingConservationSummaryStatement`

## Bivalence and AASC Governance

The bivalence development formalizes the governance spine behind AASC:

- same-scope governance systems;
- kernel roles;
- AASC-class governance;
- no same-act repair;
- no second same-scope admissibility invariant;
- standing conservation;
- governance-role exhaustion;
- bivalence and local-closure statements.

The paper-facing files are:

- `MaleyLean/Papers/BivalenceNonDegenerateReasoning/PaperStatements.lean`
- `MaleyLean/Papers/BivalenceNonDegenerateReasoning/Surface/Summary.lean`
- `MaleyLean/Papers/BivalenceNonDegenerateReasoning/Verbatim/TheoremRegister.lean`
- `Checks/Axiom/BivalenceNonDegenerateReasoningAxiomCheck.lean`

The `paper/` directory contains the phase-14 LaTeX/PDF snapshot for the
bivalence manuscript.

## Build

```powershell
lake build
```

## Axiom Audits

Claim Standing and Legitimacy:

```powershell
lake env lean Checks\Axiom\ClaimStandingAndLegitimacyAxiomCheck.lean
```

Bivalence:

```powershell
lake env lean Checks\Axiom\BivalenceNonDegenerateReasoningAxiomCheck.lean
```

Minimal Conditions for Admissible Construction:

```powershell
lake env lean Checks\Axiom\MinimalConditionsForAdmissibleConstructionAxiomCheck.lean
```

The current `Claim Standing and Legitimacy` paper-facing theorem surface is
axiom-free: the axiom audit reports that each checked theorem does not depend on
any axioms.

## Repository

GitHub:

```text
https://github.com/somamaley-ux/AASC-REPOS
```
