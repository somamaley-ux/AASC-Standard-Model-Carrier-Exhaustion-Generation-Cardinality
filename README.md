# AASC Standard Model Carrier Exhaustion / Generation Cardinality

Manuscript-faithful Lean 4 A+ audit archive for:

`Generation Cardinality as a Forced Role Occupancy Endpoint`

This repository presents the Standard Model carrier-exhaustion closure together
with its downstream generation-cardinality extension. It receives the SM-1
through SM-6 Standard Model deconstruction chain locally and adds the
open-generation endpoint:

```text
ClosedGenCert(n) iff n = 3
```

The mechanized surface is intentionally paper-shaped: it does not replace the
manuscript, and it does not claim a fresh first-principles reconstruction of the
entire Standard Model. It gives the manuscript's role-occupancy endpoint a
typed Lean audit layer, with source artifacts, theorem inventory, and local
verification kept together.

## Current Status

- `GenerationCardinality` is a standalone Lake target.
- SM-1 through SM-6 are included locally as received ARC layers.
- The extension PDF, ZIP, source `main.tex`, and source snapshot are retained
  under `papers/generation-cardinality/`.
- The controlling `main.tex` manuscript contains 53 formal environments,
  represented in `GenerationCardinality.TheoremInventory`.
- The endpoint theorem surface includes `ClosedGenCert(n) iff n = 3`, the
  forced role-occupancy theorem, and the ARC handoff theorem anchor.
- The local audit checks the build, scans for live `axiom`, `sorry`, `admit`,
  and `unsafe`, and runs focused axiom checks over the endpoint anchors.
- The scope boundary is the open-generation role-occupancy endpoint, not a
  change to the SM-6 primitive carrier package.

## Verification

```powershell
powershell -ExecutionPolicy Bypass -File scripts/check-generation-cardinality-audit.ps1 -SkipLakeUpdate
```

## Main Lean Anchors

- `GenerationCardinality.OpenGenerationArena`
- `GenerationCardinality.CandidateCardinalityArena`
- `GenerationCardinality.GenerationRoleCertificate`
- `GenerationCardinality.CardinalityEndpointCertificate`
- `GenerationCardinality.cardinality_endpoint_certificate_closure`
- `GenerationCardinality.closed_generation_certificate_iff_three`
- `GenerationCardinality.generation_cardinality_as_forced_role_occupancy_endpoint`
- `GenerationCardinality.arc_handoff`
- `GenerationCardinality.generation_cardinality_scope_boundary`
- `GenerationCardinality.a_plus_inventory_complete`

## Claim Boundary

This archive supports the strongest verified reading of the extension:
the SM-6 carrier-exhaustion closure is received locally, and generation
cardinality is treated as a forced role-occupancy endpoint over that AASC/ARC
machinery. It leaves numerical CKM/PMNS/CP values, untyped generation-holonomy
imports, and model-by-model BSM phenomenology outside the mechanized claim.
