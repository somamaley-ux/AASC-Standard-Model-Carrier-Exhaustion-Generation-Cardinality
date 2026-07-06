# AASC Generation Cardinality Endpoint Lean Audit

Standalone Lean 4 audit archive for:

`Generation Cardinality as a Forced Role Occupancy Endpoint`

This is an ARC extension manuscript. It receives the SM-1 through SM-6 Standard
Model deconstruction chain locally and mechanizes the downstream endpoint:

```text
ClosedGenCert(n) iff n = 3
```

## Current Status

- `GenerationCardinality` is a standalone Lake target.
- SM-1 through SM-6 are included locally as received ARC layers.
- The extension PDF, ZIP, source `main.tex`, and source snapshot are retained
  under `papers/generation-cardinality/`.
- The controlling `main.tex` manuscript contains 53 formal environments,
  represented in `GenerationCardinality.TheoremInventory`.
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
- `GenerationCardinality.closed_generation_certificate_iff_three`
- `GenerationCardinality.generation_cardinality_as_forced_role_occupancy_endpoint`
- `GenerationCardinality.arc_handoff`
- `GenerationCardinality.generation_cardinality_scope_boundary`
- `GenerationCardinality.a_plus_inventory_complete`
