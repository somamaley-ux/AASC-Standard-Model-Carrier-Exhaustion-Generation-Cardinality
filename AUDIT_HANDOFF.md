# Standard Model Carrier Exhaustion / Generation Cardinality Audit Handoff

This repo is the A+ handoff archive for the ARC extension manuscript
`Generation Cardinality as a Forced Role Occupancy Endpoint`, presented publicly
as `Standard Model Carrier Exhaustion / Generation Cardinality`.

## Verification Command

```powershell
powershell -ExecutionPolicy Bypass -File scripts/check-generation-cardinality-audit.ps1 -SkipLakeUpdate
```

## Main Build Target

```text
GenerationCardinality
```

The controlling extension `main.tex` source contains 53 formal environments. The
count is checked by `GenerationCardinality.manuscript_formal_environment_count`.

This repo receives SM-1 through SM-6 locally and records the generation
cardinality endpoint as a downstream ARC extension.

## Audit Meaning

The verifier confirms that the endpoint target builds, that no live project-level
`axiom`, `sorry`, `admit`, or `unsafe` declarations are present, and that the
focused endpoint anchors report no axiom dependencies. It does not broaden the
claim beyond the manuscript's open-generation role-occupancy endpoint.
