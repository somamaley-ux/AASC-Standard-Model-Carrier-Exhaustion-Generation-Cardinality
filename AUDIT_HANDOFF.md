# Generation Cardinality Audit Handoff

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
