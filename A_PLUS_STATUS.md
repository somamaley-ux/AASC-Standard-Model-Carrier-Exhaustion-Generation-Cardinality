# Standard Model Carrier Exhaustion / Generation Cardinality A+ Status

The extension manuscript is A+ at the paper-level mechanization surface. The
controlling verification command is:

```powershell
powershell -ExecutionPolicy Bypass -File scripts/check-generation-cardinality-audit.ps1 -SkipLakeUpdate
```

Evidence:

- `GenerationCardinality` builds locally.
- No live project-level `axiom`, `sorry`, `admit`, or `unsafe` declarations.
- Focused axiom check is clean for the listed endpoint anchors.
- `GenerationCardinality.a_plus_inventory_complete` checks the 53-row formal
  inventory.
- PDF/source ZIP/source snapshot are retained under
  `papers/generation-cardinality/`.
- SM-1 through SM-6 are local received layers, so this remains an ARC extension
  endpoint rather than a replacement closure layer.

The A+ claim is deliberately scoped: it is a manuscript-faithful Lean audit
surface for the forced role-occupancy endpoint over the received SM-6 carrier
exhaustion closure, not a claim that this repository rederives every upstream
Standard Model component independently.
