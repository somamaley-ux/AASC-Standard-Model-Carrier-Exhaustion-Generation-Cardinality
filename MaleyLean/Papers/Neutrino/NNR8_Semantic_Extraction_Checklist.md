# NNR8 Semantic Extraction Checklist

Target Lean object:

```lean
AASCNNR8SemanticExtractionCertificate C M H N S
```

This is the bridge from pulled corpus text to the endpoint theorem. Each field
is a source-backed proof:

```lean
AASCSourceBackedProof p
```

meaning:

```text
source row + extracted semantic claim + proof of the target proposition p
```

Lean now proves:

```lean
semanticExtractionGivesEndpointSingleton
semanticExtractionRulesOutSecondPoint
```

The semantic layer has also been tightened to a canonical-primary-source
version:

```lean
AASCPrimarySourceBackedProof
AASCNNR8PrimarySemanticExtractionCertificate
primarySemanticExtractionGivesEndpointSingleton
primarySemanticExtractionRulesOutSecondPoint
```

In this version, the proof writer no longer chooses the source row. Each field
uses the primary source assigned by:

```lean
primarySourceForCoreFrontierField
```

So the current blocker is fully localized: fill the fields below.

## MR3 Source Witness

Recommended source:

```lean
AASCNNR8CoreSourceID.mr3ShapeSourceTheorem
```

Pulled evidence:

```text
MR3 main.tex lines 55, 60, 204-237, 279, 344, 355, 427, 530, 550.
```

Fields:

| Lean field | Source-backed semantic extraction |
| --- | --- |
| `mr3_sourceCertified` | MR3 defines admitted source certificates and the main source-admission theorem. |
| `mr3_standingSpectralCarrier` | MR3 spectral carrier admission requires standing-bearing carrier. |
| `mr3_quotientStable` | MR3 source equivalence by quotient image and source-map invariance. |
| `mr3_transportClosed` | MR3 transport discipline requires quotient-level relational preservation. |
| `mr3_calibrationFree` | MR3 calibration deletion blocks target-table/proxy leakage. |
| `mr3_extractionCertified` | MR3 extraction certification is required before source admission. |
| `mr3_sourceInducesShapeMap` | MR3 source-induced shape map turns admitted sources into shape-fiber restrictions. |

## Hybrid Witness

Fields:

| Lean field | Recommended source | Semantic extraction |
| --- | --- | --- |
| `h_crossTargetAligned` | `ex8OverconstraintLegitimacy`, `rocRoleOccupancyClosure` | Independent sector certificates are legitimate only when they jointly eliminate freedom through a common standing-bearing realization constraint. |
| `h_crossTransportCoherent` | `noarUniversalOscillationQuotient`, `cs6cSameScopeRivalExhaustion` | Boundary-kernel reconstruction supplies the coherent same-scope transport object; transported interior flavor is not independent. |
| `h_crossNoOvercounting` | `noarUniversalOscillationQuotient`, `mr3ShapeSourceTheorem` | Alleged second objects map to the same quotient object or change scope; equivalent source images are not double-counted. |
| `h_crossCalibrationFree` | `ueapCalibrationOnly`, `cs7ForbiddenPMNSValuePromotion`, `cs7DeferredPMNSValues` | PMNS/numerical values and calibration-only data are not derivation sources. |
| `h_crossNoHiddenSelector` | `ueapLaunderingExclusion`, `mr5EffectStatusSeparation`, `rocLawfulClosureRouteExhaustion` | Compatible support cannot be laundered into singleton selection; hidden selectors are excluded. |

## No-Eleventh Census Witness

Fields:

| Lean field | Recommended source | Semantic extraction |
| --- | --- | --- |
| `n_noUncarriedSameTargetConstraint` | `cs6cSameScopeRivalExhaustion`, `rocLawfulClosureRouteExhaustion` | Same-scope rivals are bookkeeping-equivalent, inadmissible, or scope-changing; lawful closure routes are exhausted. |
| `n_noLegacyTheoryOutsideCensus` | `cs6cSameScopeRivalExhaustion`, `noarNoHiddenFlavorTransport` | Legacy alternatives collapse to boundary-kernel form, hidden selector, or scope change. |
| `n_noExperimentalMethodOutsideCensus` | `cs7ForbiddenPMNSValuePromotion`, `cs7DeferredPMNSValues`, `cs6cScopeExtensionRegistry` | Oscillation, PMNS, boundary, absolute-scale, and extension methods are classified or firewalled. |
| `n_noScopeChangingRouteCountsSameScope` | `cs6cScopeExtensionRegistry`, `cs6cSameScopeRivalExhaustion` | Sterile/BSM/decoherence/collapse extensions are larger scope unless witness-equivalent. |
| `n_noEmpiricalValueImportAsRoute` | `ueapCalibrationOnly`, `cs7DeferredPMNSValues`, `cs7ForbiddenPMNSValuePromotion` | Empirical/numerical values are deferred or forbidden as derivation sources. |

## Operationalization Proofs

Fields:

| Lean field | Recommended source | Semantic extraction |
| --- | --- | --- |
| `currentPointIdentification` | `rocRoleOccupancyClosure`, `noarUniversalOscillationQuotient` | The current standing carrier is the unique admissible occupant under role closure / quotient uniqueness; a second current-class point is skin, invalid, or scope-changing. |
| `jointSurvivorUEAPLegitimacy` | `ueapLaunderingExclusion`, `ex8OverconstraintLegitimacy`, `mr5EffectStatusSeparation` | A joint survivor is not merely compatible support; to be used as a branch-closing route it must satisfy UEAP legitimacy. |
| `kernelForcedUEAPFailure` | `rocLawfulClosureRouteExhaustion`, `ueapLaunderingExclusion`, `cs6cSameScopeRivalExhaustion` | Every non-current branch fails by lawful-route exhaustion: impossibility elimination, quotient skin, source-witness failure, role revision, or scope reset; UEAP records this as a coordinate failure. |

## Current Status

Cleared:

```text
source availability
field-by-field source mapping
semantic-extraction proof interface
endpoint theorem from semantic extraction
```

Remaining:

```text
inhabit AASCNNR8PrimarySemanticExtractionCertificate C M H N S
```

That means writing the actual source-backed proof terms for the fields above.
