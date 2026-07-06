# NNR8 Endpoint Upgrade Dependency Audit

This note records what must be checked before the NNR8 endpoint can be upgraded
from a conditional branch-closure theorem to an admitted AASC endpoint.

The new Lean endpoint is packaged by:

```lean
AASCNNR8EndpointUpgradeBundle
```

and its admission audit is:

```lean
AASCNNR8UpgradeAdmissionAudit C M H N S
```

Once the bundle is inhabited, Lean derives:

```lean
AASCNNR8EndpointUpgradeBundle.singletonEndpoint
AASCNNR8EndpointUpgradeBundle.noSecondPoint
```

## Endpoint Status

The upgrade is not a numerical mass or ratio computation.

It is:

```text
the admitted same-scope hybrid branch space collapses to a singleton:
the current standing neutrino splitting ratio uniquely survives.
```

The endpoint should be stated as:

```text
StandingNeutrinoRatioCertified
RatioIntervalLocked_0_lt_rho_lt_1
HybridJointRestrictionSingleton
CurrentStandingRatioUniquelySurvives
NoSecondPoint
NoNonCurrentBranchSurvivesUEAPKernelAudit
RatioValueNotComputed
EmpiricalComparisonStillUnopened
```

## The Five Inputs

The proof uses five named objects:

| Lean object | Role | Upgrade pressure |
| --- | --- | --- |
| `C : StandingRatioCertificate` | Standing neutrino ratio certificate | Must be the actual standing ratio target, not a placeholder. |
| `M : MR3SpectralSourceAdmission C` | MR3 spectral-source admission | Must be source-certified, quotient-stable, calibration-free, and transport-closed. |
| `H : AASCHybridCompressionNetwork C M` | Hybrid modular/spectral/scoto joint restriction | Must be admitted as the lawful same-scope joint restriction. |
| `N : AASCNoEleventhNeutrinoRoute C M H` | Route census | Must be complete: no same-scope route lies outside the census. |
| `S : AASCCorpusBranchSupportLedger C` | Corpus support ledger | Must supply the cited branch-exhaustion source families. |

If all five are admitted, the NNR8 upgrade is unconditional relative to the
AASC corpus.

If any one is not admitted, the correct theorem status is conditional.

## Main Pressure Points

## Current Deepest Blocker

The next dependency descent exposes a real proof-boundary:

```text
H and N contain several admission fields as propositions, not as already
available proof terms.
```

Examples:

```lean
H.crossTargetAligned : Prop
H.crossTransportCoherent : Prop
H.crossNoOvercounting : Prop
H.crossNoHiddenSelector : Prop

N.noUncarriedSameTargetConstraint : Prop
N.noLegacyTheoryOutsideCensus : Prop
N.noExperimentalMethodOutsideCensus : Prop
N.noScopeChangingRouteCountsSameScope : Prop
N.noEmpiricalValueImportAsRoute : Prop
```

Therefore the next real blocker is not the singleton theorem. It is the
source-level admission evidence for these propositions. Lean now represents
this via:

```lean
AASCNNR8InputAdmissionChain
```

which requires explicit proofs of:

```lean
AASCHybridSameScopeAdmission C M H
AASCNoEleventhRouteCensusAdmitted C M H N
```

This is useful: it prevents the upgrade from silently treating named fields as
certified. The next paper/Lean work must discharge these `H` and `N` admission
propositions from the corpus.

This blocker has now been reduced to two proof-carrying witness objects:

```lean
AASCHybridSameScopeAdmissionWitness C M H
AASCNoEleventhRouteCensusWitness C M H N
```

Lean proves:

```lean
hybridSameScopeAdmissionWitnessClearsH
noEleventhRouteCensusWitnessClearsN
inputAdmissionChainFromHNWitnesses
```

So the remaining evidence is no longer diffuse. It is exactly the following
ten proof fields:

```lean
H.crossTargetAligned
H.crossTransportCoherent
H.crossNoOvercounting
H.crossCalibrationFree
H.crossNoHiddenSelector

N.noUncarriedSameTargetConstraint
N.noLegacyTheoryOutsideCensus
N.noExperimentalMethodOutsideCensus
N.noScopeChangingRouteCountsSameScope
N.noEmpiricalValueImportAsRoute
```

The next reduction is also implemented. The endpoint bundle can now be built
directly from:

```lean
AASCNondegenerateUEAPKernelOperationalization C M H N S
MR3SpectralSourceAdmissionWitness M
AASCHybridSameScopeAdmissionWitness C M H
AASCNoEleventhRouteCensusWitness C M H N
```

by:

```lean
endpointUpgradeBundleFromKernelOperationalizationAndWitnesses
```

This clears the standing certificate automatically from `C`, obtains
current-point identification from the kernel operationalization, and supplies
default corpus reason handles for the non-current branch classes. The remaining
source-level proof burden is therefore:

```text
1. MR3 source witness: seven source-admission fields.
2. H witness: five hybrid cross-route gates.
3. N witness: five route-census exclusion gates.
4. Nondegenerate UEAP kernel operationalization itself.
```

This has now been compressed into one minimal source-proof object:

```lean
AASCNNR8CoreSourceProofBundle C M H N S
```

Lean proves:

```lean
coreSourceProofBundleGivesEndpointSingleton
coreSourceProofBundleRulesOutSecondPoint
```

The bundle fields are the current frontier:

```text
MR3 witness:
  sourceCertified
  standingSpectralCarrier
  quotientStable
  transportClosed
  calibrationFree
  extractionCertified
  sourceInducesShapeMap

H witness:
  crossTargetAligned
  crossTransportCoherent
  crossNoOvercounting
  crossCalibrationFree
  crossNoHiddenSelector

N witness:
  noUncarriedSameTargetConstraint
  noLegacyTheoryOutsideCensus
  noExperimentalMethodOutsideCensus
  noScopeChangingRouteCountsSameScope
  noEmpiricalValueImportAsRoute

Operationalization proofs:
  currentPointIdentification
  jointSurvivorUEAPLegitimacy
  kernelForcedUEAPFailure
```

### 1. Hybrid Network Admission (`H`)

The hybrid modular/spectral/scoto network must not be an arbitrary
intersection of useful constraints. It must be the lawful same-scope joint
restriction for the standing ratio target.

Checklist:

| Required check | Meaning |
| --- | --- |
| Modular route admitted | Modular/flavor algebra is allowed only as a same-target restriction, not a value selector. |
| Spectral route admitted | Spectral quotient pressure is quotient-stable and calibration-free. |
| Scoto/seesaw route admitted | Mechanism separation preserves the solar/atmospheric role structure without hidden parameter repair. |
| Cross-target alignment | All three routes constrain the same standing ratio target. |
| Cross-transport coherence | The route transports agree on the same admissible carrier. |
| No overcounting | The intersection does not double-count equivalent skin/chart presentations. |
| No hidden selector | No route imports observed values, fitted phases, absolute masses, or endpoint choices. |
| Same-scope nonemptiness | The current standing ratio lies in the joint restriction. |

Special caution: the current Lean structure `AASCHybridCompressionNetwork`
contains a `jointRestrictionSingleton` field. For the paper upgrade, the
singleton endpoint should be derived from non-degenerate UEAP kernel closure,
not merely assumed through this field. The admission proof for `H` should
therefore cite its restriction/audit/same-scope fields, while the endpoint
proof should use:

```lean
nondegenerateUEAPKernelOperationalizationGiveJointSingleton
```

### 2. No-Eleventh-Route Census (`N`)

The route census must be complete. It is not enough to list familiar model
families; the audit must show that every lawful same-scope candidate route is
carried by the census or is excluded as scope-changing, empirical, or
bookkeeping.

Checklist:

| Required check | Meaning |
| --- | --- |
| Carrier completeness | Every joint-admissible ratio candidate has an exposed route carrier. |
| No uncarried same-target constraint | There is no extra same-target constraint outside the route list. |
| No legacy theory outside census | Existing model families are represented or ruled out as non-same-scope. |
| No experimental method outside census | Oscillation, matter, beta, cosmological, and boundary methods are represented or firewall-blocked. |
| No scope-changing route counted same-scope | Sterile/singlet/AdS extensions count only if projected back to the admitted residual quotient. |
| No empirical value import | Observed splittings or absolute masses are not used as selectors. |
| Current carrier fixed | The current ratio maps to the current standing carrier, not to a retroactive survivor label. |

## Branch Exhaustion Modulo Skin

The non-current branch audit is now organized by UEAP coordinate failures:

| Branch | Coordinate failure | Corpus reason |
| --- | --- | --- |
| `modularOnlyBranch` | `alternativesNotExhaustedModuloSkin` | NNR4G/H no motif-to-target promotion. |
| `scotoParameterFiberBranch` | `launderingNotExcluded` | Residual no hidden parameter repair. |
| `spectralWithoutFiniteCollapseBranch` | `evidenceNetworkNotClosed` | Quotient-fiber exhaustion missing. |
| `sterileScopeExtensionBranch` | `scopeUnfixed` | Same-scope domain extension blocked. |
| `phaseTopologyBreakingBranch` | `reportNotPreserving` | Phase readback is not a magnitude selector. |
| `matterTransportBreakingBranch` | `targetCarrierMisaligned` | Fixed-base operator strengthening blocked. |
| `absoluteMassImportBranch` | `boundaryNotDeclared` | Boundary data import blocked. |
| `diracMajoranaSelectorBranch` | `targetAncestryNotSeparated` | Invariant endpoint selector blocked. |
| `identitySelectorBranch` | `carrierInadequate` | Quotient skin/bookkeeping. |

The audit obligation is:

```lean
kernelForcesAssignedUEAPFailure
```

Plainly:

```text
in the non-degenerate regime, the admissibility kernel forces the assigned
UEAP coordinate failure for every non-current draft branch.
```

## Current Standing Ratio Check

The current branch must be point-identifying. It cannot mean merely:

```text
whatever branch survived.
```

It must mean:

```text
the standing ratio object fixed by the standing certificate C, occupying the
unique admissible interior under the non-degenerate kernel.
```

This is supplied by:

```lean
AASCNondegenerateKernelInteriorAdmission
```

and used by:

```lean
nondegenerateCurrentClassOccupiesUniqueInterior
```

## Conditional vs Upgraded Status

Conditional status:

```text
Given admitted C, M, H, N, S and non-degenerate UEAP kernel operationalization,
the hybrid joint restriction is singleton.
```

Upgraded NNR8 status:

```text
C, M, H, N, S are AASC-admitted inputs, and the non-degenerate UEAP kernel
operationalization is inhabited. Therefore NNR8 has a certified singleton
branch-space endpoint.
```

The upgrade bundle in Lean records this distinction:

```lean
structure AASCNNR8EndpointUpgradeBundle
```

## Recommended Patch Language

Use:

```text
The NNR8 endpoint is upgraded from interval-only standing to same-scope
branch-space singleton closure. The result does not compute a numerical value
for the neutrino splitting ratio. It proves that, under the admitted AASC
same-scope hybrid restriction and no-eleventh-route census, all non-current
branches fail the non-degenerate UEAP kernel audit and the current standing
ratio uniquely survives.
```

Avoid:

```text
The neutrino mass ratio has been computed.
```

Avoid:

```text
The current ratio is whatever survived the audit.
```

Use instead:

```text
The current standing ratio is the certificate-fixed standing target, and the
audit proves that no non-current same-scope branch can supply a second point.
```
