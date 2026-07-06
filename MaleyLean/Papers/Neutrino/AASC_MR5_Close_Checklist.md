# AASC MR5 Close Checklist for the Neutrino Ratio Blocker

This file maps the v1.5 AASC corpus census to the Lean close theorem in
`RatioBlocker.lean`.

Lean close target:

```lean
theorem mr5ConstructionGivesRatioCompression
  (C : StandingRatioCertificate)
  (S : AASCMR5ShapeConstructionTheorem C) :
  RatioInvariantCompressionPrinciple C
```

The remaining construction burden is to instantiate
`AASCMR5ShapeConstructionTheorem` for the standing neutrino ratio target.

## Source Admission Fields

| Lean field | AASC source row(s) | Paper burden |
| --- | --- | --- |
| `sourceAdmission` | `AASC-MR3-THM-010` | Exhibit the neutrino spectral/hierarchy source package as an admitted MR3 source. |
| `sourceInducesShapeMap` | `AASC-MR3-DEF-003`, `AASC-MR3-THM-009` | Define the source-induced shape map and prove it restricts the standing ratio shape fiber. |
| `sourceCertified` | `AASC-MR3-THM-010` | Discharge source legitimacy conditions without target-derived fitting. |
| `standingSpectralCarrier` | `AASC-MR3-THM-010` | Show the source acts on the standing spectral carrier for the same numerator/denominator roles. |
| `quotientStable` | `AASC-MR3-THM-008`, `AASC-MR3-THM-009` | Show the source descends to the quotient/ledger level. |
| `transportClosed` | `AASC-MR5-THM-005` | Show all cross-domain moves are standing-preserving transports. |
| `calibrationFree` | `AASC-MR2-THM-008`, `AASC-MR5-THM-006` | Delete observed inventory, fitted hierarchy, target proxies, and downstream success criteria. |
| `extractionCertified` | `AASC-MR3-THM-008` | Prove the source-to-ledger extraction is invariant and not a hidden selector. |

## MR5 Singleton Network Fields

| Lean field | AASC source row(s) | Paper burden |
| --- | --- | --- |
| `SectorConstraint` | `AASC-MR5-DEF-002`, `AASC-MR5-DEF-006` | Define the admitted source-node restrictions used in the joint fiber. |
| `activeConstraint` | `AASC-MR5-DEF-004`, `AASC-MR5-PROT-001` | Mark which restrictions are counted as active collapse pressure. |
| `independentConstraint` | `AASC-MR5-PROT-001`, `AASC-MR5-THM-010` | Prove active constraints are not dependent copies. |
| `nonredundantConstraint` | `AASC-MR5-DEF-005`, `AASC-MR5-THM-011` | Extract a minimal irredundant collapse witness. |
| `networkNonempty` | `AASC-MR5-THM-007` | Rule out empty-fiber contradiction before claiming uniqueness. |
| `sameTargetAligned` | `AASC-MR5-DEF-006`, `AASC-EX8-DEF-6-1` | Show all restrictions hit the same neutrino ratio target. |
| `noOvercounting` | `AASC-MR5-THM-010` | Distinguish genuine overconstraint from repeated evidence. |
| `noHiddenSelector` | `AASC-MR3-THM-008`, `AASC-MR5-THM-006` | Prove no observed target inventory or proxy selects the value. |
| `shapeFiberSoundForMinimalInterval` | `AASC-MR2-THM-005` | Show the current shape fiber stays inside the standing minimal interval. |
| `restrictedShapeFiberSingleton` | `AASC-MR5-THM-009`, `AASC-MR5-THM-011` | Prove the joint restricted fiber is a non-empty singleton at the current ratio. |

## Close Logic

Once those fields are instantiated, Lean performs the rest:

1. `mr5NetworkGivesMR2ShapeFiberCollapse` converts the MR5 singleton network into the MR2 fiber-collapse theorem.
2. `mr5ConstructionAsNormalFormSourceTheorem` turns MR2/MR3/MR5 data into an audited normal-form source theorem.
3. `mr5ConstructionGivesRatioCompression` proves every lawful same-target deformation fixes the ratio.
4. `mr5ConstructionKillsLiveDeformations` rules out the live deformation blocker.

So the paper does not need a new logical principle. It needs the neutrino-specific
MR5 construction witness.

## Environment Verdict

This environment can complete the Lean close conditional on a supplied
neutrino-specific `AASCMR5ShapeConstructionTheorem`.

The current v1.5 census also preserves the NNR8 obstruction:

| NNR8 row | Current status |
| --- | --- |
| `NEU-Neutrino_ARC_NNR8_Manuscript_1A4A8D-THM-009` | magnitude-compression certificate exhaustion |
| `NEU-Neutrino_ARC_NNR8_Manuscript_1A4A8D-THM-011` | shape-fiber restriction without collapse |
| `NEU-Neutrino_ARC_NNR8_Manuscript_1A4A8D-THM-016` | supersession requires a stronger source-certified theorem |

So, from the presently exposed corpus rows alone, the close is not unconditional.
The exact missing object is not another Lean theorem; it is the source-certified
neutrino MR5 singleton witness discharging `restrictedShapeFiberSingleton`.

Lean now records both sides:

```lean
theorem mr5ConstructionGivesRatioCompression
  (C : StandingRatioCertificate)
  (S : AASCMR5ShapeConstructionTheorem C) :
  RatioInvariantCompressionPrinciple C

theorem mr3SecondShapePointBlocksMR5Network
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (hsecond : MR3ShapeFiberHasSecondPoint C M) :
  Not (Nonempty (MR5CrossSectorShapeSingleton C M))
```

## Candidate Source Filter

The search for a new witness now has a Lean target for candidate law forms:

```lean
inductive NeutrinoCompressionLawForm where
  | algebraicSumRule
  | finiteResidualOrbit
  | spectralQuotient
  | hierarchyCompression

structure NeutrinoCompressionCandidate
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
```

This mirrors the NNR4G audit families. A candidate is not enough because it
exists in the literature or fits the measured ratio. It must pass:

| Gate | Meaning |
| --- | --- |
| `sourceAncestryCertified` | The law form has AASC source ancestry, not just model-building motivation. |
| `targetPreservingTransport` | The law acts on the standing neutrino ratio target. |
| `quotientStable` | The law descends to the quotient/shape level. |
| `calibrationFree` | It survives deletion of observed target values and fitted proxies. |
| `noObservedValueImport` | It does not use measured splitting values to fix the output. |
| `noComparatorPromotion` | It does not promote empirical agreement or analogy to source status. |
| `noBranchSelector` | It does not choose ordering/sign/branch by convention or fit. |
| `noIdentityShapeSelector` | It is not the tautological identity map on the target ratio. |
| `collapsesShapeFiber` | It actually proves the restricted shape fiber is singleton. |

## Extended Constraint Matrix

The later Lean additions refine the MR5 checklist with convergence and
candidate-index eliminator layers. These are not independent value theorems;
they are admissible ways to discharge `restrictedShapeFiberSingleton` or to
construct the all-but-one ledger that implies it.

| Constraint layer | Lean object | Matrix role | Remaining burden |
| --- | --- | --- | --- |
| Hybrid three-route bridge | `AASCHybridCompressionNetwork` | Intersects modular/sum-rule, spectral quotient, and scoto-seesaw restrictions. | Prove `jointRestrictionSingleton`. |
| Scoto-modular phase locus | `AASCScotoModularPhaseIntersection` | Intersects tree-seesaw atmospheric carrier, scotogenic solar carrier, modular mass-matrix relation, and phase-coherent readback. | Prove `intersectionSingleton`. |
| Singlet / AdS convergence | `AASCSingletAdSConvergence` | Intersects radiative scalar-singlet, sterile gauge-singlet, and AdS/transport-rigidity pressure. | Prove `convergenceSingleton`. |
| Six-route master convergence | `AASCNeutrinoSixRouteConvergence` | Bridges the two three-route modules with same target, coherent transport, no overcounting, common quotient-skin, no selector, and no observed-value import. | Prove `sixRestrictionSingleton`. |
| Candidate-index ledger | `AASCCandidateIndexLedger` | Replaces a one-shot singleton proof by a survivor-index classification. | Prove completeness, non-current elimination, and current-index injectivity. |
| Method-invariant witness layer | `AASCMethodInvariantWitnessLedger` | Lets independent experimental method classes eliminate candidate indices without selecting by observed values. | Prove `MethodRefinedCandidateIndexLedger`. |
| Phase-coherence witness layer | `AASCPhaseCoherenceWitnessLedger` | Uses mass-basis phase transport, flavor-projection interference, coherence, and baseline/energy covariance as topology-level eliminators. | Prove `PhaseRefinedCandidateIndexLedger` and no observed phase-value/fit import. |
| Neutrino-specific discriminator layer | `AASCNeutrinoSpecificDiscriminatorLedger` | Uses neutrality, weak-only boundaries, mass/flavor mismatch, macroscopic coherence, two-scale splitting, matter-effect compatibility, Dirac/Majorana no-selector control, sterile-singlet scope control, and cross-method L/E covariance. | Prove `NeutrinoDiscriminatorRefinedCandidateIndexLedger` and no observed-value/fit import. |

The phase-coherence row is the new addition from the oscillation discussion.
Its purpose is to eliminate candidates that break coherent phase topology; it
does not claim that kinetic energy fluctuates into rest mass and it does not
select the ratio by measured oscillation parameters.

The neutrino-specific discriminator row is the broader structural layer. Its
purpose is to make native neutrino features act as eliminators rather than fit
knobs.

## Draft Elimination Pass

Lean now contains a first finite draft taxonomy:

```lean
inductive NeutrinoDraftCandidateIndex
```

The draft pass eliminates every named non-current class:

| Survivor class | Lean result |
| --- | --- |
| `currentStandingRatio` | unique uneliminated draft class |

The certified Lean statements are:

```lean
theorem draftCandidatePassOnlyCurrentSurvives
theorem draftCandidatePassEliminatesNoncurrent
```

The bridge from draft taxonomy to the real all-but-one ledger is:

```lean
structure AASCDraftTaxonomyCompleteness
def draftTaxonomyCompletenessAsCandidateIndexLedger
```

and the close/rule-out theorems are:

```lean
theorem draftTaxonomyCompletenessGivesJointSingleton
theorem draftTaxonomyCompletenessRulesOutSecondPoint
```

So the final AASC close now reduces to constructing
`AASCDraftTaxonomyCompleteness`: every admissible ratio in the hybrid joint
restriction must map into the taxonomy, every non-current class must be
impossible there, and the current class must be injective.

The non-circular construction route is:

```lean
structure AASCJointRestrictionCaseSplit
def caseSplitGivesDraftTaxonomyCompleteness
```

This is the next proof target: establish a complete disjunction over the actual
joint restriction and prove every non-current branch impossible.

The no-eleventh-route version of this target is now formalized:

```lean
structure AASCNoEleventhNeutrinoRoute

structure AASCNoEleventhRouteCaseSplitConstruction

theorem noEleventhRouteGivesJointSingleton

theorem noEleventhRouteRulesOutSecondPoint
```

This does not fake the witness by classifying every point as current. The
route census supplies a visible carrier for every admissible same-target route,
and the construction proves that the carrier's draft class is either the
current class or an impossible non-current class. In plain terms: if an
eleventh way existed as real physics or legacy theory, it would have to enter
the census as a carrier; otherwise it is outside the same-target admissible
scope.

The Impossibility Suite now has a Lean bridge into that construction:

```lean
inductive AASCImpossibilityKernel

structure AASCImpossibilitySuiteAudit

theorem impossibilitySuiteAuditGivesJointSingleton

theorem impossibilitySuiteAuditRulesOutSecondPoint
```

The kernels are: no generators, no carriers, no repairs, no domain transfer,
fail-closed, no partial closure, no admissibility-relevant parameterization,
fixed-domain exhaustion, no hidden third locus, operator exhaustion, and the
AMetric boundary. The remaining paper burden is to prove, for each non-current
draft class, that the assigned kernel eliminates it on the hybrid joint
restriction.

The default branch-to-kernel map is now part of the audit:

| Draft branch | Default impossibility kernel |
| --- | --- |
| `modularOnlyBranch` | no admissibility-relevant parameterization |
| `scotoParameterFiberBranch` | no repairs |
| `spectralWithoutFiniteCollapseBranch` | no partial closure |
| `sterileScopeExtensionBranch` | no domain transfer |
| `phaseTopologyBreakingBranch` | fail-closed |
| `matterTransportBreakingBranch` | fixed-base operator conservativity |
| `absoluteMassImportBranch` | no generators |
| `diracMajoranaSelectorBranch` | invariant endpoint selection |
| `identitySelectorBranch` | fixed-domain exhaustion |

The operator-theory papers add a focused sub-audit:

```lean
inductive AASCOperatorStrengtheningStatus

structure AASCFixedBaseOperatorAudit
```

It uses the fixed-base theorem shape: every apparent same-base operator
strengthening is conservative on old-base content, external, carrier-changing,
selector-importing, or an invariant endpoint. Conservative and invariant
endpoint cases must identify the current ratio; the other three are
inadmissible as same-scope routes.

The final audit object now has a branch-facing constructor:

```lean
structure AASCBranchImpossibilityAudit

def branchImpossibilityAuditAsImpossibilitySuiteAudit

theorem branchImpossibilityAuditGivesJointSingleton

theorem branchImpossibilityAuditRulesOutSecondPoint
```

This is the immediate close target. Fill the current-class injectivity field
and the nine named branch-impossibility fields, and Lean constructs the full
`AASCImpossibilitySuiteAudit` and closes the joint singleton.

NNR4G/NNR4H now have a dedicated source-ledger bridge:

```lean
structure AASCNNR4GHMagnitudeCompressionLedger

structure AASCNNR4GHBranchTranslation

theorem nnr4ghBranchTranslationGivesJointSingleton

theorem nnr4ghBranchTranslationRulesOutSecondPoint
```

This bridge uses the NNR4G/H named failures: no illicit stronger-output route,
no carrier-derived polynomial, no motif-to-target promotion, finite orbit not
same-target transported, no finite-collapse/overlap certificate, no
source-certified hierarchy package, no quotient-normal-form evaluator, and
named certificate-failure exhaustion. It still requires the paper-specific
translation from those NNR failures to the nine branch fields.

Additional corpus support is now represented in Lean:

```lean
structure AASCCNF2FiniteCollapseLedger
structure AASCCNF6SpectralForcingLedger
structure AASCCNF7PhaseMixingLedger
structure AASCATSRoleDecompositionLedger
structure AASCUniqueAdmissibleInteriorLedger
structure AASCCorpusBranchSupportLedger
```

These ledgers support the branch translation without pretending to close it:
CNF2 supports finite-collapse discipline, CNF6 supports spectral/mass-ratio
quotient discipline, CNF7 supports phase/mixing topology discipline, and ATS
supports the tensor-vs-skin distinction for parameter and identity branches.
Unus Solus supports the positive uniqueness side: same fixed boundary plus same
standing classification admits no second same-domain admissible interior.

The constructive bridge attempt is now explicit:

```lean
structure AASCSharedConvergencePointIdentification

structure AASCScotoModularPhaseParameterCollapse

theorem sharedConvergencePointIdentificationGivesJointSingleton

theorem scotoModularPhaseCollapseGivesJointSingleton

theorem scotoModularPhaseCollapseRulesOutSecondPoint
```

This is the theorem the extension paper would need to prove if no ready-made
singleton witness exists. It asks for source-fixed-or-skin modular/scoto
parameters, finite or reduced spectral quotient, quotient-stable phase readback,
and no observed-value, alignment/phase-branch, or external-endpoint selector.

The point-identification form is the clean mental model: prove the shared
convergence of modular, scoto/seesaw, spectral, phase/rephasing, and
role-occupancy structure identifies the current ratio point, rather than only
filtering out bad routes.

The Unus Solus bridge to current-class injectivity is:

```lean
structure AASCUniqueInteriorRatioRealization
```

It is the clean positive target: prove the standing-ratio current class is an
instance of the unique admissible interior, then any same-domain current-class
occupant is the current ratio.

Residual-parameter support is now explicit:

```lean
structure AASCResidualParameterExhaustionLedger
structure AASCQuotientRawExactnessLedger
structure AASCParameterSurvivalClassificationLedger
structure AASCResidualFreedomClosureAudit
structure AASCResidualCorpusPointClosure
structure AASCNeutrinoBridgeTranslation
structure AASCAdmittedNeutrinoSector
structure AASCNeutrinoBridgeAdmissionProof
structure AASCNeutrinoAdmissionIngredients
structure AASCFormalInteriorUniquenessAdapter
structure AASCNondegenerateKernelInteriorAdmission

theorem residualFreedomClosureAuditGivesJointSingleton
theorem residualFreedomClosureAuditRulesOutSecondPoint
theorem residualCorpusPointClosureGivesJointSingleton
theorem residualCorpusPointClosureRulesOutSecondPoint
theorem neutrinoBridgeTranslationGivesResidualCorpusPointClosure
theorem neutrinoBridgeTranslationGivesBranchAudit
theorem neutrinoBridgeTranslationGivesJointSingleton
theorem neutrinoBridgeTranslationRulesOutSecondPoint
theorem currentRatioGivesHybridJointRestrictionNonempty
theorem admittedNeutrinoSectorGivesBridgeTranslation
theorem admittedNeutrinoSectorGivesBranchAudit
theorem admittedNeutrinoSectorGivesJointSingleton
theorem admittedNeutrinoSectorRulesOutSecondPoint
theorem bridgeAdmissionProofGivesAdmittedNeutrinoSector
theorem bridgeAdmissionProofGivesJointSingleton
theorem bridgeAdmissionProofRulesOutSecondPoint
theorem admissionIngredientsGiveBridgeAdmissionProof
theorem admissionIngredientsGiveJointSingleton
theorem admissionIngredientsRulesOutSecondPoint
theorem formalInteriorUniquenessAdapterIdentifiesCurrentPoint
theorem formalInteriorUniquenessAndBranchAuditGiveJointSingleton
theorem formalInteriorUniquenessAndBranchAuditRulesOutSecondPoint
theorem nondegenerateKernelAndBranchAuditGiveJointSingleton
theorem nondegenerateKernelAndBranchAuditRulesOutSecondPoint
def residualCorpusPointClosureAsNeutrinoBridgeTranslation
def sharedConvergencePointIdentificationAsNeutrinoBridgeTranslation
def branchImpossibilityAuditAsNeutrinoBridgeTranslation
def noEleventhCaseSplitAsNeutrinoBridgeTranslation
def scotoModularPhaseCollapseAsNeutrinoBridgeTranslation
theorem residualCorpusPointClosureEquivalentToBridgeTranslation
theorem branchAuditEquivalentToBridgeTranslation
def noEleventhCaseSplitAsResidualCorpusPointClosure
def branchImpossibilityAuditAsNoEleventhRouteCaseSplitConstruction
def branchImpossibilityAuditAsResidualCorpusPointClosure
def residualCorpusPointClosureAsBranchImpossibilityAudit
def sharedConvergencePointIdentificationAsBranchImpossibilityAudit
def scotoModularPhaseCollapseAsBranchImpossibilityAudit
def hybridSingletonAsResidualCorpusPointClosure
theorem noEleventhCaseSplitResidualCorpusClosureGivesJointSingleton
theorem branchImpossibilityResidualCorpusClosureGivesJointSingleton
theorem branchImpossibilityResidualCorpusClosureRulesOutSecondPoint
theorem residualCorpusPointClosureProvesBranchAuditAndSingleton
theorem sharedConvergenceProvesBranchAuditAndSingleton
theorem scotoModularPhaseCollapseProvesBranchAuditAndSingleton
theorem hybridSingletonResidualCorpusClosureGivesJointSingleton
```

These objects encode the residual-parameter corpus distinction: a remaining
degree of freedom must be fixed-boundary data, quotient-skin, witness-forced
content, or an inadmissible same-scope repair/selector. The audit also keeps
the quotient-singleton/raw-exactness distinction visible, so a bare quotient
singleton is not silently promoted to raw numerical exactness.

The remaining mathematical burden has become very sharp:

1. identify the residual paper's Global Coherence Intersection with the
   modular/scoto/spectral/phase/role shared locus;
2. prove that this shared locus identifies the current ratio point;
3. prove every non-current residual branch is exhausted under the fixed
   same-scope classification.

This burden is now packaged as:

```lean
structure AASCNeutrinoBridgeTranslation
```

Filling that one object gives the residual corpus point closure, the branch
audit, the joint singleton, and the no-second-point theorem.

The main proof interfaces are now interchangeable:

```text
AASCNeutrinoBridgeTranslation
<-> AASCResidualCorpusPointClosure
<-> AASCBranchImpossibilityAudit
```

The equivalence is at the level of inhabited proof objects. This means the
paper can present whichever interface is most natural, while Lean can translate
it into the others.

The slogan-safe existence chain is:

```text
current standing ratio exists in the hybrid joint restriction
  -> HybridJointRestrictionNonempty

AASCAdmittedNeutrinoSector
  -> AASCNeutrinoBridgeTranslation
  -> AASCBranchImpossibilityAudit
  -> HybridJointRestrictionSingleton
```

Nonemptiness alone is deliberately weaker than closure. The admitted-sector
object adds the AASC same-scope, GCI, quotient-exactness, parameter-normal-form,
point-identification, and branch-exhaustion claims.

The next proof target is now:

```lean
structure AASCNeutrinoBridgeAdmissionProof
```

It has four paper-facing lemma groups: same-scope admission, GCI identification,
current-class point identification, and non-current branch exhaustion. See
`NeutrinoBridgeAdmission_Workplan.md` for the detailed proof plan.

This has been decomposed further as:

```lean
structure AASCNeutrinoAdmissionIngredients
```

requiring a unique-interior current-point realization and a branch-impossibility
audit. The current-point side now reuses the earlier formal theorem:

```lean
uniqueness_of_admissible_interior
```

through:

```lean
structure AASCFormalInteriorUniquenessAdapter
```

The remaining direct target is therefore the formal adapter plus the
branch-impossibility audit.

The unique-interior current-point realization now has a kernel-paper route:

```lean
structure AASCNondegenerateKernelInteriorAdmission
```

It records the claim that non-degenerate standing forces the admissibility
kernel and therefore forces the current class into the unique admissible
interior. With that object plus the branch audit, Lean closes the singleton.

The corpus now supplies the surrounding discipline: fixed residual scope,
same-scope competitor tests, enlarged-domain separation, repair-prohibition,
quotient-fiber exactness, parameter normal form, and standing-bearing
parameter classification.

There are now two ways to inhabit the residual close object:

- `noEleventhCaseSplitAsResidualCorpusPointClosure` is the non-circular paper
  route. It requires a real `AASCNoEleventhRouteCaseSplitConstruction`, i.e.
  current-class injectivity plus elimination of every non-current draft class.
- `branchImpossibilityAuditAsResidualCorpusPointClosure` is the most practical
  paper route. It requires the branch-facing audit fields directly and then
  constructs the no-eleventh case split and residual corpus closure.
- The reverse direction is now explicit too:
  `residualCorpusPointClosureAsBranchImpossibilityAudit`,
  `sharedConvergencePointIdentificationAsBranchImpossibilityAudit`, and
  `scotoModularPhaseCollapseAsBranchImpossibilityAudit` construct the branch
  audit from the corresponding stronger theorem object.
- `hybridSingletonAsResidualCorpusPointClosure` is a plumbing sanity check. It
  uses the already-present `H.jointRestrictionSingleton` field, so it proves the
  residual object only after singleton closure has already been supplied.

The close theorem for candidates is:

```lean
theorem auditedCandidateGivesRatioCompression
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (W : NeutrinoCompressionCandidate C M)
  (_haudit : NeutrinoCompressionCandidateAuditPasses W)
  ... :
  RatioInvariantCompressionPrinciple C
```

The failure theorem is:

```lean
theorem candidateFailureBlocksCompression
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (hfail : CandidateSourceFiberStillHasSecondPoint C M) :
  Not (RatioInvariantCompressionPrinciple C)
```

External literature search suggests likely candidates in mass-sum-rule and
modular-flavor models, but those currently look like model-dependent or
empirically combined constraints rather than already AASC-certified singleton
witnesses. They should be tested through this filter rather than imported as
conclusions.
