# External Candidate Filter Assessment

This note records the first internet-backed pass of candidate witnesses against
the Lean filter in `RatioBlocker.lean`.

Lean target:

```lean
structure NeutrinoCompressionCandidate
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
```

The candidate closes only if it passes `NeutrinoCompressionCandidateAuditPasses`
and supplies `collapsesShapeFiber`.

## Candidate Results

| Candidate family | Source indication | Filter result |
| --- | --- | --- |
| Neutrino mass sum rules | Sum rules are widespread flavor-model predictions. A 2017 analysis argues they are not tied to an enhanced residual symmetry and are instead due to parameter reduction/model building. | Fails `sourceAncestryCertified` for AASC purposes unless a separate source theorem derives the sum rule from the standing carrier. Also fails `collapsesShapeFiber` without an added theorem. |
| Modular `A4` mass sum rule | A modular `A4` type-II seesaw model introduces a physical neutrino-mass sum rule. The abstract says it determines absolute scale when combined with observed mass-squared differences. | Fails `noObservedValueImport` for first-principles ratio compression if the measured splittings are used. Could become a candidate only with a calibration-free derivation of the relevant ratio restriction. |
| Littlest seesaw / constrained sequential dominance | Uses a highly restricted two-right-handed-neutrino model and fixed coupling alignments to predict features of masses and mixing. | Fails `sourceAncestryCertified` unless AASC admits the alignments as source-derived rather than model assumptions. Likely also fails `noBranchSelector` if a phase/alignment choice is selected by phenomenological success. |
| Scoto-seesaw / dynamical scoto-seesaw | Separates atmospheric and solar scales by mechanism: atmospheric at tree-level seesaw, solar radiatively/scotogenically. This is structurally closer to an AASC role-separation story. | Promising for `targetPreservingTransport` and role separation, but published ratio formula still depends on model parameters such as couplings, mediator masses, and dark-sector choices. Fails `restrictionSingleton` unless AASC derives those parameters or quotients them away. |
| Radiative loop-induced scalar-singlet models | Scotogenic and related scalar-singlet extensions generate neutrino masses through loop topology and dark-sector mediators. | Strong source candidate for mechanism separation and finite-loop topology, but still generally carries Yukawa, scalar-potential, mediator-mass, and mixing fibers. Requires `parameterFiberCollapsedOrSkin` before it can help close. |
| Sterile / gauge-singlet neutrino physics | Gauge-singlet right-handed or sterile neutrinos are anomaly-inert with respect to charged SM forcing and can implement seesaw-type mass generation. | Useful because the singlet status can preserve charged-sector constraints, but it is usually a scope extension rather than same-scope singleton pressure. Requires certified readback to the standing ratio and no imported sterile-sector parameter selector. |
| AdS / completion / transport-rigidity physics | AASC rows treat AdS-like or completion-like structure as admissible only when it factors through the standing quotient or is declared as richer-scope structure. | Potentially useful as a no-escape theorem: it can block ambient-completion or duality moves from adding same-scope numerical content. It is not, by itself, a neutrino ratio source. |
| Residual/flavor symmetry mixing rules | Residual symmetries can yield mixing-angle relations in many models. | Does not directly act on the solar-atmospheric mass-splitting ratio; fails `activeForStandingRatio` unless transported to `rho_nu` by a same-target theorem. |
| Oscillation / PMNS invariant witness class | Oscillation data expose mass-squared-difference and PMNS invariant witness classes. | Certified as witness/support, but not a value or singleton source. Fails `collapsesShapeFiber` by current NNR8 status. |

## Current Verdict

No external candidate found so far supplies the missing AASC field:

```lean
collapsesShapeFiber :
  forall r : C.Ratio,
    C.inMinimalInterval r ->
      M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
        r = C.ratio
```

The best use of these candidates is therefore not immediate closure. It is to
structure the next paper's source theorem:

1. Pick a candidate law form.
2. Prove it is source-certified and target-preserving in AASC.
3. Prove it is calibration-free.
4. Prove it avoids branch/identity/comparator selection.
5. Prove actual singleton collapse of the standing ratio shape fiber.

Only step 5 closes the Lean blocker.

## AASC v1.5 Census Rerun

I reran the targeted search against:

```text
g:\AASC corpus may 7\Core spine\ZZZNew Work\ZSubmission versions\Source theorem matrix\UPdating\AASC_Corpus_Control_Matrix_v1_5_New_ERK_May27_Hardened.csv
```

The search matched 89 rows out of 14,813 using singleton, finite-collapse,
hybrid, candidate-index, method-invariant, scoto, and spectral-quotient terms.

The census does expose the general AASC machinery needed by the Lean bridge:

| Source row | Use |
| --- | --- |
| `AASC-MR2-THM-005` | Generic shape-fiber collapse theorem. |
| `AASC-MR5-DEF-006` | Cross-sector shape network and joint restricted fiber. |
| `AASC-MR5-THM-009` | Generic cross-sector shape singleton theorem. |
| `AOTCS-CS_ARC_CS2_Same_C10F5F-THM-002` | Same-target necessity for spectral, mixing, and residue carriers. |
| `ERK20260527-New_erk_files_May_D2FE05-LEM-024` | Generic hybrid reduction pressure. |
| `ERK20260527-New_erk_files_May_7381DE-CST-003` | Fixation exhaustiveness on a declared scope. |
| `ERK20260527-New_erk_files_May_7381DE-CST-004` | No third same-level hybrid fixation regime. |

But the neutrino-specific rows still preserve the blocker:

| Source row | Status |
| --- | --- |
| `NEU-Neutrino_ARC_NNR4G_Manuscript_FEB328-THM-007` | Spectral quotient route eliminated because no finite-collapse certificate is present. |
| `NEU-Neutrino_ARC_NNR4H_Manuscript_0A7976-THM-009` | Spectral quotient compression is conditional on a finite-collapse, overlap-reduction, or solver-reduction certificate. |
| `NEU-Neutrino_ARC_NNR4H_Manuscript_0A7976-THM-010` | Current admitted ledger lacks that certificate. |
| `NEU-Neutrino_ARC_NNR8_Manuscript_1A4A8D-THM-011` | The minimal interval restricts the shape fiber but does not collapse it. |

So the singleton is not available as an already exposed corpus witness. The
available rows strengthen the admissibility and no-cheating gates for the hybrid
bridge, but they do not yet populate the decisive fields:

```lean
candidate-index ledger
current survivor index
completeness over the hybrid joint restriction
elimination of every non-current index
injectivity of the current index on the joint restriction
```

The active close target remains construction of that neutrino-specific ledger.

## AASC Translation Target

Promising candidates can now be converted into an AASC version using:

```lean
structure AASCTranslatedCompressionLaw
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
```

This is the lawful route for turning a modular/flavor/sum-rule model into a
candidate source theorem. The external formula is not counted directly; it must
be translated into an `AASCRestriction : C.Ratio -> Prop`.

For a modular or mass-sum-rule candidate, the needed paper theorem would have
this form:

1. Define the external law object without measured splitting values.
2. Define the AASC restriction on the standing ratio target.
3. Prove `sourceDerivesRestriction`.
4. Prove target-preserving transport from the source domain to `rho_nu`.
5. Prove quotient stability and shape-fiber soundness.
6. Delete observed inputs, comparator success, branch selectors, and identity
   shape selectors.
7. Prove the translated restriction is singleton on the current minimal
   interval.

The decisive Lean fields are:

```lean
shapeFiberSoundForMinimalInterval :
  forall r : C.Ratio,
    M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
      C.inMinimalInterval r

restrictionSingleton :
  forall r : C.Ratio,
    C.inMinimalInterval r ->
      AASCRestriction r ->
        r = C.ratio
```

If both are supplied, Lean converts the translated law into a compression
candidate and proves `translatedLawGivesRatioCompression`.

## Modular / Mass-Sum-Rule AASC Version

The modular/sum-rule route now has a dedicated Lean interface:

```lean
structure AASCModularMassSumRuleTranslation
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
```

This specializes the generic translation target to the most promising external
family. It demands that the modular datum and sum rule be made source-internal,
not fit-selected, transported to the standing ratio target, and proved singleton
after deleting measured splittings, comparator success, and branch selection.

The close theorem is:

```lean
theorem modularMassSumRuleGivesRatioCompression
```

So the next paper can now state a precise theorem:

> If a modular/flavor mass-sum-rule datum satisfies
> `AASCModularMassSumRuleAuditPasses` and its translated restriction is singleton
> on the standing neutrino minimal interval, then the standing neutrino ratio is
> compressed.

The remaining mathematical work is exactly the construction of that translated
restriction and the singleton proof.

## Spectral Quotient / Finite-Collapse AASC Version

The spectral quotient route now has a dedicated Lean interface:

```lean
structure AASCSpectralQuotientCollapseTranslation
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
```

This specializes the candidate filter to the CNF6/QSpec route. It is the formal
version of the currently missing certificate named by NNR4G/NNR4H: a spectral
quotient must descend to the standing ratio target and carry at least one valid
reduction certificate:

```lean
def AASCSpectralQuotientHasReduction
```

where the reduction is one of:

- finite-collapse certificate,
- overlap-reduction certificate,
- solver-reduction certificate.

The close theorem is:

```lean
theorem spectralQuotientGivesRatioCompression
```

This route still requires the same decisive step: `spectralClassSingleton` on
the current minimal interval. Without that singleton theorem, the route can at
most certify finite/residual progress, not exact ratio compression.

## Scoto-Seesaw AASC Version

The scoto-seesaw route now has a dedicated Lean interface:

```lean
structure AASCScotoSeesawTranslation
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
```

This is the most structurally suggestive external candidate so far because it
separates the two roles by mechanism:

- atmospheric scale from a seesaw mechanism,
- solar scale from a radiative/scotogenic mechanism,
- dark-sector structure mediating the subordinate scale.

The AASC translation requires those mechanisms to be source-internal and
target-preserving, and it names the current missing step:

```lean
parameterFiberCollapsedOrSkin
```

Published scoto-seesaw models explain the scale hierarchy by mechanism, but the
ratio formula still contains model parameters. AASC closure would require those
parameters to be either source-collapsed or shown to be quotient-skin for the
standing ratio target.

The close theorem is:

```lean
theorem scotoSeesawGivesRatioCompression
```

So the strongest current research path is:

> Prove an AASC scoto-seesaw source theorem in which the dark/seesaw parameter
> fiber is collapsed or quotient-skin, and the resulting scoto restriction is
> singleton on the current minimal interval.

## Singlet / AdS Pressure Translation

The latest targeted search suggests three additional pressure families:

- radiative loop-induced models with scalar singlets,
- sterile or right-handed gauge-singlet neutrino physics,
- mathematical AdS/completion/transport-rigidity structure.

Lean now records these with:

```lean
inductive AASCSingletAdSPressureFamily

structure AASCSingletAdSPressureTranslation
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
```

The point is not to treat any of these as a value theorem. They must pass:

```lean
AASCSingletAdSPressureAuditPasses
```

and the close theorem remains conditional:

```lean
theorem singletAdSPressureGivesRatioCompression
```

This translation gives the three ideas a legitimate AASC role:

- scalar singlet loops can supply finite loop-topology and dark-sector
  mechanism pressure,
- sterile gauge singlets can supply anomaly-inert extension/readback pressure,
- AdS/completion rigidity can block same-scope ambient escape routes.

But all three still require the decisive field:

```lean
pressureRestrictionSingleton :
  forall r : C.Ratio,
    C.inMinimalInterval r ->
      pressureRestriction r ->
        r = C.ratio
```

So their strongest current use is as refiners of the candidate-index ledger,
not as already available singleton witnesses.

## Singlet / AdS Convergence Target

The convergence of the three new pressure families is now formalized as:

```lean
structure AASCSingletAdSConvergence
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
```

This is the proof-facing version of the intersection idea. The individual
radiative scalar-singlet, sterile gauge-singlet, and AdS/transport-rigidity
routes may each leave a non-singleton fiber, but their joint restriction can
still close if the intersection proves:

- same standing target,
- common quotient-skin status for residual parameters,
- no ambient scope escape,
- no parameter selector at the intersection,
- no observed-value import,
- singleton convergence on the current minimal interval.

The close theorem is:

```lean
theorem singletAdSConvergenceGivesRatioCompression
```

The decisive field is:

```lean
convergenceSingleton :
  forall r : C.Ratio,
    C.inMinimalInterval r ->
      radiative.pressureRestriction r ->
        sterile.pressureRestriction r ->
          ads.pressureRestriction r ->
            r = C.ratio
```

So the intersection is now informative in exactly the AASC sense: it can be
used as a candidate-index eliminator or direct joint singleton witness, but it
still has to prove the singleton rather than assume it.

## Six-Route Master Convergence

The two convergence groups now have a single master bridge:

```lean
structure AASCNeutrinoSixRouteConvergence
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
```

This object combines:

- modular / mass-sum-rule algebraic rigidity,
- spectral quotient / finite-reduction pressure,
- scoto-seesaw mechanism separation,
- radiative scalar-singlet loop pressure,
- sterile gauge-singlet pressure,
- AdS / transport-rigidity no-escape pressure.

It keeps the two three-route modules intact and adds cross-bridge conditions:

- same standing target across both modules,
- coherent transport,
- no overcounting,
- common quotient-skin status,
- no cross-selector,
- no observed-value import.

The close theorem is:

```lean
theorem sixRouteConvergenceGivesRatioCompression
```

The decisive master field is:

```lean
sixRestrictionSingleton :
  forall r : C.Ratio,
    C.inMinimalInterval r ->
      hybrid.modular.ModularRestriction r ->
        hybrid.spectral.spectralRestriction r ->
          hybrid.scoto.scotoRestriction r ->
            singletAdS.radiative.pressureRestriction r ->
              singletAdS.sterile.pressureRestriction r ->
                singletAdS.ads.pressureRestriction r ->
                  r = C.ratio
```

This is now the cleanest statement of the full convergence strategy. The
blocker is not logical plumbing anymore; it is proving the six-way singleton or
constructing the candidate-index ledger that implies it.

## Phase-Coherence Witness Layer

The oscillation mechanism adds a useful eliminator:

```text
mass-basis phase transport
+ flavor-projection interference
+ coherence across methods
+ baseline/energy covariance
```

This is not an energy-to-mass conversion story. Energy is conserved; the stable
object is the coherent phase evolution of fixed mass-eigenstate components and
their projection into weak-flavor channels.

Lean records this as:

```lean
inductive NeutrinoPhaseWitnessComponent

structure AASCPhaseCoherenceWitnessLedger
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (CandidateIndex : Type)
```

The phase ledger can refine the candidate-index ledger through:

```lean
def PhaseRefinedCandidateIndexLedger
```

and then inherits the close/rule-out theorems:

```lean
theorem phaseRefinedLedgerGivesJointSingleton
theorem phaseRefinedLedgerRulesOutSecondPoint
```

Its role is to eliminate non-current candidate indices that break coherent
phase-transport topology across oscillation methods. It is explicitly guarded
against observed phase-value selection, fitted oscillation-parameter import, or
the false assumption that kinetic energy fluctuates into rest mass.

## Neutrino-Specific Discriminator Ledger

The broader set of native neutrino discriminators is now represented by:

```lean
inductive NeutrinoSpecificDiscriminator

structure AASCNeutrinoSpecificDiscriminatorLedger
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (CandidateIndex : Type)
```

The discriminator list is:

- electric neutrality,
- weak-only source/detection boundary,
- mass/flavor basis mismatch,
- macroscopic coherence,
- two-scale splitting structure,
- no absolute-mass import,
- matter-effect compatibility,
- Dirac/Majorana no-selector control,
- sterile/gauge-singlet scope control,
- cross-method `L/E` covariance.

It refines the candidate-index ledger through:

```lean
def NeutrinoDiscriminatorRefinedCandidateIndexLedger
```

and inherits:

```lean
theorem neutrinoDiscriminatorRefinedLedgerGivesJointSingleton
theorem neutrinoDiscriminatorRefinedLedgerRulesOutSecondPoint
```

This is the general structural eliminator layer. It lets the paper argue that
every non-current candidate index violates at least one neutrino-native
constraint, while still forbidding observed-value selection and fitted-parameter
import.

## Draft Elimination Pass

Lean now includes a finite draft taxonomy:

```lean
inductive NeutrinoDraftCandidateIndex
```

with the elimination map:

```lean
def draftCandidateEliminationReason :
  NeutrinoDraftCandidateIndex -> Option HybridExclusionReason
```

Draft pass result:

| Draft candidate class | Status | Elimination reason |
| --- | --- | --- |
| `currentStandingRatio` | survives | none |
| `modularOnlyBranch` | eliminated | `modularAlgebra` |
| `scotoParameterFiberBranch` | eliminated | `scotoMechanism` |
| `spectralWithoutFiniteCollapseBranch` | eliminated | `spectralReduction` |
| `sterileScopeExtensionBranch` | eliminated | `neutrinoSpecificDiscriminator` |
| `phaseTopologyBreakingBranch` | eliminated | `phaseTopology` |
| `matterTransportBreakingBranch` | eliminated | `neutrinoSpecificDiscriminator` |
| `absoluteMassImportBranch` | eliminated | `neutrinoSpecificDiscriminator` |
| `diracMajoranaSelectorBranch` | eliminated | `neutrinoSpecificDiscriminator` |
| `identitySelectorBranch` | eliminated | `closureExhaustion` |

Lean proves:

```lean
theorem draftCandidatePassOnlyCurrentSurvives

theorem draftCandidatePassEliminatesNoncurrent
```

This is an elimination pass over the proposed candidate taxonomy. It is not yet
the full close, because the paper still has to prove that every point in the
actual hybrid joint restriction is classified by this taxonomy. In Lean terms,
the missing bridge is the real `candidateOf : C.Ratio -> CandidateIndex` plus
completeness and injectivity fields in `AASCCandidateIndexLedger`.

That bridge is now formalized as:

```lean
structure AASCDraftTaxonomyCompleteness
```

and Lean converts it into the full candidate-index ledger:

```lean
def draftTaxonomyCompletenessAsCandidateIndexLedger
```

with close/rule-out theorems:

```lean
theorem draftTaxonomyCompletenessGivesJointSingleton
theorem draftTaxonomyCompletenessRulesOutSecondPoint
```

So the proof obligation has narrowed to constructing
`AASCDraftTaxonomyCompleteness`: a classifier from actual joint-admissible
ratios into the draft taxonomy, impossibility of every non-current class on the
joint restriction, and injectivity of the current class.

There is now a non-circular construction route for that classifier:

```lean
structure AASCJointRestrictionCaseSplit

def caseSplitGivesDraftTaxonomyCompleteness
```

The case split asks the paper to prove that every actual hybrid-joint candidate
is either the current ratio or falls into one of the named failure classes:

```text
modular-only
scoto parameter fiber
spectral without finite collapse
sterile scope extension
phase topology breaking
matter transport breaking
absolute mass import
Dirac/Majorana selector
identity selector
```

and then prove each failure class is impossible on the joint restriction. This
is the real constructive path to the all-but-one theorem.

## Targeted Search: Convergence Locus

A targeted internet pass found that the strongest external convergence locus is
not generic sterile-neutrino phenomenology and not AdS by itself. It is the
scoto-seesaw / modular / phase-topology intersection:

| External locus | What it contributes | AASC status |
| --- | --- | --- |
| Dynamical scoto-seesaw with gauged symmetry | Atmospheric scale from seesaw, solar scale from scotogenic dark-sector loop; explicitly targets the solar-to-atmospheric scale ratio. | Strongest mechanism-separation candidate. Still requires parameter-fiber collapse or quotient-skin. |
| `A4` modular scoto-seesaw | Adds modular-form algebraic structure to the scoto-seesaw mass matrix; the loop mass matrix is built from modular Yukawa forms and loop functions. | Best bridge between algebraic rigidity and scoto mechanism. Still model-parameter dependent unless AASC derives or quotients the modulus/couplings. |
| Radiative mild hierarchy model | Shows that one heavy fermionic singlet plus two scalars can produce a naturally mild hierarchy qualitatively close to the observed solar/atmospheric hierarchy. | Supports the scalar-singlet/radiative route as real structural pressure, but not a singleton ratio theorem. |
| Oscillation phase/coherence literature | Confirms that the experimental readout is phase transport of coherent mass-eigenstate wave packets, with decoherence only beyond coherence length. | Justifies `AASCPhaseCoherenceWitnessLedger` as a topology eliminator, not a value selector. |
| Warped / AdS / extra-dimensional sterile-neutrino models | Gauge-singlet/bulk neutrino constructions can generate seesaw-like masses or eV sterile sectors through geometry/warping. | Useful as transport/scope/no-escape pressure. Not by itself same-scope ratio closure. |

Current search verdict:

```text
Most informative locus =
  scoto-seesaw role separation
  + modular/flavor algebraic restriction
  + phase-coherent oscillation readback
  + sterile/gauge-singlet source compatibility
  + AdS/warped transport as scope discipline
```

This points to a paper theorem of the following form:

```lean
sixRestrictionSingleton
```

but the likely constructive proof should route through a smaller named
intersection first:

```text
Tree-seesaw atmospheric carrier
∩ scotogenic solar carrier
∩ modular Yukawa/mass-matrix relation
∩ phase-coherent L/E readback
```

Lean now records this smaller target as:

```lean
structure AASCScotoModularPhaseIntersection
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
```

with close theorem:

```lean
theorem scotoModularPhaseIntersectionGivesRatioCompression
```

The decisive field is:

```lean
intersectionSingleton :
  forall r : C.Ratio,
    C.inMinimalInterval r ->
      modular.ModularRestriction r ->
        scoto.scotoRestriction r ->
          phaseRestriction r ->
            r = C.ratio
```

The missing AASC work is to show that all residual parameters in that
intersection are either source-fixed or quotient-skin, and that every
non-current candidate index breaks at least one of the modular, scoto, spectral,
or phase-topology constraints.

## Hybrid Three-Route Bridge

The three routes can now be combined in Lean:

```lean
structure AASCHybridCompressionNetwork
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
```

The hybrid restriction is the intersection of:

- modular / mass-sum-rule algebraic restriction,
- spectral quotient / finite-collapse restriction,
- scoto-seesaw mechanism-separation restriction.

This is stronger than asking one route to close alone. Each route may leave a
fiber, while the joint intersection may be singleton. The close theorem is:

```lean
theorem hybridCompressionNetworkGivesRatioCompression
```

and the live-deformation theorem is:

```lean
theorem hybridCompressionNetworkKillsLiveDeformations
```

The remaining proof burden is now:

```lean
jointRestrictionSingleton :
  forall r : C.Ratio,
    C.inMinimalInterval r ->
      modular.ModularRestriction r ->
        spectral.spectralRestriction r ->
          scoto.scotoRestriction r ->
            r = C.ratio
```

This is the sharpest current close target. It allows the strongest parts of the
three paths to cooperate:

- scoto-seesaw supplies role/mechanism separation,
- spectral quotient supplies finite/reduction pressure,
- modular/sum-rule supplies algebraic rigidity.

## Closure Exhaustion and Impossibility

The hybrid bridge now has an AASC closure-exhaustion layer:

```lean
structure AASCHybridClosureExhaustion
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
```

It records that every non-hybrid stronger-output route is blocked or
support-only, and that there is no empirical, anchor, comparator, branch, or
identity-selector escape route.

The positive close theorem is:

```lean
theorem exhaustedHybridNetworkClosesRatio
```

The live-deformation theorem is:

```lean
theorem exhaustedHybridNetworkKillsLiveDeformations
```

The impossibility theorem is:

```lean
theorem exhaustedHybridSecondPointContradiction
```

So the final bridge logic is:

1. If AASC exhaustion leaves only the audited hybrid as a live compression
   route, and the hybrid joint restriction is singleton, then the ratio closes.
2. If the hybrid joint restriction still has a second point, the close is
   impossible for that bridge.

The entire problem is now concentrated in the joint-intersection theorem.

## Joint Exclusion Certificate

The joint singleton can now be proved by exclusion rather than as a monolithic
equality theorem:

```lean
structure AASCHybridJointExclusionCertificate
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
```

Any attempted second point in the joint restriction is assigned one of:

```lean
inductive HybridExclusionReason where
  | modularAlgebra
  | spectralReduction
  | scotoMechanism
  | crossRouteCoherence
  | closureExhaustion
```

Lean then proves:

```lean
theorem hybridExclusionCertificateGivesJointSingleton
theorem hybridExclusionCertificateRulesOutSecondPoint
```

This is the most practical proof shape for the paper: classify every surviving
non-current joint point and eliminate it by one of the five AASC exclusion
reasons.

## All-But-One Elimination

There is now an explicit AASC elimination certificate:

```lean
structure AASCAllButOneElimination
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
```

This is the direct answer to "eliminate all but one solution." The paper must
provide:

- a candidate-index ledger,
- the current index,
- completeness of the index over the joint restriction,
- elimination of every non-current index,
- injectivity of the current index on the joint restriction.

Lean then proves:

```lean
theorem allButOneEliminationGivesJointSingleton
theorem allButOneEliminationRulesOutSecondPoint
```

So AASC can eliminate all but one solution exactly when this certificate is
inhabited. The remaining substantive work is to populate the candidate-index
ledger and the non-current index eliminations.

## Candidate Index Ledger

The all-but-one certificate now has a paper-facing construction kit:

```lean
structure AASCCandidateIndexLedger
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
```

It contains the five requested components:

| Required component | Lean field(s) |
| --- | --- |
| candidate-index ledger | `CandidateIndex`, `candidateOf`, `admissibleIndex`, `eliminatedIndex` |
| current survivor index | `currentIndex`, `currentHasCurrentIndex`, `currentIndexAdmissible` |
| completeness over the hybrid joint restriction | `jointCandidateAdmissible`, `jointCandidateCompleteness` |
| elimination of every non-current index | `eliminatedIndicesAreNoncurrent`, `eliminatesNoncurrentIndex`, `eliminationReason` |
| injectivity of the current index | `currentIndexInjectiveOnJointRestriction` |

Lean converts the ledger into the all-but-one certificate via:

```lean
candidateIndexLedgerAsAllButOneElimination
```

and proves:

```lean
candidateIndexLedgerGivesJointSingleton
candidateIndexLedgerRulesOutSecondPoint
```

## No-Eleventh-Route Census Bridge

The "weird eleventh way" concern is now formalized as a census bridge:

```lean
structure AASCNoEleventhNeutrinoRoute

structure AASCNoEleventhRouteCaseSplitConstruction
```

The first structure says every joint-admissible candidate has a visible route
carrier. The second supplies the mathematical eliminator: each carrier's draft
class is either the current standing-ratio class or an impossible non-current
class.

Lean then proves:

```lean
theorem noEleventhRouteGivesJointSingleton
theorem noEleventhRouteRulesOutSecondPoint
```

This is the AASC form of the eleventh-route test. An extra solution route must
show up in experimental or legacy-theory structure as a carrier, reduce to one
of the existing carrier classes, or fail same-target admissibility.

## Impossibility Suite Bridge

The local Overleaf source for `The_Impossibility_Suite_MaxHard` gives three
kernel impossibilities and their governance consequences:

- no generators,
- no carriers,
- no repairs,
- no illicit domain transfer,
- fail-closed typing,
- no partial closure.

The fixed-domain exhaustion source sharpens this with:

- no admissibility-relevant parameterization,
- fixed-domain/same-scope exhaustion,
- no hidden third locus,
- same-scope operator exhaustion,
- AMetric boundary non-parameterization.

Lean now records these as:

```lean
inductive AASCImpossibilityKernel

structure AASCImpossibilitySuiteAudit
```

The audit now also requires:

```lean
kernelAgreesWithDefaultMap
```

so the paper-facing branch eliminations are pinned to the intended kernel map
rather than left as arbitrary labels.

and proves:

```lean
theorem impossibilitySuiteAuditGivesJointSingleton
theorem impossibilitySuiteAuditRulesOutSecondPoint
```

This is the strongest current close form. Once the paper assigns every
non-current draft class to an impossibility kernel and proves that kernel
eliminates the class on the hybrid joint restriction, the no-eleventh-route
singleton follows.

## Operator-Strengthening Package

The operator-theory papers sharpen the same-scope exhaustion side:

- same-scope operator closure reduces every family to fixed governing data;
- apparent fixed-base strengthening is either conservative on old-base-relevant
  content or depends on external data;
- carrier-changing extensions are scope changes rather than same-base power;
- endpoint/self-adjoint-extension selection is admissible only when invariantly
  fixed by the base/order, otherwise it is selector import.

Lean records this as:

```lean
inductive AASCOperatorStrengtheningStatus

structure AASCFixedBaseOperatorAudit

def fixedBaseOperatorAuditEliminatesStatus
```

This is aimed especially at the `matterTransportBreakingBranch` and
`diracMajoranaSelectorBranch`: transport-style strengthening must be
fixed-base conservative or external, and endpoint-style selection must be
invariantly fixed rather than chosen as a branch selector.

## Branch Audit Constructor

Lean now exposes the final audit in the branch-by-branch form needed for the
paper:

```lean
structure AASCBranchImpossibilityAudit

def branchImpossibilityAuditAsImpossibilitySuiteAudit

theorem branchImpossibilityAuditGivesJointSingleton

theorem branchImpossibilityAuditRulesOutSecondPoint
```

This constructor assembles the full `AASCImpossibilitySuiteAudit` from one
current-class injectivity proof plus nine branch-impossibility proofs. It is
the closest non-circular close target currently in the Lean file.

## NNR4G / NNR4H Source Ledger

The NNR4G and NNR4H project sources were extracted from:

```text
NNR4G_Project_v3_LawFormTests.zip
NNR4H_Project.zip
```

Lean now records their magnitude-compression rows as:

```lean
structure AASCNNR4GHMagnitudeCompressionLedger

structure AASCNNR4GHBranchTranslation

theorem nnr4ghBranchTranslationGivesJointSingleton

theorem nnr4ghBranchTranslationRulesOutSecondPoint
```

The source-row mapping is:

| NNR row | Branch use |
| --- | --- |
| NNR4G THM 6.1, no illicit stronger-output route | absolute-mass import, sterile/scope import, Dirac/Majorana selector, empirical/comparator/free-parameter pseudo-routes |
| NNR4G THM 7.1 / NNR4H THM 6.2, no carrier-derived polynomial | modular/algebraic-only branch |
| NNR4G LEM 8.1 / NNR4H THM 6.1, no motif-to-target promotion | modular motif, phase motif, finite-orbit/matter-transport motif |
| NNR4G THM 8.2 / NNR4H THM 7.2, finite orbit not same-target transported | finite residual / matter-transport branch |
| NNR4G THM 9.1 / NNR4H THM 8.2, no finite-collapse or overlap certificate | spectral-without-finite-collapse branch |
| NNR4G THM 10.1 / NNR4H THM 9.2, no source-certified hierarchy package | scoto/hierarchy parameter-fiber branch |
| NNR4H THM 10.2, no quotient-normal-form evaluator | identity/normal-form selector branch |
| NNR4G THM 12.1 / NNR4H THM 12.1, named certificate-failure exhaustion | global closure of normalized stronger-output routes |

Important caveat: NNR4G/H by themselves prove the current strongest endpoint is
the minimal interval, not a singleton. The new Lean translation therefore asks
for an additional same-target bridge from each no-eleventh-route draft branch
to the relevant NNR certificate-failure row. That bridge is exactly
`AASCNNR4GHBranchTranslation`.

## CNF / ATS Pull

I pulled the next targeted source packages:

```text
CNF2_Finite_Sector_Collapse_PublicationReady_Project.zip
CNF6_Mass_Matrix_Spectral_Forcing_SpectralHardened_Project.zip
CNF7_Mixing_Phase_Forcing_MismatchHardened_Project.zip
Anchor_Tensor_Skin_v16_submission_ready_audited.zip
```

Lean now records them as support ledgers:

```lean
structure AASCCNF2FiniteCollapseLedger
structure AASCCNF6SpectralForcingLedger
structure AASCCNF7PhaseMixingLedger
structure AASCATSRoleDecompositionLedger
structure AASCCorpusBranchSupportLedger
```

What they contribute:

| Source | Useful for |
| --- | --- |
| CNF2 | finite-collapse requires a real certificate; enumerable/bounded is not finite; finite survival is not exact selection |
| CNF6 | spectral quotient and mass-ratio classes require standing numerator/denominator, quotient stability, no observed spectrum ancestry, and finite/overlap/solver reduction |
| CNF7 | phase/mixing constraints require independent mass and boundary carriers, common interface, rephasing quotient, and no calibration reversal |
| ATS | distinguishes load-bearing tensor content from quotient-skin; blocks auxiliary selectors, frozen skin, unfixed roles, and fourth-role escapes |
| Unus Solus | supplies unique admissible interior: same fixed boundary and standing classification allow no second same-domain admissible interior |

These sources strengthen individual translation fields, especially
`spectralWithoutFiniteCollapse`, `phaseTopologyBreaking`,
`matterTransportBreaking`, `scotoParameterFiber`, and `identitySelector`. They
still do not by themselves assert the neutrino-ratio singleton.

## Constructive Bridge Attempt

The "make it ourselves" route is now formalized as:

```lean
structure AASCSharedConvergencePointIdentification

structure AASCScotoModularPhaseParameterCollapse

theorem sharedConvergencePointIdentificationGivesJointSingleton

theorem sharedConvergencePointIdentificationRulesOutSecondPoint

def scotoModularPhaseCollapseAsNNR4GHBranchTranslation

theorem scotoModularPhaseCollapseGivesJointSingleton

theorem scotoModularPhaseCollapseRulesOutSecondPoint
```

This is the candidate theorem combining:

- modular/flavor algebraic restriction,
- scoto-seesaw role separation,
- CNF6 spectral quotient discipline,
- CNF7 phase/rephasing quotient discipline,
- ATS tensor-vs-skin filtering,
- NNR4G/H no-import/no-selector firewall.

The hard fields are exactly the ones expected from the search:

- `modularParametersSourceFixedOrSkin`,
- `scotoSeesawParametersSourceFixedOrSkin`,
- `spectralQuotientFiniteOrReduced`,
- `phaseReadbackQuotientStable`,
- `noObservedSplittingValueImport`,
- `noAlignmentOrPhaseBranchSelector`,
- `noExternalEndpointOrAbsoluteMassSelector`.

Once those and the nine branch reductions are proved, Lean closes the singleton.

The plain-language theorem is now:

```text
shared convergence identifies the point
```

It states that the modular, scoto/seesaw, spectral, phase/rephasing, and
role-occupancy restrictions do not merely coexist inside the minimal interval;
their shared realization fixes the current ratio point, while every non-current
branch reduces to an NNR4G/H named failure.

The `Unus Solus` source adds a positive-realization support object:

```lean
structure AASCUniqueAdmissibleInteriorLedger

structure AASCUniqueInteriorRatioRealization
```

This helps with the missing positive field:

```lean
currentDraftClassInjective
```

but only after the paper proves that the standing-ratio current class is an
instance of the fixed unique admissible interior, not merely a survivor of
negative filtering.

## Residual-Parameter Corpus Pull

The residual-parameter search found a directly relevant cluster:

| Source cluster | Contribution |
| --- | --- |
| `Generation Count and Residual Parameters...` | fixed residual scope, same-scope competitor discipline, maximality-remainder test, repair-prohibition check |
| `From Quotient-Singleton to Raw Exactness` | quotient singleton does not automatically yield raw exactness; quotient fiber must be exhausted modulo skin |
| `Exactness Criteria after Constructive Numerical Forcing` | exactness-relevant observables, rephasing/equivalence exhaustion |
| `Yukawa Compatibility and Parameter-Survival Classification...` | distinguishes surviving tensor content from fitted notation, chart artifacts, and inadmissible selectors |
| `Mass-Matrix, Eigenstructure, and Ratio Rigidity...` | mechanism equivalence by mass-response quotient, reduced carrier, standing texture, invariant spectral data |
| `Gauge-Coupling Parameters and Forced Uniqueness...` | standing-bearing quantities must be invariant under admissible redescription or change tensor compatibility |

Lean now represents this support as:

```lean
structure AASCResidualParameterExhaustionLedger
structure AASCQuotientRawExactnessLedger
structure AASCParameterSurvivalClassificationLedger
structure AASCResidualFreedomClosureAudit
structure AASCResidualCorpusPointClosure
structure AASCNeutrinoBridgeTranslation
structure AASCAdmittedNeutrinoSector
structure AASCNeutrinoBridgeAdmissionProof

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

This is the clean version of the new route: if the residual audit proves that
all apparent ratio-changing freedom is fixed, quotient-skin, witness-forced, or
inadmissible, and if the shared locus identifies the current point, Lean closes
the hybrid joint restriction to a singleton.

The sharper constructor is the corpus-faithful version:

```text
Global Coherence Intersection = shared convergence locus
shared convergence locus identifies current point
non-current residual branches are exhausted
```

The central bridge theorem interface is now:

```lean
AASCNeutrinoBridgeTranslation
```

It packages the scope claim, the GCI/shared-locus claim, quotient-exactness and
parameter-normal-form applicability, current-point identification, and
non-current branch exhaustion. Lean proves that this bridge gives the residual
corpus point closure, branch audit, singleton, and no-second-point theorem.

The bridge is now intertranslatable with the other main interfaces. Inhabiting
the bridge, residual point closure, or branch audit lets Lean construct the
other two and then close the singleton.

The existence claim is now separated from the closure claim:

```text
HybridJointRestrictionNonempty
```

is supplied by the current ratio, but this alone is not singleton closure. The
closed chain is:

```text
AASCAdmittedNeutrinoSector
-> AASCNeutrinoBridgeTranslation
-> AASCBranchImpossibilityAudit
-> HybridJointRestrictionSingleton
```

This is the formal version of the safe "neutrinos exist, and the sector is
AASC-admitted in the required same-scope bridge, therefore singleton" argument.

The remaining paper theorem is now isolated as:

```lean
AASCNeutrinoBridgeAdmissionProof
```

It is intentionally closer to prose than the earlier wrapper objects: it asks
for same-scope admission, GCI identification, current-class point
identification, and non-current branch exhaustion. The detailed branch plan is
in `NeutrinoBridgeAdmission_Workplan.md`.

The residual papers supply the fixed residual scope, same-scope competitor
discipline, repair-prohibition, enlarged-domain separation, and ATS role test.
EX1/EX2 supply quotient-fiber exactness discipline. The parameter papers supply
canonical parameter normal form and the rule that redescription/bookkeeping
parameters are quotiented away.

Important status distinction:

- The non-circular route is the case-split route:
  `AASCNoEleventhRouteCaseSplitConstruction` gives
  `AASCResidualCorpusPointClosure`, which gives the singleton.
- The practical proof route is the branch audit:
  `AASCBranchImpossibilityAudit` gives the no-eleventh case split, then the
  residual corpus point closure, then the singleton.
- The reverse proof route is now available:
  residual point-closure, shared convergence, or scoto-modular phase collapse
  each constructs `AASCBranchImpossibilityAudit` and the singleton together.
- The already-closed route is only a consistency check:
  `AASCHybridCompressionNetwork.jointRestrictionSingleton` also gives
  `AASCResidualCorpusPointClosure`, but that assumes the singleton field inside
  the hybrid network.

## Method-Invariant Witness Ledger

Experimental diversity now has an AASC-safe formal role:

```lean
inductive NeutrinoMethodChannel where
  | solar
  | atmospheric
  | reactor
  | accelerator
  | pmnsInvariant
  | cosmologyBoundary
  | betaBoundary
  | doubleBetaBoundary

structure AASCMethodInvariantWitnessLedger
```

The method ledger records which candidate indices survive or are eliminated by
method-invariant witness topology. It explicitly includes the no-laundering
guards:

- `noChannelUsesObservedValueAsSelector`,
- `noBoundaryChannelPromotedToValue`.

It refines the candidate-index ledger through:

```lean
def MethodRefinedCandidateIndexLedger
```

and Lean proves:

```lean
theorem methodRefinedLedgerGivesJointSingleton
theorem methodRefinedLedgerRulesOutSecondPoint
```

This is the lawful way to let real experiments constrain the ledger: not by
importing observed ratio values, but by using independent methods to eliminate
candidate-index topology.

## Sources Consulted

- `arXiv:1704.02371`, "Neutrino Mass Sum Rules and Symmetries of the Mass Matrix".
- `arXiv:2308.08981`, "Neutrino Mass Sum Rules from Modular A4 Symmetry".
- `arXiv:1512.07531`, "Littlest Seesaw".
- `arXiv:1807.11447`, "Simplest Scoto-Seesaw Mechanism".
- `arXiv:2307.04840`, "Dynamical scoto-seesaw mechanism with gauged B-L".
- `arXiv:2311.09282`, "Neutrino Mass and Mixing with Modular Symmetry".
- PDG neutrino mixing review, used for the general boundary that oscillation
  data expose mass-squared differences rather than first-principles absolute
  mass values.
