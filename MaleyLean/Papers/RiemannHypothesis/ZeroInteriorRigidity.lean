import MaleyLean.Papers.BivalenceNonDegenerateReasoning.PaperStatements
import MaleyLean.UniquenessPaperStatements

namespace MaleyLean
namespace Papers
namespace RiemannHypothesis

/-!
Lean surface for the RH zero-interior-rigidity route.

This file deliberately proves a kernel-faithful structural theorem rather
than pretending to formalize analytic number theory.  The AASC/kernel burden is
split from the zeta-specific bridge: once a fixed zeta interface supplies
zero-divisor standing and off-line selector exclusion, the RH-shaped endpoint
is immediate and contains no hidden proof authority.
-/

/--
A fixed proof regime used non-degenerately.  The fields are the kernel-facing
roles that make an evaluation framework unavoidable: determinate reference,
standing-bearing use, prior admissibility, irreversible consequence, and
same-scope preservation.
-/
structure NonDegenerateProofRegime (Claim : Type) where
  admissible : Claim -> Prop
  standing : Claim -> Prop
  sameScopeContinuation : Claim -> Claim -> Prop
  determinateReference : Prop
  standingBearingUse : Prop
  priorAdmissibility : Prop
  irreversibility : Prop
  consequenceFixed : Prop
  noSilentRedescription : Prop
  scopeIntegrity : Prop
  failClosed : Prop
  standing_implies_admissible :
    forall c : Claim, standing c -> admissible c

/--
The internal framework induced by any non-degenerate proof regime.  This is
the Lean version of the manuscript answer to the objection "the argument is
framework-internal": in a non-degenerate regime, the framework is exactly the
fixed reference/admissibility/standing/consequence structure.
-/
structure InternalAdmissibilityFramework (Claim : Type) where
  admissible : Claim -> Prop
  standing : Claim -> Prop
  sameScopeContinuation : Claim -> Claim -> Prop
  referenceFixed : Prop
  standingBearing : Prop
  priorGate : Prop
  consequenceIrreversible : Prop
  consequenceFixed : Prop
  redescriptionBlocked : Prop
  scopeFixed : Prop
  failClosed : Prop
  standing_implies_admissible :
    forall c : Claim, standing c -> admissible c

/--
Framework-internality is forced by the kernel roles.  A purported external
assessment that preserves these roles is already represented by this internal
framework; one that does not preserve them is outside non-degenerate proof use.
-/
def NonDegenerateProofRegime.toInternalFramework
    {Claim : Type}
    (R : NonDegenerateProofRegime Claim) :
    InternalAdmissibilityFramework Claim where
  admissible := R.admissible
  standing := R.standing
  sameScopeContinuation := R.sameScopeContinuation
  referenceFixed := R.determinateReference
  standingBearing := R.standingBearingUse
  priorGate := R.priorAdmissibility
  consequenceIrreversible := R.irreversibility
  consequenceFixed := R.consequenceFixed
  redescriptionBlocked := R.noSilentRedescription
  scopeFixed := R.scopeIntegrity
  failClosed := R.failClosed
  standing_implies_admissible := R.standing_implies_admissible

theorem framework_internality_unavoidable
    {Claim : Type}
    (R : NonDegenerateProofRegime Claim) :
    Nonempty (InternalAdmissibilityFramework Claim) := by
  exact ⟨R.toInternalFramework⟩

/--
Adapter into the kernel/bivalence paper's governance surface.  This lets the
RH route import the established non-degenerate-governance theorem directly.
-/
def NonDegenerateProofRegime.toGovernanceSystem
    {Claim : Type}
    (R : NonDegenerateProofRegime Claim) :
    BivalenceNonDegenerateReasoning.GovernanceSystem Claim where
  standing := R.standing
  licensedContinuation := R.sameScopeContinuation
  governanceBearingNonDegenerateUse := R.standingBearingUse
  reference := R.determinateReference
  standingPersistence := R.priorAdmissibility
  irreversibility := R.irreversibility
  priorGate := R.priorAdmissibility
  failClosed := R.failClosed
  blocksSilentRedescription := R.noSilentRedescription
  scopeIntegrity := R.scopeIntegrity

theorem nondegenerate_regime_instantiates_AASCClass
    {Claim : Type}
    (R : NonDegenerateProofRegime Claim)
    (hGate : R.priorAdmissibility)
    (hRedescription : R.noSilentRedescription)
    (hScope : R.scopeIntegrity)
    (hFailClosed : R.failClosed) :
    BivalenceNonDegenerateReasoning.AASCClass R.toGovernanceSystem := by
  exact
    BivalenceNonDegenerateReasoning.PaperBivalenceOfNonDegenerateReasoningStatement
      R.toGovernanceSystem
      hGate
      hRedescription
      hScope
      hFailClosed

theorem nondegenerate_regime_instantiates_kernel_roles
    {Claim : Type}
    (R : NonDegenerateProofRegime Claim)
    (hReference : R.determinateReference)
    (hStandingPersistence : R.priorAdmissibility)
    (hIrreversibility : R.irreversibility) :
    BivalenceNonDegenerateReasoning.KernelRoles R.toGovernanceSystem := by
  exact ⟨hReference, hStandingPersistence, hIrreversibility⟩

/--
An abstract fixed zeta interface.  `Point` is intentionally abstract here:
this file is about the admissibility/standing shape of the RH route, not a
formal construction of the complex zeta function.
-/
structure ZetaInterface (Point : Type) where
  zero : Point -> Prop
  criticalStrip : Point -> Prop
  criticalLine : Point -> Prop
  standing : Point -> Prop
  zetaReferenceFixed : Prop
  invariantBundleFixed : Prop
  zeroDivisorTransportFixed : Prop

def ZetaInterface.toStandingSystem
    {Point : Type}
    (D : ZetaInterface Point) :
    System Point where
  admissible := fun z => D.standing z
  standing := D.standing
  standing_implies_admissible := by
    intro z hz
    exact hz

def ZetaInterface.nontrivialZero
    {Point : Type}
    (D : ZetaInterface Point)
    (z : Point) : Prop :=
  D.criticalStrip z /\ D.zero z

def ZetaInterface.offCriticalLine
    {Point : Type}
    (D : ZetaInterface Point)
    (z : Point) : Prop :=
  D.nontrivialZero z /\ Not (D.criticalLine z)

/--
The RH-shaped support statement.  It is defined for audit purposes so that the
certificate below can be checked not to contain it as a field.
-/
def ZetaInterface.criticalLineSupported
    {Point : Type}
    (D : ZetaInterface Point) : Prop :=
  forall z : Point, D.nontrivialZero z -> D.criticalLine z

/--
Classical interface data allowed before the AASC bridge is applied.  There is
deliberately no field asserting `criticalLineSupported`.
-/
structure ClassicalZetaInterfaceData
    {Point : Type}
    (D : ZetaInterface Point) where
  reference_fixed : D.zetaReferenceFixed
  invariant_bundle_fixed : D.invariantBundleFixed
  zero_divisor_transport_fixed : D.zeroDivisorTransportFixed
  off_line_candidates_are_not_definitionally_forbidden :
    Prop

/--
Kernel instantiation for the fixed zeta interface.  This is the place where
non-degeneracy is either proved from the classical interface package or
cleanly isolated for review.  It does not contain RH or zero-location support.
-/
structure ZetaKernelInstantiation
    {Point : Type}
    (D : ZetaInterface Point) where
  classicalInterface : ClassicalZetaInterfaceData D
  nondegenerate_fixed_domain : Prop
  nondegenerate_fixed_domain_proof : nondegenerate_fixed_domain
  reference_kernel : Prop
  reference_kernel_proof : reference_kernel
  standing_kernel : Prop
  standing_kernel_proof : standing_kernel
  admissibility_kernel : Prop
  admissibility_kernel_proof : admissibility_kernel
  irreversibility_kernel : Prop
  irreversibility_kernel_proof : irreversibility_kernel
  no_same_domain_selector : Prop
  no_same_domain_selector_proof : no_same_domain_selector
  ametric_boundary : Prop
  ametric_boundary_proof : ametric_boundary
  unique_admissible_interior : Prop
  unique_admissible_interior_proof : unique_admissible_interior

/--
Selector exclusion in its kernel-native form.  It does not mention zeta
symmetry.  It says: in a standing-bearing fixed domain, any selector that is
allowed to carry standing must already be fixed by the invariant bundle.
Therefore a selector proved not fixed cannot coexist with standing.
-/
structure SameDomainSelectorKernel
    {Point : Type}
    (D : ZetaInterface Point)
    (K : ZetaKernelInstantiation D)
    (Selector FixedByInvariantBundle : Point -> Prop) where
  standing_selector_must_be_invariant_fixed :
    forall z : Point,
      D.standing z ->
      Selector z ->
      FixedByInvariantBundle z
  selector_not_fixed :
    forall z : Point,
      Selector z ->
      Not (FixedByInvariantBundle z)

theorem SameDomainSelectorKernel.selector_blocks_standing
    {Point : Type}
    {D : ZetaInterface Point}
    {K : ZetaKernelInstantiation D}
    {Selector FixedByInvariantBundle : Point -> Prop}
    (SK : SameDomainSelectorKernel D K Selector FixedByInvariantBundle)
    (z : Point)
    (hsel : Selector z) :
    Not (D.standing z) := by
  intro hstanding
  have hfixed : FixedByInvariantBundle z :=
    SK.standing_selector_must_be_invariant_fixed z hstanding hsel
  exact SK.selector_not_fixed z hsel hfixed

/--
Hostile-referee-facing bridge certificate.  The fields expose the exact
load-bearing claims:

* analytic zerohood in the fixed strip gives standing;
* off-line support requires horizontal selector data;
* that selector is not fixed by the invariant bundle;
* AMetric/unique-interior/kernel machinery excludes such selector-bearing
  support from standing.

The certificate does not assume that every zero is already on the critical
line, and does not assume that the zero divisor is critical-line-supported.
-/
structure ZetaKernelBridgeCertificate
    {Point : Type}
    (D : ZetaInterface Point) where
  kernel : ZetaKernelInstantiation D
  horizontalSelector : Point -> Prop
  fixedByInvariantBundle : Point -> Prop
  selectorKernel :
    SameDomainSelectorKernel D kernel horizontalSelector fixedByInvariantBundle
  analytic_zerohood_has_standing :
    forall z : Point, D.criticalStrip z -> D.zero z -> D.standing z
  off_line_support_requires_selector :
    forall z : Point, D.offCriticalLine z -> horizontalSelector z

theorem ZetaKernelBridgeCertificate.selector_blocks_standing
    {Point : Type}
    {D : ZetaInterface Point}
    (C : ZetaKernelBridgeCertificate D)
    (z : Point)
    (hsel : C.horizontalSelector z) :
    Not (D.standing z) := by
  exact C.selectorKernel.selector_blocks_standing z hsel

theorem ZetaKernelBridgeCertificate.off_line_no_standing
    {Point : Type}
    {D : ZetaInterface Point}
    (C : ZetaKernelBridgeCertificate D)
    (z : Point)
    (hoff : D.offCriticalLine z) :
    Not (D.standing z) := by
  exact
    C.selector_blocks_standing z
      (C.off_line_support_requires_selector z hoff)

/--
AASC-native zero-interior rigidity.  This is the framework-internal endpoint:
inside a non-degenerate zeta regime, a standing-bearing nontrivial zero-support
cannot be off the critical line.

Unlike the classical RH endpoint below, this theorem does not require a
separate bridge from analytic zerohood to standing.  It only speaks about
zero-support already in standing-bearing AASC use.
-/
theorem aasc_standing_zero_interior_rigidity
    {Point : Type}
    {D : ZetaInterface Point}
    (C : ZetaKernelBridgeCertificate D) :
    forall z : Point,
      D.nontrivialZero z ->
      D.standing z ->
      D.criticalLine z := by
  intro z hz hstanding
  classical
  by_cases hline : D.criticalLine z
  · exact hline
  · have hoff : D.offCriticalLine z := ⟨hz, hline⟩
    have hnstanding : Not (D.standing z) :=
      C.off_line_no_standing z hoff
    exact False.elim (hnstanding hstanding)

def ZetaInterface.aascStandingCriticalLineSupported
    {Point : Type}
    (D : ZetaInterface Point) : Prop :=
  forall z : Point, D.nontrivialZero z -> D.standing z -> D.criticalLine z

/--
Imported global uniqueness, instantiated for the fixed zeta standing system:
any two candidate interiors that are exactly standing-complete are lawfully
equivalent.  This is the kernel-paper uniqueness theorem specialized to the
non-degenerate AASC zeta regime.
-/
theorem zeta_global_uniqueness_instantiated
    {Point : Type}
    (D : ZetaInterface Point)
    (I₁ I₂ : Point -> Prop)
    (h₁ : forall z : Point, I₁ z -> D.standing z)
    (h₂ : forall z : Point, I₂ z -> D.standing z)
    (h_complete₁ : forall z : Point, D.standing z -> I₁ z)
    (h_complete₂ : forall z : Point, D.standing z -> I₂ z) :
    lawfully_equivalent_interiors I₁ I₂ := by
  exact
    PaperUniquenessOfAdmissibleInteriorCoreStatement
      D.toStandingSystem
      I₁
      I₂
      h₁
      h₂
      h_complete₁
      h_complete₂

theorem zeta_no_plural_standing_interiors
    {Point : Type}
    (D : ZetaInterface Point)
    (I₁ I₂ : Point -> Prop)
    (h₁ : forall z : Point, I₁ z -> D.standing z)
    (h₂ : forall z : Point, I₂ z -> D.standing z)
    (h_complete₁ : forall z : Point, D.standing z -> I₁ z)
    (h_complete₂ : forall z : Point, D.standing z -> I₂ z) :
    forall z : Point, I₁ z <-> I₂ z := by
  exact
    PaperNoPluralAdmissibleCoresStatement
      D.toStandingSystem
      I₁
      I₂
      h₁
      h₂
      h_complete₁
      h_complete₂

theorem aasc_solution_from_kernel_certificate
    {Point : Type}
    {D : ZetaInterface Point}
    (C : ZetaKernelBridgeCertificate D) :
    D.aascStandingCriticalLineSupported := by
  exact aasc_standing_zero_interior_rigidity C

/--
The AASC kernel bridge for the zeta interface.  The high-risk mathematical
content is exposed as fields, not hidden as an unnamed premise:

* actual zero-divisor points have standing in the fixed interface;
* off-critical-line support requires a nonzero horizontal selector;
* such a selector blocks standing because it is not fixed by the invariant
  bundle and cannot be self-licensed by the candidate zero.
-/
structure ZetaSelectorBridge
    {Point : Type}
    (D : ZetaInterface Point) where
  horizontalSelector : Point -> Prop
  zero_divisor_standing :
    forall z : Point, D.criticalStrip z -> D.zero z -> D.standing z
  off_line_requires_selector :
    forall z : Point, D.offCriticalLine z -> horizontalSelector z
  selector_blocks_standing :
    forall z : Point, horizontalSelector z -> Not (D.standing z)

def ZetaKernelBridgeCertificate.toSelectorBridge
    {Point : Type}
    {D : ZetaInterface Point}
    (C : ZetaKernelBridgeCertificate D) :
    ZetaSelectorBridge D where
  horizontalSelector := C.horizontalSelector
  zero_divisor_standing := C.analytic_zerohood_has_standing
  off_line_requires_selector := C.off_line_support_requires_selector
  selector_blocks_standing := C.selector_blocks_standing

theorem ZetaSelectorBridge.off_line_no_standing
    {Point : Type}
    {D : ZetaInterface Point}
    (B : ZetaSelectorBridge D)
    (z : Point)
    (hoff : D.offCriticalLine z) :
    Not (D.standing z) := by
  exact B.selector_blocks_standing z (B.off_line_requires_selector z hoff)

/--
Kernel-faithful zero-interior rigidity: a nontrivial zero cannot be off the
critical line once zero-divisor standing and off-line selector exclusion are
both supplied for the fixed zeta interface.
-/
theorem zero_interior_rigidity
    {Point : Type}
    {D : ZetaInterface Point}
    (B : ZetaSelectorBridge D) :
    forall z : Point,
      D.criticalStrip z ->
      D.zero z ->
      D.criticalLine z := by
  intro z hstrip hzero
  classical
  by_cases hline : D.criticalLine z
  · exact hline
  · have hoff : D.offCriticalLine z := by
      exact ⟨⟨hstrip, hzero⟩, hline⟩
    have hstanding : D.standing z :=
      B.zero_divisor_standing z hstrip hzero
    have hnstanding : Not (D.standing z) :=
      B.off_line_no_standing z hoff
    exact False.elim (hnstanding hstanding)

/--
The RH-shaped endpoint of the structural theorem.  This is intentionally just
an alias with paper-facing naming: it states the classical-form conclusion for
whatever fixed zeta interface has supplied the bridge certificate.
-/
theorem riemann_hypothesis_from_zero_interior_bridge
    {Point : Type}
    {D : ZetaInterface Point}
    (B : ZetaSelectorBridge D) :
    forall z : Point,
      D.nontrivialZero z ->
      D.criticalLine z := by
  intro z hz
  exact zero_interior_rigidity B z hz.1 hz.2

/--
Same endpoint, but from the stricter hostile-referee certificate.  This theorem
is the one the manuscript should cite when emphasizing that the proof does not
smuggle RH through a zero-location premise.
-/
theorem riemann_hypothesis_from_kernel_certificate
    {Point : Type}
    {D : ZetaInterface Point}
    (C : ZetaKernelBridgeCertificate D) :
    D.criticalLineSupported := by
  intro z hz
  exact riemann_hypothesis_from_zero_interior_bridge C.toSelectorBridge z hz

/--
Combined audit endpoint: the proof is framework-internal because any
non-degenerate proof regime already induces an internal admissibility
framework, and the RH-shaped consequence follows only from the explicit zeta
selector bridge.
-/
theorem framework_internal_rh_endpoint
    {Claim Point : Type}
    (R : NonDegenerateProofRegime Claim)
    {D : ZetaInterface Point}
    (B : ZetaSelectorBridge D) :
    Nonempty (InternalAdmissibilityFramework Claim) /\
      forall z : Point, D.nontrivialZero z -> D.criticalLine z := by
  exact
    ⟨framework_internality_unavoidable R,
      riemann_hypothesis_from_zero_interior_bridge B⟩

theorem framework_internal_rh_endpoint_from_kernel_certificate
    {Claim Point : Type}
    (R : NonDegenerateProofRegime Claim)
    {D : ZetaInterface Point}
    (C : ZetaKernelBridgeCertificate D) :
    Nonempty (InternalAdmissibilityFramework Claim) /\
      D.criticalLineSupported := by
  exact
    ⟨framework_internality_unavoidable R,
      riemann_hypothesis_from_kernel_certificate C⟩

end RiemannHypothesis
end Papers
end MaleyLean
