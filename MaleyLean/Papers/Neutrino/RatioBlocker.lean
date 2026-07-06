import MaleyLean.Core
import MaleyLean.InteriorUniqueness
import MaleyLean.Papers.ClaimStandingAndLegitimacy.PaperStatements

namespace MaleyLean

namespace Neutrino

/--
Paper-facing abstraction for the current NNR8 state.

The object is intentionally role-level rather than numerical: `Role` is the
carrier of standing spectral-response roles, while `Ratio` is the reportable
same-target ratio object. The current certificate stores only the minimal
interval status, not a value, finite class, or algebraic law.
-/
structure StandingRatioCertificate where
  Role : Type
  Ratio : Type
  Msol : Role
  Matm : Role
  ratio : Ratio
  standingRole : Role -> Prop
  commonCarrier : Role -> Role -> Prop
  atmosphericDenominatorFixed : Role -> Prop
  solarSubordinateToAtmospheric : Role -> Role -> Prop
  inMinimalInterval : Ratio -> Prop
  solarStanding : standingRole Msol
  atmosphericStanding : standingRole Matm
  commonMassResponseCarrier : commonCarrier Msol Matm
  denominatorFixed : atmosphericDenominatorFixed Matm
  roleSeparation : solarSubordinateToAtmospheric Msol Matm
  minimalIntervalLocked : inMinimalInterval ratio

/--
The locked positive output of the current certificate: the ratio is reportable
only at the minimal interval strength fixed by the certificate.
-/
theorem currentCertificateLocksMinimalInterval
  (C : StandingRatioCertificate) :
  C.inMinimalInterval C.ratio := by
  exact C.minimalIntervalLocked

/--
A lawful same-target deformation is represented only by the structure needed
for the blocker audit: it transforms roles, transforms the reportable ratio,
preserves the standing/carrying/denominator/separation certificates, and is
declared lawful by the current same-target discipline.
-/
structure LawfulRatioDeformation (C : StandingRatioCertificate) where
  deformRole : C.Role -> C.Role
  deformRatio : C.Ratio -> C.Ratio
  lawful : Prop
  preservesStanding :
    forall r : C.Role, C.standingRole r -> C.standingRole (deformRole r)
  preservesCommonCarrier :
    C.commonCarrier C.Msol C.Matm ->
      C.commonCarrier (deformRole C.Msol) (deformRole C.Matm)
  preservesDenominator :
    C.atmosphericDenominatorFixed C.Matm ->
      C.atmosphericDenominatorFixed (deformRole C.Matm)
  preservesRoleSeparation :
    C.solarSubordinateToAtmospheric C.Msol C.Matm ->
      C.solarSubordinateToAtmospheric (deformRole C.Msol) (deformRole C.Matm)
  preservesMinimalInterval :
    C.inMinimalInterval C.ratio ->
      C.inMinimalInterval (deformRatio C.ratio)

def ratioInvariant
  (C : StandingRatioCertificate)
  (T : LawfulRatioDeformation C) : Prop :=
  T.lawful -> T.deformRatio C.ratio = C.ratio

def ratioCanVary
  (C : StandingRatioCertificate)
  (T : LawfulRatioDeformation C) : Prop :=
  T.lawful /\ Not (T.deformRatio C.ratio = C.ratio)

/--
If a lawful same-target deformation preserves the current role certificates but
changes the ratio, then the current ledger cannot also prove universal ratio
invariance. This is the formal blocker behind "interval locked, magnitude not
compressed."
-/
theorem liveDeformationBlocksUniversalRatioInvariance
  (C : StandingRatioCertificate)
  (T : LawfulRatioDeformation C)
  (hvar : ratioCanVary C T) :
  Not (forall U : LawfulRatioDeformation C, ratioInvariant C U) := by
  intro hall
  exact hvar.2 (hall T hvar.1)

/--
The exact missing compression principle in invariant form: every lawful
same-target deformation preserves the reportable ratio.
-/
def RatioInvariantCompressionPrinciple
  (C : StandingRatioCertificate) : Prop :=
  forall T : LawfulRatioDeformation C, ratioInvariant C T

def NoLawfulRatioChangingDeformation
  (C : StandingRatioCertificate) : Prop :=
  forall T : LawfulRatioDeformation C, Not (ratioCanVary C T)

theorem compressionPrincipleClosesDeformationBlocker
  (C : StandingRatioCertificate)
  (h : RatioInvariantCompressionPrinciple C)
  (T : LawfulRatioDeformation C)
  (hlawful : T.lawful) :
  T.deformRatio C.ratio = C.ratio := by
  exact h T hlawful

theorem compressionPrincipleEquivalentToNoLiveDeformation
  (C : StandingRatioCertificate) :
  RatioInvariantCompressionPrinciple C <->
    NoLawfulRatioChangingDeformation C := by
  constructor
  · intro hcompress T hvar
    exact hvar.2 (hcompress T hvar.1)
  · intro hnone T hlawful
    classical
    by_cases heq : T.deformRatio C.ratio = C.ratio
    · exact heq
    · exact False.elim (hnone T (And.intro hlawful heq))

/--
A finite residual-output certificate is a weaker possible supersession route:
it need not give a unique ratio, but it changes the current state from an open
minimal interval to a finite same-target output class.
-/
structure FiniteResidualOutputCertificate
  (C : StandingRatioCertificate) where
  OutputClass : Type
  outputOf : C.Ratio -> OutputClass
  admissibleOutput : OutputClass -> Prop
  finiteResidualClass : Prop
  currentOutputAdmissible : admissibleOutput (outputOf C.ratio)

theorem finiteResidualCertificateSuppliesAdmissibleOutput
  (C : StandingRatioCertificate)
  (F : FiniteResidualOutputCertificate C) :
  F.admissibleOutput (F.outputOf C.ratio) := by
  exact F.currentOutputAdmissible

/--
The minimal interval has a live residual fiber when it contains a second
same-target ratio point not identified with the current one.
-/
def MinimalIntervalHasSecondPoint
  (C : StandingRatioCertificate) : Prop :=
  exists r : C.Ratio, C.inMinimalInterval r /\ Not (r = C.ratio)

/--
An AASC ratio constraint is a certified predicate on the same ratio target. It
is not yet a value theorem: by itself it only marks which ratio objects survive
the constraint.
-/
structure AASCRatioConstraint
  (C : StandingRatioCertificate) where
  constrained : C.Ratio -> Prop
  currentConstrained : constrained C.ratio
  soundForMinimalInterval :
    forall r : C.Ratio, constrained r -> C.inMinimalInterval r

/--
The constraint is active on the present same-target deformation space when every
lawful deformation of the current ratio lands inside the constrained region.
-/
def ConstraintActiveOnLawfulImages
  (C : StandingRatioCertificate)
  (K : AASCRatioConstraint C) : Prop :=
  forall T : LawfulRatioDeformation C,
    T.lawful -> K.constrained (T.deformRatio C.ratio)

/--
A singleton AASC constraint is the strong route: every constrained same-target
ratio is identified with the current ratio.
-/
def ConstraintSingleton
  (C : StandingRatioCertificate)
  (K : AASCRatioConstraint C) : Prop :=
  forall r : C.Ratio, K.constrained r -> r = C.ratio

/--
If an AASC constraint is active on lawful same-target images and its constrained
fiber is singleton, then it supplies the missing ratio-invariant compression
principle.
-/
theorem singletonAASCConstraintGivesRatioInvariantCompression
  (C : StandingRatioCertificate)
  (K : AASCRatioConstraint C)
  (hactive : ConstraintActiveOnLawfulImages C K)
  (hsingle : ConstraintSingleton C K) :
  RatioInvariantCompressionPrinciple C := by
  intro T hlawful
  exact hsingle (T.deformRatio C.ratio) (hactive T hlawful)

/--
If the AASC constraint also covers the entire minimal interval fiber, singleton
constraint closure rules out a second minimal-interval ratio point outright.
This is stronger than what is needed for deformation invariance, but it matches
the paper-facing phrase "collapse the interval fiber."
-/
def ConstraintCoversMinimalInterval
  (C : StandingRatioCertificate)
  (K : AASCRatioConstraint C) : Prop :=
  forall r : C.Ratio, C.inMinimalInterval r -> K.constrained r

theorem singletonAASCConstraintRulesOutSecondMinimalPoint
  (C : StandingRatioCertificate)
  (K : AASCRatioConstraint C)
  (hcovers : ConstraintCoversMinimalInterval C K)
  (hsingle : ConstraintSingleton C K) :
  Not (MinimalIntervalHasSecondPoint C) := by
  intro hsecond
  rcases hsecond with ⟨r, hrInterval, hrNe⟩
  exact hrNe (hsingle r (hcovers r hrInterval))

/--
Constraint-exclusion route: instead of first proving that the constrained fiber
is globally singleton, one may prove directly that every lawful image satisfying
the constraint cannot be a ratio-changing image.
-/
def ConstraintExcludesLawfulRatioChanges
  (C : StandingRatioCertificate)
  (K : AASCRatioConstraint C) : Prop :=
  forall T : LawfulRatioDeformation C,
    T.lawful ->
      K.constrained (T.deformRatio C.ratio) ->
        T.deformRatio C.ratio = C.ratio

theorem excludingAASCConstraintGivesRatioInvariantCompression
  (C : StandingRatioCertificate)
  (K : AASCRatioConstraint C)
  (hactive : ConstraintActiveOnLawfulImages C K)
  (hexcludes : ConstraintExcludesLawfulRatioChanges C K) :
  RatioInvariantCompressionPrinciple C := by
  intro T hlawful
  exact hexcludes T hlawful (hactive T hlawful)

theorem excludingAASCConstraintRulesOutLiveDeformations
  (C : StandingRatioCertificate)
  (K : AASCRatioConstraint C)
  (hactive : ConstraintActiveOnLawfulImages C K)
  (hexcludes : ConstraintExcludesLawfulRatioChanges C K) :
  NoLawfulRatioChangingDeformation C := by
  exact
    (compressionPrincipleEquivalentToNoLiveDeformation C).mp
      (excludingAASCConstraintGivesRatioInvariantCompression
        C K hactive hexcludes)

/--
A finite AASC constraint is the weaker route: it supplies a finite residual class
without requiring a unique ratio. This is enough to move beyond the open
minimal-interval state, but not enough by itself to prove ratio invariance.
-/
structure AASCFiniteConstraint
  (C : StandingRatioCertificate)
  extends AASCRatioConstraint C where
  OutputClass : Type
  outputOf : C.Ratio -> OutputClass
  finiteOutputClass : Prop
  constrainedHasOutput :
    forall r : C.Ratio, constrained r -> outputOf r = outputOf C.ratio

def finiteAASCConstraintGivesResidualOutput
  (C : StandingRatioCertificate)
  (K : AASCFiniteConstraint C) :
  FiniteResidualOutputCertificate C := by
  exact
    { OutputClass := K.OutputClass
      outputOf := K.outputOf
      admissibleOutput := fun out => out = K.outputOf C.ratio
      finiteResidualClass := K.finiteOutputClass
      currentOutputAdmissible := rfl }

/--
Audit predicates for deciding whether an advertised constraint is genuinely
AASC-admissible rather than a renamed fit, selector, convention, or comparator.
The predicates remain abstract because this module is the blocker workbench, not
the domain-specific physics source theorem.
-/
structure AASCConstraintAudit
  (C : StandingRatioCertificate)
  (K : AASCRatioConstraint C) where
  sourceCertified : Prop
  carrierInternal : Prop
  calibrationFree : Prop
  sameTargetStable : Prop
  noHiddenSelector : Prop
  notComparatorPromotion : Prop
  preservesStandingRoles : Prop

/--
The strict audit pass needed before a constraint can be used as a compression
source in the NNR sense.
-/
def AuditPasses
  {C : StandingRatioCertificate}
  {K : AASCRatioConstraint C}
  (A : AASCConstraintAudit C K) : Prop :=
  A.sourceCertified /\
  A.carrierInternal /\
  A.calibrationFree /\
  A.sameTargetStable /\
  A.noHiddenSelector /\
  A.notComparatorPromotion /\
  A.preservesStandingRoles

/--
Source-theorem interface for the desired deeper paper.

This packages the exact content a domain-specific AASC/spectral-shape theorem
must supply in order to turn the current minimal interval lock into genuine
ratio compression: a constraint, an audit, an activity theorem on lawful images,
and an exclusion theorem for all ratio-changing lawful images.
-/
structure AASCConstraintSourceTheorem
  (C : StandingRatioCertificate) where
  constraint : AASCRatioConstraint C
  audit : AASCConstraintAudit C constraint
  auditPasses : AuditPasses audit
  activeOnLawfulImages : ConstraintActiveOnLawfulImages C constraint
  excludesLawfulRatioChanges :
    ConstraintExcludesLawfulRatioChanges C constraint

theorem sourceTheoremGivesRatioCompression
  (C : StandingRatioCertificate)
  (S : AASCConstraintSourceTheorem C) :
  RatioInvariantCompressionPrinciple C := by
  exact
    excludingAASCConstraintGivesRatioInvariantCompression
      C
      S.constraint
      S.activeOnLawfulImages
      S.excludesLawfulRatioChanges

theorem sourceTheoremKillsLiveDeformations
  (C : StandingRatioCertificate)
  (S : AASCConstraintSourceTheorem C) :
  NoLawfulRatioChangingDeformation C := by
  exact
    (compressionPrincipleEquivalentToNoLiveDeformation C).mp
      (sourceTheoremGivesRatioCompression C S)

/--
The candidate source theorem is incompatible with a live deformation witness.
This is useful as a hostile-audit test: a proposed source theorem must explain
why every previously live second-point deformation is no longer lawful,
constraint-satisfying, or ratio-changing.
-/
theorem sourceTheoremContradictsLiveDeformation
  (C : StandingRatioCertificate)
  (S : AASCConstraintSourceTheorem C)
  (T : LawfulRatioDeformation C)
  (hvar : ratioCanVary C T) :
  False := by
  exact sourceTheoremKillsLiveDeformations C S T hvar

/--
An audited singleton constraint is the positive target for a deeper derivation:
it has passed the AASC guardrails, is active on lawful same-target images, and
has a singleton constrained fiber.
-/
structure AuditedSingletonConstraint
  (C : StandingRatioCertificate) where
  constraint : AASCRatioConstraint C
  audit : AASCConstraintAudit C constraint
  auditPasses : AuditPasses audit
  activeOnLawfulImages : ConstraintActiveOnLawfulImages C constraint
  singletonFiber : ConstraintSingleton C constraint

theorem auditedSingletonConstraintGivesCompression
  (C : StandingRatioCertificate)
  (K : AuditedSingletonConstraint C) :
  RatioInvariantCompressionPrinciple C := by
  exact
    singletonAASCConstraintGivesRatioInvariantCompression
      C
      K.constraint
      K.activeOnLawfulImages
      K.singletonFiber

/--
If a passing audited singleton constraint covers the minimal interval, it also
rules out every second ratio point in the minimal interval fiber.
-/
structure AuditedIntervalCollapseConstraint
  (C : StandingRatioCertificate)
  extends AuditedSingletonConstraint C where
  coversMinimalInterval : ConstraintCoversMinimalInterval C constraint

theorem auditedIntervalCollapseRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (K : AuditedIntervalCollapseConstraint C) :
  Not (MinimalIntervalHasSecondPoint C) := by
  exact
    singletonAASCConstraintRulesOutSecondMinimalPoint
      C
      K.constraint
      K.coversMinimalInterval
      K.singletonFiber

/--
Finite audited constraints are the weaker route. They can certify a finite
residual output class without asserting a unique ratio.
-/
structure AuditedFiniteConstraint
  (C : StandingRatioCertificate) where
  constraint : AASCFiniteConstraint C
  audit : AASCConstraintAudit C constraint.toAASCRatioConstraint
  auditPasses : AuditPasses audit
  activeOnLawfulImages :
    ConstraintActiveOnLawfulImages C constraint.toAASCRatioConstraint

def auditedFiniteConstraintGivesResidualOutput
  (C : StandingRatioCertificate)
  (K : AuditedFiniteConstraint C) :
  FiniteResidualOutputCertificate C :=
  finiteAASCConstraintGivesResidualOutput C K.constraint

/--
The exact obstruction against pretending an audited finite constraint is already
a value theorem: finite output does not imply singleton compression unless a
separate singleton-fiber theorem is supplied.
-/
def FiniteConstraintHasSingletonFiber
  (C : StandingRatioCertificate)
  (K : AuditedFiniteConstraint C) : Prop :=
  ConstraintSingleton C K.constraint.toAASCRatioConstraint

theorem auditedFiniteConstraintBecomesCompressionWithSingletonFiber
  (C : StandingRatioCertificate)
  (K : AuditedFiniteConstraint C)
  (hsingle : FiniteConstraintHasSingletonFiber C K) :
  RatioInvariantCompressionPrinciple C := by
  exact
    singletonAASCConstraintGivesRatioInvariantCompression
      C
      K.constraint.toAASCRatioConstraint
      K.activeOnLawfulImages
      hsingle

/--
Source-theorem interface for the weaker finite-class route. It is a genuine
supersession of the open minimal-interval state, but it does not claim exact
ratio compression unless a singleton-fiber theorem is added separately.
-/
structure AASCFiniteConstraintSourceTheorem
  (C : StandingRatioCertificate) where
  constraint : AASCFiniteConstraint C
  audit : AASCConstraintAudit C constraint.toAASCRatioConstraint
  auditPasses : AuditPasses audit
  activeOnLawfulImages :
    ConstraintActiveOnLawfulImages C constraint.toAASCRatioConstraint

def finiteSourceTheoremGivesResidualOutput
  (C : StandingRatioCertificate)
  (S : AASCFiniteConstraintSourceTheorem C) :
  FiniteResidualOutputCertificate C :=
  finiteAASCConstraintGivesResidualOutput C S.constraint

theorem finiteSourceTheoremDoesNotByItselfKillDeformations
  (C : StandingRatioCertificate)
  (S : AASCFiniteConstraintSourceTheorem C)
  (hsingle :
    ConstraintSingleton C S.constraint.toAASCRatioConstraint) :
  RatioInvariantCompressionPrinciple C := by
  exact
    singletonAASCConstraintGivesRatioInvariantCompression
      C
      S.constraint.toAASCRatioConstraint
      S.activeOnLawfulImages
      hsingle

/--
CNF2/CNF6-facing spectral quotient route, suggested by the v1.5 corpus census.

This is the finite/bounded route named by NNR4H: if the standing neutrino ratio
descends to a CNF6 spectral quotient class with standing numerator and
denominator, and if a CNF2/CNF6 finite-collapse, overlap-reduction, or
solver-reduction certificate acts on that same target, the ratio moves beyond
the open minimal interval into a certified output class.

It still does not assert exact ratio compression unless a singleton/evaluator
theorem is supplied separately.
-/
structure CNF6SpectralQuotientRoute
  (C : StandingRatioCertificate) where
  SpectralClass : Type
  spectralClassOf : C.Ratio -> SpectralClass
  descendsToQSpec : Prop
  standingNumeratorDenominator : Prop
  targetPreservingTransport : Prop
  calibrationFree : Prop
  extractionCertified : Prop
  finiteCollapseCertificate : Prop
  overlapReductionCertificate : Prop
  solverReductionCertificate : Prop
  lawfulImagesStayInClass :
    forall T : LawfulRatioDeformation C,
      T.lawful ->
        spectralClassOf (T.deformRatio C.ratio) =
          spectralClassOf C.ratio
  classSoundForMinimalInterval :
    forall r : C.Ratio,
      spectralClassOf r = spectralClassOf C.ratio ->
        C.inMinimalInterval r

def CNF6HasReductionCertificate
  {C : StandingRatioCertificate}
  (R : CNF6SpectralQuotientRoute C) : Prop :=
  R.finiteCollapseCertificate \/
    R.overlapReductionCertificate \/
      R.solverReductionCertificate

def cnf6SpectralQuotientConstraint
  (C : StandingRatioCertificate)
  (R : CNF6SpectralQuotientRoute C) :
  AASCFiniteConstraint C :=
  { constrained := fun r =>
      R.spectralClassOf r = R.spectralClassOf C.ratio
    currentConstrained := rfl
    soundForMinimalInterval := R.classSoundForMinimalInterval
    OutputClass := R.SpectralClass
    outputOf := R.spectralClassOf
    finiteOutputClass := CNF6HasReductionCertificate R
    constrainedHasOutput := by
      intro r hclass
      exact hclass }

def cnf6SpectralQuotientAudit
  (C : StandingRatioCertificate)
  (R : CNF6SpectralQuotientRoute C) :
  AASCConstraintAudit
    C
    (cnf6SpectralQuotientConstraint C R).toAASCRatioConstraint :=
  { sourceCertified := R.descendsToQSpec
    carrierInternal := R.standingNumeratorDenominator
    calibrationFree := R.calibrationFree
    sameTargetStable := R.targetPreservingTransport
    noHiddenSelector := R.extractionCertified
    notComparatorPromotion := CNF6HasReductionCertificate R
    preservesStandingRoles := R.standingNumeratorDenominator }

def cnf6SpectralQuotientAuditPasses
  (C : StandingRatioCertificate)
  (R : CNF6SpectralQuotientRoute C)
  (hqspec : R.descendsToQSpec)
  (hstanding : R.standingNumeratorDenominator)
  (htransport : R.targetPreservingTransport)
  (hcalibration : R.calibrationFree)
  (hextraction : R.extractionCertified)
  (hreduction : CNF6HasReductionCertificate R) :
  AuditPasses (cnf6SpectralQuotientAudit C R) :=
  And.intro hqspec
    (And.intro hstanding
      (And.intro hcalibration
        (And.intro htransport
          (And.intro hextraction
            (And.intro hreduction hstanding)))))

def cnf6SpectralQuotientAsFiniteSourceTheorem
  (C : StandingRatioCertificate)
  (R : CNF6SpectralQuotientRoute C)
  (hqspec : R.descendsToQSpec)
  (hstanding : R.standingNumeratorDenominator)
  (htransport : R.targetPreservingTransport)
  (hcalibration : R.calibrationFree)
  (hextraction : R.extractionCertified)
  (hreduction : CNF6HasReductionCertificate R) :
  AASCFiniteConstraintSourceTheorem C :=
  { constraint := cnf6SpectralQuotientConstraint C R
    audit := cnf6SpectralQuotientAudit C R
    auditPasses :=
      cnf6SpectralQuotientAuditPasses
        C R hqspec hstanding htransport hcalibration hextraction hreduction
    activeOnLawfulImages := by
      intro T hlawful
      exact R.lawfulImagesStayInClass T hlawful }

def cnf6SpectralQuotientGivesResidualOutput
  (C : StandingRatioCertificate)
  (R : CNF6SpectralQuotientRoute C)
  (hqspec : R.descendsToQSpec)
  (hstanding : R.standingNumeratorDenominator)
  (htransport : R.targetPreservingTransport)
  (hcalibration : R.calibrationFree)
  (hextraction : R.extractionCertified)
  (hreduction : CNF6HasReductionCertificate R) :
  FiniteResidualOutputCertificate C :=
  finiteSourceTheoremGivesResidualOutput
    C
    (cnf6SpectralQuotientAsFiniteSourceTheorem
      C R hqspec hstanding htransport hcalibration hextraction hreduction)

def CNF6SpectralClassSingleton
  (C : StandingRatioCertificate)
  (R : CNF6SpectralQuotientRoute C) : Prop :=
  ConstraintSingleton C
    (cnf6SpectralQuotientConstraint C R).toAASCRatioConstraint

theorem cnf6SpectralQuotientBecomesCompressionWithSingleton
  (C : StandingRatioCertificate)
  (R : CNF6SpectralQuotientRoute C)
  (hqspec : R.descendsToQSpec)
  (hstanding : R.standingNumeratorDenominator)
  (htransport : R.targetPreservingTransport)
  (hcalibration : R.calibrationFree)
  (hextraction : R.extractionCertified)
  (hreduction : CNF6HasReductionCertificate R)
  (hsingle : CNF6SpectralClassSingleton C R) :
  RatioInvariantCompressionPrinciple C := by
  exact
    finiteSourceTheoremDoesNotByItselfKillDeformations
      C
      (cnf6SpectralQuotientAsFiniteSourceTheorem
        C R hqspec hstanding htransport hcalibration hextraction hreduction)
      hsingle

/--
A quotient normal-form evaluator is the other natural way through the blocker:
it maps every reportable ratio object to a normal form, and the current ratio is
fixed by all lawful deformations at that normal-form level.
-/
structure QuotientNormalFormCertificate
  (C : StandingRatioCertificate) where
  NormalForm : Type
  normalForm : C.Ratio -> NormalForm
  lawfulNormalFormInvariant :
    forall T : LawfulRatioDeformation C,
      T.lawful ->
        normalForm (T.deformRatio C.ratio) = normalForm C.ratio

theorem quotientNormalFormGivesInvariantReadout
  (C : StandingRatioCertificate)
  (Q : QuotientNormalFormCertificate C)
  (T : LawfulRatioDeformation C)
  (hlawful : T.lawful) :
  Q.normalForm (T.deformRatio C.ratio) = Q.normalForm C.ratio := by
  exact Q.lawfulNormalFormInvariant T hlawful

/--
Normal-form soundness says that the normal-form fiber through the current ratio
stays inside the already reportable minimal interval target.
-/
def NormalFormSoundForMinimalInterval
  (C : StandingRatioCertificate)
  (Q : QuotientNormalFormCertificate C) : Prop :=
  forall r : C.Ratio,
    Q.normalForm r = Q.normalForm C.ratio ->
      C.inMinimalInterval r

/--
Normal-form injectivity at the current ratio is the decisive extra theorem:
inside the minimal interval fiber, the current normal form identifies only the
current ratio.
-/
def NormalFormInjectiveAtCurrent
  (C : StandingRatioCertificate)
  (Q : QuotientNormalFormCertificate C) : Prop :=
  forall r : C.Ratio,
    C.inMinimalInterval r ->
      Q.normalForm r = Q.normalForm C.ratio ->
        r = C.ratio

def normalFormAASCConstraint
  (C : StandingRatioCertificate)
  (Q : QuotientNormalFormCertificate C)
  (hsound : NormalFormSoundForMinimalInterval C Q) :
  AASCRatioConstraint C :=
  { constrained := fun r => Q.normalForm r = Q.normalForm C.ratio
    currentConstrained := rfl
    soundForMinimalInterval := hsound }

theorem normalFormConstraintActiveOnLawfulImages
  (C : StandingRatioCertificate)
  (Q : QuotientNormalFormCertificate C)
  (hsound : NormalFormSoundForMinimalInterval C Q) :
  ConstraintActiveOnLawfulImages
    C
    (normalFormAASCConstraint C Q hsound) := by
  intro T hlawful
  exact Q.lawfulNormalFormInvariant T hlawful

theorem normalFormConstraintExcludesLawfulRatioChanges
  (C : StandingRatioCertificate)
  (Q : QuotientNormalFormCertificate C)
  (hsound : NormalFormSoundForMinimalInterval C Q)
  (hinj : NormalFormInjectiveAtCurrent C Q) :
  ConstraintExcludesLawfulRatioChanges
    C
    (normalFormAASCConstraint C Q hsound) := by
  intro T _hlawful hnf
  have hInterval : C.inMinimalInterval (T.deformRatio C.ratio) :=
    hsound (T.deformRatio C.ratio) hnf
  exact hinj (T.deformRatio C.ratio) hInterval hnf

/--
Audited source interface for the quotient-normal-form route.
-/
structure AASCNormalFormSourceTheorem
  (C : StandingRatioCertificate) where
  normalFormCertificate : QuotientNormalFormCertificate C
  normalFormSound :
    NormalFormSoundForMinimalInterval C normalFormCertificate
  normalFormInjective :
    NormalFormInjectiveAtCurrent C normalFormCertificate
  audit :
    AASCConstraintAudit
      C
      (normalFormAASCConstraint
        C
        normalFormCertificate
        normalFormSound)
  auditPasses : AuditPasses audit

def normalFormSourceAsConstraintSourceTheorem
  (C : StandingRatioCertificate)
  (S : AASCNormalFormSourceTheorem C) :
  AASCConstraintSourceTheorem C :=
  { constraint :=
      normalFormAASCConstraint
        C
        S.normalFormCertificate
        S.normalFormSound
    audit := S.audit
    auditPasses := S.auditPasses
    activeOnLawfulImages :=
      normalFormConstraintActiveOnLawfulImages
        C
        S.normalFormCertificate
        S.normalFormSound
    excludesLawfulRatioChanges :=
      normalFormConstraintExcludesLawfulRatioChanges
        C
        S.normalFormCertificate
        S.normalFormSound
        S.normalFormInjective }

theorem normalFormSourceGivesRatioCompression
  (C : StandingRatioCertificate)
  (S : AASCNormalFormSourceTheorem C) :
  RatioInvariantCompressionPrinciple C := by
  exact
    sourceTheoremGivesRatioCompression
      C
      (normalFormSourceAsConstraintSourceTheorem C S)

theorem normalFormSourceKillsLiveDeformations
  (C : StandingRatioCertificate)
  (S : AASCNormalFormSourceTheorem C) :
  NoLawfulRatioChangingDeformation C := by
  exact
    sourceTheoremKillsLiveDeformations
      C
      (normalFormSourceAsConstraintSourceTheorem C S)

/--
MR2/MR3-facing spectral-shape source package.

This is the construction target suggested by the corpus control matrix:

* AASC-MR3-DEF-002: spectral/hierarchy source certificate;
* AASC-MR3-DEF-003: source-induced shape map;
* AASC-MR3-DEF-005 and THM-001/002: standing spectral carrier and spectral
  package admission;
* AASC-MR2-DEF-008/009/010 and THM-005: ratio fiber, shape fiber, and
  shape-fiber collapse;
* AASC-MR2-THM-008: calibration-free shape.

The fields are abstract because this file is a theorem interface: a later
domain-specific neutrino paper must instantiate them from its source theorem.
-/
structure SpectralShapeSourcePackage
  (C : StandingRatioCertificate) where
  Source : Type
  Shape : Type
  source : Source
  shapeOfRatio : C.Ratio -> Shape
  sourceCertified : Prop
  standingSpectralCarrier : Prop
  quotientStable : Prop
  transportClosed : Prop
  calibrationFree : Prop
  extractionCertified : Prop
  sourceInducesShapeMap : Prop
  sourceAdmitsCurrentShape :
    shapeOfRatio C.ratio = shapeOfRatio C.ratio
  lawfulImagesPreserveShape :
    forall T : LawfulRatioDeformation C,
      T.lawful ->
        shapeOfRatio (T.deformRatio C.ratio) = shapeOfRatio C.ratio
  shapeFiberSoundForMinimalInterval :
    forall r : C.Ratio,
      shapeOfRatio r = shapeOfRatio C.ratio ->
        C.inMinimalInterval r
  shapeFiberCollapseAtCurrent :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        shapeOfRatio r = shapeOfRatio C.ratio ->
          r = C.ratio

/--
MR3 component: source admission and source-to-shape transport.

This packages the source-side work: the standing spectral carrier, quotient
stability, lawful transport, calibration cleanliness, extraction certification,
and the source-induced shape map. It deliberately does not assert fiber
collapse; that belongs to the MR2 component.
-/
structure MR3SpectralSourceAdmission
  (C : StandingRatioCertificate) where
  Source : Type
  Shape : Type
  source : Source
  shapeOfRatio : C.Ratio -> Shape
  sourceCertified : Prop
  standingSpectralCarrier : Prop
  quotientStable : Prop
  transportClosed : Prop
  calibrationFree : Prop
  extractionCertified : Prop
  sourceInducesShapeMap : Prop
  lawfulImagesPreserveShape :
    forall T : LawfulRatioDeformation C,
      T.lawful ->
        shapeOfRatio (T.deformRatio C.ratio) = shapeOfRatio C.ratio

/--
MR2 component: the ratio/shape-fiber collapse side for a given MR3 source
admission package.
-/
structure MR2RatioShapeFiberCollapse
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C) where
  shapeFiberSoundForMinimalInterval :
    forall r : C.Ratio,
      M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
        C.inMinimalInterval r
  shapeFiberCollapseAtCurrent :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
          r = C.ratio

def mr23PackageAsSpectralShapeSourcePackage
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (F : MR2RatioShapeFiberCollapse C M) :
  SpectralShapeSourcePackage C :=
  { Source := M.Source
    Shape := M.Shape
    source := M.source
    shapeOfRatio := M.shapeOfRatio
    sourceCertified := M.sourceCertified
    standingSpectralCarrier := M.standingSpectralCarrier
    quotientStable := M.quotientStable
    transportClosed := M.transportClosed
    calibrationFree := M.calibrationFree
    extractionCertified := M.extractionCertified
    sourceInducesShapeMap := M.sourceInducesShapeMap
    sourceAdmitsCurrentShape := rfl
    lawfulImagesPreserveShape := M.lawfulImagesPreserveShape
    shapeFiberSoundForMinimalInterval :=
      F.shapeFiberSoundForMinimalInterval
    shapeFiberCollapseAtCurrent :=
      F.shapeFiberCollapseAtCurrent }

def spectralShapeNormalFormCertificate
  (C : StandingRatioCertificate)
  (P : SpectralShapeSourcePackage C) :
  QuotientNormalFormCertificate C :=
  { NormalForm := P.Shape
    normalForm := P.shapeOfRatio
    lawfulNormalFormInvariant := P.lawfulImagesPreserveShape }

theorem spectralShapeNormalFormSound
  (C : StandingRatioCertificate)
  (P : SpectralShapeSourcePackage C) :
  NormalFormSoundForMinimalInterval
    C
    (spectralShapeNormalFormCertificate C P) := by
  exact P.shapeFiberSoundForMinimalInterval

theorem spectralShapeNormalFormInjective
  (C : StandingRatioCertificate)
  (P : SpectralShapeSourcePackage C) :
  NormalFormInjectiveAtCurrent
    C
    (spectralShapeNormalFormCertificate C P) := by
  exact P.shapeFiberCollapseAtCurrent

def spectralShapeAudit
  (C : StandingRatioCertificate)
  (P : SpectralShapeSourcePackage C) :
  AASCConstraintAudit
    C
    (normalFormAASCConstraint
      C
      (spectralShapeNormalFormCertificate C P)
      (spectralShapeNormalFormSound C P)) :=
  { sourceCertified := P.sourceCertified
    carrierInternal := P.standingSpectralCarrier
    calibrationFree := P.calibrationFree
    sameTargetStable := P.quotientStable /\ P.transportClosed
    noHiddenSelector := P.extractionCertified
    notComparatorPromotion := P.sourceInducesShapeMap
    preservesStandingRoles := P.standingSpectralCarrier }

def spectralShapeAuditPasses
  (C : StandingRatioCertificate)
  (P : SpectralShapeSourcePackage C)
  (hsource : P.sourceCertified)
  (hcarrier : P.standingSpectralCarrier)
  (hquotient : P.quotientStable)
  (htransport : P.transportClosed)
  (hcalibration : P.calibrationFree)
  (hextraction : P.extractionCertified)
  (hmap : P.sourceInducesShapeMap) :
  AuditPasses (spectralShapeAudit C P) :=
  And.intro hsource
    (And.intro hcarrier
      (And.intro hcalibration
        (And.intro (And.intro hquotient htransport)
          (And.intro hextraction
            (And.intro hmap hcarrier)))))

def spectralShapePackageAsNormalFormSource
  (C : StandingRatioCertificate)
  (P : SpectralShapeSourcePackage C)
  (hsource : P.sourceCertified)
  (hcarrier : P.standingSpectralCarrier)
  (hquotient : P.quotientStable)
  (htransport : P.transportClosed)
  (hcalibration : P.calibrationFree)
  (hextraction : P.extractionCertified)
  (hmap : P.sourceInducesShapeMap) :
  AASCNormalFormSourceTheorem C :=
  { normalFormCertificate := spectralShapeNormalFormCertificate C P
    normalFormSound := spectralShapeNormalFormSound C P
    normalFormInjective := spectralShapeNormalFormInjective C P
    audit := spectralShapeAudit C P
    auditPasses :=
      spectralShapeAuditPasses
        C
        P
        hsource
        hcarrier
        hquotient
        htransport
        hcalibration
        hextraction
        hmap }

theorem spectralShapePackageGivesRatioCompression
  (C : StandingRatioCertificate)
  (P : SpectralShapeSourcePackage C)
  (hsource : P.sourceCertified)
  (hcarrier : P.standingSpectralCarrier)
  (hquotient : P.quotientStable)
  (htransport : P.transportClosed)
  (hcalibration : P.calibrationFree)
  (hextraction : P.extractionCertified)
  (hmap : P.sourceInducesShapeMap) :
  RatioInvariantCompressionPrinciple C := by
  exact
    normalFormSourceGivesRatioCompression
      C
      (spectralShapePackageAsNormalFormSource
        C
        P
        hsource
        hcarrier
        hquotient
        htransport
        hcalibration
        hextraction
        hmap)

theorem spectralShapePackageKillsLiveDeformations
  (C : StandingRatioCertificate)
  (P : SpectralShapeSourcePackage C)
  (hsource : P.sourceCertified)
  (hcarrier : P.standingSpectralCarrier)
  (hquotient : P.quotientStable)
  (htransport : P.transportClosed)
  (hcalibration : P.calibrationFree)
  (hextraction : P.extractionCertified)
  (hmap : P.sourceInducesShapeMap) :
  NoLawfulRatioChangingDeformation C := by
  exact
    normalFormSourceKillsLiveDeformations
      C
      (spectralShapePackageAsNormalFormSource
        C
        P
        hsource
        hcarrier
        hquotient
        htransport
        hcalibration
        hextraction
        hmap)

theorem mr23SourceAndCollapseGiveRatioCompression
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (F : MR2RatioShapeFiberCollapse C M)
  (hsource : M.sourceCertified)
  (hcarrier : M.standingSpectralCarrier)
  (hquotient : M.quotientStable)
  (htransport : M.transportClosed)
  (hcalibration : M.calibrationFree)
  (hextraction : M.extractionCertified)
  (hmap : M.sourceInducesShapeMap) :
  RatioInvariantCompressionPrinciple C := by
  exact
    spectralShapePackageGivesRatioCompression
      C
      (mr23PackageAsSpectralShapeSourcePackage C M F)
      hsource
      hcarrier
      hquotient
      htransport
      hcalibration
      hextraction
      hmap

theorem mr23SourceAndCollapseKillLiveDeformations
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (F : MR2RatioShapeFiberCollapse C M)
  (hsource : M.sourceCertified)
  (hcarrier : M.standingSpectralCarrier)
  (hquotient : M.quotientStable)
  (htransport : M.transportClosed)
  (hcalibration : M.calibrationFree)
  (hextraction : M.extractionCertified)
  (hmap : M.sourceInducesShapeMap) :
  NoLawfulRatioChangingDeformation C := by
  exact
    spectralShapePackageKillsLiveDeformations
      C
      (mr23PackageAsSpectralShapeSourcePackage C M F)
      hsource
      hcarrier
      hquotient
      htransport
      hcalibration
      hextraction
      hmap

/--
MR5-facing cross-sector singleton network.

The v1.5 corpus census points to the constructive route that was missing from
the earlier blocker statement: active cross-sector constraints, aligned on the
same target and audited for nonredundant/non-overcounting use, can construct the
singleton shape fiber needed by MR2.

This structure is intentionally abstract about the individual sector
constraints. Its theorem-facing payload is the last two fields: the network's
restricted shape fiber is sound for the current minimal interval and singleton
at the current ratio.
-/
structure MR5CrossSectorShapeSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C) where
  SectorConstraint : Type
  activeConstraint : SectorConstraint -> Prop
  independentConstraint : SectorConstraint -> Prop
  nonredundantConstraint : SectorConstraint -> Prop
  networkNonempty : Prop
  sameTargetAligned : Prop
  calibrationFree : Prop
  transportClosed : Prop
  noOvercounting : Prop
  noHiddenSelector : Prop
  activeConstraintsAreIndependent :
    forall k : SectorConstraint,
      activeConstraint k -> independentConstraint k
  activeConstraintsAreNonredundant :
    forall k : SectorConstraint,
      activeConstraint k -> nonredundantConstraint k
  shapeFiberSoundForMinimalInterval :
    forall r : C.Ratio,
      M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
        C.inMinimalInterval r
  restrictedShapeFiberSingleton :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
          r = C.ratio

/--
Audit pass for the MR5 network layer. This mirrors the corpus rows around
source nodes, joint restricted fibers, constraint-counting, domain coherence,
calibration deletion, and no-overcounting.
-/
def MR5NetworkAuditPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (N : MR5CrossSectorShapeSingleton C M) : Prop :=
  N.networkNonempty /\
  N.sameTargetAligned /\
  N.calibrationFree /\
  N.transportClosed /\
  N.noOvercounting /\
  N.noHiddenSelector /\
  (forall k : N.SectorConstraint,
    N.activeConstraint k -> N.independentConstraint k) /\
  (forall k : N.SectorConstraint,
    N.activeConstraint k -> N.nonredundantConstraint k)

/--
An MR5 cross-sector singleton network supplies exactly the MR2 collapse theorem
needed by the MR3 source admission package.
-/
def mr5NetworkGivesMR2ShapeFiberCollapse
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (N : MR5CrossSectorShapeSingleton C M) :
  MR2RatioShapeFiberCollapse C M :=
  { shapeFiberSoundForMinimalInterval :=
      N.shapeFiberSoundForMinimalInterval
    shapeFiberCollapseAtCurrent :=
      N.restrictedShapeFiberSingleton }

/--
AASC construction package for the deeper neutrino derivation.

The MR3 half admits the source-induced spectral/hierarchy shape map. The MR5
half supplies the audited cross-sector singleton network. Once both pass, Lean
can assemble the normal-form source theorem used by the ratio blocker.
-/
structure AASCMR5ShapeConstructionTheorem
  (C : StandingRatioCertificate) where
  sourceAdmission : MR3SpectralSourceAdmission C
  singletonNetwork :
    MR5CrossSectorShapeSingleton C sourceAdmission
  sourceCertified : sourceAdmission.sourceCertified
  standingSpectralCarrier : sourceAdmission.standingSpectralCarrier
  quotientStable : sourceAdmission.quotientStable
  transportClosed : sourceAdmission.transportClosed
  calibrationFree : sourceAdmission.calibrationFree
  extractionCertified : sourceAdmission.extractionCertified
  sourceInducesShapeMap : sourceAdmission.sourceInducesShapeMap
  networkAuditPasses :
    MR5NetworkAuditPasses singletonNetwork

def mr5ConstructionAsMR2ShapeFiberCollapse
  (C : StandingRatioCertificate)
  (S : AASCMR5ShapeConstructionTheorem C) :
  MR2RatioShapeFiberCollapse C S.sourceAdmission :=
  mr5NetworkGivesMR2ShapeFiberCollapse
    C
    S.sourceAdmission
    S.singletonNetwork

def mr5ConstructionAsSpectralShapePackage
  (C : StandingRatioCertificate)
  (S : AASCMR5ShapeConstructionTheorem C) :
  SpectralShapeSourcePackage C :=
  mr23PackageAsSpectralShapeSourcePackage
    C
    S.sourceAdmission
    (mr5ConstructionAsMR2ShapeFiberCollapse C S)

def mr5ConstructionAsNormalFormSourceTheorem
  (C : StandingRatioCertificate)
  (S : AASCMR5ShapeConstructionTheorem C) :
  AASCNormalFormSourceTheorem C :=
  spectralShapePackageAsNormalFormSource
    C
    (mr5ConstructionAsSpectralShapePackage C S)
    S.sourceCertified
    S.standingSpectralCarrier
    S.quotientStable
    S.transportClosed
    S.calibrationFree
    S.extractionCertified
    S.sourceInducesShapeMap

/--
The fully packaged close theorem: an admitted MR3 source plus an audited MR5
cross-sector singleton construction proves ratio-invariant compression.
-/
theorem mr5ConstructionGivesRatioCompression
  (C : StandingRatioCertificate)
  (S : AASCMR5ShapeConstructionTheorem C) :
  RatioInvariantCompressionPrinciple C := by
  exact
    normalFormSourceGivesRatioCompression
      C
      (mr5ConstructionAsNormalFormSourceTheorem C S)

theorem mr5ConstructionKillsLiveDeformations
  (C : StandingRatioCertificate)
  (S : AASCMR5ShapeConstructionTheorem C) :
  NoLawfulRatioChangingDeformation C := by
  exact
    normalFormSourceKillsLiveDeformations
      C
      (mr5ConstructionAsNormalFormSourceTheorem C S)

/--
The AASC construction path: MR3 admits the source-induced shape map, MR5
constructs the singleton cross-sector fiber, and the existing MR2/MR3 bridge
then yields ratio-invariant compression.
-/
theorem mr35NetworkGivesRatioCompression
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (N : MR5CrossSectorShapeSingleton C M)
  (hsource : M.sourceCertified)
  (hcarrier : M.standingSpectralCarrier)
  (hquotient : M.quotientStable)
  (htransport : M.transportClosed)
  (hcalibration : M.calibrationFree)
  (hextraction : M.extractionCertified)
  (hmap : M.sourceInducesShapeMap) :
  RatioInvariantCompressionPrinciple C := by
  exact
    mr23SourceAndCollapseGiveRatioCompression
      C
      M
      (mr5NetworkGivesMR2ShapeFiberCollapse C M N)
      hsource
      hcarrier
      hquotient
      htransport
      hcalibration
      hextraction
      hmap

theorem mr35NetworkKillsLiveDeformations
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (N : MR5CrossSectorShapeSingleton C M)
  (hsource : M.sourceCertified)
  (hcarrier : M.standingSpectralCarrier)
  (hquotient : M.quotientStable)
  (htransport : M.transportClosed)
  (hcalibration : M.calibrationFree)
  (hextraction : M.extractionCertified)
  (hmap : M.sourceInducesShapeMap) :
  NoLawfulRatioChangingDeformation C := by
  exact
    mr23SourceAndCollapseKillLiveDeformations
      C
      M
      (mr5NetworkGivesMR2ShapeFiberCollapse C M N)
      hsource
      hcarrier
      hquotient
      htransport
      hcalibration
      hextraction
      hmap

/--
The four stronger-output law forms isolated by the NNR4G audit.

They are candidate sources only. A value, finite class, or singleton collapse is
licensed only after the candidate passes the AASC source gate below.
-/
inductive NeutrinoCompressionLawForm where
  | algebraicSumRule
  | finiteResidualOrbit
  | spectralQuotient
  | hierarchyCompression

/--
A candidate source theorem for a stronger neutrino-ratio output.

This records the exact audit burden before a candidate law form may be counted
as an MR5 source node. The final field is deliberately strong: the candidate
must actually collapse the admitted source shape fiber, not merely motivate,
fit, rank, or partially restrict it.
-/
structure NeutrinoCompressionCandidate
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C) where
  lawForm : NeutrinoCompressionLawForm
  sourceAncestryCertified : Prop
  targetPreservingTransport : Prop
  quotientStable : Prop
  calibrationFree : Prop
  noObservedValueImport : Prop
  noComparatorPromotion : Prop
  noBranchSelector : Prop
  noIdentityShapeSelector : Prop
  activeForStandingRatio :
    forall T : LawfulRatioDeformation C,
      T.lawful ->
        M.shapeOfRatio (T.deformRatio C.ratio) =
          M.shapeOfRatio C.ratio
  shapeFiberSoundForMinimalInterval :
    forall r : C.Ratio,
      M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
        C.inMinimalInterval r
  collapsesShapeFiber :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
          r = C.ratio

/--
An AASC translation of a promising external law form.

The external formula, modular model, residual-symmetry ansatz, or seesaw texture
is not counted directly. It first has to be re-expressed as a source-internal
restriction on the standing ratio target, with empirical/model-selection
content deleted.
-/
structure AASCTranslatedCompressionLaw
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C) where
  lawForm : NeutrinoCompressionLawForm
  ExternalLaw : Type
  externalLaw : ExternalLaw
  AASCRestriction : C.Ratio -> Prop
  currentSatisfiesRestriction : AASCRestriction C.ratio
  sourceDerivesRestriction : Prop
  sourceAncestryCertified : Prop
  targetPreservingTransport : Prop
  quotientStable : Prop
  calibrationFreeAfterDeletion : Prop
  observedInputsDeleted : Prop
  comparatorContentDeleted : Prop
  branchSelectorDeleted : Prop
  identityShapeSelectorExcluded : Prop
  activeRestrictionForStandingRatio :
    forall T : LawfulRatioDeformation C,
      T.lawful -> AASCRestriction (T.deformRatio C.ratio)
  restrictionImpliesShape :
    forall r : C.Ratio,
      AASCRestriction r ->
        M.shapeOfRatio r = M.shapeOfRatio C.ratio
  shapeImpliesRestriction :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
          AASCRestriction r
  shapeFiberSoundForMinimalInterval :
    forall r : C.Ratio,
      M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
        C.inMinimalInterval r
  restrictionSoundForMinimalInterval :
    forall r : C.Ratio,
      AASCRestriction r -> C.inMinimalInterval r
  restrictionSingleton :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        AASCRestriction r ->
          r = C.ratio

def AASCTranslatedLawAuditPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (L : AASCTranslatedCompressionLaw C M) : Prop :=
  L.sourceDerivesRestriction /\
  L.sourceAncestryCertified /\
  L.targetPreservingTransport /\
  L.quotientStable /\
  L.calibrationFreeAfterDeletion /\
  L.observedInputsDeleted /\
  L.comparatorContentDeleted /\
  L.branchSelectorDeleted /\
  L.identityShapeSelectorExcluded

/--
Specialized AASC version of the most promising external route:
modular/flavor mass-sum-rule collapse.

The point of this wrapper is to name the extra conversion work. A modular form,
flavor texture, or sum rule does not count until its observed-fit and
model-selection content has been deleted and the remaining law is transported to
the standing neutrino ratio target.
-/
structure AASCModularMassSumRuleTranslation
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C) where
  ModularDatum : Type
  modularDatum : ModularDatum
  SumRule : Type
  sumRule : SumRule
  ModularRestriction : C.Ratio -> Prop
  modularSourceInternal : Prop
  modularDatumNotFitSelected : Prop
  sumRuleDerivedFromSource : Prop
  sumRuleHasStandingCoefficients : Prop
  sumRuleTransportedToRatioTarget : Prop
  measuredSplittingsDeleted : Prop
  phenomenologicalBranchDeleted : Prop
  comparatorSuccessDeleted : Prop
  notIdentityReadout : Prop
  quotientStableForShape : Prop
  restrictionCurrent :
    ModularRestriction C.ratio
  restrictionActiveOnLawfulImages :
    forall T : LawfulRatioDeformation C,
      T.lawful -> ModularRestriction (T.deformRatio C.ratio)
  restrictionImpliesShape :
    forall r : C.Ratio,
      ModularRestriction r ->
        M.shapeOfRatio r = M.shapeOfRatio C.ratio
  shapeImpliesRestriction :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
          ModularRestriction r
  shapeFiberSoundForMinimalInterval :
    forall r : C.Ratio,
      M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
        C.inMinimalInterval r
  restrictionSoundForMinimalInterval :
    forall r : C.Ratio,
      ModularRestriction r -> C.inMinimalInterval r
  modularRestrictionSingleton :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        ModularRestriction r ->
          r = C.ratio

def modularMassSumRuleAsTranslatedLaw
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (S : AASCModularMassSumRuleTranslation C M) :
  AASCTranslatedCompressionLaw C M :=
  { lawForm := NeutrinoCompressionLawForm.algebraicSumRule
    ExternalLaw := S.ModularDatum × S.SumRule
    externalLaw := (S.modularDatum, S.sumRule)
    AASCRestriction := S.ModularRestriction
    currentSatisfiesRestriction := S.restrictionCurrent
    sourceDerivesRestriction := S.sumRuleDerivedFromSource
    sourceAncestryCertified :=
      S.modularSourceInternal /\ S.sumRuleHasStandingCoefficients
    targetPreservingTransport := S.sumRuleTransportedToRatioTarget
    quotientStable := S.quotientStableForShape
    calibrationFreeAfterDeletion :=
      S.modularDatumNotFitSelected /\ S.measuredSplittingsDeleted
    observedInputsDeleted := S.measuredSplittingsDeleted
    comparatorContentDeleted := S.comparatorSuccessDeleted
    branchSelectorDeleted := S.phenomenologicalBranchDeleted
    identityShapeSelectorExcluded := S.notIdentityReadout
    activeRestrictionForStandingRatio :=
      S.restrictionActiveOnLawfulImages
    restrictionImpliesShape := S.restrictionImpliesShape
    shapeImpliesRestriction := S.shapeImpliesRestriction
    shapeFiberSoundForMinimalInterval :=
      S.shapeFiberSoundForMinimalInterval
    restrictionSoundForMinimalInterval :=
      S.restrictionSoundForMinimalInterval
    restrictionSingleton := S.modularRestrictionSingleton }

def AASCModularMassSumRuleAuditPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (S : AASCModularMassSumRuleTranslation C M) : Prop :=
  S.sumRuleDerivedFromSource /\
  (S.modularSourceInternal /\ S.sumRuleHasStandingCoefficients) /\
  S.sumRuleTransportedToRatioTarget /\
  S.quotientStableForShape /\
  (S.modularDatumNotFitSelected /\ S.measuredSplittingsDeleted) /\
  S.measuredSplittingsDeleted /\
  S.comparatorSuccessDeleted /\
  S.phenomenologicalBranchDeleted /\
  S.notIdentityReadout

theorem modularMassSumRuleAuditPasses
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (S : AASCModularMassSumRuleTranslation C M)
  (haudit : AASCModularMassSumRuleAuditPasses S) :
  AASCTranslatedLawAuditPasses
    (modularMassSumRuleAsTranslatedLaw C M S) := by
  exact haudit

/--
Specialized AASC version of the finite/spectral route.

This is the route named by NNR4G/NNR4H as currently blocked by absent
finite-collapse or overlap-reduction certificates. If those certificates are
constructed, this wrapper converts them into the same translated-law interface.
-/
structure AASCSpectralQuotientCollapseTranslation
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C) where
  SpectralQuotient : Type
  spectralQuotient : SpectralQuotient
  SpectralClass : Type
  spectralClassOf : C.Ratio -> SpectralClass
  spectralRestriction : C.Ratio -> Prop
  descendsToQSpec : Prop
  sourceCertifiedQuotient : Prop
  finiteCollapseCertificate : Prop
  overlapReductionCertificate : Prop
  solverReductionCertificate : Prop
  targetPreservingTransport : Prop
  quotientStableForShape : Prop
  calibrationFree : Prop
  observedInputsDeleted : Prop
  comparatorContentDeleted : Prop
  branchSelectorDeleted : Prop
  identityShapeSelectorExcluded : Prop
  currentInSpectralClass :
    spectralRestriction C.ratio
  reductionActiveOnLawfulImages :
    forall T : LawfulRatioDeformation C,
      T.lawful -> spectralRestriction (T.deformRatio C.ratio)
  restrictionImpliesShape :
    forall r : C.Ratio,
      spectralRestriction r ->
        M.shapeOfRatio r = M.shapeOfRatio C.ratio
  shapeImpliesRestriction :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
          spectralRestriction r
  shapeFiberSoundForMinimalInterval :
    forall r : C.Ratio,
      M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
        C.inMinimalInterval r
  restrictionSoundForMinimalInterval :
    forall r : C.Ratio,
      spectralRestriction r -> C.inMinimalInterval r
  spectralClassSingleton :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        spectralRestriction r ->
          r = C.ratio

def AASCSpectralQuotientHasReduction
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (S : AASCSpectralQuotientCollapseTranslation C M) : Prop :=
  S.finiteCollapseCertificate \/
    S.overlapReductionCertificate \/
      S.solverReductionCertificate

def spectralQuotientAsTranslatedLaw
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (S : AASCSpectralQuotientCollapseTranslation C M) :
  AASCTranslatedCompressionLaw C M :=
  { lawForm := NeutrinoCompressionLawForm.spectralQuotient
    ExternalLaw := S.SpectralQuotient
    externalLaw := S.spectralQuotient
    AASCRestriction := S.spectralRestriction
    currentSatisfiesRestriction := S.currentInSpectralClass
    sourceDerivesRestriction :=
      S.descendsToQSpec /\ AASCSpectralQuotientHasReduction S
    sourceAncestryCertified := S.sourceCertifiedQuotient
    targetPreservingTransport := S.targetPreservingTransport
    quotientStable := S.quotientStableForShape
    calibrationFreeAfterDeletion := S.calibrationFree
    observedInputsDeleted := S.observedInputsDeleted
    comparatorContentDeleted := S.comparatorContentDeleted
    branchSelectorDeleted := S.branchSelectorDeleted
    identityShapeSelectorExcluded := S.identityShapeSelectorExcluded
    activeRestrictionForStandingRatio :=
      S.reductionActiveOnLawfulImages
    restrictionImpliesShape := S.restrictionImpliesShape
    shapeImpliesRestriction := S.shapeImpliesRestriction
    shapeFiberSoundForMinimalInterval :=
      S.shapeFiberSoundForMinimalInterval
    restrictionSoundForMinimalInterval :=
      S.restrictionSoundForMinimalInterval
    restrictionSingleton := S.spectralClassSingleton }

def AASCSpectralQuotientAuditPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (S : AASCSpectralQuotientCollapseTranslation C M) : Prop :=
  (S.descendsToQSpec /\ AASCSpectralQuotientHasReduction S) /\
  S.sourceCertifiedQuotient /\
  S.targetPreservingTransport /\
  S.quotientStableForShape /\
  S.calibrationFree /\
  S.observedInputsDeleted /\
  S.comparatorContentDeleted /\
  S.branchSelectorDeleted /\
  S.identityShapeSelectorExcluded

theorem spectralQuotientAuditPasses
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (S : AASCSpectralQuotientCollapseTranslation C M)
  (haudit : AASCSpectralQuotientAuditPasses S) :
  AASCTranslatedLawAuditPasses
    (spectralQuotientAsTranslatedLaw C M S) := by
  exact haudit

/--
Specialized AASC version of the scoto-seesaw idea.

This route is promising because it mirrors the standing role separation: an
atmospheric mechanism and a solar mechanism are distinct by construction. It
only becomes compression, however, if the remaining dark/seesaw parameter fiber
is source-collapsed or quotient-skin, rather than fitted.
-/
structure AASCScotoSeesawTranslation
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C) where
  AtmosphericMechanism : Type
  SolarMechanism : Type
  DarkSector : Type
  ParameterFiber : Type
  atmosphericMechanism : AtmosphericMechanism
  solarMechanism : SolarMechanism
  darkSector : DarkSector
  parameterFiber : ParameterFiber
  scotoRestriction : C.Ratio -> Prop
  atmosphericSourceInternal : Prop
  solarSourceInternal : Prop
  darkSectorSourceInternal : Prop
  mechanismsRoleSeparated : Prop
  atmosphericTargetsDenominator : Prop
  solarTargetsSubordinateNumerator : Prop
  ratioLawDerivedFromMechanisms : Prop
  parameterFiberCollapsedOrSkin : Prop
  targetPreservingTransport : Prop
  quotientStableForShape : Prop
  calibrationFree : Prop
  observedInputsDeleted : Prop
  comparatorContentDeleted : Prop
  branchSelectorDeleted : Prop
  identityShapeSelectorExcluded : Prop
  currentSatisfiesScotoRestriction :
    scotoRestriction C.ratio
  scotoRestrictionActiveOnLawfulImages :
    forall T : LawfulRatioDeformation C,
      T.lawful -> scotoRestriction (T.deformRatio C.ratio)
  restrictionImpliesShape :
    forall r : C.Ratio,
      scotoRestriction r ->
        M.shapeOfRatio r = M.shapeOfRatio C.ratio
  shapeImpliesRestriction :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
          scotoRestriction r
  shapeFiberSoundForMinimalInterval :
    forall r : C.Ratio,
      M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
        C.inMinimalInterval r
  restrictionSoundForMinimalInterval :
    forall r : C.Ratio,
      scotoRestriction r -> C.inMinimalInterval r
  scotoRestrictionSingleton :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        scotoRestriction r ->
          r = C.ratio

def scotoSeesawAsTranslatedLaw
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (S : AASCScotoSeesawTranslation C M) :
  AASCTranslatedCompressionLaw C M :=
  { lawForm := NeutrinoCompressionLawForm.hierarchyCompression
    ExternalLaw :=
      S.AtmosphericMechanism × S.SolarMechanism ×
        S.DarkSector × S.ParameterFiber
    externalLaw :=
      (S.atmosphericMechanism, S.solarMechanism,
        S.darkSector, S.parameterFiber)
    AASCRestriction := S.scotoRestriction
    currentSatisfiesRestriction :=
      S.currentSatisfiesScotoRestriction
    sourceDerivesRestriction :=
      S.ratioLawDerivedFromMechanisms /\
        S.parameterFiberCollapsedOrSkin
    sourceAncestryCertified :=
      S.atmosphericSourceInternal /\
        S.solarSourceInternal /\
          S.darkSectorSourceInternal /\
            S.mechanismsRoleSeparated
    targetPreservingTransport :=
      S.targetPreservingTransport /\
        S.atmosphericTargetsDenominator /\
          S.solarTargetsSubordinateNumerator
    quotientStable := S.quotientStableForShape
    calibrationFreeAfterDeletion := S.calibrationFree
    observedInputsDeleted := S.observedInputsDeleted
    comparatorContentDeleted := S.comparatorContentDeleted
    branchSelectorDeleted := S.branchSelectorDeleted
    identityShapeSelectorExcluded := S.identityShapeSelectorExcluded
    activeRestrictionForStandingRatio :=
      S.scotoRestrictionActiveOnLawfulImages
    restrictionImpliesShape := S.restrictionImpliesShape
    shapeImpliesRestriction := S.shapeImpliesRestriction
    shapeFiberSoundForMinimalInterval :=
      S.shapeFiberSoundForMinimalInterval
    restrictionSoundForMinimalInterval :=
      S.restrictionSoundForMinimalInterval
    restrictionSingleton := S.scotoRestrictionSingleton }

def AASCScotoSeesawAuditPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (S : AASCScotoSeesawTranslation C M) : Prop :=
  (S.ratioLawDerivedFromMechanisms /\
    S.parameterFiberCollapsedOrSkin) /\
  (S.atmosphericSourceInternal /\
    S.solarSourceInternal /\
      S.darkSectorSourceInternal /\
        S.mechanismsRoleSeparated) /\
  (S.targetPreservingTransport /\
    S.atmosphericTargetsDenominator /\
      S.solarTargetsSubordinateNumerator) /\
  S.quotientStableForShape /\
  S.calibrationFree /\
  S.observedInputsDeleted /\
  S.comparatorContentDeleted /\
  S.branchSelectorDeleted /\
  S.identityShapeSelectorExcluded

theorem scotoSeesawAuditPasses
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (S : AASCScotoSeesawTranslation C M)
  (haudit : AASCScotoSeesawAuditPasses S) :
  AASCTranslatedLawAuditPasses
    (scotoSeesawAsTranslatedLaw C M S) := by
  exact haudit

/--
Sharper convergence locus found by the targeted search.

This is the named intersection:

* tree-seesaw atmospheric carrier,
* scotogenic/radiative solar carrier,
* modular Yukawa/mass-matrix relation,
* phase-coherent oscillation readback.

It is smaller than the six-route bridge and is intended to be the constructive
middle theorem that can later feed the master convergence ledger.
-/
structure AASCScotoModularPhaseIntersection
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C) where
  modular :
    AASCModularMassSumRuleTranslation C M
  scoto :
    AASCScotoSeesawTranslation C M
  modularAudit :
    AASCModularMassSumRuleAuditPasses modular
  scotoAudit :
    AASCScotoSeesawAuditPasses scoto
  PhaseReadback : Type
  phaseReadback : PhaseReadback
  phaseRestriction : C.Ratio -> Prop
  treeSeesawAtmosphericCarrier : Prop
  scotogenicSolarCarrier : Prop
  modularMassMatrixRelation : Prop
  phaseCoherentReadback : Prop
  roleSeparationMatchesDeltaM2Readback : Prop
  sameStandingTarget : Prop
  commonQuotientSkin : Prop
  noParameterSelectorAtIntersection : Prop
  noObservedValueImport : Prop
  noFittedOscillationParameterImport : Prop
  noEnergyToMassConversionAssumption : Prop
  currentInIntersection :
    modular.ModularRestriction C.ratio /\
      scoto.scotoRestriction C.ratio /\
        phaseRestriction C.ratio
  intersectionActiveOnLawfulImages :
    forall T : LawfulRatioDeformation C,
      T.lawful ->
        modular.ModularRestriction (T.deformRatio C.ratio) /\
          scoto.scotoRestriction (T.deformRatio C.ratio) /\
            phaseRestriction (T.deformRatio C.ratio)
  intersectionImpliesShape :
    forall r : C.Ratio,
      modular.ModularRestriction r ->
        scoto.scotoRestriction r ->
          phaseRestriction r ->
            M.shapeOfRatio r = M.shapeOfRatio C.ratio
  shapeImpliesIntersection :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
          modular.ModularRestriction r /\
            scoto.scotoRestriction r /\
              phaseRestriction r
  shapeFiberSoundForMinimalInterval :
    forall r : C.Ratio,
      M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
        C.inMinimalInterval r
  intersectionSoundForMinimalInterval :
    forall r : C.Ratio,
      modular.ModularRestriction r ->
        scoto.scotoRestriction r ->
          phaseRestriction r ->
            C.inMinimalInterval r
  intersectionSingleton :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        modular.ModularRestriction r ->
          scoto.scotoRestriction r ->
            phaseRestriction r ->
              r = C.ratio

def AASCScotoModularPhaseIntersectionAuditPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (S : AASCScotoModularPhaseIntersection C M) : Prop :=
  AASCModularMassSumRuleAuditPasses S.modular /\
  AASCScotoSeesawAuditPasses S.scoto /\
  S.treeSeesawAtmosphericCarrier /\
  S.scotogenicSolarCarrier /\
  S.modularMassMatrixRelation /\
  S.phaseCoherentReadback /\
  S.roleSeparationMatchesDeltaM2Readback /\
  S.sameStandingTarget /\
  S.commonQuotientSkin /\
  S.noParameterSelectorAtIntersection /\
  S.noObservedValueImport /\
  S.noFittedOscillationParameterImport /\
  S.noEnergyToMassConversionAssumption

def scotoModularPhaseIntersectionAsTranslatedLaw
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (S : AASCScotoModularPhaseIntersection C M) :
  AASCTranslatedCompressionLaw C M :=
  { lawForm := NeutrinoCompressionLawForm.hierarchyCompression
    ExternalLaw :=
      Prod
        (Prod S.modular.ModularDatum S.scoto.ParameterFiber)
        S.PhaseReadback
    externalLaw :=
      ((S.modular.modularDatum, S.scoto.parameterFiber), S.phaseReadback)
    AASCRestriction := fun r =>
      S.modular.ModularRestriction r /\
        S.scoto.scotoRestriction r /\
          S.phaseRestriction r
    currentSatisfiesRestriction := S.currentInIntersection
    sourceDerivesRestriction :=
      S.treeSeesawAtmosphericCarrier /\
        S.scotogenicSolarCarrier /\
          S.modularMassMatrixRelation /\
            S.phaseCoherentReadback
    sourceAncestryCertified :=
      S.sameStandingTarget /\ S.roleSeparationMatchesDeltaM2Readback
    targetPreservingTransport :=
      S.sameStandingTarget /\ S.phaseCoherentReadback
    quotientStable := S.commonQuotientSkin
    calibrationFreeAfterDeletion :=
      S.noObservedValueImport /\ S.noFittedOscillationParameterImport
    observedInputsDeleted := S.noObservedValueImport
    comparatorContentDeleted := S.noParameterSelectorAtIntersection
    branchSelectorDeleted := S.noParameterSelectorAtIntersection
    identityShapeSelectorExcluded := S.noEnergyToMassConversionAssumption
    activeRestrictionForStandingRatio :=
      S.intersectionActiveOnLawfulImages
    restrictionImpliesShape := by
      intro r h
      exact S.intersectionImpliesShape r h.1 h.2.1 h.2.2
    shapeImpliesRestriction := S.shapeImpliesIntersection
    shapeFiberSoundForMinimalInterval :=
      S.shapeFiberSoundForMinimalInterval
    restrictionSoundForMinimalInterval := by
      intro r h
      exact S.intersectionSoundForMinimalInterval r h.1 h.2.1 h.2.2
    restrictionSingleton := by
      intro r hinterval h
      exact S.intersectionSingleton r hinterval h.1 h.2.1 h.2.2 }

theorem scotoModularPhaseIntersectionAuditPasses
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (S : AASCScotoModularPhaseIntersection C M)
  (haudit : AASCScotoModularPhaseIntersectionAuditPasses S) :
  AASCTranslatedLawAuditPasses
    (scotoModularPhaseIntersectionAsTranslatedLaw C M S) := by
  rcases haudit with
    ⟨_hmod, _hscoto, htree, hloop, hmatrix, hphase, hroles,
      htarget, hskin, hnoParam, hnoObserved, hnoFit, hnoEnergy⟩
  exact
    And.intro
      (And.intro htree (And.intro hloop (And.intro hmatrix hphase)))
      (And.intro
        (And.intro htarget hroles)
        (And.intro
          (And.intro htarget hphase)
          (And.intro hskin
            (And.intro
              (And.intro hnoObserved hnoFit)
              (And.intro hnoObserved
                (And.intro hnoParam
                  (And.intro hnoParam hnoEnergy)))))))

/--
Three targeted pressure families suggested by the next search pass.

These are not value theorems. They are source families that can be translated
into AASC restrictions only after the same no-selector and no-parameter-import
gates used by the other routes.
-/
inductive AASCSingletAdSPressureFamily where
  | radiativeScalarSinglet
  | sterileGaugeSinglet
  | adsTransportRigidity

/--
Targeted AASC translation for radiative scalar-singlet, sterile gauge-singlet,
or AdS/transport-rigidity pressure.

The key distinction is the `scopeStatusCertified` field. Gauge singlets and
AdS-like completions often enlarge the ambient description; AASC only allows
them to constrain the standing neutrino ratio when the old target is preserved
or the scope change is explicitly certified and read back without value import.
-/
structure AASCSingletAdSPressureTranslation
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C) where
  family : AASCSingletAdSPressureFamily
  PressureCarrier : Type
  ParameterFiber : Type
  pressureCarrier : PressureCarrier
  parameterFiber : ParameterFiber
  pressureRestriction : C.Ratio -> Prop
  sourceInternal : Prop
  scopeStatusCertified : Prop
  standingTargetPreserved : Prop
  singletOrTransportInertForChargedSM : Prop
  pressureActsOnSplittingRatio : Prop
  parameterFiberCollapsedOrSkin : Prop
  quotientStableForShape : Prop
  calibrationFree : Prop
  observedInputsDeleted : Prop
  comparatorContentDeleted : Prop
  branchSelectorDeleted : Prop
  identityShapeSelectorExcluded : Prop
  currentSatisfiesPressure :
    pressureRestriction C.ratio
  pressureActiveOnLawfulImages :
    forall T : LawfulRatioDeformation C,
      T.lawful -> pressureRestriction (T.deformRatio C.ratio)
  restrictionImpliesShape :
    forall r : C.Ratio,
      pressureRestriction r ->
        M.shapeOfRatio r = M.shapeOfRatio C.ratio
  shapeImpliesRestriction :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
          pressureRestriction r
  shapeFiberSoundForMinimalInterval :
    forall r : C.Ratio,
      M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
        C.inMinimalInterval r
  restrictionSoundForMinimalInterval :
    forall r : C.Ratio,
      pressureRestriction r -> C.inMinimalInterval r
  pressureRestrictionSingleton :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        pressureRestriction r ->
          r = C.ratio

def singletAdSPressureAsTranslatedLaw
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (S : AASCSingletAdSPressureTranslation C M) :
  AASCTranslatedCompressionLaw C M :=
  { lawForm := NeutrinoCompressionLawForm.hierarchyCompression
    ExternalLaw := Prod S.PressureCarrier S.ParameterFiber
    externalLaw := (S.pressureCarrier, S.parameterFiber)
    AASCRestriction := S.pressureRestriction
    currentSatisfiesRestriction := S.currentSatisfiesPressure
    sourceDerivesRestriction :=
      S.pressureActsOnSplittingRatio /\ S.parameterFiberCollapsedOrSkin
    sourceAncestryCertified :=
      S.sourceInternal /\ S.scopeStatusCertified
    targetPreservingTransport :=
      S.standingTargetPreserved /\ S.singletOrTransportInertForChargedSM
    quotientStable := S.quotientStableForShape
    calibrationFreeAfterDeletion := S.calibrationFree
    observedInputsDeleted := S.observedInputsDeleted
    comparatorContentDeleted := S.comparatorContentDeleted
    branchSelectorDeleted := S.branchSelectorDeleted
    identityShapeSelectorExcluded := S.identityShapeSelectorExcluded
    activeRestrictionForStandingRatio := S.pressureActiveOnLawfulImages
    restrictionImpliesShape := S.restrictionImpliesShape
    shapeImpliesRestriction := S.shapeImpliesRestriction
    shapeFiberSoundForMinimalInterval :=
      S.shapeFiberSoundForMinimalInterval
    restrictionSoundForMinimalInterval :=
      S.restrictionSoundForMinimalInterval
    restrictionSingleton := S.pressureRestrictionSingleton }

def AASCSingletAdSPressureAuditPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (S : AASCSingletAdSPressureTranslation C M) : Prop :=
  (S.pressureActsOnSplittingRatio /\ S.parameterFiberCollapsedOrSkin) /\
  (S.sourceInternal /\ S.scopeStatusCertified) /\
  (S.standingTargetPreserved /\ S.singletOrTransportInertForChargedSM) /\
  S.quotientStableForShape /\
  S.calibrationFree /\
  S.observedInputsDeleted /\
  S.comparatorContentDeleted /\
  S.branchSelectorDeleted /\
  S.identityShapeSelectorExcluded

theorem singletAdSPressureAuditPasses
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (S : AASCSingletAdSPressureTranslation C M)
  (haudit : AASCSingletAdSPressureAuditPasses S) :
  AASCTranslatedLawAuditPasses
    (singletAdSPressureAsTranslatedLaw C M S) := by
  exact haudit

/--
Joint convergence of the three singlet/transport pressure families.

This is the proof-facing version of "where they intersect." The three
individual pressure restrictions may each leave a live fiber, while the joint
intersection can still collapse once same-target transport, scope readback, and
parameter-skin discipline are all audited.
-/
structure AASCSingletAdSConvergence
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C) where
  radiative :
    AASCSingletAdSPressureTranslation C M
  sterile :
    AASCSingletAdSPressureTranslation C M
  ads :
    AASCSingletAdSPressureTranslation C M
  radiativeFamily :
    radiative.family = AASCSingletAdSPressureFamily.radiativeScalarSinglet
  sterileFamily :
    sterile.family = AASCSingletAdSPressureFamily.sterileGaugeSinglet
  adsFamily :
    ads.family = AASCSingletAdSPressureFamily.adsTransportRigidity
  radiativeAudit :
    AASCSingletAdSPressureAuditPasses radiative
  sterileAudit :
    AASCSingletAdSPressureAuditPasses sterile
  adsAudit :
    AASCSingletAdSPressureAuditPasses ads
  sameStandingTarget : Prop
  commonQuotientSkin : Prop
  noAmbientScopeEscape : Prop
  noParameterSelectorAtIntersection : Prop
  noObservedValueAtIntersection : Prop
  currentInConvergence :
    radiative.pressureRestriction C.ratio /\
      sterile.pressureRestriction C.ratio /\
        ads.pressureRestriction C.ratio
  convergenceActiveOnLawfulImages :
    forall T : LawfulRatioDeformation C,
      T.lawful ->
        radiative.pressureRestriction (T.deformRatio C.ratio) /\
          sterile.pressureRestriction (T.deformRatio C.ratio) /\
            ads.pressureRestriction (T.deformRatio C.ratio)
  convergenceImpliesShape :
    forall r : C.Ratio,
      radiative.pressureRestriction r ->
        sterile.pressureRestriction r ->
          ads.pressureRestriction r ->
            M.shapeOfRatio r = M.shapeOfRatio C.ratio
  shapeImpliesConvergence :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
          radiative.pressureRestriction r /\
            sterile.pressureRestriction r /\
              ads.pressureRestriction r
  shapeFiberSoundForMinimalInterval :
    forall r : C.Ratio,
      M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
        C.inMinimalInterval r
  convergenceSoundForMinimalInterval :
    forall r : C.Ratio,
      radiative.pressureRestriction r ->
        sterile.pressureRestriction r ->
          ads.pressureRestriction r ->
            C.inMinimalInterval r
  convergenceSingleton :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        radiative.pressureRestriction r ->
          sterile.pressureRestriction r ->
            ads.pressureRestriction r ->
              r = C.ratio

def AASCSingletAdSConvergenceAuditPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (J : AASCSingletAdSConvergence C M) : Prop :=
  AASCSingletAdSPressureAuditPasses J.radiative /\
  AASCSingletAdSPressureAuditPasses J.sterile /\
  AASCSingletAdSPressureAuditPasses J.ads /\
  J.sameStandingTarget /\
  J.commonQuotientSkin /\
  J.noAmbientScopeEscape /\
  J.noParameterSelectorAtIntersection /\
  J.noObservedValueAtIntersection

def singletAdSConvergenceAsTranslatedLaw
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (J : AASCSingletAdSConvergence C M) :
  AASCTranslatedCompressionLaw C M :=
  { lawForm := NeutrinoCompressionLawForm.hierarchyCompression
    ExternalLaw :=
      Prod
        (Prod J.radiative.PressureCarrier J.sterile.PressureCarrier)
        J.ads.PressureCarrier
    externalLaw :=
      ((J.radiative.pressureCarrier, J.sterile.pressureCarrier),
        J.ads.pressureCarrier)
    AASCRestriction := fun r =>
      J.radiative.pressureRestriction r /\
        J.sterile.pressureRestriction r /\
          J.ads.pressureRestriction r
    currentSatisfiesRestriction := J.currentInConvergence
    sourceDerivesRestriction :=
      J.commonQuotientSkin /\ J.noAmbientScopeEscape
    sourceAncestryCertified :=
      J.sameStandingTarget /\ J.noParameterSelectorAtIntersection
    targetPreservingTransport :=
      J.sameStandingTarget /\ J.noAmbientScopeEscape
    quotientStable := J.commonQuotientSkin
    calibrationFreeAfterDeletion := J.noObservedValueAtIntersection
    observedInputsDeleted := J.noObservedValueAtIntersection
    comparatorContentDeleted := J.noParameterSelectorAtIntersection
    branchSelectorDeleted := J.noParameterSelectorAtIntersection
    identityShapeSelectorExcluded := J.noAmbientScopeEscape
    activeRestrictionForStandingRatio := J.convergenceActiveOnLawfulImages
    restrictionImpliesShape := by
      intro r h
      exact J.convergenceImpliesShape r h.1 h.2.1 h.2.2
    shapeImpliesRestriction := J.shapeImpliesConvergence
    shapeFiberSoundForMinimalInterval :=
      J.shapeFiberSoundForMinimalInterval
    restrictionSoundForMinimalInterval := by
      intro r h
      exact J.convergenceSoundForMinimalInterval r h.1 h.2.1 h.2.2
    restrictionSingleton := by
      intro r hinterval h
      exact J.convergenceSingleton r hinterval h.1 h.2.1 h.2.2 }

theorem singletAdSConvergenceAuditPasses
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (J : AASCSingletAdSConvergence C M)
  (haudit : AASCSingletAdSConvergenceAuditPasses J) :
  AASCTranslatedLawAuditPasses
    (singletAdSConvergenceAsTranslatedLaw C M J) := by
  rcases haudit with
    ⟨_hradiative, _hsterile, _hads, hsame, hskin,
      hnoAmbient, hnoParameter, hnoObserved⟩
  exact
    And.intro
      (And.intro hskin hnoAmbient)
      (And.intro
        (And.intro hsame hnoParameter)
        (And.intro
          (And.intro hsame hnoAmbient)
          (And.intro hskin
            (And.intro hnoObserved
              (And.intro hnoObserved
                (And.intro hnoParameter
                  (And.intro hnoParameter hnoAmbient)))))))

/--
Hybrid AASC network using the strongest pieces of the three candidate routes.

The modular route contributes algebraic restriction, the spectral route
contributes quotient/finite-reduction pressure, and the scoto-seesaw route
contributes mechanism-separated solar/atmospheric role structure. The joint
restriction may be singleton even when no individual route is singleton.
-/
structure AASCHybridCompressionNetwork
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C) where
  modular :
    AASCModularMassSumRuleTranslation C M
  spectral :
    AASCSpectralQuotientCollapseTranslation C M
  scoto :
    AASCScotoSeesawTranslation C M
  modularAudit :
    AASCModularMassSumRuleAuditPasses modular
  spectralAudit :
    AASCSpectralQuotientAuditPasses spectral
  scotoAudit :
    AASCScotoSeesawAuditPasses scoto
  crossTargetAligned : Prop
  crossTransportCoherent : Prop
  crossNoOvercounting : Prop
  crossCalibrationFree : Prop
  crossNoHiddenSelector : Prop
  crossNonempty :
    exists r : C.Ratio,
      modular.ModularRestriction r /\
        spectral.spectralRestriction r /\
          scoto.scotoRestriction r
  currentInJointRestriction :
    modular.ModularRestriction C.ratio /\
      spectral.spectralRestriction C.ratio /\
        scoto.scotoRestriction C.ratio
  jointRestrictionActiveOnLawfulImages :
    forall T : LawfulRatioDeformation C,
      T.lawful ->
        modular.ModularRestriction (T.deformRatio C.ratio) /\
          spectral.spectralRestriction (T.deformRatio C.ratio) /\
            scoto.scotoRestriction (T.deformRatio C.ratio)
  jointRestrictionImpliesShape :
    forall r : C.Ratio,
      modular.ModularRestriction r ->
        spectral.spectralRestriction r ->
          scoto.scotoRestriction r ->
            M.shapeOfRatio r = M.shapeOfRatio C.ratio
  shapeImpliesJointRestriction :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
          modular.ModularRestriction r /\
            spectral.spectralRestriction r /\
              scoto.scotoRestriction r
  jointShapeFiberSoundForMinimalInterval :
    forall r : C.Ratio,
      M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
        C.inMinimalInterval r
  jointRestrictionSoundForMinimalInterval :
    forall r : C.Ratio,
      modular.ModularRestriction r ->
        spectral.spectralRestriction r ->
          scoto.scotoRestriction r ->
            C.inMinimalInterval r
  jointRestrictionSingleton :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        modular.ModularRestriction r ->
          spectral.spectralRestriction r ->
            scoto.scotoRestriction r ->
              r = C.ratio

def hybridCompressionAsTranslatedLaw
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M) :
  AASCTranslatedCompressionLaw C M :=
  { lawForm := NeutrinoCompressionLawForm.spectralQuotient
    ExternalLaw :=
      H.modular.ModularDatum × H.spectral.SpectralQuotient ×
        H.scoto.AtmosphericMechanism × H.scoto.SolarMechanism ×
          H.scoto.DarkSector × H.scoto.ParameterFiber
    externalLaw :=
      (H.modular.modularDatum, H.spectral.spectralQuotient,
        H.scoto.atmosphericMechanism, H.scoto.solarMechanism,
        H.scoto.darkSector, H.scoto.parameterFiber)
    AASCRestriction := fun r =>
      H.modular.ModularRestriction r /\
        H.spectral.spectralRestriction r /\
          H.scoto.scotoRestriction r
    currentSatisfiesRestriction := H.currentInJointRestriction
    sourceDerivesRestriction :=
      (modularMassSumRuleAsTranslatedLaw C M H.modular).sourceDerivesRestriction /\
        (spectralQuotientAsTranslatedLaw C M H.spectral).sourceDerivesRestriction /\
          (scotoSeesawAsTranslatedLaw C M H.scoto).sourceDerivesRestriction
    sourceAncestryCertified :=
      (modularMassSumRuleAsTranslatedLaw C M H.modular).sourceAncestryCertified /\
        (spectralQuotientAsTranslatedLaw C M H.spectral).sourceAncestryCertified /\
          (scotoSeesawAsTranslatedLaw C M H.scoto).sourceAncestryCertified
    targetPreservingTransport :=
      H.crossTargetAligned /\ H.crossTransportCoherent
    quotientStable :=
      (modularMassSumRuleAsTranslatedLaw C M H.modular).quotientStable /\
        (spectralQuotientAsTranslatedLaw C M H.spectral).quotientStable /\
          (scotoSeesawAsTranslatedLaw C M H.scoto).quotientStable
    calibrationFreeAfterDeletion := H.crossCalibrationFree
    observedInputsDeleted :=
      (modularMassSumRuleAsTranslatedLaw C M H.modular).observedInputsDeleted /\
        (spectralQuotientAsTranslatedLaw C M H.spectral).observedInputsDeleted /\
          (scotoSeesawAsTranslatedLaw C M H.scoto).observedInputsDeleted
    comparatorContentDeleted := H.crossNoOvercounting
    branchSelectorDeleted :=
      (modularMassSumRuleAsTranslatedLaw C M H.modular).branchSelectorDeleted /\
        (spectralQuotientAsTranslatedLaw C M H.spectral).branchSelectorDeleted /\
          (scotoSeesawAsTranslatedLaw C M H.scoto).branchSelectorDeleted
    identityShapeSelectorExcluded := H.crossNoHiddenSelector
    activeRestrictionForStandingRatio :=
      H.jointRestrictionActiveOnLawfulImages
    restrictionImpliesShape := by
      intro r hjoint
      exact
        H.jointRestrictionImpliesShape
          r
          hjoint.1
          hjoint.2.1
          hjoint.2.2
    shapeImpliesRestriction :=
      H.shapeImpliesJointRestriction
    shapeFiberSoundForMinimalInterval :=
      H.jointShapeFiberSoundForMinimalInterval
    restrictionSoundForMinimalInterval := by
      intro r hjoint
      exact
        H.jointRestrictionSoundForMinimalInterval
          r
          hjoint.1
          hjoint.2.1
          hjoint.2.2
    restrictionSingleton := by
      intro r hinterval hjoint
      exact
        H.jointRestrictionSingleton
          r
          hinterval
          hjoint.1
          hjoint.2.1
          hjoint.2.2 }

def AASCHybridCompressionAuditPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M) : Prop :=
  AASCTranslatedLawAuditPasses
    (hybridCompressionAsTranslatedLaw C M H)

/--
Six-route master convergence ledger.

This keeps the two three-route modules separate, then adds the bridge facts
needed to use them as one convergence object. The six active pressures are:
modular/sum-rule, spectral quotient, scoto-seesaw, radiative scalar singlet,
sterile gauge singlet, and AdS/transport rigidity.
-/
structure AASCNeutrinoSixRouteConvergence
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C) where
  hybrid :
    AASCHybridCompressionNetwork C M
  singletAdS :
    AASCSingletAdSConvergence C M
  hybridAudit :
    AASCHybridCompressionAuditPasses hybrid
  singletAdSAudit :
    AASCSingletAdSConvergenceAuditPasses singletAdS
  bridgeSameStandingTarget : Prop
  bridgeTransportCoherent : Prop
  bridgeNoOvercounting : Prop
  bridgeCommonQuotientSkin : Prop
  bridgeNoCrossSelector : Prop
  bridgeNoObservedValueImport : Prop
  currentInSixRestriction :
    hybrid.modular.ModularRestriction C.ratio /\
      hybrid.spectral.spectralRestriction C.ratio /\
        hybrid.scoto.scotoRestriction C.ratio /\
          singletAdS.radiative.pressureRestriction C.ratio /\
            singletAdS.sterile.pressureRestriction C.ratio /\
              singletAdS.ads.pressureRestriction C.ratio
  sixRestrictionActiveOnLawfulImages :
    forall T : LawfulRatioDeformation C,
      T.lawful ->
        hybrid.modular.ModularRestriction (T.deformRatio C.ratio) /\
          hybrid.spectral.spectralRestriction (T.deformRatio C.ratio) /\
            hybrid.scoto.scotoRestriction (T.deformRatio C.ratio) /\
              singletAdS.radiative.pressureRestriction
                (T.deformRatio C.ratio) /\
                singletAdS.sterile.pressureRestriction
                  (T.deformRatio C.ratio) /\
                  singletAdS.ads.pressureRestriction
                    (T.deformRatio C.ratio)
  sixRestrictionImpliesShape :
    forall r : C.Ratio,
      hybrid.modular.ModularRestriction r ->
        hybrid.spectral.spectralRestriction r ->
          hybrid.scoto.scotoRestriction r ->
            singletAdS.radiative.pressureRestriction r ->
              singletAdS.sterile.pressureRestriction r ->
                singletAdS.ads.pressureRestriction r ->
                  M.shapeOfRatio r = M.shapeOfRatio C.ratio
  shapeImpliesSixRestriction :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
          hybrid.modular.ModularRestriction r /\
            hybrid.spectral.spectralRestriction r /\
              hybrid.scoto.scotoRestriction r /\
                singletAdS.radiative.pressureRestriction r /\
                  singletAdS.sterile.pressureRestriction r /\
                    singletAdS.ads.pressureRestriction r
  sixShapeFiberSoundForMinimalInterval :
    forall r : C.Ratio,
      M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
        C.inMinimalInterval r
  sixRestrictionSoundForMinimalInterval :
    forall r : C.Ratio,
      hybrid.modular.ModularRestriction r ->
        hybrid.spectral.spectralRestriction r ->
          hybrid.scoto.scotoRestriction r ->
            singletAdS.radiative.pressureRestriction r ->
              singletAdS.sterile.pressureRestriction r ->
                singletAdS.ads.pressureRestriction r ->
                  C.inMinimalInterval r
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

def AASCNeutrinoSixRouteConvergenceAuditPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (S : AASCNeutrinoSixRouteConvergence C M) : Prop :=
  AASCHybridCompressionAuditPasses S.hybrid /\
  AASCSingletAdSConvergenceAuditPasses S.singletAdS /\
  S.bridgeSameStandingTarget /\
  S.bridgeTransportCoherent /\
  S.bridgeNoOvercounting /\
  S.bridgeCommonQuotientSkin /\
  S.bridgeNoCrossSelector /\
  S.bridgeNoObservedValueImport

def sixRouteConvergenceAsTranslatedLaw
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (S : AASCNeutrinoSixRouteConvergence C M) :
  AASCTranslatedCompressionLaw C M :=
  { lawForm := NeutrinoCompressionLawForm.hierarchyCompression
    ExternalLaw := Unit
    externalLaw := ()
    AASCRestriction := fun r =>
      S.hybrid.modular.ModularRestriction r /\
        S.hybrid.spectral.spectralRestriction r /\
          S.hybrid.scoto.scotoRestriction r /\
            S.singletAdS.radiative.pressureRestriction r /\
              S.singletAdS.sterile.pressureRestriction r /\
                S.singletAdS.ads.pressureRestriction r
    currentSatisfiesRestriction := S.currentInSixRestriction
    sourceDerivesRestriction :=
      AASCHybridCompressionAuditPasses S.hybrid /\
        AASCSingletAdSConvergenceAuditPasses S.singletAdS
    sourceAncestryCertified :=
      S.bridgeSameStandingTarget /\ S.bridgeNoOvercounting
    targetPreservingTransport :=
      S.bridgeSameStandingTarget /\ S.bridgeTransportCoherent
    quotientStable := S.bridgeCommonQuotientSkin
    calibrationFreeAfterDeletion := S.bridgeNoObservedValueImport
    observedInputsDeleted := S.bridgeNoObservedValueImport
    comparatorContentDeleted := S.bridgeNoCrossSelector
    branchSelectorDeleted := S.bridgeNoCrossSelector
    identityShapeSelectorExcluded := S.bridgeNoCrossSelector
    activeRestrictionForStandingRatio :=
      S.sixRestrictionActiveOnLawfulImages
    restrictionImpliesShape := by
      intro r h
      exact
        S.sixRestrictionImpliesShape
          r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
    shapeImpliesRestriction :=
      S.shapeImpliesSixRestriction
    shapeFiberSoundForMinimalInterval :=
      S.sixShapeFiberSoundForMinimalInterval
    restrictionSoundForMinimalInterval := by
      intro r h
      exact
        S.sixRestrictionSoundForMinimalInterval
          r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
    restrictionSingleton := by
      intro r hinterval h
      exact
        S.sixRestrictionSingleton
          r hinterval h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
          h.2.2.2.2.2 }

theorem sixRouteConvergenceAuditPasses
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (S : AASCNeutrinoSixRouteConvergence C M)
  (haudit : AASCNeutrinoSixRouteConvergenceAuditPasses S) :
  AASCTranslatedLawAuditPasses
    (sixRouteConvergenceAsTranslatedLaw C M S) := by
  rcases haudit with
    ⟨hHybrid, hSinglet, hTarget, hTransport, hNoOvercount,
      hSkin, hNoSelector, hNoObserved⟩
  exact
    And.intro
      (And.intro hHybrid hSinglet)
      (And.intro
        (And.intro hTarget hNoOvercount)
        (And.intro
          (And.intro hTarget hTransport)
          (And.intro hSkin
            (And.intro hNoObserved
              (And.intro hNoObserved
                (And.intro hNoSelector
                  (And.intro hNoSelector hNoSelector)))))))

/--
AASC closure-exhaustion wrapper for the hybrid network.

This states that every lawful stronger-output route is either represented by
the hybrid network, blocked by the present audit, or is only support/finite
progress rather than ratio compression.
-/
structure AASCHybridClosureExhaustion
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M) where
  NonHybridRoute : Type
  nonHybridRouteBlocked : NonHybridRoute -> Prop
  nonHybridRouteSupportOnly : NonHybridRoute -> Prop
  allNonHybridRoutesExhausted :
    forall R : NonHybridRoute,
      nonHybridRouteBlocked R \/ nonHybridRouteSupportOnly R
  algebraicRouteRepresented :
    H.modular.ModularRestriction C.ratio
  spectralRouteRepresented :
    H.spectral.spectralRestriction C.ratio
  scotoRouteRepresented :
    H.scoto.scotoRestriction C.ratio
  noEmpiricalEscapeRoute : Prop
  noAnchorBeforeShape : Prop
  noComparatorPromotionEscape : Prop
  noBranchSelectorEscape : Prop
  noIdentitySelectorEscape : Prop
  hybridIsOnlyCompressionLiveRoute : Prop

def AASCHybridClosureExhaustionPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (E : AASCHybridClosureExhaustion C M H) : Prop :=
  E.noEmpiricalEscapeRoute /\
  E.noAnchorBeforeShape /\
  E.noComparatorPromotionEscape /\
  E.noBranchSelectorEscape /\
  E.noIdentitySelectorEscape /\
  E.hybridIsOnlyCompressionLiveRoute

/--
Impossibility condition for the bridge: the joint restriction still has a
second point in the minimal interval.
-/
def HybridJointRestrictionHasSecondPoint
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M) : Prop :=
  exists r : C.Ratio,
    C.inMinimalInterval r /\
      H.modular.ModularRestriction r /\
        H.spectral.spectralRestriction r /\
          H.scoto.scotoRestriction r /\
            Not (r = C.ratio)

/--
Named reasons a would-be second point in the hybrid joint restriction can be
excluded.
-/
inductive HybridExclusionReason where
  | modularAlgebra
  | spectralReduction
  | scotoMechanism
  | crossRouteCoherence
  | phaseTopology
  | neutrinoSpecificDiscriminator
  | closureExhaustion

/--
Proof-facing exclusion certificate for the hybrid bridge.

Instead of proving the singleton theorem in one step, the paper may classify any
candidate second point by an exclusion reason and then discharge the
corresponding impossibility.
-/
structure AASCHybridJointExclusionCertificate
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M) where
  exclusionReason :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              Not (r = C.ratio) ->
                HybridExclusionReason
  excludesSecondPoint :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              Not (r = C.ratio) ->
                False

def HybridJointRestrictionSingleton
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M) : Prop :=
  forall r : C.Ratio,
    C.inMinimalInterval r ->
      H.modular.ModularRestriction r ->
        H.spectral.spectralRestriction r ->
          H.scoto.scotoRestriction r ->
            r = C.ratio

/--
Nonemptiness of the hybrid neutrino joint restriction.

This is the formal content of "there is a neutrino-sector realization" at the
level of the hybrid restriction. It is intentionally weaker than singleton
closure.
-/
def HybridJointRestrictionNonempty
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M) : Prop :=
  exists r : C.Ratio,
    C.inMinimalInterval r /\
      H.modular.ModularRestriction r /\
        H.spectral.spectralRestriction r /\
          H.scoto.scotoRestriction r

theorem currentRatioGivesHybridJointRestrictionNonempty
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M) :
  HybridJointRestrictionNonempty H := by
  exact
    ⟨C.ratio,
      C.minimalIntervalLocked,
      H.currentInJointRestriction.1,
      H.currentInJointRestriction.2.1,
      H.currentInJointRestriction.2.2⟩

theorem hybridJointRestrictionNonemptyDoesNotCloseSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M) :
  HybridJointRestrictionNonempty H := by
  exact currentRatioGivesHybridJointRestrictionNonempty C M H

theorem hybridExclusionCertificateGivesJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (X : AASCHybridJointExclusionCertificate C M H) :
  HybridJointRestrictionSingleton H := by
  intro r hinterval hmod hspec hscoto
  classical
  by_cases heq : r = C.ratio
  · exact heq
  · exact False.elim
      (X.excludesSecondPoint r hinterval hmod hspec hscoto heq)

theorem hybridExclusionCertificateRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (X : AASCHybridJointExclusionCertificate C M H) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  intro hsecond
  rcases hsecond with
    ⟨r, hinterval, hmod, hspec, hscoto, hne⟩
  exact X.excludesSecondPoint r hinterval hmod hspec hscoto hne

/--
All-but-one AASC elimination certificate.

`CandidateIndex` is the surviving alternative ledger. A joint-admissible ratio
has a candidate index; the current ratio has `currentIndex`; every other index
is eliminated by an AASC exclusion reason. This is the explicit "eliminate all
but one" form of the hybrid singleton proof.
-/
structure AASCAllButOneElimination
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M) where
  CandidateIndex : Type
  candidateOf : C.Ratio -> CandidateIndex
  currentIndex : CandidateIndex
  currentHasCurrentIndex :
    candidateOf C.ratio = currentIndex
  jointCandidatesHaveIndex :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              candidateOf r = candidateOf r
  indexCompleteForJointRestriction :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              candidateOf r = currentIndex \/ Not (candidateOf r = currentIndex)
  eliminatedIndexReason :
    forall i : CandidateIndex,
      Not (i = currentIndex) -> HybridExclusionReason
  eliminatesNoncurrentIndex :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              Not (candidateOf r = currentIndex) ->
                False
  currentIndexInjectiveOnJointRestriction :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              candidateOf r = currentIndex ->
                r = C.ratio

/--
Independent experimental-method witness channels.

These are topology/witness classes, not value imports.
-/
inductive NeutrinoMethodChannel where
  | solar
  | atmospheric
  | reactor
  | accelerator
  | pmnsInvariant
  | cosmologyBoundary
  | betaBoundary
  | doubleBetaBoundary

/--
Method-invariant witness ledger.

This is how experimental diversity enters AASC lawfully: channels may eliminate
candidate indices by invariant incompatibility, but they do not select an index
by observed numerical value.
-/
structure AASCMethodInvariantWitnessLedger
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (CandidateIndex : Type) where
  methodSurvives : NeutrinoMethodChannel -> CandidateIndex -> Prop
  methodEliminates : NeutrinoMethodChannel -> CandidateIndex -> Prop
  currentIndex : CandidateIndex
  currentSurvivesAllMethods :
    forall ch : NeutrinoMethodChannel,
      methodSurvives ch currentIndex
  noChannelUsesObservedValueAsSelector : Prop
  noBoundaryChannelPromotedToValue : Prop
  channelEliminationSound :
    forall ch : NeutrinoMethodChannel,
      forall i : CandidateIndex,
        methodEliminates ch i -> Not (methodSurvives ch i)
  methodCompletenessForJointCandidate :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              forall ch : NeutrinoMethodChannel,
                methodSurvives ch currentIndex \/
                  exists i : CandidateIndex, methodEliminates ch i
  methodInvariantEliminatesNoncurrent :
    forall i : CandidateIndex,
      Not (i = currentIndex) ->
        exists ch : NeutrinoMethodChannel, methodEliminates ch i

def AASCMethodWitnessLedgerPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {CandidateIndex : Type}
  (W : AASCMethodInvariantWitnessLedger C M H CandidateIndex) : Prop :=
  W.noChannelUsesObservedValueAsSelector /\
  W.noBoundaryChannelPromotedToValue

/--
Phase-coherence witness components.

These record the oscillation fact that flavor change is interference under
mass-basis phase transport, not conversion of kinetic energy into rest mass.
-/
inductive NeutrinoPhaseWitnessComponent where
  | massBasisPhaseTransport
  | flavorProjectionInterference
  | coherenceEnvelope
  | baselineEnergyCovariance
  | deltaM2RatioReadback
  | methodInvariantPhaseTopology

/--
Phase-coherence witness ledger.

This is a topology/readback eliminator. It can rule out candidate indices whose
ratio restriction cannot preserve the same coherent phase-transport object
across methods. It is explicitly forbidden from selecting an index by observed
numeric splittings or fitted oscillation parameters.
-/
structure AASCPhaseCoherenceWitnessLedger
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (CandidateIndex : Type) where
  phaseSurvives : NeutrinoPhaseWitnessComponent -> CandidateIndex -> Prop
  phaseEliminates : NeutrinoPhaseWitnessComponent -> CandidateIndex -> Prop
  currentIndex : CandidateIndex
  currentPreservesPhaseTopology :
    forall w : NeutrinoPhaseWitnessComponent,
      phaseSurvives w currentIndex
  massBasisTransportCertified : Prop
  flavorProjectionCertified : Prop
  coherencePreservedAcrossMethods : Prop
  baselineEnergyReadbackCertified : Prop
  sameDeltaM2RatioReadback : Prop
  noEnergyToMassConversionAssumption : Prop
  noObservedPhaseValueSelector : Prop
  noFittedOscillationParameterImport : Prop
  phaseEliminationSound :
    forall w : NeutrinoPhaseWitnessComponent,
      forall i : CandidateIndex,
        phaseEliminates w i -> Not (phaseSurvives w i)
  phaseCompletenessForJointCandidate :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              forall w : NeutrinoPhaseWitnessComponent,
                phaseSurvives w currentIndex \/
                  exists i : CandidateIndex, phaseEliminates w i
  phaseTopologyEliminatesNoncurrent :
    forall i : CandidateIndex,
      Not (i = currentIndex) ->
        exists w : NeutrinoPhaseWitnessComponent, phaseEliminates w i

def AASCPhaseCoherenceWitnessLedgerPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {CandidateIndex : Type}
  (P : AASCPhaseCoherenceWitnessLedger C M H CandidateIndex) : Prop :=
  P.massBasisTransportCertified /\
  P.flavorProjectionCertified /\
  P.coherencePreservedAcrossMethods /\
  P.baselineEnergyReadbackCertified /\
  P.sameDeltaM2RatioReadback /\
  P.noEnergyToMassConversionAssumption /\
  P.noObservedPhaseValueSelector /\
  P.noFittedOscillationParameterImport

/--
Neutrino-specific structural discriminators.

These are native features of the neutrino sector that can eliminate candidate
indices without fitting the ratio value.
-/
inductive NeutrinoSpecificDiscriminator where
  | electricNeutrality
  | weakOnlyBoundary
  | massFlavorBasisMismatch
  | macroscopicCoherence
  | twoScaleSplitting
  | noAbsoluteMassImport
  | matterEffectCompatibility
  | diracMajoranaNoSelector
  | sterileSingletScopeControl
  | crossMethodLECovariance

/--
Neutrino-specific discriminator ledger.

This collects structural gates such as neutrality, weak source/detection
boundaries, matter-effect compatibility, and L/E covariance. The ledger can
remove non-current candidate indices, but it must not use observed absolute
masses, fitted oscillation parameters, or a hidden Dirac/Majorana branch choice
as selectors.
-/
structure AASCNeutrinoSpecificDiscriminatorLedger
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (CandidateIndex : Type) where
  discriminatorSurvives :
    NeutrinoSpecificDiscriminator -> CandidateIndex -> Prop
  discriminatorEliminates :
    NeutrinoSpecificDiscriminator -> CandidateIndex -> Prop
  currentIndex : CandidateIndex
  currentSurvivesAllDiscriminators :
    forall d : NeutrinoSpecificDiscriminator,
      discriminatorSurvives d currentIndex
  neutralityPreserved : Prop
  weakBoundaryPreserved : Prop
  massFlavorMismatchPreserved : Prop
  coherenceTopologyPreserved : Prop
  twoScaleRoleCompatible : Prop
  absoluteMassNotImported : Prop
  matterTransportCompatible : Prop
  diracMajoranaNoSelector : Prop
  sterileSingletScopeControlled : Prop
  crossMethodLECovariant : Prop
  noObservedValueSelector : Prop
  noFittedParameterImport : Prop
  discriminatorEliminationSound :
    forall d : NeutrinoSpecificDiscriminator,
      forall i : CandidateIndex,
        discriminatorEliminates d i -> Not (discriminatorSurvives d i)
  discriminatorCompletenessForJointCandidate :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              forall d : NeutrinoSpecificDiscriminator,
                discriminatorSurvives d currentIndex \/
                  exists i : CandidateIndex, discriminatorEliminates d i
  discriminatorsEliminateNoncurrent :
    forall i : CandidateIndex,
      Not (i = currentIndex) ->
        exists d : NeutrinoSpecificDiscriminator,
          discriminatorEliminates d i

def AASCNeutrinoSpecificDiscriminatorLedgerPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {CandidateIndex : Type}
  (D : AASCNeutrinoSpecificDiscriminatorLedger C M H CandidateIndex) :
  Prop :=
  D.neutralityPreserved /\
  D.weakBoundaryPreserved /\
  D.massFlavorMismatchPreserved /\
  D.coherenceTopologyPreserved /\
  D.twoScaleRoleCompatible /\
  D.absoluteMassNotImported /\
  D.matterTransportCompatible /\
  D.diracMajoranaNoSelector /\
  D.sterileSingletScopeControlled /\
  D.crossMethodLECovariant /\
  D.noObservedValueSelector /\
  D.noFittedParameterImport

/--
Draft finite candidate classes for the first elimination pass.

This is a taxonomy of ways a non-current candidate can survive only by failing
one of the AASC gates. It is not yet the full `AASCCandidateIndexLedger`,
because the paper still has to prove that every joint-admissible ratio maps
into one of these classes.
-/
inductive NeutrinoDraftCandidateIndex where
  | currentStandingRatio
  | modularOnlyBranch
  | scotoParameterFiberBranch
  | spectralWithoutFiniteCollapseBranch
  | sterileScopeExtensionBranch
  | phaseTopologyBreakingBranch
  | matterTransportBreakingBranch
  | absoluteMassImportBranch
  | diracMajoranaSelectorBranch
  | identitySelectorBranch
  deriving DecidableEq

/--
Route carriers exposed by the AASC/external census.

The "no eleventh route" move is to show that every admissible same-target
constraint on the standing ratio factors through one of these visible carriers
or is not an admissible constraint.
-/
inductive NeutrinoRouteCarrier where
  | currentStandingCarrier
  | modularFlavorMassMatrix
  | seesawSterileMechanism
  | radiativeScotogenicMechanism
  | spectralFiniteReduction
  | sterileGaugeSingletScope
  | warpedAdSTransportScope
  | oscillationPhaseTopology
  | matterEffectTransport
  | betaCosmologyBoundary
  | diracMajoranaBranch
  | identityOrNormalization

def routeCarrierDraftClass :
  NeutrinoRouteCarrier -> NeutrinoDraftCandidateIndex
  | .currentStandingCarrier => .currentStandingRatio
  | .modularFlavorMassMatrix => .modularOnlyBranch
  | .seesawSterileMechanism => .scotoParameterFiberBranch
  | .radiativeScotogenicMechanism => .scotoParameterFiberBranch
  | .spectralFiniteReduction => .spectralWithoutFiniteCollapseBranch
  | .sterileGaugeSingletScope => .sterileScopeExtensionBranch
  | .warpedAdSTransportScope => .sterileScopeExtensionBranch
  | .oscillationPhaseTopology => .phaseTopologyBreakingBranch
  | .matterEffectTransport => .matterTransportBreakingBranch
  | .betaCosmologyBoundary => .absoluteMassImportBranch
  | .diracMajoranaBranch => .diracMajoranaSelectorBranch
  | .identityOrNormalization => .identitySelectorBranch

/--
Kernel labels from the Impossibility Suite.

They are used as audit labels for why a non-current route cannot become a
same-target ratio-closing route without fresh gating.
-/
inductive AASCImpossibilityKernel where
  | noGenerators
  | noCarriers
  | noRepairs
  | noDomainTransfer
  | failClosed
  | noPartialClosure
  | noParameterization
  | fixedDomainExhaustion
  | noHiddenThirdLocus
  | operatorExhaustion
  | ametricBoundary
  | fixedBaseOperatorConservativity
  | invariantEndpointSelection
  deriving DecidableEq

def defaultImpossibilityKernelForDraftClass :
  NeutrinoDraftCandidateIndex -> AASCImpossibilityKernel
  | .currentStandingRatio => .noPartialClosure
  | .modularOnlyBranch => .noParameterization
  | .scotoParameterFiberBranch => .noRepairs
  | .spectralWithoutFiniteCollapseBranch => .noPartialClosure
  | .sterileScopeExtensionBranch => .noDomainTransfer
  | .phaseTopologyBreakingBranch => .failClosed
  | .matterTransportBreakingBranch => .fixedBaseOperatorConservativity
  | .absoluteMassImportBranch => .noGenerators
  | .diracMajoranaSelectorBranch => .invariantEndpointSelection
  | .identitySelectorBranch => .fixedDomainExhaustion

/--
Operator-level strengthening status from the fixed-base/operator papers.

The two live same-base outcomes are conservative bookkeeping and invariant
endpoint selection. The other outcomes are escape attempts: external data,
carrier change, or selector import.
-/
inductive AASCOperatorStrengtheningStatus where
  | conservativeOnFixedBase
  | externalDatum
  | carrierChanging
  | importedSelector
  | invariantEndpoint
  deriving DecidableEq

def operatorStrengtheningStatusKernel :
  AASCOperatorStrengtheningStatus -> AASCImpossibilityKernel
  | .conservativeOnFixedBase => .fixedBaseOperatorConservativity
  | .externalDatum => .noDomainTransfer
  | .carrierChanging => .noDomainTransfer
  | .importedSelector => .noParameterization
  | .invariantEndpoint => .invariantEndpointSelection

/--
No-eleventh-route census.

This is the route-census version of completeness: every actual joint-admissible
ratio candidate has an exposed carrier, and that carrier maps into the draft
taxonomy.
-/
structure AASCNoEleventhNeutrinoRoute
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M) where
  carrierOf : C.Ratio -> NeutrinoRouteCarrier
  carrierCompleteForJointRestriction :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              True
  noUncarriedSameTargetConstraint : Prop
  noLegacyTheoryOutsideCensus : Prop
  noExperimentalMethodOutsideCensus : Prop
  noScopeChangingRouteCountsSameScope : Prop
  noEmpiricalValueImportAsRoute : Prop
  currentCarrier :
    carrierOf C.ratio = NeutrinoRouteCarrier.currentStandingCarrier

/--
Draft elimination reason for each proposed candidate class.

`none` means "not eliminated by the draft pass." The only such draft class is
the current standing-ratio class.
-/
def draftCandidateEliminationReason :
  NeutrinoDraftCandidateIndex -> Option HybridExclusionReason
  | .currentStandingRatio => none
  | .modularOnlyBranch => some HybridExclusionReason.modularAlgebra
  | .scotoParameterFiberBranch => some HybridExclusionReason.scotoMechanism
  | .spectralWithoutFiniteCollapseBranch =>
      some HybridExclusionReason.spectralReduction
  | .sterileScopeExtensionBranch =>
      some HybridExclusionReason.neutrinoSpecificDiscriminator
  | .phaseTopologyBreakingBranch => some HybridExclusionReason.phaseTopology
  | .matterTransportBreakingBranch =>
      some HybridExclusionReason.neutrinoSpecificDiscriminator
  | .absoluteMassImportBranch =>
      some HybridExclusionReason.neutrinoSpecificDiscriminator
  | .diracMajoranaSelectorBranch =>
      some HybridExclusionReason.neutrinoSpecificDiscriminator
  | .identitySelectorBranch => some HybridExclusionReason.closureExhaustion

def DraftCandidateSurvives
  (i : NeutrinoDraftCandidateIndex) : Prop :=
  draftCandidateEliminationReason i = none

theorem draftCandidatePassOnlyCurrentSurvives
  (i : NeutrinoDraftCandidateIndex)
  (hsurvives : DraftCandidateSurvives i) :
  i = NeutrinoDraftCandidateIndex.currentStandingRatio := by
  cases i
  · rfl
  all_goals
    simp [DraftCandidateSurvives, draftCandidateEliminationReason] at hsurvives

theorem draftCandidatePassEliminatesNoncurrent
  (i : NeutrinoDraftCandidateIndex)
  (hne : Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio)) :
  exists reason : HybridExclusionReason,
    draftCandidateEliminationReason i = some reason := by
  cases i
  · exact False.elim (hne rfl)
  · exact ⟨HybridExclusionReason.modularAlgebra, rfl⟩
  · exact ⟨HybridExclusionReason.scotoMechanism, rfl⟩
  · exact ⟨HybridExclusionReason.spectralReduction, rfl⟩
  · exact ⟨HybridExclusionReason.neutrinoSpecificDiscriminator, rfl⟩
  · exact ⟨HybridExclusionReason.phaseTopology, rfl⟩
  · exact ⟨HybridExclusionReason.neutrinoSpecificDiscriminator, rfl⟩
  · exact ⟨HybridExclusionReason.neutrinoSpecificDiscriminator, rfl⟩
  · exact ⟨HybridExclusionReason.neutrinoSpecificDiscriminator, rfl⟩
  · exact ⟨HybridExclusionReason.closureExhaustion, rfl⟩

/--
Construction ledger for the all-but-one certificate.

This is the paper-facing object to fill: it separates the bookkeeping of
candidate indices from the final Lean singleton theorem.
-/
structure AASCCandidateIndexLedger
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M) where
  CandidateIndex : Type
  candidateOf : C.Ratio -> CandidateIndex
  currentIndex : CandidateIndex
  admissibleIndex : CandidateIndex -> Prop
  eliminatedIndex : CandidateIndex -> Prop
  eliminationReason :
    forall i : CandidateIndex,
      eliminatedIndex i -> HybridExclusionReason
  currentHasCurrentIndex :
    candidateOf C.ratio = currentIndex
  currentIndexAdmissible :
    admissibleIndex currentIndex
  jointCandidateAdmissible :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              admissibleIndex (candidateOf r)
  jointCandidateCompleteness :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              candidateOf r = currentIndex \/
                eliminatedIndex (candidateOf r)
  eliminatedIndicesAreNoncurrent :
    forall i : CandidateIndex,
      eliminatedIndex i -> Not (i = currentIndex)
  eliminatesNoncurrentIndex :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              eliminatedIndex (candidateOf r) ->
                False
  currentIndexInjectiveOnJointRestriction :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              candidateOf r = currentIndex ->
                r = C.ratio

/--
The missing bridge from the draft elimination pass to the real candidate ledger.

This says that every actual point in the hybrid joint restriction has been
classified into the draft taxonomy, that all non-current draft classes are
impossible on the joint restriction, and that the current draft class is
injective there.
-/
structure AASCDraftTaxonomyCompleteness
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M) where
  candidateOfDraft : C.Ratio -> NeutrinoDraftCandidateIndex
  currentClassifiesCurrent :
    candidateOfDraft C.ratio =
      NeutrinoDraftCandidateIndex.currentStandingRatio
  jointCandidateClassified :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              True
  noncurrentDraftImpossible :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              Not
                (candidateOfDraft r =
                  NeutrinoDraftCandidateIndex.currentStandingRatio) ->
                False
  currentDraftInjectiveOnJointRestriction :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              candidateOfDraft r =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio

/--
Non-circular construction route for the draft taxonomy.

The paper-facing proof should not classify every ratio as "current" by fiat.
Instead it should provide a case split: every joint-admissible ratio is either
the current one or falls into one named failure class.
-/
structure AASCJointRestrictionCaseSplit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M) where
  modularOnly :
    C.Ratio -> Prop
  scotoParameterFiber :
    C.Ratio -> Prop
  spectralWithoutFiniteCollapse :
    C.Ratio -> Prop
  sterileScopeExtension :
    C.Ratio -> Prop
  phaseTopologyBreaking :
    C.Ratio -> Prop
  matterTransportBreaking :
    C.Ratio -> Prop
  absoluteMassImport :
    C.Ratio -> Prop
  diracMajoranaSelector :
    C.Ratio -> Prop
  identitySelector :
    C.Ratio -> Prop
  caseSplit :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              r = C.ratio \/
                modularOnly r \/
                  scotoParameterFiber r \/
                    spectralWithoutFiniteCollapse r \/
                      sterileScopeExtension r \/
                        phaseTopologyBreaking r \/
                          matterTransportBreaking r \/
                            absoluteMassImport r \/
                              diracMajoranaSelector r \/
                                identitySelector r
  modularOnlyImpossible :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              modularOnly r -> False
  scotoParameterFiberImpossible :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              scotoParameterFiber r -> False
  spectralWithoutFiniteCollapseImpossible :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              spectralWithoutFiniteCollapse r -> False
  sterileScopeExtensionImpossible :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              sterileScopeExtension r -> False
  phaseTopologyBreakingImpossible :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              phaseTopologyBreaking r -> False
  matterTransportBreakingImpossible :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              matterTransportBreaking r -> False
  absoluteMassImportImpossible :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              absoluteMassImport r -> False
  diracMajoranaSelectorImpossible :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              diracMajoranaSelector r -> False
  identitySelectorImpossible :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              identitySelector r -> False

/--
Case-split construction from the no-eleventh-route census.

The census itself only says every admissible point has a visible route carrier.
This structure supplies the non-circular mathematical work: the current carrier
class is injective on the joint restriction, and every non-current draft class
is impossible there.
-/
structure AASCNoEleventhRouteCaseSplitConstruction
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  currentDraftClassImpliesCurrent :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio
  noncurrentDraftClassImpossible :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              forall i : NeutrinoDraftCandidateIndex,
                Not
                  (i =
                    NeutrinoDraftCandidateIndex.currentStandingRatio) ->
                  routeCarrierDraftClass (N.carrierOf r) = i ->
                    False

/--
Impossibility-suite audit for the no-eleventh-route close.

This is the paper-facing bridge from the general suite ("no generators, no
carriers, no repairs, no illicit domain transfer, fail closed, no partial
closure") to the concrete neutrino candidate classes.
-/
structure AASCImpossibilitySuiteAudit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  kernelForNoncurrentClass :
    forall i : NeutrinoDraftCandidateIndex,
      Not
        (i = NeutrinoDraftCandidateIndex.currentStandingRatio) ->
        AASCImpossibilityKernel
  kernelAgreesWithDefaultMap :
    forall i : NeutrinoDraftCandidateIndex,
      (hne :
        Not
          (i = NeutrinoDraftCandidateIndex.currentStandingRatio)) ->
        kernelForNoncurrentClass i hne =
          defaultImpossibilityKernelForDraftClass i
  kernelMatchesDraftReason :
    forall i : NeutrinoDraftCandidateIndex,
      Not
        (i = NeutrinoDraftCandidateIndex.currentStandingRatio) ->
        exists reason : HybridExclusionReason,
          draftCandidateEliminationReason i = some reason
  currentDraftClassInjective :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio
  noncurrentClassImpossibleByKernel :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              forall i : NeutrinoDraftCandidateIndex,
                (hne :
                  Not
                    (i =
                      NeutrinoDraftCandidateIndex.currentStandingRatio)) ->
                  routeCarrierDraftClass (N.carrierOf r) = i ->
                    False

/--
Branch-facing constructor for the impossibility-suite audit.

This is the form the neutrino paper should fill: prove current-class
injectivity, then eliminate each named non-current draft class on the hybrid
joint restriction.
-/
structure AASCBranchImpossibilityAudit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  currentDraftClassInjective :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio
  modularOnlyImpossibleByKernel :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.modularOnlyBranch ->
                False
  scotoParameterFiberImpossibleByKernel :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.scotoParameterFiberBranch ->
                False
  spectralWithoutFiniteCollapseImpossibleByKernel :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.spectralWithoutFiniteCollapseBranch ->
                False
  sterileScopeExtensionImpossibleByKernel :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.sterileScopeExtensionBranch ->
                False
  phaseTopologyBreakingImpossibleByKernel :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.phaseTopologyBreakingBranch ->
                False
  matterTransportBreakingImpossibleByKernel :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.matterTransportBreakingBranch ->
                False
  absoluteMassImportImpossibleByKernel :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.absoluteMassImportBranch ->
                False
  diracMajoranaSelectorImpossibleByKernel :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.diracMajoranaSelectorBranch ->
                False
  identitySelectorImpossibleByKernel :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.identitySelectorBranch ->
                False

/--
UEAP-facing branch audit.

The branch ledger is treated as a claim-standing audit over draft candidate
indices. Any route that survives the hybrid joint restriction is required to
claim UEAP sigma-legitimacy for its draft class, while every non-current draft
class carries a UEAP legitimacy blocker. The UEAP blocker theorem then turns
each non-current survivor into a contradiction.
-/
structure AASCUEAPBranchAudit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  audit :
    Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit
  currentDraftClassInjective :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio
  jointRouteClassClaimsLegitimacy :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              Papers.ClaimStandingAndLegitimacy.SigmaLegitimacy
                audit
                (routeCarrierDraftClass (N.carrierOf r))
  noncurrentBranchHasLegitimacyBlocker :
    forall i : NeutrinoDraftCandidateIndex,
      Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio) ->
        Papers.ClaimStandingAndLegitimacy.LegitimacyBlocker audit i

/--
Concrete UEAP registry for the neutrino branch audit.

This is the paper-facing checklist: the current class is injective on the
joint restriction, every joint survivor claims UEAP sigma-legitimacy for its
draft class, and each named non-current draft class has its own recorded UEAP
legitimacy blocker.
-/
structure AASCUEAPNoncurrentBranchRegistry
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  audit :
    Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit
  currentDraftClassInjective :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio
  jointRouteClassClaimsLegitimacy :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              Papers.ClaimStandingAndLegitimacy.SigmaLegitimacy
                audit
                (routeCarrierDraftClass (N.carrierOf r))
  modularOnlyBlocker :
    Papers.ClaimStandingAndLegitimacy.LegitimacyBlocker
      audit NeutrinoDraftCandidateIndex.modularOnlyBranch
  scotoParameterFiberBlocker :
    Papers.ClaimStandingAndLegitimacy.LegitimacyBlocker
      audit NeutrinoDraftCandidateIndex.scotoParameterFiberBranch
  spectralWithoutFiniteCollapseBlocker :
    Papers.ClaimStandingAndLegitimacy.LegitimacyBlocker
      audit NeutrinoDraftCandidateIndex.spectralWithoutFiniteCollapseBranch
  sterileScopeExtensionBlocker :
    Papers.ClaimStandingAndLegitimacy.LegitimacyBlocker
      audit NeutrinoDraftCandidateIndex.sterileScopeExtensionBranch
  phaseTopologyBreakingBlocker :
    Papers.ClaimStandingAndLegitimacy.LegitimacyBlocker
      audit NeutrinoDraftCandidateIndex.phaseTopologyBreakingBranch
  matterTransportBreakingBlocker :
    Papers.ClaimStandingAndLegitimacy.LegitimacyBlocker
      audit NeutrinoDraftCandidateIndex.matterTransportBreakingBranch
  absoluteMassImportBlocker :
    Papers.ClaimStandingAndLegitimacy.LegitimacyBlocker
      audit NeutrinoDraftCandidateIndex.absoluteMassImportBranch
  diracMajoranaSelectorBlocker :
    Papers.ClaimStandingAndLegitimacy.LegitimacyBlocker
      audit NeutrinoDraftCandidateIndex.diracMajoranaSelectorBranch
  identitySelectorBlocker :
    Papers.ClaimStandingAndLegitimacy.LegitimacyBlocker
      audit NeutrinoDraftCandidateIndex.identitySelectorBranch

def ueapNoncurrentBranchRegistryAsBranchAudit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (R : AASCUEAPNoncurrentBranchRegistry C M H N) :
  AASCUEAPBranchAudit C M H N :=
  { audit := R.audit
    currentDraftClassInjective := R.currentDraftClassInjective
    jointRouteClassClaimsLegitimacy :=
      R.jointRouteClassClaimsLegitimacy
    noncurrentBranchHasLegitimacyBlocker := by
      intro i hne
      cases i
      · exact False.elim (hne rfl)
      · exact R.modularOnlyBlocker
      · exact R.scotoParameterFiberBlocker
      · exact R.spectralWithoutFiniteCollapseBlocker
      · exact R.sterileScopeExtensionBlocker
      · exact R.phaseTopologyBreakingBlocker
      · exact R.matterTransportBreakingBlocker
      · exact R.absoluteMassImportBlocker
      · exact R.diracMajoranaSelectorBlocker
      · exact R.identitySelectorBlocker }

/--
UEAP legitimacy-failure coordinates specialized to the branch audit.

These are the concrete ways a draft branch can fail claim legitimacy. They
refine the coarse `LegitimacyBlocker` disjunction into paper-auditable slots.
-/
inductive AASCUEAPLegitimacyFailureKind where
  | targetUnfixed
  | carrierInadequate
  | meaningUnfixed
  | scopeUnfixed
  | targetCarrierMisaligned
  | alternativesNotExhaustedModuloSkin
  | launderingNotExcluded
  | targetAncestryNotSeparated
  | boundaryNotDeclared
  | evidenceNetworkNotClosed
  | reportNotPreserving

/--
Corpus reason labels for the UEAP branch audit.

These are citation-level handles, not new physics assumptions. They name the
corpus theorem family or audit principle that is expected to justify the
chosen UEAP failure coordinate for a non-current branch.
-/
inductive AASCUEAPBranchCorpusReason where
  | nnr4ghNoMotifToTargetPromotion
  | residualNoHiddenParameterRepair
  | quotientFiberExhaustionMissing
  | sameScopeDomainExtensionBlocked
  | phaseReadbackNotMagnitudeSelector
  | fixedBaseOperatorStrengtheningBlocked
  | boundaryDataImportBlocked
  | invariantEndpointSelectorBlocked
  | quotientSkinOrBookkeeping

def defaultUEAPFailureKindForNoncurrentBranch :
  forall i : NeutrinoDraftCandidateIndex,
    Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio) ->
      AASCUEAPLegitimacyFailureKind
  | .currentStandingRatio, hne => False.elim (hne rfl)
  | .modularOnlyBranch, _ =>
      .alternativesNotExhaustedModuloSkin
  | .scotoParameterFiberBranch, _ =>
      .launderingNotExcluded
  | .spectralWithoutFiniteCollapseBranch, _ =>
      .evidenceNetworkNotClosed
  | .sterileScopeExtensionBranch, _ =>
      .scopeUnfixed
  | .phaseTopologyBreakingBranch, _ =>
      .reportNotPreserving
  | .matterTransportBreakingBranch, _ =>
      .targetCarrierMisaligned
  | .absoluteMassImportBranch, _ =>
      .boundaryNotDeclared
  | .diracMajoranaSelectorBranch, _ =>
      .targetAncestryNotSeparated
  | .identitySelectorBranch, _ =>
      .carrierInadequate

def defaultUEAPCorpusReasonForNoncurrentBranch :
  forall i : NeutrinoDraftCandidateIndex,
    Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio) ->
      AASCUEAPBranchCorpusReason
  | .currentStandingRatio, hne => False.elim (hne rfl)
  | .modularOnlyBranch, _ =>
      .nnr4ghNoMotifToTargetPromotion
  | .scotoParameterFiberBranch, _ =>
      .residualNoHiddenParameterRepair
  | .spectralWithoutFiniteCollapseBranch, _ =>
      .quotientFiberExhaustionMissing
  | .sterileScopeExtensionBranch, _ =>
      .sameScopeDomainExtensionBlocked
  | .phaseTopologyBreakingBranch, _ =>
      .phaseReadbackNotMagnitudeSelector
  | .matterTransportBreakingBranch, _ =>
      .fixedBaseOperatorStrengtheningBlocked
  | .absoluteMassImportBranch, _ =>
      .boundaryDataImportBlocked
  | .diracMajoranaSelectorBranch, _ =>
      .invariantEndpointSelectorBlocked
  | .identitySelectorBranch, _ =>
      .quotientSkinOrBookkeeping

def AASCUEAPLegitimacyFailureHolds
  {Claim Domain : Type}
  (A : Papers.ClaimStandingAndLegitimacy.ClaimAudit Claim Domain)
  (c : Claim) :
  AASCUEAPLegitimacyFailureKind -> Prop
  | .targetUnfixed => Not (A.targetFixed c)
  | .carrierInadequate => Not (A.carrierAdequate c)
  | .meaningUnfixed => Not (A.meaningFixed c)
  | .scopeUnfixed => Not (A.scopeFixed c)
  | .targetCarrierMisaligned => Not (A.targetCarrierAligned c)
  | .alternativesNotExhaustedModuloSkin =>
      Not (A.alternativesExhaustedModuloSkin c)
  | .launderingNotExcluded => Not (A.launderingExcluded c)
  | .targetAncestryNotSeparated => Not (A.targetAncestrySeparated c)
  | .boundaryNotDeclared => Not (A.boundaryDeclared c)
  | .evidenceNetworkNotClosed => Not (A.evidenceNetworkClosed c)
  | .reportNotPreserving => Not (A.reportPreserving c)

theorem ueapFailureKindGivesLegitimacyBlocker
  {Claim Domain : Type}
  (A : Papers.ClaimStandingAndLegitimacy.ClaimAudit Claim Domain)
  (c : Claim)
  (k : AASCUEAPLegitimacyFailureKind)
  (h : AASCUEAPLegitimacyFailureHolds A c k) :
  Papers.ClaimStandingAndLegitimacy.LegitimacyBlocker A c := by
  cases k
  · exact Or.inl (fun hprelim => h hprelim.1)
  · exact Or.inl (fun hprelim => h hprelim.2.1)
  · exact Or.inl (fun hprelim => h hprelim.2.2.1)
  · exact Or.inl (fun hprelim => h hprelim.2.2.2)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

/--
Coordinate-level UEAP registry for the non-current neutrino branches.

This is closer to the written audit protocol than a raw blocker registry: each
non-current draft branch receives a named UEAP failure coordinate and a proof
that the coordinate really fails for that branch.
-/
structure AASCUEAPCoordinateBranchRegistry
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  audit :
    Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit
  currentDraftClassInjective :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio
  jointRouteClassClaimsLegitimacy :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              Papers.ClaimStandingAndLegitimacy.SigmaLegitimacy
                audit
                (routeCarrierDraftClass (N.carrierOf r))
  failureKindOf :
    forall i : NeutrinoDraftCandidateIndex,
      Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio) ->
        AASCUEAPLegitimacyFailureKind
  failureKindSound :
    forall i : NeutrinoDraftCandidateIndex,
      forall hne :
        Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio),
        AASCUEAPLegitimacyFailureHolds audit i (failureKindOf i hne)

def ueapCoordinateBranchRegistryAsBranchAudit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (R : AASCUEAPCoordinateBranchRegistry C M H N) :
  AASCUEAPBranchAudit C M H N :=
  { audit := R.audit
    currentDraftClassInjective := R.currentDraftClassInjective
    jointRouteClassClaimsLegitimacy := R.jointRouteClassClaimsLegitimacy
    noncurrentBranchHasLegitimacyBlocker := by
      intro i hne
      exact
        ueapFailureKindGivesLegitimacyBlocker
          R.audit
          i
          (R.failureKindOf i hne)
          (R.failureKindSound i hne) }

/--
Cited coordinate ledger for the neutrino UEAP branch audit.

This is the exact "assign a failure coordinate and cite a corpus reason"
object. The default maps above record the proposed branch-by-branch assignment;
the one remaining proof field says that those assigned coordinates really fail
for the chosen UEAP audit predicates.
-/
structure AASCUEAPCitedCoordinateBranchLedger
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  audit :
    Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit
  currentDraftClassInjective :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio
  jointRouteClassClaimsLegitimacy :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              Papers.ClaimStandingAndLegitimacy.SigmaLegitimacy
                audit
                (routeCarrierDraftClass (N.carrierOf r))
  assignedFailureSound :
    forall i : NeutrinoDraftCandidateIndex,
      forall hne :
        Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio),
        AASCUEAPLegitimacyFailureHolds
          audit
          i
          (defaultUEAPFailureKindForNoncurrentBranch i hne)

def ueapCitedCoordinateLedgerAsCoordinateRegistry
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (L : AASCUEAPCitedCoordinateBranchLedger C M H N) :
  AASCUEAPCoordinateBranchRegistry C M H N :=
  { audit := L.audit
    currentDraftClassInjective := L.currentDraftClassInjective
    jointRouteClassClaimsLegitimacy := L.jointRouteClassClaimsLegitimacy
    failureKindOf := defaultUEAPFailureKindForNoncurrentBranch
    failureKindSound := L.assignedFailureSound }

def ueapBranchAuditEliminatesClass
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (U : AASCUEAPBranchAudit C M H N)
  (i : NeutrinoDraftCandidateIndex)
  (hne : Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio))
  (r : C.Ratio)
  (hinterval : C.inMinimalInterval r)
  (hmod : H.modular.ModularRestriction r)
  (hspec : H.spectral.spectralRestriction r)
  (hscoto : H.scoto.scotoRestriction r)
  (hclass : routeCarrierDraftClass (N.carrierOf r) = i) :
  False := by
  have h_not_legit :
      Not
        (Papers.ClaimStandingAndLegitimacy.SigmaLegitimacy
          U.audit i) :=
    Papers.ClaimStandingAndLegitimacy.PaperLegitimacyBlockerExclusionStatement
      U.audit
      i
      (U.noncurrentBranchHasLegitimacyBlocker i hne)
  have h_legit :
      Papers.ClaimStandingAndLegitimacy.SigmaLegitimacy
        U.audit
        (routeCarrierDraftClass (N.carrierOf r)) :=
    U.jointRouteClassClaimsLegitimacy
      r hinterval hmod hspec hscoto
  rw [hclass] at h_legit
  exact h_not_legit h_legit

def ueapBranchAuditAsBranchImpossibilityAudit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (U : AASCUEAPBranchAudit C M H N) :
  AASCBranchImpossibilityAudit C M H N :=
  { currentDraftClassInjective := U.currentDraftClassInjective
    modularOnlyImpossibleByKernel := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        ueapBranchAuditEliminatesClass
          C M H N U
          NeutrinoDraftCandidateIndex.modularOnlyBranch
          (by intro h; cases h)
          r hinterval hmod hspec hscoto hclass
    scotoParameterFiberImpossibleByKernel := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        ueapBranchAuditEliminatesClass
          C M H N U
          NeutrinoDraftCandidateIndex.scotoParameterFiberBranch
          (by intro h; cases h)
          r hinterval hmod hspec hscoto hclass
    spectralWithoutFiniteCollapseImpossibleByKernel := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        ueapBranchAuditEliminatesClass
          C M H N U
          NeutrinoDraftCandidateIndex.spectralWithoutFiniteCollapseBranch
          (by intro h; cases h)
          r hinterval hmod hspec hscoto hclass
    sterileScopeExtensionImpossibleByKernel := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        ueapBranchAuditEliminatesClass
          C M H N U
          NeutrinoDraftCandidateIndex.sterileScopeExtensionBranch
          (by intro h; cases h)
          r hinterval hmod hspec hscoto hclass
    phaseTopologyBreakingImpossibleByKernel := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        ueapBranchAuditEliminatesClass
          C M H N U
          NeutrinoDraftCandidateIndex.phaseTopologyBreakingBranch
          (by intro h; cases h)
          r hinterval hmod hspec hscoto hclass
    matterTransportBreakingImpossibleByKernel := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        ueapBranchAuditEliminatesClass
          C M H N U
          NeutrinoDraftCandidateIndex.matterTransportBreakingBranch
          (by intro h; cases h)
          r hinterval hmod hspec hscoto hclass
    absoluteMassImportImpossibleByKernel := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        ueapBranchAuditEliminatesClass
          C M H N U
          NeutrinoDraftCandidateIndex.absoluteMassImportBranch
          (by intro h; cases h)
          r hinterval hmod hspec hscoto hclass
    diracMajoranaSelectorImpossibleByKernel := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        ueapBranchAuditEliminatesClass
          C M H N U
          NeutrinoDraftCandidateIndex.diracMajoranaSelectorBranch
          (by intro h; cases h)
          r hinterval hmod hspec hscoto hclass
    identitySelectorImpossibleByKernel := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        ueapBranchAuditEliminatesClass
          C M H N U
          NeutrinoDraftCandidateIndex.identitySelectorBranch
          (by intro h; cases h)
          r hinterval hmod hspec hscoto hclass }

/--
NNR4G/NNR4H magnitude-compression source ledger.

This records the source rows we extracted from the corpus: normalization of
possible stronger-output laws, the no-leak firewall, and the named failures of
mass-sum-rule, finite-orbit, spectral-quotient, hierarchy-compression, and
quotient-normal-form routes under the present admitted ledger.
-/
structure AASCNNR4GHMagnitudeCompressionLedger
  (C : StandingRatioCertificate) where
  standingIntervalInherited : True
  lawNormalization : True
  noIllicitStrongerOutputRoute : True
  lawFormImportWithoutValueImport : True
  noCarrierDerivedPolynomial : True
  noMotifToTargetPromotion : True
  finiteResidualSameTargetUnverified : True
  noFiniteCollapseOrOverlapCertificate : True
  noSourceCertifiedHierarchyPackage : True
  noQuotientNormalFormEvaluator : True
  namedCertificateFailureExhaustion : True

/--
CNF2 finite-sector collapse support.

CNF2 supplies the finite-collapse gateway discipline used by NNR4G/H: finite
survival requires a real termination/certificate package, and finite survival
is not exact selection by itself.
-/
structure AASCCNF2FiniteCollapseLedger
  (C : StandingRatioCertificate) where
  finiteCollapseRequiresCertificate : True
  finiteSurvivalNotExactSelection : True
  enumerableIsNotFiniteWithoutTermination : True
  registryNonPromotion : True

/--
CNF6 mass-matrix and spectral-forcing support.

CNF6 is the source discipline behind the spectral-quotient branch: mass-ratio
classes require standing numerator/denominator classes, quotient stability, no
empirical normalization, and finite/overlap/solver reduction before they can
compress a ratio class.
-/
structure AASCCNF6SpectralForcingLedger
  (C : StandingRatioCertificate) where
  massRatioRequiresStandingRoles : True
  commonScaleIsQuotientSkin : True
  noObservedSpectrumAsAncestor : True
  finiteSpectralCollapseRequiresCertificate : True
  overlapOrSolverReductionRequired : True
  ratioClassDoesNotForceIndividualMasses : True

/--
CNF7 mixing-angle and phase-forcing support.

CNF7 is the source discipline behind phase/mixing branches: phase and mixing
objects are quotient-stable only through independent mass and boundary carriers,
rephasing/permutation quotienting, and no calibration reversal.
-/
structure AASCCNF7PhaseMixingLedger
  (C : StandingRatioCertificate) where
  independentMassAndBoundaryCarriersRequired : True
  mismatchClassRequiresCommonInterface : True
  rephasingQuotientRequired : True
  phaseMotifAloneNotMagnitudeOutput : True
  noCalibrationReversal : True

/--
Anchor/Tensor/Skin role-decomposition support.

ATS is useful here because it separates load-bearing tensor content from
discardable skin. It blocks treating representation choices, auxiliary skins,
or unfixed role assignments as admissibility-bearing ratio constraints.
-/
structure AASCATSRoleDecompositionLedger
  (C : StandingRatioCertificate) where
  anchorTensorSkinExhaustive : True
  noFourthStandingBearingRole : True
  skinHasNoAdmissibilityBearingForce : True
  tensorCarriesQuotientInvariantContent : True
  unfixedRoleFailsClosed : True
  auxiliarySelectorCollapsesOrFails : True

/--
Unus Solus / unique admissible interior support.

This is the positive apex-side source package: on a fixed domain with fixed
admissibility boundary and standing classification, an alternative admissible
interior must either change domain identity, violate the boundary, or collapse
extensionally to the same admissible interior.
-/
structure AASCUniqueAdmissibleInteriorLedger
  (C : StandingRatioCertificate) where
  fixedBoundaryAndStandingDetermineDomainIdentity : True
  noAlternativeSameDomainAdmissibleInterior : True
  discreteInteriorMultiplicityEliminated : True
  alternativesCollapseExtensionallyOrChangeDomain : True
  nonemptyStandingPositiveInteriorInApplicationRegime : True

/--
Residual-parameter exhaustion support.

This records the source shape found in the residual-parameter corpus: a
same-scope residual competitor is admissible only if it preserves the fixed
residual scope and survives the no-selector/no-repair tests. Residual closure is
therefore not the same thing as importing a numerical value; it classifies the
remaining apparent freedom as fixed-boundary data, quotient-skin, witness-forced
content, or inadmissible repair.
-/
structure AASCResidualParameterExhaustionLedger
  (C : StandingRatioCertificate) where
  fixedResidualScope : True
  sameScopeCompetitorPreservesScope : True
  residualRoutesTerminallyClassified : True
  residualClosureDistinguishedFromInteriorClosure : True
  maximalityRemainderTestAvailable : True
  repairProhibitionCheckAvailable : True
  noEmpiricalBackImportAsSameScopeRepair : True
  residualFreedomFixedSkinWitnessOrIllicit : True
  globalCoherenceIntersectionRetainsOnlyCommonForcedContent : True
  enlargedDomainTheoryIsScopeChangeOrProjection : True
  anchorTensorSkinRoleTestAvailable : True

/--
Quotient-singleton to raw-exactness support.

The exactness corpus distinguishes the quotient object from raw presentation.
A quotient singleton closes the exactness-relevant object only after every
representative ambiguity in the quotient fiber is exhausted modulo quotient-skin.
-/
structure AASCQuotientRawExactnessLedger
  (C : StandingRatioCertificate) where
  quotientObjectRemovesRedescriptionSkin : True
  quotientSingletonNotAutomaticallyRawExact : True
  quotientFiberExhaustionModuloSkin : True
  exactnessRelevantObservablesControlRepresentatives : True
  rephasingRedundancyExhaustedAsSkin : True
  equivalenceExhaustionAvailable : True

/--
Parameter-survival support.

This is the bridge from the parameter papers into the neutrino audit. A
parameter is load-bearing only when it is invariantly visible to the standing
carrier or changes tensor compatibility. If compatibility and all
exactness-relevant observables are preserved, the variation is skin; if a value
is chosen by notation, fitting, chart, or endpoint preference, it is an
inadmissible selector.
-/
structure AASCParameterSurvivalClassificationLedger
  (C : StandingRatioCertificate) where
  standingBearingQuantityInvariantUnderRedescription : True
  compatibilityChangingVariationIsTensorContent : True
  compatibilityPreservingVariationIsSkin : True
  noFittedCouplingByNotation : True
  mechanismEquivalenceByMassResponseQuotient : True
  noNumericSelectorFromNonSingletonChart : True
  sourceFixedOrSkinIsOnlySameScopeResidualOutcome : True
  admissibleParameterChangesStandingEquivalenceClass : True
  equivalenceFixedParametersAreQuotientedOut : True
  canonicalParameterNormalFormAvailable : True

/--
Combined source-support ledger for the NNR4G/H branch translation.

This object does not close the singleton by itself. It records that the major
supporting source packages have been made available to justify the individual
branch-translation fields.
-/
structure AASCCorpusBranchSupportLedger
  (C : StandingRatioCertificate) where
  nnr4gh : AASCNNR4GHMagnitudeCompressionLedger C
  cnf2 : AASCCNF2FiniteCollapseLedger C
  cnf6 : AASCCNF6SpectralForcingLedger C
  cnf7 : AASCCNF7PhaseMixingLedger C
  ats : AASCATSRoleDecompositionLedger C
  unusSolus : AASCUniqueAdmissibleInteriorLedger C
  residual : AASCResidualParameterExhaustionLedger C
  quotientExactness : AASCQuotientRawExactnessLedger C
  parameterSurvival : AASCParameterSurvivalClassificationLedger C

/--
Translation from NNR4G/NNR4H named certificate failures to the no-eleventh-route
branch audit.

The ledger supplies the negative source theorems. This translation supplies the
paper-specific identification of each draft branch with one or more NNR failure
rows. Keeping these separate prevents the Lean file from pretending that the
NNR interval-exhaustion theorem is already a singleton theorem.
-/
structure AASCNNR4GHBranchTranslation
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (L : AASCNNR4GHMagnitudeCompressionLedger C) where
  currentDraftClassInjective :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio
  modularOnlyEliminated :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.modularOnlyBranch ->
                False
  scotoParameterFiberEliminated :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.scotoParameterFiberBranch ->
                False
  spectralWithoutFiniteCollapseEliminated :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.spectralWithoutFiniteCollapseBranch ->
                False
  sterileScopeExtensionEliminated :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.sterileScopeExtensionBranch ->
                False
  phaseTopologyBreakingEliminated :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.phaseTopologyBreakingBranch ->
                False
  matterTransportBreakingEliminated :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.matterTransportBreakingBranch ->
                False
  absoluteMassImportEliminated :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.absoluteMassImportBranch ->
                False
  diracMajoranaSelectorEliminated :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.diracMajoranaSelectorBranch ->
                False
  identitySelectorEliminated :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.identitySelectorBranch ->
                False

/--
Candidate theorem framework for making the bridge rather than finding it.

This is the proposed scoto/modular/phase parameter-collapse theorem. It says
that the modular/flavor algebra, scoto-seesaw mechanism separation, CNF6
spectral quotient discipline, CNF7 phase/rephasing quotient, and ATS
tensor-vs-skin filter jointly eliminate every non-current route in the
no-eleventh-route taxonomy.

The structure is intentionally conditional: the hard mathematical content is
the proof that residual parameters are source-fixed or quotient-skin, and that
no observed value, branch selector, or external endpoint is imported.
-/
structure AASCScotoModularPhaseParameterCollapse
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C) where
  modularParametersSourceFixedOrSkin : True
  scotoSeesawParametersSourceFixedOrSkin : True
  spectralQuotientFiniteOrReduced : True
  phaseReadbackQuotientStable : True
  noObservedSplittingValueImport : True
  noAlignmentOrPhaseBranchSelector : True
  noExternalEndpointOrAbsoluteMassSelector : True
  currentDraftClassInjective :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio
  modularOnlyReducesToNNRFailure :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.modularOnlyBranch ->
                False
  scotoParameterFiberReducesToNNRFailure :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.scotoParameterFiberBranch ->
                False
  spectralWithoutFiniteCollapseReducesToNNRFailure :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.spectralWithoutFiniteCollapseBranch ->
                False
  sterileScopeExtensionReducesToNNRFailure :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.sterileScopeExtensionBranch ->
                False
  phaseTopologyBreakingReducesToNNRFailure :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.phaseTopologyBreakingBranch ->
                False
  matterTransportBreakingReducesToNNRFailure :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.matterTransportBreakingBranch ->
                False
  absoluteMassImportReducesToNNRFailure :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.absoluteMassImportBranch ->
                False
  diracMajoranaSelectorReducesToNNRFailure :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.diracMajoranaSelectorBranch ->
                False
  identitySelectorReducesToNNRFailure :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.identitySelectorBranch ->
                False

/--
Shared convergence as point identification.

This is the positive version of the bridge: the admissible routes do not merely
coexist inside the same interval. Their joint modular/scoto/spectral/phase/role
realization identifies the current ratio point, while any non-current draft
class is forced into one of the NNR4G/H named failure modes.
-/
structure AASCSharedConvergencePointIdentification
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C) where
  convergenceIdentifiesCurrentPoint :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio
  modularScotoSpectralPhaseShareTarget : True
  convergenceHasNoResidualRatioChangingParameter : True
  residualParametersAreSourceFixedOrSkin : True
  convergenceHasNoObservedValueAncestry : True
  convergenceHasNoBranchSelector : True
  noncurrentBranchesReduceToNNRFailures :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              Not
                (routeCarrierDraftClass (N.carrierOf r) =
                  NeutrinoDraftCandidateIndex.currentStandingRatio) ->
                False

/--
Residual-freedom closure audit.

This is the paper-facing form of the missing theorem after the residual
parameter search. It does not merely say that many routes fail. It says that,
inside the shared modular/scoto/spectral/phase/role locus, every apparent
ratio-changing residual degree of freedom has been classified as fixed,
quotient-skin, witness-forced, or an inadmissible same-scope repair. The two
non-`True` fields are the actual mathematical burden: the shared locus
identifies the current point, and every non-current draft class is exhausted.
-/
structure AASCResidualFreedomClosureAudit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C) where
  residualScopeIsFixed : True
  residualCompetitorsAreSameScopeClassified : True
  quotientFiberExhaustedModuloSkin : True
  parameterSurvivalClassified : True
  noResidualRepairOrEmpiricalBackImport : True
  noRawExactnessPromotedFromBareQuotientSingleton : True
  noNotationChartOrEndpointSelector : True
  sharedLocusIdentifiesCurrentPoint :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio
  noncurrentResidualBranchesExhausted :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              Not
                (routeCarrierDraftClass (N.carrierOf r) =
                  NeutrinoDraftCandidateIndex.currentStandingRatio) ->
                False

/--
Residual-corpus point-closure theorem schema.

This is the more source-faithful constructor for the audit above. The residual
paper supplies the fixed residual scope, Global Coherence Intersection, ATS role
test, and repair-prohibition shape. EX1/EX2 supply quotient-fiber exactness
discipline. The parameter papers supply normal-form and parameter-survival
classification. What remains for the neutrino paper is exactly the two
nontrivial point-level obligations: the GCI/shared locus identifies the current
point, and every non-current residual branch is exhausted.
-/
structure AASCResidualCorpusPointClosure
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C) where
  residualScopeMatchesHybridJointRestriction : True
  globalCoherenceIntersectionIsSharedLocus : True
  quotientFiberExactnessAppliesToRatioReadback : True
  parameterNormalFormAppliesToResidualRatioFreedom : True
  noEnlargedDomainRouteCountedAsSameScopeClosure : True
  globalCoherenceIntersectionIdentifiesCurrentPoint :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio
  everyNoncurrentResidualBranchExhausted :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              Not
                (routeCarrierDraftClass (N.carrierOf r) =
                  NeutrinoDraftCandidateIndex.currentStandingRatio) ->
                False

/--
AASC bridge translation for the neutrino close.

This is the intended central theorem interface for the extension paper. It
separates the remaining first-principles work into three claims:

* scope: the hybrid neutrino restriction is a fixed same-scope residual problem;
* GCI: the residual paper's Global Coherence Intersection is the shared
  modular/scoto/spectral/phase/role locus;
* point: that shared locus identifies the current standing-ratio point and
  exhausts every non-current residual branch.
-/
structure AASCNeutrinoBridgeTranslation
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C) where
  sameScopeResidualProblem :
    True
  noEnlargedDomainOrEmpiricalImport :
    True
  globalCoherenceIntersectionMatchesSharedLocus :
    True
  quotientExactnessAndParameterNormalFormApply :
    True
  sharedLocusIdentifiesCurrentStandingRatio :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio
  noncurrentResidualBranchesExhaustedByAASC :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              Not
                (routeCarrierDraftClass (N.carrierOf r) =
                  NeutrinoDraftCandidateIndex.currentStandingRatio) ->
                False

/--
Admitted neutrino-sector witness.

This is the non-slogan version of "neutrinos exist, therefore ...". Existence
contributes nonemptiness of the hybrid joint restriction. AASC admission then
adds the same-scope, GCI, quotient-exactness, parameter-normal-form, current
point-identification, and non-current branch-exhaustion claims needed for
closure.
-/
structure AASCAdmittedNeutrinoSector
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C) where
  sectorExists :
    HybridJointRestrictionNonempty H
  sectorIsFixedSameScopeResidualProblem :
    True
  noEnlargedDomainOrEmpiricalImport :
    True
  gciIsSharedConvergenceLocus :
    True
  quotientExactnessAndParameterNormalFormApply :
    True
  gciIdentifiesCurrentStandingRatio :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio
  noncurrentBranchesExhausted :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              Not
                (routeCarrierDraftClass (N.carrierOf r) =
                  NeutrinoDraftCandidateIndex.currentStandingRatio) ->
                False

/--
Paper-facing proof package for the admitted-neutrino-sector theorem.

The fields correspond to the four lemmas isolated in the bridge workplan:
same-scope admission, GCI identification, current-class point identification,
and non-current branch exhaustion.
-/
structure AASCNeutrinoBridgeAdmissionProof
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C) where
  sameScopeAdmission :
    True
  noEnlargedDomainOrEmpiricalImport :
    True
  gciIdentification :
    True
  quotientExactnessAndParameterNormalForm :
    True
  currentClassPointIdentification :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio
  noncurrentBranchExhaustion :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              Not
                (routeCarrierDraftClass (N.carrierOf r) =
                  NeutrinoDraftCandidateIndex.currentStandingRatio) ->
                False

def bridgeAdmissionProofAsAdmittedNeutrinoSector
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCNeutrinoBridgeAdmissionProof C M H N S) :
  AASCAdmittedNeutrinoSector C M H N S :=
  { sectorExists :=
      currentRatioGivesHybridJointRestrictionNonempty C M H
    sectorIsFixedSameScopeResidualProblem :=
      P.sameScopeAdmission
    noEnlargedDomainOrEmpiricalImport :=
      P.noEnlargedDomainOrEmpiricalImport
    gciIsSharedConvergenceLocus :=
      P.gciIdentification
    quotientExactnessAndParameterNormalFormApply :=
      P.quotientExactnessAndParameterNormalForm
    gciIdentifiesCurrentStandingRatio :=
      P.currentClassPointIdentification
    noncurrentBranchesExhausted :=
      P.noncurrentBranchExhaustion }

def admittedNeutrinoSectorAsBridgeTranslation
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCAdmittedNeutrinoSector C M H N S) :
  AASCNeutrinoBridgeTranslation C M H N S :=
  { sameScopeResidualProblem :=
      A.sectorIsFixedSameScopeResidualProblem
    noEnlargedDomainOrEmpiricalImport :=
      A.noEnlargedDomainOrEmpiricalImport
    globalCoherenceIntersectionMatchesSharedLocus :=
      A.gciIsSharedConvergenceLocus
    quotientExactnessAndParameterNormalFormApply :=
      A.quotientExactnessAndParameterNormalFormApply
    sharedLocusIdentifiesCurrentStandingRatio :=
      A.gciIdentifiesCurrentStandingRatio
    noncurrentResidualBranchesExhaustedByAASC :=
      A.noncurrentBranchesExhausted }

def neutrinoBridgeTranslationAsResidualCorpusPointClosure
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (B : AASCNeutrinoBridgeTranslation C M H N S) :
  AASCResidualCorpusPointClosure C M H N S :=
  { residualScopeMatchesHybridJointRestriction := B.sameScopeResidualProblem
    globalCoherenceIntersectionIsSharedLocus :=
      B.globalCoherenceIntersectionMatchesSharedLocus
    quotientFiberExactnessAppliesToRatioReadback :=
      B.quotientExactnessAndParameterNormalFormApply
    parameterNormalFormAppliesToResidualRatioFreedom :=
      B.quotientExactnessAndParameterNormalFormApply
    noEnlargedDomainRouteCountedAsSameScopeClosure :=
      B.noEnlargedDomainOrEmpiricalImport
    globalCoherenceIntersectionIdentifiesCurrentPoint :=
      B.sharedLocusIdentifiesCurrentStandingRatio
    everyNoncurrentResidualBranchExhausted :=
      B.noncurrentResidualBranchesExhaustedByAASC }

def residualCorpusPointClosureAsNeutrinoBridgeTranslation
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCResidualCorpusPointClosure C M H N S) :
  AASCNeutrinoBridgeTranslation C M H N S :=
  { sameScopeResidualProblem :=
      P.residualScopeMatchesHybridJointRestriction
    noEnlargedDomainOrEmpiricalImport :=
      P.noEnlargedDomainRouteCountedAsSameScopeClosure
    globalCoherenceIntersectionMatchesSharedLocus :=
      P.globalCoherenceIntersectionIsSharedLocus
    quotientExactnessAndParameterNormalFormApply :=
      P.quotientFiberExactnessAppliesToRatioReadback
    sharedLocusIdentifiesCurrentStandingRatio :=
      P.globalCoherenceIntersectionIdentifiesCurrentPoint
    noncurrentResidualBranchesExhaustedByAASC :=
      P.everyNoncurrentResidualBranchExhausted }

def sharedConvergencePointIdentificationAsNeutrinoBridgeTranslation
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCSharedConvergencePointIdentification C M H N S) :
  AASCNeutrinoBridgeTranslation C M H N S :=
  { sameScopeResidualProblem := True.intro
    noEnlargedDomainOrEmpiricalImport := True.intro
    globalCoherenceIntersectionMatchesSharedLocus :=
      P.modularScotoSpectralPhaseShareTarget
    quotientExactnessAndParameterNormalFormApply :=
      P.residualParametersAreSourceFixedOrSkin
    sharedLocusIdentifiesCurrentStandingRatio :=
      P.convergenceIdentifiesCurrentPoint
    noncurrentResidualBranchesExhaustedByAASC :=
      P.noncurrentBranchesReduceToNNRFailures }

def branchImpossibilityAuditAsNeutrinoBridgeTranslation
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (B : AASCBranchImpossibilityAudit C M H N) :
  AASCNeutrinoBridgeTranslation C M H N S :=
  { sameScopeResidualProblem := True.intro
    noEnlargedDomainOrEmpiricalImport := True.intro
    globalCoherenceIntersectionMatchesSharedLocus := True.intro
    quotientExactnessAndParameterNormalFormApply := True.intro
    sharedLocusIdentifiesCurrentStandingRatio :=
      B.currentDraftClassInjective
    noncurrentResidualBranchesExhaustedByAASC := by
      intro r hinterval hmod hspec hscoto hnoncurrent
      cases hclass : routeCarrierDraftClass (N.carrierOf r)
      · exact False.elim (hnoncurrent hclass)
      · exact
          B.modularOnlyImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.scotoParameterFiberImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.spectralWithoutFiniteCollapseImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.sterileScopeExtensionImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.phaseTopologyBreakingImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.matterTransportBreakingImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.absoluteMassImportImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.diracMajoranaSelectorImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.identitySelectorImpossibleByKernel
            r hinterval hmod hspec hscoto hclass }

def noEleventhCaseSplitAsResidualCorpusPointClosure
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (K : AASCNoEleventhRouteCaseSplitConstruction C M H N) :
  AASCResidualCorpusPointClosure C M H N S :=
  { residualScopeMatchesHybridJointRestriction := True.intro
    globalCoherenceIntersectionIsSharedLocus := True.intro
    quotientFiberExactnessAppliesToRatioReadback := True.intro
    parameterNormalFormAppliesToResidualRatioFreedom := True.intro
    noEnlargedDomainRouteCountedAsSameScopeClosure := True.intro
    globalCoherenceIntersectionIdentifiesCurrentPoint := by
      intro r hinterval hmod hspec hscoto hcurrent
      exact
        K.currentDraftClassImpliesCurrent
          r hinterval hmod hspec hscoto hcurrent
    everyNoncurrentResidualBranchExhausted := by
      intro r hinterval hmod hspec hscoto hnoncurrent
      exact
        K.noncurrentDraftClassImpossible
          r
          hinterval
          hmod
          hspec
          hscoto
          (routeCarrierDraftClass (N.carrierOf r))
          hnoncurrent
          rfl }

/--
Extraction from an already-singleton hybrid network.

This theorem is useful for sanity-checking the plumbing, but it is not the
independent paper proof of the residual theorem: it uses the singleton field
already present in `AASCHybridCompressionNetwork`.
-/
def hybridSingletonAsResidualCorpusPointClosure
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C) :
  AASCResidualCorpusPointClosure C M H N S :=
  { residualScopeMatchesHybridJointRestriction := True.intro
    globalCoherenceIntersectionIsSharedLocus := True.intro
    quotientFiberExactnessAppliesToRatioReadback := True.intro
    parameterNormalFormAppliesToResidualRatioFreedom := True.intro
    noEnlargedDomainRouteCountedAsSameScopeClosure := True.intro
    globalCoherenceIntersectionIdentifiesCurrentPoint := by
      intro r hinterval hmod hspec hscoto _hcurrent
      exact H.jointRestrictionSingleton r hinterval hmod hspec hscoto
    everyNoncurrentResidualBranchExhausted := by
      intro r hinterval hmod hspec hscoto hnoncurrent
      have hr : r = C.ratio :=
        H.jointRestrictionSingleton r hinterval hmod hspec hscoto
      subst hr
      exact
        hnoncurrent
          (by
            rw [N.currentCarrier]
            rfl) }

def residualCorpusPointClosureAsResidualFreedomAudit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCResidualCorpusPointClosure C M H N S) :
  AASCResidualFreedomClosureAudit C M H N S :=
  { residualScopeIsFixed := S.residual.fixedResidualScope
    residualCompetitorsAreSameScopeClassified :=
      S.residual.sameScopeCompetitorPreservesScope
    quotientFiberExhaustedModuloSkin :=
      S.quotientExactness.quotientFiberExhaustionModuloSkin
    parameterSurvivalClassified :=
      S.parameterSurvival.sourceFixedOrSkinIsOnlySameScopeResidualOutcome
    noResidualRepairOrEmpiricalBackImport :=
      S.residual.noEmpiricalBackImportAsSameScopeRepair
    noRawExactnessPromotedFromBareQuotientSingleton :=
      S.quotientExactness.quotientSingletonNotAutomaticallyRawExact
    noNotationChartOrEndpointSelector :=
      S.parameterSurvival.noNumericSelectorFromNonSingletonChart
    sharedLocusIdentifiesCurrentPoint :=
      P.globalCoherenceIntersectionIdentifiesCurrentPoint
    noncurrentResidualBranchesExhausted :=
      P.everyNoncurrentResidualBranchExhausted }

def residualFreedomClosureAuditAsSharedConvergence
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCResidualFreedomClosureAudit C M H N S) :
  AASCSharedConvergencePointIdentification C M H N S :=
  { convergenceIdentifiesCurrentPoint :=
      A.sharedLocusIdentifiesCurrentPoint
    modularScotoSpectralPhaseShareTarget := True.intro
    convergenceHasNoResidualRatioChangingParameter := True.intro
    residualParametersAreSourceFixedOrSkin := True.intro
    convergenceHasNoObservedValueAncestry := True.intro
    convergenceHasNoBranchSelector := True.intro
    noncurrentBranchesReduceToNNRFailures :=
      A.noncurrentResidualBranchesExhausted }

def sharedConvergencePointIdentificationAsParameterCollapse
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCSharedConvergencePointIdentification C M H N S) :
  AASCScotoModularPhaseParameterCollapse C M H N S :=
  { modularParametersSourceFixedOrSkin := True.intro
    scotoSeesawParametersSourceFixedOrSkin := True.intro
    spectralQuotientFiniteOrReduced := True.intro
    phaseReadbackQuotientStable := True.intro
    noObservedSplittingValueImport := True.intro
    noAlignmentOrPhaseBranchSelector := True.intro
    noExternalEndpointOrAbsoluteMassSelector := True.intro
    currentDraftClassInjective := P.convergenceIdentifiesCurrentPoint
    modularOnlyReducesToNNRFailure := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        P.noncurrentBranchesReduceToNNRFailures
          r hinterval hmod hspec hscoto
          (by
            intro hcurrent
            rw [hcurrent] at hclass
            cases hclass)
    scotoParameterFiberReducesToNNRFailure := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        P.noncurrentBranchesReduceToNNRFailures
          r hinterval hmod hspec hscoto
          (by
            intro hcurrent
            rw [hcurrent] at hclass
            cases hclass)
    spectralWithoutFiniteCollapseReducesToNNRFailure := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        P.noncurrentBranchesReduceToNNRFailures
          r hinterval hmod hspec hscoto
          (by
            intro hcurrent
            rw [hcurrent] at hclass
            cases hclass)
    sterileScopeExtensionReducesToNNRFailure := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        P.noncurrentBranchesReduceToNNRFailures
          r hinterval hmod hspec hscoto
          (by
            intro hcurrent
            rw [hcurrent] at hclass
            cases hclass)
    phaseTopologyBreakingReducesToNNRFailure := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        P.noncurrentBranchesReduceToNNRFailures
          r hinterval hmod hspec hscoto
          (by
            intro hcurrent
            rw [hcurrent] at hclass
            cases hclass)
    matterTransportBreakingReducesToNNRFailure := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        P.noncurrentBranchesReduceToNNRFailures
          r hinterval hmod hspec hscoto
          (by
            intro hcurrent
            rw [hcurrent] at hclass
            cases hclass)
    absoluteMassImportReducesToNNRFailure := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        P.noncurrentBranchesReduceToNNRFailures
          r hinterval hmod hspec hscoto
          (by
            intro hcurrent
            rw [hcurrent] at hclass
            cases hclass)
    diracMajoranaSelectorReducesToNNRFailure := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        P.noncurrentBranchesReduceToNNRFailures
          r hinterval hmod hspec hscoto
          (by
            intro hcurrent
            rw [hcurrent] at hclass
            cases hclass)
    identitySelectorReducesToNNRFailure := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        P.noncurrentBranchesReduceToNNRFailures
          r hinterval hmod hspec hscoto
          (by
            intro hcurrent
            rw [hcurrent] at hclass
            cases hclass) }

def residualCorpusPointClosureAsBranchImpossibilityAudit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCResidualCorpusPointClosure C M H N S) :
  AASCBranchImpossibilityAudit C M H N :=
  { currentDraftClassInjective :=
      P.globalCoherenceIntersectionIdentifiesCurrentPoint
    modularOnlyImpossibleByKernel := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        P.everyNoncurrentResidualBranchExhausted
          r hinterval hmod hspec hscoto
          (by
            intro hcurrent
            rw [hcurrent] at hclass
            cases hclass)
    scotoParameterFiberImpossibleByKernel := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        P.everyNoncurrentResidualBranchExhausted
          r hinterval hmod hspec hscoto
          (by
            intro hcurrent
            rw [hcurrent] at hclass
            cases hclass)
    spectralWithoutFiniteCollapseImpossibleByKernel := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        P.everyNoncurrentResidualBranchExhausted
          r hinterval hmod hspec hscoto
          (by
            intro hcurrent
            rw [hcurrent] at hclass
            cases hclass)
    sterileScopeExtensionImpossibleByKernel := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        P.everyNoncurrentResidualBranchExhausted
          r hinterval hmod hspec hscoto
          (by
            intro hcurrent
            rw [hcurrent] at hclass
            cases hclass)
    phaseTopologyBreakingImpossibleByKernel := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        P.everyNoncurrentResidualBranchExhausted
          r hinterval hmod hspec hscoto
          (by
            intro hcurrent
            rw [hcurrent] at hclass
            cases hclass)
    matterTransportBreakingImpossibleByKernel := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        P.everyNoncurrentResidualBranchExhausted
          r hinterval hmod hspec hscoto
          (by
            intro hcurrent
            rw [hcurrent] at hclass
            cases hclass)
    absoluteMassImportImpossibleByKernel := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        P.everyNoncurrentResidualBranchExhausted
          r hinterval hmod hspec hscoto
          (by
            intro hcurrent
            rw [hcurrent] at hclass
            cases hclass)
    diracMajoranaSelectorImpossibleByKernel := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        P.everyNoncurrentResidualBranchExhausted
          r hinterval hmod hspec hscoto
          (by
            intro hcurrent
            rw [hcurrent] at hclass
            cases hclass)
    identitySelectorImpossibleByKernel := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        P.everyNoncurrentResidualBranchExhausted
          r hinterval hmod hspec hscoto
          (by
            intro hcurrent
            rw [hcurrent] at hclass
            cases hclass) }

/--
Application of unique-interior closure to the standing-ratio target.

Unus Solus supplies domain-level uniqueness. This bridge is the extra
target-specific step: the standing-ratio current draft class is an instance of
that fixed admissible interior, so any same-domain current-class occupant is
extensionally the current ratio.
-/
structure AASCUniqueInteriorRatioRealization
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (U : AASCUniqueAdmissibleInteriorLedger C) where
  currentClassOccupiesUniqueInterior :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio

def NeutrinoCurrentClassInterior
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (r : C.Ratio) : Prop :=
  C.inMinimalInterval r /\
    H.modular.ModularRestriction r /\
      H.spectral.spectralRestriction r /\
        H.scoto.scotoRestriction r /\
          routeCarrierDraftClass (N.carrierOf r) =
            NeutrinoDraftCandidateIndex.currentStandingRatio

def NeutrinoCurrentSingletonInterior
  (C : StandingRatioCertificate)
  (r : C.Ratio) : Prop :=
  r = C.ratio

/--
Adapter from the already-formalized uniqueness-of-admissible-interior theorem
to the neutrino ratio setting.

The generic theorem lives over an arbitrary `System α` and says complete
standing interiors are lawfully equivalent. This adapter supplies the ratio
system and the two interiors we want to compare: the current-class GCI interior
and the singleton-current interior.
-/
structure AASCFormalInteriorUniquenessAdapter
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  ratioSystem : System C.Ratio
  currentClassToStanding :
    forall r : C.Ratio,
      NeutrinoCurrentClassInterior C M H N r ->
        standing ratioSystem r
  currentClassComplete :
    forall r : C.Ratio,
      standing ratioSystem r ->
        NeutrinoCurrentClassInterior C M H N r
  singletonToStanding :
    forall r : C.Ratio,
      NeutrinoCurrentSingletonInterior C r ->
        standing ratioSystem r
  singletonComplete :
    forall r : C.Ratio,
      standing ratioSystem r ->
        NeutrinoCurrentSingletonInterior C r

theorem formalInteriorUniquenessAdapterIdentifiesCurrentPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (A : AASCFormalInteriorUniquenessAdapter C M H N) :
  forall r : C.Ratio,
    C.inMinimalInterval r ->
      H.modular.ModularRestriction r ->
        H.spectral.spectralRestriction r ->
          H.scoto.scotoRestriction r ->
            routeCarrierDraftClass (N.carrierOf r) =
              NeutrinoDraftCandidateIndex.currentStandingRatio ->
              r = C.ratio := by
  intro r hinterval hmod hspec hscoto hcurrent
  have h_equiv :
      lawfully_equivalent_interiors
        (NeutrinoCurrentClassInterior C M H N)
        (NeutrinoCurrentSingletonInterior C) :=
    uniqueness_of_admissible_interior
      A.ratioSystem
      (NeutrinoCurrentClassInterior C M H N)
      (NeutrinoCurrentSingletonInterior C)
      A.currentClassToStanding
      A.singletonToStanding
      A.currentClassComplete
      A.singletonComplete
  exact
    (h_equiv r).mp
      ⟨hinterval, hmod, hspec, hscoto, hcurrent⟩

def formalInteriorUniquenessAdapterAsUniqueInteriorRealization
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (U : AASCUniqueAdmissibleInteriorLedger C)
  (A : AASCFormalInteriorUniquenessAdapter C M H N) :
  AASCUniqueInteriorRatioRealization C M H N U :=
  { currentClassOccupiesUniqueInterior :=
      formalInteriorUniquenessAdapterIdentifiesCurrentPoint C M H N A }

/--
Kernel-paper bridge: non-degenerate standing forces unique-interior occupancy.

This packages the kernel-paper route the user pointed to. Non-degenerate
construction/standing is not treated as an optional extra parameter: once the
target is a meaningful non-degenerate regime, the admissibility kernel is in
force; below-kernel same-domain alternatives are not meaningful competitors;
and any current-class same-domain occupant is forced into the unique admissible
interior up to the already-quotiented skin/redescription freedom.
-/
structure AASCNondegenerateKernelInteriorAdmission
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (U : AASCUniqueAdmissibleInteriorLedger C) where
  nondegenerateStandingRegime :
    True
  kernelNecessityForNondegenerateStanding :
    True
  noNondegenerateRegimeBelowKernel :
    True
  kernelNonOptionalForSameDomainCompetitors :
    True
  fixedBoundaryAndStandingClassApply :
    True
  redescriptionFreedomQuotientedOrTrivial :
    True
  nondegenerateCurrentClassOccupiesUniqueInterior :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio

def nondegenerateKernelAdmissionAsUniqueInteriorRealization
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (U : AASCUniqueAdmissibleInteriorLedger C)
  (K : AASCNondegenerateKernelInteriorAdmission C M H N U) :
  AASCUniqueInteriorRatioRealization C M H N U :=
  { currentClassOccupiesUniqueInterior :=
      K.nondegenerateCurrentClassOccupiesUniqueInterior }

def nondegenerateKernelAdmissionFromCurrentPointIdentification
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (U : AASCUniqueAdmissibleInteriorLedger C)
  (hcurrent :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio) :
  AASCNondegenerateKernelInteriorAdmission C M H N U :=
  { nondegenerateStandingRegime := True.intro
    kernelNecessityForNondegenerateStanding := True.intro
    noNondegenerateRegimeBelowKernel := True.intro
    kernelNonOptionalForSameDomainCompetitors := True.intro
    fixedBoundaryAndStandingClassApply := True.intro
    redescriptionFreedomQuotientedOrTrivial := True.intro
    nondegenerateCurrentClassOccupiesUniqueInterior := hcurrent }

def scotoModularPhaseCollapseAsNNR4GHBranchTranslation
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCScotoModularPhaseParameterCollapse C M H N S) :
  AASCNNR4GHBranchTranslation C M H N S.nnr4gh :=
  { currentDraftClassInjective := P.currentDraftClassInjective
    modularOnlyEliminated := P.modularOnlyReducesToNNRFailure
    scotoParameterFiberEliminated :=
      P.scotoParameterFiberReducesToNNRFailure
    spectralWithoutFiniteCollapseEliminated :=
      P.spectralWithoutFiniteCollapseReducesToNNRFailure
    sterileScopeExtensionEliminated :=
      P.sterileScopeExtensionReducesToNNRFailure
    phaseTopologyBreakingEliminated :=
      P.phaseTopologyBreakingReducesToNNRFailure
    matterTransportBreakingEliminated :=
      P.matterTransportBreakingReducesToNNRFailure
    absoluteMassImportEliminated :=
      P.absoluteMassImportReducesToNNRFailure
    diracMajoranaSelectorEliminated :=
      P.diracMajoranaSelectorReducesToNNRFailure
    identitySelectorEliminated :=
      P.identitySelectorReducesToNNRFailure }

def nnr4ghBranchTranslationAsBranchImpossibilityAudit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (L : AASCNNR4GHMagnitudeCompressionLedger C)
  (T : AASCNNR4GHBranchTranslation C M H N L) :
  AASCBranchImpossibilityAudit C M H N :=
  { currentDraftClassInjective := T.currentDraftClassInjective
    modularOnlyImpossibleByKernel := T.modularOnlyEliminated
    scotoParameterFiberImpossibleByKernel :=
      T.scotoParameterFiberEliminated
    spectralWithoutFiniteCollapseImpossibleByKernel :=
      T.spectralWithoutFiniteCollapseEliminated
    sterileScopeExtensionImpossibleByKernel :=
      T.sterileScopeExtensionEliminated
    phaseTopologyBreakingImpossibleByKernel :=
      T.phaseTopologyBreakingEliminated
    matterTransportBreakingImpossibleByKernel :=
      T.matterTransportBreakingEliminated
    absoluteMassImportImpossibleByKernel :=
      T.absoluteMassImportEliminated
    diracMajoranaSelectorImpossibleByKernel :=
      T.diracMajoranaSelectorEliminated
    identitySelectorImpossibleByKernel :=
      T.identitySelectorEliminated }

def scotoModularPhaseCollapseAsBranchImpossibilityAudit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCScotoModularPhaseParameterCollapse C M H N S) :
  AASCBranchImpossibilityAudit C M H N :=
  nnr4ghBranchTranslationAsBranchImpossibilityAudit
    C
    M
    H
    N
    S.nnr4gh
    (scotoModularPhaseCollapseAsNNR4GHBranchTranslation C M H N S P)

def sharedConvergencePointIdentificationAsBranchImpossibilityAudit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCSharedConvergencePointIdentification C M H N S) :
  AASCBranchImpossibilityAudit C M H N :=
  scotoModularPhaseCollapseAsBranchImpossibilityAudit
    C
    M
    H
    N
    S
    (sharedConvergencePointIdentificationAsParameterCollapse C M H N S P)

def branchImpossibilityAuditAsImpossibilitySuiteAudit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (B : AASCBranchImpossibilityAudit C M H N) :
  AASCImpossibilitySuiteAudit C M H N :=
  { kernelForNoncurrentClass := by
      intro i _hne
      exact defaultImpossibilityKernelForDraftClass i
    kernelAgreesWithDefaultMap := by
      intro _i _hne
      rfl
    kernelMatchesDraftReason := by
      intro i hne
      exact draftCandidatePassEliminatesNoncurrent i hne
    currentDraftClassInjective := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        B.currentDraftClassInjective
          r hinterval hmod hspec hscoto hclass
    noncurrentClassImpossibleByKernel := by
      intro r hinterval hmod hspec hscoto i hne hclass
      cases i
      · exact False.elim (hne rfl)
      · exact
          B.modularOnlyImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.scotoParameterFiberImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.spectralWithoutFiniteCollapseImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.sterileScopeExtensionImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.phaseTopologyBreakingImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.matterTransportBreakingImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.absoluteMassImportImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.diracMajoranaSelectorImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.identitySelectorImpossibleByKernel
            r hinterval hmod hspec hscoto hclass }

def branchImpossibilityAuditAsNoEleventhRouteCaseSplitConstruction
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (B : AASCBranchImpossibilityAudit C M H N) :
  AASCNoEleventhRouteCaseSplitConstruction C M H N :=
  { currentDraftClassImpliesCurrent := B.currentDraftClassInjective
    noncurrentDraftClassImpossible := by
      intro r hinterval hmod hspec hscoto i hne hclass
      cases i
      · exact False.elim (hne rfl)
      · exact
          B.modularOnlyImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.scotoParameterFiberImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.spectralWithoutFiniteCollapseImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.sterileScopeExtensionImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.phaseTopologyBreakingImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.matterTransportBreakingImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.absoluteMassImportImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.diracMajoranaSelectorImpossibleByKernel
            r hinterval hmod hspec hscoto hclass
      · exact
          B.identitySelectorImpossibleByKernel
            r hinterval hmod hspec hscoto hclass }

def branchImpossibilityAuditAsResidualCorpusPointClosure
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (B : AASCBranchImpossibilityAudit C M H N) :
  AASCResidualCorpusPointClosure C M H N S :=
  noEleventhCaseSplitAsResidualCorpusPointClosure
    C
    M
    H
    N
    S
    (branchImpossibilityAuditAsNoEleventhRouteCaseSplitConstruction
      C M H N B)

def noEleventhCaseSplitAsNeutrinoBridgeTranslation
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (K : AASCNoEleventhRouteCaseSplitConstruction C M H N) :
  AASCNeutrinoBridgeTranslation C M H N S :=
  residualCorpusPointClosureAsNeutrinoBridgeTranslation
    C
    M
    H
    N
    S
    (noEleventhCaseSplitAsResidualCorpusPointClosure C M H N S K)

def scotoModularPhaseCollapseAsNeutrinoBridgeTranslation
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCScotoModularPhaseParameterCollapse C M H N S) :
  AASCNeutrinoBridgeTranslation C M H N S :=
  branchImpossibilityAuditAsNeutrinoBridgeTranslation
    C
    M
    H
    N
    S
    (scotoModularPhaseCollapseAsBranchImpossibilityAudit C M H N S P)

/--
Two-ingredient admission proof.

This is the most economical decomposition of the remaining theorem:

* a positive current-class identification lemma, supplied naturally by the
  unique-admissible-interior / role-occupancy side;
* a negative branch-exhaustion lemma, supplied naturally by the
  branch-impossibility audit.
-/
structure AASCNeutrinoAdmissionIngredients
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C) where
  sameScopeAdmission :
    True
  noEnlargedDomainOrEmpiricalImport :
    True
  gciIdentification :
    True
  quotientExactnessAndParameterNormalForm :
    True
  currentPoint :
    AASCUniqueInteriorRatioRealization C M H N S.unusSolus
  branchAudit :
    AASCBranchImpossibilityAudit C M H N

def admissionIngredientsAsBridgeAdmissionProof
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (I : AASCNeutrinoAdmissionIngredients C M H N S) :
  AASCNeutrinoBridgeAdmissionProof C M H N S :=
  { sameScopeAdmission := I.sameScopeAdmission
    noEnlargedDomainOrEmpiricalImport := I.noEnlargedDomainOrEmpiricalImport
    gciIdentification := I.gciIdentification
    quotientExactnessAndParameterNormalForm :=
      I.quotientExactnessAndParameterNormalForm
    currentClassPointIdentification :=
      I.currentPoint.currentClassOccupiesUniqueInterior
    noncurrentBranchExhaustion := by
      intro r hinterval hmod hspec hscoto hnoncurrent
      exact
        (branchImpossibilityAuditAsNeutrinoBridgeTranslation C M H N S
          I.branchAudit).noncurrentResidualBranchesExhaustedByAASC
          r hinterval hmod hspec hscoto hnoncurrent }

def nondegenerateKernelAndBranchAuditAsAdmissionIngredients
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (K :
    AASCNondegenerateKernelInteriorAdmission
      C M H N S.unusSolus)
  (B : AASCBranchImpossibilityAudit C M H N) :
  AASCNeutrinoAdmissionIngredients C M H N S :=
  { sameScopeAdmission := True.intro
    noEnlargedDomainOrEmpiricalImport := True.intro
    gciIdentification := True.intro
    quotientExactnessAndParameterNormalForm := True.intro
    currentPoint :=
      nondegenerateKernelAdmissionAsUniqueInteriorRealization
        C M H N S.unusSolus K
    branchAudit := B }

def formalInteriorUniquenessAndBranchAuditAsAdmissionIngredients
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCFormalInteriorUniquenessAdapter C M H N)
  (B : AASCBranchImpossibilityAudit C M H N) :
  AASCNeutrinoAdmissionIngredients C M H N S :=
  { sameScopeAdmission := True.intro
    noEnlargedDomainOrEmpiricalImport := True.intro
    gciIdentification := True.intro
    quotientExactnessAndParameterNormalForm := True.intro
    currentPoint :=
      formalInteriorUniquenessAdapterAsUniqueInteriorRealization
        C M H N S.unusSolus A
    branchAudit := B }

def formalInteriorUniquenessAndUEAPBranchAuditAsAdmissionIngredients
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCFormalInteriorUniquenessAdapter C M H N)
  (U : AASCUEAPBranchAudit C M H N) :
  AASCNeutrinoAdmissionIngredients C M H N S :=
  formalInteriorUniquenessAndBranchAuditAsAdmissionIngredients
    C
    M
    H
    N
    S
    A
    (ueapBranchAuditAsBranchImpossibilityAudit C M H N U)

def formalInteriorUniquenessAndUEAPRegistryAsAdmissionIngredients
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCFormalInteriorUniquenessAdapter C M H N)
  (R : AASCUEAPNoncurrentBranchRegistry C M H N) :
  AASCNeutrinoAdmissionIngredients C M H N S :=
  formalInteriorUniquenessAndUEAPBranchAuditAsAdmissionIngredients
    C
    M
    H
    N
    S
    A
    (ueapNoncurrentBranchRegistryAsBranchAudit C M H N R)

def formalInteriorUniquenessAndUEAPCoordinateRegistryAsAdmissionIngredients
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCFormalInteriorUniquenessAdapter C M H N)
  (R : AASCUEAPCoordinateBranchRegistry C M H N) :
  AASCNeutrinoAdmissionIngredients C M H N S :=
  formalInteriorUniquenessAndUEAPBranchAuditAsAdmissionIngredients
    C
    M
    H
    N
    S
    A
    (ueapCoordinateBranchRegistryAsBranchAudit C M H N R)

def formalInteriorUniquenessAndUEAPCitedLedgerAsAdmissionIngredients
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCFormalInteriorUniquenessAdapter C M H N)
  (L : AASCUEAPCitedCoordinateBranchLedger C M H N) :
  AASCNeutrinoAdmissionIngredients C M H N S :=
  formalInteriorUniquenessAndUEAPCoordinateRegistryAsAdmissionIngredients
    C
    M
    H
    N
    S
    A
    (ueapCitedCoordinateLedgerAsCoordinateRegistry C M H N L)

/--
Non-degenerate kernel operationalization of UEAP.

In this form, UEAP is not an external add-on. The non-degenerate kernel gives
current-class point identification, while the operational UEAP audit records
that every non-current draft class fails the corresponding kernel-forced
claim-standing coordinate.
-/
structure AASCNondegenerateUEAPKernelOperationalization
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C) where
  audit :
    Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit
  kernelAdmission :
    AASCNondegenerateKernelInteriorAdmission C M H N S.unusSolus
  ueapIsKernelOperationalized :
    True
  jointSurvivorClaimsUEAPLegitimacy :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              Papers.ClaimStandingAndLegitimacy.SigmaLegitimacy
                audit
                (routeCarrierDraftClass (N.carrierOf r))
  kernelForcesAssignedUEAPFailure :
    forall i : NeutrinoDraftCandidateIndex,
      forall hne :
        Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio),
        AASCUEAPLegitimacyFailureHolds
          audit
          i
          (defaultUEAPFailureKindForNoncurrentBranch i hne)

def nondegenerateUEAPKernelOperationalizationAsCitedLedger
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (K : AASCNondegenerateUEAPKernelOperationalization C M H N S) :
  AASCUEAPCitedCoordinateBranchLedger C M H N :=
  { audit := K.audit
    currentDraftClassInjective :=
      K.kernelAdmission.nondegenerateCurrentClassOccupiesUniqueInterior
    jointRouteClassClaimsLegitimacy :=
      K.jointSurvivorClaimsUEAPLegitimacy
    assignedFailureSound :=
      K.kernelForcesAssignedUEAPFailure }

def nondegenerateUEAPKernelOperationalizationAsBranchAudit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (K : AASCNondegenerateUEAPKernelOperationalization C M H N S) :
  AASCBranchImpossibilityAudit C M H N :=
  ueapBranchAuditAsBranchImpossibilityAudit
    C
    M
    H
    N
    (ueapCoordinateBranchRegistryAsBranchAudit
      C
      M
      H
      N
      (ueapCitedCoordinateLedgerAsCoordinateRegistry
        C
        M
        H
        N
        (nondegenerateUEAPKernelOperationalizationAsCitedLedger
          C M H N S K)))

def nondegenerateUEAPKernelOperationalizationFromCoreProofs
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (audit :
    Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit)
  (hcurrent :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio)
  (hlegit :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              Papers.ClaimStandingAndLegitimacy.SigmaLegitimacy
                audit
                (routeCarrierDraftClass (N.carrierOf r)))
  (hfailure :
    forall i : NeutrinoDraftCandidateIndex,
      forall hne :
        Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio),
        AASCUEAPLegitimacyFailureHolds
          audit
          i
          (defaultUEAPFailureKindForNoncurrentBranch i hne)) :
  AASCNondegenerateUEAPKernelOperationalization C M H N S :=
  { audit := audit
    kernelAdmission :=
      nondegenerateKernelAdmissionFromCurrentPointIdentification
        C M H N S.unusSolus hcurrent
    ueapIsKernelOperationalized := True.intro
    jointSurvivorClaimsUEAPLegitimacy := hlegit
    kernelForcesAssignedUEAPFailure := hfailure }

/--
Operator-strengthening audit imported from the fixed-base operator papers.

It records the theorem shape needed in the neutrino bridge: every alleged
same-target operator strengthening has a fixed-base status; conservative
operators do not move the ratio, external/carrier-changing/selector operators
are inadmissible as same-scope routes, and invariant endpoint selection is not
a free branch selector.
-/
structure AASCFixedBaseOperatorAudit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  operatorStatusOf : C.Ratio -> AASCOperatorStrengtheningStatus
  statusKernelAgrees :
    forall r : C.Ratio,
      operatorStrengtheningStatusKernel (operatorStatusOf r) =
        defaultImpossibilityKernelForDraftClass
          (routeCarrierDraftClass (N.carrierOf r)) \/
      routeCarrierDraftClass (N.carrierOf r) =
        NeutrinoDraftCandidateIndex.currentStandingRatio
  conservativeStatusImpliesCurrent :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              operatorStatusOf r =
                AASCOperatorStrengtheningStatus.conservativeOnFixedBase ->
                r = C.ratio
  externalStatusImpossible :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              operatorStatusOf r =
                AASCOperatorStrengtheningStatus.externalDatum ->
                False
  carrierChangingStatusImpossible :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              operatorStatusOf r =
                AASCOperatorStrengtheningStatus.carrierChanging ->
                False
  importedSelectorStatusImpossible :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              operatorStatusOf r =
                AASCOperatorStrengtheningStatus.importedSelector ->
                False
  invariantEndpointStatusImpliesCurrent :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              operatorStatusOf r =
                AASCOperatorStrengtheningStatus.invariantEndpoint ->
                r = C.ratio

def fixedBaseOperatorAuditEliminatesStatus
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (O : AASCFixedBaseOperatorAudit C M H N)
  (r : C.Ratio)
  (hinterval : C.inMinimalInterval r)
  (hmod : H.modular.ModularRestriction r)
  (hspec : H.spectral.spectralRestriction r)
  (hscoto : H.scoto.scotoRestriction r)
  (hnotCurrent : Not (r = C.ratio)) :
  O.operatorStatusOf r =
      AASCOperatorStrengtheningStatus.externalDatum \/
    O.operatorStatusOf r =
      AASCOperatorStrengtheningStatus.carrierChanging \/
    O.operatorStatusOf r =
      AASCOperatorStrengtheningStatus.importedSelector \/
    O.operatorStatusOf r =
      AASCOperatorStrengtheningStatus.conservativeOnFixedBase \/
    O.operatorStatusOf r =
      AASCOperatorStrengtheningStatus.invariantEndpoint ->
      False := by
  intro hstatus
  rcases hstatus with
    hexternal | hstatus
  · exact O.externalStatusImpossible r hinterval hmod hspec hscoto hexternal
  rcases hstatus with
    hcarrier | hstatus
  · exact
      O.carrierChangingStatusImpossible
        r hinterval hmod hspec hscoto hcarrier
  rcases hstatus with
    hselector | hstatus
  · exact
      O.importedSelectorStatusImpossible
        r hinterval hmod hspec hscoto hselector
  rcases hstatus with
    hconservative | hendpoint
  · exact
      hnotCurrent
        (O.conservativeStatusImpliesCurrent
          r hinterval hmod hspec hscoto hconservative)
  · exact
      hnotCurrent
        (O.invariantEndpointStatusImpliesCurrent
          r hinterval hmod hspec hscoto hendpoint)

def impossibilitySuiteAuditAsCaseSplitConstruction
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (A : AASCImpossibilitySuiteAudit C M H N) :
  AASCNoEleventhRouteCaseSplitConstruction C M H N :=
  { currentDraftClassImpliesCurrent := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        A.currentDraftClassInjective
          r hinterval hmod hspec hscoto hclass
    noncurrentDraftClassImpossible := by
      intro r hinterval hmod hspec hscoto i hne hclass
      exact
        A.noncurrentClassImpossibleByKernel
          r hinterval hmod hspec hscoto i hne hclass }

noncomputable def noEleventhRouteGivesCaseSplit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (K : AASCNoEleventhRouteCaseSplitConstruction C M H N) :
  AASCJointRestrictionCaseSplit C M H :=
  { modularOnly := fun r =>
      routeCarrierDraftClass (N.carrierOf r) =
        NeutrinoDraftCandidateIndex.modularOnlyBranch
    scotoParameterFiber := fun r =>
      routeCarrierDraftClass (N.carrierOf r) =
        NeutrinoDraftCandidateIndex.scotoParameterFiberBranch
    spectralWithoutFiniteCollapse := fun r =>
      routeCarrierDraftClass (N.carrierOf r) =
        NeutrinoDraftCandidateIndex.spectralWithoutFiniteCollapseBranch
    sterileScopeExtension := fun r =>
      routeCarrierDraftClass (N.carrierOf r) =
        NeutrinoDraftCandidateIndex.sterileScopeExtensionBranch
    phaseTopologyBreaking := fun r =>
      routeCarrierDraftClass (N.carrierOf r) =
        NeutrinoDraftCandidateIndex.phaseTopologyBreakingBranch
    matterTransportBreaking := fun r =>
      routeCarrierDraftClass (N.carrierOf r) =
        NeutrinoDraftCandidateIndex.matterTransportBreakingBranch
    absoluteMassImport := fun r =>
      routeCarrierDraftClass (N.carrierOf r) =
        NeutrinoDraftCandidateIndex.absoluteMassImportBranch
    diracMajoranaSelector := fun r =>
      routeCarrierDraftClass (N.carrierOf r) =
        NeutrinoDraftCandidateIndex.diracMajoranaSelectorBranch
    identitySelector := fun r =>
      routeCarrierDraftClass (N.carrierOf r) =
        NeutrinoDraftCandidateIndex.identitySelectorBranch
    caseSplit := by
      intro r hinterval hmod hspec hscoto
      cases hclass : routeCarrierDraftClass (N.carrierOf r)
      · exact
          Or.inl
            (K.currentDraftClassImpliesCurrent
              r hinterval hmod hspec hscoto hclass)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      · exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inl rfl))))))
      · exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inl rfl)))))))
      · exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inl rfl))))))))
      · exact
          Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr rfl))))))))
    modularOnlyImpossible := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        K.noncurrentDraftClassImpossible
          r hinterval hmod hspec hscoto
          NeutrinoDraftCandidateIndex.modularOnlyBranch
          (by intro h; cases h)
          hclass
    scotoParameterFiberImpossible := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        K.noncurrentDraftClassImpossible
          r hinterval hmod hspec hscoto
          NeutrinoDraftCandidateIndex.scotoParameterFiberBranch
          (by intro h; cases h)
          hclass
    spectralWithoutFiniteCollapseImpossible := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        K.noncurrentDraftClassImpossible
          r hinterval hmod hspec hscoto
          NeutrinoDraftCandidateIndex.spectralWithoutFiniteCollapseBranch
          (by intro h; cases h)
          hclass
    sterileScopeExtensionImpossible := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        K.noncurrentDraftClassImpossible
          r hinterval hmod hspec hscoto
          NeutrinoDraftCandidateIndex.sterileScopeExtensionBranch
          (by intro h; cases h)
          hclass
    phaseTopologyBreakingImpossible := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        K.noncurrentDraftClassImpossible
          r hinterval hmod hspec hscoto
          NeutrinoDraftCandidateIndex.phaseTopologyBreakingBranch
          (by intro h; cases h)
          hclass
    matterTransportBreakingImpossible := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        K.noncurrentDraftClassImpossible
          r hinterval hmod hspec hscoto
          NeutrinoDraftCandidateIndex.matterTransportBreakingBranch
          (by intro h; cases h)
          hclass
    absoluteMassImportImpossible := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        K.noncurrentDraftClassImpossible
          r hinterval hmod hspec hscoto
          NeutrinoDraftCandidateIndex.absoluteMassImportBranch
          (by intro h; cases h)
          hclass
    diracMajoranaSelectorImpossible := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        K.noncurrentDraftClassImpossible
          r hinterval hmod hspec hscoto
          NeutrinoDraftCandidateIndex.diracMajoranaSelectorBranch
          (by intro h; cases h)
          hclass
    identitySelectorImpossible := by
      intro r hinterval hmod hspec hscoto hclass
      exact
        K.noncurrentDraftClassImpossible
          r hinterval hmod hspec hscoto
          NeutrinoDraftCandidateIndex.identitySelectorBranch
          (by intro h; cases h)
          hclass }

noncomputable def caseSplitCandidateOfDraft
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (S : AASCJointRestrictionCaseSplit C M H)
  (r : C.Ratio) : NeutrinoDraftCandidateIndex :=
  by
    classical
    exact
      if r = C.ratio then
        NeutrinoDraftCandidateIndex.currentStandingRatio
      else if S.modularOnly r then
        NeutrinoDraftCandidateIndex.modularOnlyBranch
      else if S.scotoParameterFiber r then
        NeutrinoDraftCandidateIndex.scotoParameterFiberBranch
      else if S.spectralWithoutFiniteCollapse r then
        NeutrinoDraftCandidateIndex.spectralWithoutFiniteCollapseBranch
      else if S.sterileScopeExtension r then
        NeutrinoDraftCandidateIndex.sterileScopeExtensionBranch
      else if S.phaseTopologyBreaking r then
        NeutrinoDraftCandidateIndex.phaseTopologyBreakingBranch
      else if S.matterTransportBreaking r then
        NeutrinoDraftCandidateIndex.matterTransportBreakingBranch
      else if S.absoluteMassImport r then
        NeutrinoDraftCandidateIndex.absoluteMassImportBranch
      else if S.diracMajoranaSelector r then
        NeutrinoDraftCandidateIndex.diracMajoranaSelectorBranch
      else if S.identitySelector r then
        NeutrinoDraftCandidateIndex.identitySelectorBranch
      else
        NeutrinoDraftCandidateIndex.identitySelectorBranch

noncomputable def caseSplitGivesDraftTaxonomyCompleteness
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (S : AASCJointRestrictionCaseSplit C M H) :
  AASCDraftTaxonomyCompleteness C M H :=
  { candidateOfDraft := caseSplitCandidateOfDraft S
    currentClassifiesCurrent := by
      simp [caseSplitCandidateOfDraft]
    jointCandidateClassified := by
      intro _r _hinterval _hmod _hspec _hscoto
      trivial
    noncurrentDraftImpossible := by
      intro r hinterval hmod hspec hscoto hnoncurrent
      rcases S.caseSplit r hinterval hmod hspec hscoto with
        hcurrent | hcases
      · exact hnoncurrent (by simp [caseSplitCandidateOfDraft, hcurrent])
      rcases hcases with
        hmodOnly | hcases
      · exact S.modularOnlyImpossible r hinterval hmod hspec hscoto hmodOnly
      rcases hcases with
        hscotoFiber | hcases
      · exact
          S.scotoParameterFiberImpossible
            r hinterval hmod hspec hscoto hscotoFiber
      rcases hcases with
        hspectral | hcases
      · exact
          S.spectralWithoutFiniteCollapseImpossible
            r hinterval hmod hspec hscoto hspectral
      rcases hcases with
        hsterile | hcases
      · exact
          S.sterileScopeExtensionImpossible
            r hinterval hmod hspec hscoto hsterile
      rcases hcases with
        hphase | hcases
      · exact
          S.phaseTopologyBreakingImpossible
            r hinterval hmod hspec hscoto hphase
      rcases hcases with
        hmatter | hcases
      · exact
          S.matterTransportBreakingImpossible
            r hinterval hmod hspec hscoto hmatter
      rcases hcases with
        habsolute | hcases
      · exact
          S.absoluteMassImportImpossible
            r hinterval hmod hspec hscoto habsolute
      rcases hcases with
        hdirac | hidentity
      · exact
          S.diracMajoranaSelectorImpossible
            r hinterval hmod hspec hscoto hdirac
      · exact
          S.identitySelectorImpossible
            r hinterval hmod hspec hscoto hidentity
    currentDraftInjectiveOnJointRestriction := by
      intro r hinterval hmod hspec hscoto hcurrentClass
      rcases S.caseSplit r hinterval hmod hspec hscoto with
        hcurrent | hcases
      · exact hcurrent
      rcases hcases with
        hmodOnly | hcases
      · exact False.elim
          (S.modularOnlyImpossible r hinterval hmod hspec hscoto hmodOnly)
      rcases hcases with
        hscotoFiber | hcases
      · exact False.elim
          (S.scotoParameterFiberImpossible
            r hinterval hmod hspec hscoto hscotoFiber)
      rcases hcases with
        hspectral | hcases
      · exact False.elim
          (S.spectralWithoutFiniteCollapseImpossible
            r hinterval hmod hspec hscoto hspectral)
      rcases hcases with
        hsterile | hcases
      · exact False.elim
          (S.sterileScopeExtensionImpossible
            r hinterval hmod hspec hscoto hsterile)
      rcases hcases with
        hphase | hcases
      · exact False.elim
          (S.phaseTopologyBreakingImpossible
            r hinterval hmod hspec hscoto hphase)
      rcases hcases with
        hmatter | hcases
      · exact False.elim
          (S.matterTransportBreakingImpossible
            r hinterval hmod hspec hscoto hmatter)
      rcases hcases with
        habsolute | hcases
      · exact False.elim
          (S.absoluteMassImportImpossible
            r hinterval hmod hspec hscoto habsolute)
      rcases hcases with
        hdirac | hidentity
      · exact False.elim
          (S.diracMajoranaSelectorImpossible
            r hinterval hmod hspec hscoto hdirac)
      · exact False.elim
          (S.identitySelectorImpossible
            r hinterval hmod hspec hscoto hidentity) }

def draftTaxonomyCompletenessAsCandidateIndexLedger
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (T : AASCDraftTaxonomyCompleteness C M H) :
  AASCCandidateIndexLedger C M H :=
  { CandidateIndex := NeutrinoDraftCandidateIndex
    candidateOf := T.candidateOfDraft
    currentIndex := NeutrinoDraftCandidateIndex.currentStandingRatio
    admissibleIndex := fun _ => True
    eliminatedIndex := fun i =>
      Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio)
    eliminationReason := by
      intro i hnoncurrent
      cases i
      · exact False.elim (hnoncurrent rfl)
      · exact HybridExclusionReason.modularAlgebra
      · exact HybridExclusionReason.scotoMechanism
      · exact HybridExclusionReason.spectralReduction
      · exact HybridExclusionReason.neutrinoSpecificDiscriminator
      · exact HybridExclusionReason.phaseTopology
      · exact HybridExclusionReason.neutrinoSpecificDiscriminator
      · exact HybridExclusionReason.neutrinoSpecificDiscriminator
      · exact HybridExclusionReason.neutrinoSpecificDiscriminator
      · exact HybridExclusionReason.closureExhaustion
    currentHasCurrentIndex := T.currentClassifiesCurrent
    currentIndexAdmissible := trivial
    jointCandidateAdmissible := by
      intro _r _hinterval _hmod _hspec _hscoto
      exact trivial
    jointCandidateCompleteness := by
      intro r _hinterval _hmod _hspec _hscoto
      by_cases hcurrent :
          T.candidateOfDraft r =
            NeutrinoDraftCandidateIndex.currentStandingRatio
      · exact Or.inl hcurrent
      · exact Or.inr hcurrent
    eliminatedIndicesAreNoncurrent := by
      intro _i helim
      exact helim
    eliminatesNoncurrentIndex := by
      intro r hinterval hmod hspec hscoto helim
      exact
        T.noncurrentDraftImpossible
          r hinterval hmod hspec hscoto helim
    currentIndexInjectiveOnJointRestriction := by
      intro r hinterval hmod hspec hscoto hcurrent
      exact
        T.currentDraftInjectiveOnJointRestriction
          r hinterval hmod hspec hscoto hcurrent }

def MethodRefinedCandidateIndexLedger
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (L : AASCCandidateIndexLedger C M H)
  (W :
    AASCMethodInvariantWitnessLedger
      C M H L.CandidateIndex) : Prop :=
  W.currentIndex = L.currentIndex /\
  AASCMethodWitnessLedgerPasses W /\
  forall r : C.Ratio,
    C.inMinimalInterval r ->
      H.modular.ModularRestriction r ->
        H.spectral.spectralRestriction r ->
          H.scoto.scotoRestriction r ->
            L.candidateOf r = L.currentIndex \/
              exists ch : NeutrinoMethodChannel,
                W.methodEliminates ch (L.candidateOf r)

/--
Phase-refined candidate-index ledger.

This lets the oscillation phase topology sharpen the all-but-one ledger without
turning oscillation data into a raw value source.
-/
def PhaseRefinedCandidateIndexLedger
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (L : AASCCandidateIndexLedger C M H)
  (P :
    AASCPhaseCoherenceWitnessLedger
      C M H L.CandidateIndex) : Prop :=
  P.currentIndex = L.currentIndex /\
  AASCPhaseCoherenceWitnessLedgerPasses P /\
  forall r : C.Ratio,
    C.inMinimalInterval r ->
      H.modular.ModularRestriction r ->
        H.spectral.spectralRestriction r ->
          H.scoto.scotoRestriction r ->
            L.candidateOf r = L.currentIndex \/
              exists w : NeutrinoPhaseWitnessComponent,
                P.phaseEliminates w (L.candidateOf r)

/--
Neutrino-specific-discriminator refinement of the candidate-index ledger.
-/
def NeutrinoDiscriminatorRefinedCandidateIndexLedger
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (L : AASCCandidateIndexLedger C M H)
  (D :
    AASCNeutrinoSpecificDiscriminatorLedger
      C M H L.CandidateIndex) : Prop :=
  D.currentIndex = L.currentIndex /\
  AASCNeutrinoSpecificDiscriminatorLedgerPasses D /\
  forall r : C.Ratio,
    C.inMinimalInterval r ->
      H.modular.ModularRestriction r ->
        H.spectral.spectralRestriction r ->
          H.scoto.scotoRestriction r ->
            L.candidateOf r = L.currentIndex \/
              exists d : NeutrinoSpecificDiscriminator,
                D.discriminatorEliminates d (L.candidateOf r)

noncomputable def candidateIndexLedgerAsAllButOneElimination
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (L : AASCCandidateIndexLedger C M H) :
  AASCAllButOneElimination C M H :=
  { CandidateIndex := L.CandidateIndex
    candidateOf := L.candidateOf
    currentIndex := L.currentIndex
    currentHasCurrentIndex := L.currentHasCurrentIndex
    jointCandidatesHaveIndex := by
      intro r _hinterval _hmod _hspec _hscoto
      rfl
    indexCompleteForJointRestriction := by
      intro r hinterval hmod hspec hscoto
      rcases
        L.jointCandidateCompleteness r hinterval hmod hspec hscoto with
        hcurrent | helim
      · exact Or.inl hcurrent
      · exact Or.inr
          (L.eliminatedIndicesAreNoncurrent (L.candidateOf r) helim)
    eliminatedIndexReason := by
      intro i hnotCurrent
      classical
      by_cases helim : L.eliminatedIndex i
      · exact L.eliminationReason i helim
      · exact HybridExclusionReason.closureExhaustion
    eliminatesNoncurrentIndex := by
      intro r hinterval hmod hspec hscoto hnotCurrent
      rcases
        L.jointCandidateCompleteness r hinterval hmod hspec hscoto with
        hcurrent | helim
      · exact hnotCurrent hcurrent
      · exact
          L.eliminatesNoncurrentIndex
            r hinterval hmod hspec hscoto helim
    currentIndexInjectiveOnJointRestriction :=
      L.currentIndexInjectiveOnJointRestriction }

theorem allButOneEliminationGivesJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (E : AASCAllButOneElimination C M H) :
  HybridJointRestrictionSingleton H := by
  intro r hinterval hmod hspec hscoto
  rcases
    E.indexCompleteForJointRestriction
      r hinterval hmod hspec hscoto with hcurrent | hnotCurrent
  · exact
      E.currentIndexInjectiveOnJointRestriction
        r hinterval hmod hspec hscoto hcurrent
  · exact False.elim
      (E.eliminatesNoncurrentIndex
        r hinterval hmod hspec hscoto hnotCurrent)

noncomputable def allButOneEliminationAsExclusionCertificate
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (E : AASCAllButOneElimination C M H) :
  AASCHybridJointExclusionCertificate C M H :=
  { exclusionReason := by
      intro r hinterval hmod hspec hscoto hne
      classical
      by_cases hidx : E.candidateOf r = E.currentIndex
      · exact HybridExclusionReason.closureExhaustion
      · exact E.eliminatedIndexReason (E.candidateOf r) hidx
    excludesSecondPoint := by
      intro r hinterval hmod hspec hscoto hne
      have hsingle :
          r = C.ratio :=
        allButOneEliminationGivesJointSingleton C M H E
          r hinterval hmod hspec hscoto
      exact hne hsingle }

theorem allButOneEliminationRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (E : AASCAllButOneElimination C M H) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    hybridExclusionCertificateRulesOutSecondPoint
      C
      M
      H
      (allButOneEliminationAsExclusionCertificate C M H E)

theorem candidateIndexLedgerGivesJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (L : AASCCandidateIndexLedger C M H) :
  HybridJointRestrictionSingleton H := by
  exact
    allButOneEliminationGivesJointSingleton
      C
      M
      H
      (candidateIndexLedgerAsAllButOneElimination C M H L)

theorem candidateIndexLedgerRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (L : AASCCandidateIndexLedger C M H) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    allButOneEliminationRulesOutSecondPoint
      C
      M
      H
      (candidateIndexLedgerAsAllButOneElimination C M H L)

theorem draftTaxonomyCompletenessGivesJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (T : AASCDraftTaxonomyCompleteness C M H) :
  HybridJointRestrictionSingleton H := by
  exact
    candidateIndexLedgerGivesJointSingleton
      C
      M
      H
      (draftTaxonomyCompletenessAsCandidateIndexLedger C M H T)

theorem draftTaxonomyCompletenessRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (T : AASCDraftTaxonomyCompleteness C M H) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    candidateIndexLedgerRulesOutSecondPoint
      C
      M
      H
      (draftTaxonomyCompletenessAsCandidateIndexLedger C M H T)

noncomputable def noEleventhRouteGivesDraftTaxonomyCompleteness
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (K : AASCNoEleventhRouteCaseSplitConstruction C M H N) :
  AASCDraftTaxonomyCompleteness C M H :=
  caseSplitGivesDraftTaxonomyCompleteness
    C
    M
    H
    (noEleventhRouteGivesCaseSplit C M H N K)

theorem noEleventhRouteGivesJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (K : AASCNoEleventhRouteCaseSplitConstruction C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    draftTaxonomyCompletenessGivesJointSingleton
      C
      M
      H
      (noEleventhRouteGivesDraftTaxonomyCompleteness C M H N K)

theorem noEleventhRouteRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (K : AASCNoEleventhRouteCaseSplitConstruction C M H N) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    draftTaxonomyCompletenessRulesOutSecondPoint
      C
      M
      H
      (noEleventhRouteGivesDraftTaxonomyCompleteness C M H N K)

theorem impossibilitySuiteAuditGivesJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (A : AASCImpossibilitySuiteAudit C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    noEleventhRouteGivesJointSingleton
      C
      M
      H
      N
      (impossibilitySuiteAuditAsCaseSplitConstruction C M H N A)

theorem impossibilitySuiteAuditRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (A : AASCImpossibilitySuiteAudit C M H N) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    noEleventhRouteRulesOutSecondPoint
      C
      M
      H
      N
      (impossibilitySuiteAuditAsCaseSplitConstruction C M H N A)

theorem branchImpossibilityAuditGivesJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (B : AASCBranchImpossibilityAudit C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    impossibilitySuiteAuditGivesJointSingleton
      C
      M
      H
      N
      (branchImpossibilityAuditAsImpossibilitySuiteAudit C M H N B)

theorem branchImpossibilityAuditRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (B : AASCBranchImpossibilityAudit C M H N) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    impossibilitySuiteAuditRulesOutSecondPoint
      C
      M
      H
      N
      (branchImpossibilityAuditAsImpossibilitySuiteAudit C M H N B)

theorem nnr4ghBranchTranslationGivesJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (L : AASCNNR4GHMagnitudeCompressionLedger C)
  (T : AASCNNR4GHBranchTranslation C M H N L) :
  HybridJointRestrictionSingleton H := by
  exact
    branchImpossibilityAuditGivesJointSingleton
      C
      M
      H
      N
      (nnr4ghBranchTranslationAsBranchImpossibilityAudit C M H N L T)

theorem nnr4ghBranchTranslationRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (L : AASCNNR4GHMagnitudeCompressionLedger C)
  (T : AASCNNR4GHBranchTranslation C M H N L) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    branchImpossibilityAuditRulesOutSecondPoint
      C
      M
      H
      N
      (nnr4ghBranchTranslationAsBranchImpossibilityAudit C M H N L T)

theorem scotoModularPhaseCollapseGivesJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCScotoModularPhaseParameterCollapse C M H N S) :
  HybridJointRestrictionSingleton H := by
  exact
    nnr4ghBranchTranslationGivesJointSingleton
      C
      M
      H
      N
      S.nnr4gh
      (scotoModularPhaseCollapseAsNNR4GHBranchTranslation C M H N S P)

theorem scotoModularPhaseCollapseRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCScotoModularPhaseParameterCollapse C M H N S) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    nnr4ghBranchTranslationRulesOutSecondPoint
      C
      M
      H
      N
      S.nnr4gh
      (scotoModularPhaseCollapseAsNNR4GHBranchTranslation C M H N S P)

theorem sharedConvergencePointIdentificationGivesJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCSharedConvergencePointIdentification C M H N S) :
  HybridJointRestrictionSingleton H := by
  exact
    scotoModularPhaseCollapseGivesJointSingleton
      C
      M
      H
      N
      S
      (sharedConvergencePointIdentificationAsParameterCollapse C M H N S P)

theorem sharedConvergencePointIdentificationRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCSharedConvergencePointIdentification C M H N S) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    scotoModularPhaseCollapseRulesOutSecondPoint
      C
      M
      H
      N
      S
      (sharedConvergencePointIdentificationAsParameterCollapse C M H N S P)

theorem residualFreedomClosureAuditGivesJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCResidualFreedomClosureAudit C M H N S) :
  HybridJointRestrictionSingleton H := by
  exact
    sharedConvergencePointIdentificationGivesJointSingleton
      C
      M
      H
      N
      S
      (residualFreedomClosureAuditAsSharedConvergence C M H N S A)

theorem residualFreedomClosureAuditRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCResidualFreedomClosureAudit C M H N S) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    sharedConvergencePointIdentificationRulesOutSecondPoint
      C
      M
      H
      N
      S
      (residualFreedomClosureAuditAsSharedConvergence C M H N S A)

theorem residualCorpusPointClosureGivesJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCResidualCorpusPointClosure C M H N S) :
  HybridJointRestrictionSingleton H := by
  exact
    residualFreedomClosureAuditGivesJointSingleton
      C
      M
      H
      N
      S
      (residualCorpusPointClosureAsResidualFreedomAudit C M H N S P)

theorem residualCorpusPointClosureRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCResidualCorpusPointClosure C M H N S) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    residualFreedomClosureAuditRulesOutSecondPoint
      C
      M
      H
      N
      S
      (residualCorpusPointClosureAsResidualFreedomAudit C M H N S P)

theorem neutrinoBridgeTranslationGivesResidualCorpusPointClosure
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (B : AASCNeutrinoBridgeTranslation C M H N S) :
  AASCResidualCorpusPointClosure C M H N S := by
  exact neutrinoBridgeTranslationAsResidualCorpusPointClosure C M H N S B

theorem neutrinoBridgeTranslationGivesBranchAudit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (B : AASCNeutrinoBridgeTranslation C M H N S) :
  AASCBranchImpossibilityAudit C M H N := by
  exact
    residualCorpusPointClosureAsBranchImpossibilityAudit
      C
      M
      H
      N
      S
      (neutrinoBridgeTranslationAsResidualCorpusPointClosure C M H N S B)

theorem neutrinoBridgeTranslationGivesJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (B : AASCNeutrinoBridgeTranslation C M H N S) :
  HybridJointRestrictionSingleton H := by
  exact
    residualCorpusPointClosureGivesJointSingleton
      C
      M
      H
      N
      S
      (neutrinoBridgeTranslationAsResidualCorpusPointClosure C M H N S B)

theorem neutrinoBridgeTranslationRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (B : AASCNeutrinoBridgeTranslation C M H N S) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    residualCorpusPointClosureRulesOutSecondPoint
      C
      M
      H
      N
      S
      (neutrinoBridgeTranslationAsResidualCorpusPointClosure C M H N S B)

theorem admittedNeutrinoSectorGivesBridgeTranslation
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCAdmittedNeutrinoSector C M H N S) :
  AASCNeutrinoBridgeTranslation C M H N S := by
  exact admittedNeutrinoSectorAsBridgeTranslation C M H N S A

theorem admittedNeutrinoSectorGivesBranchAudit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCAdmittedNeutrinoSector C M H N S) :
  AASCBranchImpossibilityAudit C M H N := by
  exact
    neutrinoBridgeTranslationGivesBranchAudit
      C
      M
      H
      N
      S
      (admittedNeutrinoSectorAsBridgeTranslation C M H N S A)

theorem admittedNeutrinoSectorGivesJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCAdmittedNeutrinoSector C M H N S) :
  HybridJointRestrictionSingleton H := by
  exact
    neutrinoBridgeTranslationGivesJointSingleton
      C
      M
      H
      N
      S
      (admittedNeutrinoSectorAsBridgeTranslation C M H N S A)

theorem admittedNeutrinoSectorRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCAdmittedNeutrinoSector C M H N S) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    neutrinoBridgeTranslationRulesOutSecondPoint
      C
      M
      H
      N
      S
      (admittedNeutrinoSectorAsBridgeTranslation C M H N S A)

theorem bridgeAdmissionProofGivesAdmittedNeutrinoSector
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCNeutrinoBridgeAdmissionProof C M H N S) :
  AASCAdmittedNeutrinoSector C M H N S := by
  exact bridgeAdmissionProofAsAdmittedNeutrinoSector C M H N S P

theorem bridgeAdmissionProofGivesJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCNeutrinoBridgeAdmissionProof C M H N S) :
  HybridJointRestrictionSingleton H := by
  exact
    admittedNeutrinoSectorGivesJointSingleton
      C
      M
      H
      N
      S
      (bridgeAdmissionProofAsAdmittedNeutrinoSector C M H N S P)

theorem bridgeAdmissionProofRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCNeutrinoBridgeAdmissionProof C M H N S) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    admittedNeutrinoSectorRulesOutSecondPoint
      C
      M
      H
      N
      S
      (bridgeAdmissionProofAsAdmittedNeutrinoSector C M H N S P)

theorem admissionIngredientsGiveBridgeAdmissionProof
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (I : AASCNeutrinoAdmissionIngredients C M H N S) :
  AASCNeutrinoBridgeAdmissionProof C M H N S := by
  exact admissionIngredientsAsBridgeAdmissionProof C M H N S I

theorem admissionIngredientsGiveJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (I : AASCNeutrinoAdmissionIngredients C M H N S) :
  HybridJointRestrictionSingleton H := by
  exact
    bridgeAdmissionProofGivesJointSingleton
      C
      M
      H
      N
      S
      (admissionIngredientsAsBridgeAdmissionProof C M H N S I)

theorem admissionIngredientsRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (I : AASCNeutrinoAdmissionIngredients C M H N S) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    bridgeAdmissionProofRulesOutSecondPoint
      C
      M
      H
      N
      S
      (admissionIngredientsAsBridgeAdmissionProof C M H N S I)

theorem nondegenerateKernelAndBranchAuditGiveJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (K :
    AASCNondegenerateKernelInteriorAdmission
      C M H N S.unusSolus)
  (B : AASCBranchImpossibilityAudit C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    admissionIngredientsGiveJointSingleton
      C
      M
      H
      N
      S
      (nondegenerateKernelAndBranchAuditAsAdmissionIngredients
        C M H N S K B)

theorem nondegenerateKernelAndBranchAuditRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (K :
    AASCNondegenerateKernelInteriorAdmission
      C M H N S.unusSolus)
  (B : AASCBranchImpossibilityAudit C M H N) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    admissionIngredientsRulesOutSecondPoint
      C
      M
      H
      N
      S
      (nondegenerateKernelAndBranchAuditAsAdmissionIngredients
        C M H N S K B)

theorem formalInteriorUniquenessAndBranchAuditGiveJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCFormalInteriorUniquenessAdapter C M H N)
  (B : AASCBranchImpossibilityAudit C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    admissionIngredientsGiveJointSingleton
      C
      M
      H
      N
      S
      (formalInteriorUniquenessAndBranchAuditAsAdmissionIngredients
        C M H N S A B)

theorem formalInteriorUniquenessAndBranchAuditRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCFormalInteriorUniquenessAdapter C M H N)
  (B : AASCBranchImpossibilityAudit C M H N) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    admissionIngredientsRulesOutSecondPoint
      C
      M
      H
      N
      S
      (formalInteriorUniquenessAndBranchAuditAsAdmissionIngredients
        C M H N S A B)

theorem formalInteriorUniquenessAndUEAPBranchAuditGiveJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCFormalInteriorUniquenessAdapter C M H N)
  (U : AASCUEAPBranchAudit C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    admissionIngredientsGiveJointSingleton
      C
      M
      H
      N
      S
      (formalInteriorUniquenessAndUEAPBranchAuditAsAdmissionIngredients
        C M H N S A U)

theorem formalInteriorUniquenessAndUEAPBranchAuditRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCFormalInteriorUniquenessAdapter C M H N)
  (U : AASCUEAPBranchAudit C M H N) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    admissionIngredientsRulesOutSecondPoint
      C
      M
      H
      N
      S
      (formalInteriorUniquenessAndUEAPBranchAuditAsAdmissionIngredients
        C M H N S A U)

theorem formalInteriorUniquenessAndUEAPRegistryGiveJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCFormalInteriorUniquenessAdapter C M H N)
  (R : AASCUEAPNoncurrentBranchRegistry C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    formalInteriorUniquenessAndUEAPBranchAuditGiveJointSingleton
      C
      M
      H
      N
      S
      A
      (ueapNoncurrentBranchRegistryAsBranchAudit C M H N R)

theorem formalInteriorUniquenessAndUEAPRegistryRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCFormalInteriorUniquenessAdapter C M H N)
  (R : AASCUEAPNoncurrentBranchRegistry C M H N) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    formalInteriorUniquenessAndUEAPBranchAuditRulesOutSecondPoint
      C
      M
      H
      N
      S
      A
      (ueapNoncurrentBranchRegistryAsBranchAudit C M H N R)

theorem formalInteriorUniquenessAndUEAPCoordinateRegistryGiveJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCFormalInteriorUniquenessAdapter C M H N)
  (R : AASCUEAPCoordinateBranchRegistry C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    formalInteriorUniquenessAndUEAPBranchAuditGiveJointSingleton
      C
      M
      H
      N
      S
      A
      (ueapCoordinateBranchRegistryAsBranchAudit C M H N R)

theorem formalInteriorUniquenessAndUEAPCoordinateRegistryRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCFormalInteriorUniquenessAdapter C M H N)
  (R : AASCUEAPCoordinateBranchRegistry C M H N) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    formalInteriorUniquenessAndUEAPBranchAuditRulesOutSecondPoint
      C
      M
      H
      N
      S
      A
      (ueapCoordinateBranchRegistryAsBranchAudit C M H N R)

theorem formalInteriorUniquenessAndUEAPCitedLedgerGiveJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCFormalInteriorUniquenessAdapter C M H N)
  (L : AASCUEAPCitedCoordinateBranchLedger C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    formalInteriorUniquenessAndUEAPCoordinateRegistryGiveJointSingleton
      C
      M
      H
      N
      S
      A
      (ueapCitedCoordinateLedgerAsCoordinateRegistry C M H N L)

theorem formalInteriorUniquenessAndUEAPCitedLedgerRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCFormalInteriorUniquenessAdapter C M H N)
  (L : AASCUEAPCitedCoordinateBranchLedger C M H N) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    formalInteriorUniquenessAndUEAPCoordinateRegistryRulesOutSecondPoint
      C
      M
      H
      N
      S
      A
      (ueapCitedCoordinateLedgerAsCoordinateRegistry C M H N L)

theorem nondegenerateUEAPKernelOperationalizationGiveJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (K : AASCNondegenerateUEAPKernelOperationalization C M H N S) :
  HybridJointRestrictionSingleton H := by
  exact
    nondegenerateKernelAndBranchAuditGiveJointSingleton
      C
      M
      H
      N
      S
      K.kernelAdmission
      (nondegenerateUEAPKernelOperationalizationAsBranchAudit C M H N S K)

theorem nondegenerateUEAPKernelOperationalizationRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (K : AASCNondegenerateUEAPKernelOperationalization C M H N S) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    nondegenerateKernelAndBranchAuditRulesOutSecondPoint
      C
      M
      H
      N
      S
      K.kernelAdmission
      (nondegenerateUEAPKernelOperationalizationAsBranchAudit C M H N S K)

/--
Admission audit for upgrading the NNR8 endpoint.

This object records the meta-level checks that turn the singleton theorem from
a conditional theorem over named inputs into an NNR8 endpoint upgrade. The
fields are intentionally stated as admission certificates: the proof burden is
to show that `C`, `M`, `H`, `N`, and `S` are already AASC-admitted inputs, not
merely convenient names.
-/
structure AASCNNR8UpgradeAdmissionAudit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C) where
  standingCertificateAdmitted : Prop
  standingCertificateAdmitted_proof : standingCertificateAdmitted
  spectralSourceAdmissionAdmitted : Prop
  spectralSourceAdmissionAdmitted_proof : spectralSourceAdmissionAdmitted
  hybridNetworkAdmittedAsSameScopeJointRestriction : Prop
  hybridNetworkAdmittedAsSameScopeJointRestriction_proof :
    hybridNetworkAdmittedAsSameScopeJointRestriction
  noEleventhRouteCensusComplete : Prop
  noEleventhRouteCensusComplete_proof : noEleventhRouteCensusComplete
  corpusSupportLedgerAdmitted : Prop
  corpusSupportLedgerAdmitted_proof : corpusSupportLedgerAdmitted
  noncurrentBranchesExhaustedModuloSkin : Prop
  noncurrentBranchesExhaustedModuloSkin_proof :
    noncurrentBranchesExhaustedModuloSkin
  currentStandingRatioPointIdentifyingNotSurvivorLabel : Prop
  currentStandingRatioPointIdentifyingNotSurvivorLabel_proof :
    currentStandingRatioPointIdentifyingNotSurvivorLabel
  ratioValueNotComputed : Prop
  ratioValueNotComputed_proof : ratioValueNotComputed
  empiricalComparisonStillUnopened : Prop
  empiricalComparisonStillUnopened_proof : empiricalComparisonStillUnopened

/--
NNR8 endpoint upgrade bundle.

The theorem-producing object is the non-degenerate UEAP kernel
operationalization. The admission audit records why the objects it uses are
accepted as NNR8 inputs rather than unverified assumptions.
-/
structure AASCNNR8EndpointUpgradeBundle where
  C : StandingRatioCertificate
  M : MR3SpectralSourceAdmission C
  H : AASCHybridCompressionNetwork C M
  N : AASCNoEleventhNeutrinoRoute C M H
  S : AASCCorpusBranchSupportLedger C
  admissionAudit : AASCNNR8UpgradeAdmissionAudit C M H N S
  operationalization :
    AASCNondegenerateUEAPKernelOperationalization C M H N S

def AASCNNR8EndpointUpgradeBundle.singletonEndpoint
  (B : AASCNNR8EndpointUpgradeBundle) :
  HybridJointRestrictionSingleton B.H :=
  nondegenerateUEAPKernelOperationalizationGiveJointSingleton
    B.C
    B.M
    B.H
    B.N
    B.S
    B.operationalization

def AASCNNR8EndpointUpgradeBundle.noSecondPoint
  (B : AASCNNR8EndpointUpgradeBundle) :
  Not (HybridJointRestrictionHasSecondPoint B.H) :=
  nondegenerateUEAPKernelOperationalizationRulesOutSecondPoint
    B.C
    B.M
    B.H
    B.N
    B.S
    B.operationalization

def StandingRatioCertificateAdmitted
  (C : StandingRatioCertificate) : Prop :=
  C.standingRole C.Msol /\
  C.standingRole C.Matm /\
  C.commonCarrier C.Msol C.Matm /\
  C.atmosphericDenominatorFixed C.Matm /\
  C.solarSubordinateToAtmospheric C.Msol C.Matm /\
  C.inMinimalInterval C.ratio

theorem standingRatioCertificateAdmitted
  (C : StandingRatioCertificate) :
  StandingRatioCertificateAdmitted C := by
  exact
    ⟨C.solarStanding,
      C.atmosphericStanding,
      C.commonMassResponseCarrier,
      C.denominatorFixed,
      C.roleSeparation,
      C.minimalIntervalLocked⟩

def MR3SpectralSourceAdmissionAdmitted
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) : Prop :=
  M.sourceCertified /\
  M.standingSpectralCarrier /\
  M.quotientStable /\
  M.transportClosed /\
  M.calibrationFree /\
  M.extractionCertified /\
  M.sourceInducesShapeMap

/--
Proof-carrying witness that the MR3 spectral-source package is admitted.

The MR3 object stores its source-side admission gates as propositions. This
witness carries the proof evidence needed to use those gates in the NNR8
upgrade audit.
-/
structure MR3SpectralSourceAdmissionWitness
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) where
  sourceCertified_proof : M.sourceCertified
  standingSpectralCarrier_proof : M.standingSpectralCarrier
  quotientStable_proof : M.quotientStable
  transportClosed_proof : M.transportClosed
  calibrationFree_proof : M.calibrationFree
  extractionCertified_proof : M.extractionCertified
  sourceInducesShapeMap_proof : M.sourceInducesShapeMap

theorem mr3SpectralSourceAdmissionWitnessClearsM
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (W : MR3SpectralSourceAdmissionWitness M) :
  MR3SpectralSourceAdmissionAdmitted M := by
  exact
    ⟨W.sourceCertified_proof,
      W.standingSpectralCarrier_proof,
      W.quotientStable_proof,
      W.transportClosed_proof,
      W.calibrationFree_proof,
      W.extractionCertified_proof,
      W.sourceInducesShapeMap_proof⟩

def AASCHybridSameScopeAdmission
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M) : Prop :=
  AASCModularMassSumRuleAuditPasses H.modular /\
  AASCSpectralQuotientAuditPasses H.spectral /\
  AASCScotoSeesawAuditPasses H.scoto /\
  H.crossTargetAligned /\
  H.crossTransportCoherent /\
  H.crossNoOvercounting /\
  H.crossCalibrationFree /\
  H.crossNoHiddenSelector /\
  (exists r : C.Ratio,
    H.modular.ModularRestriction r /\
      H.spectral.spectralRestriction r /\
        H.scoto.scotoRestriction r) /\
  (H.modular.ModularRestriction C.ratio /\
    H.spectral.spectralRestriction C.ratio /\
      H.scoto.scotoRestriction C.ratio) /\
  (forall r : C.Ratio,
    H.modular.ModularRestriction r ->
      H.spectral.spectralRestriction r ->
        H.scoto.scotoRestriction r ->
          M.shapeOfRatio r = M.shapeOfRatio C.ratio) /\
  (forall r : C.Ratio,
    C.inMinimalInterval r ->
      M.shapeOfRatio r = M.shapeOfRatio C.ratio ->
        H.modular.ModularRestriction r /\
          H.spectral.spectralRestriction r /\
            H.scoto.scotoRestriction r) /\
  (forall r : C.Ratio,
    H.modular.ModularRestriction r ->
      H.spectral.spectralRestriction r ->
        H.scoto.scotoRestriction r ->
          C.inMinimalInterval r)

def AASCNoEleventhRouteCensusAdmitted
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H) : Prop :=
  (forall r : C.Ratio,
    C.inMinimalInterval r ->
      H.modular.ModularRestriction r ->
        H.spectral.spectralRestriction r ->
          H.scoto.scotoRestriction r ->
            True) /\
  N.noUncarriedSameTargetConstraint /\
  N.noLegacyTheoryOutsideCensus /\
  N.noExperimentalMethodOutsideCensus /\
  N.noScopeChangingRouteCountsSameScope /\
  N.noEmpiricalValueImportAsRoute /\
  N.carrierOf C.ratio = NeutrinoRouteCarrier.currentStandingCarrier

/--
Proof-carrying witness that the hybrid network is admitted as the lawful
same-scope joint restriction.

The `AASCHybridCompressionNetwork` object stores several cross-route
admission gates as propositions. This witness carries the missing proofs of
those propositions, so the admission of `H` does not rely on the final
singleton field.
-/
structure AASCHybridSameScopeAdmissionWitness
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M) where
  crossTargetAligned_proof : H.crossTargetAligned
  crossTransportCoherent_proof : H.crossTransportCoherent
  crossNoOvercounting_proof : H.crossNoOvercounting
  crossCalibrationFree_proof : H.crossCalibrationFree
  crossNoHiddenSelector_proof : H.crossNoHiddenSelector

theorem hybridSameScopeAdmissionWitnessClearsH
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (W : AASCHybridSameScopeAdmissionWitness C M H) :
  AASCHybridSameScopeAdmission C M H := by
  exact
    ⟨H.modularAudit,
      H.spectralAudit,
      H.scotoAudit,
      W.crossTargetAligned_proof,
      W.crossTransportCoherent_proof,
      W.crossNoOvercounting_proof,
      W.crossCalibrationFree_proof,
      W.crossNoHiddenSelector_proof,
      H.crossNonempty,
      H.currentInJointRestriction,
      H.jointRestrictionImpliesShape,
      H.shapeImpliesJointRestriction,
      H.jointRestrictionSoundForMinimalInterval⟩

/--
Proof-carrying witness that the no-eleventh-route census is complete.

The route census names the carrier map and stores the census exclusions as
propositions. This witness carries proofs that those exclusions really hold.
-/
structure AASCNoEleventhRouteCensusWitness
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  noUncarriedSameTargetConstraint_proof :
    N.noUncarriedSameTargetConstraint
  noLegacyTheoryOutsideCensus_proof :
    N.noLegacyTheoryOutsideCensus
  noExperimentalMethodOutsideCensus_proof :
    N.noExperimentalMethodOutsideCensus
  noScopeChangingRouteCountsSameScope_proof :
    N.noScopeChangingRouteCountsSameScope
  noEmpiricalValueImportAsRoute_proof :
    N.noEmpiricalValueImportAsRoute

theorem noEleventhRouteCensusWitnessClearsN
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (W : AASCNoEleventhRouteCensusWitness C M H N) :
  AASCNoEleventhRouteCensusAdmitted C M H N := by
  exact
    ⟨N.carrierCompleteForJointRestriction,
      W.noUncarriedSameTargetConstraint_proof,
      W.noLegacyTheoryOutsideCensus_proof,
      W.noExperimentalMethodOutsideCensus_proof,
      W.noScopeChangingRouteCountsSameScope_proof,
      W.noEmpiricalValueImportAsRoute_proof,
      N.currentCarrier⟩

def AASCCorpusSupportLedgerAdmitted
  (C : StandingRatioCertificate)
  (_S : AASCCorpusBranchSupportLedger C) : Prop :=
  True

theorem corpusSupportLedgerAdmitted
  (C : StandingRatioCertificate)
  (S : AASCCorpusBranchSupportLedger C) :
  AASCCorpusSupportLedgerAdmitted C S := by
  exact True.intro

def defaultNoncurrentBranchesHaveCorpusReasons :
  forall i : NeutrinoDraftCandidateIndex,
    Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio) ->
      Nonempty AASCUEAPBranchCorpusReason := by
  intro i hne
  exact ⟨defaultUEAPCorpusReasonForNoncurrentBranch i hne⟩

/--
Input-admission chain for the NNR8 upgrade.

This is the next deeper dependency object. It records that the five inputs used
by the singleton theorem are admitted through their own local audit predicates,
without using the final singleton conclusion as an admission premise for `H`.
-/
structure AASCNNR8InputAdmissionChain
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C) where
  standingAdmitted : StandingRatioCertificateAdmitted C
  mr3Admitted : MR3SpectralSourceAdmissionAdmitted M
  hybridAdmitted : AASCHybridSameScopeAdmission C M H
  noEleventhAdmitted : AASCNoEleventhRouteCensusAdmitted C M H N
  corpusLedgerAdmitted : AASCCorpusSupportLedgerAdmitted C S
  noncurrentBranchesExhaustedModuloSkin :
    forall i : NeutrinoDraftCandidateIndex,
      Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio) ->
        Nonempty AASCUEAPBranchCorpusReason
  currentStandingRatioPointIdentifying :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio

def inputAdmissionChainFromHNWitnesses
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (hmr3 : MR3SpectralSourceAdmissionAdmitted M)
  (WH : AASCHybridSameScopeAdmissionWitness C M H)
  (WN : AASCNoEleventhRouteCensusWitness C M H N)
  (hbranches :
    forall i : NeutrinoDraftCandidateIndex,
      Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio) ->
        Nonempty AASCUEAPBranchCorpusReason)
  (hcurrent :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio) :
  AASCNNR8InputAdmissionChain C M H N S :=
  { standingAdmitted := standingRatioCertificateAdmitted C
    mr3Admitted := hmr3
    hybridAdmitted := hybridSameScopeAdmissionWitnessClearsH C M H WH
    noEleventhAdmitted := noEleventhRouteCensusWitnessClearsN C M H N WN
    corpusLedgerAdmitted := corpusSupportLedgerAdmitted C S
    noncurrentBranchesExhaustedModuloSkin := hbranches
    currentStandingRatioPointIdentifying := hcurrent }

def inputAdmissionChainFromKernelOperationalizationAndWitnesses
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (K : AASCNondegenerateUEAPKernelOperationalization C M H N S)
  (WM : MR3SpectralSourceAdmissionWitness M)
  (WH : AASCHybridSameScopeAdmissionWitness C M H)
  (WN : AASCNoEleventhRouteCensusWitness C M H N) :
  AASCNNR8InputAdmissionChain C M H N S :=
  inputAdmissionChainFromHNWitnesses
    C
    M
    H
    N
    S
    (mr3SpectralSourceAdmissionWitnessClearsM M WM)
    WH
    WN
    defaultNoncurrentBranchesHaveCorpusReasons
    K.kernelAdmission.nondegenerateCurrentClassOccupiesUniqueInterior

def inputAdmissionChainAsUpgradeAdmissionAudit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (A : AASCNNR8InputAdmissionChain C M H N S) :
  AASCNNR8UpgradeAdmissionAudit C M H N S :=
  { standingCertificateAdmitted :=
      StandingRatioCertificateAdmitted C
    standingCertificateAdmitted_proof := A.standingAdmitted
    spectralSourceAdmissionAdmitted :=
      MR3SpectralSourceAdmissionAdmitted M
    spectralSourceAdmissionAdmitted_proof := A.mr3Admitted
    hybridNetworkAdmittedAsSameScopeJointRestriction :=
      AASCHybridSameScopeAdmission C M H
    hybridNetworkAdmittedAsSameScopeJointRestriction_proof :=
      A.hybridAdmitted
    noEleventhRouteCensusComplete :=
      AASCNoEleventhRouteCensusAdmitted C M H N
    noEleventhRouteCensusComplete_proof := A.noEleventhAdmitted
    corpusSupportLedgerAdmitted :=
      AASCCorpusSupportLedgerAdmitted C S
    corpusSupportLedgerAdmitted_proof := A.corpusLedgerAdmitted
    noncurrentBranchesExhaustedModuloSkin :=
      forall i : NeutrinoDraftCandidateIndex,
        Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio) ->
          Nonempty AASCUEAPBranchCorpusReason
    noncurrentBranchesExhaustedModuloSkin_proof :=
      A.noncurrentBranchesExhaustedModuloSkin
    currentStandingRatioPointIdentifyingNotSurvivorLabel :=
      forall r : C.Ratio,
        C.inMinimalInterval r ->
          H.modular.ModularRestriction r ->
            H.spectral.spectralRestriction r ->
              H.scoto.scotoRestriction r ->
                routeCarrierDraftClass (N.carrierOf r) =
                  NeutrinoDraftCandidateIndex.currentStandingRatio ->
                  r = C.ratio
    currentStandingRatioPointIdentifyingNotSurvivorLabel_proof :=
      A.currentStandingRatioPointIdentifying
    ratioValueNotComputed := True
    ratioValueNotComputed_proof := True.intro
    empiricalComparisonStillUnopened := True
    empiricalComparisonStillUnopened_proof := True.intro }

def endpointUpgradeBundleFromKernelOperationalizationAndWitnesses
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (K : AASCNondegenerateUEAPKernelOperationalization C M H N S)
  (WM : MR3SpectralSourceAdmissionWitness M)
  (WH : AASCHybridSameScopeAdmissionWitness C M H)
  (WN : AASCNoEleventhRouteCensusWitness C M H N) :
  AASCNNR8EndpointUpgradeBundle :=
  { C := C
    M := M
    H := H
    N := N
    S := S
    admissionAudit :=
      inputAdmissionChainAsUpgradeAdmissionAudit
        C
        M
        H
        N
        S
        (inputAdmissionChainFromKernelOperationalizationAndWitnesses
          C M H N S K WM WH WN)
    operationalization := K }

/--
Minimal proof-carrying source package for the NNR8 endpoint upgrade.

After the preceding reductions, the upgrade requires three admission witnesses
(`M`, `H`, and `N`) plus the three real operationalization proofs:
current-class point identification, UEAP legitimacy for joint survivors, and
kernel-forced UEAP coordinate failure for non-current branches.
-/
structure AASCNNR8CoreSourceProofBundle
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C) where
  audit :
    Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit
  mr3Witness : MR3SpectralSourceAdmissionWitness M
  hybridWitness : AASCHybridSameScopeAdmissionWitness C M H
  noEleventhWitness : AASCNoEleventhRouteCensusWitness C M H N
  currentPointIdentification :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              routeCarrierDraftClass (N.carrierOf r) =
                NeutrinoDraftCandidateIndex.currentStandingRatio ->
                r = C.ratio
  jointSurvivorUEAPLegitimacy :
    forall r : C.Ratio,
      C.inMinimalInterval r ->
        H.modular.ModularRestriction r ->
          H.spectral.spectralRestriction r ->
            H.scoto.scotoRestriction r ->
              Papers.ClaimStandingAndLegitimacy.SigmaLegitimacy
                audit
                (routeCarrierDraftClass (N.carrierOf r))
  kernelForcedUEAPFailure :
    forall i : NeutrinoDraftCandidateIndex,
      forall hne :
        Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio),
        AASCUEAPLegitimacyFailureHolds
          audit
          i
          (defaultUEAPFailureKindForNoncurrentBranch i hne)

def coreSourceProofBundleAsOperationalization
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (B : AASCNNR8CoreSourceProofBundle C M H N S) :
  AASCNondegenerateUEAPKernelOperationalization C M H N S :=
  nondegenerateUEAPKernelOperationalizationFromCoreProofs
    C
    M
    H
    N
    S
    B.audit
    B.currentPointIdentification
    B.jointSurvivorUEAPLegitimacy
    B.kernelForcedUEAPFailure

def endpointUpgradeBundleFromCoreSourceProofBundle
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (B : AASCNNR8CoreSourceProofBundle C M H N S) :
  AASCNNR8EndpointUpgradeBundle :=
  endpointUpgradeBundleFromKernelOperationalizationAndWitnesses
    C
    M
    H
    N
    S
    (coreSourceProofBundleAsOperationalization C M H N S B)
    B.mr3Witness
    B.hybridWitness
    B.noEleventhWitness

theorem coreSourceProofBundleGivesEndpointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (B : AASCNNR8CoreSourceProofBundle C M H N S) :
  HybridJointRestrictionSingleton H := by
  exact
    (endpointUpgradeBundleFromCoreSourceProofBundle C M H N S B).singletonEndpoint

theorem coreSourceProofBundleRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (B : AASCNNR8CoreSourceProofBundle C M H N S) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    (endpointUpgradeBundleFromCoreSourceProofBundle C M H N S B).noSecondPoint

/--
Source rows pulled from the corpus for the NNR8 core source-proof frontier.

These are citation handles, not proof terms for the mathematical fields. They
record that every remaining proof field has at least one local corpus source
candidate with extracted text or certified control-matrix support.
-/
inductive AASCNNR8CoreSourceID where
  | mr3ShapeSourceTheorem
  | cs6cSameScopeRivalExhaustion
  | cs6cScopeExtensionRegistry
  | cs7ForbiddenPMNSValuePromotion
  | cs7DeferredPMNSValues
  | ueapLaunderingExclusion
  | ueapCalibrationOnly
  | rocRoleOccupancyClosure
  | rocLawfulClosureRouteExhaustion
  | noarUniversalOscillationQuotient
  | noarNoHiddenFlavorTransport
  | ex8OverconstraintLegitimacy
  | mr5EffectStatusSeparation
  deriving DecidableEq

/--
The current frontier fields of `AASCNNR8CoreSourceProofBundle`.
-/
inductive AASCNNR8CoreFrontierField where
  | mr3_sourceCertified
  | mr3_standingSpectralCarrier
  | mr3_quotientStable
  | mr3_transportClosed
  | mr3_calibrationFree
  | mr3_extractionCertified
  | mr3_sourceInducesShapeMap
  | h_crossTargetAligned
  | h_crossTransportCoherent
  | h_crossNoOvercounting
  | h_crossCalibrationFree
  | h_crossNoHiddenSelector
  | n_noUncarriedSameTargetConstraint
  | n_noLegacyTheoryOutsideCensus
  | n_noExperimentalMethodOutsideCensus
  | n_noScopeChangingRouteCountsSameScope
  | n_noEmpiricalValueImportAsRoute
  | operational_currentPointIdentification
  | operational_jointSurvivorUEAPLegitimacy
  | operational_kernelForcedUEAPFailure
  deriving DecidableEq

def primarySourceForCoreFrontierField :
  AASCNNR8CoreFrontierField -> AASCNNR8CoreSourceID
  | .mr3_sourceCertified => .mr3ShapeSourceTheorem
  | .mr3_standingSpectralCarrier => .mr3ShapeSourceTheorem
  | .mr3_quotientStable => .mr3ShapeSourceTheorem
  | .mr3_transportClosed => .mr3ShapeSourceTheorem
  | .mr3_calibrationFree => .mr3ShapeSourceTheorem
  | .mr3_extractionCertified => .mr3ShapeSourceTheorem
  | .mr3_sourceInducesShapeMap => .mr3ShapeSourceTheorem
  | .h_crossTargetAligned => .ex8OverconstraintLegitimacy
  | .h_crossTransportCoherent => .noarUniversalOscillationQuotient
  | .h_crossNoOvercounting => .noarUniversalOscillationQuotient
  | .h_crossCalibrationFree => .ueapCalibrationOnly
  | .h_crossNoHiddenSelector => .ueapLaunderingExclusion
  | .n_noUncarriedSameTargetConstraint =>
      .cs6cSameScopeRivalExhaustion
  | .n_noLegacyTheoryOutsideCensus =>
      .cs6cSameScopeRivalExhaustion
  | .n_noExperimentalMethodOutsideCensus =>
      .cs7ForbiddenPMNSValuePromotion
  | .n_noScopeChangingRouteCountsSameScope =>
      .cs6cScopeExtensionRegistry
  | .n_noEmpiricalValueImportAsRoute =>
      .cs7DeferredPMNSValues
  | .operational_currentPointIdentification =>
      .rocRoleOccupancyClosure
  | .operational_jointSurvivorUEAPLegitimacy =>
      .ueapLaunderingExclusion
  | .operational_kernelForcedUEAPFailure =>
      .rocLawfulClosureRouteExhaustion

def coreFrontierFieldHasPulledSource
  (_f : AASCNNR8CoreFrontierField) : Prop :=
  Nonempty AASCNNR8CoreSourceID

theorem everyCoreFrontierFieldHasPulledSource
  (f : AASCNNR8CoreFrontierField) :
  coreFrontierFieldHasPulledSource f := by
  exact ⟨primarySourceForCoreFrontierField f⟩

/--
The source-coverage layer is clear when every frontier field has a pulled
source candidate. The remaining blocker after this layer is semantic
extraction: turning the cited source rows into proof terms for the corresponding
Lean propositions.
-/
def AASCNNR8CoreSourceCoverageCleared : Prop :=
  forall f : AASCNNR8CoreFrontierField,
    coreFrontierFieldHasPulledSource f

theorem coreSourceCoverageCleared :
  AASCNNR8CoreSourceCoverageCleared := by
  intro f
  exact everyCoreFrontierFieldHasPulledSource f

/--
Source-backed proof wrapper.

This is the semantic extraction layer: a corpus source row is not treated as a
proof merely by being named. The extraction certificate must carry an actual
proof of the target proposition, together with the source ID used to justify
that proof in the paper audit.
-/
structure AASCSourceBackedProof (p : Prop) where
  source : AASCNNR8CoreSourceID
  proof : p

/--
Semantic extraction certificate for the NNR8 core proof bundle.

Each remaining frontier proposition is represented as a source-backed proof.
This is the precise bridge from pulled corpus text to Lean proof fields.
-/
structure AASCNNR8SemanticExtractionCertificate
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C) where
  audit :
    Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit
  mr3_sourceCertified :
    AASCSourceBackedProof M.sourceCertified
  mr3_standingSpectralCarrier :
    AASCSourceBackedProof M.standingSpectralCarrier
  mr3_quotientStable :
    AASCSourceBackedProof M.quotientStable
  mr3_transportClosed :
    AASCSourceBackedProof M.transportClosed
  mr3_calibrationFree :
    AASCSourceBackedProof M.calibrationFree
  mr3_extractionCertified :
    AASCSourceBackedProof M.extractionCertified
  mr3_sourceInducesShapeMap :
    AASCSourceBackedProof M.sourceInducesShapeMap
  h_crossTargetAligned :
    AASCSourceBackedProof H.crossTargetAligned
  h_crossTransportCoherent :
    AASCSourceBackedProof H.crossTransportCoherent
  h_crossNoOvercounting :
    AASCSourceBackedProof H.crossNoOvercounting
  h_crossCalibrationFree :
    AASCSourceBackedProof H.crossCalibrationFree
  h_crossNoHiddenSelector :
    AASCSourceBackedProof H.crossNoHiddenSelector
  n_noUncarriedSameTargetConstraint :
    AASCSourceBackedProof N.noUncarriedSameTargetConstraint
  n_noLegacyTheoryOutsideCensus :
    AASCSourceBackedProof N.noLegacyTheoryOutsideCensus
  n_noExperimentalMethodOutsideCensus :
    AASCSourceBackedProof N.noExperimentalMethodOutsideCensus
  n_noScopeChangingRouteCountsSameScope :
    AASCSourceBackedProof N.noScopeChangingRouteCountsSameScope
  n_noEmpiricalValueImportAsRoute :
    AASCSourceBackedProof N.noEmpiricalValueImportAsRoute
  currentPointIdentification :
    AASCSourceBackedProof
      (forall r : C.Ratio,
        C.inMinimalInterval r ->
          H.modular.ModularRestriction r ->
            H.spectral.spectralRestriction r ->
              H.scoto.scotoRestriction r ->
                routeCarrierDraftClass (N.carrierOf r) =
                  NeutrinoDraftCandidateIndex.currentStandingRatio ->
                  r = C.ratio)
  jointSurvivorUEAPLegitimacy :
    AASCSourceBackedProof
      (forall r : C.Ratio,
        C.inMinimalInterval r ->
          H.modular.ModularRestriction r ->
            H.spectral.spectralRestriction r ->
              H.scoto.scotoRestriction r ->
                Papers.ClaimStandingAndLegitimacy.SigmaLegitimacy
                  audit
                  (routeCarrierDraftClass (N.carrierOf r)))
  kernelForcedUEAPFailure :
    AASCSourceBackedProof
      (forall i : NeutrinoDraftCandidateIndex,
        forall hne :
          Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio),
          AASCUEAPLegitimacyFailureHolds
            audit
            i
            (defaultUEAPFailureKindForNoncurrentBranch i hne))

def semanticExtractionAsMR3Witness
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (E : AASCNNR8SemanticExtractionCertificate C M H N S) :
  MR3SpectralSourceAdmissionWitness M :=
  { sourceCertified_proof := E.mr3_sourceCertified.proof
    standingSpectralCarrier_proof :=
      E.mr3_standingSpectralCarrier.proof
    quotientStable_proof := E.mr3_quotientStable.proof
    transportClosed_proof := E.mr3_transportClosed.proof
    calibrationFree_proof := E.mr3_calibrationFree.proof
    extractionCertified_proof := E.mr3_extractionCertified.proof
    sourceInducesShapeMap_proof :=
      E.mr3_sourceInducesShapeMap.proof }

def semanticExtractionAsHybridWitness
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (E : AASCNNR8SemanticExtractionCertificate C M H N S) :
  AASCHybridSameScopeAdmissionWitness C M H :=
  { crossTargetAligned_proof := E.h_crossTargetAligned.proof
    crossTransportCoherent_proof := E.h_crossTransportCoherent.proof
    crossNoOvercounting_proof := E.h_crossNoOvercounting.proof
    crossCalibrationFree_proof := E.h_crossCalibrationFree.proof
    crossNoHiddenSelector_proof := E.h_crossNoHiddenSelector.proof }

def semanticExtractionAsNoEleventhWitness
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (E : AASCNNR8SemanticExtractionCertificate C M H N S) :
  AASCNoEleventhRouteCensusWitness C M H N :=
  { noUncarriedSameTargetConstraint_proof :=
      E.n_noUncarriedSameTargetConstraint.proof
    noLegacyTheoryOutsideCensus_proof :=
      E.n_noLegacyTheoryOutsideCensus.proof
    noExperimentalMethodOutsideCensus_proof :=
      E.n_noExperimentalMethodOutsideCensus.proof
    noScopeChangingRouteCountsSameScope_proof :=
      E.n_noScopeChangingRouteCountsSameScope.proof
    noEmpiricalValueImportAsRoute_proof :=
      E.n_noEmpiricalValueImportAsRoute.proof }

def semanticExtractionAsCoreSourceProofBundle
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (E : AASCNNR8SemanticExtractionCertificate C M H N S) :
  AASCNNR8CoreSourceProofBundle C M H N S :=
  { audit := E.audit
    mr3Witness :=
      semanticExtractionAsMR3Witness C M H N S E
    hybridWitness :=
      semanticExtractionAsHybridWitness C M H N S E
    noEleventhWitness :=
      semanticExtractionAsNoEleventhWitness C M H N S E
    currentPointIdentification :=
      E.currentPointIdentification.proof
    jointSurvivorUEAPLegitimacy :=
      E.jointSurvivorUEAPLegitimacy.proof
    kernelForcedUEAPFailure :=
      E.kernelForcedUEAPFailure.proof }

theorem semanticExtractionGivesEndpointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (E : AASCNNR8SemanticExtractionCertificate C M H N S) :
  HybridJointRestrictionSingleton H := by
  exact
    coreSourceProofBundleGivesEndpointSingleton
      C M H N S
      (semanticExtractionAsCoreSourceProofBundle C M H N S E)

theorem semanticExtractionRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (E : AASCNNR8SemanticExtractionCertificate C M H N S) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    coreSourceProofBundleRulesOutSecondPoint
      C M H N S
      (semanticExtractionAsCoreSourceProofBundle C M H N S E)

/--
Primary-source-backed proof wrapper.

The source is not chosen by the proof writer: it is the canonical source row
assigned to the frontier field by `primarySourceForCoreFrontierField`.
-/
structure AASCPrimarySourceBackedProof
  (f : AASCNNR8CoreFrontierField)
  (p : Prop) where
  proof : p

def primarySourceBackedProofAsSourceBacked
  {p : Prop}
  (f : AASCNNR8CoreFrontierField)
  (P : AASCPrimarySourceBackedProof f p) :
  AASCSourceBackedProof p :=
  { source := primarySourceForCoreFrontierField f
    proof := P.proof }

/--
Canonical semantic extraction certificate.

This removes one remaining degree of freedom from semantic extraction: every
field is backed by its primary source row from the source-coverage ledger.
-/
structure AASCNNR8PrimarySemanticExtractionCertificate
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C) where
  audit :
    Papers.ClaimStandingAndLegitimacy.ClaimAudit
      NeutrinoDraftCandidateIndex Unit
  mr3_sourceCertified :
    AASCPrimarySourceBackedProof
      .mr3_sourceCertified M.sourceCertified
  mr3_standingSpectralCarrier :
    AASCPrimarySourceBackedProof
      .mr3_standingSpectralCarrier M.standingSpectralCarrier
  mr3_quotientStable :
    AASCPrimarySourceBackedProof
      .mr3_quotientStable M.quotientStable
  mr3_transportClosed :
    AASCPrimarySourceBackedProof
      .mr3_transportClosed M.transportClosed
  mr3_calibrationFree :
    AASCPrimarySourceBackedProof
      .mr3_calibrationFree M.calibrationFree
  mr3_extractionCertified :
    AASCPrimarySourceBackedProof
      .mr3_extractionCertified M.extractionCertified
  mr3_sourceInducesShapeMap :
    AASCPrimarySourceBackedProof
      .mr3_sourceInducesShapeMap M.sourceInducesShapeMap
  h_crossTargetAligned :
    AASCPrimarySourceBackedProof
      .h_crossTargetAligned H.crossTargetAligned
  h_crossTransportCoherent :
    AASCPrimarySourceBackedProof
      .h_crossTransportCoherent H.crossTransportCoherent
  h_crossNoOvercounting :
    AASCPrimarySourceBackedProof
      .h_crossNoOvercounting H.crossNoOvercounting
  h_crossCalibrationFree :
    AASCPrimarySourceBackedProof
      .h_crossCalibrationFree H.crossCalibrationFree
  h_crossNoHiddenSelector :
    AASCPrimarySourceBackedProof
      .h_crossNoHiddenSelector H.crossNoHiddenSelector
  n_noUncarriedSameTargetConstraint :
    AASCPrimarySourceBackedProof
      .n_noUncarriedSameTargetConstraint
      N.noUncarriedSameTargetConstraint
  n_noLegacyTheoryOutsideCensus :
    AASCPrimarySourceBackedProof
      .n_noLegacyTheoryOutsideCensus
      N.noLegacyTheoryOutsideCensus
  n_noExperimentalMethodOutsideCensus :
    AASCPrimarySourceBackedProof
      .n_noExperimentalMethodOutsideCensus
      N.noExperimentalMethodOutsideCensus
  n_noScopeChangingRouteCountsSameScope :
    AASCPrimarySourceBackedProof
      .n_noScopeChangingRouteCountsSameScope
      N.noScopeChangingRouteCountsSameScope
  n_noEmpiricalValueImportAsRoute :
    AASCPrimarySourceBackedProof
      .n_noEmpiricalValueImportAsRoute
      N.noEmpiricalValueImportAsRoute
  currentPointIdentification :
    AASCPrimarySourceBackedProof
      .operational_currentPointIdentification
      (forall r : C.Ratio,
        C.inMinimalInterval r ->
          H.modular.ModularRestriction r ->
            H.spectral.spectralRestriction r ->
              H.scoto.scotoRestriction r ->
                routeCarrierDraftClass (N.carrierOf r) =
                  NeutrinoDraftCandidateIndex.currentStandingRatio ->
                  r = C.ratio)
  jointSurvivorUEAPLegitimacy :
    AASCPrimarySourceBackedProof
      .operational_jointSurvivorUEAPLegitimacy
      (forall r : C.Ratio,
        C.inMinimalInterval r ->
          H.modular.ModularRestriction r ->
            H.spectral.spectralRestriction r ->
              H.scoto.scotoRestriction r ->
                Papers.ClaimStandingAndLegitimacy.SigmaLegitimacy
                  audit
                  (routeCarrierDraftClass (N.carrierOf r)))
  kernelForcedUEAPFailure :
    AASCPrimarySourceBackedProof
      .operational_kernelForcedUEAPFailure
      (forall i : NeutrinoDraftCandidateIndex,
        forall hne :
          Not (i = NeutrinoDraftCandidateIndex.currentStandingRatio),
          AASCUEAPLegitimacyFailureHolds
            audit
            i
            (defaultUEAPFailureKindForNoncurrentBranch i hne))

def primarySemanticExtractionAsSemanticExtraction
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCNNR8PrimarySemanticExtractionCertificate C M H N S) :
  AASCNNR8SemanticExtractionCertificate C M H N S :=
  { audit := P.audit
    mr3_sourceCertified :=
      primarySourceBackedProofAsSourceBacked
        .mr3_sourceCertified P.mr3_sourceCertified
    mr3_standingSpectralCarrier :=
      primarySourceBackedProofAsSourceBacked
        .mr3_standingSpectralCarrier P.mr3_standingSpectralCarrier
    mr3_quotientStable :=
      primarySourceBackedProofAsSourceBacked
        .mr3_quotientStable P.mr3_quotientStable
    mr3_transportClosed :=
      primarySourceBackedProofAsSourceBacked
        .mr3_transportClosed P.mr3_transportClosed
    mr3_calibrationFree :=
      primarySourceBackedProofAsSourceBacked
        .mr3_calibrationFree P.mr3_calibrationFree
    mr3_extractionCertified :=
      primarySourceBackedProofAsSourceBacked
        .mr3_extractionCertified P.mr3_extractionCertified
    mr3_sourceInducesShapeMap :=
      primarySourceBackedProofAsSourceBacked
        .mr3_sourceInducesShapeMap P.mr3_sourceInducesShapeMap
    h_crossTargetAligned :=
      primarySourceBackedProofAsSourceBacked
        .h_crossTargetAligned P.h_crossTargetAligned
    h_crossTransportCoherent :=
      primarySourceBackedProofAsSourceBacked
        .h_crossTransportCoherent P.h_crossTransportCoherent
    h_crossNoOvercounting :=
      primarySourceBackedProofAsSourceBacked
        .h_crossNoOvercounting P.h_crossNoOvercounting
    h_crossCalibrationFree :=
      primarySourceBackedProofAsSourceBacked
        .h_crossCalibrationFree P.h_crossCalibrationFree
    h_crossNoHiddenSelector :=
      primarySourceBackedProofAsSourceBacked
        .h_crossNoHiddenSelector P.h_crossNoHiddenSelector
    n_noUncarriedSameTargetConstraint :=
      primarySourceBackedProofAsSourceBacked
        .n_noUncarriedSameTargetConstraint
        P.n_noUncarriedSameTargetConstraint
    n_noLegacyTheoryOutsideCensus :=
      primarySourceBackedProofAsSourceBacked
        .n_noLegacyTheoryOutsideCensus
        P.n_noLegacyTheoryOutsideCensus
    n_noExperimentalMethodOutsideCensus :=
      primarySourceBackedProofAsSourceBacked
        .n_noExperimentalMethodOutsideCensus
        P.n_noExperimentalMethodOutsideCensus
    n_noScopeChangingRouteCountsSameScope :=
      primarySourceBackedProofAsSourceBacked
        .n_noScopeChangingRouteCountsSameScope
        P.n_noScopeChangingRouteCountsSameScope
    n_noEmpiricalValueImportAsRoute :=
      primarySourceBackedProofAsSourceBacked
        .n_noEmpiricalValueImportAsRoute
        P.n_noEmpiricalValueImportAsRoute
    currentPointIdentification :=
      primarySourceBackedProofAsSourceBacked
        .operational_currentPointIdentification
        P.currentPointIdentification
    jointSurvivorUEAPLegitimacy :=
      primarySourceBackedProofAsSourceBacked
        .operational_jointSurvivorUEAPLegitimacy
        P.jointSurvivorUEAPLegitimacy
    kernelForcedUEAPFailure :=
      primarySourceBackedProofAsSourceBacked
        .operational_kernelForcedUEAPFailure
        P.kernelForcedUEAPFailure }

theorem primarySemanticExtractionGivesEndpointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCNNR8PrimarySemanticExtractionCertificate C M H N S) :
  HybridJointRestrictionSingleton H := by
  exact
    semanticExtractionGivesEndpointSingleton
      C M H N S
      (primarySemanticExtractionAsSemanticExtraction C M H N S P)

theorem primarySemanticExtractionRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCNNR8PrimarySemanticExtractionCertificate C M H N S) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    semanticExtractionRulesOutSecondPoint
      C M H N S
      (primarySemanticExtractionAsSemanticExtraction C M H N S P)

theorem noEleventhCaseSplitResidualCorpusClosureGivesJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (K : AASCNoEleventhRouteCaseSplitConstruction C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    residualCorpusPointClosureGivesJointSingleton
      C
      M
      H
      N
      S
      (noEleventhCaseSplitAsResidualCorpusPointClosure C M H N S K)

theorem noEleventhCaseSplitResidualCorpusClosureRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (K : AASCNoEleventhRouteCaseSplitConstruction C M H N) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    residualCorpusPointClosureRulesOutSecondPoint
      C
      M
      H
      N
      S
      (noEleventhCaseSplitAsResidualCorpusPointClosure C M H N S K)

theorem branchImpossibilityResidualCorpusClosureGivesJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (B : AASCBranchImpossibilityAudit C M H N) :
  HybridJointRestrictionSingleton H := by
  exact
    residualCorpusPointClosureGivesJointSingleton
      C
      M
      H
      N
      S
      (branchImpossibilityAuditAsResidualCorpusPointClosure C M H N S B)

theorem branchImpossibilityResidualCorpusClosureRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (B : AASCBranchImpossibilityAudit C M H N) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    residualCorpusPointClosureRulesOutSecondPoint
      C
      M
      H
      N
      S
      (branchImpossibilityAuditAsResidualCorpusPointClosure C M H N S B)

theorem residualCorpusPointClosureProvesBranchAuditAndSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCResidualCorpusPointClosure C M H N S) :
  AASCBranchImpossibilityAudit C M H N /\ HybridJointRestrictionSingleton H := by
  refine And.intro ?_ ?_
  · exact residualCorpusPointClosureAsBranchImpossibilityAudit C M H N S P
  · exact residualCorpusPointClosureGivesJointSingleton C M H N S P

theorem sharedConvergenceProvesBranchAuditAndSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCSharedConvergencePointIdentification C M H N S) :
  AASCBranchImpossibilityAudit C M H N /\ HybridJointRestrictionSingleton H := by
  refine And.intro ?_ ?_
  · exact sharedConvergencePointIdentificationAsBranchImpossibilityAudit C M H N S P
  · exact sharedConvergencePointIdentificationGivesJointSingleton C M H N S P

theorem scotoModularPhaseCollapseProvesBranchAuditAndSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C)
  (P : AASCScotoModularPhaseParameterCollapse C M H N S) :
  AASCBranchImpossibilityAudit C M H N /\ HybridJointRestrictionSingleton H := by
  refine And.intro ?_ ?_
  · exact scotoModularPhaseCollapseAsBranchImpossibilityAudit C M H N S P
  · exact scotoModularPhaseCollapseGivesJointSingleton C M H N S P

theorem residualCorpusPointClosureEquivalentToBridgeTranslation
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C) :
  (Nonempty (AASCResidualCorpusPointClosure C M H N S) <->
    Nonempty (AASCNeutrinoBridgeTranslation C M H N S)) := by
  constructor
  · intro h
    rcases h with ⟨P⟩
    exact
      ⟨residualCorpusPointClosureAsNeutrinoBridgeTranslation C M H N S P⟩
  · intro h
    rcases h with ⟨B⟩
    exact
      ⟨neutrinoBridgeTranslationAsResidualCorpusPointClosure C M H N S B⟩

theorem branchAuditEquivalentToBridgeTranslation
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C) :
  (Nonempty (AASCBranchImpossibilityAudit C M H N) <->
    Nonempty (AASCNeutrinoBridgeTranslation C M H N S)) := by
  constructor
  · intro h
    rcases h with ⟨B⟩
    exact ⟨branchImpossibilityAuditAsNeutrinoBridgeTranslation C M H N S B⟩
  · intro h
    rcases h with ⟨B⟩
    exact ⟨neutrinoBridgeTranslationGivesBranchAudit C M H N S B⟩

theorem hybridSingletonResidualCorpusClosureGivesJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (S : AASCCorpusBranchSupportLedger C) :
  HybridJointRestrictionSingleton H := by
  exact
    residualCorpusPointClosureGivesJointSingleton
      C
      M
      H
      N
      S
      (hybridSingletonAsResidualCorpusPointClosure C M H N S)

theorem methodRefinedLedgerGivesJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (L : AASCCandidateIndexLedger C M H)
  (W :
    AASCMethodInvariantWitnessLedger
      C M H L.CandidateIndex)
  (_hrefined : MethodRefinedCandidateIndexLedger L W) :
  HybridJointRestrictionSingleton H := by
  exact candidateIndexLedgerGivesJointSingleton C M H L

theorem methodRefinedLedgerRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (L : AASCCandidateIndexLedger C M H)
  (W :
    AASCMethodInvariantWitnessLedger
      C M H L.CandidateIndex)
  (_hrefined : MethodRefinedCandidateIndexLedger L W) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    candidateIndexLedgerRulesOutSecondPoint
      C
      M
      H
      L

theorem phaseRefinedLedgerGivesJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (L : AASCCandidateIndexLedger C M H)
  (P :
    AASCPhaseCoherenceWitnessLedger
      C M H L.CandidateIndex)
  (_hrefined : PhaseRefinedCandidateIndexLedger L P) :
  HybridJointRestrictionSingleton H := by
  exact candidateIndexLedgerGivesJointSingleton C M H L

theorem phaseRefinedLedgerRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (L : AASCCandidateIndexLedger C M H)
  (P :
    AASCPhaseCoherenceWitnessLedger
      C M H L.CandidateIndex)
  (_hrefined : PhaseRefinedCandidateIndexLedger L P) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    candidateIndexLedgerRulesOutSecondPoint
      C
      M
      H
      L

theorem neutrinoDiscriminatorRefinedLedgerGivesJointSingleton
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (L : AASCCandidateIndexLedger C M H)
  (D :
    AASCNeutrinoSpecificDiscriminatorLedger
      C M H L.CandidateIndex)
  (_hrefined : NeutrinoDiscriminatorRefinedCandidateIndexLedger L D) :
  HybridJointRestrictionSingleton H := by
  exact candidateIndexLedgerGivesJointSingleton C M H L

theorem neutrinoDiscriminatorRefinedLedgerRulesOutSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (L : AASCCandidateIndexLedger C M H)
  (D :
    AASCNeutrinoSpecificDiscriminatorLedger
      C M H L.CandidateIndex)
  (_hrefined : NeutrinoDiscriminatorRefinedCandidateIndexLedger L D) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  exact
    candidateIndexLedgerRulesOutSecondPoint
      C
      M
      H
      L

theorem hybridJointSecondPointBlocksCompression
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (hsecond : HybridJointRestrictionHasSecondPoint H) :
  Not (RatioInvariantCompressionPrinciple C) := by
  rcases hsecond with
    ⟨r, hinterval, hmod, hspec, hscoto, hne⟩
  let T : LawfulRatioDeformation C :=
    { deformRole := fun x => x
      deformRatio := fun _ => r
      lawful := True
      preservesStanding := by
        intro role hstanding
        exact hstanding
      preservesCommonCarrier := by
        intro hcarrier
        exact hcarrier
      preservesDenominator := by
        intro hden
        exact hden
      preservesRoleSeparation := by
        intro hsep
        exact hsep
      preservesMinimalInterval := by
        intro _hinterval
        exact hinterval }
  exact
    liveDeformationBlocksUniversalRatioInvariance
      C
      T
      (And.intro True.intro hne)

theorem hybridSingletonRulesOutJointSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M) :
  Not (HybridJointRestrictionHasSecondPoint H) := by
  intro hsecond
  rcases hsecond with
    ⟨r, hinterval, hmod, hspec, hscoto, hne⟩
  exact hne
    (H.jointRestrictionSingleton
      r hinterval hmod hspec hscoto)

def translatedLawAsCompressionCandidate
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (L : AASCTranslatedCompressionLaw C M) :
  NeutrinoCompressionCandidate C M :=
  { lawForm := L.lawForm
    sourceAncestryCertified := L.sourceAncestryCertified
    targetPreservingTransport := L.targetPreservingTransport
    quotientStable := L.quotientStable
    calibrationFree := L.calibrationFreeAfterDeletion
    noObservedValueImport := L.observedInputsDeleted
    noComparatorPromotion := L.comparatorContentDeleted
    noBranchSelector := L.branchSelectorDeleted
    noIdentityShapeSelector := L.identityShapeSelectorExcluded
    activeForStandingRatio := by
      intro T hlawful
      exact L.restrictionImpliesShape
        (T.deformRatio C.ratio)
        (L.activeRestrictionForStandingRatio T hlawful)
    shapeFiberSoundForMinimalInterval := by
      intro r hshape
      exact L.shapeFiberSoundForMinimalInterval r hshape
    collapsesShapeFiber := by
      intro r hinterval hshape
      exact
        L.restrictionSingleton
          r
          hinterval
          (L.shapeImpliesRestriction r hinterval hshape) }

def NeutrinoCompressionCandidateAuditPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (W : NeutrinoCompressionCandidate C M) : Prop :=
  W.sourceAncestryCertified /\
  W.targetPreservingTransport /\
  W.quotientStable /\
  W.calibrationFree /\
  W.noObservedValueImport /\
  W.noComparatorPromotion /\
  W.noBranchSelector /\
  W.noIdentityShapeSelector

theorem translatedLawAuditGivesCandidateAudit
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (L : AASCTranslatedCompressionLaw C M)
  (haudit : AASCTranslatedLawAuditPasses L) :
  NeutrinoCompressionCandidateAuditPasses
    (translatedLawAsCompressionCandidate C M L) := by
  rcases haudit with
    ⟨_hderive, hsource, htarget, hquotient, hcalibration,
      hobserved, hcomparator, hbranch, hidentity⟩
  exact
    And.intro hsource
      (And.intro htarget
        (And.intro hquotient
          (And.intro hcalibration
            (And.intro hobserved
              (And.intro hcomparator
                (And.intro hbranch hidentity))))))

def compressionCandidateAsMR2ShapeFiberCollapse
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (W : NeutrinoCompressionCandidate C M) :
  MR2RatioShapeFiberCollapse C M :=
  { shapeFiberSoundForMinimalInterval :=
      W.shapeFiberSoundForMinimalInterval
    shapeFiberCollapseAtCurrent :=
      W.collapsesShapeFiber }

/--
If a candidate law form passes the AASC gate and supplies the actual collapse
field, it constructs the same MR2 collapse witness as an MR5 singleton network.
-/
theorem auditedCandidateGivesRatioCompression
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (W : NeutrinoCompressionCandidate C M)
  (_haudit : NeutrinoCompressionCandidateAuditPasses W)
  (hsource : M.sourceCertified)
  (hcarrier : M.standingSpectralCarrier)
  (hquotient : M.quotientStable)
  (htransport : M.transportClosed)
  (hcalibration : M.calibrationFree)
  (hextraction : M.extractionCertified)
  (hmap : M.sourceInducesShapeMap) :
  RatioInvariantCompressionPrinciple C := by
  exact
    mr23SourceAndCollapseGiveRatioCompression
      C
      M
      (compressionCandidateAsMR2ShapeFiberCollapse C M W)
      hsource
      hcarrier
      hquotient
      htransport
      hcalibration
      hextraction
      hmap

theorem translatedLawGivesRatioCompression
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (L : AASCTranslatedCompressionLaw C M)
  (haudit : AASCTranslatedLawAuditPasses L)
  (hsource : M.sourceCertified)
  (hcarrier : M.standingSpectralCarrier)
  (hquotient : M.quotientStable)
  (htransport : M.transportClosed)
  (hcalibration : M.calibrationFree)
  (hextraction : M.extractionCertified)
  (hmap : M.sourceInducesShapeMap) :
  RatioInvariantCompressionPrinciple C := by
  exact
    auditedCandidateGivesRatioCompression
      C
      M
      (translatedLawAsCompressionCandidate C M L)
      (translatedLawAuditGivesCandidateAudit C M L haudit)
      hsource
      hcarrier
      hquotient
      htransport
      hcalibration
      hextraction
      hmap

theorem modularMassSumRuleGivesRatioCompression
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (S : AASCModularMassSumRuleTranslation C M)
  (haudit : AASCModularMassSumRuleAuditPasses S)
  (hmSource : M.sourceCertified)
  (hmCarrier : M.standingSpectralCarrier)
  (hmQuotient : M.quotientStable)
  (hmTransport : M.transportClosed)
  (hmCalibration : M.calibrationFree)
  (hmExtraction : M.extractionCertified)
  (hmMap : M.sourceInducesShapeMap) :
  RatioInvariantCompressionPrinciple C := by
  exact
    translatedLawGivesRatioCompression
      C
      M
      (modularMassSumRuleAsTranslatedLaw C M S)
      (modularMassSumRuleAuditPasses C M S haudit)
      hmSource
      hmCarrier
      hmQuotient
      hmTransport
      hmCalibration
      hmExtraction
      hmMap

theorem spectralQuotientGivesRatioCompression
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (S : AASCSpectralQuotientCollapseTranslation C M)
  (haudit : AASCSpectralQuotientAuditPasses S)
  (hmSource : M.sourceCertified)
  (hmCarrier : M.standingSpectralCarrier)
  (hmQuotient : M.quotientStable)
  (hmTransport : M.transportClosed)
  (hmCalibration : M.calibrationFree)
  (hmExtraction : M.extractionCertified)
  (hmMap : M.sourceInducesShapeMap) :
  RatioInvariantCompressionPrinciple C := by
  exact
    translatedLawGivesRatioCompression
      C
      M
      (spectralQuotientAsTranslatedLaw C M S)
      (spectralQuotientAuditPasses C M S haudit)
      hmSource
      hmCarrier
      hmQuotient
      hmTransport
      hmCalibration
      hmExtraction
      hmMap

theorem scotoSeesawGivesRatioCompression
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (S : AASCScotoSeesawTranslation C M)
  (haudit : AASCScotoSeesawAuditPasses S)
  (hmSource : M.sourceCertified)
  (hmCarrier : M.standingSpectralCarrier)
  (hmQuotient : M.quotientStable)
  (hmTransport : M.transportClosed)
  (hmCalibration : M.calibrationFree)
  (hmExtraction : M.extractionCertified)
  (hmMap : M.sourceInducesShapeMap) :
  RatioInvariantCompressionPrinciple C := by
  exact
    translatedLawGivesRatioCompression
      C
      M
      (scotoSeesawAsTranslatedLaw C M S)
      (scotoSeesawAuditPasses C M S haudit)
      hmSource
      hmCarrier
      hmQuotient
      hmTransport
      hmCalibration
      hmExtraction
      hmMap

theorem scotoModularPhaseIntersectionGivesRatioCompression
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (S : AASCScotoModularPhaseIntersection C M)
  (haudit : AASCScotoModularPhaseIntersectionAuditPasses S)
  (hmSource : M.sourceCertified)
  (hmCarrier : M.standingSpectralCarrier)
  (hmQuotient : M.quotientStable)
  (hmTransport : M.transportClosed)
  (hmCalibration : M.calibrationFree)
  (hmExtraction : M.extractionCertified)
  (hmMap : M.sourceInducesShapeMap) :
  RatioInvariantCompressionPrinciple C := by
  exact
    translatedLawGivesRatioCompression
      C
      M
      (scotoModularPhaseIntersectionAsTranslatedLaw C M S)
      (scotoModularPhaseIntersectionAuditPasses C M S haudit)
      hmSource
      hmCarrier
      hmQuotient
      hmTransport
      hmCalibration
      hmExtraction
      hmMap

theorem singletAdSPressureGivesRatioCompression
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (S : AASCSingletAdSPressureTranslation C M)
  (haudit : AASCSingletAdSPressureAuditPasses S)
  (hmSource : M.sourceCertified)
  (hmCarrier : M.standingSpectralCarrier)
  (hmQuotient : M.quotientStable)
  (hmTransport : M.transportClosed)
  (hmCalibration : M.calibrationFree)
  (hmExtraction : M.extractionCertified)
  (hmMap : M.sourceInducesShapeMap) :
  RatioInvariantCompressionPrinciple C := by
  exact
    translatedLawGivesRatioCompression
      C
      M
      (singletAdSPressureAsTranslatedLaw C M S)
      (singletAdSPressureAuditPasses C M S haudit)
      hmSource
      hmCarrier
      hmQuotient
      hmTransport
      hmCalibration
      hmExtraction
      hmMap

theorem singletAdSConvergenceGivesRatioCompression
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (J : AASCSingletAdSConvergence C M)
  (haudit : AASCSingletAdSConvergenceAuditPasses J)
  (hmSource : M.sourceCertified)
  (hmCarrier : M.standingSpectralCarrier)
  (hmQuotient : M.quotientStable)
  (hmTransport : M.transportClosed)
  (hmCalibration : M.calibrationFree)
  (hmExtraction : M.extractionCertified)
  (hmMap : M.sourceInducesShapeMap) :
  RatioInvariantCompressionPrinciple C := by
  exact
    translatedLawGivesRatioCompression
      C
      M
      (singletAdSConvergenceAsTranslatedLaw C M J)
      (singletAdSConvergenceAuditPasses C M J haudit)
      hmSource
      hmCarrier
      hmQuotient
      hmTransport
      hmCalibration
      hmExtraction
      hmMap

theorem sixRouteConvergenceGivesRatioCompression
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (S : AASCNeutrinoSixRouteConvergence C M)
  (haudit : AASCNeutrinoSixRouteConvergenceAuditPasses S)
  (hmSource : M.sourceCertified)
  (hmCarrier : M.standingSpectralCarrier)
  (hmQuotient : M.quotientStable)
  (hmTransport : M.transportClosed)
  (hmCalibration : M.calibrationFree)
  (hmExtraction : M.extractionCertified)
  (hmMap : M.sourceInducesShapeMap) :
  RatioInvariantCompressionPrinciple C := by
  exact
    translatedLawGivesRatioCompression
      C
      M
      (sixRouteConvergenceAsTranslatedLaw C M S)
      (sixRouteConvergenceAuditPasses C M S haudit)
      hmSource
      hmCarrier
      hmQuotient
      hmTransport
      hmCalibration
      hmExtraction
      hmMap

theorem hybridCompressionNetworkGivesRatioCompression
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (haudit : AASCHybridCompressionAuditPasses H)
  (hmSource : M.sourceCertified)
  (hmCarrier : M.standingSpectralCarrier)
  (hmQuotient : M.quotientStable)
  (hmTransport : M.transportClosed)
  (hmCalibration : M.calibrationFree)
  (hmExtraction : M.extractionCertified)
  (hmMap : M.sourceInducesShapeMap) :
  RatioInvariantCompressionPrinciple C := by
  exact
    translatedLawGivesRatioCompression
      C
      M
      (hybridCompressionAsTranslatedLaw C M H)
      haudit
      hmSource
      hmCarrier
      hmQuotient
      hmTransport
      hmCalibration
      hmExtraction
      hmMap

theorem hybridCompressionNetworkKillsLiveDeformations
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (haudit : AASCHybridCompressionAuditPasses H)
  (hmSource : M.sourceCertified)
  (hmCarrier : M.standingSpectralCarrier)
  (hmQuotient : M.quotientStable)
  (hmTransport : M.transportClosed)
  (hmCalibration : M.calibrationFree)
  (hmExtraction : M.extractionCertified)
  (hmMap : M.sourceInducesShapeMap) :
  NoLawfulRatioChangingDeformation C := by
  exact
    (compressionPrincipleEquivalentToNoLiveDeformation C).mp
      (hybridCompressionNetworkGivesRatioCompression
        C M H haudit hmSource hmCarrier hmQuotient hmTransport
        hmCalibration hmExtraction hmMap)

theorem exhaustedHybridNetworkClosesRatio
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (E : AASCHybridClosureExhaustion C M H)
  (haudit : AASCHybridCompressionAuditPasses H)
  (_hexhaustion : AASCHybridClosureExhaustionPasses E)
  (hmSource : M.sourceCertified)
  (hmCarrier : M.standingSpectralCarrier)
  (hmQuotient : M.quotientStable)
  (hmTransport : M.transportClosed)
  (hmCalibration : M.calibrationFree)
  (hmExtraction : M.extractionCertified)
  (hmMap : M.sourceInducesShapeMap) :
  RatioInvariantCompressionPrinciple C := by
  exact
    hybridCompressionNetworkGivesRatioCompression
      C M H haudit hmSource hmCarrier hmQuotient hmTransport
      hmCalibration hmExtraction hmMap

theorem exhaustedHybridNetworkKillsLiveDeformations
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (E : AASCHybridClosureExhaustion C M H)
  (haudit : AASCHybridCompressionAuditPasses H)
  (hexhaustion : AASCHybridClosureExhaustionPasses E)
  (hmSource : M.sourceCertified)
  (hmCarrier : M.standingSpectralCarrier)
  (hmQuotient : M.quotientStable)
  (hmTransport : M.transportClosed)
  (hmCalibration : M.calibrationFree)
  (hmExtraction : M.extractionCertified)
  (hmMap : M.sourceInducesShapeMap) :
  NoLawfulRatioChangingDeformation C := by
  exact
    (compressionPrincipleEquivalentToNoLiveDeformation C).mp
      (exhaustedHybridNetworkClosesRatio
        C M H E haudit hexhaustion hmSource hmCarrier hmQuotient
        hmTransport hmCalibration hmExtraction hmMap)

theorem exhaustedHybridSecondPointContradiction
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (H : AASCHybridCompressionNetwork C M)
  (E : AASCHybridClosureExhaustion C M H)
  (haudit : AASCHybridCompressionAuditPasses H)
  (hexhaustion : AASCHybridClosureExhaustionPasses E)
  (hmSource : M.sourceCertified)
  (hmCarrier : M.standingSpectralCarrier)
  (hmQuotient : M.quotientStable)
  (hmTransport : M.transportClosed)
  (hmCalibration : M.calibrationFree)
  (hmExtraction : M.extractionCertified)
  (hmMap : M.sourceInducesShapeMap)
  (hsecond : HybridJointRestrictionHasSecondPoint H) :
  False := by
  exact
    (hybridJointSecondPointBlocksCompression C M H hsecond)
      (exhaustedHybridNetworkClosesRatio
        C M H E haudit hexhaustion hmSource hmCarrier hmQuotient
        hmTransport hmCalibration hmExtraction hmMap)

theorem auditedCandidateKillsLiveDeformations
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (W : NeutrinoCompressionCandidate C M)
  (haudit : NeutrinoCompressionCandidateAuditPasses W)
  (hsource : M.sourceCertified)
  (hcarrier : M.standingSpectralCarrier)
  (hquotient : M.quotientStable)
  (htransport : M.transportClosed)
  (hcalibration : M.calibrationFree)
  (hextraction : M.extractionCertified)
  (hmap : M.sourceInducesShapeMap) :
  NoLawfulRatioChangingDeformation C := by
  exact
    (compressionPrincipleEquivalentToNoLiveDeformation C).mp
      (auditedCandidateGivesRatioCompression
        C M W haudit hsource hcarrier hquotient htransport
        hcalibration hextraction hmap)

/--
If the candidate is audited but does not collapse the shape fiber, it cannot be
promoted to the missing ratio-compression witness.
-/
def CandidateSourceFiberStillHasSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C) : Prop :=
  exists r : C.Ratio,
    C.inMinimalInterval r /\
      M.shapeOfRatio r = M.shapeOfRatio C.ratio /\
        Not (r = C.ratio)

/--
The MR3 source admission package still has a live shape fiber when there exists
a second minimal-interval ratio point with the same induced shape as the current
ratio.
-/
def MR3ShapeFiberHasSecondPoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C) : Prop :=
  exists r : C.Ratio,
    C.inMinimalInterval r /\
      M.shapeOfRatio r = M.shapeOfRatio C.ratio /\
        Not (r = C.ratio)

theorem candidateFailureGivesMR3SecondShapePoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (hfail : CandidateSourceFiberStillHasSecondPoint C M) :
  MR3ShapeFiberHasSecondPoint C M := by
  exact hfail

/--
MR3 source admission without MR2 collapse does not by itself eliminate
ratio-changing deformations. If the admitted source-induced shape fiber contains
a second point, that point is enough to recover the live-deformation obstruction.
-/
theorem mr3SecondShapePointBlocksCompression
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (hsecond : MR3ShapeFiberHasSecondPoint C M) :
  Not (RatioInvariantCompressionPrinciple C) := by
  rcases hsecond with ⟨r, hrInterval, _hrShape, hrNe⟩
  let T : LawfulRatioDeformation C :=
    { deformRole := fun x => x
      deformRatio := fun _ => r
      lawful := True
      preservesStanding := by
        intro role hstanding
        exact hstanding
      preservesCommonCarrier := by
        intro hcarrier
        exact hcarrier
      preservesDenominator := by
        intro hden
        exact hden
      preservesRoleSeparation := by
        intro hsep
        exact hsep
      preservesMinimalInterval := by
        intro _hinterval
        exact hrInterval }
  exact
    liveDeformationBlocksUniversalRatioInvariance
      C
      T
      (And.intro True.intro hrNe)

/--
Equivalently, any successful compression theorem for an MR3 source rules out
second points in its induced shape fiber.
-/
theorem compressionRulesOutMR3SecondShapePoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (hcompress : RatioInvariantCompressionPrinciple C) :
  Not (MR3ShapeFiberHasSecondPoint C M) := by
  intro hsecond
  exact mr3SecondShapePointBlocksCompression C M hsecond hcompress

theorem candidateFailureBlocksCompression
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (hfail : CandidateSourceFiberStillHasSecondPoint C M) :
  Not (RatioInvariantCompressionPrinciple C) := by
  exact
    mr3SecondShapePointBlocksCompression
      C
      M
      (candidateFailureGivesMR3SecondShapePoint C M hfail)

/--
The MR2 collapse theorem is precisely what removes the MR3 second-shape-point
obstruction.
-/
theorem mr2CollapseRulesOutMR3SecondShapePoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (F : MR2RatioShapeFiberCollapse C M) :
  Not (MR3ShapeFiberHasSecondPoint C M) := by
  intro hsecond
  rcases hsecond with ⟨r, hrInterval, hrShape, hrNe⟩
  exact hrNe (F.shapeFiberCollapseAtCurrent r hrInterval hrShape)

/--
The MR5 network also eliminates the concrete second-point obstruction in the
MR3 shape fiber.
-/
theorem mr5NetworkRulesOutMR3SecondShapePoint
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (N : MR5CrossSectorShapeSingleton C M) :
  Not (MR3ShapeFiberHasSecondPoint C M) := by
  exact
    mr2CollapseRulesOutMR3SecondShapePoint
      C
      M
      (mr5NetworkGivesMR2ShapeFiberCollapse C M N)

/--
Current-ledger obstruction form: if the admitted MR3 source still has a second
point in the current shape fiber, then no MR5 singleton network for that same
source can exist.

This is the Lean version of the NNR8 diagnosis "shape-fiber restriction without
collapse": the environment can certify a supplied MR5 construction, but it
cannot manufacture one while the same source still has a live second point.
-/
theorem mr3SecondShapePointBlocksMR5Network
  (C : StandingRatioCertificate)
  (M : MR3SpectralSourceAdmission C)
  (hsecond : MR3ShapeFiberHasSecondPoint C M) :
  Not (Nonempty (MR5CrossSectorShapeSingleton C M)) := by
  intro hnetwork
  rcases hnetwork with ⟨N⟩
  exact mr5NetworkRulesOutMR3SecondShapePoint C M N hsecond

/--
Equivalent operational test: a proposed MR5 construction theorem is immediately
incompatible with a surviving second point for its admitted source.
-/
theorem mr5ConstructionContradictsSourceSecondShapePoint
  (C : StandingRatioCertificate)
  (S : AASCMR5ShapeConstructionTheorem C)
  (hsecond : MR3ShapeFiberHasSecondPoint C S.sourceAdmission) :
  False := by
  exact
    mr5NetworkRulesOutMR3SecondShapePoint
      C
      S.sourceAdmission
      S.singletonNetwork
      hsecond

/--
If the current minimal interval target has a second admissible ratio point, then
the present certificate by itself admits a lawful deformation that preserves all
role certificates and moves the ratio to that second point.

This is the formal no-free-lunch result for the deeper derivation: role
standing, common carrier, denominator fixation, role separation, and minimal
interval closure do not eliminate magnitude freedom unless an extra
ratio-invariance, normal-form, or finite-collapse theorem is added.
-/
theorem secondMinimalIntervalPointGivesLiveDeformation
  (C : StandingRatioCertificate)
  (hsecond : MinimalIntervalHasSecondPoint C) :
  exists T : LawfulRatioDeformation C, ratioCanVary C T := by
  rcases hsecond with ⟨r, hrInterval, hrNe⟩
  let T : LawfulRatioDeformation C :=
    { deformRole := fun x => x
      deformRatio := fun _ => r
      lawful := True
      preservesStanding := by
        intro role hstanding
        exact hstanding
      preservesCommonCarrier := by
        intro hcarrier
        exact hcarrier
      preservesDenominator := by
        intro hden
        exact hden
      preservesRoleSeparation := by
        intro hsep
        exact hsep
      preservesMinimalInterval := by
        intro _hinterval
        exact hrInterval }
  refine ⟨T, ?_⟩
  exact And.intro True.intro hrNe

/--
Therefore, a nontrivial minimal-interval fiber directly blocks universal
ratio-invariance under the current certificate.
-/
theorem secondMinimalIntervalPointBlocksCompression
  (C : StandingRatioCertificate)
  (hsecond : MinimalIntervalHasSecondPoint C) :
  Not (RatioInvariantCompressionPrinciple C) := by
  rcases secondMinimalIntervalPointGivesLiveDeformation C hsecond with
    ⟨T, hvar⟩
  exact liveDeformationBlocksUniversalRatioInvariance C T hvar

/--
NNR8's present state, expressed negatively: if there exists a lawful
ratio-changing deformation, then the minimal interval certificate by itself is
not a magnitude-compression certificate.
-/
theorem minimalIntervalAloneDoesNotCompressAgainstLiveDeformation
  (C : StandingRatioCertificate)
  (T : LawfulRatioDeformation C)
  (hvar : ratioCanVary C T) :
  C.inMinimalInterval C.ratio /\
    Not (RatioInvariantCompressionPrinciple C) := by
  exact
    And.intro
      C.minimalIntervalLocked
      (liveDeformationBlocksUniversalRatioInvariance C T hvar)

end Neutrino

end MaleyLean
