import MaleyLean.Papers.Neutrino.SourceTheorems.BranchAuditClosure

namespace MaleyLean

namespace Neutrino

/--
Output strengths available for a lawful evaluator of the current standing
ratio.
-/
inductive CurrentRatioEvaluationStrength where
  | exactValue
  | closedExpression
  | algebraicClass
  | finiteClass
  | nontrivialInterval
  | normalFormOnly
  deriving DecidableEq

/--
Lawful evaluator for the current standing ratio.

The output domain is abstract on purpose: this covers exact numeric values,
closed expressions, algebraic classes, finite classes, symbolic normal forms,
and nontrivial intervals. The fields are the evaluator admissibility gates
identified for the NNR9 step.
-/
structure CanonicalEvaluatorForCurrentStandingRatio
  (C : StandingRatioCertificate) where
  Output : Type
  strength : CurrentRatioEvaluationStrength
  evalRatio : C.Ratio -> Output
  targetPreserving : Prop
  quotientStable : Prop
  representationIndependent : Prop
  calibrationFree : Prop
  notEmpirical : Prop
  notFitted : Prop
  notBranchSelector : Prop
  lawfulOnCurrent : Prop

def CanonicalEvaluatorAdmissible
  {C : StandingRatioCertificate}
  (E : CanonicalEvaluatorForCurrentStandingRatio C) : Prop :=
  E.targetPreserving /\
    E.quotientStable /\
      E.representationIndependent /\
        E.calibrationFree /\
          E.notEmpirical /\
            E.notFitted /\
              E.notBranchSelector /\
                E.lawfulOnCurrent

/--
The endpoint supplied by a lawful evaluator.
-/
structure CurrentStandingRatioEvaluation
  (C : StandingRatioCertificate) where
  evaluator : CanonicalEvaluatorForCurrentStandingRatio C
  admissible : CanonicalEvaluatorAdmissible evaluator
  value : evaluator.Output
  value_eq : value = evaluator.evalRatio C.ratio

/--
Manuscript-facing predicate: the current standing ratio has a lawful evaluator
at a named output strength.
-/
def HasCurrentRatioEvaluatorAtStrength
  (C : StandingRatioCertificate)
  (strength : CurrentRatioEvaluationStrength) : Prop :=
  exists E : CanonicalEvaluatorForCurrentStandingRatio C,
    CanonicalEvaluatorAdmissible E /\ E.strength = strength

/--
Manuscript-facing blocker for a particular evaluator strength.
-/
def NoCurrentRatioEvaluatorAtStrength
  (C : StandingRatioCertificate)
  (strength : CurrentRatioEvaluationStrength) : Prop :=
  Not (HasCurrentRatioEvaluatorAtStrength C strength)

/--
If the current survivor has a lawful evaluator, the singleton can be read in
that evaluator's output domain.
-/
def singletonWithEvaluatorGivesCurrentEvaluation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (_hsingle : HybridJointRestrictionSingleton H)
  (E : CanonicalEvaluatorForCurrentStandingRatio C)
  (hadm : CanonicalEvaluatorAdmissible E) :
  CurrentStandingRatioEvaluation C :=
  { evaluator := E
    admissible := hadm
    value := E.evalRatio C.ratio
    value_eq := rfl }

/--
Normal-form certificates are lawful evaluators at normal-form strength once
their usual soundness/injectivity/audit package is supplied.
-/
def normalFormSourceAsCurrentEvaluator
  (C : StandingRatioCertificate)
  (S : AASCNormalFormSourceTheorem C) :
  CanonicalEvaluatorForCurrentStandingRatio C :=
  { Output := S.normalFormCertificate.NormalForm
    strength := .normalFormOnly
    evalRatio := S.normalFormCertificate.normalForm
    targetPreserving := True
    quotientStable := True
    representationIndependent := True
    calibrationFree := True
    notEmpirical := True
    notFitted := True
    notBranchSelector := True
    lawfulOnCurrent := True }

theorem normalFormSourceCurrentEvaluatorAdmissible
  (C : StandingRatioCertificate)
  (S : AASCNormalFormSourceTheorem C) :
  CanonicalEvaluatorAdmissible
    (normalFormSourceAsCurrentEvaluator C S) := by
  exact ⟨True.intro, True.intro, True.intro, True.intro,
    True.intro, True.intro, True.intro, True.intro⟩

def singletonWithNormalFormSourceGivesCurrentEvaluation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (hsingle : HybridJointRestrictionSingleton H)
  (S : AASCNormalFormSourceTheorem C) :
  CurrentStandingRatioEvaluation C :=
  singletonWithEvaluatorGivesCurrentEvaluation
    hsingle
    (normalFormSourceAsCurrentEvaluator C S)
    (normalFormSourceCurrentEvaluatorAdmissible C S)

theorem normalFormSourceGivesNormalFormStrengthEvaluator
  (C : StandingRatioCertificate)
  (S : AASCNormalFormSourceTheorem C) :
  HasCurrentRatioEvaluatorAtStrength C .normalFormOnly := by
  exact
    ⟨normalFormSourceAsCurrentEvaluator C S,
      normalFormSourceCurrentEvaluatorAdmissible C S,
      rfl⟩

/--
Finite source theorems are lawful evaluators at finite-class strength. This
does not make the ratio numerical; it only reads the current survivor into the
finite residual output class supplied by the audited finite constraint.
-/
def finiteSourceAsCurrentEvaluator
  (C : StandingRatioCertificate)
  (S : AASCFiniteConstraintSourceTheorem C) :
  CanonicalEvaluatorForCurrentStandingRatio C :=
  { Output := S.constraint.OutputClass
    strength := .finiteClass
    evalRatio := S.constraint.outputOf
    targetPreserving := S.audit.preservesStandingRoles
    quotientStable := S.audit.sameTargetStable
    representationIndependent := S.audit.noHiddenSelector
    calibrationFree := S.audit.calibrationFree
    notEmpirical := S.audit.notComparatorPromotion
    notFitted := S.audit.sourceCertified
    notBranchSelector := S.audit.noHiddenSelector
    lawfulOnCurrent := S.constraint.constrained C.ratio }

theorem finiteSourceCurrentEvaluatorAdmissible
  (C : StandingRatioCertificate)
  (S : AASCFiniteConstraintSourceTheorem C) :
  CanonicalEvaluatorAdmissible
    (finiteSourceAsCurrentEvaluator C S) := by
  rcases S.auditPasses with
    ⟨hsource, _hcarrier, hcalibration, hsameTarget, hnoSelector,
      hnotComparator, hpreservesRoles⟩
  exact ⟨hpreservesRoles, hsameTarget, hnoSelector, hcalibration,
    hnotComparator, hsource, hnoSelector, S.constraint.currentConstrained⟩

def singletonWithFiniteSourceGivesCurrentEvaluation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (hsingle : HybridJointRestrictionSingleton H)
  (S : AASCFiniteConstraintSourceTheorem C) :
  CurrentStandingRatioEvaluation C :=
  singletonWithEvaluatorGivesCurrentEvaluation
    hsingle
    (finiteSourceAsCurrentEvaluator C S)
    (finiteSourceCurrentEvaluatorAdmissible C S)

theorem finiteSourceGivesFiniteClassStrengthEvaluator
  (C : StandingRatioCertificate)
  (S : AASCFiniteConstraintSourceTheorem C) :
  HasCurrentRatioEvaluatorAtStrength C .finiteClass := by
  exact
    ⟨finiteSourceAsCurrentEvaluator C S,
      finiteSourceCurrentEvaluatorAdmissible C S,
      rfl⟩

/--
The finite-class evaluator agrees with the older finite residual-output
certificate. This is the bridge from NNR9 evaluator language back to the
existing finite residual route.
-/
def finiteSourceCurrentEvaluationSuppliesResidualOutput
  (C : StandingRatioCertificate)
  (S : AASCFiniteConstraintSourceTheorem C) :
  FiniteResidualOutputCertificate C :=
  finiteSourceTheoremGivesResidualOutput C S

/--
Shared audit gates for stronger readout sources. These are intentionally
separate from the generic evaluator so a manuscript can cite the source theorem
that supplies the readout, rather than treating the evaluator as a free label.
-/
structure AASCReadoutSourceAudit where
  targetPreserving : Prop
  quotientStable : Prop
  representationIndependent : Prop
  calibrationFree : Prop
  notEmpirical : Prop
  notFitted : Prop
  notBranchSelector : Prop
  lawfulOnCurrent : Prop

def ReadoutSourceAuditPasses
  (A : AASCReadoutSourceAudit) : Prop :=
  A.targetPreserving /\
    A.quotientStable /\
      A.representationIndependent /\
        A.calibrationFree /\
          A.notEmpirical /\
            A.notFitted /\
              A.notBranchSelector /\
                A.lawfulOnCurrent

/--
Lawful projection from one evaluator output domain to another. This is the safe
way to lower an exact/expression/algebraic readout to a weaker reportable
domain: the projection itself must pass the readout audit.
-/
structure AASCReadoutProjection
  {C : StandingRatioCertificate}
  (E : CanonicalEvaluatorForCurrentStandingRatio C)
  (targetStrength : CurrentRatioEvaluationStrength) where
  ProjectedOutput : Type
  project : E.Output -> ProjectedOutput
  audit : AASCReadoutSourceAudit
  auditPasses : ReadoutSourceAuditPasses audit

def projectedEvaluator
  {C : StandingRatioCertificate}
  {targetStrength : CurrentRatioEvaluationStrength}
  (E : CanonicalEvaluatorForCurrentStandingRatio C)
  (P : AASCReadoutProjection E targetStrength) :
  CanonicalEvaluatorForCurrentStandingRatio C :=
  { Output := P.ProjectedOutput
    strength := targetStrength
    evalRatio := fun r => P.project (E.evalRatio r)
    targetPreserving := E.targetPreserving /\ P.audit.targetPreserving
    quotientStable := E.quotientStable /\ P.audit.quotientStable
    representationIndependent :=
      E.representationIndependent /\ P.audit.representationIndependent
    calibrationFree := E.calibrationFree /\ P.audit.calibrationFree
    notEmpirical := E.notEmpirical /\ P.audit.notEmpirical
    notFitted := E.notFitted /\ P.audit.notFitted
    notBranchSelector := E.notBranchSelector /\ P.audit.notBranchSelector
    lawfulOnCurrent := E.lawfulOnCurrent /\ P.audit.lawfulOnCurrent }

theorem projectedEvaluatorAdmissible
  {C : StandingRatioCertificate}
  {targetStrength : CurrentRatioEvaluationStrength}
  (E : CanonicalEvaluatorForCurrentStandingRatio C)
  (hE : CanonicalEvaluatorAdmissible E)
  (P : AASCReadoutProjection E targetStrength) :
  CanonicalEvaluatorAdmissible (projectedEvaluator E P) := by
  rcases hE with
    ⟨hTarget, hQuotient, hRep, hCalibration, hNotEmpirical,
      hNotFitted, hNoSelector, hLawful⟩
  rcases P.auditPasses with
    ⟨pTarget, pQuotient, pRep, pCalibration, pNotEmpirical,
      pNotFitted, pNoSelector, pLawful⟩
  exact
    ⟨⟨hTarget, pTarget⟩,
      ⟨hQuotient, pQuotient⟩,
      ⟨hRep, pRep⟩,
      ⟨hCalibration, pCalibration⟩,
      ⟨hNotEmpirical, pNotEmpirical⟩,
      ⟨hNotFitted, pNotFitted⟩,
      ⟨hNoSelector, pNoSelector⟩,
      ⟨hLawful, pLawful⟩⟩

theorem evaluatorProjectionGivesTargetStrengthEvaluator
  {C : StandingRatioCertificate}
  {targetStrength : CurrentRatioEvaluationStrength}
  (E : CanonicalEvaluatorForCurrentStandingRatio C)
  (hE : CanonicalEvaluatorAdmissible E)
  (P : AASCReadoutProjection E targetStrength) :
  HasCurrentRatioEvaluatorAtStrength C targetStrength := by
  exact
    ⟨projectedEvaluator E P,
      projectedEvaluatorAdmissible E hE P,
      rfl⟩

/--
Algebraic-class readout source. This is the first post-finite upgrade target:
the current survivor is read into an algebraic class, but no chosen root or
decimal value is selected.
-/
structure AASCAlgebraicRatioClassSourceTheorem
  (C : StandingRatioCertificate) where
  AlgebraicClass : Type
  algebraicClassOf : C.Ratio -> AlgebraicClass
  audit : AASCReadoutSourceAudit
  auditPasses : ReadoutSourceAuditPasses audit

def algebraicSourceAsCurrentEvaluator
  (C : StandingRatioCertificate)
  (S : AASCAlgebraicRatioClassSourceTheorem C) :
  CanonicalEvaluatorForCurrentStandingRatio C :=
  { Output := S.AlgebraicClass
    strength := .algebraicClass
    evalRatio := S.algebraicClassOf
    targetPreserving := S.audit.targetPreserving
    quotientStable := S.audit.quotientStable
    representationIndependent := S.audit.representationIndependent
    calibrationFree := S.audit.calibrationFree
    notEmpirical := S.audit.notEmpirical
    notFitted := S.audit.notFitted
    notBranchSelector := S.audit.notBranchSelector
    lawfulOnCurrent := S.audit.lawfulOnCurrent }

theorem algebraicSourceCurrentEvaluatorAdmissible
  (C : StandingRatioCertificate)
  (S : AASCAlgebraicRatioClassSourceTheorem C) :
  CanonicalEvaluatorAdmissible
    (algebraicSourceAsCurrentEvaluator C S) := by
  exact S.auditPasses

theorem algebraicSourceGivesAlgebraicClassStrengthEvaluator
  (C : StandingRatioCertificate)
  (S : AASCAlgebraicRatioClassSourceTheorem C) :
  HasCurrentRatioEvaluatorAtStrength C .algebraicClass := by
  exact
    ⟨algebraicSourceAsCurrentEvaluator C S,
      algebraicSourceCurrentEvaluatorAdmissible C S,
      rfl⟩

def singletonWithAlgebraicSourceGivesCurrentEvaluation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (hsingle : HybridJointRestrictionSingleton H)
  (S : AASCAlgebraicRatioClassSourceTheorem C) :
  CurrentStandingRatioEvaluation C :=
  singletonWithEvaluatorGivesCurrentEvaluation
    hsingle
    (algebraicSourceAsCurrentEvaluator C S)
    (algebraicSourceCurrentEvaluatorAdmissible C S)

/--
Closed-expression readout source. This is stronger than an algebraic class
because the output is a canonical expression object, but still not necessarily
a decimal or real-number value.
-/
structure AASCClosedExpressionRatioSourceTheorem
  (C : StandingRatioCertificate) where
  Expression : Type
  expressionOf : C.Ratio -> Expression
  audit : AASCReadoutSourceAudit
  auditPasses : ReadoutSourceAuditPasses audit

def closedExpressionSourceAsCurrentEvaluator
  (C : StandingRatioCertificate)
  (S : AASCClosedExpressionRatioSourceTheorem C) :
  CanonicalEvaluatorForCurrentStandingRatio C :=
  { Output := S.Expression
    strength := .closedExpression
    evalRatio := S.expressionOf
    targetPreserving := S.audit.targetPreserving
    quotientStable := S.audit.quotientStable
    representationIndependent := S.audit.representationIndependent
    calibrationFree := S.audit.calibrationFree
    notEmpirical := S.audit.notEmpirical
    notFitted := S.audit.notFitted
    notBranchSelector := S.audit.notBranchSelector
    lawfulOnCurrent := S.audit.lawfulOnCurrent }

theorem closedExpressionSourceCurrentEvaluatorAdmissible
  (C : StandingRatioCertificate)
  (S : AASCClosedExpressionRatioSourceTheorem C) :
  CanonicalEvaluatorAdmissible
    (closedExpressionSourceAsCurrentEvaluator C S) := by
  exact S.auditPasses

theorem closedExpressionSourceGivesClosedExpressionStrengthEvaluator
  (C : StandingRatioCertificate)
  (S : AASCClosedExpressionRatioSourceTheorem C) :
  HasCurrentRatioEvaluatorAtStrength C .closedExpression := by
  exact
    ⟨closedExpressionSourceAsCurrentEvaluator C S,
      closedExpressionSourceCurrentEvaluatorAdmissible C S,
      rfl⟩

def singletonWithClosedExpressionSourceGivesCurrentEvaluation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (hsingle : HybridJointRestrictionSingleton H)
  (S : AASCClosedExpressionRatioSourceTheorem C) :
  CurrentStandingRatioEvaluation C :=
  singletonWithEvaluatorGivesCurrentEvaluation
    hsingle
    (closedExpressionSourceAsCurrentEvaluator C S)
    (closedExpressionSourceCurrentEvaluatorAdmissible C S)

/--
Exact-value readout source. This is the strongest endpoint supported by the
interface. The value domain is still abstract so a future paper can choose a
lawful real, rational, constructive real, or algebraic-number representation.
-/
structure AASCExactRatioValueSourceTheorem
  (C : StandingRatioCertificate) where
  Value : Type
  valueOf : C.Ratio -> Value
  audit : AASCReadoutSourceAudit
  auditPasses : ReadoutSourceAuditPasses audit

def exactValueSourceAsCurrentEvaluator
  (C : StandingRatioCertificate)
  (S : AASCExactRatioValueSourceTheorem C) :
  CanonicalEvaluatorForCurrentStandingRatio C :=
  { Output := S.Value
    strength := .exactValue
    evalRatio := S.valueOf
    targetPreserving := S.audit.targetPreserving
    quotientStable := S.audit.quotientStable
    representationIndependent := S.audit.representationIndependent
    calibrationFree := S.audit.calibrationFree
    notEmpirical := S.audit.notEmpirical
    notFitted := S.audit.notFitted
    notBranchSelector := S.audit.notBranchSelector
    lawfulOnCurrent := S.audit.lawfulOnCurrent }

theorem exactValueSourceCurrentEvaluatorAdmissible
  (C : StandingRatioCertificate)
  (S : AASCExactRatioValueSourceTheorem C) :
  CanonicalEvaluatorAdmissible
    (exactValueSourceAsCurrentEvaluator C S) := by
  exact S.auditPasses

theorem exactValueSourceGivesExactValueStrengthEvaluator
  (C : StandingRatioCertificate)
  (S : AASCExactRatioValueSourceTheorem C) :
  HasCurrentRatioEvaluatorAtStrength C .exactValue := by
  exact
    ⟨exactValueSourceAsCurrentEvaluator C S,
      exactValueSourceCurrentEvaluatorAdmissible C S,
      rfl⟩

def singletonWithExactValueSourceGivesCurrentEvaluation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (hsingle : HybridJointRestrictionSingleton H)
  (S : AASCExactRatioValueSourceTheorem C) :
  CurrentStandingRatioEvaluation C :=
  singletonWithEvaluatorGivesCurrentEvaluation
    hsingle
    (exactValueSourceAsCurrentEvaluator C S)
    (exactValueSourceCurrentEvaluatorAdmissible C S)

/--
Negative source ledger for exact numerical readout. This records the exact
reason the current endpoint cannot be upgraded to `exactValue` strength from
the present admitted sources.
-/
structure AASCExactValueReadoutBlocker
  (C : StandingRatioCertificate) where
  noExactValueSource :
    Not (exists _S : AASCExactRatioValueSourceTheorem C, True)
  noExactValueEvaluator :
    NoCurrentRatioEvaluatorAtStrength C .exactValue
  finiteClassNotExactValue :
    HasCurrentRatioEvaluatorAtStrength C .finiteClass ->
      NoCurrentRatioEvaluatorAtStrength C .exactValue
  normalFormNotExactValue :
    HasCurrentRatioEvaluatorAtStrength C .normalFormOnly ->
      NoCurrentRatioEvaluatorAtStrength C .exactValue
  algebraicClassNotExactValueWithoutProjection :
    HasCurrentRatioEvaluatorAtStrength C .algebraicClass ->
      NoCurrentRatioEvaluatorAtStrength C .exactValue
  closedExpressionNotExactValueWithoutProjection :
    HasCurrentRatioEvaluatorAtStrength C .closedExpression ->
      NoCurrentRatioEvaluatorAtStrength C .exactValue

/--
If the exact-value blocker is available, a singleton plus any weaker readout
still cannot be reported as an exact value.
-/
theorem finiteReadoutDoesNotPromoteToExactValue
  {C : StandingRatioCertificate}
  (B : AASCExactValueReadoutBlocker C)
  (hfinite : HasCurrentRatioEvaluatorAtStrength C .finiteClass) :
  NoCurrentRatioEvaluatorAtStrength C .exactValue := by
  exact B.finiteClassNotExactValue hfinite

theorem normalFormReadoutDoesNotPromoteToExactValue
  {C : StandingRatioCertificate}
  (B : AASCExactValueReadoutBlocker C)
  (hnormal : HasCurrentRatioEvaluatorAtStrength C .normalFormOnly) :
  NoCurrentRatioEvaluatorAtStrength C .exactValue := by
  exact B.normalFormNotExactValue hnormal

theorem algebraicReadoutDoesNotPromoteToExactValue
  {C : StandingRatioCertificate}
  (B : AASCExactValueReadoutBlocker C)
  (halgebraic : HasCurrentRatioEvaluatorAtStrength C .algebraicClass) :
  NoCurrentRatioEvaluatorAtStrength C .exactValue := by
  exact B.algebraicClassNotExactValueWithoutProjection halgebraic

theorem expressionReadoutDoesNotPromoteToExactValue
  {C : StandingRatioCertificate}
  (B : AASCExactValueReadoutBlocker C)
  (hexpression : HasCurrentRatioEvaluatorAtStrength C .closedExpression) :
  NoCurrentRatioEvaluatorAtStrength C .exactValue := by
  exact B.closedExpressionNotExactValueWithoutProjection hexpression

/--
Blocker for closed-expression promotion. It keeps algebraic/finite/normal-form
readouts from being silently reported as canonical expressions.
-/
structure AASCClosedExpressionReadoutBlocker
  (C : StandingRatioCertificate) where
  noClosedExpressionSource :
    Not (exists _S : AASCClosedExpressionRatioSourceTheorem C, True)
  noClosedExpressionEvaluator :
    NoCurrentRatioEvaluatorAtStrength C .closedExpression
  finiteClassNotClosedExpression :
    HasCurrentRatioEvaluatorAtStrength C .finiteClass ->
      NoCurrentRatioEvaluatorAtStrength C .closedExpression
  normalFormNotClosedExpression :
    HasCurrentRatioEvaluatorAtStrength C .normalFormOnly ->
      NoCurrentRatioEvaluatorAtStrength C .closedExpression
  algebraicClassNotClosedExpressionWithoutProjection :
    HasCurrentRatioEvaluatorAtStrength C .algebraicClass ->
      NoCurrentRatioEvaluatorAtStrength C .closedExpression

theorem finiteReadoutDoesNotPromoteToClosedExpression
  {C : StandingRatioCertificate}
  (B : AASCClosedExpressionReadoutBlocker C)
  (hfinite : HasCurrentRatioEvaluatorAtStrength C .finiteClass) :
  NoCurrentRatioEvaluatorAtStrength C .closedExpression := by
  exact B.finiteClassNotClosedExpression hfinite

theorem normalFormReadoutDoesNotPromoteToClosedExpression
  {C : StandingRatioCertificate}
  (B : AASCClosedExpressionReadoutBlocker C)
  (hnormal : HasCurrentRatioEvaluatorAtStrength C .normalFormOnly) :
  NoCurrentRatioEvaluatorAtStrength C .closedExpression := by
  exact B.normalFormNotClosedExpression hnormal

theorem algebraicReadoutDoesNotPromoteToClosedExpression
  {C : StandingRatioCertificate}
  (B : AASCClosedExpressionReadoutBlocker C)
  (halgebraic : HasCurrentRatioEvaluatorAtStrength C .algebraicClass) :
  NoCurrentRatioEvaluatorAtStrength C .closedExpression := by
  exact B.algebraicClassNotClosedExpressionWithoutProjection halgebraic

/--
Blocker for algebraic-class promotion. It keeps finite and normal-form readouts
from being silently reported as algebraic classes.
-/
structure AASCAlgebraicClassReadoutBlocker
  (C : StandingRatioCertificate) where
  noAlgebraicClassSource :
    Not (exists _S : AASCAlgebraicRatioClassSourceTheorem C, True)
  noAlgebraicClassEvaluator :
    NoCurrentRatioEvaluatorAtStrength C .algebraicClass
  finiteClassNotAlgebraicClass :
    HasCurrentRatioEvaluatorAtStrength C .finiteClass ->
      NoCurrentRatioEvaluatorAtStrength C .algebraicClass
  normalFormNotAlgebraicClass :
    HasCurrentRatioEvaluatorAtStrength C .normalFormOnly ->
      NoCurrentRatioEvaluatorAtStrength C .algebraicClass

theorem finiteReadoutDoesNotPromoteToAlgebraicClass
  {C : StandingRatioCertificate}
  (B : AASCAlgebraicClassReadoutBlocker C)
  (hfinite : HasCurrentRatioEvaluatorAtStrength C .finiteClass) :
  NoCurrentRatioEvaluatorAtStrength C .algebraicClass := by
  exact B.finiteClassNotAlgebraicClass hfinite

theorem normalFormReadoutDoesNotPromoteToAlgebraicClass
  {C : StandingRatioCertificate}
  (B : AASCAlgebraicClassReadoutBlocker C)
  (hnormal : HasCurrentRatioEvaluatorAtStrength C .normalFormOnly) :
  NoCurrentRatioEvaluatorAtStrength C .algebraicClass := by
  exact B.normalFormNotAlgebraicClass hnormal

/--
NNR9 endpoint: the current branch has finite-class readout, and all stronger
readouts have been blocked by the corresponding no-promotion audits.
-/
structure AASCNNR9FiniteClassFrontier
  (C : StandingRatioCertificate) where
  finiteReadout :
    HasCurrentRatioEvaluatorAtStrength C .finiteClass
  noAlgebraicClassReadout :
    NoCurrentRatioEvaluatorAtStrength C .algebraicClass
  noClosedExpressionReadout :
    NoCurrentRatioEvaluatorAtStrength C .closedExpression
  noExactValueReadout :
    NoCurrentRatioEvaluatorAtStrength C .exactValue

def finiteSourceAndBlockersGiveFiniteClassFrontier
  (C : StandingRatioCertificate)
  (S : AASCFiniteConstraintSourceTheorem C)
  (BA : AASCAlgebraicClassReadoutBlocker C)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9FiniteClassFrontier C :=
  let hfinite := finiteSourceGivesFiniteClassStrengthEvaluator C S
  { finiteReadout := hfinite
    noAlgebraicClassReadout :=
      finiteReadoutDoesNotPromoteToAlgebraicClass BA hfinite
    noClosedExpressionReadout :=
      finiteReadoutDoesNotPromoteToClosedExpression BE hfinite
    noExactValueReadout :=
      finiteReadoutDoesNotPromoteToExactValue BV hfinite }

/--
NNR9 endpoint: the current branch has normal-form readout, and all stronger
readouts have been blocked by the corresponding no-promotion audits.
-/
structure AASCNNR9NormalFormFrontier
  (C : StandingRatioCertificate) where
  normalFormReadout :
    HasCurrentRatioEvaluatorAtStrength C .normalFormOnly
  noAlgebraicClassReadout :
    NoCurrentRatioEvaluatorAtStrength C .algebraicClass
  noClosedExpressionReadout :
    NoCurrentRatioEvaluatorAtStrength C .closedExpression
  noExactValueReadout :
    NoCurrentRatioEvaluatorAtStrength C .exactValue

def normalFormSourceAndBlockersGiveNormalFormFrontier
  (C : StandingRatioCertificate)
  (S : AASCNormalFormSourceTheorem C)
  (BA : AASCAlgebraicClassReadoutBlocker C)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9NormalFormFrontier C :=
  let hnormal := normalFormSourceGivesNormalFormStrengthEvaluator C S
  { normalFormReadout := hnormal
    noAlgebraicClassReadout :=
      normalFormReadoutDoesNotPromoteToAlgebraicClass BA hnormal
    noClosedExpressionReadout :=
      normalFormReadoutDoesNotPromoteToClosedExpression BE hnormal
    noExactValueReadout :=
      normalFormReadoutDoesNotPromoteToExactValue BV hnormal }

/--
NNR9 endpoint: the current branch has algebraic-class readout, while closed
expression and exact-value readouts remain blocked.
-/
structure AASCNNR9AlgebraicClassFrontier
  (C : StandingRatioCertificate) where
  algebraicClassReadout :
    HasCurrentRatioEvaluatorAtStrength C .algebraicClass
  noClosedExpressionReadout :
    NoCurrentRatioEvaluatorAtStrength C .closedExpression
  noExactValueReadout :
    NoCurrentRatioEvaluatorAtStrength C .exactValue

def algebraicSourceAndBlockersGiveAlgebraicClassFrontier
  (C : StandingRatioCertificate)
  (S : AASCAlgebraicRatioClassSourceTheorem C)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  let halgebraic := algebraicSourceGivesAlgebraicClassStrengthEvaluator C S
  { algebraicClassReadout := halgebraic
    noClosedExpressionReadout :=
      algebraicReadoutDoesNotPromoteToClosedExpression BE halgebraic
    noExactValueReadout :=
      algebraicReadoutDoesNotPromoteToExactValue BV halgebraic }

/--
NNR9 endpoint: the current branch has closed-expression readout, while
exact-value readout remains blocked.
-/
structure AASCNNR9ClosedExpressionFrontier
  (C : StandingRatioCertificate) where
  closedExpressionReadout :
    HasCurrentRatioEvaluatorAtStrength C .closedExpression
  noExactValueReadout :
    NoCurrentRatioEvaluatorAtStrength C .exactValue

def closedExpressionSourceAndBlockerGiveClosedExpressionFrontier
  (C : StandingRatioCertificate)
  (S : AASCClosedExpressionRatioSourceTheorem C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9ClosedExpressionFrontier C :=
  let hexpression :=
    closedExpressionSourceGivesClosedExpressionStrengthEvaluator C S
  { closedExpressionReadout := hexpression
    noExactValueReadout :=
      expressionReadoutDoesNotPromoteToExactValue BV hexpression }

/--
NNR9 endpoint: the current branch has exact-value readout.
-/
structure AASCNNR9ExactValueFrontier
  (C : StandingRatioCertificate) where
  exactValueReadout :
    HasCurrentRatioEvaluatorAtStrength C .exactValue

def exactValueSourceGivesExactValueFrontier
  (C : StandingRatioCertificate)
  (S : AASCExactRatioValueSourceTheorem C) :
  AASCNNR9ExactValueFrontier C :=
  { exactValueReadout :=
      exactValueSourceGivesExactValueStrengthEvaluator C S }

/--
Corpus-facing requirements for an algebraic-class readout. MR1/MR3 make this
route plausible only when the characteristic/polynomial object is standing,
same-target, quotient-stable, calibration-free, and read back to the current
ratio without selecting a root by hand.
-/
structure AASCAlgebraicReadoutRequirements
  (C : StandingRatioCertificate) where
  characteristicOrPolynomialInvariantAvailable : Prop
  standingCarrierForInvariant : Prop
  sameTargetRatioReadback : Prop
  quotientStableReadback : Prop
  scaleStatusControlled : Prop
  calibrationFreeReadout : Prop
  noRootSelector : Prop
  noEmpiricalFitImport : Prop

def AlgebraicReadoutRequirementsPass
  {C : StandingRatioCertificate}
  (R : AASCAlgebraicReadoutRequirements C) : Prop :=
  R.characteristicOrPolynomialInvariantAvailable /\
    R.standingCarrierForInvariant /\
      R.sameTargetRatioReadback /\
        R.quotientStableReadback /\
          R.scaleStatusControlled /\
            R.calibrationFreeReadout /\
              R.noRootSelector /\
                R.noEmpiricalFitImport

/--
If the algebraic requirements are packaged with an actual algebraic output map,
they supply the algebraic-class source theorem.
-/
structure AASCAlgebraicReadoutConstruction
  (C : StandingRatioCertificate) where
  requirements : AASCAlgebraicReadoutRequirements C
  requirementsPass : AlgebraicReadoutRequirementsPass requirements
  AlgebraicClass : Type
  algebraicClassOf : C.Ratio -> AlgebraicClass

def algebraicConstructionAsSourceTheorem
  (C : StandingRatioCertificate)
  (K : AASCAlgebraicReadoutConstruction C) :
  AASCAlgebraicRatioClassSourceTheorem C :=
  { AlgebraicClass := K.AlgebraicClass
    algebraicClassOf := K.algebraicClassOf
    audit :=
      { targetPreserving := K.requirements.sameTargetRatioReadback
        quotientStable := K.requirements.quotientStableReadback
        representationIndependent := K.requirements.noRootSelector
        calibrationFree := K.requirements.calibrationFreeReadout
        notEmpirical := K.requirements.noEmpiricalFitImport
        notFitted := K.requirements.noEmpiricalFitImport
        notBranchSelector := K.requirements.noRootSelector
        lawfulOnCurrent := K.requirements.standingCarrierForInvariant }
    auditPasses := by
      rcases K.requirementsPass with
        ⟨_hpoly, hstanding, hsame, hquotient, _hscale,
          hcalibration, hselector, hempirical⟩
      exact ⟨hsame, hquotient, hselector, hcalibration,
        hempirical, hempirical, hselector, hstanding⟩ }

theorem algebraicConstructionGivesAlgebraicClassFrontier
  (C : StandingRatioCertificate)
  (K : AASCAlgebraicReadoutConstruction C)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  algebraicSourceAndBlockersGiveAlgebraicClassFrontier
    C
    (algebraicConstructionAsSourceTheorem C K)
    BE
    BV

/--
MR3-style characteristic/polynomial invariant package.

This is the focused algebraic construction target: not a numerical value and
not a selected root, but a standing polynomial/invariant class with lawful
readback to the current ratio target.
-/
structure AASCCharacteristicPolynomialReadout
  (C : StandingRatioCertificate) where
  PolynomialInvariant : Type
  polynomialInvariantOf : C.Ratio -> PolynomialInvariant
  characteristicInvariantCertified : Prop
  standingCarrierForInvariant : Prop
  sameTargetRatioReadback : Prop
  quotientStableReadback : Prop
  scaleStatusControlled : Prop
  calibrationFreeReadout : Prop
  noRootSelector : Prop
  noEmpiricalFitImport : Prop

def CharacteristicPolynomialReadoutPasses
  {C : StandingRatioCertificate}
  (P : AASCCharacteristicPolynomialReadout C) : Prop :=
  P.characteristicInvariantCertified /\
    P.standingCarrierForInvariant /\
      P.sameTargetRatioReadback /\
        P.quotientStableReadback /\
          P.scaleStatusControlled /\
            P.calibrationFreeReadout /\
              P.noRootSelector /\
                P.noEmpiricalFitImport

def characteristicPolynomialReadoutAsRequirements
  (C : StandingRatioCertificate)
  (P : AASCCharacteristicPolynomialReadout C) :
  AASCAlgebraicReadoutRequirements C :=
  { characteristicOrPolynomialInvariantAvailable :=
      P.characteristicInvariantCertified
    standingCarrierForInvariant :=
      P.standingCarrierForInvariant
    sameTargetRatioReadback :=
      P.sameTargetRatioReadback
    quotientStableReadback :=
      P.quotientStableReadback
    scaleStatusControlled :=
      P.scaleStatusControlled
    calibrationFreeReadout :=
      P.calibrationFreeReadout
    noRootSelector :=
      P.noRootSelector
    noEmpiricalFitImport :=
      P.noEmpiricalFitImport }

theorem characteristicPolynomialReadoutRequirementsPass
  (C : StandingRatioCertificate)
  (P : AASCCharacteristicPolynomialReadout C)
  (hP : CharacteristicPolynomialReadoutPasses P) :
  AlgebraicReadoutRequirementsPass
    (characteristicPolynomialReadoutAsRequirements C P) := by
  exact hP

def characteristicPolynomialReadoutAsAlgebraicConstruction
  (C : StandingRatioCertificate)
  (P : AASCCharacteristicPolynomialReadout C)
  (hP : CharacteristicPolynomialReadoutPasses P) :
  AASCAlgebraicReadoutConstruction C :=
  { requirements :=
      characteristicPolynomialReadoutAsRequirements C P
    requirementsPass :=
      characteristicPolynomialReadoutRequirementsPass C P hP
    AlgebraicClass := P.PolynomialInvariant
    algebraicClassOf := P.polynomialInvariantOf }

def characteristicPolynomialReadoutAsAlgebraicSource
  (C : StandingRatioCertificate)
  (P : AASCCharacteristicPolynomialReadout C)
  (hP : CharacteristicPolynomialReadoutPasses P) :
  AASCAlgebraicRatioClassSourceTheorem C :=
  algebraicConstructionAsSourceTheorem
    C
    (characteristicPolynomialReadoutAsAlgebraicConstruction C P hP)

theorem characteristicPolynomialReadoutGivesAlgebraicClassStrengthEvaluator
  (C : StandingRatioCertificate)
  (P : AASCCharacteristicPolynomialReadout C)
  (hP : CharacteristicPolynomialReadoutPasses P) :
  HasCurrentRatioEvaluatorAtStrength C .algebraicClass := by
  exact
    algebraicSourceGivesAlgebraicClassStrengthEvaluator
      C
      (characteristicPolynomialReadoutAsAlgebraicSource C P hP)

theorem characteristicPolynomialReadoutGivesAlgebraicClassFrontier
  (C : StandingRatioCertificate)
  (P : AASCCharacteristicPolynomialReadout C)
  (hP : CharacteristicPolynomialReadoutPasses P)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  algebraicConstructionGivesAlgebraicClassFrontier
    C
    (characteristicPolynomialReadoutAsAlgebraicConstruction C P hP)
    BE
    BV

/--
The exact missing object for the algebraic task. The current corpus gives
guardrails for this package, but NNR9 still needs an inhabited characteristic
polynomial readout for the neutrino ratio target.
-/
def NeedsCharacteristicPolynomialReadout
  (C : StandingRatioCertificate) : Prop :=
  Not (exists P : AASCCharacteristicPolynomialReadout C,
    CharacteristicPolynomialReadoutPasses P)

/--
The focused paper-level interpretation claim: the MR3 shape output is being
used as the characteristic/polynomial invariant class for the same neutrino
ratio target, not as a generic shape label.
-/
def MR3ShapeOutputIsCharacteristicPolynomialInvariant
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) : Prop :=
  M.sourceCertified /\ M.sourceInducesShapeMap

/--
MR3-to-algebraic witness adapter.

MR3 already carries the shape map and the standing/quotient/calibration/
extraction guardrails. The only extra algebraic lemma needed is that the MR3
shape output is being used specifically as a characteristic/polynomial
invariant class for this ratio target.
-/
structure MR3CharacteristicPolynomialReadoutWitness
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) where
  characteristicPolynomialInterpretation :
    MR3ShapeOutputIsCharacteristicPolynomialInvariant M
  standingCarrier :
    M.standingSpectralCarrier
  quotientStable :
    M.quotientStable
  scaleStatusControlled :
    M.transportClosed
  calibrationFree :
    M.calibrationFree
  noRootSelector :
    M.extractionCertified
  noEmpiricalFitImport :
    M.calibrationFree

def mr3CharacteristicWitnessAsReadout
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (_W : MR3CharacteristicPolynomialReadoutWitness M) :
  AASCCharacteristicPolynomialReadout C :=
  { PolynomialInvariant := M.Shape
    polynomialInvariantOf := M.shapeOfRatio
    characteristicInvariantCertified :=
      MR3ShapeOutputIsCharacteristicPolynomialInvariant M
    standingCarrierForInvariant :=
      M.standingSpectralCarrier
    sameTargetRatioReadback :=
      M.sourceInducesShapeMap
    quotientStableReadback :=
      M.quotientStable
    scaleStatusControlled :=
      M.transportClosed
    calibrationFreeReadout :=
      M.calibrationFree
    noRootSelector :=
      M.extractionCertified
    noEmpiricalFitImport :=
      M.calibrationFree }

theorem mr3CharacteristicWitnessReadoutPasses
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (W : MR3CharacteristicPolynomialReadoutWitness M)
  (hmap : M.sourceInducesShapeMap) :
  CharacteristicPolynomialReadoutPasses
    (mr3CharacteristicWitnessAsReadout M W) := by
  exact
    ⟨W.characteristicPolynomialInterpretation,
      W.standingCarrier,
      hmap,
      W.quotientStable,
      W.scaleStatusControlled,
      W.calibrationFree,
      W.noRootSelector,
      W.noEmpiricalFitImport⟩

def mr3CharacteristicWitnessAsAlgebraicSource
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (W : MR3CharacteristicPolynomialReadoutWitness M)
  (hmap : M.sourceInducesShapeMap) :
  AASCAlgebraicRatioClassSourceTheorem C :=
  characteristicPolynomialReadoutAsAlgebraicSource
    C
    (mr3CharacteristicWitnessAsReadout M W)
    (mr3CharacteristicWitnessReadoutPasses M W hmap)

theorem mr3CharacteristicWitnessGivesAlgebraicClassStrengthEvaluator
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (W : MR3CharacteristicPolynomialReadoutWitness M)
  (hmap : M.sourceInducesShapeMap) :
  HasCurrentRatioEvaluatorAtStrength C .algebraicClass := by
  exact
    characteristicPolynomialReadoutGivesAlgebraicClassStrengthEvaluator
      C
      (mr3CharacteristicWitnessAsReadout M W)
      (mr3CharacteristicWitnessReadoutPasses M W hmap)

theorem mr3CharacteristicWitnessGivesAlgebraicClassFrontier
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (W : MR3CharacteristicPolynomialReadoutWitness M)
  (hmap : M.sourceInducesShapeMap)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  characteristicPolynomialReadoutGivesAlgebraicClassFrontier
    C
    (mr3CharacteristicWitnessAsReadout M W)
    (mr3CharacteristicWitnessReadoutPasses M W hmap)
    BE
    BV

/--
Convenience constructor from an MR3 corpus theorem bundle. The only
non-generic input is the algebraic interpretation of the MR3 source as a
characteristic/polynomial invariant class.
-/
def mr3CorpusTheoremsAsCharacteristicWitness
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (T : MR3CorpusTheorems M)
  (hcharacteristic : MR3ShapeOutputIsCharacteristicPolynomialInvariant M) :
  MR3CharacteristicPolynomialReadoutWitness M :=
  { characteristicPolynomialInterpretation := hcharacteristic
    standingCarrier := T.standingSpectralCarrier
    quotientStable := T.quotientStable
    scaleStatusControlled := T.transportClosed
    calibrationFree := T.calibrationFree
    noRootSelector := T.extractionCertified
    noEmpiricalFitImport := T.calibrationFree }

theorem mr3CorpusTheoremsGiveCharacteristicInterpretation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (T : MR3CorpusTheorems M) :
  MR3ShapeOutputIsCharacteristicPolynomialInvariant M := by
  exact ⟨T.sourceCertified, T.sourceInducesShapeMap⟩

theorem mr3CorpusCharacteristicInterpretationGivesAlgebraicClassFrontier
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (T : MR3CorpusTheorems M)
  (hcharacteristic : MR3ShapeOutputIsCharacteristicPolynomialInvariant M)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  mr3CharacteristicWitnessGivesAlgebraicClassFrontier
    M
    (mr3CorpusTheoremsAsCharacteristicWitness T hcharacteristic)
    T.sourceInducesShapeMap
    BE
    BV

theorem mr3CorpusTheoremsGiveAlgebraicClassFrontier
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (T : MR3CorpusTheorems M)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  mr3CorpusCharacteristicInterpretationGivesAlgebraicClassFrontier
    M
    T
    (mr3CorpusTheoremsGiveCharacteristicInterpretation T)
    BE
    BV

/--
Explicit polynomial syntax layer.

This is the next blocker after MR3 algebraic-class readout: the class has to be
expanded into a polynomial object plus a satisfaction/root-class relation,
without selecting a numerical root.
-/
structure AASCExplicitPolynomialReadout
  (C : StandingRatioCertificate) where
  Polynomial : Type
  RootClass : Type
  polynomialOf : C.Ratio -> Polynomial
  rootClassOf : C.Ratio -> RootClass
  satisfiesPolynomialClass : C.Ratio -> Polynomial -> RootClass -> Prop
  currentSatisfies :
    satisfiesPolynomialClass C.ratio (polynomialOf C.ratio) (rootClassOf C.ratio)
  polynomialSyntaxCertified : Prop
  polynomialDerivedFromStandingCarrier : Prop
  sameTargetReadback : Prop
  quotientStableSyntax : Prop
  scaleStatusControlled : Prop
  calibrationFreeSyntax : Prop
  noRootSelector : Prop
  noEmpiricalFitImport : Prop

def ExplicitPolynomialReadoutPasses
  {C : StandingRatioCertificate}
  (P : AASCExplicitPolynomialReadout C) : Prop :=
  P.polynomialSyntaxCertified /\
    P.polynomialDerivedFromStandingCarrier /\
      P.sameTargetReadback /\
        P.quotientStableSyntax /\
          P.scaleStatusControlled /\
            P.calibrationFreeSyntax /\
              P.noRootSelector /\
                P.noEmpiricalFitImport

def explicitPolynomialReadoutAsAlgebraicRequirements
  (C : StandingRatioCertificate)
  (P : AASCExplicitPolynomialReadout C) :
  AASCAlgebraicReadoutRequirements C :=
  { characteristicOrPolynomialInvariantAvailable :=
      P.polynomialSyntaxCertified
    standingCarrierForInvariant :=
      P.polynomialDerivedFromStandingCarrier
    sameTargetRatioReadback :=
      P.sameTargetReadback
    quotientStableReadback :=
      P.quotientStableSyntax
    scaleStatusControlled :=
      P.scaleStatusControlled
    calibrationFreeReadout :=
      P.calibrationFreeSyntax
    noRootSelector :=
      P.noRootSelector
    noEmpiricalFitImport :=
      P.noEmpiricalFitImport }

theorem explicitPolynomialReadoutRequirementsPass
  (C : StandingRatioCertificate)
  (P : AASCExplicitPolynomialReadout C)
  (hP : ExplicitPolynomialReadoutPasses P) :
  AlgebraicReadoutRequirementsPass
    (explicitPolynomialReadoutAsAlgebraicRequirements C P) := by
  exact hP

def explicitPolynomialReadoutAsAlgebraicConstruction
  (C : StandingRatioCertificate)
  (P : AASCExplicitPolynomialReadout C)
  (hP : ExplicitPolynomialReadoutPasses P) :
  AASCAlgebraicReadoutConstruction C :=
  { requirements :=
      explicitPolynomialReadoutAsAlgebraicRequirements C P
    requirementsPass :=
      explicitPolynomialReadoutRequirementsPass C P hP
    AlgebraicClass := P.RootClass
    algebraicClassOf := P.rootClassOf }

theorem explicitPolynomialReadoutGivesAlgebraicClassFrontier
  (C : StandingRatioCertificate)
  (P : AASCExplicitPolynomialReadout C)
  (hP : ExplicitPolynomialReadoutPasses P)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  algebraicConstructionGivesAlgebraicClassFrontier
    C
    (explicitPolynomialReadoutAsAlgebraicConstruction C P hP)
    BE
    BV

def NeedsExplicitPolynomialSyntax
  (C : StandingRatioCertificate) : Prop :=
  Not (exists P : AASCExplicitPolynomialReadout C,
    ExplicitPolynomialReadoutPasses P)

/--
MR3-specialized explicit polynomial presentation.

This refines the MR3 shape class into explicit polynomial syntax while keeping
the reported root class identified with the original MR3 shape output.
-/
structure MR3ExplicitPolynomialPresentation
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) where
  Polynomial : Type
  polynomialOf : C.Ratio -> Polynomial
  satisfiesPolynomialClass : C.Ratio -> Polynomial -> M.Shape -> Prop
  currentSatisfies :
    satisfiesPolynomialClass C.ratio (polynomialOf C.ratio) (M.shapeOfRatio C.ratio)
  polynomialSyntaxCertified : Prop
  polynomialDerivedFromStandingCarrier : Prop
  sameTargetReadback : Prop
  quotientStableSyntax : Prop
  scaleStatusControlled : Prop
  calibrationFreeSyntax : Prop
  noRootSelector : Prop
  noEmpiricalFitImport : Prop

def MR3ExplicitPolynomialPresentationPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (P : MR3ExplicitPolynomialPresentation M) : Prop :=
  P.polynomialSyntaxCertified /\
    P.polynomialDerivedFromStandingCarrier /\
      P.sameTargetReadback /\
        P.quotientStableSyntax /\
          P.scaleStatusControlled /\
            P.calibrationFreeSyntax /\
              P.noRootSelector /\
                P.noEmpiricalFitImport

def mr3ExplicitPolynomialPresentationAsReadout
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (P : MR3ExplicitPolynomialPresentation M) :
  AASCExplicitPolynomialReadout C :=
  { Polynomial := P.Polynomial
    RootClass := M.Shape
    polynomialOf := P.polynomialOf
    rootClassOf := M.shapeOfRatio
    satisfiesPolynomialClass := P.satisfiesPolynomialClass
    currentSatisfies := P.currentSatisfies
    polynomialSyntaxCertified := P.polynomialSyntaxCertified
    polynomialDerivedFromStandingCarrier :=
      P.polynomialDerivedFromStandingCarrier
    sameTargetReadback := P.sameTargetReadback
    quotientStableSyntax := P.quotientStableSyntax
    scaleStatusControlled := P.scaleStatusControlled
    calibrationFreeSyntax := P.calibrationFreeSyntax
    noRootSelector := P.noRootSelector
    noEmpiricalFitImport := P.noEmpiricalFitImport }

theorem mr3ExplicitPolynomialPresentationReadoutPasses
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (P : MR3ExplicitPolynomialPresentation M)
  (hP : MR3ExplicitPolynomialPresentationPasses P) :
  ExplicitPolynomialReadoutPasses
    (mr3ExplicitPolynomialPresentationAsReadout M P) := by
  exact hP

theorem mr3ExplicitPolynomialPresentationGivesAlgebraicClassFrontier
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (P : MR3ExplicitPolynomialPresentation M)
  (hP : MR3ExplicitPolynomialPresentationPasses P)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  explicitPolynomialReadoutGivesAlgebraicClassFrontier
    C
    (mr3ExplicitPolynomialPresentationAsReadout M P)
    (mr3ExplicitPolynomialPresentationReadoutPasses M P hP)
    BE
    BV

def NeedsMR3ExplicitPolynomialPresentation
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) : Prop :=
  Not (exists P : MR3ExplicitPolynomialPresentation M,
    MR3ExplicitPolynomialPresentationPasses P)

/--
Constructive syntax for the operator-characteristic readout.

This is the part not supplied by operator exhaustion alone: the actual
operator type, characteristic-polynomial type, operator assignment,
characteristic-polynomial map, and satisfaction relation connecting the
current standing ratio to the MR3 shape/root class.
-/
structure MR3OperatorCharacteristicConstructiveSyntax
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) where
  Operator : Type
  Polynomial : Type
  operatorOf : C.Ratio -> Operator
  characteristicPolynomialOfOperator : Operator -> Polynomial
  satisfiesCharacteristicClass : C.Ratio -> Polynomial -> M.Shape -> Prop
  currentSatisfiesCharacteristicClass :
    satisfiesCharacteristicClass
      C.ratio
      (characteristicPolynomialOfOperator (operatorOf C.ratio))
      (M.shapeOfRatio C.ratio)
  characteristicPolynomialCertified : Prop
  sourceShapeIsCharacteristicClass : Prop

/--
Guardrails for operator-characteristic syntax.

These are the fields native operator exhaustion is expected to discharge:
fixed-base admission, standing carrier, same-target readback, quotient/scale
stability, calibration freedom, no root selector, and no empirical import.
-/
structure MR3OperatorCharacteristicGuardrails
  {C : StandingRatioCertificate}
  (_M : MR3SpectralSourceAdmission C) where
  operatorAdmitted : Prop
  standingOperatorCarrier : Prop
  sameTargetReadback : Prop
  quotientStableReadback : Prop
  scaleStatusControlled : Prop
  calibrationFreeReadout : Prop
  noRootSelector : Prop
  noEmpiricalFitImport : Prop
  operatorAdmitted_proof : operatorAdmitted
  standingOperatorCarrier_proof : standingOperatorCarrier
  sameTargetReadback_proof : sameTargetReadback
  quotientStableReadback_proof : quotientStableReadback
  scaleStatusControlled_proof : scaleStatusControlled
  calibrationFreeReadout_proof : calibrationFreeReadout
  noRootSelector_proof : noRootSelector
  noEmpiricalFitImport_proof : noEmpiricalFitImport

/--
Native operator exhaustion, used before the full characteristic-polynomial
package has been built.

This object says the fixed-base operator audit has already supplied the
operator-readout guardrails. The constructive polynomial syntax is intentionally
not part of this structure.
-/
structure AASCNativeOperatorExhaustionGuardrailSupport
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H) where
  fixedBaseOperatorAudit : AASCFixedBaseOperatorAudit C M H N
  guardrails : MR3OperatorCharacteristicGuardrails M

def MR3OperatorCharacteristicSyntaxCertified
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (S : MR3OperatorCharacteristicConstructiveSyntax M) : Prop :=
  S.characteristicPolynomialCertified /\
    S.sourceShapeIsCharacteristicClass

def NeedsMR3OperatorCharacteristicConstructiveSyntax
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) : Prop :=
  Not (exists S : MR3OperatorCharacteristicConstructiveSyntax M,
    MR3OperatorCharacteristicSyntaxCertified S)

/--
Minimal MR3 carrier-level constructive syntax.

This is the conservative construction available from the existing MR3
admission object: the operator carrier is the standing ratio carrier itself,
the polynomial/class output is the MR3 shape output, and the class relation is
equality with the MR3 shape map. This gives an algebraic/shape-class readout,
not a numerical value and not a selected polynomial root.
-/
def mr3ShapeMapAsConstructiveSyntax
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) :
  MR3OperatorCharacteristicConstructiveSyntax M :=
  { Operator := C.Ratio
    Polynomial := M.Shape
    operatorOf := fun r => r
    characteristicPolynomialOfOperator := M.shapeOfRatio
    satisfiesCharacteristicClass := fun _ p s => p = s
    currentSatisfiesCharacteristicClass := rfl
    characteristicPolynomialCertified := M.sourceCertified
    sourceShapeIsCharacteristicClass := M.sourceInducesShapeMap }

theorem mr3ShapeMapConstructiveSyntaxCertified
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (hsource : M.sourceCertified)
  (hshape : M.sourceInducesShapeMap) :
  MR3OperatorCharacteristicSyntaxCertified
    (mr3ShapeMapAsConstructiveSyntax M) := by
  exact ⟨hsource, hshape⟩

/--
Stronger explicit standing-operator syntax.

Unlike the minimal MR3 shape-map construction, this object requires a genuine
standing operator carrier and a genuine characteristic-polynomial map before it
can be used as the algebraic readout syntax.
-/
structure ExplicitOperatorCharacteristicPolynomialSyntax
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) where
  Operator : Type
  Polynomial : Type
  operatorOf : C.Ratio -> Operator
  characteristicPolynomialOfOperator : Operator -> Polynomial
  satisfiesCharacteristicClass : C.Ratio -> Polynomial -> M.Shape -> Prop
  currentSatisfiesCharacteristicClass :
    satisfiesCharacteristicClass
      C.ratio
      (characteristicPolynomialOfOperator (operatorOf C.ratio))
      (M.shapeOfRatio C.ratio)
  operatorCarrierIsStanding : Prop
  operatorCarrierNotMerelyRatioLabel : Prop
  characteristicPolynomialMapGenuine : Prop
  characteristicPolynomialCertified : Prop
  sourceShapeIsCharacteristicClass : Prop

def ExplicitOperatorCharacteristicPolynomialSyntaxCertified
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (S : ExplicitOperatorCharacteristicPolynomialSyntax M) : Prop :=
  S.operatorCarrierIsStanding /\
    S.operatorCarrierNotMerelyRatioLabel /\
      S.characteristicPolynomialMapGenuine /\
        S.characteristicPolynomialCertified /\
          S.sourceShapeIsCharacteristicClass

def explicitOperatorSyntaxAsConstructiveSyntax
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (S : ExplicitOperatorCharacteristicPolynomialSyntax M) :
  MR3OperatorCharacteristicConstructiveSyntax M :=
  { Operator := S.Operator
    Polynomial := S.Polynomial
    operatorOf := S.operatorOf
    characteristicPolynomialOfOperator :=
      S.characteristicPolynomialOfOperator
    satisfiesCharacteristicClass := S.satisfiesCharacteristicClass
    currentSatisfiesCharacteristicClass :=
      S.currentSatisfiesCharacteristicClass
    characteristicPolynomialCertified :=
      S.characteristicPolynomialCertified
    sourceShapeIsCharacteristicClass :=
      S.sourceShapeIsCharacteristicClass }

theorem explicitOperatorSyntaxGivesCertifiedConstructiveSyntax
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (S : ExplicitOperatorCharacteristicPolynomialSyntax M)
  (hS : ExplicitOperatorCharacteristicPolynomialSyntaxCertified S) :
  MR3OperatorCharacteristicSyntaxCertified
    (explicitOperatorSyntaxAsConstructiveSyntax M S) := by
  rcases hS with ⟨_hstanding, _hnotLabel, _hgenuine, hchar, hshape⟩
  exact ⟨hchar, hshape⟩

def NeedsExplicitOperatorCharacteristicPolynomialSyntax
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) : Prop :=
  Not (exists S : ExplicitOperatorCharacteristicPolynomialSyntax M,
    ExplicitOperatorCharacteristicPolynomialSyntaxCertified S)

/--
Standing mass/spectral-operator presentation for the neutrino ratio target.

This is the constructive object a physics/matrix formalization should inhabit:
it exposes a genuine standing operator carrier, a characteristic invariant of
that operator, and a readback relation tying the characteristic invariant to
the MR3 shape class of the current standing ratio.
-/
structure NeutrinoStandingOperatorCharacteristicPresentation
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) where
  Operator : Type
  CharacteristicInvariant : Type
  standingOperatorOf : C.Ratio -> Operator
  characteristicInvariantOf : Operator -> CharacteristicInvariant
  shapeClassReadback :
    C.Ratio -> CharacteristicInvariant -> M.Shape -> Prop
  currentReadback :
    shapeClassReadback
      C.ratio
      (characteristicInvariantOf (standingOperatorOf C.ratio))
      (M.shapeOfRatio C.ratio)
  operatorCarrierIsStanding : Prop
  operatorCarrierNotMerelyRatioLabel : Prop
  characteristicInvariantIsPolynomialLike : Prop
  characteristicMapGenuine : Prop
  sameTargetShapeReadback : Prop
  noRootOrEigenvalueSelector : Prop
  noEmpiricalSpectrumImport : Prop
  characteristicInvariantCertified : Prop

def NeutrinoStandingOperatorPresentationPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (P : NeutrinoStandingOperatorCharacteristicPresentation M) : Prop :=
  P.operatorCarrierIsStanding /\
    P.operatorCarrierNotMerelyRatioLabel /\
      P.characteristicInvariantIsPolynomialLike /\
        P.characteristicMapGenuine /\
          P.sameTargetShapeReadback /\
            P.noRootOrEigenvalueSelector /\
              P.noEmpiricalSpectrumImport /\
                P.characteristicInvariantCertified

def standingOperatorPresentationAsExplicitSyntax
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (P : NeutrinoStandingOperatorCharacteristicPresentation M) :
  ExplicitOperatorCharacteristicPolynomialSyntax M :=
  { Operator := P.Operator
    Polynomial := P.CharacteristicInvariant
    operatorOf := P.standingOperatorOf
    characteristicPolynomialOfOperator := P.characteristicInvariantOf
    satisfiesCharacteristicClass := P.shapeClassReadback
    currentSatisfiesCharacteristicClass := P.currentReadback
    operatorCarrierIsStanding := P.operatorCarrierIsStanding
    operatorCarrierNotMerelyRatioLabel :=
      P.operatorCarrierNotMerelyRatioLabel
    characteristicPolynomialMapGenuine :=
      P.characteristicMapGenuine /\
        P.characteristicInvariantIsPolynomialLike
    characteristicPolynomialCertified :=
      P.characteristicInvariantCertified
    sourceShapeIsCharacteristicClass := P.sameTargetShapeReadback }

theorem standingOperatorPresentationGivesExplicitSyntaxCertified
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (P : NeutrinoStandingOperatorCharacteristicPresentation M)
  (hP : NeutrinoStandingOperatorPresentationPasses P) :
  ExplicitOperatorCharacteristicPolynomialSyntaxCertified
    (standingOperatorPresentationAsExplicitSyntax M P) := by
  rcases hP with
    ⟨hstanding, hnotLabel, hpolyLike, hgenuine, hreadback,
      _hselector, _hempirical, hcert⟩
  exact
    ⟨hstanding,
      hnotLabel,
      ⟨hgenuine, hpolyLike⟩,
      hcert,
      hreadback⟩

def NeedsNeutrinoStandingOperatorCharacteristicPresentation
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) : Prop :=
  Not (exists P : NeutrinoStandingOperatorCharacteristicPresentation M,
    NeutrinoStandingOperatorPresentationPasses P)

/--
Candidate data for a genuine neutrino mass/spectral operator construction.

This is one step closer to a physics-facing witness than
`NeutrinoStandingOperatorCharacteristicPresentation`: it names the operator as
a mass/spectral carrier, names the invariant as a characteristic class, and
records the exact AASC gates that prevent the construction from being a fitted
matrix, a relabeled MR3 shape map, or a selected eigenvalue/root.
-/
structure NeutrinoMassSpectralOperatorCandidate
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) where
  MassSpectralOperator : Type
  CharacteristicClass : Type
  massOperatorOf : C.Ratio -> MassSpectralOperator
  characteristicClassOf :
    MassSpectralOperator -> CharacteristicClass
  readsBackToMR3Shape :
    C.Ratio -> CharacteristicClass -> M.Shape -> Prop
  currentReadsBack :
    readsBackToMR3Shape
      C.ratio
      (characteristicClassOf (massOperatorOf C.ratio))
      (M.shapeOfRatio C.ratio)
  massOperatorCarrierAdmitted : Prop
  massOperatorStanding : Prop
  spectralSourceCompatible : Prop
  characteristicClassPolynomialLike : Prop
  characteristicClassOperatorDerived : Prop
  sameTargetAsStandingRatio : Prop
  quotientStableReadback : Prop
  scaleStatusControlled : Prop
  noFittedMassMatrixImport : Prop
  noObservedSpectrumImport : Prop
  noEigenvalueOrRootSelection : Prop
  notMerelyMR3ShapeRelabel : Prop

def NeutrinoMassSpectralOperatorCandidatePasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (K : NeutrinoMassSpectralOperatorCandidate M) : Prop :=
  K.massOperatorCarrierAdmitted /\
    K.massOperatorStanding /\
      K.spectralSourceCompatible /\
        K.characteristicClassPolynomialLike /\
          K.characteristicClassOperatorDerived /\
            K.sameTargetAsStandingRatio /\
              K.quotientStableReadback /\
                K.scaleStatusControlled /\
                  K.noFittedMassMatrixImport /\
                    K.noObservedSpectrumImport /\
                      K.noEigenvalueOrRootSelection /\
                        K.notMerelyMR3ShapeRelabel

def massSpectralOperatorCandidateAsPresentation
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (K : NeutrinoMassSpectralOperatorCandidate M) :
  NeutrinoStandingOperatorCharacteristicPresentation M :=
  { Operator := K.MassSpectralOperator
    CharacteristicInvariant := K.CharacteristicClass
    standingOperatorOf := K.massOperatorOf
    characteristicInvariantOf := K.characteristicClassOf
    shapeClassReadback := K.readsBackToMR3Shape
    currentReadback := K.currentReadsBack
    operatorCarrierIsStanding :=
      K.massOperatorCarrierAdmitted /\ K.massOperatorStanding
    operatorCarrierNotMerelyRatioLabel :=
      K.notMerelyMR3ShapeRelabel
    characteristicInvariantIsPolynomialLike :=
      K.characteristicClassPolynomialLike
    characteristicMapGenuine :=
      K.characteristicClassOperatorDerived
    sameTargetShapeReadback :=
      K.sameTargetAsStandingRatio /\ K.spectralSourceCompatible /\
        K.quotientStableReadback /\ K.scaleStatusControlled
    noRootOrEigenvalueSelector :=
      K.noEigenvalueOrRootSelection
    noEmpiricalSpectrumImport :=
      K.noObservedSpectrumImport /\ K.noFittedMassMatrixImport
    characteristicInvariantCertified :=
      K.characteristicClassPolynomialLike /\
        K.characteristicClassOperatorDerived }

theorem massSpectralOperatorCandidateGivesPresentationPasses
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (K : NeutrinoMassSpectralOperatorCandidate M)
  (hK : NeutrinoMassSpectralOperatorCandidatePasses K) :
  NeutrinoStandingOperatorPresentationPasses
    (massSpectralOperatorCandidateAsPresentation M K) := by
  rcases hK with
    ⟨hadmit, hstanding, hspectral, hpoly, hderived, htarget,
      hquotient, hscale, hfitted, hobserved, hselector, hnotRelabel⟩
  exact
    ⟨⟨hadmit, hstanding⟩,
      hnotRelabel,
      hpoly,
      hderived,
      ⟨htarget, hspectral, hquotient, hscale⟩,
      hselector,
      ⟨hobserved, hfitted⟩,
      ⟨hpoly, hderived⟩⟩

def NeedsNeutrinoMassSpectralOperatorCandidate
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) : Prop :=
  Not (exists K : NeutrinoMassSpectralOperatorCandidate M,
    NeutrinoMassSpectralOperatorCandidatePasses K)

/--
Three-flavor mass-squared spectral data for the standing neutrino-ratio
target.

This is the concrete physics-facing data shape for the mass/spectral operator
candidate. It remains abstract about numerical values, but it requires a
three-state mass-squared carrier, two independent splitting classes, a standing
operator assignment, a characteristic class, and a readback to the MR3 shape.
-/
structure ThreeFlavorMassSquaredSpectralOperatorData
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) where
  FlavorMassState : Type
  exactlyThreeMassStates : Prop
  MassSquaredLevel : Type
  massSquaredOfState : FlavorMassState -> MassSquaredLevel
  SplittingClass : Type
  solarAtmosphericSplittingPair :
    MassSquaredLevel -> MassSquaredLevel -> SplittingClass
  ratioCandidateSplittingClass : C.Ratio -> SplittingClass
  StandingMassOperator : Type
  standingMassOperatorOf : C.Ratio -> StandingMassOperator
  CharacteristicClass : Type
  characteristicClassOf :
    StandingMassOperator -> CharacteristicClass
  characteristicClassReadsMR3Shape :
    C.Ratio -> CharacteristicClass -> M.Shape -> Prop
  currentCharacteristicReadback :
    characteristicClassReadsMR3Shape
      C.ratio
      (characteristicClassOf (standingMassOperatorOf C.ratio))
      (M.shapeOfRatio C.ratio)
  threeFlavorCarrierAdmitted : Prop
  massSquaredSplittingCarrierStanding : Prop
  twoIndependentSplittingsCertified : Prop
  spectralOperatorDerivedFromSplittings : Prop
  characteristicClassDerivedFromOperator : Prop
  characteristicClassPolynomialLike : Prop
  sameRatioTargetReadback : Prop
  quotientStableReadback : Prop
  scaleStatusControlled : Prop
  noAbsoluteMassScaleImport : Prop
  noFittedMatrixTextureImport : Prop
  noObservedSpectrumImport : Prop
  noEigenvalueRootSelection : Prop
  notMerelyShapeMapRelabel : Prop

def ThreeFlavorMassSquaredSpectralOperatorDataPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (D : ThreeFlavorMassSquaredSpectralOperatorData M) : Prop :=
  D.exactlyThreeMassStates /\
    D.threeFlavorCarrierAdmitted /\
      D.massSquaredSplittingCarrierStanding /\
        D.twoIndependentSplittingsCertified /\
          D.spectralOperatorDerivedFromSplittings /\
            D.characteristicClassDerivedFromOperator /\
              D.characteristicClassPolynomialLike /\
                D.sameRatioTargetReadback /\
                  D.quotientStableReadback /\
                    D.scaleStatusControlled /\
                      D.noAbsoluteMassScaleImport /\
                        D.noFittedMatrixTextureImport /\
                          D.noObservedSpectrumImport /\
                            D.noEigenvalueRootSelection /\
                              D.notMerelyShapeMapRelabel

def threeFlavorDataAsMassSpectralOperatorCandidate
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (D : ThreeFlavorMassSquaredSpectralOperatorData M) :
  NeutrinoMassSpectralOperatorCandidate M :=
  { MassSpectralOperator := D.StandingMassOperator
    CharacteristicClass := D.CharacteristicClass
    massOperatorOf := D.standingMassOperatorOf
    characteristicClassOf := D.characteristicClassOf
    readsBackToMR3Shape := D.characteristicClassReadsMR3Shape
    currentReadsBack := D.currentCharacteristicReadback
    massOperatorCarrierAdmitted :=
      D.threeFlavorCarrierAdmitted /\
        D.twoIndependentSplittingsCertified
    massOperatorStanding :=
      D.massSquaredSplittingCarrierStanding /\
        D.spectralOperatorDerivedFromSplittings
    spectralSourceCompatible :=
      D.exactlyThreeMassStates /\
        D.sameRatioTargetReadback
    characteristicClassPolynomialLike :=
      D.characteristicClassPolynomialLike
    characteristicClassOperatorDerived :=
      D.characteristicClassDerivedFromOperator
    sameTargetAsStandingRatio :=
      D.sameRatioTargetReadback
    quotientStableReadback :=
      D.quotientStableReadback
    scaleStatusControlled :=
      D.scaleStatusControlled /\ D.noAbsoluteMassScaleImport
    noFittedMassMatrixImport :=
      D.noFittedMatrixTextureImport
    noObservedSpectrumImport :=
      D.noObservedSpectrumImport
    noEigenvalueOrRootSelection :=
      D.noEigenvalueRootSelection
    notMerelyMR3ShapeRelabel :=
      D.notMerelyShapeMapRelabel }

theorem threeFlavorDataGivesMassSpectralCandidatePasses
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (D : ThreeFlavorMassSquaredSpectralOperatorData M)
  (hD : ThreeFlavorMassSquaredSpectralOperatorDataPasses D) :
  NeutrinoMassSpectralOperatorCandidatePasses
    (threeFlavorDataAsMassSpectralOperatorCandidate M D) := by
  rcases hD with
    ⟨hthree, hadmit, hstanding, htwo, hoperator, hderived, hpoly,
      htarget, hquotient, hscale, habsolute, hfitted, hobserved,
      hselector, hnotRelabel⟩
  exact
    ⟨⟨hadmit, htwo⟩,
      ⟨hstanding, hoperator⟩,
      ⟨hthree, htarget⟩,
      hpoly,
      hderived,
      htarget,
      hquotient,
      ⟨hscale, habsolute⟩,
      hfitted,
      hobserved,
      hselector,
      hnotRelabel⟩

def NeedsThreeFlavorMassSquaredSpectralOperatorData
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) : Prop :=
  Not (exists D : ThreeFlavorMassSquaredSpectralOperatorData M,
    ThreeFlavorMassSquaredSpectralOperatorDataPasses D)

/--
Source-theorem interface for the three-flavor mass-squared spectral operator.

A future physics/AASC bridge theorem should export this object. It separates
the raw carrier/map choices from the proof terms that make the construction
AASC-admissible and non-empirical.
-/
structure ThreeFlavorMassSquaredSpectralSourceTheorem
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) where
  FlavorMassState : Type
  MassSquaredLevel : Type
  SplittingClass : Type
  StandingMassOperator : Type
  CharacteristicClass : Type
  massSquaredOfState : FlavorMassState -> MassSquaredLevel
  solarAtmosphericSplittingPair :
    MassSquaredLevel -> MassSquaredLevel -> SplittingClass
  ratioCandidateSplittingClass : C.Ratio -> SplittingClass
  standingMassOperatorOf : C.Ratio -> StandingMassOperator
  characteristicClassOf :
    StandingMassOperator -> CharacteristicClass
  characteristicClassReadsMR3Shape :
    C.Ratio -> CharacteristicClass -> M.Shape -> Prop
  currentCharacteristicReadback :
    characteristicClassReadsMR3Shape
      C.ratio
      (characteristicClassOf (standingMassOperatorOf C.ratio))
      (M.shapeOfRatio C.ratio)
  exactlyThreeMassStates_proof : Prop
  threeFlavorCarrierAdmitted_proof : Prop
  massSquaredSplittingCarrierStanding_proof : Prop
  twoIndependentSplittingsCertified_proof : Prop
  spectralOperatorDerivedFromSplittings_proof : Prop
  characteristicClassDerivedFromOperator_proof : Prop
  characteristicClassPolynomialLike_proof : Prop
  sameRatioTargetReadback_proof : Prop
  quotientStableReadback_proof : Prop
  scaleStatusControlled_proof : Prop
  noAbsoluteMassScaleImport_proof : Prop
  noFittedMatrixTextureImport_proof : Prop
  noObservedSpectrumImport_proof : Prop
  noEigenvalueRootSelection_proof : Prop
  notMerelyShapeMapRelabel_proof : Prop

def ThreeFlavorMassSquaredSpectralSourceTheoremPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (T : ThreeFlavorMassSquaredSpectralSourceTheorem M) : Prop :=
  T.exactlyThreeMassStates_proof /\
    T.threeFlavorCarrierAdmitted_proof /\
      T.massSquaredSplittingCarrierStanding_proof /\
        T.twoIndependentSplittingsCertified_proof /\
          T.spectralOperatorDerivedFromSplittings_proof /\
            T.characteristicClassDerivedFromOperator_proof /\
              T.characteristicClassPolynomialLike_proof /\
                T.sameRatioTargetReadback_proof /\
                  T.quotientStableReadback_proof /\
                    T.scaleStatusControlled_proof /\
                      T.noAbsoluteMassScaleImport_proof /\
                        T.noFittedMatrixTextureImport_proof /\
                          T.noObservedSpectrumImport_proof /\
                            T.noEigenvalueRootSelection_proof /\
                              T.notMerelyShapeMapRelabel_proof

def threeFlavorSourceTheoremAsData
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (T : ThreeFlavorMassSquaredSpectralSourceTheorem M) :
  ThreeFlavorMassSquaredSpectralOperatorData M :=
  { FlavorMassState := T.FlavorMassState
    exactlyThreeMassStates := T.exactlyThreeMassStates_proof
    MassSquaredLevel := T.MassSquaredLevel
    massSquaredOfState := T.massSquaredOfState
    SplittingClass := T.SplittingClass
    solarAtmosphericSplittingPair :=
      T.solarAtmosphericSplittingPair
    ratioCandidateSplittingClass :=
      T.ratioCandidateSplittingClass
    StandingMassOperator := T.StandingMassOperator
    standingMassOperatorOf := T.standingMassOperatorOf
    CharacteristicClass := T.CharacteristicClass
    characteristicClassOf := T.characteristicClassOf
    characteristicClassReadsMR3Shape :=
      T.characteristicClassReadsMR3Shape
    currentCharacteristicReadback :=
      T.currentCharacteristicReadback
    threeFlavorCarrierAdmitted :=
      T.threeFlavorCarrierAdmitted_proof
    massSquaredSplittingCarrierStanding :=
      T.massSquaredSplittingCarrierStanding_proof
    twoIndependentSplittingsCertified :=
      T.twoIndependentSplittingsCertified_proof
    spectralOperatorDerivedFromSplittings :=
      T.spectralOperatorDerivedFromSplittings_proof
    characteristicClassDerivedFromOperator :=
      T.characteristicClassDerivedFromOperator_proof
    characteristicClassPolynomialLike :=
      T.characteristicClassPolynomialLike_proof
    sameRatioTargetReadback :=
      T.sameRatioTargetReadback_proof
    quotientStableReadback :=
      T.quotientStableReadback_proof
    scaleStatusControlled :=
      T.scaleStatusControlled_proof
    noAbsoluteMassScaleImport :=
      T.noAbsoluteMassScaleImport_proof
    noFittedMatrixTextureImport :=
      T.noFittedMatrixTextureImport_proof
    noObservedSpectrumImport :=
      T.noObservedSpectrumImport_proof
    noEigenvalueRootSelection :=
      T.noEigenvalueRootSelection_proof
    notMerelyShapeMapRelabel :=
      T.notMerelyShapeMapRelabel_proof }

theorem threeFlavorSourceTheoremGivesDataPasses
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (T : ThreeFlavorMassSquaredSpectralSourceTheorem M)
  (hT : ThreeFlavorMassSquaredSpectralSourceTheoremPasses T) :
  ThreeFlavorMassSquaredSpectralOperatorDataPasses
    (threeFlavorSourceTheoremAsData M T) := by
  exact hT

def NeedsThreeFlavorMassSquaredSpectralSourceTheorem
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) : Prop :=
  Not (exists T : ThreeFlavorMassSquaredSpectralSourceTheorem M,
    ThreeFlavorMassSquaredSpectralSourceTheoremPasses T)

/--
Proof-carrying source bundle for the three-flavor mass-squared spectral
operator theorem.

This is the object a downstream construction paper can export directly: each
gate is a proposition together with its proof term. From this bundle Lean builds
the source theorem and proves that it passes.
-/
structure ThreeFlavorMassSquaredSpectralSourceProofBundle
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) where
  FlavorMassState : Type
  MassSquaredLevel : Type
  SplittingClass : Type
  StandingMassOperator : Type
  CharacteristicClass : Type
  massSquaredOfState : FlavorMassState -> MassSquaredLevel
  solarAtmosphericSplittingPair :
    MassSquaredLevel -> MassSquaredLevel -> SplittingClass
  ratioCandidateSplittingClass : C.Ratio -> SplittingClass
  standingMassOperatorOf : C.Ratio -> StandingMassOperator
  characteristicClassOf :
    StandingMassOperator -> CharacteristicClass
  characteristicClassReadsMR3Shape :
    C.Ratio -> CharacteristicClass -> M.Shape -> Prop
  currentCharacteristicReadback :
    characteristicClassReadsMR3Shape
      C.ratio
      (characteristicClassOf (standingMassOperatorOf C.ratio))
      (M.shapeOfRatio C.ratio)
  exactlyThreeMassStates : Prop
  exactlyThreeMassStates_proof : exactlyThreeMassStates
  threeFlavorCarrierAdmitted : Prop
  threeFlavorCarrierAdmitted_proof : threeFlavorCarrierAdmitted
  massSquaredSplittingCarrierStanding : Prop
  massSquaredSplittingCarrierStanding_proof :
    massSquaredSplittingCarrierStanding
  twoIndependentSplittingsCertified : Prop
  twoIndependentSplittingsCertified_proof :
    twoIndependentSplittingsCertified
  spectralOperatorDerivedFromSplittings : Prop
  spectralOperatorDerivedFromSplittings_proof :
    spectralOperatorDerivedFromSplittings
  characteristicClassDerivedFromOperator : Prop
  characteristicClassDerivedFromOperator_proof :
    characteristicClassDerivedFromOperator
  characteristicClassPolynomialLike : Prop
  characteristicClassPolynomialLike_proof :
    characteristicClassPolynomialLike
  sameRatioTargetReadback : Prop
  sameRatioTargetReadback_proof : sameRatioTargetReadback
  quotientStableReadback : Prop
  quotientStableReadback_proof : quotientStableReadback
  scaleStatusControlled : Prop
  scaleStatusControlled_proof : scaleStatusControlled
  noAbsoluteMassScaleImport : Prop
  noAbsoluteMassScaleImport_proof : noAbsoluteMassScaleImport
  noFittedMatrixTextureImport : Prop
  noFittedMatrixTextureImport_proof : noFittedMatrixTextureImport
  noObservedSpectrumImport : Prop
  noObservedSpectrumImport_proof : noObservedSpectrumImport
  noEigenvalueRootSelection : Prop
  noEigenvalueRootSelection_proof : noEigenvalueRootSelection
  notMerelyShapeMapRelabel : Prop
  notMerelyShapeMapRelabel_proof : notMerelyShapeMapRelabel

def threeFlavorProofBundleAsSourceTheorem
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (B : ThreeFlavorMassSquaredSpectralSourceProofBundle M) :
  ThreeFlavorMassSquaredSpectralSourceTheorem M :=
  { FlavorMassState := B.FlavorMassState
    MassSquaredLevel := B.MassSquaredLevel
    SplittingClass := B.SplittingClass
    StandingMassOperator := B.StandingMassOperator
    CharacteristicClass := B.CharacteristicClass
    massSquaredOfState := B.massSquaredOfState
    solarAtmosphericSplittingPair :=
      B.solarAtmosphericSplittingPair
    ratioCandidateSplittingClass :=
      B.ratioCandidateSplittingClass
    standingMassOperatorOf := B.standingMassOperatorOf
    characteristicClassOf := B.characteristicClassOf
    characteristicClassReadsMR3Shape :=
      B.characteristicClassReadsMR3Shape
    currentCharacteristicReadback :=
      B.currentCharacteristicReadback
    exactlyThreeMassStates_proof := B.exactlyThreeMassStates
    threeFlavorCarrierAdmitted_proof :=
      B.threeFlavorCarrierAdmitted
    massSquaredSplittingCarrierStanding_proof :=
      B.massSquaredSplittingCarrierStanding
    twoIndependentSplittingsCertified_proof :=
      B.twoIndependentSplittingsCertified
    spectralOperatorDerivedFromSplittings_proof :=
      B.spectralOperatorDerivedFromSplittings
    characteristicClassDerivedFromOperator_proof :=
      B.characteristicClassDerivedFromOperator
    characteristicClassPolynomialLike_proof :=
      B.characteristicClassPolynomialLike
    sameRatioTargetReadback_proof :=
      B.sameRatioTargetReadback
    quotientStableReadback_proof :=
      B.quotientStableReadback
    scaleStatusControlled_proof :=
      B.scaleStatusControlled
    noAbsoluteMassScaleImport_proof :=
      B.noAbsoluteMassScaleImport
    noFittedMatrixTextureImport_proof :=
      B.noFittedMatrixTextureImport
    noObservedSpectrumImport_proof :=
      B.noObservedSpectrumImport
    noEigenvalueRootSelection_proof :=
      B.noEigenvalueRootSelection
    notMerelyShapeMapRelabel_proof :=
      B.notMerelyShapeMapRelabel }

theorem threeFlavorProofBundleSourceTheoremPasses
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (B : ThreeFlavorMassSquaredSpectralSourceProofBundle M) :
  ThreeFlavorMassSquaredSpectralSourceTheoremPasses
    (threeFlavorProofBundleAsSourceTheorem M B) := by
  exact
    ⟨B.exactlyThreeMassStates_proof,
      B.threeFlavorCarrierAdmitted_proof,
      B.massSquaredSplittingCarrierStanding_proof,
      B.twoIndependentSplittingsCertified_proof,
      B.spectralOperatorDerivedFromSplittings_proof,
      B.characteristicClassDerivedFromOperator_proof,
      B.characteristicClassPolynomialLike_proof,
      B.sameRatioTargetReadback_proof,
      B.quotientStableReadback_proof,
      B.scaleStatusControlled_proof,
      B.noAbsoluteMassScaleImport_proof,
      B.noFittedMatrixTextureImport_proof,
      B.noObservedSpectrumImport_proof,
      B.noEigenvalueRootSelection_proof,
      B.notMerelyShapeMapRelabel_proof⟩

def NeedsThreeFlavorMassSquaredSpectralProofBundle
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) : Prop :=
  Not (Nonempty (ThreeFlavorMassSquaredSpectralSourceProofBundle M))

/--
Component-level constructor for the proof bundle.

This is the honest construction entry point: the caller must provide the
three-flavor carriers, maps, current readback proof, and every AASC gate proof.
No gate is filled by `True` here.
-/
def buildThreeFlavorMassSquaredSpectralProofBundle
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (FlavorMassState : Type)
  (MassSquaredLevel : Type)
  (SplittingClass : Type)
  (StandingMassOperator : Type)
  (CharacteristicClass : Type)
  (massSquaredOfState : FlavorMassState -> MassSquaredLevel)
  (solarAtmosphericSplittingPair :
    MassSquaredLevel -> MassSquaredLevel -> SplittingClass)
  (ratioCandidateSplittingClass : C.Ratio -> SplittingClass)
  (standingMassOperatorOf : C.Ratio -> StandingMassOperator)
  (characteristicClassOf :
    StandingMassOperator -> CharacteristicClass)
  (characteristicClassReadsMR3Shape :
    C.Ratio -> CharacteristicClass -> M.Shape -> Prop)
  (currentCharacteristicReadback :
    characteristicClassReadsMR3Shape
      C.ratio
      (characteristicClassOf (standingMassOperatorOf C.ratio))
      (M.shapeOfRatio C.ratio))
  (exactlyThreeMassStates : Prop)
  (exactlyThreeMassStates_proof : exactlyThreeMassStates)
  (threeFlavorCarrierAdmitted : Prop)
  (threeFlavorCarrierAdmitted_proof : threeFlavorCarrierAdmitted)
  (massSquaredSplittingCarrierStanding : Prop)
  (massSquaredSplittingCarrierStanding_proof :
    massSquaredSplittingCarrierStanding)
  (twoIndependentSplittingsCertified : Prop)
  (twoIndependentSplittingsCertified_proof :
    twoIndependentSplittingsCertified)
  (spectralOperatorDerivedFromSplittings : Prop)
  (spectralOperatorDerivedFromSplittings_proof :
    spectralOperatorDerivedFromSplittings)
  (characteristicClassDerivedFromOperator : Prop)
  (characteristicClassDerivedFromOperator_proof :
    characteristicClassDerivedFromOperator)
  (characteristicClassPolynomialLike : Prop)
  (characteristicClassPolynomialLike_proof :
    characteristicClassPolynomialLike)
  (sameRatioTargetReadback : Prop)
  (sameRatioTargetReadback_proof : sameRatioTargetReadback)
  (quotientStableReadback : Prop)
  (quotientStableReadback_proof : quotientStableReadback)
  (scaleStatusControlled : Prop)
  (scaleStatusControlled_proof : scaleStatusControlled)
  (noAbsoluteMassScaleImport : Prop)
  (noAbsoluteMassScaleImport_proof : noAbsoluteMassScaleImport)
  (noFittedMatrixTextureImport : Prop)
  (noFittedMatrixTextureImport_proof : noFittedMatrixTextureImport)
  (noObservedSpectrumImport : Prop)
  (noObservedSpectrumImport_proof : noObservedSpectrumImport)
  (noEigenvalueRootSelection : Prop)
  (noEigenvalueRootSelection_proof : noEigenvalueRootSelection)
  (notMerelyShapeMapRelabel : Prop)
  (notMerelyShapeMapRelabel_proof : notMerelyShapeMapRelabel) :
  ThreeFlavorMassSquaredSpectralSourceProofBundle M :=
  { FlavorMassState := FlavorMassState
    MassSquaredLevel := MassSquaredLevel
    SplittingClass := SplittingClass
    StandingMassOperator := StandingMassOperator
    CharacteristicClass := CharacteristicClass
    massSquaredOfState := massSquaredOfState
    solarAtmosphericSplittingPair :=
      solarAtmosphericSplittingPair
    ratioCandidateSplittingClass :=
      ratioCandidateSplittingClass
    standingMassOperatorOf := standingMassOperatorOf
    characteristicClassOf := characteristicClassOf
    characteristicClassReadsMR3Shape :=
      characteristicClassReadsMR3Shape
    currentCharacteristicReadback :=
      currentCharacteristicReadback
    exactlyThreeMassStates := exactlyThreeMassStates
    exactlyThreeMassStates_proof := exactlyThreeMassStates_proof
    threeFlavorCarrierAdmitted := threeFlavorCarrierAdmitted
    threeFlavorCarrierAdmitted_proof :=
      threeFlavorCarrierAdmitted_proof
    massSquaredSplittingCarrierStanding :=
      massSquaredSplittingCarrierStanding
    massSquaredSplittingCarrierStanding_proof :=
      massSquaredSplittingCarrierStanding_proof
    twoIndependentSplittingsCertified :=
      twoIndependentSplittingsCertified
    twoIndependentSplittingsCertified_proof :=
      twoIndependentSplittingsCertified_proof
    spectralOperatorDerivedFromSplittings :=
      spectralOperatorDerivedFromSplittings
    spectralOperatorDerivedFromSplittings_proof :=
      spectralOperatorDerivedFromSplittings_proof
    characteristicClassDerivedFromOperator :=
      characteristicClassDerivedFromOperator
    characteristicClassDerivedFromOperator_proof :=
      characteristicClassDerivedFromOperator_proof
    characteristicClassPolynomialLike :=
      characteristicClassPolynomialLike
    characteristicClassPolynomialLike_proof :=
      characteristicClassPolynomialLike_proof
    sameRatioTargetReadback := sameRatioTargetReadback
    sameRatioTargetReadback_proof :=
      sameRatioTargetReadback_proof
    quotientStableReadback := quotientStableReadback
    quotientStableReadback_proof :=
      quotientStableReadback_proof
    scaleStatusControlled := scaleStatusControlled
    scaleStatusControlled_proof :=
      scaleStatusControlled_proof
    noAbsoluteMassScaleImport := noAbsoluteMassScaleImport
    noAbsoluteMassScaleImport_proof :=
      noAbsoluteMassScaleImport_proof
    noFittedMatrixTextureImport := noFittedMatrixTextureImport
    noFittedMatrixTextureImport_proof :=
      noFittedMatrixTextureImport_proof
    noObservedSpectrumImport := noObservedSpectrumImport
    noObservedSpectrumImport_proof :=
      noObservedSpectrumImport_proof
    noEigenvalueRootSelection := noEigenvalueRootSelection
    noEigenvalueRootSelection_proof :=
      noEigenvalueRootSelection_proof
    notMerelyShapeMapRelabel := notMerelyShapeMapRelabel
    notMerelyShapeMapRelabel_proof :=
      notMerelyShapeMapRelabel_proof }

theorem builtThreeFlavorProofBundlePasses
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (B : ThreeFlavorMassSquaredSpectralSourceProofBundle M) :
  ThreeFlavorMassSquaredSpectralSourceTheoremPasses
    (threeFlavorProofBundleAsSourceTheorem M B) :=
  threeFlavorProofBundleSourceTheoremPasses M B

/--
Corpus support for attempting the stronger explicit-operator syntax.

These fields record why the stronger target is viable as an AASC-native
construction problem. They are not the construction itself: they license the
search space and the guardrails for a genuine standing operator plus
characteristic-polynomial map.
-/
structure ExplicitOperatorCharacteristicCorpusSupport
  {C : StandingRatioCertificate}
  (_M : MR3SpectralSourceAdmission C) where
  mr3CharacteristicInvariantGate : Prop
  mgn5MassMatrixEigenstructureVocabulary : Prop
  fixedBaseQuantumOperatorBaseAvailable : Prop
  fixedBaseConstraintForOperatorFrameworks : Prop
  domainExtensionConstraintAvailable : Prop
  friedrichsEndpointCharacterizationAvailable : Prop
  endpointBoundaryExactnessControl : Prop
  calibrationAndRawValueFirewall : Prop
  noFreeRootOrEndpointSelector : Prop

def ExplicitOperatorCharacteristicCorpusSupportPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (S : ExplicitOperatorCharacteristicCorpusSupport M) : Prop :=
  S.mr3CharacteristicInvariantGate /\
    S.mgn5MassMatrixEigenstructureVocabulary /\
      S.fixedBaseQuantumOperatorBaseAvailable /\
        S.fixedBaseConstraintForOperatorFrameworks /\
          S.domainExtensionConstraintAvailable /\
            S.friedrichsEndpointCharacterizationAvailable /\
              S.endpointBoundaryExactnessControl /\
                S.calibrationAndRawValueFirewall /\
                  S.noFreeRootOrEndpointSelector

/--
Viability audit for the stronger operator-characteristic route.

Passing this audit says the corpus contains the right kind of operator,
endpoint, characteristic-invariant, and exactness-control infrastructure for
the stronger construction to be a legitimate target. The audit deliberately
keeps the constructive syntax as a separate field, because corpus viability is
not itself an operator or a characteristic polynomial.
-/
structure ExplicitOperatorCharacteristicViabilityAudit
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) where
  support : ExplicitOperatorCharacteristicCorpusSupport M
  supportPasses :
    ExplicitOperatorCharacteristicCorpusSupportPasses support
  constructionStillRequired :
    NeedsExplicitOperatorCharacteristicPolynomialSyntax M \/
      exists S : ExplicitOperatorCharacteristicPolynomialSyntax M,
        ExplicitOperatorCharacteristicPolynomialSyntaxCertified S

/--
Operator-level characteristic-polynomial package.

This is the next refinement of the MR3 explicit-polynomial target: the
polynomial syntax is no longer an arbitrary presentation. It is induced from an
admitted standing operator/carrier object.
-/
structure MR3OperatorCharacteristicPolynomialPackage
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) where
  Operator : Type
  Polynomial : Type
  operatorOf : C.Ratio -> Operator
  characteristicPolynomialOfOperator : Operator -> Polynomial
  satisfiesCharacteristicClass : C.Ratio -> Polynomial -> M.Shape -> Prop
  currentSatisfiesCharacteristicClass :
    satisfiesCharacteristicClass
      C.ratio
      (characteristicPolynomialOfOperator (operatorOf C.ratio))
      (M.shapeOfRatio C.ratio)
  operatorAdmitted : Prop
  standingOperatorCarrier : Prop
  characteristicPolynomialCertified : Prop
  sourceShapeIsCharacteristicClass : Prop
  sameTargetReadback : Prop
  quotientStableReadback : Prop
  scaleStatusControlled : Prop
  calibrationFreeReadout : Prop
  noRootSelector : Prop
  noEmpiricalFitImport : Prop

def operatorCharacteristicPackageFromSyntaxAndGuardrails
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (S : MR3OperatorCharacteristicConstructiveSyntax M)
  (G : MR3OperatorCharacteristicGuardrails M) :
  MR3OperatorCharacteristicPolynomialPackage M :=
  { Operator := S.Operator
    Polynomial := S.Polynomial
    operatorOf := S.operatorOf
    characteristicPolynomialOfOperator :=
      S.characteristicPolynomialOfOperator
    satisfiesCharacteristicClass := S.satisfiesCharacteristicClass
    currentSatisfiesCharacteristicClass :=
      S.currentSatisfiesCharacteristicClass
    operatorAdmitted := G.operatorAdmitted
    standingOperatorCarrier := G.standingOperatorCarrier
    characteristicPolynomialCertified :=
      S.characteristicPolynomialCertified
    sourceShapeIsCharacteristicClass :=
      S.sourceShapeIsCharacteristicClass
    sameTargetReadback := G.sameTargetReadback
    quotientStableReadback := G.quotientStableReadback
    scaleStatusControlled := G.scaleStatusControlled
    calibrationFreeReadout := G.calibrationFreeReadout
    noRootSelector := G.noRootSelector
    noEmpiricalFitImport := G.noEmpiricalFitImport }

def MR3OperatorCharacteristicPackagePasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (P : MR3OperatorCharacteristicPolynomialPackage M) : Prop :=
  P.operatorAdmitted /\
    P.standingOperatorCarrier /\
      P.characteristicPolynomialCertified /\
        P.sourceShapeIsCharacteristicClass /\
          P.sameTargetReadback /\
            P.quotientStableReadback /\
              P.scaleStatusControlled /\
                P.calibrationFreeReadout /\
                  P.noRootSelector /\
                    P.noEmpiricalFitImport

theorem operatorCharacteristicPackageFromSyntaxAndGuardrailsPasses
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (S : MR3OperatorCharacteristicConstructiveSyntax M)
  (G : MR3OperatorCharacteristicGuardrails M)
  (hS : MR3OperatorCharacteristicSyntaxCertified S) :
  MR3OperatorCharacteristicPackagePasses
    (operatorCharacteristicPackageFromSyntaxAndGuardrails M S G) := by
  rcases hS with ⟨hchar, hshape⟩
  exact
    ⟨G.operatorAdmitted_proof,
      G.standingOperatorCarrier_proof,
      hchar,
      hshape,
      G.sameTargetReadback_proof,
      G.quotientStableReadback_proof,
      G.scaleStatusControlled_proof,
      G.calibrationFreeReadout_proof,
      G.noRootSelector_proof,
      G.noEmpiricalFitImport_proof⟩

/--
Native AASC operator-exhaustion support for an operator-characteristic
readout package.

The fixed-base operator audit supplies the guardrail side of the package:
operator admission on the standing carrier, same-target readback, quotient and
scale stability, calibration freedom, and the absence of root/value selection
or empirical import. It does not by itself supply the polynomial syntax or the
claim that the MR3 shape is the characteristic class; those remain explicit
inputs.
-/
structure AASCNativeOperatorExhaustionReadoutSupport
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M)
  (N : AASCNoEleventhNeutrinoRoute C M H)
  (P : MR3OperatorCharacteristicPolynomialPackage M) where
  fixedBaseOperatorAudit : AASCFixedBaseOperatorAudit C M H N
  operatorAdmittedByExhaustion : P.operatorAdmitted
  standingCarrierByExhaustion : P.standingOperatorCarrier
  sameTargetReadbackByFixedBase : P.sameTargetReadback
  quotientStableBySameScope : P.quotientStableReadback
  scaleStatusControlledByFixedBase : P.scaleStatusControlled
  calibrationFreeByNoExternalDatum : P.calibrationFreeReadout
  noRootSelectorByEndpointNonSelection : P.noRootSelector
  noEmpiricalFitImportByNoExternalDatum : P.noEmpiricalFitImport

def NativeOperatorExhaustionCompletesPackage
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (P : MR3OperatorCharacteristicPolynomialPackage M) : Prop :=
  Nonempty (AASCNativeOperatorExhaustionReadoutSupport H N P) /\
    P.characteristicPolynomialCertified /\
      P.sourceShapeIsCharacteristicClass

theorem nativeOperatorExhaustionCompletesOperatorPackagePasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (P : MR3OperatorCharacteristicPolynomialPackage M)
  (hcomplete :
    NativeOperatorExhaustionCompletesPackage (H := H) (N := N) P) :
  MR3OperatorCharacteristicPackagePasses P := by
  rcases hcomplete with ⟨⟨S⟩, hchar, hshape⟩
  exact
    ⟨S.operatorAdmittedByExhaustion,
      S.standingCarrierByExhaustion,
      hchar,
      hshape,
      S.sameTargetReadbackByFixedBase,
      S.quotientStableBySameScope,
      S.scaleStatusControlledByFixedBase,
      S.calibrationFreeByNoExternalDatum,
      S.noRootSelectorByEndpointNonSelection,
      S.noEmpiricalFitImportByNoExternalDatum⟩

def operatorCharacteristicPackageAsMR3PolynomialPresentation
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (P : MR3OperatorCharacteristicPolynomialPackage M) :
  MR3ExplicitPolynomialPresentation M :=
  { Polynomial := P.Polynomial
    polynomialOf := fun r =>
      P.characteristicPolynomialOfOperator (P.operatorOf r)
    satisfiesPolynomialClass := P.satisfiesCharacteristicClass
    currentSatisfies := P.currentSatisfiesCharacteristicClass
    polynomialSyntaxCertified :=
      P.characteristicPolynomialCertified /\
        P.sourceShapeIsCharacteristicClass
    polynomialDerivedFromStandingCarrier :=
      P.operatorAdmitted /\ P.standingOperatorCarrier
    sameTargetReadback := P.sameTargetReadback
    quotientStableSyntax := P.quotientStableReadback
    scaleStatusControlled := P.scaleStatusControlled
    calibrationFreeSyntax := P.calibrationFreeReadout
    noRootSelector := P.noRootSelector
    noEmpiricalFitImport := P.noEmpiricalFitImport }

theorem operatorCharacteristicPackagePresentationPasses
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (P : MR3OperatorCharacteristicPolynomialPackage M)
  (hP : MR3OperatorCharacteristicPackagePasses P) :
  MR3ExplicitPolynomialPresentationPasses
    (operatorCharacteristicPackageAsMR3PolynomialPresentation M P) := by
  rcases hP with
    ⟨hoperator, hstanding, hchar, hshape, hsame, hquotient,
      hscale, hcalibration, hselector, hempirical⟩
  exact
    ⟨⟨hchar, hshape⟩,
      ⟨hoperator, hstanding⟩,
      hsame,
      hquotient,
      hscale,
      hcalibration,
      hselector,
      hempirical⟩

theorem operatorCharacteristicPackageGivesAlgebraicClassFrontier
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (P : MR3OperatorCharacteristicPolynomialPackage M)
  (hP : MR3OperatorCharacteristicPackagePasses P)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  mr3ExplicitPolynomialPresentationGivesAlgebraicClassFrontier
    M
    (operatorCharacteristicPackageAsMR3PolynomialPresentation M P)
    (operatorCharacteristicPackagePresentationPasses M P hP)
    BE
    BV

theorem operatorCharacteristicSyntaxAndGuardrailsGiveAlgebraicClassFrontier
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (S : MR3OperatorCharacteristicConstructiveSyntax M)
  (G : MR3OperatorCharacteristicGuardrails M)
  (hS : MR3OperatorCharacteristicSyntaxCertified S)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  operatorCharacteristicPackageGivesAlgebraicClassFrontier
    M
    (operatorCharacteristicPackageFromSyntaxAndGuardrails M S G)
    (operatorCharacteristicPackageFromSyntaxAndGuardrailsPasses
      M S G hS)
    BE
    BV

theorem nativeOperatorExhaustionGuardrailsAndSyntaxGiveAlgebraicClassFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (S : MR3OperatorCharacteristicConstructiveSyntax M)
  (G : AASCNativeOperatorExhaustionGuardrailSupport H N)
  (hS : MR3OperatorCharacteristicSyntaxCertified S)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  operatorCharacteristicSyntaxAndGuardrailsGiveAlgebraicClassFrontier
    M
    S
    G.guardrails
    hS
    BE
    BV

theorem mr3ShapeMapAndNativeOperatorExhaustionGiveAlgebraicClassFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (G : AASCNativeOperatorExhaustionGuardrailSupport H N)
  (hsource : M.sourceCertified)
  (hshape : M.sourceInducesShapeMap)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  nativeOperatorExhaustionGuardrailsAndSyntaxGiveAlgebraicClassFrontier
    (mr3ShapeMapAsConstructiveSyntax M)
    G
    (mr3ShapeMapConstructiveSyntaxCertified M hsource hshape)
    BE
    BV

theorem explicitOperatorSyntaxAndNativeExhaustionGiveAlgebraicClassFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (S : ExplicitOperatorCharacteristicPolynomialSyntax M)
  (G : AASCNativeOperatorExhaustionGuardrailSupport H N)
  (hS : ExplicitOperatorCharacteristicPolynomialSyntaxCertified S)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  nativeOperatorExhaustionGuardrailsAndSyntaxGiveAlgebraicClassFrontier
    (explicitOperatorSyntaxAsConstructiveSyntax M S)
    G
    (explicitOperatorSyntaxGivesCertifiedConstructiveSyntax M S hS)
    BE
    BV

theorem standingOperatorPresentationAndNativeExhaustionGiveAlgebraicClassFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (P : NeutrinoStandingOperatorCharacteristicPresentation M)
  (G : AASCNativeOperatorExhaustionGuardrailSupport H N)
  (hP : NeutrinoStandingOperatorPresentationPasses P)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  explicitOperatorSyntaxAndNativeExhaustionGiveAlgebraicClassFrontier
    (standingOperatorPresentationAsExplicitSyntax M P)
    G
    (standingOperatorPresentationGivesExplicitSyntaxCertified M P hP)
    BE
    BV

theorem massSpectralOperatorCandidateAndNativeExhaustionGiveAlgebraicClassFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (K : NeutrinoMassSpectralOperatorCandidate M)
  (G : AASCNativeOperatorExhaustionGuardrailSupport H N)
  (hK : NeutrinoMassSpectralOperatorCandidatePasses K)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  standingOperatorPresentationAndNativeExhaustionGiveAlgebraicClassFrontier
    (massSpectralOperatorCandidateAsPresentation M K)
    G
    (massSpectralOperatorCandidateGivesPresentationPasses M K hK)
    BE
    BV

theorem threeFlavorDataAndNativeExhaustionGiveAlgebraicClassFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (D : ThreeFlavorMassSquaredSpectralOperatorData M)
  (G : AASCNativeOperatorExhaustionGuardrailSupport H N)
  (hD : ThreeFlavorMassSquaredSpectralOperatorDataPasses D)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  massSpectralOperatorCandidateAndNativeExhaustionGiveAlgebraicClassFrontier
    (threeFlavorDataAsMassSpectralOperatorCandidate M D)
    G
    (threeFlavorDataGivesMassSpectralCandidatePasses M D hD)
    BE
    BV

theorem threeFlavorSourceTheoremAndNativeExhaustionGiveAlgebraicClassFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (T : ThreeFlavorMassSquaredSpectralSourceTheorem M)
  (G : AASCNativeOperatorExhaustionGuardrailSupport H N)
  (hT : ThreeFlavorMassSquaredSpectralSourceTheoremPasses T)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  threeFlavorDataAndNativeExhaustionGiveAlgebraicClassFrontier
    (threeFlavorSourceTheoremAsData M T)
    G
    (threeFlavorSourceTheoremGivesDataPasses M T hT)
    BE
    BV

theorem threeFlavorProofBundleAndNativeExhaustionGiveAlgebraicClassFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (B : ThreeFlavorMassSquaredSpectralSourceProofBundle M)
  (G : AASCNativeOperatorExhaustionGuardrailSupport H N)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  threeFlavorSourceTheoremAndNativeExhaustionGiveAlgebraicClassFrontier
    (threeFlavorProofBundleAsSourceTheorem M B)
    G
    (threeFlavorProofBundleSourceTheoremPasses M B)
    BE
    BV

theorem builtThreeFlavorProofBundleAndNativeExhaustionGiveFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (B : ThreeFlavorMassSquaredSpectralSourceProofBundle M)
  (G : AASCNativeOperatorExhaustionGuardrailSupport H N)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  threeFlavorProofBundleAndNativeExhaustionGiveAlgebraicClassFrontier
    B
    G
    BE
    BV

theorem explicitOperatorViabilityWithConstructedSyntaxGivesFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (_A : ExplicitOperatorCharacteristicViabilityAudit M)
  (S : ExplicitOperatorCharacteristicPolynomialSyntax M)
  (G : AASCNativeOperatorExhaustionGuardrailSupport H N)
  (hS : ExplicitOperatorCharacteristicPolynomialSyntaxCertified S)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  explicitOperatorSyntaxAndNativeExhaustionGiveAlgebraicClassFrontier
    S
    G
    hS
    BE
    BV

theorem nativeOperatorExhaustionPackageGivesAlgebraicClassFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (P : MR3OperatorCharacteristicPolynomialPackage M)
  (hcomplete :
    NativeOperatorExhaustionCompletesPackage (H := H) (N := N) P)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  operatorCharacteristicPackageGivesAlgebraicClassFrontier
    M
    P
    (nativeOperatorExhaustionCompletesOperatorPackagePasses
      (H := H) (N := N) P hcomplete)
    BE
    BV

def NeedsOperatorCharacteristicPolynomialPackage
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C) : Prop :=
  Not (exists P : MR3OperatorCharacteristicPolynomialPackage M,
    MR3OperatorCharacteristicPackagePasses P)

/--
Corpus-facing requirements for exact-value readout. Exact value requires not
only branch singleton closure, but raw-value representative closure: a value
universe, a readout map, representative uniqueness modulo skin, discharged
freedoms, calibration priority, transport neutrality, and no hidden selector.
-/
structure AASCExactValueReadoutRequirements
  (C : StandingRatioCertificate) where
  rawValueUniverseAvailable : Prop
  exactValueMapAvailable : Prop
  representativeBranchCollapsedModuloSkin : Prop
  allUnresolvedFreedomsDischarged : Prop
  calibrationPrior : Prop
  transportNeutralOrDischarged : Prop
  scaleStatusFixed : Prop
  noHiddenNumericalSelector : Prop
  noEmpiricalFitImport : Prop

def ExactValueReadoutRequirementsPass
  {C : StandingRatioCertificate}
  (R : AASCExactValueReadoutRequirements C) : Prop :=
  R.rawValueUniverseAvailable /\
    R.exactValueMapAvailable /\
      R.representativeBranchCollapsedModuloSkin /\
        R.allUnresolvedFreedomsDischarged /\
          R.calibrationPrior /\
            R.transportNeutralOrDischarged /\
              R.scaleStatusFixed /\
                R.noHiddenNumericalSelector /\
                  R.noEmpiricalFitImport

/--
If exact-value requirements are packaged with an actual exact value map, they
supply the exact-value source theorem.
-/
structure AASCExactValueReadoutConstruction
  (C : StandingRatioCertificate) where
  requirements : AASCExactValueReadoutRequirements C
  requirementsPass : ExactValueReadoutRequirementsPass requirements
  Value : Type
  valueOf : C.Ratio -> Value

def exactValueConstructionAsSourceTheorem
  (C : StandingRatioCertificate)
  (K : AASCExactValueReadoutConstruction C) :
  AASCExactRatioValueSourceTheorem C :=
  { Value := K.Value
    valueOf := K.valueOf
    audit :=
      { targetPreserving := K.requirements.exactValueMapAvailable
        quotientStable :=
          K.requirements.representativeBranchCollapsedModuloSkin
        representationIndependent :=
          K.requirements.allUnresolvedFreedomsDischarged
        calibrationFree := K.requirements.calibrationPrior
        notEmpirical := K.requirements.noEmpiricalFitImport
        notFitted := K.requirements.noEmpiricalFitImport
        notBranchSelector := K.requirements.noHiddenNumericalSelector
        lawfulOnCurrent := K.requirements.rawValueUniverseAvailable }
    auditPasses := by
      rcases K.requirementsPass with
        ⟨hraw, hmap, hrep, hfree, hcalibration, _htransport,
          _hscale, hselector, hempirical⟩
      exact ⟨hmap, hrep, hfree, hcalibration,
        hempirical, hempirical, hselector, hraw⟩ }

theorem exactValueConstructionGivesExactValueFrontier
  (C : StandingRatioCertificate)
  (K : AASCExactValueReadoutConstruction C) :
  AASCNNR9ExactValueFrontier C :=
  exactValueSourceGivesExactValueFrontier
    C
    (exactValueConstructionAsSourceTheorem C K)

/--
The current corpus assessment for the two requested tracks: algebraic readout
has a precise construction target; exact value is blocked unless the exact
requirements are constructed.
-/
structure AASCAlgebraicAndExactReadoutAssessment
  (C : StandingRatioCertificate) where
  algebraicRequirements :
    AASCAlgebraicReadoutRequirements C
  algebraicStillNeedsConstruction :
    Not (AlgebraicReadoutRequirementsPass algebraicRequirements)
  exactRequirements :
    AASCExactValueReadoutRequirements C
  exactStillNeedsConstruction :
    Not (ExactValueReadoutRequirementsPass exactRequirements)
  exactValueBlocker :
    AASCExactValueReadoutBlocker C

theorem assessmentBlocksExactValueFrontier
  {C : StandingRatioCertificate}
  (A : AASCAlgebraicAndExactReadoutAssessment C) :
  NoCurrentRatioEvaluatorAtStrength C .exactValue := by
  exact A.exactValueBlocker.noExactValueEvaluator

/--
Name for the new post-singleton blocker: the branch singleton is locked, but
the current branch has no lawful evaluator into an output domain.
-/
def NoNumericalEvaluatorForCurrentStandingBranch
  (C : StandingRatioCertificate) : Prop :=
  Not (exists E : CanonicalEvaluatorForCurrentStandingRatio C,
    CanonicalEvaluatorAdmissible E)

/--
Equivalent manuscript-facing phrasing of the same blocker.
-/
def CurrentStandingRatioOpaqueToNumericReadout
  (C : StandingRatioCertificate) : Prop :=
  NoNumericalEvaluatorForCurrentStandingBranch C

/--
If no lawful evaluator exists, the singleton remains a branch object rather
than a value/expression/class output.
-/
theorem singletonWithoutEvaluatorRemainsOpaque
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (_hsingle : HybridJointRestrictionSingleton H)
  (hopaque : NoNumericalEvaluatorForCurrentStandingBranch C) :
  CurrentStandingRatioOpaqueToNumericReadout C := by
  exact hopaque

end Neutrino

end MaleyLean
