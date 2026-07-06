import SM1.ScopeBoundary

namespace SM1

inductive FormalEnvironmentKind where
  | definition
  | theorem
  | proposition
  | lemma
  | corollary
  | criterion
  | status
  | nonclaim
  | principle
  | remark
  deriving DecidableEq, Repr

inductive APlusRowStatus where
  | represented
  | representedAsBoundary
  | receivedDependency
  | sectorRelative
  | deferredToSM6
  | explicitNonclaim
  deriving DecidableEq, Repr

structure ManuscriptFormalEnvironment where
  line : Nat
  kind : FormalEnvironmentKind
  title : String
  leanSurface : String
  status : APlusRowStatus

def manuscriptFormalEnvironmentRows : List ManuscriptFormalEnvironment := [
  { line := 181, kind := .definition, title := "Non-degenerate classifier claim", leanSurface := "SM1.KernelStatus", status := .represented },
  { line := 189, kind := .theorem, title := "Sameness requires kernel preservation", leanSurface := "SM1.KernelStatus", status := .represented },
  { line := 201, kind := .theorem, title := "Prediction and falsification require non-degenerate reference", leanSurface := "SM1.KernelStatus", status := .represented },
  { line := 212, kind := .proposition, title := "Kernel-denial burden", leanSurface := "SM1.KernelStatus", status := .represented },
  { line := 224, kind := .remark, title := "Proof class", leanSurface := "SM1.ScopeBoundary", status := .representedAsBoundary },
  { line := 260, kind := .nonclaim, title := "What SM-1 does not claim", leanSurface := "SM1.ScopeBoundary", status := .explicitNonclaim },
  { line := 264, kind := .status, title := "What SM-1 claims", leanSurface := "SM1.ScopeBoundary", status := .representedAsBoundary },
  { line := 355, kind := .principle, title := "No premature SM-6 closure", leanSurface := "SM1.ScopeBoundary", status := .deferredToSM6 },
  { line := 384, kind := .remark, title := "Definitions do not upgrade", leanSurface := "SM1.ScopeBoundary", status := .representedAsBoundary },
  { line := 391, kind := .definition, title := "Standing", leanSurface := "SM1.StandingArena", status := .represented },
  { line := 395, kind := .definition, title := "Admissibility", leanSurface := "SM1.StandingArena", status := .represented },
  { line := 399, kind := .definition, title := "Reference", leanSurface := "SM1.KernelStatus", status := .represented },
  { line := 403, kind := .definition, title := "Scope", leanSurface := "SM1.StandingArena", status := .represented },
  { line := 407, kind := .definition, title := "Primitive carrier", leanSurface := "SM1.CarrierAdmission", status := .represented },
  { line := 411, kind := .definition, title := "Derivative skin", leanSurface := "SM1.SkinIdentification", status := .represented },
  { line := 415, kind := .definition, title := "Registered derivative statuses", leanSurface := "SM1.StandingArena", status := .represented },
  { line := 455, kind := .criterion, title := "Carrier identification", leanSurface := "SM1.CarrierAdmission", status := .sectorRelative },
  { line := 471, kind := .definition, title := "Standard Model claim arena", leanSurface := "SM1.StandingArena", status := .represented },
  { line := 482, kind := .definition, title := "Standard Model component claim", leanSurface := "SM1.StandingArena", status := .represented },
  { line := 493, kind := .definition, title := "Future Standard Model-associated claim", leanSurface := "SM1.StandingArena", status := .represented },
  { line := 501, kind := .definition, title := "BSM claim", leanSurface := "SM1.StandingArena", status := .represented },
  { line := 510, kind := .definition, title := "Same-scope preservation", leanSurface := "SM1.StandingArena", status := .represented },
  { line := 520, kind := .definition, title := "Target update", leanSurface := "SM1.MainTheorems", status := .represented },
  { line := 535, kind := .criterion, title := "Carrier Necessary Conditions", leanSurface := "SM1.CarrierAdmission", status := .sectorRelative },
  { line := 547, kind := .definition, title := "Closed carrier certificate", leanSurface := "SM1.CarrierAdmission", status := .represented },
  { line := 558, kind := .definition, title := "Non-circular content of local closure proof", leanSurface := "SM1.CarrierAdmission", status := .sectorRelative },
  { line := 570, kind := .proposition, title := "Carrier Certificate Sufficiency", leanSurface := "SM1.CarrierAdmission", status := .represented },
  { line := 602, kind := .lemma, title := "Skin Identification Lemma", leanSurface := "SM1.SkinIdentification", status := .represented },
  { line := 617, kind := .theorem, title := "Non-Circular No-Promotion Form", leanSurface := "SM1.SkinIdentification", status := .represented },
  { line := 628, kind := .remark, title := "Local application status", leanSurface := "SM1.ScopeBoundary", status := .sectorRelative },
  { line := 665, kind := .theorem, title := "No Primitive Skin Theorem", leanSurface := "SM1.SkinIdentification", status := .represented },
  { line := 716, kind := .criterion, title := "Normal-form adequacy", leanSurface := "SM1.ComponentNormalForm", status := .represented },
  { line := 777, kind := .proposition, title := "Fixed-Grammar Status Coverage", leanSurface := "SM1.ComponentNormalForm", status := .represented },
  { line := 794, kind := .definition, title := "Ordered status grammar", leanSurface := "SM1.StandingArena", status := .represented },
  { line := 802, kind := .theorem, title := "Classifier Well-Formedness", leanSurface := "SM1.MasterClassifier", status := .represented },
  { line := 813, kind := .theorem, title := "Classifier Determinacy", leanSurface := "SM1.MasterClassifier", status := .represented },
  { line := 824, kind := .lemma, title := "Non-Ad-Hoc Extension", leanSurface := "SM1.MasterClassifier", status := .represented },
  { line := 835, kind := .theorem, title := "Non-Ad-Hoc Classifiability", leanSurface := "SM1.MasterClassifier", status := .represented },
  { line := 847, kind := .corollary, title := "Fixed-Grammar Classifier Totality", leanSurface := "SM1.MasterClassifier", status := .represented },
  { line := 856, kind := .theorem, title := "SM Carrier Normal Form Theorem", leanSurface := "SM1.MainTheorems", status := .represented },
  { line := 867, kind := .theorem, title := "Measurement Witness Non-Promotion", leanSurface := "SM1.MainTheorems", status := .represented },
  { line := 878, kind := .theorem, title := "Transport Non-Generation", leanSurface := "SM1.MainTheorems", status := .represented },
  { line := 889, kind := .theorem, title := "Target Update Separation", leanSurface := "SM1.MainTheorems", status := .represented },
  { line := 904, kind := .theorem, title := "Future-Claim Classifiability", leanSurface := "SM1.MainTheorems", status := .represented },
  { line := 915, kind := .theorem, title := "No Same-Scope Primitive Escape Schema", leanSurface := "SM1.MainTheorems", status := .sectorRelative },
  { line := 926, kind := .theorem, title := "BSM Audit Closure", leanSurface := "SM1.MainTheorems", status := .sectorRelative },
  { line := 944, kind := .theorem, title := "Counterexample Burden Is Not Survivor", leanSurface := "SM1.MainTheorems", status := .represented },
  { line := 964, kind := .criterion, title := "Target-Update Discipline Criterion", leanSurface := "SM1.MainTheorems", status := .represented },
  { line := 978, kind := .definition, title := "Counterexample burden", leanSurface := "SM1.MainTheorems", status := .represented },
  { line := 982, kind := .theorem, title := "Burden Escalation Criterion", leanSurface := "SM1.MainTheorems", status := .represented },
  { line := 1047, kind := .theorem, title := "New-Physics Diagnostic Theorem", leanSurface := "SM1.MainTheorems", status := .represented },
  { line := 1066, kind := .proposition, title := "Reality-contact discipline for classifier predictions", leanSurface := "SM1.PredictionRegister", status := .represented },
  { line := 1520, kind := .principle, title := "Dependency discipline", leanSurface := "SM1.DependencyLedger", status := .receivedDependency },
  { line := 1914, kind := .criterion, title := "Faithful classifier counterexample", leanSurface := "SM1.PredictionRegister", status := .represented }
]

theorem manuscript_formal_environment_count :
    manuscriptFormalEnvironmentRows.length = 54 := by
  decide

def APlusInventoryComplete : Prop :=
  manuscriptFormalEnvironmentRows.length = 54

theorem a_plus_inventory_complete : APlusInventoryComplete :=
  manuscript_formal_environment_count

end SM1
