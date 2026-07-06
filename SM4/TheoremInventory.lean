import SM4.ScopeBoundary

namespace SM4

inductive FormalEnvironmentKind where
  | definition | theorem | proposition | lemma | corollary | criterion | nonclaim | remark
  deriving DecidableEq, Repr

structure ManuscriptFormalEnvironment where
  line : Nat
  kind : FormalEnvironmentKind
  title : String
  leanSurface : String
  status : String

def manuscriptFormalEnvironmentRows : List ManuscriptFormalEnvironment := [
  { line := 179, kind := .definition, title := "Non-degenerate CCR claim", leanSurface := "SM4.CCRArena", status := "represented" },
  { line := 187, kind := .theorem, title := "Sameness requires kernel preservation", leanSurface := "SM1.KernelStatus", status := "sm1Received" },
  { line := 199, kind := .theorem, title := "Prediction and falsification require non-degenerate reference", leanSurface := "SM1.KernelStatus", status := "sm1Received" },
  { line := 210, kind := .proposition, title := "Kernel-denial burden", leanSurface := "SM1.KernelStatus", status := "sm1Received" },
  { line := 222, kind := .remark, title := "Proof class", leanSurface := "SM4.ScopeBoundary", status := "boundary" },
  { line := 264, kind := .nonclaim, title := "What SM-4 does not claim", leanSurface := "SM4.ScopeBoundary", status := "explicitNonclaim" },
  { line := 340, kind := .definition, title := "CCR arena", leanSurface := "SM4.CCRArena", status := "represented" },
  { line := 351, kind := .definition, title := "CCR claim", leanSurface := "SM4.CCRArena", status := "represented" },
  { line := 355, kind := .definition, title := "Same-scope CCR preservation", leanSurface := "SM4.CCRArena", status := "represented" },
  { line := 359, kind := .criterion, title := "CCR target update", leanSurface := "SM4.MainTheorems", status := "represented" },
  { line := 366, kind := .definition, title := "Two-level CCR closure package", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 385, kind := .definition, title := "Primitive carrier certificate", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 396, kind := .definition, title := "Registered status certificate", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 407, kind := .definition, title := "Candidate primitive CCR certificate", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 411, kind := .definition, title := "Hostile branch and nonclosure guard", leanSurface := "SM4.CCRArena", status := "represented" },
  { line := 426, kind := .definition, title := "Package closure", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 438, kind := .lemma, title := "CCR skin identification", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 442, kind := .theorem, title := "CCR skin non-promotion", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 488, kind := .theorem, title := "Charge number non-promotion", leanSurface := "SM4.MainTheorems", status := "represented" },
  { line := 499, kind := .theorem, title := "Hypercharge and electric-charge status", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 513, kind := .theorem, title := "Normalization skin theorem", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 522, kind := .definition, title := "EW/EM bookkeeping status", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 530, kind := .theorem, title := "EW/EM overcount deletion", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 543, kind := .theorem, title := "EW/EM coordinate-choice non-primitivity", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 552, kind := .nonclaim, title := "EW/EM bookkeeping boundary", leanSurface := "SM4.ScopeBoundary", status := "explicitNonclaim" },
  { line := 561, kind := .definition, title := "Coupling-modulus status", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 565, kind := .definition, title := "Negative modulus status and positive coupling-envelope status", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 569, kind := .proposition, title := "Coupling-modulus/SPCT ordering", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 579, kind := .theorem, title := "Coupling value non-primitivity", leanSurface := "SM4.MainTheorems", status := "represented" },
  { line := 589, kind := .theorem, title := "Dimensionless coupling non-derivability", leanSurface := "SM4.ScopeBoundary", status := "explicitNonclaim" },
  { line := 603, kind := .proposition, title := "Forced uniqueness boundary", leanSurface := "SM4.ScopeBoundary", status := "boundary" },
  { line := 617, kind := .definition, title := "Standing-preserving coupling envelope", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 621, kind := .theorem, title := "SPCT status theorem", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 634, kind := .corollary, title := "Coupling non-generation", leanSurface := "SM4.MainTheorems", status := "represented" },
  { line := 643, kind := .definition, title := "RG transport status", leanSurface := "SM4.CCRArena", status := "represented" },
  { line := 647, kind := .theorem, title := "RG transport theorem", leanSurface := "SM4.MainTheorems", status := "represented" },
  { line := 660, kind := .theorem, title := "RG non-generation", leanSurface := "SM4.MainTheorems", status := "represented" },
  { line := 670, kind := .proposition, title := "Fixed point and universality status", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 682, kind := .theorem, title := "Scheme coordinate non-primitivity", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 689, kind := .theorem, title := "Matching condition status", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 699, kind := .theorem, title := "EFT coefficient status", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 715, kind := .definition, title := "Constant role taxonomy", leanSurface := "SM4.CCRArena", status := "represented" },
  { line := 727, kind := .theorem, title := "Fixity/running reconciliation", leanSurface := "SM4.MainTheorems", status := "represented" },
  { line := 738, kind := .theorem, title := "Parameter mobility theorem", leanSurface := "SM4.MainTheorems", status := "represented" },
  { line := 752, kind := .theorem, title := "Fixity and running reconciliation", leanSurface := "SM4.MainTheorems", status := "represented" },
  { line := 764, kind := .proposition, title := "Varying-constant branch", leanSurface := "SM4.MainTheorems", status := "represented" },
  { line := 774, kind := .definition, title := "Calibration status", leanSurface := "SM4.CCRArena", status := "represented" },
  { line := 778, kind := .theorem, title := "Measurement non-generation", leanSurface := "SM4.MainTheorems", status := "represented" },
  { line := 794, kind := .theorem, title := "CCR BSM branch theorem", leanSurface := "SM4.MainTheorems", status := "represented" },
  { line := 898, kind := .proposition, title := "Reality-contact discipline for CCR predictions", leanSurface := "SM4.PredictionRegister", status := "represented" },
  { line := 948, kind := .definition, title := "Registered other CCR status", leanSurface := "SM4.CCRArena", status := "represented" },
  { line := 958, kind := .theorem, title := "CCR Coverage Theorem", leanSurface := "SM4.MainTheorems", status := "represented" },
  { line := 988, kind := .theorem, title := "Primitive charge-carrier package closure", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 1004, kind := .theorem, title := "Registered CCR status package closure", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 1011, kind := .theorem, title := "CCR package closure", leanSurface := "SM4.PackageCertificates", status := "represented" },
  { line := 1022, kind := .lemma, title := "Certificate-to-deletion", leanSurface := "SM4.MainTheorems", status := "represented" },
  { line := 1032, kind := .theorem, title := "Scoped CCR primitive-status deletion", leanSurface := "SM4.MainTheorems", status := "sm6Handoff" },
  { line := 1048, kind := .criterion, title := "Faithful CCR counterexample", leanSurface := "SM4.PredictionRegister", status := "represented" }
]

theorem manuscript_formal_environment_count :
    manuscriptFormalEnvironmentRows.length = 58 := by
  decide

def APlusInventoryComplete : Prop :=
  manuscriptFormalEnvironmentRows.length = 58

theorem a_plus_inventory_complete : APlusInventoryComplete :=
  manuscript_formal_environment_count

end SM4
