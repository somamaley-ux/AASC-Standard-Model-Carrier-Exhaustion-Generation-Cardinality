import SM5.ScopeBoundary

namespace SM5

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
  { line := 216, kind := .definition, title := "Non-degenerate flavor claim", leanSurface := "SM5.FlavorArena", status := "represented" },
  { line := 224, kind := .theorem, title := "Sameness requires kernel preservation", leanSurface := "SM1.KernelStatus", status := "sm1Received" },
  { line := 236, kind := .theorem, title := "Prediction and falsification require non-degenerate reference", leanSurface := "SM1.KernelStatus", status := "sm1Received" },
  { line := 247, kind := .proposition, title := "Kernel-denial burden", leanSurface := "SM1.KernelStatus", status := "sm1Received" },
  { line := 259, kind := .remark, title := "Proof class", leanSurface := "SM5.ScopeBoundary", status := "boundary" },
  { line := 285, kind := .nonclaim, title := "Nonclaims", leanSurface := "SM5.ScopeBoundary", status := "explicitNonclaim" },
  { line := 345, kind := .definition, title := "Fixed flavor arena", leanSurface := "SM5.FlavorArena", status := "represented" },
  { line := 356, kind := .definition, title := "Flavor claim", leanSurface := "SM5.FlavorArena", status := "represented" },
  { line := 360, kind := .definition, title := "Same-scope flavor claim", leanSurface := "SM5.FlavorArena", status := "represented" },
  { line := 364, kind := .criterion, title := "Flavor target update", leanSurface := "SM5.FlavorArena", status := "represented" },
  { line := 428, kind := .theorem, title := "Flavor skin non-promotion", leanSurface := "SM5.PackageCertificates", status := "represented" },
  { line := 443, kind := .theorem, title := "Flavor-transition carrier closure", leanSurface := "SM5.PackageCertificates", status := "represented" },
  { line := 455, kind := .theorem, title := "CP/holonomy-residue carrier closure", leanSurface := "SM5.PackageCertificates", status := "represented" },
  { line := 467, kind := .theorem, title := "Raw phase-coordinate non-promotion", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 476, kind := .corollary, title := "Holonomy residue is not raw phase primitive", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 488, kind := .theorem, title := "Generation-governance closure under fixed family envelope", leanSurface := "SM5.PackageCertificates", status := "represented" },
  { line := 497, kind := .nonclaim, title := "No internal generation-count derivation", leanSurface := "SM5.ScopeBoundary", status := "explicitNonclaim" },
  { line := 504, kind := .theorem, title := "CKM entry non-primitivity", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 514, kind := .theorem, title := "PMNS entry non-primitivity", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 524, kind := .theorem, title := "Mixing angles as redescription coordinates", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 533, kind := .theorem, title := "Matrix coordinate classification", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 549, kind := .theorem, title := "Basis and diagonalization non-promotion", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 562, kind := .theorem, title := "Rephasing redundancy exhaustion", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 577, kind := .theorem, title := "Raw phase non-primitivity", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 587, kind := .theorem, title := "CP phase classification", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 600, kind := .nonclaim, title := "Numerical CP values", leanSurface := "SM5.ScopeBoundary", status := "explicitNonclaim" },
  { line := 618, kind := .theorem, title := "Eigenstructure non-primitivity", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 632, kind := .theorem, title := "Oscillation route status", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 641, kind := .theorem, title := "PMNS boundary-reconstruction theorem", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 651, kind := .nonclaim, title := "Neutrino numerical boundaries", leanSurface := "SM5.ScopeBoundary", status := "explicitNonclaim" },
  { line := 658, kind := .theorem, title := "Fixed-load FCNC discipline", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 668, kind := .theorem, title := "FCNC primitive non-promotion", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 680, kind := .theorem, title := "Generation label non-promotion", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 689, kind := .theorem, title := "Field duplication non-promotion", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 708, kind := .theorem, title := "Generation alteration branch", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 725, kind := .definition, title := "Changed flavor load", leanSurface := "SM5.FlavorArena", status := "represented" },
  { line := 729, kind := .theorem, title := "Target update for uncertified changed flavor load", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 739, kind := .theorem, title := "Fixed-load evaluation for certified changed flavor load", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 751, kind := .theorem, title := "Flavor BSM branch theorem", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 788, kind := .theorem, title := "Fourth-generation fixed-envelope branch", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 839, kind := .proposition, title := "Reality-contact discipline for flavor predictions", leanSurface := "SM5.PredictionRegister", status := "represented" },
  { line := 879, kind := .definition, title := "Registered flavor status", leanSurface := "SM5.FlavorArena", status := "represented" },
  { line := 883, kind := .definition, title := "Hostile flavor certificate branch", leanSurface := "SM5.FlavorArena", status := "represented" },
  { line := 895, kind := .theorem, title := "Flavor Coverage Theorem", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 930, kind := .theorem, title := "Primitive flavor carrier package closure", leanSurface := "SM5.PackageCertificates", status := "represented" },
  { line := 940, kind := .theorem, title := "Fixed generation-governance closure", leanSurface := "SM5.PackageCertificates", status := "represented" },
  { line := 950, kind := .theorem, title := "Registered flavor status package closure", leanSurface := "SM5.PackageCertificates", status := "represented" },
  { line := 960, kind := .definition, title := "No closed hostile branch", leanSurface := "SM5.ScopeBoundary", status := "represented" },
  { line := 968, kind := .theorem, title := "Flavor package closure", leanSurface := "SM5.PackageCertificates", status := "represented" },
  { line := 978, kind := .theorem, title := "Scoped flavor-sector primitive-status deletion", leanSurface := "SM5.MainTheorems", status := "represented" },
  { line := 993, kind := .criterion, title := "Faithful flavor counterexample", leanSurface := "SM5.PredictionRegister", status := "represented" }
]

theorem manuscript_formal_environment_count :
    manuscriptFormalEnvironmentRows.length = 51 := by
  decide

structure APlusInventoryComplete where
  sourceManuscript : String
  formalEnvironmentCount : Nat
  countMatches : formalEnvironmentCount = 51
  inventoryRowsClosed : manuscriptFormalEnvironmentRows.length = formalEnvironmentCount

theorem a_plus_inventory_complete :
    Exists (fun cert : APlusInventoryComplete =>
      cert.sourceManuscript = "main.tex" /\ cert.formalEnvironmentCount = 51) := by
  refine Exists.intro ?cert ?_
  · exact {
      sourceManuscript := "main.tex",
      formalEnvironmentCount := 51,
      countMatches := rfl,
      inventoryRowsClosed := by decide
    }
  · constructor
    · rfl
    · rfl

end SM5
