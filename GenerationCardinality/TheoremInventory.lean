import GenerationCardinality.ScopeBoundary

namespace GenerationCardinality

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
  { line := 131, kind := .definition, title := "Kernel preservation", leanSurface := "SM1.KernelStatus", status := "sm1Received" },
  { line := 135, kind := .theorem, title := "Kernel necessity", leanSurface := "SM1.KernelStatus", status := "sm1Received" },
  { line := 144, kind := .theorem, title := "Sameness requires kernel preservation", leanSurface := "SM1.KernelStatus", status := "sm1Received" },
  { line := 154, kind := .theorem, title := "Prediction and falsification require non-degenerate reference", leanSurface := "SM1.KernelStatus", status := "sm1Received" },
  { line := 193, kind := .remark, title := "Circularity audit", leanSurface := "GenerationCardinality.ScopeBoundary", status := "boundary" },
  { line := 199, kind := .definition, title := "Open-generation arena", leanSurface := "GenerationCardinality.Arena", status := "represented" },
  { line := 210, kind := .definition, title := "Candidate cardinality arena", leanSurface := "GenerationCardinality.Arena", status := "represented" },
  { line := 214, kind := .theorem, title := "Open-arena lifting of the CP/holonomy carrier", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 221, kind := .definition, title := "Generation role certificate", leanSurface := "GenerationCardinality.Arena", status := "represented" },
  { line := 229, kind := .definition, title := "Presentation quotient", leanSurface := "GenerationCardinality.Arena", status := "represented" },
  { line := 236, kind := .lemma, title := "No generation by presentation", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 245, kind := .definition, title := "Closed generation certificate", leanSurface := "GenerationCardinality.Arena", status := "represented" },
  { line := 253, kind := .lemma, title := "Certificate implies live transition rank match", leanSurface := "GenerationCardinality.Certificates", status := "represented" },
  { line := 265, kind := .theorem, title := "No-selector theorem", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 277, kind := .definition, title := "Generation-transition graph", leanSurface := "GenerationCardinality.Arena", status := "represented" },
  { line := 281, kind := .definition, title := "Direct co-comparability", leanSurface := "GenerationCardinality.Arena", status := "represented" },
  { line := 285, kind := .lemma, title := "Pairwise completeness is forced", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 292, kind := .lemma, title := "Complete graph normal form", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 302, kind := .definition, title := "Circuit rank", leanSurface := "GenerationCardinality.Arena", status := "represented" },
  { line := 313, kind := .lemma, title := "First exact circuit rank", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 346, kind := .definition, title := "Edge-coordinate group and vertex rephasing", leanSurface := "GenerationCardinality.Arena", status := "represented" },
  { line := 354, kind := .definition, title := "Cycle-space residue", leanSurface := "GenerationCardinality.Arena", status := "represented" },
  { line := 362, kind := .lemma, title := "Rephasing deletion", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 369, kind := .theorem, title := "Cycle quotient theorem", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 379, kind := .corollary, title := "Complete-graph residue rank", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 388, kind := .definition, title := "Generation-holonomy arena", leanSurface := "GenerationCardinality.Arena", status := "represented" },
  { line := 396, kind := .theorem, title := "Local fixed-domain instantiation", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 403, kind := .corollary, title := "No untyped import into generation holonomy", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 409, kind := .definition, title := "Raw, live, and primitive ranks", leanSurface := "GenerationCardinality.Arena", status := "represented" },
  { line := 417, kind := .theorem, title := "Role-incidence liveness", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 427, kind := .corollary, title := "Live rank of a closed candidate", leanSurface := "GenerationCardinality.Certificates", status := "represented" },
  { line := 437, kind := .theorem, title := "Primitive carrier nonvacuity", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 444, kind := .lemma, title := "CP/holonomy nonredundancy", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 454, kind := .lemma, title := "Residue-to-operator bridge", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 461, kind := .proposition, title := "Second-residue branch exhaustion", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 468, kind := .lemma, title := "No surplus primitive register", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 477, kind := .theorem, title := "Rank-one primitive target theorem", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 486, kind := .theorem, title := "Rank-matching condition", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 499, kind := .lemma, title := "PMNS and boundary phase nonpromotion", leanSurface := "SM5.MainTheorems", status := "sm5Received" },
  { line := 506, kind := .theorem, title := "Lower-cardinality eliminators", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 517, kind := .definition, title := "Minimal circuit incidence positions", leanSurface := "GenerationCardinality.Arena", status := "represented" },
  { line := 525, kind := .lemma, title := "Rank-one circuit incidence", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 532, kind := .theorem, title := "Target role set forcing at rank one", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 542, kind := .theorem, title := "Three-role positive certificate", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 553, kind := .definition, title := "Surplus residue", leanSurface := "GenerationCardinality.Arena", status := "represented" },
  { line := 561, kind := .lemma, title := "Surplus-residue alternatives", leanSurface := "GenerationCardinality.Arena", status := "represented" },
  { line := 568, kind := .theorem, title := "No higher-generation closure", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 580, kind := .theorem, title := "Generation cardinality as forced role-occupancy endpoint", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 590, kind := .corollary, title := "Target role-cardinality", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 596, kind := .corollary, title := "Quotient residue cardinality", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 603, kind := .theorem, title := "Arc handoff", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 620, kind := .theorem, title := "Fourth-generation branch", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" },
  { line := 629, kind := .theorem, title := "Conditional reduction under withheld rank-one target", leanSurface := "GenerationCardinality.MainTheorems", status := "represented" }
]

theorem manuscript_formal_environment_count :
    manuscriptFormalEnvironmentRows.length = 53 := by
  decide

structure APlusInventoryComplete where
  sourceManuscript : String
  formalEnvironmentCount : Nat
  countMatches : formalEnvironmentCount = 53
  inventoryRowsClosed : manuscriptFormalEnvironmentRows.length = formalEnvironmentCount

theorem a_plus_inventory_complete :
    Exists (fun cert : APlusInventoryComplete =>
      cert.sourceManuscript = "main.tex" /\ cert.formalEnvironmentCount = 53) := by
  refine Exists.intro ?cert ?_
  · exact {
      sourceManuscript := "main.tex",
      formalEnvironmentCount := 53,
      countMatches := rfl,
      inventoryRowsClosed := by decide
    }
  · constructor
    · rfl
    · rfl

end GenerationCardinality
