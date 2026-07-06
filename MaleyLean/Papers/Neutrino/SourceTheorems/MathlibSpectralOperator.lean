import Mathlib
import MaleyLean.Papers.Neutrino.SourceTheorems.EvaluationFrontier

namespace MaleyLean

namespace Neutrino

/--
Mathlib-backed three-flavor mass-squared operator.

The carrier is `Fin 3`; the operator is a `3 x 3` matrix; and the characteristic
invariant is the matrix characteristic polynomial. This is intentionally still
symbolic: no observed mass values, fitted matrix entries, or eigenvalue/root
representatives are selected.
-/
abbrev ThreeFlavorMassSquaredMatrix (R : Type) :=
  Matrix (Fin 3) (Fin 3) R

def diagonalThreeFlavorMassSquaredOperator
  {R : Type}
  [Zero R]
  (m2 : Fin 3 -> R) :
  ThreeFlavorMassSquaredMatrix R :=
  Matrix.diagonal m2

noncomputable def threeFlavorCharacteristicPolynomial
  {R : Type}
  [CommRing R]
  (M : ThreeFlavorMassSquaredMatrix R) :
  Polynomial R :=
  Matrix.charpoly M

theorem diagonalThreeFlavorCharacteristicPolynomial_eq_prod
  {R : Type}
  [CommRing R]
  (m2 : Fin 3 -> R) :
  threeFlavorCharacteristicPolynomial
      (diagonalThreeFlavorMassSquaredOperator m2) =
    ∏ i : Fin 3, (Polynomial.X - Polynomial.C (m2 i)) := by
  exact Matrix.charpoly_diagonal m2

/--
Mathlib-backed diagonal operator data.

This specializes the standing mass operator to the diagonal mass-squared
operator determined by a symbolic three-level assignment `m2`. The
characteristic polynomial is then mathlib's `Matrix.charpoly` for that diagonal
operator.
-/
structure ThreeFlavorDiagonalMathlibSpectralProofData
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (R : Type)
  [CommRing R] where
  massSquaredLevelOf : Fin 3 -> R
  SplittingClass : Type
  solarAtmosphericSplittingPair : R -> R -> SplittingClass
  ratioCandidateSplittingClass : C.Ratio -> SplittingClass
  characteristicClassReadsMR3Shape :
    C.Ratio -> Polynomial R -> M.Shape -> Prop
  currentCharacteristicReadback :
    characteristicClassReadsMR3Shape
      C.ratio
      (threeFlavorCharacteristicPolynomial
        (diagonalThreeFlavorMassSquaredOperator massSquaredLevelOf))
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

/--
Readback from a diagonal three-flavor characteristic polynomial to a
splitting-ratio class.

This is the next mathematical bridge: the characteristic polynomial exposes the
three symbolic mass-squared levels, and this object certifies a ratio class of
two mass-squared gaps without importing an absolute scale, fitted texture,
observed spectrum, or selected eigenvalue/root representative.
-/
structure ThreeFlavorSplittingRatioReadback
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (R : Type)
  [CommRing R] where
  massSquaredLevelOf : Fin 3 -> R
  GapClass : Type
  gapClassOf : R -> R -> GapClass
  RatioClass : Type
  ratioClassOfGaps : GapClass -> GapClass -> RatioClass
  solarGap : GapClass
  atmosphericGap : GapClass
  solarGap_eq :
    solarGap =
      gapClassOf (massSquaredLevelOf 1) (massSquaredLevelOf 0)
  atmosphericGap_eq :
    atmosphericGap =
      gapClassOf (massSquaredLevelOf 2) (massSquaredLevelOf 0)
  splittingRatioClass : RatioClass
  splittingRatioClass_eq :
    splittingRatioClass = ratioClassOfGaps solarGap atmosphericGap
  characteristicPolynomial :
    Polynomial R
  characteristicPolynomial_eq :
    characteristicPolynomial =
      threeFlavorCharacteristicPolynomial
        (diagonalThreeFlavorMassSquaredOperator massSquaredLevelOf)
  characteristicPolynomial_prod_eq :
    characteristicPolynomial =
      ∏ i : Fin 3, (Polynomial.X - Polynomial.C (massSquaredLevelOf i))
  shapeClassReadback :
    C.Ratio -> Polynomial R -> M.Shape -> Prop
  currentShapeReadback :
    shapeClassReadback
      C.ratio
      characteristicPolynomial
      (M.shapeOfRatio C.ratio)
  ratioClassReadbackCertified : Prop
  twoIndependentGapsCertified : Prop
  quotientStableGapRatio : Prop
  scaleFreeGapRatio : Prop
  noAbsoluteMassScaleImport : Prop
  noObservedGapImport : Prop
  noEigenvalueRootSelection : Prop
  noOrderingFitImport : Prop
  sameStandingRatioTarget : Prop

def ThreeFlavorSplittingRatioReadbackPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {R : Type}
  [CommRing R]
  (B : ThreeFlavorSplittingRatioReadback M R) : Prop :=
  B.ratioClassReadbackCertified /\
    B.twoIndependentGapsCertified /\
      B.quotientStableGapRatio /\
        B.scaleFreeGapRatio /\
          B.noAbsoluteMassScaleImport /\
            B.noObservedGapImport /\
              B.noEigenvalueRootSelection /\
                B.noOrderingFitImport /\
                  B.sameStandingRatioTarget

theorem splittingRatioReadbackUsesDiagonalCharpolyProduct
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {R : Type}
  [CommRing R]
  (B : ThreeFlavorSplittingRatioReadback M R) :
  B.characteristicPolynomial =
    ∏ i : Fin 3, (Polynomial.X - Polynomial.C (B.massSquaredLevelOf i)) :=
  B.characteristicPolynomial_prod_eq

def threeFlavorSolarGap
  {R : Type}
  [Sub R]
  (m2 : Fin 3 -> R) : R :=
  m2 1 - m2 0

def threeFlavorAtmosphericGap
  {R : Type}
  [Sub R]
  (m2 : Fin 3 -> R) : R :=
  m2 2 - m2 0

def threeFlavorGapRatio
  {R : Type}
  [Field R]
  (m2 : Fin 3 -> R) : R :=
  threeFlavorSolarGap m2 / threeFlavorAtmosphericGap m2

theorem threeFlavorSolarGap_shift
  {R : Type}
  [Ring R]
  (m2 : Fin 3 -> R)
  (s : R) :
  threeFlavorSolarGap (fun i => m2 i + s) =
    threeFlavorSolarGap m2 := by
  simp [threeFlavorSolarGap]

theorem threeFlavorAtmosphericGap_shift
  {R : Type}
  [Ring R]
  (m2 : Fin 3 -> R)
  (s : R) :
  threeFlavorAtmosphericGap (fun i => m2 i + s) =
    threeFlavorAtmosphericGap m2 := by
  simp [threeFlavorAtmosphericGap]

theorem threeFlavorGapRatio_shift
  {R : Type}
  [Field R]
  (m2 : Fin 3 -> R)
  (s : R) :
  threeFlavorGapRatio (fun i => m2 i + s) =
    threeFlavorGapRatio m2 := by
  simp
    [threeFlavorGapRatio,
      threeFlavorSolarGap_shift,
      threeFlavorAtmosphericGap_shift]

theorem threeFlavorSolarGap_scale
  {R : Type}
  [CommRing R]
  (m2 : Fin 3 -> R)
  (a : R) :
  threeFlavorSolarGap (fun i => a * m2 i) =
    a * threeFlavorSolarGap m2 := by
  simp [threeFlavorSolarGap]
  ring

theorem threeFlavorAtmosphericGap_scale
  {R : Type}
  [CommRing R]
  (m2 : Fin 3 -> R)
  (a : R) :
  threeFlavorAtmosphericGap (fun i => a * m2 i) =
    a * threeFlavorAtmosphericGap m2 := by
  simp [threeFlavorAtmosphericGap]
  ring

theorem threeFlavorGapRatio_scale
  {R : Type}
  [Field R]
  (m2 : Fin 3 -> R)
  (a : R)
  (ha : Not (a = 0)) :
  threeFlavorGapRatio (fun i => a * m2 i) =
    threeFlavorGapRatio m2 := by
  simp
    [threeFlavorGapRatio,
      threeFlavorSolarGap_scale,
      threeFlavorAtmosphericGap_scale]
  field_simp [ha]

/--
Concrete algebraic gap-ratio readback.

This upgrades the splitting-ratio bridge from an abstract ratio class to the
symbolic field expression
`(m2 1 - m2 0) / (m2 2 - m2 0)`, while retaining the AASC controls that prevent
absolute-scale import, empirical gap import, ordering fit, or root selection.
-/
structure ThreeFlavorGapRatioAlgebra
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (R : Type)
  [Field R] where
  massSquaredLevelOf : Fin 3 -> R
  atmosphericGapNonzero :
    Not (threeFlavorAtmosphericGap massSquaredLevelOf = 0)
  shapeClassReadback :
    C.Ratio -> Polynomial R -> M.Shape -> Prop
  currentShapeReadback :
    shapeClassReadback
      C.ratio
      (threeFlavorCharacteristicPolynomial
        (diagonalThreeFlavorMassSquaredOperator massSquaredLevelOf))
      (M.shapeOfRatio C.ratio)
  ratioClassReadbackCertified : Prop
  twoIndependentGapsCertified : Prop
  quotientStableGapRatio : Prop
  scaleFreeGapRatio : Prop
  noAbsoluteMassScaleImport : Prop
  noObservedGapImport : Prop
  noEigenvalueRootSelection : Prop
  noOrderingFitImport : Prop
  sameStandingRatioTarget : Prop

def ThreeFlavorGapRatioAlgebraPasses
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {R : Type}
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) : Prop :=
  A.ratioClassReadbackCertified /\
    A.twoIndependentGapsCertified /\
      A.quotientStableGapRatio /\
        A.scaleFreeGapRatio /\
          A.noAbsoluteMassScaleImport /\
            A.noObservedGapImport /\
              A.noEigenvalueRootSelection /\
                A.noOrderingFitImport /\
                  A.sameStandingRatioTarget

noncomputable def gapRatioAlgebraAsSplittingReadback
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) :
  ThreeFlavorSplittingRatioReadback M R :=
  { massSquaredLevelOf := A.massSquaredLevelOf
    GapClass := R
    gapClassOf := fun hi lo => hi - lo
    RatioClass := R
    ratioClassOfGaps := fun solar atmospheric => solar / atmospheric
    solarGap := threeFlavorSolarGap A.massSquaredLevelOf
    atmosphericGap := threeFlavorAtmosphericGap A.massSquaredLevelOf
    solarGap_eq := rfl
    atmosphericGap_eq := rfl
    splittingRatioClass := threeFlavorGapRatio A.massSquaredLevelOf
    splittingRatioClass_eq := rfl
    characteristicPolynomial :=
      threeFlavorCharacteristicPolynomial
        (diagonalThreeFlavorMassSquaredOperator A.massSquaredLevelOf)
    characteristicPolynomial_eq := rfl
    characteristicPolynomial_prod_eq :=
      diagonalThreeFlavorCharacteristicPolynomial_eq_prod
        A.massSquaredLevelOf
    shapeClassReadback := A.shapeClassReadback
    currentShapeReadback := A.currentShapeReadback
    ratioClassReadbackCertified := A.ratioClassReadbackCertified
    twoIndependentGapsCertified := A.twoIndependentGapsCertified
    quotientStableGapRatio := A.quotientStableGapRatio
    scaleFreeGapRatio := A.scaleFreeGapRatio
    noAbsoluteMassScaleImport := A.noAbsoluteMassScaleImport
    noObservedGapImport := A.noObservedGapImport
    noEigenvalueRootSelection := A.noEigenvalueRootSelection
    noOrderingFitImport := A.noOrderingFitImport
    sameStandingRatioTarget := A.sameStandingRatioTarget }

theorem gapRatioAlgebraGivesSplittingReadbackPasses
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (hA : ThreeFlavorGapRatioAlgebraPasses A) :
  ThreeFlavorSplittingRatioReadbackPasses
    (gapRatioAlgebraAsSplittingReadback M R A) := by
  exact hA

theorem gapRatioAlgebra_shiftInvariant
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {R : Type}
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (s : R) :
  threeFlavorGapRatio (fun i => A.massSquaredLevelOf i + s) =
    threeFlavorGapRatio A.massSquaredLevelOf :=
  threeFlavorGapRatio_shift A.massSquaredLevelOf s

theorem gapRatioAlgebra_scaleInvariant
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {R : Type}
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (a : R)
  (ha : Not (a = 0)) :
  threeFlavorGapRatio (fun i => a * A.massSquaredLevelOf i) =
    threeFlavorGapRatio A.massSquaredLevelOf :=
  threeFlavorGapRatio_scale A.massSquaredLevelOf a ha

noncomputable def splittingRatioReadbackAsDiagonalMathlibData
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (R : Type)
  [CommRing R]
  (B : ThreeFlavorSplittingRatioReadback M R)
  (hB : ThreeFlavorSplittingRatioReadbackPasses B)
  (exactlyThreeMassStates : Prop)
  (hexactlyThree : exactlyThreeMassStates)
  (threeFlavorCarrierAdmitted : Prop)
  (hcarrier : threeFlavorCarrierAdmitted)
  (massSquaredSplittingCarrierStanding : Prop)
  (hstanding : massSquaredSplittingCarrierStanding)
  (spectralOperatorDerivedFromSplittings : Prop)
  (hoperator : spectralOperatorDerivedFromSplittings)
  (characteristicClassPolynomialLike : Prop)
  (hpolyLike : characteristicClassPolynomialLike)
  (notMerelyShapeMapRelabel : Prop)
  (hnotRelabel : notMerelyShapeMapRelabel) :
  ThreeFlavorDiagonalMathlibSpectralProofData M R := by
  rcases hB with
    ⟨hratioReadback, htwoGaps, hquotient, hscale, habsolute,
      hobserved, hroot, hordering, htarget⟩
  exact
  { massSquaredLevelOf := B.massSquaredLevelOf
    SplittingClass := B.RatioClass
    solarAtmosphericSplittingPair := fun a b =>
      B.ratioClassOfGaps (B.gapClassOf a b) B.atmosphericGap
    ratioCandidateSplittingClass := fun _ =>
      B.splittingRatioClass
    characteristicClassReadsMR3Shape := B.shapeClassReadback
    currentCharacteristicReadback := by
      rw [← B.characteristicPolynomial_eq]
      exact B.currentShapeReadback
    exactlyThreeMassStates := exactlyThreeMassStates
    exactlyThreeMassStates_proof := hexactlyThree
    threeFlavorCarrierAdmitted := threeFlavorCarrierAdmitted
    threeFlavorCarrierAdmitted_proof := hcarrier
    massSquaredSplittingCarrierStanding :=
      massSquaredSplittingCarrierStanding
    massSquaredSplittingCarrierStanding_proof := hstanding
    twoIndependentSplittingsCertified :=
      B.twoIndependentGapsCertified
    twoIndependentSplittingsCertified_proof := htwoGaps
    spectralOperatorDerivedFromSplittings :=
      spectralOperatorDerivedFromSplittings
    spectralOperatorDerivedFromSplittings_proof := hoperator
    characteristicClassDerivedFromOperator :=
      B.ratioClassReadbackCertified
    characteristicClassDerivedFromOperator_proof := hratioReadback
    characteristicClassPolynomialLike := characteristicClassPolynomialLike
    characteristicClassPolynomialLike_proof := hpolyLike
    sameRatioTargetReadback := B.sameStandingRatioTarget
    sameRatioTargetReadback_proof := htarget
    quotientStableReadback := B.quotientStableGapRatio
    quotientStableReadback_proof := hquotient
    scaleStatusControlled :=
      B.scaleFreeGapRatio
    scaleStatusControlled_proof := hscale
    noAbsoluteMassScaleImport := B.noAbsoluteMassScaleImport
    noAbsoluteMassScaleImport_proof := habsolute
    noFittedMatrixTextureImport := B.noOrderingFitImport
    noFittedMatrixTextureImport_proof := hordering
    noObservedSpectrumImport := B.noObservedGapImport
    noObservedSpectrumImport_proof := hobserved
    noEigenvalueRootSelection := B.noEigenvalueRootSelection
    noEigenvalueRootSelection_proof := hroot
    notMerelyShapeMapRelabel := notMerelyShapeMapRelabel
    notMerelyShapeMapRelabel_proof := hnotRelabel }

/--
Mathlib data needed to inhabit the three-flavor source-theorem socket.

The mathematical part is concrete: `Fin 3`, a commutative coefficient ring,
`Matrix (Fin 3) (Fin 3) R`, and `Matrix.charpoly`. The AASC gates remain proof
obligations supplied by the construction paper/corpus audit.
-/
structure ThreeFlavorMathlibSpectralProofData
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (R : Type)
  [CommRing R] where
  massSquaredLevelOf : Fin 3 -> R
  SplittingClass : Type
  solarAtmosphericSplittingPair : R -> R -> SplittingClass
  ratioCandidateSplittingClass : C.Ratio -> SplittingClass
  standingMassOperatorOf :
    C.Ratio -> ThreeFlavorMassSquaredMatrix R
  characteristicClassReadsMR3Shape :
    C.Ratio -> Polynomial R -> M.Shape -> Prop
  currentCharacteristicReadback :
    characteristicClassReadsMR3Shape
      C.ratio
      (threeFlavorCharacteristicPolynomial
        (standingMassOperatorOf C.ratio))
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

noncomputable def threeFlavorMathlibDataAsProofBundle
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (R : Type)
  [CommRing R]
  (D : ThreeFlavorMathlibSpectralProofData M R) :
  ThreeFlavorMassSquaredSpectralSourceProofBundle M :=
  buildThreeFlavorMassSquaredSpectralProofBundle
    M
    (Fin 3)
    R
    D.SplittingClass
    (ThreeFlavorMassSquaredMatrix R)
    (Polynomial R)
    D.massSquaredLevelOf
    D.solarAtmosphericSplittingPair
    D.ratioCandidateSplittingClass
    D.standingMassOperatorOf
    threeFlavorCharacteristicPolynomial
    D.characteristicClassReadsMR3Shape
    D.currentCharacteristicReadback
    D.exactlyThreeMassStates
    D.exactlyThreeMassStates_proof
    D.threeFlavorCarrierAdmitted
    D.threeFlavorCarrierAdmitted_proof
    D.massSquaredSplittingCarrierStanding
    D.massSquaredSplittingCarrierStanding_proof
    D.twoIndependentSplittingsCertified
    D.twoIndependentSplittingsCertified_proof
    D.spectralOperatorDerivedFromSplittings
    D.spectralOperatorDerivedFromSplittings_proof
    D.characteristicClassDerivedFromOperator
    D.characteristicClassDerivedFromOperator_proof
    D.characteristicClassPolynomialLike
    D.characteristicClassPolynomialLike_proof
    D.sameRatioTargetReadback
    D.sameRatioTargetReadback_proof
    D.quotientStableReadback
    D.quotientStableReadback_proof
    D.scaleStatusControlled
    D.scaleStatusControlled_proof
    D.noAbsoluteMassScaleImport
    D.noAbsoluteMassScaleImport_proof
    D.noFittedMatrixTextureImport
    D.noFittedMatrixTextureImport_proof
    D.noObservedSpectrumImport
    D.noObservedSpectrumImport_proof
    D.noEigenvalueRootSelection
    D.noEigenvalueRootSelection_proof
    D.notMerelyShapeMapRelabel
    D.notMerelyShapeMapRelabel_proof

noncomputable def threeFlavorDiagonalMathlibDataAsMathlibData
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (R : Type)
  [CommRing R]
  (D : ThreeFlavorDiagonalMathlibSpectralProofData M R) :
  ThreeFlavorMathlibSpectralProofData M R :=
  { massSquaredLevelOf := D.massSquaredLevelOf
    SplittingClass := D.SplittingClass
    solarAtmosphericSplittingPair :=
      D.solarAtmosphericSplittingPair
    ratioCandidateSplittingClass :=
      D.ratioCandidateSplittingClass
    standingMassOperatorOf := fun _ =>
      diagonalThreeFlavorMassSquaredOperator D.massSquaredLevelOf
    characteristicClassReadsMR3Shape :=
      D.characteristicClassReadsMR3Shape
    currentCharacteristicReadback :=
      D.currentCharacteristicReadback
    exactlyThreeMassStates := D.exactlyThreeMassStates
    exactlyThreeMassStates_proof := D.exactlyThreeMassStates_proof
    threeFlavorCarrierAdmitted := D.threeFlavorCarrierAdmitted
    threeFlavorCarrierAdmitted_proof :=
      D.threeFlavorCarrierAdmitted_proof
    massSquaredSplittingCarrierStanding :=
      D.massSquaredSplittingCarrierStanding
    massSquaredSplittingCarrierStanding_proof :=
      D.massSquaredSplittingCarrierStanding_proof
    twoIndependentSplittingsCertified :=
      D.twoIndependentSplittingsCertified
    twoIndependentSplittingsCertified_proof :=
      D.twoIndependentSplittingsCertified_proof
    spectralOperatorDerivedFromSplittings :=
      D.spectralOperatorDerivedFromSplittings
    spectralOperatorDerivedFromSplittings_proof :=
      D.spectralOperatorDerivedFromSplittings_proof
    characteristicClassDerivedFromOperator :=
      D.characteristicClassDerivedFromOperator
    characteristicClassDerivedFromOperator_proof :=
      D.characteristicClassDerivedFromOperator_proof
    characteristicClassPolynomialLike :=
      D.characteristicClassPolynomialLike
    characteristicClassPolynomialLike_proof :=
      D.characteristicClassPolynomialLike_proof
    sameRatioTargetReadback := D.sameRatioTargetReadback
    sameRatioTargetReadback_proof :=
      D.sameRatioTargetReadback_proof
    quotientStableReadback := D.quotientStableReadback
    quotientStableReadback_proof :=
      D.quotientStableReadback_proof
    scaleStatusControlled := D.scaleStatusControlled
    scaleStatusControlled_proof :=
      D.scaleStatusControlled_proof
    noAbsoluteMassScaleImport := D.noAbsoluteMassScaleImport
    noAbsoluteMassScaleImport_proof :=
      D.noAbsoluteMassScaleImport_proof
    noFittedMatrixTextureImport := D.noFittedMatrixTextureImport
    noFittedMatrixTextureImport_proof :=
      D.noFittedMatrixTextureImport_proof
    noObservedSpectrumImport := D.noObservedSpectrumImport
    noObservedSpectrumImport_proof :=
      D.noObservedSpectrumImport_proof
    noEigenvalueRootSelection := D.noEigenvalueRootSelection
    noEigenvalueRootSelection_proof :=
      D.noEigenvalueRootSelection_proof
    notMerelyShapeMapRelabel := D.notMerelyShapeMapRelabel
    notMerelyShapeMapRelabel_proof :=
      D.notMerelyShapeMapRelabel_proof }

theorem threeFlavorMathlibDataProofBundlePasses
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (R : Type)
  [CommRing R]
  (D : ThreeFlavorMathlibSpectralProofData M R) :
  ThreeFlavorMassSquaredSpectralSourceTheoremPasses
    (threeFlavorProofBundleAsSourceTheorem
      M
      (threeFlavorMathlibDataAsProofBundle M R D)) :=
  threeFlavorProofBundleSourceTheoremPasses
    M
    (threeFlavorMathlibDataAsProofBundle M R D)

theorem threeFlavorMathlibDataAndNativeExhaustionGiveAlgebraicClassFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (R : Type)
  [CommRing R]
  (D : ThreeFlavorMathlibSpectralProofData M R)
  (G : AASCNativeOperatorExhaustionGuardrailSupport H N)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  threeFlavorProofBundleAndNativeExhaustionGiveAlgebraicClassFrontier
    (threeFlavorMathlibDataAsProofBundle M R D)
    G
    BE
    BV

theorem threeFlavorDiagonalMathlibDataAndNativeExhaustionGiveAlgebraicClassFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (R : Type)
  [CommRing R]
  (D : ThreeFlavorDiagonalMathlibSpectralProofData M R)
  (G : AASCNativeOperatorExhaustionGuardrailSupport H N)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  threeFlavorMathlibDataAndNativeExhaustionGiveAlgebraicClassFrontier
    R
    (threeFlavorDiagonalMathlibDataAsMathlibData M R D)
    G
    BE
    BV

/--
The three-flavor gap algebra also supplies a closed-expression evaluator:
the current standing ratio is read as the symbolic quotient of the solar
mass-squared gap by the atmospheric mass-squared gap.

This is deliberately not an exact numeric readout.  The expression domain is
the chosen coefficient field `R`; a later value theorem would still need a
lawful map from this expression to a certified number.
-/
noncomputable def gapRatioAlgebraAsClosedExpressionSource
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (hA : ThreeFlavorGapRatioAlgebraPasses A) :
  AASCClosedExpressionRatioSourceTheorem C := by
  rcases hA with
    ⟨hratioReadback, _htwoGaps, hquotient, _hscale, habsolute,
      hobserved, hroot, hordering, htarget⟩
  exact
  { Expression := R
    expressionOf := fun _ => threeFlavorGapRatio A.massSquaredLevelOf
    audit :=
      { targetPreserving := A.sameStandingRatioTarget
        quotientStable := A.quotientStableGapRatio
        representationIndependent := A.ratioClassReadbackCertified
        calibrationFree := A.noAbsoluteMassScaleImport
        notEmpirical := A.noObservedGapImport
        notFitted := A.noOrderingFitImport
        notBranchSelector := A.noEigenvalueRootSelection
        lawfulOnCurrent := A.ratioClassReadbackCertified }
    auditPasses :=
      ⟨htarget, hquotient, hratioReadback, habsolute, hobserved,
        hordering, hroot, hratioReadback⟩ }

theorem gapRatioAlgebraGivesClosedExpressionEvaluator
  {C : StandingRatioCertificate}
  (M : MR3SpectralSourceAdmission C)
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (hA : ThreeFlavorGapRatioAlgebraPasses A) :
  HasCurrentRatioEvaluatorAtStrength C .closedExpression :=
  closedExpressionSourceGivesClosedExpressionStrengthEvaluator
    C
    (gapRatioAlgebraAsClosedExpressionSource M R A hA)

noncomputable def gapRatioAlgebraSingletonGivesCurrentClosedExpressionEvaluation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (hsingle : HybridJointRestrictionSingleton H) :
  CurrentStandingRatioEvaluation C :=
  singletonWithClosedExpressionSourceGivesCurrentEvaluation
    hsingle
    (gapRatioAlgebraAsClosedExpressionSource M R A hA)

def gapRatioAlgebraAndExactBlockerGiveClosedExpressionFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9ClosedExpressionFrontier C :=
  closedExpressionSourceAndBlockerGiveClosedExpressionFrontier
    C
    (gapRatioAlgebraAsClosedExpressionSource M R A hA)
    BV

/--
Internal shape anchor for evaluating the three-flavor gap ratio.

This is the non-empirical replacement for a one-mass or one-gap import.  It
does not insert observed values.  Instead it asserts that the admitted
three-level shape itself supplies a canonical ratio in the coefficient field
and proves that this ratio is the symbolic gap quotient already read from the
current branch.
-/
structure ThreeFlavorInternalGapShapeAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) where
  canonicalRatio : R
  canonicalRatio_eq_gapRatio :
    canonicalRatio = threeFlavorGapRatio A.massSquaredLevelOf
  internalShapeDeterminesRatio : Prop
  internalShapeDeterminesRatio_proof : internalShapeDeterminesRatio
  noOneAnchorImport : Prop
  noOneAnchorImport_proof : noOneAnchorImport
  representativeBranchCollapsedModuloSkin : Prop
  representativeBranchCollapsedModuloSkin_proof :
    representativeBranchCollapsedModuloSkin
  allUnresolvedFreedomsDischarged : Prop
  allUnresolvedFreedomsDischarged_proof :
    allUnresolvedFreedomsDischarged
  calibrationPrior : Prop
  calibrationPrior_proof : calibrationPrior
  transportNeutralOrDischarged : Prop
  transportNeutralOrDischarged_proof :
    transportNeutralOrDischarged
  scaleStatusFixed : Prop
  scaleStatusFixed_proof : scaleStatusFixed
  noHiddenNumericalSelector : Prop
  noHiddenNumericalSelector_proof : noHiddenNumericalSelector
  noEmpiricalFitImport : Prop
  noEmpiricalFitImport_proof : noEmpiricalFitImport

def internalGapShapeAnchorValue
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {R : Type}
  [Field R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  (S : ThreeFlavorInternalGapShapeAnchor R A) : R :=
  S.canonicalRatio

theorem internalGapShapeAnchorValue_eq_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {R : Type}
  [Field R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  (S : ThreeFlavorInternalGapShapeAnchor R A) :
  internalGapShapeAnchorValue S =
    threeFlavorGapRatio A.massSquaredLevelOf :=
  S.canonicalRatio_eq_gapRatio

/--
Normalized internal three-level shape.

This is the first constructive form of the internal anchor.  It says the
admitted mass-squared shape is fixed, after the already-allowed affine/scale
normalization, as `(0, r, 1)`.  That is enough to compute the gap ratio as
`r` without importing an observed mass, observed gap, or fitted ordering.
-/
structure ThreeFlavorNormalizedGapShape
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) where
  normalizedRatio : R
  level0_eq_zero : A.massSquaredLevelOf 0 = 0
  level1_eq_ratio : A.massSquaredLevelOf 1 = normalizedRatio
  level2_eq_one : A.massSquaredLevelOf 2 = 1
  internalShapeDeterminesRatio : Prop
  internalShapeDeterminesRatio_proof : internalShapeDeterminesRatio
  noOneAnchorImport : Prop
  noOneAnchorImport_proof : noOneAnchorImport
  representativeBranchCollapsedModuloSkin : Prop
  representativeBranchCollapsedModuloSkin_proof :
    representativeBranchCollapsedModuloSkin
  allUnresolvedFreedomsDischarged : Prop
  allUnresolvedFreedomsDischarged_proof :
    allUnresolvedFreedomsDischarged
  calibrationPrior : Prop
  calibrationPrior_proof : calibrationPrior
  transportNeutralOrDischarged : Prop
  transportNeutralOrDischarged_proof :
    transportNeutralOrDischarged
  scaleStatusFixed : Prop
  scaleStatusFixed_proof : scaleStatusFixed
  noHiddenNumericalSelector : Prop
  noHiddenNumericalSelector_proof : noHiddenNumericalSelector
  noEmpiricalFitImport : Prop
  noEmpiricalFitImport_proof : noEmpiricalFitImport

theorem normalizedGapShape_ratio_eq_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {R : Type}
  [Field R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  (S : ThreeFlavorNormalizedGapShape R A) :
  S.normalizedRatio = threeFlavorGapRatio A.massSquaredLevelOf := by
  unfold threeFlavorGapRatio threeFlavorSolarGap threeFlavorAtmosphericGap
  rw [S.level0_eq_zero, S.level1_eq_ratio, S.level2_eq_one]
  simp

def normalizedGapShapeAsInternalAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorNormalizedGapShape R A) :
  ThreeFlavorInternalGapShapeAnchor R A :=
  { canonicalRatio := S.normalizedRatio
    canonicalRatio_eq_gapRatio :=
      normalizedGapShape_ratio_eq_gapRatio S
    internalShapeDeterminesRatio := S.internalShapeDeterminesRatio
    internalShapeDeterminesRatio_proof :=
      S.internalShapeDeterminesRatio_proof
    noOneAnchorImport := S.noOneAnchorImport
    noOneAnchorImport_proof := S.noOneAnchorImport_proof
    representativeBranchCollapsedModuloSkin :=
      S.representativeBranchCollapsedModuloSkin
    representativeBranchCollapsedModuloSkin_proof :=
      S.representativeBranchCollapsedModuloSkin_proof
    allUnresolvedFreedomsDischarged :=
      S.allUnresolvedFreedomsDischarged
    allUnresolvedFreedomsDischarged_proof :=
      S.allUnresolvedFreedomsDischarged_proof
    calibrationPrior := S.calibrationPrior
    calibrationPrior_proof := S.calibrationPrior_proof
    transportNeutralOrDischarged := S.transportNeutralOrDischarged
    transportNeutralOrDischarged_proof :=
      S.transportNeutralOrDischarged_proof
    scaleStatusFixed := S.scaleStatusFixed
    scaleStatusFixed_proof := S.scaleStatusFixed_proof
    noHiddenNumericalSelector := S.noHiddenNumericalSelector
    noHiddenNumericalSelector_proof :=
      S.noHiddenNumericalSelector_proof
    noEmpiricalFitImport := S.noEmpiricalFitImport
    noEmpiricalFitImport_proof := S.noEmpiricalFitImport_proof }

/--
Affine-normalized internal three-level shape.

This is the invariant form of the normalized-shape constructor.  The admitted
levels need not literally be `(0, r, 1)`; it is enough that an internally
certified nonzero common scale and shift send them to `(0, r, 1)`.  Since the
gap ratio is shift-invariant and nonzero-scale-invariant, Lean can still read
the original branch as the same `r`.
-/
structure ThreeFlavorAffineNormalizedGapShape
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) where
  normalizedRatio : R
  scale : R
  shift : R
  scale_ne_zero : Not (scale = 0)
  affineLevel0_eq_zero : scale * A.massSquaredLevelOf 0 + shift = 0
  affineLevel1_eq_ratio :
    scale * A.massSquaredLevelOf 1 + shift = normalizedRatio
  affineLevel2_eq_one : scale * A.massSquaredLevelOf 2 + shift = 1
  internalShapeDeterminesRatio : Prop
  internalShapeDeterminesRatio_proof : internalShapeDeterminesRatio
  noOneAnchorImport : Prop
  noOneAnchorImport_proof : noOneAnchorImport
  representativeBranchCollapsedModuloSkin : Prop
  representativeBranchCollapsedModuloSkin_proof :
    representativeBranchCollapsedModuloSkin
  allUnresolvedFreedomsDischarged : Prop
  allUnresolvedFreedomsDischarged_proof :
    allUnresolvedFreedomsDischarged
  calibrationPrior : Prop
  calibrationPrior_proof : calibrationPrior
  transportNeutralOrDischarged : Prop
  transportNeutralOrDischarged_proof :
    transportNeutralOrDischarged
  scaleStatusFixed : Prop
  scaleStatusFixed_proof : scaleStatusFixed
  noHiddenNumericalSelector : Prop
  noHiddenNumericalSelector_proof : noHiddenNumericalSelector
  noEmpiricalFitImport : Prop
  noEmpiricalFitImport_proof : noEmpiricalFitImport

theorem affineNormalizedGapShape_ratio_eq_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {R : Type}
  [Field R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  (S : ThreeFlavorAffineNormalizedGapShape R A) :
  S.normalizedRatio = threeFlavorGapRatio A.massSquaredLevelOf := by
  let affineLevel : Fin 3 -> R :=
    fun i => S.scale * A.massSquaredLevelOf i + S.shift
  have hnormalized :
      S.normalizedRatio = threeFlavorGapRatio affineLevel := by
    unfold threeFlavorGapRatio threeFlavorSolarGap threeFlavorAtmosphericGap
    change
      S.normalizedRatio =
        ((S.scale * A.massSquaredLevelOf 1 + S.shift) -
            (S.scale * A.massSquaredLevelOf 0 + S.shift)) /
          ((S.scale * A.massSquaredLevelOf 2 + S.shift) -
            (S.scale * A.massSquaredLevelOf 0 + S.shift))
    rw [S.affineLevel0_eq_zero, S.affineLevel1_eq_ratio,
      S.affineLevel2_eq_one]
    simp
  have hshift :
      threeFlavorGapRatio affineLevel =
        threeFlavorGapRatio
          (fun i => S.scale * A.massSquaredLevelOf i) := by
    exact
      threeFlavorGapRatio_shift
        (fun i => S.scale * A.massSquaredLevelOf i)
        S.shift
  have hscale :
      threeFlavorGapRatio
          (fun i => S.scale * A.massSquaredLevelOf i) =
        threeFlavorGapRatio A.massSquaredLevelOf := by
    exact
      threeFlavorGapRatio_scale
        A.massSquaredLevelOf
        S.scale
        S.scale_ne_zero
  exact hnormalized.trans (hshift.trans hscale)

def affineNormalizedGapShapeAsInternalAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorAffineNormalizedGapShape R A) :
  ThreeFlavorInternalGapShapeAnchor R A :=
  { canonicalRatio := S.normalizedRatio
    canonicalRatio_eq_gapRatio :=
      affineNormalizedGapShape_ratio_eq_gapRatio S
    internalShapeDeterminesRatio := S.internalShapeDeterminesRatio
    internalShapeDeterminesRatio_proof :=
      S.internalShapeDeterminesRatio_proof
    noOneAnchorImport := S.noOneAnchorImport
    noOneAnchorImport_proof := S.noOneAnchorImport_proof
    representativeBranchCollapsedModuloSkin :=
      S.representativeBranchCollapsedModuloSkin
    representativeBranchCollapsedModuloSkin_proof :=
      S.representativeBranchCollapsedModuloSkin_proof
    allUnresolvedFreedomsDischarged :=
      S.allUnresolvedFreedomsDischarged
    allUnresolvedFreedomsDischarged_proof :=
      S.allUnresolvedFreedomsDischarged_proof
    calibrationPrior := S.calibrationPrior
    calibrationPrior_proof := S.calibrationPrior_proof
    transportNeutralOrDischarged := S.transportNeutralOrDischarged
    transportNeutralOrDischarged_proof :=
      S.transportNeutralOrDischarged_proof
    scaleStatusFixed := S.scaleStatusFixed
    scaleStatusFixed_proof := S.scaleStatusFixed_proof
    noHiddenNumericalSelector := S.noHiddenNumericalSelector
    noHiddenNumericalSelector_proof :=
      S.noHiddenNumericalSelector_proof
    noEmpiricalFitImport := S.noEmpiricalFitImport
    noEmpiricalFitImport_proof := S.noEmpiricalFitImport_proof }

/--
Audit gates for the canonical affine normalization.  The normalization itself
is algebraic and comes from the gap data; these fields record that using it is
licensed by the corpus/AASC side as an internal shape operation rather than a
hidden numerical selector or empirical anchor.
-/
structure ThreeFlavorCanonicalAffineNormalizationAudit
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {R : Type}
  [Field R]
  (_A : ThreeFlavorGapRatioAlgebra M R) where
  internalShapeDeterminesRatio : Prop
  internalShapeDeterminesRatio_proof : internalShapeDeterminesRatio
  noOneAnchorImport : Prop
  noOneAnchorImport_proof : noOneAnchorImport
  representativeBranchCollapsedModuloSkin : Prop
  representativeBranchCollapsedModuloSkin_proof :
    representativeBranchCollapsedModuloSkin
  allUnresolvedFreedomsDischarged : Prop
  allUnresolvedFreedomsDischarged_proof :
    allUnresolvedFreedomsDischarged
  calibrationPrior : Prop
  calibrationPrior_proof : calibrationPrior
  transportNeutralOrDischarged : Prop
  transportNeutralOrDischarged_proof :
    transportNeutralOrDischarged
  scaleStatusFixed : Prop
  scaleStatusFixed_proof : scaleStatusFixed
  noHiddenNumericalSelector : Prop
  noHiddenNumericalSelector_proof : noHiddenNumericalSelector
  noEmpiricalFitImport : Prop
  noEmpiricalFitImport_proof : noEmpiricalFitImport

noncomputable def canonicalAffineScale
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {R : Type}
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) : R :=
  (threeFlavorAtmosphericGap A.massSquaredLevelOf)⁻¹

noncomputable def canonicalAffineShift
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {R : Type}
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) : R :=
  -canonicalAffineScale A * A.massSquaredLevelOf 0

theorem canonicalAffineScale_ne_zero
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {R : Type}
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) :
  Not (canonicalAffineScale A = 0) := by
  unfold canonicalAffineScale
  exact inv_ne_zero A.atmosphericGapNonzero

theorem canonicalAffine_level0_eq_zero
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {R : Type}
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) :
  canonicalAffineScale A * A.massSquaredLevelOf 0 +
      canonicalAffineShift A = 0 := by
  unfold canonicalAffineShift
  ring

theorem canonicalAffine_level1_eq_ratio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {R : Type}
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) :
  canonicalAffineScale A * A.massSquaredLevelOf 1 +
      canonicalAffineShift A =
    threeFlavorGapRatio A.massSquaredLevelOf := by
  unfold canonicalAffineShift
  simp only [canonicalAffineScale]
  unfold threeFlavorGapRatio threeFlavorSolarGap threeFlavorAtmosphericGap
  field_simp [A.atmosphericGapNonzero]
  ring_nf

theorem canonicalAffine_level2_eq_one
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {R : Type}
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) :
  canonicalAffineScale A * A.massSquaredLevelOf 2 +
      canonicalAffineShift A = 1 := by
  unfold canonicalAffineShift
  simp only [canonicalAffineScale]
  unfold threeFlavorAtmosphericGap
  calc
    (A.massSquaredLevelOf 2 - A.massSquaredLevelOf 0)⁻¹ *
          A.massSquaredLevelOf 2 +
        - (A.massSquaredLevelOf 2 - A.massSquaredLevelOf 0)⁻¹ *
          A.massSquaredLevelOf 0 =
        (A.massSquaredLevelOf 2 - A.massSquaredLevelOf 0) *
          (A.massSquaredLevelOf 2 - A.massSquaredLevelOf 0)⁻¹ := by
          ring
    _ = 1 := by
      exact mul_inv_cancel₀ A.atmosphericGapNonzero

/--
Every gap algebra with nonzero atmospheric gap has a canonical internal affine
normalization to `(0, rho, 1)`, where `rho` is the symbolic gap ratio.  This
does not yet make `rho` a new numeral; it proves that the affine-normalized
shape object is constructible from the standing gap algebra plus the audit
gates.
-/
noncomputable def canonicalAffineNormalizedGapShape
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (Q : ThreeFlavorCanonicalAffineNormalizationAudit A) :
  ThreeFlavorAffineNormalizedGapShape R A :=
  { normalizedRatio := threeFlavorGapRatio A.massSquaredLevelOf
    scale := canonicalAffineScale A
    shift := canonicalAffineShift A
    scale_ne_zero := canonicalAffineScale_ne_zero A
    affineLevel0_eq_zero := canonicalAffine_level0_eq_zero A
    affineLevel1_eq_ratio := canonicalAffine_level1_eq_ratio A
    affineLevel2_eq_one := canonicalAffine_level2_eq_one A
    internalShapeDeterminesRatio := Q.internalShapeDeterminesRatio
    internalShapeDeterminesRatio_proof :=
      Q.internalShapeDeterminesRatio_proof
    noOneAnchorImport := Q.noOneAnchorImport
    noOneAnchorImport_proof := Q.noOneAnchorImport_proof
    representativeBranchCollapsedModuloSkin :=
      Q.representativeBranchCollapsedModuloSkin
    representativeBranchCollapsedModuloSkin_proof :=
      Q.representativeBranchCollapsedModuloSkin_proof
    allUnresolvedFreedomsDischarged :=
      Q.allUnresolvedFreedomsDischarged
    allUnresolvedFreedomsDischarged_proof :=
      Q.allUnresolvedFreedomsDischarged_proof
    calibrationPrior := Q.calibrationPrior
    calibrationPrior_proof := Q.calibrationPrior_proof
    transportNeutralOrDischarged := Q.transportNeutralOrDischarged
    transportNeutralOrDischarged_proof :=
      Q.transportNeutralOrDischarged_proof
    scaleStatusFixed := Q.scaleStatusFixed
    scaleStatusFixed_proof := Q.scaleStatusFixed_proof
    noHiddenNumericalSelector := Q.noHiddenNumericalSelector
    noHiddenNumericalSelector_proof :=
      Q.noHiddenNumericalSelector_proof
    noEmpiricalFitImport := Q.noEmpiricalFitImport
    noEmpiricalFitImport_proof := Q.noEmpiricalFitImport_proof }

/--
Internal closed-constant identification for the normalized ratio.

This is the next post-affine-normalization target: AASC/MR3/operator
exhaustion may derive a closed internal constant and prove that the symbolic
gap quotient is that constant.  This does not import data; it is a pure
identification of the already-normalized ratio with a closed value in `R`.
-/
structure ThreeFlavorInternalClosedRatioConstant
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) where
  closedRatio : R
  closedRatio_eq_gapRatio :
    closedRatio = threeFlavorGapRatio A.massSquaredLevelOf
  closedConstantDerivedInternally : Prop
  closedConstantDerivedInternally_proof :
    closedConstantDerivedInternally
  noOneAnchorImport : Prop
  noOneAnchorImport_proof : noOneAnchorImport
  representativeBranchCollapsedModuloSkin : Prop
  representativeBranchCollapsedModuloSkin_proof :
    representativeBranchCollapsedModuloSkin
  allUnresolvedFreedomsDischarged : Prop
  allUnresolvedFreedomsDischarged_proof :
    allUnresolvedFreedomsDischarged
  calibrationPrior : Prop
  calibrationPrior_proof : calibrationPrior
  transportNeutralOrDischarged : Prop
  transportNeutralOrDischarged_proof :
    transportNeutralOrDischarged
  scaleStatusFixed : Prop
  scaleStatusFixed_proof : scaleStatusFixed
  noHiddenNumericalSelector : Prop
  noHiddenNumericalSelector_proof : noHiddenNumericalSelector
  noEmpiricalFitImport : Prop
  noEmpiricalFitImport_proof : noEmpiricalFitImport

def closedRatioConstantAsInternalAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (K : ThreeFlavorInternalClosedRatioConstant R A) :
  ThreeFlavorInternalGapShapeAnchor R A :=
  { canonicalRatio := K.closedRatio
    canonicalRatio_eq_gapRatio := K.closedRatio_eq_gapRatio
    internalShapeDeterminesRatio := K.closedConstantDerivedInternally
    internalShapeDeterminesRatio_proof :=
      K.closedConstantDerivedInternally_proof
    noOneAnchorImport := K.noOneAnchorImport
    noOneAnchorImport_proof := K.noOneAnchorImport_proof
    representativeBranchCollapsedModuloSkin :=
      K.representativeBranchCollapsedModuloSkin
    representativeBranchCollapsedModuloSkin_proof :=
      K.representativeBranchCollapsedModuloSkin_proof
    allUnresolvedFreedomsDischarged :=
      K.allUnresolvedFreedomsDischarged
    allUnresolvedFreedomsDischarged_proof :=
      K.allUnresolvedFreedomsDischarged_proof
    calibrationPrior := K.calibrationPrior
    calibrationPrior_proof := K.calibrationPrior_proof
    transportNeutralOrDischarged := K.transportNeutralOrDischarged
    transportNeutralOrDischarged_proof :=
      K.transportNeutralOrDischarged_proof
    scaleStatusFixed := K.scaleStatusFixed
    scaleStatusFixed_proof := K.scaleStatusFixed_proof
    noHiddenNumericalSelector := K.noHiddenNumericalSelector
    noHiddenNumericalSelector_proof :=
      K.noHiddenNumericalSelector_proof
    noEmpiricalFitImport := K.noEmpiricalFitImport
    noEmpiricalFitImport_proof := K.noEmpiricalFitImport_proof }

def internalGapShapeAnchorAsClosedRatioConstant
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorInternalGapShapeAnchor R A) :
  ThreeFlavorInternalClosedRatioConstant R A :=
  { closedRatio := S.canonicalRatio
    closedRatio_eq_gapRatio := S.canonicalRatio_eq_gapRatio
    closedConstantDerivedInternally := S.internalShapeDeterminesRatio
    closedConstantDerivedInternally_proof :=
      S.internalShapeDeterminesRatio_proof
    noOneAnchorImport := S.noOneAnchorImport
    noOneAnchorImport_proof := S.noOneAnchorImport_proof
    representativeBranchCollapsedModuloSkin :=
      S.representativeBranchCollapsedModuloSkin
    representativeBranchCollapsedModuloSkin_proof :=
      S.representativeBranchCollapsedModuloSkin_proof
    allUnresolvedFreedomsDischarged :=
      S.allUnresolvedFreedomsDischarged
    allUnresolvedFreedomsDischarged_proof :=
      S.allUnresolvedFreedomsDischarged_proof
    calibrationPrior := S.calibrationPrior
    calibrationPrior_proof := S.calibrationPrior_proof
    transportNeutralOrDischarged := S.transportNeutralOrDischarged
    transportNeutralOrDischarged_proof :=
      S.transportNeutralOrDischarged_proof
    scaleStatusFixed := S.scaleStatusFixed
    scaleStatusFixed_proof := S.scaleStatusFixed_proof
    noHiddenNumericalSelector := S.noHiddenNumericalSelector
    noHiddenNumericalSelector_proof := S.noHiddenNumericalSelector_proof
    noEmpiricalFitImport := S.noEmpiricalFitImport
    noEmpiricalFitImport_proof := S.noEmpiricalFitImport_proof }

noncomputable def canonicalAffineNormalizationAsClosedRatioConstant
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (Q : ThreeFlavorCanonicalAffineNormalizationAudit A) :
  ThreeFlavorInternalClosedRatioConstant R A :=
  internalGapShapeAnchorAsClosedRatioConstant
    R
    A
    (affineNormalizedGapShapeAsInternalAnchor
      R
      A
      (canonicalAffineNormalizedGapShape R A Q))

/--
Polynomial unique-root route to a closed ratio constant.

The polynomial is an internal law on the normalized ratio.  If the symbolic
gap ratio is an admissible root, and the closed constant is the unique
admissible root of the same law, then the symbolic quotient equals the closed
constant.  This is the precise Lean socket for a non-empirical polynomial
readout.
-/
structure ThreeFlavorInternalPolynomialRatioAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) where
  polynomial : Polynomial R
  closedRatio : R
  AdmissibleRoot : R -> Prop
  gapRatio_is_root :
    polynomial.eval (threeFlavorGapRatio A.massSquaredLevelOf) = 0
  gapRatio_admissible :
    AdmissibleRoot (threeFlavorGapRatio A.massSquaredLevelOf)
  closedRatio_is_root : polynomial.eval closedRatio = 0
  closedRatio_admissible : AdmissibleRoot closedRatio
  uniqueAdmissibleRoot :
    ∀ x : R, polynomial.eval x = 0 -> AdmissibleRoot x -> x = closedRatio
  polynomialLawDerivedInternally : Prop
  polynomialLawDerivedInternally_proof :
    polynomialLawDerivedInternally
  noOneAnchorImport : Prop
  noOneAnchorImport_proof : noOneAnchorImport
  representativeBranchCollapsedModuloSkin : Prop
  representativeBranchCollapsedModuloSkin_proof :
    representativeBranchCollapsedModuloSkin
  allUnresolvedFreedomsDischarged : Prop
  allUnresolvedFreedomsDischarged_proof :
    allUnresolvedFreedomsDischarged
  calibrationPrior : Prop
  calibrationPrior_proof : calibrationPrior
  transportNeutralOrDischarged : Prop
  transportNeutralOrDischarged_proof :
    transportNeutralOrDischarged
  scaleStatusFixed : Prop
  scaleStatusFixed_proof : scaleStatusFixed
  noHiddenNumericalSelector : Prop
  noHiddenNumericalSelector_proof : noHiddenNumericalSelector
  noEmpiricalFitImport : Prop
  noEmpiricalFitImport_proof : noEmpiricalFitImport

/--
AASC uniqueness adapter for polynomial readout roots.

This is the local socket for the corpus uniqueness machinery.  It packages the
claim that, under the admitted root predicate for the current target, the
polynomial law has exactly one admissible root.  The witness root is the closed
ratio reported by the construction.
-/
structure AASCAdmissiblePolynomialRootUniquenessCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (_A : ThreeFlavorGapRatioAlgebra M R) where
  polynomial : Polynomial R
  closedRatio : R
  AdmissibleRoot : R -> Prop
  closedRatio_is_root : polynomial.eval closedRatio = 0
  closedRatio_admissible : AdmissibleRoot closedRatio
  uniqueAdmissibleRoot :
    ∀ x : R, polynomial.eval x = 0 -> AdmissibleRoot x -> x = closedRatio
  uniquenessFromAASC : Prop
  uniquenessFromAASC_proof : uniquenessFromAASC
  sameScopeRootPredicate : Prop
  sameScopeRootPredicate_proof : sameScopeRootPredicate
  noExtraRootSelector : Prop
  noExtraRootSelector_proof : noExtraRootSelector

/--
AASC unique-interior root-occupancy ledger.

This is a more native way to obtain the admissible-root uniqueness certificate:
roots are not compared by an ad hoc selector.  Instead, every admissible root
of the internal polynomial must occupy the unique admissible interior, whose
root representative is the closed ratio.
-/
structure AASCPolynomialRootUniqueInteriorLedger
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (_A : ThreeFlavorGapRatioAlgebra M R) where
  polynomial : Polynomial R
  closedRatio : R
  AdmissibleRoot : R -> Prop
  RootInterior : Type
  rootOfInterior : RootInterior -> R
  currentInterior : RootInterior
  currentInterior_root_eq_closed :
    rootOfInterior currentInterior = closedRatio
  closedRatio_is_root : polynomial.eval closedRatio = 0
  closedRatio_admissible : AdmissibleRoot closedRatio
  admissibleRootOccupiesInterior :
    ∀ x : R, polynomial.eval x = 0 -> AdmissibleRoot x ->
      ∃ I : RootInterior, rootOfInterior I = x
  uniqueAdmissibleInterior :
    ∀ I : RootInterior, rootOfInterior I = rootOfInterior currentInterior
  uniquenessFromAASC : Prop
  uniquenessFromAASC_proof : uniquenessFromAASC
  sameScopeRootPredicate : Prop
  sameScopeRootPredicate_proof : sameScopeRootPredicate
  noExtraRootSelector : Prop
  noExtraRootSelector_proof : noExtraRootSelector

theorem rootUniqueInteriorLedger_uniqueAdmissibleRoot
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {R : Type}
  [Field R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  (L : AASCPolynomialRootUniqueInteriorLedger R A) :
  ∀ x : R, L.polynomial.eval x = 0 -> L.AdmissibleRoot x ->
    x = L.closedRatio := by
  intro x hx hAdm
  rcases L.admissibleRootOccupiesInterior x hx hAdm with ⟨I, hI⟩
  calc
    x = L.rootOfInterior I := hI.symm
    _ = L.rootOfInterior L.currentInterior :=
      L.uniqueAdmissibleInterior I
    _ = L.closedRatio := L.currentInterior_root_eq_closed

def rootUniqueInteriorLedgerAsUniquenessCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (L : AASCPolynomialRootUniqueInteriorLedger R A) :
  AASCAdmissiblePolynomialRootUniquenessCertificate R A :=
  { polynomial := L.polynomial
    closedRatio := L.closedRatio
    AdmissibleRoot := L.AdmissibleRoot
    closedRatio_is_root := L.closedRatio_is_root
    closedRatio_admissible := L.closedRatio_admissible
    uniqueAdmissibleRoot :=
      rootUniqueInteriorLedger_uniqueAdmissibleRoot L
    uniquenessFromAASC := L.uniquenessFromAASC
    uniquenessFromAASC_proof := L.uniquenessFromAASC_proof
    sameScopeRootPredicate := L.sameScopeRootPredicate
    sameScopeRootPredicate_proof := L.sameScopeRootPredicate_proof
    noExtraRootSelector := L.noExtraRootSelector
    noExtraRootSelector_proof := L.noExtraRootSelector_proof }

/--
Branch-singleton realization of polynomial-root uniqueness.

This adapter connects the NNR8/UEAP branch singleton directly to root
uniqueness: every admissible polynomial root must be realized by a
hybrid-joint ratio, and the readout of that ratio is the root.  Since the
hybrid joint restriction is singleton, every such realized ratio is the current
standing ratio, hence every admissible root equals the current closed ratio.
-/
structure AASCPolynomialRootHybridSingletonRealization
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M)
  (R : Type)
  [Field R]
  (_A : ThreeFlavorGapRatioAlgebra M R) where
  polynomial : Polynomial R
  closedRatio : R
  AdmissibleRoot : R -> Prop
  valueOfRatio : C.Ratio -> R
  currentValue_eq_closed : valueOfRatio C.ratio = closedRatio
  closedRatio_is_root : polynomial.eval closedRatio = 0
  closedRatio_admissible : AdmissibleRoot closedRatio
  rootRatioOf :
    ∀ x : R, polynomial.eval x = 0 -> AdmissibleRoot x -> C.Ratio
  rootRatio_value :
    ∀ x hx hAdm, valueOfRatio (rootRatioOf x hx hAdm) = x
  rootRatio_minimal :
    ∀ x hx hAdm, C.inMinimalInterval (rootRatioOf x hx hAdm)
  rootRatio_modular :
    ∀ x hx hAdm, H.modular.ModularRestriction (rootRatioOf x hx hAdm)
  rootRatio_spectral :
    ∀ x hx hAdm, H.spectral.spectralRestriction (rootRatioOf x hx hAdm)
  rootRatio_scoto :
    ∀ x hx hAdm, H.scoto.scotoRestriction (rootRatioOf x hx hAdm)
  uniquenessFromAASC : Prop
  uniquenessFromAASC_proof : uniquenessFromAASC
  sameScopeRootPredicate : Prop
  sameScopeRootPredicate_proof : sameScopeRootPredicate
  noExtraRootSelector : Prop
  noExtraRootSelector_proof : noExtraRootSelector

/--
Root-realization construction target.

This is the next thing a construction paper must prove: every admissible root
of the internal polynomial can be lifted to a same-scope hybrid-joint ratio
whose readout is exactly that root.  The object separates this realization
data from the branch-singleton theorem that later collapses all such lifts to
the current ratio.
-/
structure AASCPolynomialRootRealizationTheorem
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M)
  (R : Type)
  [Field R]
  (_A : ThreeFlavorGapRatioAlgebra M R) where
  polynomial : Polynomial R
  closedRatio : R
  AdmissibleRoot : R -> Prop
  valueOfRatio : C.Ratio -> R
  currentValue_eq_closed : valueOfRatio C.ratio = closedRatio
  closedRatio_is_root : polynomial.eval closedRatio = 0
  closedRatio_admissible : AdmissibleRoot closedRatio
  liftRootToRatio :
    ∀ x : R, polynomial.eval x = 0 -> AdmissibleRoot x -> C.Ratio
  liftedRootReadsBack :
    ∀ x hx hAdm, valueOfRatio (liftRootToRatio x hx hAdm) = x
  liftedRootInMinimalInterval :
    ∀ x hx hAdm, C.inMinimalInterval (liftRootToRatio x hx hAdm)
  liftedRootModular :
    ∀ x hx hAdm, H.modular.ModularRestriction (liftRootToRatio x hx hAdm)
  liftedRootSpectral :
    ∀ x hx hAdm, H.spectral.spectralRestriction (liftRootToRatio x hx hAdm)
  liftedRootScoto :
    ∀ x hx hAdm, H.scoto.scotoRestriction (liftRootToRatio x hx hAdm)
  rootRealizationSameScope : Prop
  rootRealizationSameScope_proof : rootRealizationSameScope
  rootRealizationExhaustive : Prop
  rootRealizationExhaustive_proof : rootRealizationExhaustive
  rootReadbackLawful : Prop
  rootReadbackLawful_proof : rootReadbackLawful
  noEmpiricalRootImport : Prop
  noEmpiricalRootImport_proof : noEmpiricalRootImport
  noExtraRootSelector : Prop
  noExtraRootSelector_proof : noExtraRootSelector

/--
Existential same-scope root predicate theorem.

This is easier for a paper to prove than an explicit lift function: every
admissible root is shown to have some same-scope hybrid-joint ratio
realization whose readout is the root.  Lean then chooses that realization to
build `AASCPolynomialRootRealizationTheorem`.
-/
structure AASCSameScopePolynomialRootPredicateTheorem
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M)
  (R : Type)
  [Field R]
  (_A : ThreeFlavorGapRatioAlgebra M R) where
  polynomial : Polynomial R
  closedRatio : R
  AdmissibleRoot : R -> Prop
  valueOfRatio : C.Ratio -> R
  currentValue_eq_closed : valueOfRatio C.ratio = closedRatio
  closedRatio_is_root : polynomial.eval closedRatio = 0
  closedRatio_admissible : AdmissibleRoot closedRatio
  admissibleRootHasSameScopeRealization :
    ∀ x : R, polynomial.eval x = 0 -> AdmissibleRoot x ->
      ∃ r : C.Ratio,
        C.inMinimalInterval r /\
          H.modular.ModularRestriction r /\
            H.spectral.spectralRestriction r /\
              H.scoto.scotoRestriction r /\
                valueOfRatio r = x
  rootRealizationSameScope : Prop
  rootRealizationSameScope_proof : rootRealizationSameScope
  rootRealizationExhaustive : Prop
  rootRealizationExhaustive_proof : rootRealizationExhaustive
  rootReadbackLawful : Prop
  rootReadbackLawful_proof : rootReadbackLawful
  noEmpiricalRootImport : Prop
  noEmpiricalRootImport_proof : noEmpiricalRootImport
  noExtraRootSelector : Prop
  noExtraRootSelector_proof : noExtraRootSelector

/--
Canonical same-scope admissible-root predicate.

For a proposed root value `x`, admissibility means exactly that `x` is read
from some ratio point in the hybrid joint restriction.  This turns root
admissibility into same-scope realizability rather than a free numerical
predicate.
-/
def SameScopeHybridRootRealized
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M)
  (R : Type)
  [Field R]
  (valueOfRatio : C.Ratio -> R)
  (x : R) : Prop :=
  exists r : C.Ratio,
    C.inMinimalInterval r /\
      H.modular.ModularRestriction r /\
        H.spectral.spectralRestriction r /\
          H.scoto.scotoRestriction r /\
            valueOfRatio r = x

/--
If the admissible-root predicate is definitionally the same-scope realization
predicate, root realization is automatic.
-/
structure AASCSameScopeRootPredicateDefinition
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M)
  (R : Type)
  [Field R]
  (_A : ThreeFlavorGapRatioAlgebra M R) where
  polynomial : Polynomial R
  closedRatio : R
  valueOfRatio : C.Ratio -> R
  currentValue_eq_closed : valueOfRatio C.ratio = closedRatio
  currentRatioInMinimalInterval : C.inMinimalInterval C.ratio
  currentRatioModular : H.modular.ModularRestriction C.ratio
  currentRatioSpectral : H.spectral.spectralRestriction C.ratio
  currentRatioScoto : H.scoto.scotoRestriction C.ratio
  closedRatio_is_root : polynomial.eval closedRatio = 0
  rootRealizationSameScope : Prop
  rootRealizationSameScope_proof : rootRealizationSameScope
  rootRealizationExhaustive : Prop
  rootRealizationExhaustive_proof : rootRealizationExhaustive
  rootReadbackLawful : Prop
  rootReadbackLawful_proof : rootReadbackLawful
  noEmpiricalRootImport : Prop
  noEmpiricalRootImport_proof : noEmpiricalRootImport
  noExtraRootSelector : Prop
  noExtraRootSelector_proof : noExtraRootSelector

def sameScopeRootPredicateDefinitionAsPredicateTheorem
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (D : AASCSameScopeRootPredicateDefinition H R A) :
  AASCSameScopePolynomialRootPredicateTheorem H R A :=
  { polynomial := D.polynomial
    closedRatio := D.closedRatio
    AdmissibleRoot :=
      SameScopeHybridRootRealized H R D.valueOfRatio
    valueOfRatio := D.valueOfRatio
    currentValue_eq_closed := D.currentValue_eq_closed
    closedRatio_is_root := D.closedRatio_is_root
    closedRatio_admissible := by
      exact
        ⟨C.ratio,
          D.currentRatioInMinimalInterval,
          D.currentRatioModular,
          D.currentRatioSpectral,
          D.currentRatioScoto,
          D.currentValue_eq_closed⟩
    admissibleRootHasSameScopeRealization := by
      intro x _hx hAdm
      exact hAdm
    rootRealizationSameScope := D.rootRealizationSameScope
    rootRealizationSameScope_proof := D.rootRealizationSameScope_proof
    rootRealizationExhaustive := D.rootRealizationExhaustive
    rootRealizationExhaustive_proof := D.rootRealizationExhaustive_proof
    rootReadbackLawful := D.rootReadbackLawful
    rootReadbackLawful_proof := D.rootReadbackLawful_proof
    noEmpiricalRootImport := D.noEmpiricalRootImport
    noEmpiricalRootImport_proof := D.noEmpiricalRootImport_proof
    noExtraRootSelector := D.noExtraRootSelector
    noExtraRootSelector_proof := D.noExtraRootSelector_proof }

noncomputable def sameScopeRootPredicateAsRootRealizationTheorem
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (T : AASCSameScopePolynomialRootPredicateTheorem H R A) :
  AASCPolynomialRootRealizationTheorem H R A :=
  { polynomial := T.polynomial
    closedRatio := T.closedRatio
    AdmissibleRoot := T.AdmissibleRoot
    valueOfRatio := T.valueOfRatio
    currentValue_eq_closed := T.currentValue_eq_closed
    closedRatio_is_root := T.closedRatio_is_root
    closedRatio_admissible := T.closedRatio_admissible
    liftRootToRatio := fun x hx hAdm =>
      Classical.choose
        (T.admissibleRootHasSameScopeRealization x hx hAdm)
    liftedRootReadsBack := by
      intro x hx hAdm
      exact
        ((((Classical.choose_spec
          (T.admissibleRootHasSameScopeRealization x hx hAdm)).2).2).2).2
    liftedRootInMinimalInterval := by
      intro x hx hAdm
      exact
        (Classical.choose_spec
          (T.admissibleRootHasSameScopeRealization x hx hAdm)).1
    liftedRootModular := by
      intro x hx hAdm
      exact
        ((Classical.choose_spec
          (T.admissibleRootHasSameScopeRealization x hx hAdm)).2).1
    liftedRootSpectral := by
      intro x hx hAdm
      exact
        (((Classical.choose_spec
          (T.admissibleRootHasSameScopeRealization x hx hAdm)).2).2).1
    liftedRootScoto := by
      intro x hx hAdm
      exact
        ((((Classical.choose_spec
          (T.admissibleRootHasSameScopeRealization x hx hAdm)).2).2).2).1
    rootRealizationSameScope := T.rootRealizationSameScope
    rootRealizationSameScope_proof := T.rootRealizationSameScope_proof
    rootRealizationExhaustive := T.rootRealizationExhaustive
    rootRealizationExhaustive_proof := T.rootRealizationExhaustive_proof
    rootReadbackLawful := T.rootReadbackLawful
    rootReadbackLawful_proof := T.rootReadbackLawful_proof
    noEmpiricalRootImport := T.noEmpiricalRootImport
    noEmpiricalRootImport_proof := T.noEmpiricalRootImport_proof
    noExtraRootSelector := T.noExtraRootSelector
    noExtraRootSelector_proof := T.noExtraRootSelector_proof }

def polynomialRootRealizationAsHybridSingletonRealization
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (T : AASCPolynomialRootRealizationTheorem H R A) :
  AASCPolynomialRootHybridSingletonRealization H R A :=
  { polynomial := T.polynomial
    closedRatio := T.closedRatio
    AdmissibleRoot := T.AdmissibleRoot
    valueOfRatio := T.valueOfRatio
    currentValue_eq_closed := T.currentValue_eq_closed
    closedRatio_is_root := T.closedRatio_is_root
    closedRatio_admissible := T.closedRatio_admissible
    rootRatioOf := T.liftRootToRatio
    rootRatio_value := T.liftedRootReadsBack
    rootRatio_minimal := T.liftedRootInMinimalInterval
    rootRatio_modular := T.liftedRootModular
    rootRatio_spectral := T.liftedRootSpectral
    rootRatio_scoto := T.liftedRootScoto
    uniquenessFromAASC :=
      T.rootRealizationSameScope /\ T.rootRealizationExhaustive
    uniquenessFromAASC_proof :=
      ⟨T.rootRealizationSameScope_proof,
        T.rootRealizationExhaustive_proof⟩
    sameScopeRootPredicate := T.rootReadbackLawful
    sameScopeRootPredicate_proof := T.rootReadbackLawful_proof
    noExtraRootSelector :=
      T.noExtraRootSelector /\ T.noEmpiricalRootImport
    noExtraRootSelector_proof :=
      ⟨T.noExtraRootSelector_proof, T.noEmpiricalRootImport_proof⟩ }

theorem rootHybridSingletonRealization_uniqueAdmissibleRoot
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  (B : AASCPolynomialRootHybridSingletonRealization H R A)
  (hsingle : HybridJointRestrictionSingleton H) :
  ∀ x : R, B.polynomial.eval x = 0 -> B.AdmissibleRoot x ->
    x = B.closedRatio := by
  intro x hx hAdm
  let r := B.rootRatioOf x hx hAdm
  have hr : r = C.ratio :=
    hsingle
      r
      (B.rootRatio_minimal x hx hAdm)
      (B.rootRatio_modular x hx hAdm)
      (B.rootRatio_spectral x hx hAdm)
      (B.rootRatio_scoto x hx hAdm)
  calc
    x = B.valueOfRatio r := (B.rootRatio_value x hx hAdm).symm
    _ = B.valueOfRatio C.ratio := by rw [hr]
    _ = B.closedRatio := B.currentValue_eq_closed

def rootHybridSingletonRealizationAsUniquenessCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (B : AASCPolynomialRootHybridSingletonRealization H R A)
  (hsingle : HybridJointRestrictionSingleton H) :
  AASCAdmissiblePolynomialRootUniquenessCertificate R A :=
  { polynomial := B.polynomial
    closedRatio := B.closedRatio
    AdmissibleRoot := B.AdmissibleRoot
    closedRatio_is_root := B.closedRatio_is_root
    closedRatio_admissible := B.closedRatio_admissible
    uniqueAdmissibleRoot :=
      rootHybridSingletonRealization_uniqueAdmissibleRoot B hsingle
    uniquenessFromAASC := B.uniquenessFromAASC
    uniquenessFromAASC_proof := B.uniquenessFromAASC_proof
    sameScopeRootPredicate := B.sameScopeRootPredicate
    sameScopeRootPredicate_proof := B.sameScopeRootPredicate_proof
    noExtraRootSelector := B.noExtraRootSelector
    noExtraRootSelector_proof := B.noExtraRootSelector_proof }

/--
Internal polynomial law for the current gap ratio, separated from the
uniqueness proof.  This lets AASC supply uniqueness independently through
`AASCAdmissiblePolynomialRootUniquenessCertificate`.
-/
structure ThreeFlavorInternalPolynomialRatioLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (U : AASCAdmissiblePolynomialRootUniquenessCertificate R A) where
  gapRatio_is_root :
    U.polynomial.eval (threeFlavorGapRatio A.massSquaredLevelOf) = 0
  gapRatio_admissible :
    U.AdmissibleRoot (threeFlavorGapRatio A.massSquaredLevelOf)
  polynomialLawDerivedInternally : Prop
  polynomialLawDerivedInternally_proof :
    polynomialLawDerivedInternally
  noOneAnchorImport : Prop
  noOneAnchorImport_proof : noOneAnchorImport
  representativeBranchCollapsedModuloSkin : Prop
  representativeBranchCollapsedModuloSkin_proof :
    representativeBranchCollapsedModuloSkin
  allUnresolvedFreedomsDischarged : Prop
  allUnresolvedFreedomsDischarged_proof :
    allUnresolvedFreedomsDischarged
  calibrationPrior : Prop
  calibrationPrior_proof : calibrationPrior
  transportNeutralOrDischarged : Prop
  transportNeutralOrDischarged_proof :
    transportNeutralOrDischarged
  scaleStatusFixed : Prop
  scaleStatusFixed_proof : scaleStatusFixed
  noEmpiricalFitImport : Prop
  noEmpiricalFitImport_proof : noEmpiricalFitImport

def polynomialLawAndAASCUniquenessAsPolynomialAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (U : AASCAdmissiblePolynomialRootUniquenessCertificate R A)
  (L : ThreeFlavorInternalPolynomialRatioLaw R A U) :
  ThreeFlavorInternalPolynomialRatioAnchor R A :=
  { polynomial := U.polynomial
    closedRatio := U.closedRatio
    AdmissibleRoot := U.AdmissibleRoot
    gapRatio_is_root := L.gapRatio_is_root
    gapRatio_admissible := L.gapRatio_admissible
    closedRatio_is_root := U.closedRatio_is_root
    closedRatio_admissible := U.closedRatio_admissible
    uniqueAdmissibleRoot := U.uniqueAdmissibleRoot
    polynomialLawDerivedInternally :=
      L.polynomialLawDerivedInternally /\
        U.uniquenessFromAASC /\
          U.sameScopeRootPredicate /\
            U.noExtraRootSelector
    polynomialLawDerivedInternally_proof :=
      ⟨L.polynomialLawDerivedInternally_proof,
        U.uniquenessFromAASC_proof,
        U.sameScopeRootPredicate_proof,
        U.noExtraRootSelector_proof⟩
    noOneAnchorImport := L.noOneAnchorImport
    noOneAnchorImport_proof := L.noOneAnchorImport_proof
    representativeBranchCollapsedModuloSkin :=
      L.representativeBranchCollapsedModuloSkin
    representativeBranchCollapsedModuloSkin_proof :=
      L.representativeBranchCollapsedModuloSkin_proof
    allUnresolvedFreedomsDischarged :=
      L.allUnresolvedFreedomsDischarged
    allUnresolvedFreedomsDischarged_proof :=
      L.allUnresolvedFreedomsDischarged_proof
    calibrationPrior := L.calibrationPrior
    calibrationPrior_proof := L.calibrationPrior_proof
    transportNeutralOrDischarged := L.transportNeutralOrDischarged
    transportNeutralOrDischarged_proof :=
      L.transportNeutralOrDischarged_proof
    scaleStatusFixed := L.scaleStatusFixed
    scaleStatusFixed_proof := L.scaleStatusFixed_proof
    noHiddenNumericalSelector := U.noExtraRootSelector
    noHiddenNumericalSelector_proof := U.noExtraRootSelector_proof
    noEmpiricalFitImport := L.noEmpiricalFitImport
    noEmpiricalFitImport_proof := L.noEmpiricalFitImport_proof }

theorem polynomialRatioAnchor_closedRatio_eq_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {R : Type}
  [Field R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  (P : ThreeFlavorInternalPolynomialRatioAnchor R A) :
  P.closedRatio = threeFlavorGapRatio A.massSquaredLevelOf := by
  exact
    (P.uniqueAdmissibleRoot
      (threeFlavorGapRatio A.massSquaredLevelOf)
      P.gapRatio_is_root
      P.gapRatio_admissible).symm

def polynomialRatioAnchorAsClosedConstant
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (P : ThreeFlavorInternalPolynomialRatioAnchor R A) :
  ThreeFlavorInternalClosedRatioConstant R A :=
  { closedRatio := P.closedRatio
    closedRatio_eq_gapRatio :=
      polynomialRatioAnchor_closedRatio_eq_gapRatio P
    closedConstantDerivedInternally := P.polynomialLawDerivedInternally
    closedConstantDerivedInternally_proof :=
      P.polynomialLawDerivedInternally_proof
    noOneAnchorImport := P.noOneAnchorImport
    noOneAnchorImport_proof := P.noOneAnchorImport_proof
    representativeBranchCollapsedModuloSkin :=
      P.representativeBranchCollapsedModuloSkin
    representativeBranchCollapsedModuloSkin_proof :=
      P.representativeBranchCollapsedModuloSkin_proof
    allUnresolvedFreedomsDischarged :=
      P.allUnresolvedFreedomsDischarged
    allUnresolvedFreedomsDischarged_proof :=
      P.allUnresolvedFreedomsDischarged_proof
    calibrationPrior := P.calibrationPrior
    calibrationPrior_proof := P.calibrationPrior_proof
    transportNeutralOrDischarged := P.transportNeutralOrDischarged
    transportNeutralOrDischarged_proof :=
      P.transportNeutralOrDischarged_proof
    scaleStatusFixed := P.scaleStatusFixed
    scaleStatusFixed_proof := P.scaleStatusFixed_proof
    noHiddenNumericalSelector := P.noHiddenNumericalSelector
    noHiddenNumericalSelector_proof :=
      P.noHiddenNumericalSelector_proof
    noEmpiricalFitImport := P.noEmpiricalFitImport
    noEmpiricalFitImport_proof := P.noEmpiricalFitImport_proof }

/--
Exact numerical readout for the gap-ratio expression.

This is the narrow object needed to upgrade the current endpoint from a closed
symbolic expression to an exact value.  It is intentionally stronger than the
gap-ratio algebra: a symbolic quotient is not automatically a number.  The
bundle must supply the value domain, the numerical map, and the full exactness
audit.
-/
structure ThreeFlavorGapRatioNumericalValueMap
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (_A : ThreeFlavorGapRatioAlgebra M R) where
  Value : Type
  valueOfExpression : R -> Value
  rawValueUniverseAvailable : Prop
  rawValueUniverseAvailable_proof : rawValueUniverseAvailable
  exactValueMapAvailable : Prop
  exactValueMapAvailable_proof : exactValueMapAvailable
  representativeBranchCollapsedModuloSkin : Prop
  representativeBranchCollapsedModuloSkin_proof :
    representativeBranchCollapsedModuloSkin
  allUnresolvedFreedomsDischarged : Prop
  allUnresolvedFreedomsDischarged_proof :
    allUnresolvedFreedomsDischarged
  calibrationPrior : Prop
  calibrationPrior_proof : calibrationPrior
  transportNeutralOrDischarged : Prop
  transportNeutralOrDischarged_proof :
    transportNeutralOrDischarged
  scaleStatusFixed : Prop
  scaleStatusFixed_proof : scaleStatusFixed
  noHiddenNumericalSelector : Prop
  noHiddenNumericalSelector_proof : noHiddenNumericalSelector
  noEmpiricalFitImport : Prop
  noEmpiricalFitImport_proof : noEmpiricalFitImport

/--
An internal shape anchor supplies the exact-value map demanded by the NNR9
exact readout interface.  The value type is the same coefficient field `R`;
the only admissible value is the internally anchored canonical ratio.
-/
def internalGapShapeAnchorAsNumericalValueMap
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorInternalGapShapeAnchor R A) :
  ThreeFlavorGapRatioNumericalValueMap R A :=
  { Value := R
    valueOfExpression := fun _ => S.canonicalRatio
    rawValueUniverseAvailable := S.internalShapeDeterminesRatio
    rawValueUniverseAvailable_proof :=
      S.internalShapeDeterminesRatio_proof
    exactValueMapAvailable := S.internalShapeDeterminesRatio
    exactValueMapAvailable_proof :=
      S.internalShapeDeterminesRatio_proof
    representativeBranchCollapsedModuloSkin :=
      S.representativeBranchCollapsedModuloSkin
    representativeBranchCollapsedModuloSkin_proof :=
      S.representativeBranchCollapsedModuloSkin_proof
    allUnresolvedFreedomsDischarged :=
      S.allUnresolvedFreedomsDischarged
    allUnresolvedFreedomsDischarged_proof :=
      S.allUnresolvedFreedomsDischarged_proof
    calibrationPrior := S.calibrationPrior
    calibrationPrior_proof := S.calibrationPrior_proof
    transportNeutralOrDischarged := S.transportNeutralOrDischarged
    transportNeutralOrDischarged_proof :=
      S.transportNeutralOrDischarged_proof
    scaleStatusFixed := S.scaleStatusFixed
    scaleStatusFixed_proof := S.scaleStatusFixed_proof
    noHiddenNumericalSelector := S.noHiddenNumericalSelector
    noHiddenNumericalSelector_proof :=
      S.noHiddenNumericalSelector_proof
    noEmpiricalFitImport := S.noEmpiricalFitImport /\ S.noOneAnchorImport
    noEmpiricalFitImport_proof :=
      ⟨S.noEmpiricalFitImport_proof, S.noOneAnchorImport_proof⟩ }

def gapRatioNumericalValueMapRequirements
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  (V : ThreeFlavorGapRatioNumericalValueMap R A) :
  AASCExactValueReadoutRequirements C :=
  { rawValueUniverseAvailable := V.rawValueUniverseAvailable
    exactValueMapAvailable := V.exactValueMapAvailable
    representativeBranchCollapsedModuloSkin :=
      V.representativeBranchCollapsedModuloSkin
    allUnresolvedFreedomsDischarged :=
      V.allUnresolvedFreedomsDischarged
    calibrationPrior := V.calibrationPrior
    transportNeutralOrDischarged := V.transportNeutralOrDischarged
    scaleStatusFixed := V.scaleStatusFixed
    noHiddenNumericalSelector := V.noHiddenNumericalSelector
    noEmpiricalFitImport := V.noEmpiricalFitImport }

theorem gapRatioNumericalValueMapRequirementsPass
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  (V : ThreeFlavorGapRatioNumericalValueMap R A) :
  ExactValueReadoutRequirementsPass
    (gapRatioNumericalValueMapRequirements R V) := by
  exact
    ⟨V.rawValueUniverseAvailable_proof,
      V.exactValueMapAvailable_proof,
      V.representativeBranchCollapsedModuloSkin_proof,
      V.allUnresolvedFreedomsDischarged_proof,
      V.calibrationPrior_proof,
      V.transportNeutralOrDischarged_proof,
      V.scaleStatusFixed_proof,
      V.noHiddenNumericalSelector_proof,
      V.noEmpiricalFitImport_proof⟩

noncomputable def gapRatioNumericalValueMapAsExactConstruction
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (V : ThreeFlavorGapRatioNumericalValueMap R A) :
  AASCExactValueReadoutConstruction C :=
  { requirements := gapRatioNumericalValueMapRequirements R V
    requirementsPass := gapRatioNumericalValueMapRequirementsPass R V
    Value := V.Value
    valueOf := fun _ =>
      V.valueOfExpression (threeFlavorGapRatio A.massSquaredLevelOf) }

noncomputable def gapRatioNumericalValueMapAsExactSource
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (V : ThreeFlavorGapRatioNumericalValueMap R A) :
  AASCExactRatioValueSourceTheorem C :=
  exactValueConstructionAsSourceTheorem
    C
    (gapRatioNumericalValueMapAsExactConstruction R A V)

theorem gapRatioNumericalValueMapGivesExactValueEvaluator
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (V : ThreeFlavorGapRatioNumericalValueMap R A) :
  HasCurrentRatioEvaluatorAtStrength C .exactValue :=
  exactValueSourceGivesExactValueStrengthEvaluator
    C
    (gapRatioNumericalValueMapAsExactSource R A V)

noncomputable def gapRatioNumericalValueMapAndSingletonGiveCurrentExactEvaluation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (V : ThreeFlavorGapRatioNumericalValueMap R A)
  (hsingle : HybridJointRestrictionSingleton H) :
  CurrentStandingRatioEvaluation C :=
  singletonWithExactValueSourceGivesCurrentEvaluation
    hsingle
    (gapRatioNumericalValueMapAsExactSource R A V)

def gapRatioNumericalValueMapGivesExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (V : ThreeFlavorGapRatioNumericalValueMap R A) :
  AASCNNR9ExactValueFrontier C :=
  exactValueConstructionGivesExactValueFrontier
    C
    (gapRatioNumericalValueMapAsExactConstruction R A V)

theorem internalGapShapeAnchorGivesExactValueEvaluator
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorInternalGapShapeAnchor R A) :
  HasCurrentRatioEvaluatorAtStrength C .exactValue :=
  gapRatioNumericalValueMapGivesExactValueEvaluator
    R
    A
    (internalGapShapeAnchorAsNumericalValueMap R A S)

noncomputable def internalGapShapeAnchorAndSingletonGiveCurrentExactEvaluation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorInternalGapShapeAnchor R A)
  (hsingle : HybridJointRestrictionSingleton H) :
  CurrentStandingRatioEvaluation C :=
  gapRatioNumericalValueMapAndSingletonGiveCurrentExactEvaluation
    R
    A
    (internalGapShapeAnchorAsNumericalValueMap R A S)
    hsingle

def internalGapShapeAnchorGivesExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorInternalGapShapeAnchor R A) :
  AASCNNR9ExactValueFrontier C :=
  gapRatioNumericalValueMapGivesExactValueFrontier
    R
    A
    (internalGapShapeAnchorAsNumericalValueMap R A S)

theorem normalizedGapShapeGivesExactValueEvaluator
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorNormalizedGapShape R A) :
  HasCurrentRatioEvaluatorAtStrength C .exactValue :=
  internalGapShapeAnchorGivesExactValueEvaluator
    R
    A
    (normalizedGapShapeAsInternalAnchor R A S)

noncomputable def normalizedGapShapeAndSingletonGiveCurrentExactEvaluation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorNormalizedGapShape R A)
  (hsingle : HybridJointRestrictionSingleton H) :
  CurrentStandingRatioEvaluation C :=
  internalGapShapeAnchorAndSingletonGiveCurrentExactEvaluation
    R
    A
    (normalizedGapShapeAsInternalAnchor R A S)
    hsingle

def normalizedGapShapeGivesExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorNormalizedGapShape R A) :
  AASCNNR9ExactValueFrontier C :=
  internalGapShapeAnchorGivesExactValueFrontier
    R
    A
    (normalizedGapShapeAsInternalAnchor R A S)

theorem affineNormalizedGapShapeGivesExactValueEvaluator
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorAffineNormalizedGapShape R A) :
  HasCurrentRatioEvaluatorAtStrength C .exactValue :=
  internalGapShapeAnchorGivesExactValueEvaluator
    R
    A
    (affineNormalizedGapShapeAsInternalAnchor R A S)

noncomputable def affineNormalizedGapShapeAndSingletonGiveCurrentExactEvaluation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorAffineNormalizedGapShape R A)
  (hsingle : HybridJointRestrictionSingleton H) :
  CurrentStandingRatioEvaluation C :=
  internalGapShapeAnchorAndSingletonGiveCurrentExactEvaluation
    R
    A
    (affineNormalizedGapShapeAsInternalAnchor R A S)
    hsingle

def affineNormalizedGapShapeGivesExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorAffineNormalizedGapShape R A) :
  AASCNNR9ExactValueFrontier C :=
  internalGapShapeAnchorGivesExactValueFrontier
    R
    A
    (affineNormalizedGapShapeAsInternalAnchor R A S)

theorem closedRatioConstantGivesExactValueEvaluator
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (K : ThreeFlavorInternalClosedRatioConstant R A) :
  HasCurrentRatioEvaluatorAtStrength C .exactValue :=
  internalGapShapeAnchorGivesExactValueEvaluator
    R
    A
    (closedRatioConstantAsInternalAnchor R A K)

def closedRatioConstantGivesExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (K : ThreeFlavorInternalClosedRatioConstant R A) :
  AASCNNR9ExactValueFrontier C :=
  internalGapShapeAnchorGivesExactValueFrontier
    R
    A
    (closedRatioConstantAsInternalAnchor R A K)

theorem polynomialRatioAnchorGivesExactValueEvaluator
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (P : ThreeFlavorInternalPolynomialRatioAnchor R A) :
  HasCurrentRatioEvaluatorAtStrength C .exactValue :=
  closedRatioConstantGivesExactValueEvaluator
    R
    A
    (polynomialRatioAnchorAsClosedConstant R A P)

def polynomialRatioAnchorGivesExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (P : ThreeFlavorInternalPolynomialRatioAnchor R A) :
  AASCNNR9ExactValueFrontier C :=
  closedRatioConstantGivesExactValueFrontier
    R
    A
    (polynomialRatioAnchorAsClosedConstant R A P)

theorem polynomialLawAndAASCUniquenessGiveExactValueEvaluator
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (U : AASCAdmissiblePolynomialRootUniquenessCertificate R A)
  (L : ThreeFlavorInternalPolynomialRatioLaw R A U) :
  HasCurrentRatioEvaluatorAtStrength C .exactValue :=
  polynomialRatioAnchorGivesExactValueEvaluator
    R
    A
    (polynomialLawAndAASCUniquenessAsPolynomialAnchor R A U L)

def polynomialLawAndAASCUniquenessGiveExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (U : AASCAdmissiblePolynomialRootUniquenessCertificate R A)
  (L : ThreeFlavorInternalPolynomialRatioLaw R A U) :
  AASCNNR9ExactValueFrontier C :=
  polynomialRatioAnchorGivesExactValueFrontier
    R
    A
    (polynomialLawAndAASCUniquenessAsPolynomialAnchor R A U L)

theorem polynomialLawAndRootInteriorLedgerGiveExactValueEvaluator
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (U : AASCPolynomialRootUniqueInteriorLedger R A)
  (L :
    ThreeFlavorInternalPolynomialRatioLaw
      R
      A
      (rootUniqueInteriorLedgerAsUniquenessCertificate R A U)) :
  HasCurrentRatioEvaluatorAtStrength C .exactValue :=
  polynomialLawAndAASCUniquenessGiveExactValueEvaluator
    R
    A
    (rootUniqueInteriorLedgerAsUniquenessCertificate R A U)
    L

def polynomialLawAndRootInteriorLedgerGiveExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (U : AASCPolynomialRootUniqueInteriorLedger R A)
  (L :
    ThreeFlavorInternalPolynomialRatioLaw
      R
      A
      (rootUniqueInteriorLedgerAsUniquenessCertificate R A U)) :
  AASCNNR9ExactValueFrontier C :=
  polynomialLawAndAASCUniquenessGiveExactValueFrontier
    R
    A
    (rootUniqueInteriorLedgerAsUniquenessCertificate R A U)
    L

theorem polynomialLawAndHybridSingletonRealizationGiveExactValueEvaluator
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (B : AASCPolynomialRootHybridSingletonRealization H R A)
  (hsingle : HybridJointRestrictionSingleton H)
  (L :
    ThreeFlavorInternalPolynomialRatioLaw
      R
      A
      (rootHybridSingletonRealizationAsUniquenessCertificate
        R A B hsingle)) :
  HasCurrentRatioEvaluatorAtStrength C .exactValue :=
  polynomialLawAndAASCUniquenessGiveExactValueEvaluator
    R
    A
    (rootHybridSingletonRealizationAsUniquenessCertificate
      R A B hsingle)
    L

def polynomialLawAndHybridSingletonRealizationGiveExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (B : AASCPolynomialRootHybridSingletonRealization H R A)
  (hsingle : HybridJointRestrictionSingleton H)
  (L :
    ThreeFlavorInternalPolynomialRatioLaw
      R
      A
      (rootHybridSingletonRealizationAsUniquenessCertificate
        R A B hsingle)) :
  AASCNNR9ExactValueFrontier C :=
  polynomialLawAndAASCUniquenessGiveExactValueFrontier
    R
    A
    (rootHybridSingletonRealizationAsUniquenessCertificate
      R A B hsingle)
    L

theorem polynomialLawAndRootRealizationGiveExactValueEvaluator
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (T : AASCPolynomialRootRealizationTheorem H R A)
  (hsingle : HybridJointRestrictionSingleton H)
  (L :
    ThreeFlavorInternalPolynomialRatioLaw
      R
      A
      (rootHybridSingletonRealizationAsUniquenessCertificate
        R
        A
        (polynomialRootRealizationAsHybridSingletonRealization R A T)
        hsingle)) :
  HasCurrentRatioEvaluatorAtStrength C .exactValue :=
  polynomialLawAndHybridSingletonRealizationGiveExactValueEvaluator
    R
    A
    (polynomialRootRealizationAsHybridSingletonRealization R A T)
    hsingle
    L

def polynomialLawAndRootRealizationGiveExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (T : AASCPolynomialRootRealizationTheorem H R A)
  (hsingle : HybridJointRestrictionSingleton H)
  (L :
    ThreeFlavorInternalPolynomialRatioLaw
      R
      A
      (rootHybridSingletonRealizationAsUniquenessCertificate
        R
        A
        (polynomialRootRealizationAsHybridSingletonRealization R A T)
        hsingle)) :
  AASCNNR9ExactValueFrontier C :=
  polynomialLawAndHybridSingletonRealizationGiveExactValueFrontier
    R
    A
    (polynomialRootRealizationAsHybridSingletonRealization R A T)
    hsingle
    L

theorem polynomialLawAndSameScopeRootPredicateGiveExactValueEvaluator
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (T : AASCSameScopePolynomialRootPredicateTheorem H R A)
  (hsingle : HybridJointRestrictionSingleton H)
  (L :
    ThreeFlavorInternalPolynomialRatioLaw
      R
      A
      (rootHybridSingletonRealizationAsUniquenessCertificate
        R
        A
        (polynomialRootRealizationAsHybridSingletonRealization
          R
          A
          (sameScopeRootPredicateAsRootRealizationTheorem R A T))
        hsingle)) :
  HasCurrentRatioEvaluatorAtStrength C .exactValue :=
  polynomialLawAndRootRealizationGiveExactValueEvaluator
    R
    A
    (sameScopeRootPredicateAsRootRealizationTheorem R A T)
    hsingle
    L

def polynomialLawAndSameScopeRootPredicateGiveExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (T : AASCSameScopePolynomialRootPredicateTheorem H R A)
  (hsingle : HybridJointRestrictionSingleton H)
  (L :
    ThreeFlavorInternalPolynomialRatioLaw
      R
      A
      (rootHybridSingletonRealizationAsUniquenessCertificate
        R
        A
        (polynomialRootRealizationAsHybridSingletonRealization
          R
          A
          (sameScopeRootPredicateAsRootRealizationTheorem R A T))
        hsingle)) :
  AASCNNR9ExactValueFrontier C :=
  polynomialLawAndRootRealizationGiveExactValueFrontier
    R
    A
    (sameScopeRootPredicateAsRootRealizationTheorem R A T)
    hsingle
    L

theorem polynomialLawAndSameScopeRootPredicateDefinitionGiveExactValueEvaluator
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (D : AASCSameScopeRootPredicateDefinition H R A)
  (hsingle : HybridJointRestrictionSingleton H)
  (L :
    ThreeFlavorInternalPolynomialRatioLaw
      R
      A
      (rootHybridSingletonRealizationAsUniquenessCertificate
        R
        A
        (polynomialRootRealizationAsHybridSingletonRealization
          R
          A
          (sameScopeRootPredicateAsRootRealizationTheorem
            R
            A
            (sameScopeRootPredicateDefinitionAsPredicateTheorem R A D)))
        hsingle)) :
  HasCurrentRatioEvaluatorAtStrength C .exactValue :=
  polynomialLawAndSameScopeRootPredicateGiveExactValueEvaluator
    R
    A
    (sameScopeRootPredicateDefinitionAsPredicateTheorem R A D)
    hsingle
    L

def polynomialLawAndSameScopeRootPredicateDefinitionGiveExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (D : AASCSameScopeRootPredicateDefinition H R A)
  (hsingle : HybridJointRestrictionSingleton H)
  (L :
    ThreeFlavorInternalPolynomialRatioLaw
      R
      A
      (rootHybridSingletonRealizationAsUniquenessCertificate
        R
        A
        (polynomialRootRealizationAsHybridSingletonRealization
          R
          A
          (sameScopeRootPredicateAsRootRealizationTheorem
            R
            A
            (sameScopeRootPredicateDefinitionAsPredicateTheorem R A D)))
        hsingle)) :
  AASCNNR9ExactValueFrontier C :=
  polynomialLawAndSameScopeRootPredicateGiveExactValueFrontier
    R
    A
    (sameScopeRootPredicateDefinitionAsPredicateTheorem R A D)
    hsingle
    L

/--
Audit gates for promoting a same-scope polynomial root predicate to an
internal polynomial law.  The mathematical equation is kept outside this audit:
the audit only records that the law is internal, calibration-free, and carries
no hidden selector or empirical import.
-/
structure AASCInternalSameScopePolynomialLawAudit where
  polynomialLawDerivedInternally : Prop
  polynomialLawDerivedInternally_proof :
    polynomialLawDerivedInternally
  noOneAnchorImport : Prop
  noOneAnchorImport_proof : noOneAnchorImport
  representativeBranchCollapsedModuloSkin : Prop
  representativeBranchCollapsedModuloSkin_proof :
    representativeBranchCollapsedModuloSkin
  allUnresolvedFreedomsDischarged : Prop
  allUnresolvedFreedomsDischarged_proof :
    allUnresolvedFreedomsDischarged
  calibrationPrior : Prop
  calibrationPrior_proof : calibrationPrior
  transportNeutralOrDischarged : Prop
  transportNeutralOrDischarged_proof :
    transportNeutralOrDischarged
  scaleStatusFixed : Prop
  scaleStatusFixed_proof : scaleStatusFixed
  noEmpiricalFitImport : Prop
  noEmpiricalFitImport_proof : noEmpiricalFitImport

/--
Construct the internal same-scope polynomial law once the closed root carried
by the same-scope predicate is identified with the gap-ratio expression.

This is the main local bridge from the branch singleton route to numerical
prediction: the singleton supplies uniqueness, while `closedRoot_eq_gapRatio`
supplies the actual polynomial-law payload for the current gap ratio.
-/
def sameScopePredicateClosedRootAsPolynomialLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (D : AASCSameScopeRootPredicateDefinition H R A)
  (hsingle : HybridJointRestrictionSingleton H)
  (closedRoot_eq_gapRatio :
    D.closedRatio = threeFlavorGapRatio A.massSquaredLevelOf)
  (audit : AASCInternalSameScopePolynomialLawAudit) :
  ThreeFlavorInternalPolynomialRatioLaw
    R
    A
    (rootHybridSingletonRealizationAsUniquenessCertificate
      R
      A
      (polynomialRootRealizationAsHybridSingletonRealization
        R
        A
        (sameScopeRootPredicateAsRootRealizationTheorem
          R
          A
          (sameScopeRootPredicateDefinitionAsPredicateTheorem R A D)))
      hsingle) :=
  { gapRatio_is_root := by
      simpa [closedRoot_eq_gapRatio] using D.closedRatio_is_root
    gapRatio_admissible := by
      refine
        ⟨C.ratio,
          D.currentRatioInMinimalInterval,
          D.currentRatioModular,
          D.currentRatioSpectral,
          D.currentRatioScoto,
          ?_⟩
      simpa [closedRoot_eq_gapRatio] using D.currentValue_eq_closed
    polynomialLawDerivedInternally :=
      audit.polynomialLawDerivedInternally
    polynomialLawDerivedInternally_proof :=
      audit.polynomialLawDerivedInternally_proof
    noOneAnchorImport := audit.noOneAnchorImport
    noOneAnchorImport_proof := audit.noOneAnchorImport_proof
    representativeBranchCollapsedModuloSkin :=
      audit.representativeBranchCollapsedModuloSkin
    representativeBranchCollapsedModuloSkin_proof :=
      audit.representativeBranchCollapsedModuloSkin_proof
    allUnresolvedFreedomsDischarged :=
      audit.allUnresolvedFreedomsDischarged
    allUnresolvedFreedomsDischarged_proof :=
      audit.allUnresolvedFreedomsDischarged_proof
    calibrationPrior := audit.calibrationPrior
    calibrationPrior_proof := audit.calibrationPrior_proof
    transportNeutralOrDischarged :=
      audit.transportNeutralOrDischarged
    transportNeutralOrDischarged_proof :=
      audit.transportNeutralOrDischarged_proof
    scaleStatusFixed := audit.scaleStatusFixed
    scaleStatusFixed_proof := audit.scaleStatusFixed_proof
    noEmpiricalFitImport := audit.noEmpiricalFitImport
    noEmpiricalFitImport_proof := audit.noEmpiricalFitImport_proof }

/--
The compact package for the next numerical-prediction step.

At this point the branch singleton is already inherited.  What remains is a
polynomial law for the same-scope root predicate.  Once that law is supplied,
Lean exposes a closed value in the coefficient field `R` and proves that this
value is exactly the current three-flavor gap-ratio expression.
-/
structure AASCSameScopePolynomialNumericalPredictionPackage
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M)
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) where
  sameScopePredicate :
    AASCSameScopeRootPredicateDefinition H R A
  branchSingleton :
    HybridJointRestrictionSingleton H
  polynomialLaw :
    ThreeFlavorInternalPolynomialRatioLaw
      R
      A
      (rootHybridSingletonRealizationAsUniquenessCertificate
        R
        A
        (polynomialRootRealizationAsHybridSingletonRealization
          R
          A
          (sameScopeRootPredicateAsRootRealizationTheorem
            R
            A
            (sameScopeRootPredicateDefinitionAsPredicateTheorem
              R
              A
              sameScopePredicate)))
        branchSingleton)

def sameScopeNumericalPredictionClosedValue
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A) : R :=
  P.sameScopePredicate.closedRatio

theorem sameScopeNumericalPredictionClosedValue_eq_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A) :
  sameScopeNumericalPredictionClosedValue P =
    threeFlavorGapRatio A.massSquaredLevelOf := by
  let U :=
    rootHybridSingletonRealizationAsUniquenessCertificate
      R
      A
      (polynomialRootRealizationAsHybridSingletonRealization
        R
        A
        (sameScopeRootPredicateAsRootRealizationTheorem
          R
          A
          (sameScopeRootPredicateDefinitionAsPredicateTheorem
            R
            A
            P.sameScopePredicate)))
      P.branchSingleton
  let anchor :=
    polynomialLawAndAASCUniquenessAsPolynomialAnchor
      R
      A
      U
      P.polynomialLaw
  exact polynomialRatioAnchor_closedRatio_eq_gapRatio anchor

def sameScopeNumericalPredictionExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A) :
  AASCNNR9ExactValueFrontier C :=
  polynomialLawAndSameScopeRootPredicateDefinitionGiveExactValueFrontier
    R
    A
    P.sameScopePredicate
    P.branchSingleton
    P.polynomialLaw

theorem sameScopeNumericalPredictionGivesExactValueEvaluator
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A) :
  HasCurrentRatioEvaluatorAtStrength C .exactValue :=
  polynomialLawAndSameScopeRootPredicateDefinitionGiveExactValueEvaluator
    R
    A
    P.sameScopePredicate
    P.branchSingleton
    P.polynomialLaw

/--
The remaining blocker after this package is fully explicit: one must construct
the package, and its only mathematical payload not already supplied by branch
closure is the internal same-scope polynomial law.
-/
def NeedsSameScopePolynomialNumericalPredictionPackage
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M)
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) : Prop :=
  Not (exists _P :
    AASCSameScopePolynomialNumericalPredictionPackage H R A, True)

def sameScopePredicateClosedRootAsNumericalPredictionPackage
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (D : AASCSameScopeRootPredicateDefinition H R A)
  (hsingle : HybridJointRestrictionSingleton H)
  (closedRoot_eq_gapRatio :
    D.closedRatio = threeFlavorGapRatio A.massSquaredLevelOf)
  (audit : AASCInternalSameScopePolynomialLawAudit) :
  AASCSameScopePolynomialNumericalPredictionPackage H R A :=
  { sameScopePredicate := D
    branchSingleton := hsingle
    polynomialLaw :=
      sameScopePredicateClosedRootAsPolynomialLaw
        R
        A
        D
        hsingle
        closedRoot_eq_gapRatio
        audit }

/--
The audit gates needed to place the current standing ratio inside the hybrid
joint restriction when a closed constant is used as the readback value.
-/
structure AASCCurrentHybridJointWitness
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M) where
  currentRatioInMinimalInterval : C.inMinimalInterval C.ratio
  currentRatioModular : H.modular.ModularRestriction C.ratio
  currentRatioSpectral : H.spectral.spectralRestriction C.ratio
  currentRatioScoto : H.scoto.scotoRestriction C.ratio

noncomputable def closedRatioConstantAsSameScopeRootPredicateDefinition
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (K : ThreeFlavorInternalClosedRatioConstant R A)
  (J : AASCCurrentHybridJointWitness H) :
  AASCSameScopeRootPredicateDefinition H R A :=
  { polynomial := Polynomial.X - Polynomial.C K.closedRatio
    closedRatio := K.closedRatio
    valueOfRatio := fun _ => K.closedRatio
    currentValue_eq_closed := rfl
    currentRatioInMinimalInterval := J.currentRatioInMinimalInterval
    currentRatioModular := J.currentRatioModular
    currentRatioSpectral := J.currentRatioSpectral
    currentRatioScoto := J.currentRatioScoto
    closedRatio_is_root := by simp
    rootRealizationSameScope := K.closedConstantDerivedInternally
    rootRealizationSameScope_proof :=
      K.closedConstantDerivedInternally_proof
    rootRealizationExhaustive :=
      K.representativeBranchCollapsedModuloSkin
    rootRealizationExhaustive_proof :=
      K.representativeBranchCollapsedModuloSkin_proof
    rootReadbackLawful :=
      K.allUnresolvedFreedomsDischarged
    rootReadbackLawful_proof :=
      K.allUnresolvedFreedomsDischarged_proof
    noEmpiricalRootImport := K.noEmpiricalFitImport
    noEmpiricalRootImport_proof := K.noEmpiricalFitImport_proof
    noExtraRootSelector := K.noHiddenNumericalSelector
    noExtraRootSelector_proof := K.noHiddenNumericalSelector_proof }

def closedRatioConstantAsPolynomialLawAudit
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {R : Type}
  [Field R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  (K : ThreeFlavorInternalClosedRatioConstant R A) :
  AASCInternalSameScopePolynomialLawAudit :=
  { polynomialLawDerivedInternally := K.closedConstantDerivedInternally
    polynomialLawDerivedInternally_proof :=
      K.closedConstantDerivedInternally_proof
    noOneAnchorImport := K.noOneAnchorImport
    noOneAnchorImport_proof := K.noOneAnchorImport_proof
    representativeBranchCollapsedModuloSkin :=
      K.representativeBranchCollapsedModuloSkin
    representativeBranchCollapsedModuloSkin_proof :=
      K.representativeBranchCollapsedModuloSkin_proof
    allUnresolvedFreedomsDischarged :=
      K.allUnresolvedFreedomsDischarged
    allUnresolvedFreedomsDischarged_proof :=
      K.allUnresolvedFreedomsDischarged_proof
    calibrationPrior := K.calibrationPrior
    calibrationPrior_proof := K.calibrationPrior_proof
    transportNeutralOrDischarged := K.transportNeutralOrDischarged
    transportNeutralOrDischarged_proof :=
      K.transportNeutralOrDischarged_proof
    scaleStatusFixed := K.scaleStatusFixed
    scaleStatusFixed_proof := K.scaleStatusFixed_proof
    noEmpiricalFitImport := K.noEmpiricalFitImport
    noEmpiricalFitImport_proof := K.noEmpiricalFitImport_proof }

noncomputable def closedRatioConstantAsSameScopeNumericalPredictionPackage
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (K : ThreeFlavorInternalClosedRatioConstant R A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  AASCSameScopePolynomialNumericalPredictionPackage H R A :=
  sameScopePredicateClosedRootAsNumericalPredictionPackage
    R
    A
    (closedRatioConstantAsSameScopeRootPredicateDefinition R A K J)
        hsingle
        K.closedRatio_eq_gapRatio
        (closedRatioConstantAsPolynomialLawAudit K)

noncomputable def canonicalAffineNormalizationAsSameScopeNumericalPredictionPackage
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (Q : ThreeFlavorCanonicalAffineNormalizationAudit A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  AASCSameScopePolynomialNumericalPredictionPackage H R A :=
  closedRatioConstantAsSameScopeNumericalPredictionPackage
    R
    A
    (canonicalAffineNormalizationAsClosedRatioConstant R A Q)
    J
    hsingle

noncomputable def canonicalAffineNormalizationGivesExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (Q : ThreeFlavorCanonicalAffineNormalizationAudit A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  AASCNNR9ExactValueFrontier C :=
  sameScopeNumericalPredictionExactValueFrontier
    R
    A
    (canonicalAffineNormalizationAsSameScopeNumericalPredictionPackage
      R
      A
      Q
      J
      hsingle)

theorem canonicalAffineNormalizationGivesExactValueEvaluator
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (Q : ThreeFlavorCanonicalAffineNormalizationAudit A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  HasCurrentRatioEvaluatorAtStrength C .exactValue :=
  sameScopeNumericalPredictionGivesExactValueEvaluator
    R
    A
    (canonicalAffineNormalizationAsSameScopeNumericalPredictionPackage
      R
      A
      Q
      J
      hsingle)

/--
Displayed value presentation for the current ratio.

The exact evaluator above gives an element of the coefficient field `R`.  A
paper-facing numerical prediction needs one more layer: a concrete presentation
whose denotation is that element.  The presentation may be a numeral, a closed
expression, or an algebraic-root certificate.
-/
structure ThreeFlavorDisplayedRatioPresentation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) where
  Presentation : Type
  displayed : Presentation
  denote : Presentation -> R
  displayed_denotes_gapRatio :
    denote displayed = threeFlavorGapRatio A.massSquaredLevelOf
  presentationDerivedInternally : Prop
  presentationDerivedInternally_proof :
    presentationDerivedInternally
  noOneAnchorImport : Prop
  noOneAnchorImport_proof : noOneAnchorImport
  representativeBranchCollapsedModuloSkin : Prop
  representativeBranchCollapsedModuloSkin_proof :
    representativeBranchCollapsedModuloSkin
  allUnresolvedFreedomsDischarged : Prop
  allUnresolvedFreedomsDischarged_proof :
    allUnresolvedFreedomsDischarged
  calibrationPrior : Prop
  calibrationPrior_proof : calibrationPrior
  transportNeutralOrDischarged : Prop
  transportNeutralOrDischarged_proof :
    transportNeutralOrDischarged
  scaleStatusFixed : Prop
  scaleStatusFixed_proof : scaleStatusFixed
  noHiddenNumericalSelector : Prop
  noHiddenNumericalSelector_proof : noHiddenNumericalSelector
  noEmpiricalFitImport : Prop
  noEmpiricalFitImport_proof : noEmpiricalFitImport

def displayedRatioPresentationAsClosedRatioConstant
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (P : ThreeFlavorDisplayedRatioPresentation R A) :
  ThreeFlavorInternalClosedRatioConstant R A :=
  { closedRatio := P.denote P.displayed
    closedRatio_eq_gapRatio := P.displayed_denotes_gapRatio
    closedConstantDerivedInternally := P.presentationDerivedInternally
    closedConstantDerivedInternally_proof :=
      P.presentationDerivedInternally_proof
    noOneAnchorImport := P.noOneAnchorImport
    noOneAnchorImport_proof := P.noOneAnchorImport_proof
    representativeBranchCollapsedModuloSkin :=
      P.representativeBranchCollapsedModuloSkin
    representativeBranchCollapsedModuloSkin_proof :=
      P.representativeBranchCollapsedModuloSkin_proof
    allUnresolvedFreedomsDischarged :=
      P.allUnresolvedFreedomsDischarged
    allUnresolvedFreedomsDischarged_proof :=
      P.allUnresolvedFreedomsDischarged_proof
    calibrationPrior := P.calibrationPrior
    calibrationPrior_proof := P.calibrationPrior_proof
    transportNeutralOrDischarged := P.transportNeutralOrDischarged
    transportNeutralOrDischarged_proof :=
      P.transportNeutralOrDischarged_proof
    scaleStatusFixed := P.scaleStatusFixed
    scaleStatusFixed_proof := P.scaleStatusFixed_proof
    noHiddenNumericalSelector := P.noHiddenNumericalSelector
    noHiddenNumericalSelector_proof := P.noHiddenNumericalSelector_proof
    noEmpiricalFitImport := P.noEmpiricalFitImport
    noEmpiricalFitImport_proof := P.noEmpiricalFitImport_proof }

noncomputable def displayedRatioPresentationAsNumericalPredictionPackage
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (P : ThreeFlavorDisplayedRatioPresentation R A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  AASCSameScopePolynomialNumericalPredictionPackage H R A :=
  closedRatioConstantAsSameScopeNumericalPredictionPackage
    R
    A
    (displayedRatioPresentationAsClosedRatioConstant R A P)
    J
    hsingle

noncomputable def displayedRatioPresentationGivesExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (P : ThreeFlavorDisplayedRatioPresentation R A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  AASCNNR9ExactValueFrontier C :=
  sameScopeNumericalPredictionExactValueFrontier
    R
    A
    (displayedRatioPresentationAsNumericalPredictionPackage
      R
      A
      P
      J
      hsingle)

def NeedsThreeFlavorDisplayedRatioPresentation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) : Prop :=
  Not (exists _P : ThreeFlavorDisplayedRatioPresentation R A, True)

/--
Algebraic-root presentation of the displayed ratio.

This is stronger than merely saying that the exact value lives in `R`: the
displayed object is a polynomial/root certificate whose denotation is a
distinguished root.  The `root_eq_gapRatio` field is the mathematical readout
claim; the remaining fields certify that the presentation is internal and not
an empirical or selector import.
-/
structure ThreeFlavorAlgebraicRootDisplayedPresentation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) where
  polynomial : Polynomial R
  root : R
  root_is_root : polynomial.eval root = 0
  root_eq_gapRatio : root = threeFlavorGapRatio A.massSquaredLevelOf
  rootClassCertified : Prop
  rootClassCertified_proof : rootClassCertified
  rootUniqueInAdmissibleClass : Prop
  rootUniqueInAdmissibleClass_proof : rootUniqueInAdmissibleClass
  polynomialDerivedInternally : Prop
  polynomialDerivedInternally_proof :
    polynomialDerivedInternally
  noOneAnchorImport : Prop
  noOneAnchorImport_proof : noOneAnchorImport
  representativeBranchCollapsedModuloSkin : Prop
  representativeBranchCollapsedModuloSkin_proof :
    representativeBranchCollapsedModuloSkin
  allUnresolvedFreedomsDischarged : Prop
  allUnresolvedFreedomsDischarged_proof :
    allUnresolvedFreedomsDischarged
  calibrationPrior : Prop
  calibrationPrior_proof : calibrationPrior
  transportNeutralOrDischarged : Prop
  transportNeutralOrDischarged_proof :
    transportNeutralOrDischarged
  scaleStatusFixed : Prop
  scaleStatusFixed_proof : scaleStatusFixed
  noHiddenNumericalSelector : Prop
  noHiddenNumericalSelector_proof : noHiddenNumericalSelector
  noEmpiricalFitImport : Prop
  noEmpiricalFitImport_proof : noEmpiricalFitImport

structure AlgebraicRootPresentationSyntax
  (R : Type)
  [Field R] where
  polynomial : Polynomial R
  root : R
  root_is_root : polynomial.eval root = 0

def algebraicRootDisplayedPresentationAsDisplayed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (P : ThreeFlavorAlgebraicRootDisplayedPresentation R A) :
  ThreeFlavorDisplayedRatioPresentation R A :=
  { Presentation := AlgebraicRootPresentationSyntax R
    displayed :=
      { polynomial := P.polynomial
        root := P.root
        root_is_root := P.root_is_root }
    denote := fun q => q.root
    displayed_denotes_gapRatio := P.root_eq_gapRatio
    presentationDerivedInternally :=
      P.polynomialDerivedInternally /\
        P.rootClassCertified /\
          P.rootUniqueInAdmissibleClass
    presentationDerivedInternally_proof :=
      ⟨P.polynomialDerivedInternally_proof,
        P.rootClassCertified_proof,
        P.rootUniqueInAdmissibleClass_proof⟩
    noOneAnchorImport := P.noOneAnchorImport
    noOneAnchorImport_proof := P.noOneAnchorImport_proof
    representativeBranchCollapsedModuloSkin :=
      P.representativeBranchCollapsedModuloSkin
    representativeBranchCollapsedModuloSkin_proof :=
      P.representativeBranchCollapsedModuloSkin_proof
    allUnresolvedFreedomsDischarged :=
      P.allUnresolvedFreedomsDischarged
    allUnresolvedFreedomsDischarged_proof :=
      P.allUnresolvedFreedomsDischarged_proof
    calibrationPrior := P.calibrationPrior
    calibrationPrior_proof := P.calibrationPrior_proof
    transportNeutralOrDischarged := P.transportNeutralOrDischarged
    transportNeutralOrDischarged_proof :=
      P.transportNeutralOrDischarged_proof
    scaleStatusFixed := P.scaleStatusFixed
    scaleStatusFixed_proof := P.scaleStatusFixed_proof
    noHiddenNumericalSelector := P.noHiddenNumericalSelector
    noHiddenNumericalSelector_proof := P.noHiddenNumericalSelector_proof
    noEmpiricalFitImport := P.noEmpiricalFitImport
    noEmpiricalFitImport_proof := P.noEmpiricalFitImport_proof }

noncomputable def algebraicRootDisplayedPresentationGivesExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (P : ThreeFlavorAlgebraicRootDisplayedPresentation R A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  AASCNNR9ExactValueFrontier C :=
  displayedRatioPresentationGivesExactValueFrontier
    R
    A
    (algebraicRootDisplayedPresentationAsDisplayed R A P)
    J
    hsingle

def NeedsThreeFlavorAlgebraicRootDisplayedPresentation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) : Prop :=
  Not (exists _P :
    ThreeFlavorAlgebraicRootDisplayedPresentation R A, True)

/--
Canonical interior-ratio law.

This is the exact anchor missing after branch singleton closure.  It says an
internal source derives a polynomial and a canonical root for the normalized
interior coordinate, and proves that this root is the three-flavor gap ratio.
Possible sources include modular fixed points, flavor-symmetry sum rules, or
AASC-native role-occupancy/endpoint arguments.
-/
structure ThreeFlavorCanonicalInteriorRatioLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) where
  polynomial : Polynomial R
  canonicalRoot : R
  canonicalRoot_is_root : polynomial.eval canonicalRoot = 0
  canonicalRoot_eq_gapRatio :
    canonicalRoot = threeFlavorGapRatio A.massSquaredLevelOf
  sourceKind : Type
  source : sourceKind
  sourceDerivesPolynomial : Prop
  sourceDerivesPolynomial_proof : sourceDerivesPolynomial
  sourceDerivesCanonicalRoot : Prop
  sourceDerivesCanonicalRoot_proof :
    sourceDerivesCanonicalRoot
  rootClassCertified : Prop
  rootClassCertified_proof : rootClassCertified
  rootUniqueInAdmissibleClass : Prop
  rootUniqueInAdmissibleClass_proof :
    rootUniqueInAdmissibleClass
  sameScopeInteriorLaw : Prop
  sameScopeInteriorLaw_proof : sameScopeInteriorLaw
  notEmpiricalFit : Prop
  notEmpiricalFit_proof : notEmpiricalFit
  notParameterTuning : Prop
  notParameterTuning_proof : notParameterTuning
  noHiddenRootSelector : Prop
  noHiddenRootSelector_proof : noHiddenRootSelector
  noOneAnchorImport : Prop
  noOneAnchorImport_proof : noOneAnchorImport
  representativeBranchCollapsedModuloSkin : Prop
  representativeBranchCollapsedModuloSkin_proof :
    representativeBranchCollapsedModuloSkin
  allUnresolvedFreedomsDischarged : Prop
  allUnresolvedFreedomsDischarged_proof :
    allUnresolvedFreedomsDischarged
  calibrationPrior : Prop
  calibrationPrior_proof : calibrationPrior
  transportNeutralOrDischarged : Prop
  transportNeutralOrDischarged_proof :
    transportNeutralOrDischarged
  scaleStatusFixed : Prop
  scaleStatusFixed_proof : scaleStatusFixed

def canonicalInteriorRatioLawAsAlgebraicRootPresentation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (L : ThreeFlavorCanonicalInteriorRatioLaw R A) :
  ThreeFlavorAlgebraicRootDisplayedPresentation R A :=
  { polynomial := L.polynomial
    root := L.canonicalRoot
    root_is_root := L.canonicalRoot_is_root
    root_eq_gapRatio := L.canonicalRoot_eq_gapRatio
    rootClassCertified := L.rootClassCertified
    rootClassCertified_proof := L.rootClassCertified_proof
    rootUniqueInAdmissibleClass :=
      L.rootUniqueInAdmissibleClass /\
        L.sameScopeInteriorLaw
    rootUniqueInAdmissibleClass_proof :=
      ⟨L.rootUniqueInAdmissibleClass_proof,
        L.sameScopeInteriorLaw_proof⟩
    polynomialDerivedInternally :=
      L.sourceDerivesPolynomial /\
        L.sourceDerivesCanonicalRoot /\
          L.notParameterTuning
    polynomialDerivedInternally_proof :=
      ⟨L.sourceDerivesPolynomial_proof,
        L.sourceDerivesCanonicalRoot_proof,
        L.notParameterTuning_proof⟩
    noOneAnchorImport := L.noOneAnchorImport
    noOneAnchorImport_proof := L.noOneAnchorImport_proof
    representativeBranchCollapsedModuloSkin :=
      L.representativeBranchCollapsedModuloSkin
    representativeBranchCollapsedModuloSkin_proof :=
      L.representativeBranchCollapsedModuloSkin_proof
    allUnresolvedFreedomsDischarged :=
      L.allUnresolvedFreedomsDischarged
    allUnresolvedFreedomsDischarged_proof :=
      L.allUnresolvedFreedomsDischarged_proof
    calibrationPrior := L.calibrationPrior
    calibrationPrior_proof := L.calibrationPrior_proof
    transportNeutralOrDischarged := L.transportNeutralOrDischarged
    transportNeutralOrDischarged_proof :=
      L.transportNeutralOrDischarged_proof
    scaleStatusFixed := L.scaleStatusFixed
    scaleStatusFixed_proof := L.scaleStatusFixed_proof
    noHiddenNumericalSelector := L.noHiddenRootSelector
    noHiddenNumericalSelector_proof := L.noHiddenRootSelector_proof
    noEmpiricalFitImport := L.notEmpiricalFit
    noEmpiricalFitImport_proof := L.notEmpiricalFit_proof }

noncomputable def canonicalInteriorRatioLawGivesExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (L : ThreeFlavorCanonicalInteriorRatioLaw R A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  AASCNNR9ExactValueFrontier C :=
  algebraicRootDisplayedPresentationGivesExactValueFrontier
    R
    A
    (canonicalInteriorRatioLawAsAlgebraicRootPresentation R A L)
    J
    hsingle

def NeedsThreeFlavorCanonicalInteriorRatioLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) : Prop :=
  Not (exists _L : ThreeFlavorCanonicalInteriorRatioLaw R A, True)

/--
Named source families that could genuinely fix the normalized interior
coordinate.  This is provenance, not proof authority.
-/
inductive AASCInteriorAnchorSourceKind where
  | modularFixedPoint
  | flavorSymmetrySumRule
  | roleOccupancyEndpoint
  | operatorSpectralInvariant
  | quotientNormalForm
  | otherInternalAASCSource
  deriving DecidableEq

/--
Nontrivial coordinate anchor for the normalized interior ratio.

This is stronger than the branch singleton and stronger than the symbolic
quotient formula.  It must provide a root value from an internal source and
prove that this independently presented root is the gap ratio.  The
`notDefinedByGapQuotient` field blocks the vacuous construction where the
"anchor" is just `threeFlavorGapRatio A.massSquaredLevelOf` renamed.
-/
structure ThreeFlavorInternalCoordinateAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) where
  kind : AASCInteriorAnchorSourceKind
  Source : Type
  source : Source
  polynomial : Polynomial R
  root : R
  root_is_root : polynomial.eval root = 0
  root_eq_gapRatio : root = threeFlavorGapRatio A.massSquaredLevelOf
  sourceConstructsPolynomial : Prop
  sourceConstructsPolynomial_proof : sourceConstructsPolynomial
  sourceConstructsRoot : Prop
  sourceConstructsRoot_proof : sourceConstructsRoot
  notDefinedByGapQuotient : Prop
  notDefinedByGapQuotient_proof : notDefinedByGapQuotient
  sameScopeAsStandingRatio : Prop
  sameScopeAsStandingRatio_proof : sameScopeAsStandingRatio
  rootClassCertified : Prop
  rootClassCertified_proof : rootClassCertified
  rootUniqueInAdmissibleClass : Prop
  rootUniqueInAdmissibleClass_proof :
    rootUniqueInAdmissibleClass
  noEmpiricalFitImport : Prop
  noEmpiricalFitImport_proof : noEmpiricalFitImport
  noParameterTuning : Prop
  noParameterTuning_proof : noParameterTuning
  noHiddenRootSelector : Prop
  noHiddenRootSelector_proof : noHiddenRootSelector
  noOneAnchorImport : Prop
  noOneAnchorImport_proof : noOneAnchorImport
  representativeBranchCollapsedModuloSkin : Prop
  representativeBranchCollapsedModuloSkin_proof :
    representativeBranchCollapsedModuloSkin
  allUnresolvedFreedomsDischarged : Prop
  allUnresolvedFreedomsDischarged_proof :
    allUnresolvedFreedomsDischarged
  calibrationPrior : Prop
  calibrationPrior_proof : calibrationPrior
  transportNeutralOrDischarged : Prop
  transportNeutralOrDischarged_proof :
    transportNeutralOrDischarged
  scaleStatusFixed : Prop
  scaleStatusFixed_proof : scaleStatusFixed

def internalCoordinateAnchorAsCanonicalInteriorRatioLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (K : ThreeFlavorInternalCoordinateAnchor R A) :
  ThreeFlavorCanonicalInteriorRatioLaw R A :=
  { polynomial := K.polynomial
    canonicalRoot := K.root
    canonicalRoot_is_root := K.root_is_root
    canonicalRoot_eq_gapRatio := K.root_eq_gapRatio
    sourceKind := K.Source
    source := K.source
    sourceDerivesPolynomial := K.sourceConstructsPolynomial
    sourceDerivesPolynomial_proof :=
      K.sourceConstructsPolynomial_proof
    sourceDerivesCanonicalRoot :=
      K.sourceConstructsRoot /\ K.notDefinedByGapQuotient
    sourceDerivesCanonicalRoot_proof :=
      ⟨K.sourceConstructsRoot_proof,
        K.notDefinedByGapQuotient_proof⟩
    rootClassCertified := K.rootClassCertified
    rootClassCertified_proof := K.rootClassCertified_proof
    rootUniqueInAdmissibleClass := K.rootUniqueInAdmissibleClass
    rootUniqueInAdmissibleClass_proof :=
      K.rootUniqueInAdmissibleClass_proof
    sameScopeInteriorLaw := K.sameScopeAsStandingRatio
    sameScopeInteriorLaw_proof := K.sameScopeAsStandingRatio_proof
    notEmpiricalFit := K.noEmpiricalFitImport
    notEmpiricalFit_proof := K.noEmpiricalFitImport_proof
    notParameterTuning := K.noParameterTuning
    notParameterTuning_proof := K.noParameterTuning_proof
    noHiddenRootSelector := K.noHiddenRootSelector
    noHiddenRootSelector_proof := K.noHiddenRootSelector_proof
    noOneAnchorImport := K.noOneAnchorImport
    noOneAnchorImport_proof := K.noOneAnchorImport_proof
    representativeBranchCollapsedModuloSkin :=
      K.representativeBranchCollapsedModuloSkin
    representativeBranchCollapsedModuloSkin_proof :=
      K.representativeBranchCollapsedModuloSkin_proof
    allUnresolvedFreedomsDischarged :=
      K.allUnresolvedFreedomsDischarged
    allUnresolvedFreedomsDischarged_proof :=
      K.allUnresolvedFreedomsDischarged_proof
    calibrationPrior := K.calibrationPrior
    calibrationPrior_proof := K.calibrationPrior_proof
    transportNeutralOrDischarged := K.transportNeutralOrDischarged
    transportNeutralOrDischarged_proof :=
      K.transportNeutralOrDischarged_proof
    scaleStatusFixed := K.scaleStatusFixed
    scaleStatusFixed_proof := K.scaleStatusFixed_proof }

noncomputable def internalCoordinateAnchorGivesExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (K : ThreeFlavorInternalCoordinateAnchor R A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  AASCNNR9ExactValueFrontier C :=
  canonicalInteriorRatioLawGivesExactValueFrontier
    R
    A
    (internalCoordinateAnchorAsCanonicalInteriorRatioLaw R A K)
    J
    hsingle

def NeedsThreeFlavorInternalCoordinateAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) : Prop :=
  Not (exists _K : ThreeFlavorInternalCoordinateAnchor R A, True)

/--
Source-certified coordinate anchor.

The shared anchor object carries the mathematical payload.  This wrapper records
which source family supplies it, so manuscript routes can be audited without
duplicating the whole coordinate-anchor field list.
-/
structure ThreeFlavorSourceCertifiedCoordinateAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (kind : AASCInteriorAnchorSourceKind) where
  anchor : ThreeFlavorInternalCoordinateAnchor R A
  anchorKind_eq : anchor.kind = kind
  sourceFamilyCertified : Prop
  sourceFamilyCertified_proof : sourceFamilyCertified

def sourceCertifiedCoordinateAnchorAsInternalAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  {kind : AASCInteriorAnchorSourceKind}
  (S : ThreeFlavorSourceCertifiedCoordinateAnchor R A kind) :
  ThreeFlavorInternalCoordinateAnchor R A :=
  S.anchor

noncomputable def sourceCertifiedCoordinateAnchorGivesExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  {kind : AASCInteriorAnchorSourceKind}
  (S : ThreeFlavorSourceCertifiedCoordinateAnchor R A kind)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  AASCNNR9ExactValueFrontier C :=
  internalCoordinateAnchorGivesExactValueFrontier
    R
    A
    (sourceCertifiedCoordinateAnchorAsInternalAnchor R A S)
    J
    hsingle

abbrev ThreeFlavorModularFixedPointCoordinateAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) :=
  ThreeFlavorSourceCertifiedCoordinateAnchor
    R A .modularFixedPoint

abbrev ThreeFlavorFlavorSumRuleCoordinateAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) :=
  ThreeFlavorSourceCertifiedCoordinateAnchor
    R A .flavorSymmetrySumRule

abbrev ThreeFlavorRoleOccupancyEndpointCoordinateAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) :=
  ThreeFlavorSourceCertifiedCoordinateAnchor
    R A .roleOccupancyEndpoint

abbrev ThreeFlavorOperatorSpectralInvariantCoordinateAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) :=
  ThreeFlavorSourceCertifiedCoordinateAnchor
    R A .operatorSpectralInvariant

abbrev ThreeFlavorQuotientNormalFormCoordinateAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) :=
  ThreeFlavorSourceCertifiedCoordinateAnchor
    R A .quotientNormalForm

def NeedsThreeFlavorModularFixedPointCoordinateAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) : Prop :=
  Not (exists _S :
    ThreeFlavorModularFixedPointCoordinateAnchor R A, True)

def NeedsThreeFlavorFlavorSumRuleCoordinateAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) : Prop :=
  Not (exists _S :
    ThreeFlavorFlavorSumRuleCoordinateAnchor R A, True)

def NeedsThreeFlavorRoleOccupancyEndpointCoordinateAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) : Prop :=
  Not (exists _S :
    ThreeFlavorRoleOccupancyEndpointCoordinateAnchor R A, True)

def NeedsThreeFlavorOperatorSpectralInvariantCoordinateAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) : Prop :=
  Not (exists _S :
    ThreeFlavorOperatorSpectralInvariantCoordinateAnchor R A, True)

def NeedsThreeFlavorQuotientNormalFormCoordinateAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) : Prop :=
  Not (exists _S :
    ThreeFlavorQuotientNormalFormCoordinateAnchor R A, True)

/--
Syntax/root part of a quotient-normal-form coordinate law.

This deliberately does not say that the normal form denotes the neutrino ratio.
It only supplies the formal object, its denotation map, and the polynomial/root
certificate carried by that object.
-/
structure ThreeFlavorQuotientNormalFormSyntax
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) where
  NormalForm : Type
  normalForm : NormalForm
  denoteNormalForm : NormalForm -> R
  polynomialOfNormalForm : NormalForm -> Polynomial R
  rootOfNormalForm : NormalForm -> R
  root_is_root :
    (polynomialOfNormalForm normalForm).eval
      (rootOfNormalForm normalForm) = 0
  root_eq_denotation :
    rootOfNormalForm normalForm = denoteNormalForm normalForm

/--
Denotation part of the quotient-normal-form coordinate law.

This is the actual mathematical payload: the internally constructed normal form
denotes the same element as the standing three-flavor gap ratio.
-/
structure ThreeFlavorQuotientNormalFormDenotation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A) where
  denotation_eq_gapRatio :
    S.denoteNormalForm S.normalForm =
      threeFlavorGapRatio A.massSquaredLevelOf

/--
Uniqueness criterion for proving the normal-form denotation theorem.

Rather than asserting the equality directly, this object says that the
normal-form denotation and the standing gap ratio both satisfy the same
source-internal coordinate predicate, and that this predicate has at most one
solution.  This is the natural AASC route from object singleton to coordinate
readout: identify the shared internal role, then use uniqueness.
-/
structure ThreeFlavorQuotientNormalFormDenotationCriterion
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A) where
  CoordinatePredicate : R -> Prop
  normalFormDenotation_satisfies :
    CoordinatePredicate (S.denoteNormalForm S.normalForm)
  gapRatio_satisfies :
    CoordinatePredicate (threeFlavorGapRatio A.massSquaredLevelOf)
  coordinatePredicate_unique :
    forall x y : R,
      CoordinatePredicate x ->
        CoordinatePredicate y ->
          x = y
  predicateConstructedInternally : Prop
  predicateConstructedInternally_proof :
    predicateConstructedInternally
  predicateSameScopeAsStandingRatio : Prop
  predicateSameScopeAsStandingRatio_proof :
    predicateSameScopeAsStandingRatio
  predicateNotGapQuotientDefinition : Prop
  predicateNotGapQuotientDefinition_proof :
    predicateNotGapQuotientDefinition

def quotientNormalFormDenotationCriterionAsDenotation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A)
  (K : ThreeFlavorQuotientNormalFormDenotationCriterion R A S) :
  ThreeFlavorQuotientNormalFormDenotation R A S :=
  { denotation_eq_gapRatio :=
      K.coordinatePredicate_unique
        (S.denoteNormalForm S.normalForm)
        (threeFlavorGapRatio A.massSquaredLevelOf)
        K.normalFormDenotation_satisfies
        K.gapRatio_satisfies }

/--
Readback bridge from a quotient normal form to an already established
same-scope polynomial root predicate.

The numerical-prediction package contains the branch-singleton uniqueness
engine.  This object supplies the missing local readback: the normal-form
denotation is a root in the same admitted root predicate.  It is intentionally
not a value claim by itself.
-/
structure ThreeFlavorQuotientNormalFormSameScopeRootReadback
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A) where
  normalFormDenotation_is_root :
    P.sameScopePredicate.polynomial.eval
      (S.denoteNormalForm S.normalForm) = 0
  normalFormDenotation_admissible :
    SameScopeHybridRootRealized
      H
      R
      P.sameScopePredicate.valueOfRatio
      (S.denoteNormalForm S.normalForm)
  readbackConstructedInternally : Prop
  readbackConstructedInternally_proof :
    readbackConstructedInternally
  readbackSameScopeAsStandingRatio : Prop
  readbackSameScopeAsStandingRatio_proof :
    readbackSameScopeAsStandingRatio
  readbackNotGapQuotientDefinition : Prop
  readbackNotGapQuotientDefinition_proof :
    readbackNotGapQuotientDefinition

/--
Concrete same-scope realization of the quotient-normal-form denotation.

This is a more constructive way to discharge the root-readback obligation:
exhibit a same-scope ratio whose certified readout is exactly the normal-form
denotation, and prove that this denotation satisfies the internal polynomial.
-/
structure ThreeFlavorQuotientNormalFormSameScopeRealization
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A) where
  realizedRatio : C.Ratio
  realizedRatio_minimal :
    C.inMinimalInterval realizedRatio
  realizedRatio_modular :
    H.modular.ModularRestriction realizedRatio
  realizedRatio_spectral :
    H.spectral.spectralRestriction realizedRatio
  realizedRatio_scoto :
    H.scoto.scotoRestriction realizedRatio
  realizedRatio_reads_denotation :
    P.sameScopePredicate.valueOfRatio realizedRatio =
      S.denoteNormalForm S.normalForm
  normalFormDenotation_is_root :
    P.sameScopePredicate.polynomial.eval
      (S.denoteNormalForm S.normalForm) = 0
  realizationConstructedInternally : Prop
  realizationConstructedInternally_proof :
    realizationConstructedInternally
  realizationSameScopeAsStandingRatio : Prop
  realizationSameScopeAsStandingRatio_proof :
    realizationSameScopeAsStandingRatio
  realizationNotGapQuotientDefinition : Prop
  realizationNotGapQuotientDefinition_proof :
    realizationNotGapQuotientDefinition

/--
Current-ratio readback for the quotient-normal-form denotation.

This is the most local realization route: prove that the normal-form denotation
is exactly the readout of the already current same-scope ratio.  The same-scope
predicate package then supplies the joint-restriction witnesses and the
polynomial-root proof.
-/
structure ThreeFlavorQuotientNormalFormCurrentRatioReadback
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A) where
  normalFormDenotation_eq_currentReadout :
    S.denoteNormalForm S.normalForm =
      P.sameScopePredicate.valueOfRatio C.ratio
  readbackConstructedInternally : Prop
  readbackConstructedInternally_proof :
    readbackConstructedInternally
  readbackSameScopeAsStandingRatio : Prop
  readbackSameScopeAsStandingRatio_proof :
    readbackSameScopeAsStandingRatio
  readbackNotGapQuotientDefinition : Prop
  readbackNotGapQuotientDefinition_proof :
    readbackNotGapQuotientDefinition

/--
Closed-root readback for the quotient-normal-form denotation.

This proves the current-ratio readback without defining the normal form by the
gap quotient.  The source only has to identify the normal-form root with the
closed root carried by the same-scope polynomial package.  Since the syntax
already proves `root = denotation`, and the package proves the current readout
is the same closed root, the desired readback follows.
-/
structure ThreeFlavorQuotientNormalFormClosedRootReadback
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A) where
  normalFormRoot_eq_closedRoot :
    S.rootOfNormalForm S.normalForm =
      P.sameScopePredicate.closedRatio
  closedRootReadbackConstructedInternally : Prop
  closedRootReadbackConstructedInternally_proof :
    closedRootReadbackConstructedInternally
  closedRootReadbackSameScopeAsStandingRatio : Prop
  closedRootReadbackSameScopeAsStandingRatio_proof :
    closedRootReadbackSameScopeAsStandingRatio
  closedRootReadbackNotGapQuotientDefinition : Prop
  closedRootReadbackNotGapQuotientDefinition_proof :
    closedRootReadbackNotGapQuotientDefinition

/--
Final local payload for the quotient-normal-form route.

This object says that the quotient-normal-form syntax, the same-scope
polynomial package, and the AASC audit all share the same closed root.  Once it
is supplied, every downstream object is assembled mechanically.
-/
structure ThreeFlavorQuotientNormalFormClosedRootIdentification
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A) where
  root_eq_sameScopeClosedRoot :
    S.rootOfNormalForm S.normalForm =
      P.sameScopePredicate.closedRatio
  rootIdentificationConstructedInternally : Prop
  rootIdentificationConstructedInternally_proof :
    rootIdentificationConstructedInternally
  rootIdentificationSameScopeAsStandingRatio : Prop
  rootIdentificationSameScopeAsStandingRatio_proof :
    rootIdentificationSameScopeAsStandingRatio
  rootIdentificationNotGapQuotientDefinition : Prop
  rootIdentificationNotGapQuotientDefinition_proof :
    rootIdentificationNotGapQuotientDefinition
  rootIdentificationNoEmpiricalFitImport : Prop
  rootIdentificationNoEmpiricalFitImport_proof :
    rootIdentificationNoEmpiricalFitImport
  rootIdentificationNoParameterTuning : Prop
  rootIdentificationNoParameterTuning_proof :
    rootIdentificationNoParameterTuning
  rootIdentificationNoHiddenRootSelector : Prop
  rootIdentificationNoHiddenRootSelector_proof :
    rootIdentificationNoHiddenRootSelector

def quotientNormalFormClosedRootIdentificationAsReadback
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A)
  (I : ThreeFlavorQuotientNormalFormClosedRootIdentification R A S P) :
  ThreeFlavorQuotientNormalFormClosedRootReadback R A S P :=
  { normalFormRoot_eq_closedRoot :=
      I.root_eq_sameScopeClosedRoot
    closedRootReadbackConstructedInternally :=
      I.rootIdentificationConstructedInternally
    closedRootReadbackConstructedInternally_proof :=
      I.rootIdentificationConstructedInternally_proof
    closedRootReadbackSameScopeAsStandingRatio :=
      I.rootIdentificationSameScopeAsStandingRatio
    closedRootReadbackSameScopeAsStandingRatio_proof :=
      I.rootIdentificationSameScopeAsStandingRatio_proof
    closedRootReadbackNotGapQuotientDefinition :=
      I.rootIdentificationNotGapQuotientDefinition
    closedRootReadbackNotGapQuotientDefinition_proof :=
      I.rootIdentificationNotGapQuotientDefinition_proof }

/--
Canonical quotient-normal-form syntax obtained from the same-scope closed
root.  This is not the gap quotient in disguise: the root is taken from the
same-scope polynomial package.
-/
def sameScopeClosedRootAsQuotientNormalFormSyntax
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A) :
  ThreeFlavorQuotientNormalFormSyntax R A :=
  { NormalForm := Unit
    normalForm := ()
    denoteNormalForm := fun _ => P.sameScopePredicate.closedRatio
    polynomialOfNormalForm := fun _ => P.sameScopePredicate.polynomial
    rootOfNormalForm := fun _ => P.sameScopePredicate.closedRatio
    root_is_root := P.sameScopePredicate.closedRatio_is_root
    root_eq_denotation := rfl }

/--
For the canonical same-scope closed-root normal form, the quotient-normal-form
root is definitionally the same internal closed root carried by the same-scope
polynomial package.
-/
def sameScopeClosedRootNormalFormIdentification
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A) :
  ThreeFlavorQuotientNormalFormClosedRootIdentification
    R
    A
    (sameScopeClosedRootAsQuotientNormalFormSyntax R A P)
    P :=
  { root_eq_sameScopeClosedRoot := rfl
    rootIdentificationConstructedInternally :=
      P.polynomialLaw.polynomialLawDerivedInternally
    rootIdentificationConstructedInternally_proof :=
      P.polynomialLaw.polynomialLawDerivedInternally_proof
    rootIdentificationSameScopeAsStandingRatio :=
      P.sameScopePredicate.rootReadbackLawful
    rootIdentificationSameScopeAsStandingRatio_proof :=
      P.sameScopePredicate.rootReadbackLawful_proof
    rootIdentificationNotGapQuotientDefinition :=
      P.polynomialLaw.noOneAnchorImport /\
        P.sameScopePredicate.noExtraRootSelector
    rootIdentificationNotGapQuotientDefinition_proof :=
      ⟨P.polynomialLaw.noOneAnchorImport_proof,
        P.sameScopePredicate.noExtraRootSelector_proof⟩
    rootIdentificationNoEmpiricalFitImport :=
      P.polynomialLaw.noEmpiricalFitImport /\
        P.sameScopePredicate.noEmpiricalRootImport
    rootIdentificationNoEmpiricalFitImport_proof :=
      ⟨P.polynomialLaw.noEmpiricalFitImport_proof,
        P.sameScopePredicate.noEmpiricalRootImport_proof⟩
    rootIdentificationNoParameterTuning :=
      P.polynomialLaw.calibrationPrior /\
        P.polynomialLaw.transportNeutralOrDischarged /\
          P.polynomialLaw.scaleStatusFixed
    rootIdentificationNoParameterTuning_proof :=
      ⟨P.polynomialLaw.calibrationPrior_proof,
        P.polynomialLaw.transportNeutralOrDischarged_proof,
        P.polynomialLaw.scaleStatusFixed_proof⟩
    rootIdentificationNoHiddenRootSelector :=
      P.sameScopePredicate.noExtraRootSelector
    rootIdentificationNoHiddenRootSelector_proof :=
      P.sameScopePredicate.noExtraRootSelector_proof }

theorem quotientNormalFormClosedRootReadback_eq_currentReadout
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {S : ThreeFlavorQuotientNormalFormSyntax R A}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (B : ThreeFlavorQuotientNormalFormClosedRootReadback R A S P) :
  S.denoteNormalForm S.normalForm =
    P.sameScopePredicate.valueOfRatio C.ratio := by
  calc
    S.denoteNormalForm S.normalForm =
        S.rootOfNormalForm S.normalForm := S.root_eq_denotation.symm
    _ = P.sameScopePredicate.closedRatio :=
        B.normalFormRoot_eq_closedRoot
    _ = P.sameScopePredicate.valueOfRatio C.ratio :=
        P.sameScopePredicate.currentValue_eq_closed.symm

def quotientNormalFormClosedRootReadbackAsCurrentRatioReadback
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A)
  (B : ThreeFlavorQuotientNormalFormClosedRootReadback R A S P) :
  ThreeFlavorQuotientNormalFormCurrentRatioReadback R A S P :=
  { normalFormDenotation_eq_currentReadout :=
      quotientNormalFormClosedRootReadback_eq_currentReadout B
    readbackConstructedInternally :=
      B.closedRootReadbackConstructedInternally
    readbackConstructedInternally_proof :=
      B.closedRootReadbackConstructedInternally_proof
    readbackSameScopeAsStandingRatio :=
      B.closedRootReadbackSameScopeAsStandingRatio
    readbackSameScopeAsStandingRatio_proof :=
      B.closedRootReadbackSameScopeAsStandingRatio_proof
    readbackNotGapQuotientDefinition :=
      B.closedRootReadbackNotGapQuotientDefinition
    readbackNotGapQuotientDefinition_proof :=
      B.closedRootReadbackNotGapQuotientDefinition_proof }

def quotientNormalFormCurrentRatioReadbackAsSameScopeRealization
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A)
  (B : ThreeFlavorQuotientNormalFormCurrentRatioReadback R A S P) :
  ThreeFlavorQuotientNormalFormSameScopeRealization R A S P := by
  let d := S.denoteNormalForm S.normalForm
  have hdClosed : d = P.sameScopePredicate.closedRatio := by
    calc
      d = P.sameScopePredicate.valueOfRatio C.ratio :=
        B.normalFormDenotation_eq_currentReadout
      _ = P.sameScopePredicate.closedRatio :=
        P.sameScopePredicate.currentValue_eq_closed
  exact
  { realizedRatio := C.ratio
    realizedRatio_minimal :=
      P.sameScopePredicate.currentRatioInMinimalInterval
    realizedRatio_modular :=
      P.sameScopePredicate.currentRatioModular
    realizedRatio_spectral :=
      P.sameScopePredicate.currentRatioSpectral
    realizedRatio_scoto :=
      P.sameScopePredicate.currentRatioScoto
    realizedRatio_reads_denotation :=
      B.normalFormDenotation_eq_currentReadout.symm
    normalFormDenotation_is_root := by
      simpa [d, hdClosed] using
        P.sameScopePredicate.closedRatio_is_root
    realizationConstructedInternally :=
      B.readbackConstructedInternally
    realizationConstructedInternally_proof :=
      B.readbackConstructedInternally_proof
    realizationSameScopeAsStandingRatio :=
      B.readbackSameScopeAsStandingRatio
    realizationSameScopeAsStandingRatio_proof :=
      B.readbackSameScopeAsStandingRatio_proof
    realizationNotGapQuotientDefinition :=
      B.readbackNotGapQuotientDefinition
    realizationNotGapQuotientDefinition_proof :=
      B.readbackNotGapQuotientDefinition_proof }

def quotientNormalFormSameScopeRealizationAsReadback
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A)
  (B : ThreeFlavorQuotientNormalFormSameScopeRealization R A S P) :
  ThreeFlavorQuotientNormalFormSameScopeRootReadback R A S P :=
  { normalFormDenotation_is_root :=
      B.normalFormDenotation_is_root
    normalFormDenotation_admissible :=
      ⟨B.realizedRatio,
        B.realizedRatio_minimal,
        B.realizedRatio_modular,
        B.realizedRatio_spectral,
        B.realizedRatio_scoto,
        B.realizedRatio_reads_denotation⟩
    readbackConstructedInternally :=
      B.realizationConstructedInternally
    readbackConstructedInternally_proof :=
      B.realizationConstructedInternally_proof
    readbackSameScopeAsStandingRatio :=
      B.realizationSameScopeAsStandingRatio
    readbackSameScopeAsStandingRatio_proof :=
      B.realizationSameScopeAsStandingRatio_proof
    readbackNotGapQuotientDefinition :=
      B.realizationNotGapQuotientDefinition
    readbackNotGapQuotientDefinition_proof :=
      B.realizationNotGapQuotientDefinition_proof }

def quotientNormalFormClosedRootIdentificationAsCurrentReadback
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A)
  (I : ThreeFlavorQuotientNormalFormClosedRootIdentification R A S P) :
  ThreeFlavorQuotientNormalFormCurrentRatioReadback R A S P :=
  quotientNormalFormClosedRootReadbackAsCurrentRatioReadback
    R
    A
    S
    P
    (quotientNormalFormClosedRootIdentificationAsReadback R A S P I)

def quotientNormalFormClosedRootIdentificationAsSameScopeRealization
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A)
  (I : ThreeFlavorQuotientNormalFormClosedRootIdentification R A S P) :
  ThreeFlavorQuotientNormalFormSameScopeRealization R A S P :=
  quotientNormalFormCurrentRatioReadbackAsSameScopeRealization
    R
    A
    S
    P
    (quotientNormalFormClosedRootIdentificationAsCurrentReadback R A S P I)

def quotientNormalFormClosedRootIdentificationAsRootReadback
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A)
  (I : ThreeFlavorQuotientNormalFormClosedRootIdentification R A S P) :
  ThreeFlavorQuotientNormalFormSameScopeRootReadback R A S P :=
  quotientNormalFormSameScopeRealizationAsReadback
    R
    A
    S
    P
    (quotientNormalFormClosedRootIdentificationAsSameScopeRealization R A S P I)

def quotientNormalFormSameScopeReadbackAsDenotationCriterion
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A)
  (B : ThreeFlavorQuotientNormalFormSameScopeRootReadback R A S P) :
  ThreeFlavorQuotientNormalFormDenotationCriterion R A S := by
  let T :=
    sameScopeRootPredicateDefinitionAsPredicateTheorem
      R
      A
      P.sameScopePredicate
  let realization :=
    sameScopeRootPredicateAsRootRealizationTheorem
      R
      A
      T
  let singleton :=
    polynomialRootRealizationAsHybridSingletonRealization
      R
      A
      realization
  let U :=
    rootHybridSingletonRealizationAsUniquenessCertificate
      R
      A
      singleton
      P.branchSingleton
  exact
  { CoordinatePredicate := fun x =>
      P.sameScopePredicate.polynomial.eval x = 0 /\
        SameScopeHybridRootRealized
          H
          R
          P.sameScopePredicate.valueOfRatio
          x
    normalFormDenotation_satisfies :=
      ⟨B.normalFormDenotation_is_root,
        B.normalFormDenotation_admissible⟩
    gapRatio_satisfies :=
      ⟨P.polynomialLaw.gapRatio_is_root,
        P.polynomialLaw.gapRatio_admissible⟩
    coordinatePredicate_unique := by
      intro x y hx hy
      have hxClosed : x = U.closedRatio :=
        U.uniqueAdmissibleRoot x hx.1 hx.2
      have hyClosed : y = U.closedRatio :=
        U.uniqueAdmissibleRoot y hy.1 hy.2
      exact hxClosed.trans hyClosed.symm
    predicateConstructedInternally := B.readbackConstructedInternally
    predicateConstructedInternally_proof :=
      B.readbackConstructedInternally_proof
    predicateSameScopeAsStandingRatio := B.readbackSameScopeAsStandingRatio
    predicateSameScopeAsStandingRatio_proof :=
      B.readbackSameScopeAsStandingRatio_proof
    predicateNotGapQuotientDefinition :=
      B.readbackNotGapQuotientDefinition
    predicateNotGapQuotientDefinition_proof :=
      B.readbackNotGapQuotientDefinition_proof }

/--
AASC audit part of the quotient-normal-form coordinate law.

These are the admissibility and anti-tautology guards.  They do not determine
the value by themselves, but they certify that the value theorem is not a hidden
empirical import, parameter choice, or quotient-as-answer relabeling.
-/
structure ThreeFlavorQuotientNormalFormAASCAudit
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A) where
  normalFormConstructedInternally : Prop
  normalFormConstructedInternally_proof :
    normalFormConstructedInternally
  normalFormUniqueInQuotient : Prop
  normalFormUniqueInQuotient_proof :
    normalFormUniqueInQuotient
  quotientFiberExhaustedModuloSkin : Prop
  quotientFiberExhaustedModuloSkin_proof :
    quotientFiberExhaustedModuloSkin
  exactnessRelevantRepresentativesControlled : Prop
  exactnessRelevantRepresentativesControlled_proof :
    exactnessRelevantRepresentativesControlled
  notDefinedByGapQuotient : Prop
  notDefinedByGapQuotient_proof : notDefinedByGapQuotient
  sameScopeAsStandingRatio : Prop
  sameScopeAsStandingRatio_proof : sameScopeAsStandingRatio
  rootClassCertified : Prop
  rootClassCertified_proof : rootClassCertified
  noEmpiricalFitImport : Prop
  noEmpiricalFitImport_proof : noEmpiricalFitImport
  noParameterTuning : Prop
  noParameterTuning_proof : noParameterTuning
  noHiddenRootSelector : Prop
  noHiddenRootSelector_proof : noHiddenRootSelector
  noOneAnchorImport : Prop
  noOneAnchorImport_proof : noOneAnchorImport
  allUnresolvedFreedomsDischarged : Prop
  allUnresolvedFreedomsDischarged_proof :
    allUnresolvedFreedomsDischarged
  calibrationPrior : Prop
  calibrationPrior_proof : calibrationPrior
  transportNeutralOrDischarged : Prop
  transportNeutralOrDischarged_proof :
    transportNeutralOrDischarged
  scaleStatusFixed : Prop
  scaleStatusFixed_proof : scaleStatusFixed

/--
AASC audit for the canonical same-scope closed-root normal form.

The guard fields are inherited from the same-scope predicate and polynomial-law
package: no empirical root import, no extra root selector, no one-anchor import,
quotient/skin control, calibration control, and scale/transport control.
-/
def sameScopeClosedRootNormalFormAASCAudit
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A) :
  ThreeFlavorQuotientNormalFormAASCAudit
    R
    A
    (sameScopeClosedRootAsQuotientNormalFormSyntax R A P) :=
  { normalFormConstructedInternally :=
      P.polynomialLaw.polynomialLawDerivedInternally
    normalFormConstructedInternally_proof :=
      P.polynomialLaw.polynomialLawDerivedInternally_proof
    normalFormUniqueInQuotient :=
      P.sameScopePredicate.rootRealizationExhaustive /\
        P.sameScopePredicate.noExtraRootSelector
    normalFormUniqueInQuotient_proof :=
      ⟨P.sameScopePredicate.rootRealizationExhaustive_proof,
        P.sameScopePredicate.noExtraRootSelector_proof⟩
    quotientFiberExhaustedModuloSkin :=
      P.polynomialLaw.representativeBranchCollapsedModuloSkin
    quotientFiberExhaustedModuloSkin_proof :=
      P.polynomialLaw.representativeBranchCollapsedModuloSkin_proof
    exactnessRelevantRepresentativesControlled :=
      P.polynomialLaw.allUnresolvedFreedomsDischarged
    exactnessRelevantRepresentativesControlled_proof :=
      P.polynomialLaw.allUnresolvedFreedomsDischarged_proof
    notDefinedByGapQuotient :=
      P.polynomialLaw.noOneAnchorImport /\
        P.sameScopePredicate.noExtraRootSelector
    notDefinedByGapQuotient_proof :=
      ⟨P.polynomialLaw.noOneAnchorImport_proof,
        P.sameScopePredicate.noExtraRootSelector_proof⟩
    sameScopeAsStandingRatio :=
      P.sameScopePredicate.rootReadbackLawful
    sameScopeAsStandingRatio_proof :=
      P.sameScopePredicate.rootReadbackLawful_proof
    rootClassCertified :=
      P.sameScopePredicate.rootRealizationSameScope /\
        P.sameScopePredicate.rootReadbackLawful
    rootClassCertified_proof :=
      ⟨P.sameScopePredicate.rootRealizationSameScope_proof,
        P.sameScopePredicate.rootReadbackLawful_proof⟩
    noEmpiricalFitImport :=
      P.polynomialLaw.noEmpiricalFitImport /\
        P.sameScopePredicate.noEmpiricalRootImport
    noEmpiricalFitImport_proof :=
      ⟨P.polynomialLaw.noEmpiricalFitImport_proof,
        P.sameScopePredicate.noEmpiricalRootImport_proof⟩
    noParameterTuning :=
      P.polynomialLaw.calibrationPrior /\
        P.polynomialLaw.transportNeutralOrDischarged /\
          P.polynomialLaw.scaleStatusFixed
    noParameterTuning_proof :=
      ⟨P.polynomialLaw.calibrationPrior_proof,
        P.polynomialLaw.transportNeutralOrDischarged_proof,
        P.polynomialLaw.scaleStatusFixed_proof⟩
    noHiddenRootSelector :=
      P.sameScopePredicate.noExtraRootSelector
    noHiddenRootSelector_proof :=
      P.sameScopePredicate.noExtraRootSelector_proof
    noOneAnchorImport := P.polynomialLaw.noOneAnchorImport
    noOneAnchorImport_proof :=
      P.polynomialLaw.noOneAnchorImport_proof
    allUnresolvedFreedomsDischarged :=
      P.polynomialLaw.allUnresolvedFreedomsDischarged
    allUnresolvedFreedomsDischarged_proof :=
      P.polynomialLaw.allUnresolvedFreedomsDischarged_proof
    calibrationPrior := P.polynomialLaw.calibrationPrior
    calibrationPrior_proof :=
      P.polynomialLaw.calibrationPrior_proof
    transportNeutralOrDischarged :=
      P.polynomialLaw.transportNeutralOrDischarged
    transportNeutralOrDischarged_proof :=
      P.polynomialLaw.transportNeutralOrDischarged_proof
    scaleStatusFixed := P.polynomialLaw.scaleStatusFixed
    scaleStatusFixed_proof :=
      P.polynomialLaw.scaleStatusFixed_proof }

/--
Quotient-normal-form source theorem for the normalized interior coordinate.

This is the preferred AASC-native route after the corpus scan.  It says the
ratio coordinate has a normal form, the normal form has a denotation in `R`,
and the denotation is the three-flavor gap ratio.  The polynomial/root fields
turn that normal form into the shared algebraic coordinate-anchor interface.
-/
structure ThreeFlavorQuotientNormalFormInteriorLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) where
  NormalForm : Type
  normalForm : NormalForm
  denoteNormalForm : NormalForm -> R
  polynomialOfNormalForm : NormalForm -> Polynomial R
  rootOfNormalForm : NormalForm -> R
  root_is_root :
    (polynomialOfNormalForm normalForm).eval
      (rootOfNormalForm normalForm) = 0
  root_eq_denotation :
    rootOfNormalForm normalForm = denoteNormalForm normalForm
  denotation_eq_gapRatio :
    denoteNormalForm normalForm =
      threeFlavorGapRatio A.massSquaredLevelOf
  normalFormConstructedInternally : Prop
  normalFormConstructedInternally_proof :
    normalFormConstructedInternally
  normalFormUniqueInQuotient : Prop
  normalFormUniqueInQuotient_proof :
    normalFormUniqueInQuotient
  quotientFiberExhaustedModuloSkin : Prop
  quotientFiberExhaustedModuloSkin_proof :
    quotientFiberExhaustedModuloSkin
  exactnessRelevantRepresentativesControlled : Prop
  exactnessRelevantRepresentativesControlled_proof :
    exactnessRelevantRepresentativesControlled
  notDefinedByGapQuotient : Prop
  notDefinedByGapQuotient_proof : notDefinedByGapQuotient
  sameScopeAsStandingRatio : Prop
  sameScopeAsStandingRatio_proof : sameScopeAsStandingRatio
  rootClassCertified : Prop
  rootClassCertified_proof : rootClassCertified
  noEmpiricalFitImport : Prop
  noEmpiricalFitImport_proof : noEmpiricalFitImport
  noParameterTuning : Prop
  noParameterTuning_proof : noParameterTuning
  noHiddenRootSelector : Prop
  noHiddenRootSelector_proof : noHiddenRootSelector
  noOneAnchorImport : Prop
  noOneAnchorImport_proof : noOneAnchorImport
  allUnresolvedFreedomsDischarged : Prop
  allUnresolvedFreedomsDischarged_proof :
    allUnresolvedFreedomsDischarged
  calibrationPrior : Prop
  calibrationPrior_proof : calibrationPrior
  transportNeutralOrDischarged : Prop
  transportNeutralOrDischarged_proof :
    transportNeutralOrDischarged
  scaleStatusFixed : Prop
  scaleStatusFixed_proof : scaleStatusFixed

def quotientNormalFormComponentsAsInteriorLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A)
  (D : ThreeFlavorQuotientNormalFormDenotation R A S)
  (U : ThreeFlavorQuotientNormalFormAASCAudit R A S) :
  ThreeFlavorQuotientNormalFormInteriorLaw R A :=
  { NormalForm := S.NormalForm
    normalForm := S.normalForm
    denoteNormalForm := S.denoteNormalForm
    polynomialOfNormalForm := S.polynomialOfNormalForm
    rootOfNormalForm := S.rootOfNormalForm
    root_is_root := S.root_is_root
    root_eq_denotation := S.root_eq_denotation
    denotation_eq_gapRatio := D.denotation_eq_gapRatio
    normalFormConstructedInternally :=
      U.normalFormConstructedInternally
    normalFormConstructedInternally_proof :=
      U.normalFormConstructedInternally_proof
    normalFormUniqueInQuotient :=
      U.normalFormUniqueInQuotient
    normalFormUniqueInQuotient_proof :=
      U.normalFormUniqueInQuotient_proof
    quotientFiberExhaustedModuloSkin :=
      U.quotientFiberExhaustedModuloSkin
    quotientFiberExhaustedModuloSkin_proof :=
      U.quotientFiberExhaustedModuloSkin_proof
    exactnessRelevantRepresentativesControlled :=
      U.exactnessRelevantRepresentativesControlled
    exactnessRelevantRepresentativesControlled_proof :=
      U.exactnessRelevantRepresentativesControlled_proof
    notDefinedByGapQuotient := U.notDefinedByGapQuotient
    notDefinedByGapQuotient_proof :=
      U.notDefinedByGapQuotient_proof
    sameScopeAsStandingRatio := U.sameScopeAsStandingRatio
    sameScopeAsStandingRatio_proof :=
      U.sameScopeAsStandingRatio_proof
    rootClassCertified := U.rootClassCertified
    rootClassCertified_proof := U.rootClassCertified_proof
    noEmpiricalFitImport := U.noEmpiricalFitImport
    noEmpiricalFitImport_proof := U.noEmpiricalFitImport_proof
    noParameterTuning := U.noParameterTuning
    noParameterTuning_proof := U.noParameterTuning_proof
    noHiddenRootSelector := U.noHiddenRootSelector
    noHiddenRootSelector_proof := U.noHiddenRootSelector_proof
    noOneAnchorImport := U.noOneAnchorImport
    noOneAnchorImport_proof := U.noOneAnchorImport_proof
    allUnresolvedFreedomsDischarged :=
      U.allUnresolvedFreedomsDischarged
    allUnresolvedFreedomsDischarged_proof :=
      U.allUnresolvedFreedomsDischarged_proof
    calibrationPrior := U.calibrationPrior
    calibrationPrior_proof := U.calibrationPrior_proof
    transportNeutralOrDischarged := U.transportNeutralOrDischarged
    transportNeutralOrDischarged_proof :=
      U.transportNeutralOrDischarged_proof
    scaleStatusFixed := U.scaleStatusFixed
    scaleStatusFixed_proof := U.scaleStatusFixed_proof }

def quotientNormalFormCriterionComponentsAsInteriorLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A)
  (K : ThreeFlavorQuotientNormalFormDenotationCriterion R A S)
  (U : ThreeFlavorQuotientNormalFormAASCAudit R A S) :
  ThreeFlavorQuotientNormalFormInteriorLaw R A :=
  quotientNormalFormComponentsAsInteriorLaw
    R
    A
    S
    (quotientNormalFormDenotationCriterionAsDenotation R A S K)
    U

def quotientNormalFormInteriorLawAsInternalCoordinateAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw R A) :
  ThreeFlavorInternalCoordinateAnchor R A :=
  { kind := .quotientNormalForm
    Source := Q.NormalForm
    source := Q.normalForm
    polynomial := Q.polynomialOfNormalForm Q.normalForm
    root := Q.rootOfNormalForm Q.normalForm
    root_is_root := Q.root_is_root
    root_eq_gapRatio := by
      exact Q.root_eq_denotation.trans Q.denotation_eq_gapRatio
    sourceConstructsPolynomial := Q.normalFormConstructedInternally
    sourceConstructsPolynomial_proof :=
      Q.normalFormConstructedInternally_proof
    sourceConstructsRoot := Q.normalFormUniqueInQuotient
    sourceConstructsRoot_proof :=
      Q.normalFormUniqueInQuotient_proof
    notDefinedByGapQuotient := Q.notDefinedByGapQuotient
    notDefinedByGapQuotient_proof := Q.notDefinedByGapQuotient_proof
    sameScopeAsStandingRatio := Q.sameScopeAsStandingRatio
    sameScopeAsStandingRatio_proof := Q.sameScopeAsStandingRatio_proof
    rootClassCertified := Q.rootClassCertified
    rootClassCertified_proof := Q.rootClassCertified_proof
    rootUniqueInAdmissibleClass :=
      Q.normalFormUniqueInQuotient /\
        Q.quotientFiberExhaustedModuloSkin /\
          Q.exactnessRelevantRepresentativesControlled
    rootUniqueInAdmissibleClass_proof :=
      ⟨Q.normalFormUniqueInQuotient_proof,
        Q.quotientFiberExhaustedModuloSkin_proof,
        Q.exactnessRelevantRepresentativesControlled_proof⟩
    noEmpiricalFitImport := Q.noEmpiricalFitImport
    noEmpiricalFitImport_proof := Q.noEmpiricalFitImport_proof
    noParameterTuning := Q.noParameterTuning
    noParameterTuning_proof := Q.noParameterTuning_proof
    noHiddenRootSelector := Q.noHiddenRootSelector
    noHiddenRootSelector_proof := Q.noHiddenRootSelector_proof
    noOneAnchorImport := Q.noOneAnchorImport
    noOneAnchorImport_proof := Q.noOneAnchorImport_proof
    representativeBranchCollapsedModuloSkin :=
      Q.quotientFiberExhaustedModuloSkin
    representativeBranchCollapsedModuloSkin_proof :=
      Q.quotientFiberExhaustedModuloSkin_proof
    allUnresolvedFreedomsDischarged :=
      Q.allUnresolvedFreedomsDischarged
    allUnresolvedFreedomsDischarged_proof :=
      Q.allUnresolvedFreedomsDischarged_proof
    calibrationPrior := Q.calibrationPrior
    calibrationPrior_proof := Q.calibrationPrior_proof
    transportNeutralOrDischarged := Q.transportNeutralOrDischarged
    transportNeutralOrDischarged_proof :=
      Q.transportNeutralOrDischarged_proof
    scaleStatusFixed := Q.scaleStatusFixed
    scaleStatusFixed_proof := Q.scaleStatusFixed_proof }

def quotientNormalFormInteriorLawAsCertifiedAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw R A) :
  ThreeFlavorQuotientNormalFormCoordinateAnchor R A :=
  { anchor := quotientNormalFormInteriorLawAsInternalCoordinateAnchor R A Q
    anchorKind_eq := rfl
    sourceFamilyCertified := Q.normalFormConstructedInternally
    sourceFamilyCertified_proof :=
      Q.normalFormConstructedInternally_proof }

noncomputable def quotientNormalFormInteriorLawGivesExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw R A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  AASCNNR9ExactValueFrontier C :=
  sourceCertifiedCoordinateAnchorGivesExactValueFrontier
    R
    A
    (quotientNormalFormInteriorLawAsCertifiedAnchor R A Q)
    J
    hsingle

def quotientNormalFormClosedRootIdentificationAsDenotationCriterion
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A)
  (I : ThreeFlavorQuotientNormalFormClosedRootIdentification R A S P) :
  ThreeFlavorQuotientNormalFormDenotationCriterion R A S :=
  quotientNormalFormSameScopeReadbackAsDenotationCriterion
    R
    A
    S
    P
    (quotientNormalFormClosedRootIdentificationAsRootReadback R A S P I)

def quotientNormalFormClosedRootIdentificationAsInteriorLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A)
  (I : ThreeFlavorQuotientNormalFormClosedRootIdentification R A S P)
  (U : ThreeFlavorQuotientNormalFormAASCAudit R A S) :
  ThreeFlavorQuotientNormalFormInteriorLaw R A :=
  quotientNormalFormCriterionComponentsAsInteriorLaw
    R
    A
    S
    (quotientNormalFormClosedRootIdentificationAsDenotationCriterion R A S P I)
    U

noncomputable def quotientNormalFormClosedRootIdentificationGivesExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (S : ThreeFlavorQuotientNormalFormSyntax R A)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A)
  (I : ThreeFlavorQuotientNormalFormClosedRootIdentification R A S P)
  (U : ThreeFlavorQuotientNormalFormAASCAudit R A S)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  AASCNNR9ExactValueFrontier C :=
  quotientNormalFormInteriorLawGivesExactValueFrontier
    R
    A
    (quotientNormalFormClosedRootIdentificationAsInteriorLaw R A S P I U)
    J
    hsingle

def sameScopeClosedRootNormalFormAsInteriorLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A) :
  ThreeFlavorQuotientNormalFormInteriorLaw R A :=
  quotientNormalFormClosedRootIdentificationAsInteriorLaw
    R
    A
    (sameScopeClosedRootAsQuotientNormalFormSyntax R A P)
    P
    (sameScopeClosedRootNormalFormIdentification R A P)
    (sameScopeClosedRootNormalFormAASCAudit R A P)

noncomputable def sameScopeClosedRootNormalFormGivesExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  AASCNNR9ExactValueFrontier C :=
  quotientNormalFormClosedRootIdentificationGivesExactValueFrontier
    R
    A
    (sameScopeClosedRootAsQuotientNormalFormSyntax R A P)
    P
    (sameScopeClosedRootNormalFormIdentification R A P)
    (sameScopeClosedRootNormalFormAASCAudit R A P)
    J
    hsingle

/--
Algebraic presentation of the internal closed root.

This is the next layer after quotient-normal-form closure.  It gives the
closed root as a distinguished root of an explicit polynomial together with a
selector/isolating predicate that is unique on that polynomial.  It is still
not a decimal value.
-/
structure ThreeFlavorAlgebraicClosedRootPresentation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A) where
  explicitPolynomial : Polynomial R
  selectedRoot : R
  selectedRoot_eq_closedRoot :
    selectedRoot = P.sameScopePredicate.closedRatio
  selectedRoot_is_root :
    explicitPolynomial.eval selectedRoot = 0
  RootSelector : R -> Prop
  selectedRoot_selected : RootSelector selectedRoot
  unique_selected_root :
    forall x : R,
      explicitPolynomial.eval x = 0 ->
        RootSelector x ->
          x = selectedRoot
  polynomialPresentedInternally : Prop
  polynomialPresentedInternally_proof :
    polynomialPresentedInternally
  selectorPresentedInternally : Prop
  selectorPresentedInternally_proof :
    selectorPresentedInternally
  selectorSameScopeAsStandingRatio : Prop
  selectorSameScopeAsStandingRatio_proof :
    selectorSameScopeAsStandingRatio
  noEmpiricalFitImport : Prop
  noEmpiricalFitImport_proof : noEmpiricalFitImport
  noParameterTuning : Prop
  noParameterTuning_proof : noParameterTuning
  noHiddenRootSelector : Prop
  noHiddenRootSelector_proof : noHiddenRootSelector

def sameScopePackageAsAlgebraicClosedRootPresentation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A) :
  ThreeFlavorAlgebraicClosedRootPresentation R A P := by
  let T :=
    sameScopeRootPredicateDefinitionAsPredicateTheorem
      R
      A
      P.sameScopePredicate
  let realization :=
    sameScopeRootPredicateAsRootRealizationTheorem
      R
      A
      T
  let singleton :=
    polynomialRootRealizationAsHybridSingletonRealization
      R
      A
      realization
  let U :=
    rootHybridSingletonRealizationAsUniquenessCertificate
      R
      A
      singleton
      P.branchSingleton
  exact
  { explicitPolynomial := P.sameScopePredicate.polynomial
    selectedRoot := P.sameScopePredicate.closedRatio
    selectedRoot_eq_closedRoot := rfl
    selectedRoot_is_root :=
      P.sameScopePredicate.closedRatio_is_root
    RootSelector :=
      SameScopeHybridRootRealized
        H
        R
        P.sameScopePredicate.valueOfRatio
    selectedRoot_selected :=
      ⟨C.ratio,
        P.sameScopePredicate.currentRatioInMinimalInterval,
        P.sameScopePredicate.currentRatioModular,
        P.sameScopePredicate.currentRatioSpectral,
        P.sameScopePredicate.currentRatioScoto,
        P.sameScopePredicate.currentValue_eq_closed⟩
    unique_selected_root := by
      intro x hx hsel
      exact U.uniqueAdmissibleRoot x hx hsel
    polynomialPresentedInternally :=
      P.polynomialLaw.polynomialLawDerivedInternally
    polynomialPresentedInternally_proof :=
      P.polynomialLaw.polynomialLawDerivedInternally_proof
    selectorPresentedInternally :=
      P.sameScopePredicate.rootRealizationSameScope /\
        P.sameScopePredicate.rootRealizationExhaustive
    selectorPresentedInternally_proof :=
      ⟨P.sameScopePredicate.rootRealizationSameScope_proof,
        P.sameScopePredicate.rootRealizationExhaustive_proof⟩
    selectorSameScopeAsStandingRatio :=
      P.sameScopePredicate.rootReadbackLawful
    selectorSameScopeAsStandingRatio_proof :=
      P.sameScopePredicate.rootReadbackLawful_proof
    noEmpiricalFitImport :=
      P.polynomialLaw.noEmpiricalFitImport /\
        P.sameScopePredicate.noEmpiricalRootImport
    noEmpiricalFitImport_proof :=
      ⟨P.polynomialLaw.noEmpiricalFitImport_proof,
        P.sameScopePredicate.noEmpiricalRootImport_proof⟩
    noParameterTuning :=
      P.polynomialLaw.calibrationPrior /\
        P.polynomialLaw.transportNeutralOrDischarged /\
          P.polynomialLaw.scaleStatusFixed
    noParameterTuning_proof :=
      ⟨P.polynomialLaw.calibrationPrior_proof,
        P.polynomialLaw.transportNeutralOrDischarged_proof,
        P.polynomialLaw.scaleStatusFixed_proof⟩
    noHiddenRootSelector :=
      P.sameScopePredicate.noExtraRootSelector
    noHiddenRootSelector_proof :=
      P.sameScopePredicate.noExtraRootSelector_proof }

theorem algebraicClosedRootPresentation_selectedRoot_eq_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation R A P) :
  G.selectedRoot = threeFlavorGapRatio A.massSquaredLevelOf := by
  exact G.selectedRoot_eq_closedRoot.trans
    (sameScopeNumericalPredictionClosedValue_eq_gapRatio P)

/--
Explicit rational coefficient presentation for the closed-root polynomial.

This is the computational syntax needed before a genuine root-isolation
certificate can be produced.  It does not choose a root and does not import a
decimal; it only states that the abstract same-scope polynomial has been
displayed as a finite rational coefficient list.
-/
structure ThreeFlavorRationalPolynomialCoefficientPresentation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P) where
  coefficientBound : Nat
  coefficientAt : Nat -> ℚ
  polynomial_eq_coefficients :
    G.explicitPolynomial =
      (Finset.range (coefficientBound + 1)).sum
        (fun k => Polynomial.C (coefficientAt k) * Polynomial.X ^ k)
  coefficientsDisplayedInternally : Prop
  coefficientsDisplayedInternally_proof :
    coefficientsDisplayedInternally
  coefficientsSameScope : Prop
  coefficientsSameScope_proof :
    coefficientsSameScope
  noEmpiricalCoefficientImport : Prop
  noEmpiricalCoefficientImport_proof :
    noEmpiricalCoefficientImport
  noCoefficientFitTuning : Prop
  noCoefficientFitTuning_proof :
    noCoefficientFitTuning
  noHiddenRootEncodingInCoefficients : Prop
  noHiddenRootEncodingInCoefficients_proof :
    noHiddenRootEncodingInCoefficients

theorem rationalCoefficientPresentation_selectedRoot_is_root
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (_K : ThreeFlavorRationalPolynomialCoefficientPresentation G) :
  G.explicitPolynomial.eval G.selectedRoot = 0 :=
  G.selectedRoot_is_root

def NeedsThreeFlavorRationalPolynomialCoefficientPresentation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P) : Prop :=
  Not (exists _K : ThreeFlavorRationalPolynomialCoefficientPresentation G, True)

/--
Rational coefficient presentation transported into an ordered root domain.

This is the form needed for algebraic/real root isolation: the coefficients
are rational numerals, while the selected root may live in a larger ordered
field.
-/
structure ThreeFlavorRationalCoefficientPolynomialOver
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation R A P) where
  coefficientBound : Nat
  rationalCoefficientAt : Nat -> ℚ
  polynomial_eq_rational_coefficients :
    G.explicitPolynomial =
      (Finset.range (coefficientBound + 1)).sum
        (fun k =>
          Polynomial.C (algebraMap ℚ R (rationalCoefficientAt k)) *
            Polynomial.X ^ k)
  coefficientsDisplayedInternally : Prop
  coefficientsDisplayedInternally_proof :
    coefficientsDisplayedInternally
  coefficientsSameScope : Prop
  coefficientsSameScope_proof :
    coefficientsSameScope
  noEmpiricalCoefficientImport : Prop
  noEmpiricalCoefficientImport_proof :
    noEmpiricalCoefficientImport
  noCoefficientFitTuning : Prop
  noCoefficientFitTuning_proof :
    noCoefficientFitTuning
  noHiddenRootEncodingInCoefficients : Prop
  noHiddenRootEncodingInCoefficients_proof :
    noHiddenRootEncodingInCoefficients

def NeedsThreeFlavorRationalCoefficientPolynomialOver
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation R A P) : Prop :=
  Not (exists _K : ThreeFlavorRationalCoefficientPolynomialOver R G, True)

/--
Source-derived rational coefficient law for the closed-root polynomial.

This is the new-territory object: it is not merely a display of coefficients.
It records that the coefficient law is produced by a source construction
acting on the standing neutrino ratio target, not by encoding the selected
root or fitting a decimal.
-/
structure ThreeFlavorSourceDerivedRationalCoefficientLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation R A P) where
  coefficientBound : Nat
  rationalCoefficientAt : Nat -> ℚ
  coefficientPolynomial : Polynomial R :=
    (Finset.range (coefficientBound + 1)).sum
      (fun k =>
        Polynomial.C (algebraMap ℚ R (rationalCoefficientAt k)) *
          Polynomial.X ^ k)
  coefficientPolynomial_eq_coefficients :
    coefficientPolynomial =
      (Finset.range (coefficientBound + 1)).sum
        (fun k =>
          Polynomial.C (algebraMap ℚ R (rationalCoefficientAt k)) *
            Polynomial.X ^ k)
  coefficientPolynomial_eq_closedRootPolynomial :
    coefficientPolynomial = G.explicitPolynomial
  selectedRoot_is_coefficientPolynomial_root :
    coefficientPolynomial.eval G.selectedRoot = 0
  sourceConstructsCoefficientLaw : Prop
  sourceConstructsCoefficientLaw_proof :
    sourceConstructsCoefficientLaw
  coefficientLawTargetsStandingRatio : Prop
  coefficientLawTargetsStandingRatio_proof :
    coefficientLawTargetsStandingRatio
  coefficientLawSameScope : Prop
  coefficientLawSameScope_proof :
    coefficientLawSameScope
  coefficientLawQuotientStable : Prop
  coefficientLawQuotientStable_proof :
    coefficientLawQuotientStable
  coefficientLawCalibrationFree : Prop
  coefficientLawCalibrationFree_proof :
    coefficientLawCalibrationFree
  coefficientLawNotClosedRootLinearPackaging : Prop
  coefficientLawNotClosedRootLinearPackaging_proof :
    coefficientLawNotClosedRootLinearPackaging
  noEmpiricalCoefficientImport : Prop
  noEmpiricalCoefficientImport_proof :
    noEmpiricalCoefficientImport
  noCoefficientFitTuning : Prop
  noCoefficientFitTuning_proof :
    noCoefficientFitTuning
  noHiddenRootEncodingInCoefficients : Prop
  noHiddenRootEncodingInCoefficients_proof :
    noHiddenRootEncodingInCoefficients

def sourceDerivedRationalCoefficientLawAsPolynomialOver
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (L : ThreeFlavorSourceDerivedRationalCoefficientLaw R G) :
  ThreeFlavorRationalCoefficientPolynomialOver R G :=
  { coefficientBound := L.coefficientBound
    rationalCoefficientAt := L.rationalCoefficientAt
    polynomial_eq_rational_coefficients := by
      calc
        G.explicitPolynomial = L.coefficientPolynomial :=
          L.coefficientPolynomial_eq_closedRootPolynomial.symm
        _ =
            (Finset.range (L.coefficientBound + 1)).sum
              (fun k =>
                Polynomial.C (algebraMap ℚ R (L.rationalCoefficientAt k)) *
                  Polynomial.X ^ k) :=
          L.coefficientPolynomial_eq_coefficients
    coefficientsDisplayedInternally :=
      L.sourceConstructsCoefficientLaw
    coefficientsDisplayedInternally_proof :=
      L.sourceConstructsCoefficientLaw_proof
    coefficientsSameScope :=
      L.coefficientLawTargetsStandingRatio /\
        L.coefficientLawSameScope /\
          L.coefficientLawQuotientStable
    coefficientsSameScope_proof :=
      ⟨L.coefficientLawTargetsStandingRatio_proof,
        L.coefficientLawSameScope_proof,
        L.coefficientLawQuotientStable_proof⟩
    noEmpiricalCoefficientImport :=
      L.coefficientLawCalibrationFree /\
        L.noEmpiricalCoefficientImport
    noEmpiricalCoefficientImport_proof :=
      ⟨L.coefficientLawCalibrationFree_proof,
        L.noEmpiricalCoefficientImport_proof⟩
    noCoefficientFitTuning :=
      L.noCoefficientFitTuning /\
        L.coefficientLawNotClosedRootLinearPackaging
    noCoefficientFitTuning_proof :=
      ⟨L.noCoefficientFitTuning_proof,
        L.coefficientLawNotClosedRootLinearPackaging_proof⟩
    noHiddenRootEncodingInCoefficients :=
      L.noHiddenRootEncodingInCoefficients /\
        L.coefficientLawNotClosedRootLinearPackaging
    noHiddenRootEncodingInCoefficients_proof :=
      ⟨L.noHiddenRootEncodingInCoefficients_proof,
        L.coefficientLawNotClosedRootLinearPackaging_proof⟩ }

theorem sourceDerivedRationalCoefficientLaw_selectedRoot_is_root
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (L : ThreeFlavorSourceDerivedRationalCoefficientLaw R G) :
  L.coefficientPolynomial.eval G.selectedRoot = 0 :=
  L.selectedRoot_is_coefficientPolynomial_root

def NeedsThreeFlavorSourceDerivedRationalCoefficientLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation R A P) : Prop :=
  Not (exists _L :
    ThreeFlavorSourceDerivedRationalCoefficientLaw R G, True)

/--
Syntactic part of a source-derived coefficient law.

This is just the finite rational coefficient expression and its equality with
the closed-root polynomial.  The root theorem and admissibility audit are kept
separate so the construction can be attacked in smaller pieces.
-/
structure ThreeFlavorSourceCoefficientSyntax
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation R A P) where
  coefficientBound : Nat
  rationalCoefficientAt : Nat -> ℚ
  coefficientPolynomial : Polynomial R :=
    (Finset.range (coefficientBound + 1)).sum
      (fun k =>
        Polynomial.C (algebraMap ℚ R (rationalCoefficientAt k)) *
          Polynomial.X ^ k)
  coefficientPolynomial_eq_coefficients :
    coefficientPolynomial =
      (Finset.range (coefficientBound + 1)).sum
        (fun k =>
          Polynomial.C (algebraMap ℚ R (rationalCoefficientAt k)) *
            Polynomial.X ^ k)
  coefficientPolynomial_eq_closedRootPolynomial :
    coefficientPolynomial = G.explicitPolynomial

/-- The selected closed root satisfies the coefficient syntax. -/
structure ThreeFlavorSourceCoefficientRootCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (S : ThreeFlavorSourceCoefficientSyntax R G) where
  selectedRoot_is_coefficientPolynomial_root :
    S.coefficientPolynomial.eval G.selectedRoot = 0

def sourceCoefficientSyntaxAsRootCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (S : ThreeFlavorSourceCoefficientSyntax R G) :
  ThreeFlavorSourceCoefficientRootCertificate S :=
  { selectedRoot_is_coefficientPolynomial_root := by
      rw [S.coefficientPolynomial_eq_closedRootPolynomial]
      exact G.selectedRoot_is_root }

/-- AASC audit part of a source-derived coefficient law. -/
structure ThreeFlavorSourceCoefficientLawAudit where
  sourceConstructsCoefficientLaw : Prop
  sourceConstructsCoefficientLaw_proof :
    sourceConstructsCoefficientLaw
  coefficientLawTargetsStandingRatio : Prop
  coefficientLawTargetsStandingRatio_proof :
    coefficientLawTargetsStandingRatio
  coefficientLawSameScope : Prop
  coefficientLawSameScope_proof :
    coefficientLawSameScope
  coefficientLawQuotientStable : Prop
  coefficientLawQuotientStable_proof :
    coefficientLawQuotientStable
  coefficientLawCalibrationFree : Prop
  coefficientLawCalibrationFree_proof :
    coefficientLawCalibrationFree
  coefficientLawNotClosedRootLinearPackaging : Prop
  coefficientLawNotClosedRootLinearPackaging_proof :
    coefficientLawNotClosedRootLinearPackaging
  noEmpiricalCoefficientImport : Prop
  noEmpiricalCoefficientImport_proof :
    noEmpiricalCoefficientImport
  noCoefficientFitTuning : Prop
  noCoefficientFitTuning_proof :
    noCoefficientFitTuning
  noHiddenRootEncodingInCoefficients : Prop
  noHiddenRootEncodingInCoefficients_proof :
    noHiddenRootEncodingInCoefficients

/--
Focused audit that blocks the forbidden closed-root linear packaging.

This is the key non-tautology gate for numerical readout.  A coefficient table
may display any polynomial; this object certifies that the displayed polynomial
is not merely `X - C selectedRoot`, and that its coefficients do not smuggle
the selected root back into the readout.
-/
structure ThreeFlavorCoefficientNonTautologyAudit
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (_S : ThreeFlavorSourceCoefficientSyntax R G) where
  notClosedRootLinearPackaging : Prop
  notClosedRootLinearPackaging_proof :
    notClosedRootLinearPackaging
  coefficientsDoNotEncodeSelectedRoot : Prop
  coefficientsDoNotEncodeSelectedRoot_proof :
    coefficientsDoNotEncodeSelectedRoot
  noOneAnchorCoefficientImport : Prop
  noOneAnchorCoefficientImport_proof :
    noOneAnchorCoefficientImport

/--
Positive source audit for a coefficient table, separated from non-tautology.
-/
structure ThreeFlavorCoefficientPositiveSourceAudit where
  sourceConstructsCoefficientLaw : Prop
  sourceConstructsCoefficientLaw_proof :
    sourceConstructsCoefficientLaw
  coefficientLawTargetsStandingRatio : Prop
  coefficientLawTargetsStandingRatio_proof :
    coefficientLawTargetsStandingRatio
  coefficientLawSameScope : Prop
  coefficientLawSameScope_proof :
    coefficientLawSameScope
  coefficientLawQuotientStable : Prop
  coefficientLawQuotientStable_proof :
    coefficientLawQuotientStable
  coefficientLawCalibrationFree : Prop
  coefficientLawCalibrationFree_proof :
    coefficientLawCalibrationFree
  noEmpiricalCoefficientImport : Prop
  noEmpiricalCoefficientImport_proof :
    noEmpiricalCoefficientImport
  noCoefficientFitTuning : Prop
  noCoefficientFitTuning_proof :
    noCoefficientFitTuning

/--
Canonical positive source audit supplied by a same-scope numerical-prediction
package.

This removes one generic input from the canonical readout path: the package
already carries the internality, same-scope, quotient-stability,
calibration/no-fit, and no-empirical-import audits needed for the coefficient
law route.
-/
def sameScopePackageAsCoefficientPositiveSourceAudit
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A) :
  ThreeFlavorCoefficientPositiveSourceAudit :=
  { sourceConstructsCoefficientLaw :=
      P.polynomialLaw.polynomialLawDerivedInternally
    sourceConstructsCoefficientLaw_proof :=
      P.polynomialLaw.polynomialLawDerivedInternally_proof
    coefficientLawTargetsStandingRatio :=
      P.sameScopePredicate.rootReadbackLawful
    coefficientLawTargetsStandingRatio_proof :=
      P.sameScopePredicate.rootReadbackLawful_proof
    coefficientLawSameScope :=
      P.sameScopePredicate.rootRealizationSameScope
    coefficientLawSameScope_proof :=
      P.sameScopePredicate.rootRealizationSameScope_proof
    coefficientLawQuotientStable :=
      P.polynomialLaw.representativeBranchCollapsedModuloSkin
    coefficientLawQuotientStable_proof :=
      P.polynomialLaw.representativeBranchCollapsedModuloSkin_proof
    coefficientLawCalibrationFree :=
      P.polynomialLaw.calibrationPrior /\
        P.polynomialLaw.transportNeutralOrDischarged /\
          P.polynomialLaw.scaleStatusFixed
    coefficientLawCalibrationFree_proof :=
      ⟨P.polynomialLaw.calibrationPrior_proof,
        P.polynomialLaw.transportNeutralOrDischarged_proof,
        P.polynomialLaw.scaleStatusFixed_proof⟩
    noEmpiricalCoefficientImport :=
      P.polynomialLaw.noEmpiricalFitImport /\
        P.sameScopePredicate.noEmpiricalRootImport
    noEmpiricalCoefficientImport_proof :=
      ⟨P.polynomialLaw.noEmpiricalFitImport_proof,
        P.sameScopePredicate.noEmpiricalRootImport_proof⟩
    noCoefficientFitTuning :=
      P.polynomialLaw.noOneAnchorImport /\
        P.polynomialLaw.allUnresolvedFreedomsDischarged
    noCoefficientFitTuning_proof :=
      ⟨P.polynomialLaw.noOneAnchorImport_proof,
        P.polynomialLaw.allUnresolvedFreedomsDischarged_proof⟩ }

/--
A checkable sufficient criterion for the first non-tautology gate.  If the
source coefficient polynomial is not degree one, then it cannot merely be the
linear closed-root wrapper `X - C selectedRoot`.

The remaining two fields are still source-audit obligations: degree alone does
not prove that the coefficients are not imported from an anchor or encoded from
the selected root by another route.
-/
structure ThreeFlavorCoefficientDegreeNonlinearCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (S : ThreeFlavorSourceCoefficientSyntax R G) where
  natDegree_ne_one :
    S.coefficientPolynomial.natDegree ≠ 1
  coefficientsDoNotEncodeSelectedRoot : Prop
  coefficientsDoNotEncodeSelectedRoot_proof :
    coefficientsDoNotEncodeSelectedRoot
  noOneAnchorCoefficientImport : Prop
  noOneAnchorCoefficientImport_proof :
    noOneAnchorCoefficientImport

/--
Coefficient-level sufficient criterion for degree nonlinearity.  Instead of
asking for `natDegree != 1` directly, it is enough to exhibit a nonzero
coefficient in degree at least two.
-/
structure ThreeFlavorHighCoefficientNonlinearCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (S : ThreeFlavorSourceCoefficientSyntax R G) where
  witnessDegree : ℕ
  witnessDegree_ge_two :
    2 ≤ witnessDegree
  witnessCoefficient_ne_zero :
    S.coefficientPolynomial.coeff witnessDegree ≠ 0
  coefficientsDoNotEncodeSelectedRoot : Prop
  coefficientsDoNotEncodeSelectedRoot_proof :
    coefficientsDoNotEncodeSelectedRoot
  noOneAnchorCoefficientImport : Prop
  noOneAnchorCoefficientImport_proof :
    noOneAnchorCoefficientImport

/--
A nonzero coefficient in degree at least two proves the polynomial is not
degree one, hence gives the degree-nonlinear certificate.
-/
def highCoefficientAsDegreeNonlinearCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  {S : ThreeFlavorSourceCoefficientSyntax R G}
  (K : ThreeFlavorHighCoefficientNonlinearCertificate S) :
  ThreeFlavorCoefficientDegreeNonlinearCertificate S :=
  { natDegree_ne_one := by
      intro hdeg
      have hle :
          K.witnessDegree ≤ S.coefficientPolynomial.natDegree :=
        Polynomial.le_natDegree_of_ne_zero K.witnessCoefficient_ne_zero
      rw [hdeg] at hle
      have hge : 2 ≤ K.witnessDegree :=
        K.witnessDegree_ge_two
      omega
    coefficientsDoNotEncodeSelectedRoot :=
      K.coefficientsDoNotEncodeSelectedRoot
    coefficientsDoNotEncodeSelectedRoot_proof :=
      K.coefficientsDoNotEncodeSelectedRoot_proof
    noOneAnchorCoefficientImport :=
      K.noOneAnchorCoefficientImport
    noOneAnchorCoefficientImport_proof :=
      K.noOneAnchorCoefficientImport_proof }

/--
Turns the degree-based certificate into the general non-tautology audit.  The
proof uses mathlib's theorem that every polynomial of the form `X - C a` has
natural degree one over a field.
-/
def coefficientDegreeNonlinearAsNonTautologyAudit
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  {S : ThreeFlavorSourceCoefficientSyntax R G}
  (D : ThreeFlavorCoefficientDegreeNonlinearCertificate S) :
  ThreeFlavorCoefficientNonTautologyAudit S :=
  { notClosedRootLinearPackaging :=
      S.coefficientPolynomial ≠
        (Polynomial.X - Polynomial.C G.selectedRoot : Polynomial R)
    notClosedRootLinearPackaging_proof := by
      intro h
      have hdeg :
          S.coefficientPolynomial.natDegree =
            (Polynomial.X - Polynomial.C G.selectedRoot : Polynomial R).natDegree := by
        exact congrArg Polynomial.natDegree h
      have hlin :
          (Polynomial.X - Polynomial.C G.selectedRoot : Polynomial R).natDegree = 1 :=
        Polynomial.natDegree_X_sub_C G.selectedRoot
      rw [hlin] at hdeg
      exact D.natDegree_ne_one hdeg
    coefficientsDoNotEncodeSelectedRoot :=
      D.coefficientsDoNotEncodeSelectedRoot
    coefficientsDoNotEncodeSelectedRoot_proof :=
      D.coefficientsDoNotEncodeSelectedRoot_proof
    noOneAnchorCoefficientImport :=
      D.noOneAnchorCoefficientImport
    noOneAnchorCoefficientImport_proof :=
      D.noOneAnchorCoefficientImport_proof }

def NeedsThreeFlavorCoefficientNonTautologyAudit
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (S : ThreeFlavorSourceCoefficientSyntax R G) : Prop :=
  Not (exists _N : ThreeFlavorCoefficientNonTautologyAudit S, True)

theorem coefficientDegreeNonlinear_discharge_nonTautologyNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  {S : ThreeFlavorSourceCoefficientSyntax R G}
  (D : ThreeFlavorCoefficientDegreeNonlinearCertificate S) :
  Not (NeedsThreeFlavorCoefficientNonTautologyAudit S) := by
  intro hneed
  exact hneed ⟨coefficientDegreeNonlinearAsNonTautologyAudit D, True.intro⟩

def coefficientPositiveAndNonTautologyAsLawAudit
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  {S : ThreeFlavorSourceCoefficientSyntax R G}
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (N : ThreeFlavorCoefficientNonTautologyAudit S) :
  ThreeFlavorSourceCoefficientLawAudit :=
  { sourceConstructsCoefficientLaw :=
      Psrc.sourceConstructsCoefficientLaw
    sourceConstructsCoefficientLaw_proof :=
      Psrc.sourceConstructsCoefficientLaw_proof
    coefficientLawTargetsStandingRatio :=
      Psrc.coefficientLawTargetsStandingRatio
    coefficientLawTargetsStandingRatio_proof :=
      Psrc.coefficientLawTargetsStandingRatio_proof
    coefficientLawSameScope := Psrc.coefficientLawSameScope
    coefficientLawSameScope_proof :=
      Psrc.coefficientLawSameScope_proof
    coefficientLawQuotientStable :=
      Psrc.coefficientLawQuotientStable
    coefficientLawQuotientStable_proof :=
      Psrc.coefficientLawQuotientStable_proof
    coefficientLawCalibrationFree :=
      Psrc.coefficientLawCalibrationFree
    coefficientLawCalibrationFree_proof :=
      Psrc.coefficientLawCalibrationFree_proof
    coefficientLawNotClosedRootLinearPackaging :=
      N.notClosedRootLinearPackaging
    coefficientLawNotClosedRootLinearPackaging_proof :=
      N.notClosedRootLinearPackaging_proof
    noEmpiricalCoefficientImport :=
      Psrc.noEmpiricalCoefficientImport /\
        N.noOneAnchorCoefficientImport
    noEmpiricalCoefficientImport_proof :=
      ⟨Psrc.noEmpiricalCoefficientImport_proof,
        N.noOneAnchorCoefficientImport_proof⟩
    noCoefficientFitTuning := Psrc.noCoefficientFitTuning
    noCoefficientFitTuning_proof :=
      Psrc.noCoefficientFitTuning_proof
    noHiddenRootEncodingInCoefficients :=
      N.coefficientsDoNotEncodeSelectedRoot /\
        N.notClosedRootLinearPackaging
    noHiddenRootEncodingInCoefficients_proof :=
      ⟨N.coefficientsDoNotEncodeSelectedRoot_proof,
        N.notClosedRootLinearPackaging_proof⟩ }

def sourceCoefficientComponentsAsRationalCoefficientLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (S : ThreeFlavorSourceCoefficientSyntax R G)
  (K : ThreeFlavorSourceCoefficientRootCertificate S)
  (Q : ThreeFlavorSourceCoefficientLawAudit) :
  ThreeFlavorSourceDerivedRationalCoefficientLaw R G :=
  { coefficientBound := S.coefficientBound
    rationalCoefficientAt := S.rationalCoefficientAt
    coefficientPolynomial := S.coefficientPolynomial
    coefficientPolynomial_eq_coefficients :=
      S.coefficientPolynomial_eq_coefficients
    coefficientPolynomial_eq_closedRootPolynomial :=
      S.coefficientPolynomial_eq_closedRootPolynomial
    selectedRoot_is_coefficientPolynomial_root :=
      K.selectedRoot_is_coefficientPolynomial_root
    sourceConstructsCoefficientLaw :=
      Q.sourceConstructsCoefficientLaw
    sourceConstructsCoefficientLaw_proof :=
      Q.sourceConstructsCoefficientLaw_proof
    coefficientLawTargetsStandingRatio :=
      Q.coefficientLawTargetsStandingRatio
    coefficientLawTargetsStandingRatio_proof :=
      Q.coefficientLawTargetsStandingRatio_proof
    coefficientLawSameScope := Q.coefficientLawSameScope
    coefficientLawSameScope_proof :=
      Q.coefficientLawSameScope_proof
    coefficientLawQuotientStable :=
      Q.coefficientLawQuotientStable
    coefficientLawQuotientStable_proof :=
      Q.coefficientLawQuotientStable_proof
    coefficientLawCalibrationFree :=
      Q.coefficientLawCalibrationFree
    coefficientLawCalibrationFree_proof :=
      Q.coefficientLawCalibrationFree_proof
    coefficientLawNotClosedRootLinearPackaging :=
      Q.coefficientLawNotClosedRootLinearPackaging
    coefficientLawNotClosedRootLinearPackaging_proof :=
      Q.coefficientLawNotClosedRootLinearPackaging_proof
    noEmpiricalCoefficientImport :=
      Q.noEmpiricalCoefficientImport
    noEmpiricalCoefficientImport_proof :=
      Q.noEmpiricalCoefficientImport_proof
    noCoefficientFitTuning := Q.noCoefficientFitTuning
    noCoefficientFitTuning_proof :=
      Q.noCoefficientFitTuning_proof
    noHiddenRootEncodingInCoefficients :=
      Q.noHiddenRootEncodingInCoefficients
    noHiddenRootEncodingInCoefficients_proof :=
      Q.noHiddenRootEncodingInCoefficients_proof }

def sourceCoefficientSyntaxAndAuditAsRationalCoefficientLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (S : ThreeFlavorSourceCoefficientSyntax R G)
  (Q : ThreeFlavorSourceCoefficientLawAudit) :
  ThreeFlavorSourceDerivedRationalCoefficientLaw R G :=
  sourceCoefficientComponentsAsRationalCoefficientLaw
    S
    (sourceCoefficientSyntaxAsRootCertificate S)
    Q

def NeedsThreeFlavorSourceCoefficientSyntax
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation R A P) : Prop :=
  Not (exists _S : ThreeFlavorSourceCoefficientSyntax R G, True)

/--
Extensional coefficient table for the source polynomial.

This is often the most practical way to construct
`ThreeFlavorSourceCoefficientSyntax`: give rational coefficients and prove,
coefficient-by-coefficient, that their polynomial is the closed-root
polynomial.
-/
structure ThreeFlavorSourceCoefficientExtensionalTable
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation R A P) where
  coefficientBound : Nat
  rationalCoefficientAt : Nat -> ℚ
  coefficient_extensionality :
    forall n : Nat,
      ((Finset.range (coefficientBound + 1)).sum
        (fun k =>
          Polynomial.C (algebraMap ℚ R (rationalCoefficientAt k)) *
            Polynomial.X ^ k)).coeff n =
        G.explicitPolynomial.coeff n
  coefficientTableSourceDerived : Prop
  coefficientTableSourceDerived_proof :
    coefficientTableSourceDerived

noncomputable def sourceCoefficientExtensionalTableAsSyntax
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (T : ThreeFlavorSourceCoefficientExtensionalTable R G) :
  ThreeFlavorSourceCoefficientSyntax R G :=
  { coefficientBound := T.coefficientBound
    rationalCoefficientAt := T.rationalCoefficientAt
    coefficientPolynomial :=
      (Finset.range (T.coefficientBound + 1)).sum
        (fun k =>
          Polynomial.C (algebraMap ℚ R (T.rationalCoefficientAt k)) *
            Polynomial.X ^ k)
    coefficientPolynomial_eq_coefficients := rfl
    coefficientPolynomial_eq_closedRootPolynomial := by
      apply Polynomial.ext
      intro n
      exact T.coefficient_extensionality n }

theorem sourceCoefficientExtensionalTable_discharge_syntax_need
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (T : ThreeFlavorSourceCoefficientExtensionalTable R G) :
  Not (NeedsThreeFlavorSourceCoefficientSyntax R G) := by
  intro hneed
  exact hneed ⟨sourceCoefficientExtensionalTableAsSyntax T, True.intro⟩

noncomputable def rationalClosedRootPolynomialAsCoefficientTable
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P) :
  ThreeFlavorSourceCoefficientExtensionalTable ℚ G :=
  { coefficientBound := G.explicitPolynomial.natDegree
    rationalCoefficientAt := fun n => G.explicitPolynomial.coeff n
    coefficient_extensionality := by
      intro n
      have hpoly :
          (Finset.range (G.explicitPolynomial.natDegree + 1)).sum
              (fun k =>
                Polynomial.C
                    (algebraMap ℚ ℚ (G.explicitPolynomial.coeff k)) *
                  Polynomial.X ^ k) =
            G.explicitPolynomial := by
        simpa using
          (G.explicitPolynomial.as_sum_range_C_mul_X_pow).symm
      exact congrArg (fun p : Polynomial ℚ => p.coeff n) hpoly
    coefficientTableSourceDerived :=
      G.polynomialPresentedInternally
    coefficientTableSourceDerived_proof :=
      G.polynomialPresentedInternally_proof }

noncomputable def rationalClosedRootPolynomialAsCoefficientSyntax
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P) :
  ThreeFlavorSourceCoefficientSyntax ℚ G :=
  sourceCoefficientExtensionalTableAsSyntax
    (rationalClosedRootPolynomialAsCoefficientTable G)

theorem rationalClosedRootPolynomial_discharge_syntax_need
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P) :
  Not (NeedsThreeFlavorSourceCoefficientSyntax ℚ G) :=
  sourceCoefficientExtensionalTable_discharge_syntax_need
    (rationalClosedRootPolynomialAsCoefficientTable G)

noncomputable def sourceCoefficientTableAndAuditAsRationalCoefficientLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (T : ThreeFlavorSourceCoefficientExtensionalTable R G)
  (Q : ThreeFlavorSourceCoefficientLawAudit) :
  ThreeFlavorSourceDerivedRationalCoefficientLaw R G :=
  sourceCoefficientSyntaxAndAuditAsRationalCoefficientLaw
    (sourceCoefficientExtensionalTableAsSyntax T)
    Q

noncomputable def sourceCoefficientTableAuditsAsRationalCoefficientLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (T : ThreeFlavorSourceCoefficientExtensionalTable R G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (N :
    ThreeFlavorCoefficientNonTautologyAudit
      (sourceCoefficientExtensionalTableAsSyntax T)) :
  ThreeFlavorSourceDerivedRationalCoefficientLaw R G :=
  sourceCoefficientTableAndAuditAsRationalCoefficientLaw
    T
    (coefficientPositiveAndNonTautologyAsLawAudit Psrc N)

/--
One-step constructor for the most useful non-tautological coefficient-law
route now available: a source coefficient table, a positive AASC source audit,
and a degree-nonlinearity certificate for that table's polynomial.
-/
noncomputable def sourceCoefficientTablePositiveDegreeAsRationalCoefficientLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (T : ThreeFlavorSourceCoefficientExtensionalTable R G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (D :
    ThreeFlavorCoefficientDegreeNonlinearCertificate
      (sourceCoefficientExtensionalTableAsSyntax T)) :
  ThreeFlavorSourceDerivedRationalCoefficientLaw R G :=
  sourceCoefficientTableAuditsAsRationalCoefficientLaw
    T
    Psrc
    (coefficientDegreeNonlinearAsNonTautologyAudit D)

/--
Coefficient-level constructor: a table, positive source audit, and one nonzero
coefficient in degree at least two are enough to assemble the full
source-derived rational coefficient law.
-/
noncomputable def sourceCoefficientTableHighCoefficientAsRationalCoefficientLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (T : ThreeFlavorSourceCoefficientExtensionalTable R G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (K :
    ThreeFlavorHighCoefficientNonlinearCertificate
      (sourceCoefficientExtensionalTableAsSyntax T)) :
  ThreeFlavorSourceDerivedRationalCoefficientLaw R G :=
  sourceCoefficientTablePositiveDegreeAsRationalCoefficientLaw
    T
    Psrc
    (highCoefficientAsDegreeNonlinearCertificate K)

theorem sourceCoefficientTableAndAudit_discharge_coefficientLawNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (T : ThreeFlavorSourceCoefficientExtensionalTable R G)
  (Q : ThreeFlavorSourceCoefficientLawAudit) :
  Not (NeedsThreeFlavorSourceDerivedRationalCoefficientLaw R G) := by
  intro hneed
  exact hneed
    ⟨sourceCoefficientTableAndAuditAsRationalCoefficientLaw T Q, True.intro⟩

theorem sourceCoefficientTablePositiveDegree_discharge_coefficientLawNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (T : ThreeFlavorSourceCoefficientExtensionalTable R G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (D :
    ThreeFlavorCoefficientDegreeNonlinearCertificate
      (sourceCoefficientExtensionalTableAsSyntax T)) :
  Not (NeedsThreeFlavorSourceDerivedRationalCoefficientLaw R G) := by
  intro hneed
  exact hneed
    ⟨sourceCoefficientTablePositiveDegreeAsRationalCoefficientLaw T Psrc D,
      True.intro⟩

theorem sourceCoefficientTableHighCoefficient_discharge_coefficientLawNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (T : ThreeFlavorSourceCoefficientExtensionalTable R G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (K :
    ThreeFlavorHighCoefficientNonlinearCertificate
      (sourceCoefficientExtensionalTableAsSyntax T)) :
  Not (NeedsThreeFlavorSourceDerivedRationalCoefficientLaw R G) := by
  intro hneed
  exact hneed
    ⟨sourceCoefficientTableHighCoefficientAsRationalCoefficientLaw T Psrc K,
      True.intro⟩

/--
Certified isolating interval for the algebraic closed root.

This is the first genuinely numerical layer.  It does not compute a decimal;
it says that the selected algebraic root lies in a certified ordered interval,
that the interval has a controlled width, and that no other selected root of
the explicit polynomial lies in that interval.
-/
structure ThreeFlavorClosedRootIsolatingInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [LinearOrder R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation R A P) where
  lower : R
  upper : R
  tolerance : R
  lower_lt_upper : lower < upper
  tolerance_pos : 0 < tolerance
  selectedRoot_mem :
    lower <= G.selectedRoot /\ G.selectedRoot <= upper
  width_le_tolerance : upper - lower <= tolerance
  interval_unique_selected_root :
    forall x : R,
      G.explicitPolynomial.eval x = 0 ->
        G.RootSelector x ->
          lower <= x ->
            x <= upper ->
              x = G.selectedRoot
  intervalConstructedInternally : Prop
  intervalConstructedInternally_proof :
    intervalConstructedInternally
  noEmpiricalDecimalImport : Prop
  noEmpiricalDecimalImport_proof :
    noEmpiricalDecimalImport
  noDecimalFitTuning : Prop
  noDecimalFitTuning_proof : noDecimalFitTuning

theorem isolatingInterval_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (I : ThreeFlavorClosedRootIsolatingInterval R G) :
  I.lower <= threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <= I.upper := by
  have hroot :
      G.selectedRoot = threeFlavorGapRatio A.massSquaredLevelOf :=
    algebraicClosedRootPresentation_selectedRoot_eq_gapRatio G
  exact
    ⟨by simpa [hroot] using I.selectedRoot_mem.1,
      by simpa [hroot] using I.selectedRoot_mem.2⟩

/--
Decimal-window certificate for the algebraic closed root.

The human-readable `decimalLabel` is only presentation metadata.  The actual
mathematical content is the certified interval and its tolerance bound.
-/
structure ThreeFlavorClosedRootDecimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [LinearOrder R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation R A P) where
  interval :
    ThreeFlavorClosedRootIsolatingInterval R G
  decimalLabel : String
  decimalLabelCertifiedByInterval : Prop
  decimalLabelCertifiedByInterval_proof :
    decimalLabelCertifiedByInterval

theorem decimalWindow_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (D : ThreeFlavorClosedRootDecimalWindow R G) :
  D.interval.lower <= threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <= D.interval.upper :=
  isolatingInterval_contains_gapRatio D.interval

/--
Arbitrary-precision isolating interval scheme for the algebraic closed root.

This is stronger than a single decimal window: for every positive tolerance it
constructs a certified isolating interval whose width is bounded by that
tolerance.
-/
structure ThreeFlavorClosedRootApproximationScheme
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [LinearOrder R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation R A P) where
  intervalFor :
    forall eps : R,
      0 < eps ->
        ThreeFlavorClosedRootIsolatingInterval R G
  interval_tolerance_le :
    forall (eps : R) (heps : 0 < eps),
      (intervalFor eps heps).tolerance <= eps
  schemeConstructedInternally : Prop
  schemeConstructedInternally_proof :
    schemeConstructedInternally
  noEmpiricalApproximationImport : Prop
  noEmpiricalApproximationImport_proof :
    noEmpiricalApproximationImport
  noApproximationFitTuning : Prop
  noApproximationFitTuning_proof :
    noApproximationFitTuning

theorem approximationScheme_interval_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (S : ThreeFlavorClosedRootApproximationScheme R G)
  (eps : R)
  (heps : 0 < eps) :
  (S.intervalFor eps heps).lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (S.intervalFor eps heps).upper :=
  isolatingInterval_contains_gapRatio (S.intervalFor eps heps)

theorem approximationScheme_width_le_requested
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (S : ThreeFlavorClosedRootApproximationScheme R G)
  (eps : R)
  (heps : 0 < eps) :
  (S.intervalFor eps heps).upper -
      (S.intervalFor eps heps).lower <= eps := by
  exact le_trans
    (S.intervalFor eps heps).width_le_tolerance
    (S.interval_tolerance_le eps heps)

/--
Decimal-readout readiness: an algebraic presentation together with an
arbitrary-precision isolating interval scheme.

This is the formal point at which decimal computation is licensed.  The
result is still a certificate family, not a hard-coded decimal.
-/
structure ThreeFlavorClosedRootDecimalReadoutReady
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [LinearOrder R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H R A) where
  algebraicPresentation :
    ThreeFlavorAlgebraicClosedRootPresentation R A P
  approximationScheme :
    ThreeFlavorClosedRootApproximationScheme R algebraicPresentation

/--
Certified rational root-isolation method for the same-scope closed root.

This is the concrete computational-domain target for decimal readout.  The
coefficient domain is `ℚ`; every interval endpoint and tolerance is rational.
The method is proof-carrying: it must certify that each interval isolates the
selected algebraic root and has width bounded by the requested rational
tolerance.
-/
structure ThreeFlavorRationalClosedRootIsolationMethod
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  algebraicPresentation :
    ThreeFlavorAlgebraicClosedRootPresentation ℚ A P :=
      sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P
  intervalFor :
    forall eps : ℚ,
      0 < eps ->
        ThreeFlavorClosedRootIsolatingInterval ℚ algebraicPresentation
  interval_tolerance_le :
    forall (eps : ℚ) (heps : 0 < eps),
      (intervalFor eps heps).tolerance <= eps
  methodConstructedInternally : Prop
  methodConstructedInternally_proof :
    methodConstructedInternally
  rationalEndpointsCertified : Prop
  rationalEndpointsCertified_proof :
    rationalEndpointsCertified
  noEmpiricalApproximationImport : Prop
  noEmpiricalApproximationImport_proof :
    noEmpiricalApproximationImport
  noApproximationFitTuning : Prop
  noApproximationFitTuning_proof :
    noApproximationFitTuning

def rationalClosedRootIsolationMethodAsApproximationScheme
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorRationalClosedRootIsolationMethod A P) :
  ThreeFlavorClosedRootApproximationScheme
    ℚ
    K.algebraicPresentation :=
  { intervalFor := K.intervalFor
    interval_tolerance_le := K.interval_tolerance_le
    schemeConstructedInternally :=
      K.methodConstructedInternally /\ K.rationalEndpointsCertified
    schemeConstructedInternally_proof :=
      ⟨K.methodConstructedInternally_proof,
        K.rationalEndpointsCertified_proof⟩
    noEmpiricalApproximationImport :=
      K.noEmpiricalApproximationImport
    noEmpiricalApproximationImport_proof :=
      K.noEmpiricalApproximationImport_proof
    noApproximationFitTuning :=
      K.noApproximationFitTuning
    noApproximationFitTuning_proof :=
      K.noApproximationFitTuning_proof }

def rationalClosedRootIsolationMethodAsDecimalReadoutReady
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorRationalClosedRootIsolationMethod A P) :
  ThreeFlavorClosedRootDecimalReadoutReady ℚ A P :=
  { algebraicPresentation := K.algebraicPresentation
    approximationScheme :=
      rationalClosedRootIsolationMethodAsApproximationScheme K }

def NeedsThreeFlavorRationalClosedRootIsolationMethod
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) : Prop :=
  Not (exists _K : ThreeFlavorRationalClosedRootIsolationMethod A P, True)

/--
Canonical rational isolation method for a rational same-scope closed root.

For every positive rational tolerance `eps`, use the interval
`[selectedRoot, selectedRoot + eps]`.  Root uniqueness is inherited from the
algebraic presentation, so no additional numerical root selector is introduced.
-/
noncomputable def sameScopePackageAsRationalClosedRootIsolationMethod
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) :
  ThreeFlavorRationalClosedRootIsolationMethod A P := by
  let G := sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P
  exact
  { algebraicPresentation := G
    intervalFor := fun eps heps =>
      { lower := G.selectedRoot
        upper := G.selectedRoot + eps
        tolerance := eps
        lower_lt_upper := by
          linarith
        tolerance_pos := heps
        selectedRoot_mem := by
          constructor
          · rfl
          · linarith
        width_le_tolerance := by
          ring_nf
          exact le_rfl
        interval_unique_selected_root := by
          intro x hx hsel _hlow _hupper
          exact G.unique_selected_root x hx hsel
        intervalConstructedInternally :=
          G.polynomialPresentedInternally /\
            G.selectorPresentedInternally
        intervalConstructedInternally_proof :=
          ⟨G.polynomialPresentedInternally_proof,
            G.selectorPresentedInternally_proof⟩
        noEmpiricalDecimalImport := G.noEmpiricalFitImport
        noEmpiricalDecimalImport_proof :=
          G.noEmpiricalFitImport_proof
        noDecimalFitTuning := G.noParameterTuning
        noDecimalFitTuning_proof :=
          G.noParameterTuning_proof }
    interval_tolerance_le := by
      intro eps heps
      exact le_rfl
    methodConstructedInternally :=
      G.polynomialPresentedInternally /\
        G.selectorPresentedInternally
    methodConstructedInternally_proof :=
      ⟨G.polynomialPresentedInternally_proof,
        G.selectorPresentedInternally_proof⟩
    rationalEndpointsCertified := True
    rationalEndpointsCertified_proof := True.intro
    noEmpiricalApproximationImport := G.noEmpiricalFitImport
    noEmpiricalApproximationImport_proof :=
      G.noEmpiricalFitImport_proof
    noApproximationFitTuning := G.noParameterTuning
    noApproximationFitTuning_proof :=
      G.noParameterTuning_proof }

noncomputable def sameScopePackageAsRationalDecimalReadoutReady
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) :
  ThreeFlavorClosedRootDecimalReadoutReady ℚ A P :=
  rationalClosedRootIsolationMethodAsDecimalReadoutReady
    (sameScopePackageAsRationalClosedRootIsolationMethod A P)

/--
Explicit rational interval for the closed root.

Unlike the canonical interval `[selectedRoot, selectedRoot + eps]`, these
endpoints are supplied as rational bounds in their own right.  The audit fields
record that they are not symbolic aliases for the selected root.
-/
structure ThreeFlavorExplicitRationalClosedRootInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P) where
  lower : ℚ
  upper : ℚ
  tolerance : ℚ
  lower_lt_upper : lower < upper
  tolerance_pos : 0 < tolerance
  selectedRoot_mem :
    lower <= G.selectedRoot /\ G.selectedRoot <= upper
  width_le_tolerance : upper - lower <= tolerance
  endpointsExplicitRational : Prop
  endpointsExplicitRational_proof :
    endpointsExplicitRational
  endpointsNotRootSymbolic : Prop
  endpointsNotRootSymbolic_proof :
    endpointsNotRootSymbolic
  endpointsConstructedInternally : Prop
  endpointsConstructedInternally_proof :
    endpointsConstructedInternally
  noEmpiricalEndpointImport : Prop
  noEmpiricalEndpointImport_proof :
    noEmpiricalEndpointImport
  noEndpointFitTuning : Prop
  noEndpointFitTuning_proof :
    noEndpointFitTuning

def explicitRationalClosedRootIntervalAsIsolatingInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (E : ThreeFlavorExplicitRationalClosedRootInterval G) :
  ThreeFlavorClosedRootIsolatingInterval ℚ G :=
  { lower := E.lower
    upper := E.upper
    tolerance := E.tolerance
    lower_lt_upper := E.lower_lt_upper
    tolerance_pos := E.tolerance_pos
    selectedRoot_mem := E.selectedRoot_mem
    width_le_tolerance := E.width_le_tolerance
    interval_unique_selected_root := by
      intro x hx hsel _hlow _hupper
      exact G.unique_selected_root x hx hsel
    intervalConstructedInternally :=
      E.endpointsExplicitRational /\
        E.endpointsNotRootSymbolic /\
          E.endpointsConstructedInternally
    intervalConstructedInternally_proof :=
      ⟨E.endpointsExplicitRational_proof,
        E.endpointsNotRootSymbolic_proof,
        E.endpointsConstructedInternally_proof⟩
    noEmpiricalDecimalImport := E.noEmpiricalEndpointImport
    noEmpiricalDecimalImport_proof :=
      E.noEmpiricalEndpointImport_proof
    noDecimalFitTuning := E.noEndpointFitTuning
    noDecimalFitTuning_proof :=
      E.noEndpointFitTuning_proof }

/--
Explicit rational approximation scheme.

This is the non-symbolic-endpoint version of decimal readiness: every requested
positive rational tolerance must be met by an explicit rational interval whose
endpoints are certified not to be `selectedRoot` aliases.
-/
structure ThreeFlavorExplicitRationalApproximationScheme
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  algebraicPresentation :
    ThreeFlavorAlgebraicClosedRootPresentation ℚ A P :=
      sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P
  explicitIntervalFor :
    forall eps : ℚ,
      0 < eps ->
        ThreeFlavorExplicitRationalClosedRootInterval algebraicPresentation
  explicitInterval_tolerance_le :
    forall (eps : ℚ) (heps : 0 < eps),
      (explicitIntervalFor eps heps).tolerance <= eps
  schemeConstructedInternally : Prop
  schemeConstructedInternally_proof :
    schemeConstructedInternally
  endpointsNeverRootSymbolic : Prop
  endpointsNeverRootSymbolic_proof :
    endpointsNeverRootSymbolic
  noEmpiricalApproximationImport : Prop
  noEmpiricalApproximationImport_proof :
    noEmpiricalApproximationImport
  noApproximationFitTuning : Prop
  noApproximationFitTuning_proof :
    noApproximationFitTuning

def explicitRationalApproximationSchemeAsIsolationMethod
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (S : ThreeFlavorExplicitRationalApproximationScheme A P) :
  ThreeFlavorRationalClosedRootIsolationMethod A P :=
  { algebraicPresentation := S.algebraicPresentation
    intervalFor := fun eps heps =>
      explicitRationalClosedRootIntervalAsIsolatingInterval
        (S.explicitIntervalFor eps heps)
    interval_tolerance_le := S.explicitInterval_tolerance_le
    methodConstructedInternally := S.schemeConstructedInternally
    methodConstructedInternally_proof :=
      S.schemeConstructedInternally_proof
    rationalEndpointsCertified := S.endpointsNeverRootSymbolic
    rationalEndpointsCertified_proof :=
      S.endpointsNeverRootSymbolic_proof
    noEmpiricalApproximationImport :=
      S.noEmpiricalApproximationImport
    noEmpiricalApproximationImport_proof :=
      S.noEmpiricalApproximationImport_proof
    noApproximationFitTuning := S.noApproximationFitTuning
    noApproximationFitTuning_proof :=
      S.noApproximationFitTuning_proof }

def explicitRationalApproximationSchemeAsDecimalReadoutReady
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (S : ThreeFlavorExplicitRationalApproximationScheme A P) :
  ThreeFlavorClosedRootDecimalReadoutReady ℚ A P :=
  rationalClosedRootIsolationMethodAsDecimalReadoutReady
    (explicitRationalApproximationSchemeAsIsolationMethod S)

def NeedsThreeFlavorExplicitRationalApproximationScheme
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) : Prop :=
  Not (exists _S : ThreeFlavorExplicitRationalApproximationScheme A P, True)

/--
Numeral-encoded rational interval for the closed root.

This strengthens `ThreeFlavorExplicitRationalClosedRootInterval` by requiring
both endpoints to be displayed as integer-over-natural rational numerals.
-/
structure ThreeFlavorNumeralRationalClosedRootInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P) where
  lower : ℚ
  upper : ℚ
  tolerance : ℚ
  lowerNumerator : Int
  lowerDenominator : Nat
  lowerDenominator_pos : 0 < lowerDenominator
  upperNumerator : Int
  upperDenominator : Nat
  upperDenominator_pos : 0 < upperDenominator
  lower_eq_numeral :
    lower = (lowerNumerator : ℚ) / (lowerDenominator : ℚ)
  upper_eq_numeral :
    upper = (upperNumerator : ℚ) / (upperDenominator : ℚ)
  lower_lt_upper : lower < upper
  tolerance_pos : 0 < tolerance
  selectedRoot_mem :
    lower <= G.selectedRoot /\ G.selectedRoot <= upper
  width_le_tolerance : upper - lower <= tolerance
  endpointsConstructedInternally : Prop
  endpointsConstructedInternally_proof :
    endpointsConstructedInternally
  noEmpiricalEndpointImport : Prop
  noEmpiricalEndpointImport_proof :
    noEmpiricalEndpointImport
  noEndpointFitTuning : Prop
  noEndpointFitTuning_proof :
    noEndpointFitTuning

def numeralRationalClosedRootIntervalAsExplicitInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (N : ThreeFlavorNumeralRationalClosedRootInterval G) :
  ThreeFlavorExplicitRationalClosedRootInterval G :=
  { lower := N.lower
    upper := N.upper
    tolerance := N.tolerance
    lower_lt_upper := N.lower_lt_upper
    tolerance_pos := N.tolerance_pos
    selectedRoot_mem := N.selectedRoot_mem
    width_le_tolerance := N.width_le_tolerance
    endpointsExplicitRational :=
      N.lower =
          (N.lowerNumerator : ℚ) / (N.lowerDenominator : ℚ) /\
        N.upper =
          (N.upperNumerator : ℚ) / (N.upperDenominator : ℚ)
    endpointsExplicitRational_proof :=
      ⟨N.lower_eq_numeral, N.upper_eq_numeral⟩
    endpointsNotRootSymbolic :=
      N.lower =
          (N.lowerNumerator : ℚ) / (N.lowerDenominator : ℚ) /\
        N.upper =
          (N.upperNumerator : ℚ) / (N.upperDenominator : ℚ)
    endpointsNotRootSymbolic_proof :=
      ⟨N.lower_eq_numeral, N.upper_eq_numeral⟩
    endpointsConstructedInternally :=
      N.endpointsConstructedInternally
    endpointsConstructedInternally_proof :=
      N.endpointsConstructedInternally_proof
    noEmpiricalEndpointImport := N.noEmpiricalEndpointImport
    noEmpiricalEndpointImport_proof :=
      N.noEmpiricalEndpointImport_proof
    noEndpointFitTuning := N.noEndpointFitTuning
    noEndpointFitTuning_proof :=
      N.noEndpointFitTuning_proof }

/--
Numeral-endpoint approximation scheme.

Every tolerance is met by a rational interval with numerator/denominator
endpoint witnesses, rather than endpoint terms that mention the selected root.
-/
structure ThreeFlavorNumeralRationalApproximationScheme
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  algebraicPresentation :
    ThreeFlavorAlgebraicClosedRootPresentation ℚ A P :=
      sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P
  numeralIntervalFor :
    forall eps : ℚ,
      0 < eps ->
        ThreeFlavorNumeralRationalClosedRootInterval algebraicPresentation
  numeralInterval_tolerance_le :
    forall (eps : ℚ) (heps : 0 < eps),
      (numeralIntervalFor eps heps).tolerance <= eps
  schemeConstructedInternally : Prop
  schemeConstructedInternally_proof :
    schemeConstructedInternally
  noEmpiricalApproximationImport : Prop
  noEmpiricalApproximationImport_proof :
    noEmpiricalApproximationImport
  noApproximationFitTuning : Prop
  noApproximationFitTuning_proof :
    noApproximationFitTuning

def numeralRationalApproximationSchemeAsExplicitScheme
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (S : ThreeFlavorNumeralRationalApproximationScheme A P) :
  ThreeFlavorExplicitRationalApproximationScheme A P :=
  { algebraicPresentation := S.algebraicPresentation
    explicitIntervalFor := fun eps heps =>
      numeralRationalClosedRootIntervalAsExplicitInterval
        (S.numeralIntervalFor eps heps)
    explicitInterval_tolerance_le :=
      S.numeralInterval_tolerance_le
    schemeConstructedInternally :=
      S.schemeConstructedInternally
    schemeConstructedInternally_proof :=
      S.schemeConstructedInternally_proof
    endpointsNeverRootSymbolic :=
      forall eps heps,
        (S.numeralIntervalFor eps heps).lower =
            ((S.numeralIntervalFor eps heps).lowerNumerator : ℚ) /
              ((S.numeralIntervalFor eps heps).lowerDenominator : ℚ) /\
          (S.numeralIntervalFor eps heps).upper =
            ((S.numeralIntervalFor eps heps).upperNumerator : ℚ) /
              ((S.numeralIntervalFor eps heps).upperDenominator : ℚ)
    endpointsNeverRootSymbolic_proof := by
      intro eps heps
      exact ⟨
        (S.numeralIntervalFor eps heps).lower_eq_numeral,
        (S.numeralIntervalFor eps heps).upper_eq_numeral⟩
    noEmpiricalApproximationImport :=
      S.noEmpiricalApproximationImport
    noEmpiricalApproximationImport_proof :=
      S.noEmpiricalApproximationImport_proof
    noApproximationFitTuning :=
      S.noApproximationFitTuning
    noApproximationFitTuning_proof :=
      S.noApproximationFitTuning_proof }

def numeralRationalApproximationSchemeAsDecimalReadoutReady
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (S : ThreeFlavorNumeralRationalApproximationScheme A P) :
  ThreeFlavorClosedRootDecimalReadoutReady ℚ A P :=
  explicitRationalApproximationSchemeAsDecimalReadoutReady
    (numeralRationalApproximationSchemeAsExplicitScheme S)

def NeedsThreeFlavorNumeralRationalApproximationScheme
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) : Prop :=
  Not (exists _S : ThreeFlavorNumeralRationalApproximationScheme A P, True)

/--
Single certified numeral decimal window.

This is weaker than an arbitrary-precision scheme: it certifies one explicit
rational interval and one decimal label.  It is the object to fill after a
finite root-isolation computation produces concrete numerator/denominator
endpoints for a chosen tolerance.
-/
structure ThreeFlavorSingleNumeralDecimalCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P) where
  numeralInterval :
    ThreeFlavorNumeralRationalClosedRootInterval G
  decimalLabel : String
  decimalLabelCertifiedByNumeralInterval : Prop
  decimalLabelCertifiedByNumeralInterval_proof :
    decimalLabelCertifiedByNumeralInterval

def singleNumeralDecimalCertificateAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (K : ThreeFlavorSingleNumeralDecimalCertificate G) :
  ThreeFlavorClosedRootDecimalWindow ℚ G :=
  { interval :=
      explicitRationalClosedRootIntervalAsIsolatingInterval
        (numeralRationalClosedRootIntervalAsExplicitInterval
          K.numeralInterval)
    decimalLabel := K.decimalLabel
    decimalLabelCertifiedByInterval :=
      K.decimalLabelCertifiedByNumeralInterval
    decimalLabelCertifiedByInterval_proof :=
      K.decimalLabelCertifiedByNumeralInterval_proof }

theorem singleNumeralDecimalCertificate_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (K : ThreeFlavorSingleNumeralDecimalCertificate G) :
  (singleNumeralDecimalCertificateAsWindow K).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (singleNumeralDecimalCertificateAsWindow K).interval.upper :=
  decimalWindow_contains_gapRatio
    (singleNumeralDecimalCertificateAsWindow K)

theorem singleNumeralDecimalCertificate_width_le_tolerance
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (K : ThreeFlavorSingleNumeralDecimalCertificate G) :
  (singleNumeralDecimalCertificateAsWindow K).interval.upper -
      (singleNumeralDecimalCertificateAsWindow K).interval.lower <=
    K.numeralInterval.tolerance := by
  exact K.numeralInterval.width_le_tolerance

def NeedsThreeFlavorSingleNumeralDecimalCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P) : Prop :=
  Not (exists _K : ThreeFlavorSingleNumeralDecimalCertificate G, True)

/--
Concrete rational root-isolation certificate over an ordered root domain.

The endpoints are rational numerals, but the interval is interpreted in the
field `R` via `algebraMap ℚ R`.  This avoids assuming that the closed root is
itself rational.
-/
structure ThreeFlavorConcreteRationalRootIsolationCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation R A P) where
  coefficientPresentation :
    ThreeFlavorRationalCoefficientPolynomialOver R G
  lowerNumerator : Int
  lowerDenominator : Nat
  lowerDenominator_pos : 0 < lowerDenominator
  upperNumerator : Int
  upperDenominator : Nat
  upperDenominator_pos : 0 < upperDenominator
  toleranceNumerator : Nat
  toleranceDenominator : Nat
  toleranceDenominator_pos : 0 < toleranceDenominator
  lower : ℚ :=
    (lowerNumerator : ℚ) / (lowerDenominator : ℚ)
  upper : ℚ :=
    (upperNumerator : ℚ) / (upperDenominator : ℚ)
  tolerance : ℚ :=
    (toleranceNumerator : ℚ) / (toleranceDenominator : ℚ)
  lower_lt_upper :
    algebraMap ℚ R lower < algebraMap ℚ R upper
  tolerance_pos :
    0 < algebraMap ℚ R tolerance
  selectedRoot_mem :
    algebraMap ℚ R lower <= G.selectedRoot /\
      G.selectedRoot <= algebraMap ℚ R upper
  width_le_tolerance :
    algebraMap ℚ R upper - algebraMap ℚ R lower <=
      algebraMap ℚ R tolerance
  rootIsolationComputedFromCoefficients : Prop
  rootIsolationComputedFromCoefficients_proof :
    rootIsolationComputedFromCoefficients
  noEmpiricalEndpointImport : Prop
  noEmpiricalEndpointImport_proof :
    noEmpiricalEndpointImport
  noEndpointFitTuning : Prop
  noEndpointFitTuning_proof :
    noEndpointFitTuning
  noHiddenRootEncodingInEndpoints : Prop
  noHiddenRootEncodingInEndpoints_proof :
    noHiddenRootEncodingInEndpoints

def concreteRationalRootIsolationAsIsolatingInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (K : ThreeFlavorConcreteRationalRootIsolationCertificate R G) :
  ThreeFlavorClosedRootIsolatingInterval R G :=
  { lower := algebraMap ℚ R K.lower
    upper := algebraMap ℚ R K.upper
    tolerance := algebraMap ℚ R K.tolerance
    lower_lt_upper := K.lower_lt_upper
    tolerance_pos := K.tolerance_pos
    selectedRoot_mem := K.selectedRoot_mem
    width_le_tolerance := K.width_le_tolerance
    interval_unique_selected_root := by
      intro x hx hsel _hlow _hupper
      exact G.unique_selected_root x hx hsel
    intervalConstructedInternally :=
      K.coefficientPresentation.coefficientsDisplayedInternally /\
        K.coefficientPresentation.coefficientsSameScope /\
          K.rootIsolationComputedFromCoefficients /\
            K.noHiddenRootEncodingInEndpoints
    intervalConstructedInternally_proof :=
      ⟨K.coefficientPresentation.coefficientsDisplayedInternally_proof,
        K.coefficientPresentation.coefficientsSameScope_proof,
        K.rootIsolationComputedFromCoefficients_proof,
        K.noHiddenRootEncodingInEndpoints_proof⟩
    noEmpiricalDecimalImport :=
      K.coefficientPresentation.noEmpiricalCoefficientImport /\
        K.noEmpiricalEndpointImport
    noEmpiricalDecimalImport_proof :=
      ⟨K.coefficientPresentation.noEmpiricalCoefficientImport_proof,
        K.noEmpiricalEndpointImport_proof⟩
    noDecimalFitTuning :=
      K.coefficientPresentation.noCoefficientFitTuning /\
        K.noEndpointFitTuning
    noDecimalFitTuning_proof :=
      ⟨K.coefficientPresentation.noCoefficientFitTuning_proof,
        K.noEndpointFitTuning_proof⟩ }

theorem concreteRationalRootIsolation_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (K : ThreeFlavorConcreteRationalRootIsolationCertificate R G) :
  algebraMap ℚ R K.lower <= threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <= algebraMap ℚ R K.upper :=
  isolatingInterval_contains_gapRatio
    (concreteRationalRootIsolationAsIsolatingInterval K)

def NeedsThreeFlavorConcreteRationalRootIsolationCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation R A P) : Prop :=
  Not (exists _K :
    ThreeFlavorConcreteRationalRootIsolationCertificate R G, True)

/--
Endpoint-bound payload for a source-derived coefficient law.

This isolates the remaining finite decimal arithmetic: rational numerator /
denominator endpoints, interpreted in `R`, together with containment and width
proofs for the selected closed root.
-/
structure ThreeFlavorSourceDerivedEndpointBounds
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (_L : ThreeFlavorSourceDerivedRationalCoefficientLaw R G) where
  lowerNumerator : Int
  lowerDenominator : Nat
  lowerDenominator_pos : 0 < lowerDenominator
  upperNumerator : Int
  upperDenominator : Nat
  upperDenominator_pos : 0 < upperDenominator
  toleranceNumerator : Nat
  toleranceDenominator : Nat
  toleranceDenominator_pos : 0 < toleranceDenominator
  lower : ℚ :=
    (lowerNumerator : ℚ) / (lowerDenominator : ℚ)
  upper : ℚ :=
    (upperNumerator : ℚ) / (upperDenominator : ℚ)
  tolerance : ℚ :=
    (toleranceNumerator : ℚ) / (toleranceDenominator : ℚ)
  lower_lt_upper :
    algebraMap ℚ R lower < algebraMap ℚ R upper
  tolerance_pos :
    0 < algebraMap ℚ R tolerance
  selectedRoot_mem :
    algebraMap ℚ R lower <= G.selectedRoot /\
      G.selectedRoot <= algebraMap ℚ R upper
  width_le_tolerance :
    algebraMap ℚ R upper - algebraMap ℚ R lower <=
      algebraMap ℚ R tolerance
  rootIsolationComputedFromCoefficientLaw : Prop
  rootIsolationComputedFromCoefficientLaw_proof :
    rootIsolationComputedFromCoefficientLaw
  noEmpiricalEndpointImport : Prop
  noEmpiricalEndpointImport_proof :
    noEmpiricalEndpointImport
  noEndpointFitTuning : Prop
  noEndpointFitTuning_proof :
    noEndpointFitTuning
  noHiddenRootEncodingInEndpoints : Prop
  noHiddenRootEncodingInEndpoints_proof :
    noHiddenRootEncodingInEndpoints

def sourceDerivedEndpointBoundsAsConcreteIsolation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (L : ThreeFlavorSourceDerivedRationalCoefficientLaw R G)
  (B : ThreeFlavorSourceDerivedEndpointBounds R L) :
  ThreeFlavorConcreteRationalRootIsolationCertificate R G :=
  { coefficientPresentation :=
      sourceDerivedRationalCoefficientLawAsPolynomialOver L
    lowerNumerator := B.lowerNumerator
    lowerDenominator := B.lowerDenominator
    lowerDenominator_pos := B.lowerDenominator_pos
    upperNumerator := B.upperNumerator
    upperDenominator := B.upperDenominator
    upperDenominator_pos := B.upperDenominator_pos
    toleranceNumerator := B.toleranceNumerator
    toleranceDenominator := B.toleranceDenominator
    toleranceDenominator_pos := B.toleranceDenominator_pos
    lower := B.lower
    upper := B.upper
    tolerance := B.tolerance
    lower_lt_upper := B.lower_lt_upper
    tolerance_pos := B.tolerance_pos
    selectedRoot_mem := B.selectedRoot_mem
    width_le_tolerance := B.width_le_tolerance
    rootIsolationComputedFromCoefficients :=
      B.rootIsolationComputedFromCoefficientLaw
    rootIsolationComputedFromCoefficients_proof :=
      B.rootIsolationComputedFromCoefficientLaw_proof
    noEmpiricalEndpointImport := B.noEmpiricalEndpointImport
    noEmpiricalEndpointImport_proof :=
      B.noEmpiricalEndpointImport_proof
    noEndpointFitTuning := B.noEndpointFitTuning
    noEndpointFitTuning_proof := B.noEndpointFitTuning_proof
    noHiddenRootEncodingInEndpoints :=
      B.noHiddenRootEncodingInEndpoints
    noHiddenRootEncodingInEndpoints_proof :=
      B.noHiddenRootEncodingInEndpoints_proof }

theorem sourceDerivedEndpointBounds_discharge_isolationNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (L : ThreeFlavorSourceDerivedRationalCoefficientLaw R G)
  (B : ThreeFlavorSourceDerivedEndpointBounds R L) :
  Not (NeedsThreeFlavorConcreteRationalRootIsolationCertificate R G) := by
  intro hneed
  exact hneed
    ⟨sourceDerivedEndpointBoundsAsConcreteIsolation L B, True.intro⟩

/--
End-to-end source-derived decimal window certificate.

This combines the two new-territory payloads:

1. a non-tautological source-derived rational coefficient law, and
2. rational endpoint bounds computed from that coefficient law.

The result is still a finite window, not arbitrary-precision readiness.
-/
structure ThreeFlavorSourceDerivedRationalDecimalWindowCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation R A P) where
  coefficientLaw :
    ThreeFlavorSourceDerivedRationalCoefficientLaw R G
  isolationCertificate :
    ThreeFlavorConcreteRationalRootIsolationCertificate R G
  isolationUsesCoefficientLaw :
    isolationCertificate.coefficientPresentation =
      sourceDerivedRationalCoefficientLawAsPolynomialOver coefficientLaw
  decimalLabel : String
  decimalLabelCertifiedBySourceDerivedWindow : Prop
  decimalLabelCertifiedBySourceDerivedWindow_proof :
    decimalLabelCertifiedBySourceDerivedWindow

def sourceDerivedLawAndEndpointBoundsAsDecimalWindowCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (L : ThreeFlavorSourceDerivedRationalCoefficientLaw R G)
  (B : ThreeFlavorSourceDerivedEndpointBounds R L)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  ThreeFlavorSourceDerivedRationalDecimalWindowCertificate R G :=
  { coefficientLaw := L
    isolationCertificate :=
      sourceDerivedEndpointBoundsAsConcreteIsolation L B
    isolationUsesCoefficientLaw := rfl
    decimalLabel := decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow :=
      decimalLabelCertifiedBySourceDerivedWindow
    decimalLabelCertifiedBySourceDerivedWindow_proof := hlabel }

def sourceDerivedRationalDecimalWindowAsDecimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (K : ThreeFlavorSourceDerivedRationalDecimalWindowCertificate R G) :
  ThreeFlavorClosedRootDecimalWindow R G :=
  { interval :=
      concreteRationalRootIsolationAsIsolatingInterval
        K.isolationCertificate
    decimalLabel := K.decimalLabel
    decimalLabelCertifiedByInterval :=
      K.decimalLabelCertifiedBySourceDerivedWindow
    decimalLabelCertifiedByInterval_proof :=
      K.decimalLabelCertifiedBySourceDerivedWindow_proof }

theorem sourceDerivedRationalDecimalWindow_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (K : ThreeFlavorSourceDerivedRationalDecimalWindowCertificate R G) :
  (sourceDerivedRationalDecimalWindowAsDecimalWindow K).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (sourceDerivedRationalDecimalWindowAsDecimalWindow K).interval.upper :=
  decimalWindow_contains_gapRatio
    (sourceDerivedRationalDecimalWindowAsDecimalWindow K)

/--
Positive-readout sign premise for the selected same-scope root.

The Cauchy route gives a coefficient-derived symmetric interval
`[-B, B]`.  For the neutrino ratio readout, the standing minimal interval
should also supply the sign orientation `0 < selectedRoot`.  We keep that
orientation as an explicit audit payload, rather than hiding it inside the
coefficient bound.
-/
structure ThreeFlavorPositiveStandingRootReadout
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P) where
  selectedRoot_pos : 0 < G.selectedRoot
  signOrientationFromStandingMinimalInterval : Prop
  signOrientationFromStandingMinimalInterval_proof :
    signOrientationFromStandingMinimalInterval
  noEmpiricalSignImport : Prop
  noEmpiricalSignImport_proof : noEmpiricalSignImport
  noSignFitTuning : Prop
  noSignFitTuning_proof : noSignFitTuning

/--
Turn a source-derived rational decimal window into a positive readout window.

This clips only the lower endpoint to `0`; the upper endpoint remains the
coefficient-derived endpoint from the source window.  The result is useful
once the standing/minimal-interval layer has certified that the selected root
is positive, but it still does not claim a concrete decimal unless the source
window already supplied one.
-/
noncomputable def sourceDerivedRationalDecimalWindowAsPositiveReadoutWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (K : ThreeFlavorSourceDerivedRationalDecimalWindowCertificate ℚ G)
  (S : ThreeFlavorPositiveStandingRootReadout G) :
  ThreeFlavorClosedRootDecimalWindow ℚ G := by
  let D := sourceDerivedRationalDecimalWindowAsDecimalWindow K
  have hroot_le_upper : G.selectedRoot <= D.interval.upper :=
    D.interval.selectedRoot_mem.2
  have hupper_pos : 0 < D.interval.upper := by
    linarith [S.selectedRoot_pos, hroot_le_upper]
  exact
  { interval :=
      { lower := 0
        upper := D.interval.upper
        tolerance := D.interval.upper
        lower_lt_upper := by
          simpa using hupper_pos
        tolerance_pos := by
          simpa using hupper_pos
        selectedRoot_mem := by
          exact ⟨le_of_lt S.selectedRoot_pos, hroot_le_upper⟩
        width_le_tolerance := by
          ring_nf
          exact le_rfl
        interval_unique_selected_root := by
          intro x hx hsel _hlow _hupper
          exact G.unique_selected_root x hx hsel
        intervalConstructedInternally :=
          D.interval.intervalConstructedInternally /\
            S.signOrientationFromStandingMinimalInterval
        intervalConstructedInternally_proof :=
          ⟨D.interval.intervalConstructedInternally_proof,
            S.signOrientationFromStandingMinimalInterval_proof⟩
        noEmpiricalDecimalImport :=
          D.interval.noEmpiricalDecimalImport /\
            S.noEmpiricalSignImport
        noEmpiricalDecimalImport_proof :=
          ⟨D.interval.noEmpiricalDecimalImport_proof,
            S.noEmpiricalSignImport_proof⟩
        noDecimalFitTuning :=
          D.interval.noDecimalFitTuning /\ S.noSignFitTuning
        noDecimalFitTuning_proof :=
          ⟨D.interval.noDecimalFitTuning_proof,
            S.noSignFitTuning_proof⟩ }
    decimalLabel := D.decimalLabel
    decimalLabelCertifiedByInterval :=
      D.decimalLabelCertifiedByInterval
    decimalLabelCertifiedByInterval_proof :=
      D.decimalLabelCertifiedByInterval_proof }

theorem sourceDerivedRationalDecimalWindow_positiveReadout_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (K : ThreeFlavorSourceDerivedRationalDecimalWindowCertificate ℚ G)
  (S : ThreeFlavorPositiveStandingRootReadout G) :
  (sourceDerivedRationalDecimalWindowAsPositiveReadoutWindow K S).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (sourceDerivedRationalDecimalWindowAsPositiveReadoutWindow K S).interval.upper := by
  have hroot :
      G.selectedRoot = threeFlavorGapRatio A.massSquaredLevelOf :=
    algebraicClosedRootPresentation_selectedRoot_eq_gapRatio G
  constructor
  · dsimp [sourceDerivedRationalDecimalWindowAsPositiveReadoutWindow]
    rw [← hroot]
    exact le_of_lt S.selectedRoot_pos
  · dsimp [sourceDerivedRationalDecimalWindowAsPositiveReadoutWindow]
    rw [← hroot]
    exact
      (sourceDerivedRationalDecimalWindowAsDecimalWindow K).interval.selectedRoot_mem.2

def NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P) : Prop :=
  Not (exists W : ThreeFlavorClosedRootDecimalWindow ℚ G,
    W.interval.lower = 0 /\ True)

theorem sourceDerivedRationalDecimalWindowAndPositiveStandingReadout_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (K : ThreeFlavorSourceDerivedRationalDecimalWindowCertificate ℚ G)
  (S : ThreeFlavorPositiveStandingRootReadout G) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow G) := by
  intro hneed
  exact hneed
    ⟨sourceDerivedRationalDecimalWindowAsPositiveReadoutWindow K S,
      by
        dsimp [sourceDerivedRationalDecimalWindowAsPositiveReadoutWindow]
        exact ⟨rfl, True.intro⟩⟩

def NeedsThreeFlavorSourceDerivedRationalDecimalWindowCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation R A P) : Prop :=
  Not (exists _K :
    ThreeFlavorSourceDerivedRationalDecimalWindowCertificate R G, True)

theorem sourceDerivedLawAndEndpointBounds_discharge_decimalWindowNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (L : ThreeFlavorSourceDerivedRationalCoefficientLaw R G)
  (B : ThreeFlavorSourceDerivedEndpointBounds R L)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  Not (NeedsThreeFlavorSourceDerivedRationalDecimalWindowCertificate R G) := by
  intro hneed
  exact hneed
    ⟨sourceDerivedLawAndEndpointBoundsAsDecimalWindowCertificate
        L B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel,
      True.intro⟩

/--
End-to-end finite decimal-window constructor from a source coefficient table
whose non-tautology is witnessed by a nonzero coefficient in degree at least
two.  The endpoint bounds are still substantive input: they must be certified
for the coefficient law assembled from the table and audit.
-/
noncomputable def sourceCoefficientTableHighCoefficientAndEndpointBoundsAsDecimalWindowCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (T : ThreeFlavorSourceCoefficientExtensionalTable R G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (K :
    ThreeFlavorHighCoefficientNonlinearCertificate
      (sourceCoefficientExtensionalTableAsSyntax T))
  (B :
    ThreeFlavorSourceDerivedEndpointBounds R
      (sourceCoefficientTableHighCoefficientAsRationalCoefficientLaw T Psrc K))
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  ThreeFlavorSourceDerivedRationalDecimalWindowCertificate R G :=
  sourceDerivedLawAndEndpointBoundsAsDecimalWindowCertificate
    (sourceCoefficientTableHighCoefficientAsRationalCoefficientLaw T Psrc K)
    B
    decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow
    hlabel

theorem sourceCoefficientTableHighCoefficientAndEndpointBounds_discharge_decimalWindowNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (T : ThreeFlavorSourceCoefficientExtensionalTable R G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (K :
    ThreeFlavorHighCoefficientNonlinearCertificate
      (sourceCoefficientExtensionalTableAsSyntax T))
  (B :
    ThreeFlavorSourceDerivedEndpointBounds R
      (sourceCoefficientTableHighCoefficientAsRationalCoefficientLaw T Psrc K))
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  Not (NeedsThreeFlavorSourceDerivedRationalDecimalWindowCertificate R G) := by
  intro hneed
  exact hneed
    ⟨sourceCoefficientTableHighCoefficientAndEndpointBoundsAsDecimalWindowCertificate
        T Psrc K B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel,
      True.intro⟩

/--
Coefficient-side construction program for the new source polynomial.  This is
the part that can be built and audited before any endpoint/root-isolation
arithmetic is attempted.
-/
structure ThreeFlavorNewSourcePolynomialCoefficientProgram
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation R A P) where
  coefficientTable :
    ThreeFlavorSourceCoefficientExtensionalTable R G
  positiveSourceAudit :
    ThreeFlavorCoefficientPositiveSourceAudit
  highCoefficientWitness :
    ThreeFlavorHighCoefficientNonlinearCertificate
      (sourceCoefficientExtensionalTableAsSyntax coefficientTable)

noncomputable def newSourcePolynomialCoefficientProgramAsCoefficientLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (Q : ThreeFlavorNewSourcePolynomialCoefficientProgram R G) :
  ThreeFlavorSourceDerivedRationalCoefficientLaw R G :=
  sourceCoefficientTableHighCoefficientAsRationalCoefficientLaw
    Q.coefficientTable
    Q.positiveSourceAudit
    Q.highCoefficientWitness

theorem newSourcePolynomialCoefficientProgram_discharge_coefficientLawNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (Q : ThreeFlavorNewSourcePolynomialCoefficientProgram R G) :
  Not (NeedsThreeFlavorSourceDerivedRationalCoefficientLaw R G) := by
  intro hneed
  exact hneed
    ⟨newSourcePolynomialCoefficientProgramAsCoefficientLaw Q, True.intro⟩

theorem newSourcePolynomialCoefficientProgram_not_linear_packaging
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (Q : ThreeFlavorNewSourcePolynomialCoefficientProgram R G) :
  (newSourcePolynomialCoefficientProgramAsCoefficientLaw Q).coefficientLawNotClosedRootLinearPackaging :=
  (newSourcePolynomialCoefficientProgramAsCoefficientLaw Q).coefficientLawNotClosedRootLinearPackaging_proof

theorem newSourcePolynomialCoefficientProgram_no_hidden_root_encoding
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (Q : ThreeFlavorNewSourcePolynomialCoefficientProgram R G) :
  (newSourcePolynomialCoefficientProgramAsCoefficientLaw Q).noHiddenRootEncodingInCoefficients :=
  (newSourcePolynomialCoefficientProgramAsCoefficientLaw Q).noHiddenRootEncodingInCoefficients_proof

/--
Candidate format for the genuinely new polynomial: a rational polynomial whose
base-change to `R` is the closed-root polynomial, with a high-degree nonzero
coefficient after base change.
-/
structure ThreeFlavorSourceRationalPolynomialCandidate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation R A P) where
  sourcePolynomial : Polynomial ℚ
  sourcePolynomial_maps_to_closedRoot :
    sourcePolynomial.map (algebraMap ℚ R) = G.explicitPolynomial
  coefficient_extensionality :
    forall n : Nat,
      ((Finset.range (sourcePolynomial.natDegree + 1)).sum
        (fun k =>
          Polynomial.C (algebraMap ℚ R (sourcePolynomial.coeff k)) *
            Polynomial.X ^ k)).coeff n =
        G.explicitPolynomial.coeff n
  sourcePolynomialSourceDerived : Prop
  sourcePolynomialSourceDerived_proof :
    sourcePolynomialSourceDerived
  witnessDegree : ℕ
  witnessDegree_ge_two :
    2 ≤ witnessDegree
  mappedWitnessCoefficient_ne_zero :
    algebraMap ℚ R (sourcePolynomial.coeff witnessDegree) ≠ 0
  coefficientsDoNotEncodeSelectedRoot : Prop
  coefficientsDoNotEncodeSelectedRoot_proof :
    coefficientsDoNotEncodeSelectedRoot
  noOneAnchorCoefficientImport : Prop
  noOneAnchorCoefficientImport_proof :
    noOneAnchorCoefficientImport

/--
Alignment certificate from an internal coordinate anchor to the rational
closed-root presentation.

This is deliberately not a polynomial witness by itself.  It records the
additional facts needed to reuse an independently constructed internal anchor
as the concrete source polynomial for the closed-root readout route.
-/
structure ThreeFlavorInternalAnchorRationalPolynomialAlignment
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (K : ThreeFlavorInternalCoordinateAnchor ℚ A) where
  polynomial_eq_closedRoot :
    K.polynomial = G.explicitPolynomial
  root_eq_selectedRoot :
    K.root = G.selectedRoot
  witnessDegree : ℕ
  witnessDegree_ge_two :
    2 ≤ witnessDegree
  witnessCoefficient_ne_zero :
    K.polynomial.coeff witnessDegree ≠ 0
  coefficientsDoNotEncodeSelectedRoot : Prop
  coefficientsDoNotEncodeSelectedRoot_proof :
    coefficientsDoNotEncodeSelectedRoot

noncomputable def internalAnchorAlignmentAsSourceRationalPolynomialCandidate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (K : ThreeFlavorInternalCoordinateAnchor ℚ A)
  (L : ThreeFlavorInternalAnchorRationalPolynomialAlignment G K) :
  ThreeFlavorSourceRationalPolynomialCandidate ℚ G :=
  { sourcePolynomial := K.polynomial
    sourcePolynomial_maps_to_closedRoot := by
      ext n
      simp [L.polynomial_eq_closedRoot]
    coefficient_extensionality := by
      intro n
      have hsum :
          (Finset.range (K.polynomial.natDegree + 1)).sum
              (fun k =>
                Polynomial.C (algebraMap ℚ ℚ (K.polynomial.coeff k)) *
                  Polynomial.X ^ k) =
            K.polynomial := by
        simpa using (K.polynomial.as_sum_range_C_mul_X_pow).symm
      exact
        (congrArg (fun p : Polynomial ℚ => p.coeff n) hsum).trans
          (congrArg (fun p : Polynomial ℚ => p.coeff n)
            L.polynomial_eq_closedRoot)
    sourcePolynomialSourceDerived :=
      K.sourceConstructsPolynomial
    sourcePolynomialSourceDerived_proof :=
      K.sourceConstructsPolynomial_proof
    witnessDegree := L.witnessDegree
    witnessDegree_ge_two := L.witnessDegree_ge_two
    mappedWitnessCoefficient_ne_zero := by
      simpa using L.witnessCoefficient_ne_zero
    coefficientsDoNotEncodeSelectedRoot :=
      L.coefficientsDoNotEncodeSelectedRoot
    coefficientsDoNotEncodeSelectedRoot_proof :=
      L.coefficientsDoNotEncodeSelectedRoot_proof
    noOneAnchorCoefficientImport :=
      K.noOneAnchorImport
    noOneAnchorCoefficientImport_proof :=
      K.noOneAnchorImport_proof }

theorem internalAnchorAlignment_root_matches_closedRoot
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {K : ThreeFlavorInternalCoordinateAnchor ℚ A}
  (L : ThreeFlavorInternalAnchorRationalPolynomialAlignment G K) :
  K.root = P.sameScopePredicate.closedRatio := by
  rw [L.root_eq_selectedRoot, G.selectedRoot_eq_closedRoot]

noncomputable def sourceRationalPolynomialCandidateAsCoefficientTable
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate R G) :
  ThreeFlavorSourceCoefficientExtensionalTable R G :=
  { coefficientBound :=
      Q.sourcePolynomial.natDegree
    rationalCoefficientAt := fun n => Q.sourcePolynomial.coeff n
    coefficient_extensionality := by
      intro n
      exact Q.coefficient_extensionality n
    coefficientTableSourceDerived :=
      Q.sourcePolynomialSourceDerived
    coefficientTableSourceDerived_proof :=
      Q.sourcePolynomialSourceDerived_proof }

noncomputable def sourceRationalPolynomialCandidateAsHighCoefficientWitness
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate R G) :
  ThreeFlavorHighCoefficientNonlinearCertificate
    (sourceCoefficientExtensionalTableAsSyntax
      (sourceRationalPolynomialCandidateAsCoefficientTable Q)) :=
  { witnessDegree := Q.witnessDegree
    witnessDegree_ge_two := Q.witnessDegree_ge_two
    witnessCoefficient_ne_zero := by
      have hcoeff_ne :
          Q.sourcePolynomial.coeff Q.witnessDegree ≠ 0 := by
        intro hzero
        exact Q.mappedWitnessCoefficient_ne_zero (by rw [hzero]; simp)
      have hle :
          Q.witnessDegree ≤ Q.sourcePolynomial.natDegree :=
        Polynomial.le_natDegree_of_ne_zero hcoeff_ne
      simpa [sourceCoefficientExtensionalTableAsSyntax,
        sourceRationalPolynomialCandidateAsCoefficientTable,
        hle] using Q.mappedWitnessCoefficient_ne_zero
    coefficientsDoNotEncodeSelectedRoot :=
      Q.coefficientsDoNotEncodeSelectedRoot
    coefficientsDoNotEncodeSelectedRoot_proof :=
      Q.coefficientsDoNotEncodeSelectedRoot_proof
    noOneAnchorCoefficientImport :=
      Q.noOneAnchorCoefficientImport
    noOneAnchorCoefficientImport_proof :=
      Q.noOneAnchorCoefficientImport_proof }

noncomputable def sourceRationalPolynomialCandidateAsCoefficientProgram
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate R G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit) :
  ThreeFlavorNewSourcePolynomialCoefficientProgram R G :=
  { coefficientTable :=
      sourceRationalPolynomialCandidateAsCoefficientTable Q
    positiveSourceAudit := Psrc
    highCoefficientWitness :=
      sourceRationalPolynomialCandidateAsHighCoefficientWitness Q }

theorem sourceRationalPolynomialCandidate_discharge_coefficientLawNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate R G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit) :
  Not (NeedsThreeFlavorSourceDerivedRationalCoefficientLaw R G) :=
  newSourcePolynomialCoefficientProgram_discharge_coefficientLawNeed
    (sourceRationalPolynomialCandidateAsCoefficientProgram Q Psrc)

theorem internalAnchorAlignment_discharge_sourcePolynomialNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (K : ThreeFlavorInternalCoordinateAnchor ℚ A)
  (L : ThreeFlavorInternalAnchorRationalPolynomialAlignment G K)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit) :
  Not (NeedsThreeFlavorSourceDerivedRationalCoefficientLaw ℚ G) :=
  sourceRationalPolynomialCandidate_discharge_coefficientLawNeed
    (internalAnchorAlignmentAsSourceRationalPolynomialCandidate G K L)
    Psrc

/--
Rational-polynomial alignment for the quotient-normal-form route.

This is the direct construction target for the preferred AASC-native path:
after a quotient-normal-form law is built over `ℚ`, this alignment states that
its polynomial/root are the same concrete polynomial/root used by the
closed-root presentation.  The nonzero high coefficient and anti-encoding
fields keep the route from collapsing into a mere relabeling.
-/
structure ThreeFlavorQuotientNormalFormRationalPolynomialAlignment
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) where
  normalFormPolynomial_eq_closedRoot :
    Q.polynomialOfNormalForm Q.normalForm = G.explicitPolynomial
  normalFormRoot_eq_selectedRoot :
    Q.rootOfNormalForm Q.normalForm = G.selectedRoot
  witnessDegree : ℕ
  witnessDegree_ge_two :
    2 ≤ witnessDegree
  witnessCoefficient_ne_zero :
    (Q.polynomialOfNormalForm Q.normalForm).coeff witnessDegree ≠ 0
  coefficientsDoNotEncodeSelectedRoot : Prop
  coefficientsDoNotEncodeSelectedRoot_proof :
    coefficientsDoNotEncodeSelectedRoot

/--
Canonical same-scope polynomial audit for the QNF route.

This is the focused witness needed to reuse the canonical same-scope closed-root
normal form as the QNF source polynomial for a chosen algebraic presentation
`G`.  It records the one presentation equality Lean cannot infer for an
arbitrary `G`, plus the nonlinear/non-encoding guards.
-/
structure ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P) where
  sameScopePolynomial_eq_closedRoot :
    P.sameScopePredicate.polynomial = G.explicitPolynomial
  witnessDegree : ℕ
  witnessDegree_ge_two :
    2 ≤ witnessDegree
  witnessCoefficient_ne_zero :
    P.sameScopePredicate.polynomial.coeff witnessDegree ≠ 0
  coefficientsDoNotEncodeSelectedRoot : Prop
  coefficientsDoNotEncodeSelectedRoot_proof :
    coefficientsDoNotEncodeSelectedRoot

def canonicalSameScopeQNFPolynomialAuditAsAlignment
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (U : ThreeFlavorCanonicalSameScopeQNFPolynomialAudit G) :
  ThreeFlavorQuotientNormalFormRationalPolynomialAlignment
    G
    (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P) :=
  { normalFormPolynomial_eq_closedRoot := by
      simpa [sameScopeClosedRootNormalFormAsInteriorLaw,
        quotientNormalFormClosedRootIdentificationAsInteriorLaw,
        quotientNormalFormComponentsAsInteriorLaw,
        sameScopeClosedRootAsQuotientNormalFormSyntax] using
        U.sameScopePolynomial_eq_closedRoot
    normalFormRoot_eq_selectedRoot := by
      simpa [sameScopeClosedRootNormalFormAsInteriorLaw,
        quotientNormalFormClosedRootIdentificationAsInteriorLaw,
        quotientNormalFormComponentsAsInteriorLaw,
        sameScopeClosedRootAsQuotientNormalFormSyntax] using
        G.selectedRoot_eq_closedRoot.symm
    witnessDegree := U.witnessDegree
    witnessDegree_ge_two := U.witnessDegree_ge_two
    witnessCoefficient_ne_zero := by
      simpa [sameScopeClosedRootNormalFormAsInteriorLaw,
        quotientNormalFormClosedRootIdentificationAsInteriorLaw,
        quotientNormalFormComponentsAsInteriorLaw,
        sameScopeClosedRootAsQuotientNormalFormSyntax] using
        U.witnessCoefficient_ne_zero
    coefficientsDoNotEncodeSelectedRoot :=
      U.coefficientsDoNotEncodeSelectedRoot
    coefficientsDoNotEncodeSelectedRoot_proof :=
      U.coefficientsDoNotEncodeSelectedRoot_proof }

def quotientNormalFormRationalAlignmentAsInternalAnchorAlignment
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A)
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q) :
  ThreeFlavorInternalAnchorRationalPolynomialAlignment
    G
    (quotientNormalFormInteriorLawAsInternalCoordinateAnchor ℚ A Q) :=
  { polynomial_eq_closedRoot :=
      L.normalFormPolynomial_eq_closedRoot
    root_eq_selectedRoot :=
      L.normalFormRoot_eq_selectedRoot
    witnessDegree := L.witnessDegree
    witnessDegree_ge_two := L.witnessDegree_ge_two
    witnessCoefficient_ne_zero :=
      L.witnessCoefficient_ne_zero
    coefficientsDoNotEncodeSelectedRoot :=
      L.coefficientsDoNotEncodeSelectedRoot
    coefficientsDoNotEncodeSelectedRoot_proof :=
      L.coefficientsDoNotEncodeSelectedRoot_proof }

noncomputable def quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A)
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q) :
  ThreeFlavorSourceRationalPolynomialCandidate ℚ G :=
  internalAnchorAlignmentAsSourceRationalPolynomialCandidate
    G
    (quotientNormalFormInteriorLawAsInternalCoordinateAnchor ℚ A Q)
    (quotientNormalFormRationalAlignmentAsInternalAnchorAlignment G Q L)

theorem quotientNormalFormInteriorLaw_discharge_sourcePolynomialNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A)
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit) :
  Not (NeedsThreeFlavorSourceDerivedRationalCoefficientLaw ℚ G) :=
  internalAnchorAlignment_discharge_sourcePolynomialNeed
    G
    (quotientNormalFormInteriorLawAsInternalCoordinateAnchor ℚ A Q)
    (quotientNormalFormRationalAlignmentAsInternalAnchorAlignment G Q L)
    Psrc

/--
Bundled construction program for the new-territory readout route.  This object
does not assume a ready-made source polynomial exists in the corpus.  It states
exactly what must be newly constructed: a source coefficient table, positive
AASC audit, high-coefficient non-tautology witness, and endpoint bounds
computed from the assembled law.
-/
structure ThreeFlavorNewSourcePolynomialReadoutProgram
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation R A P) where
  coefficientTable :
    ThreeFlavorSourceCoefficientExtensionalTable R G
  positiveSourceAudit :
    ThreeFlavorCoefficientPositiveSourceAudit
  highCoefficientWitness :
    ThreeFlavorHighCoefficientNonlinearCertificate
      (sourceCoefficientExtensionalTableAsSyntax coefficientTable)
  endpointBounds :
    ThreeFlavorSourceDerivedEndpointBounds R
      (sourceCoefficientTableHighCoefficientAsRationalCoefficientLaw
        coefficientTable
        positiveSourceAudit
        highCoefficientWitness)
  decimalLabel : String
  decimalLabelCertifiedBySourceDerivedWindow : Prop
  decimalLabelCertifiedBySourceDerivedWindow_proof :
    decimalLabelCertifiedBySourceDerivedWindow

noncomputable def newSourcePolynomialCoefficientProgramAndEndpointBoundsAsReadoutProgram
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (Q : ThreeFlavorNewSourcePolynomialCoefficientProgram R G)
  (B :
    ThreeFlavorSourceDerivedEndpointBounds R
      (newSourcePolynomialCoefficientProgramAsCoefficientLaw Q))
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  ThreeFlavorNewSourcePolynomialReadoutProgram R G :=
  { coefficientTable := Q.coefficientTable
    positiveSourceAudit := Q.positiveSourceAudit
    highCoefficientWitness := Q.highCoefficientWitness
    endpointBounds := B
    decimalLabel := decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow :=
      decimalLabelCertifiedBySourceDerivedWindow
    decimalLabelCertifiedBySourceDerivedWindow_proof := hlabel }

noncomputable def newSourcePolynomialReadoutProgramAsCoefficientLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (Q : ThreeFlavorNewSourcePolynomialReadoutProgram R G) :
  ThreeFlavorSourceDerivedRationalCoefficientLaw R G :=
  sourceCoefficientTableHighCoefficientAsRationalCoefficientLaw
    Q.coefficientTable
    Q.positiveSourceAudit
    Q.highCoefficientWitness

@[simp] theorem newSourcePolynomialCoefficientProgramAndEndpointBounds_coeffLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (Q : ThreeFlavorNewSourcePolynomialCoefficientProgram R G)
  (B :
    ThreeFlavorSourceDerivedEndpointBounds R
      (newSourcePolynomialCoefficientProgramAsCoefficientLaw Q))
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  newSourcePolynomialReadoutProgramAsCoefficientLaw
      (newSourcePolynomialCoefficientProgramAndEndpointBoundsAsReadoutProgram
        Q B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel) =
    newSourcePolynomialCoefficientProgramAsCoefficientLaw Q :=
  rfl

noncomputable def newSourcePolynomialReadoutProgramAsDecimalWindowCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (Q : ThreeFlavorNewSourcePolynomialReadoutProgram R G) :
  ThreeFlavorSourceDerivedRationalDecimalWindowCertificate R G :=
  sourceCoefficientTableHighCoefficientAndEndpointBoundsAsDecimalWindowCertificate
    Q.coefficientTable
    Q.positiveSourceAudit
    Q.highCoefficientWitness
    Q.endpointBounds
    Q.decimalLabel
    Q.decimalLabelCertifiedBySourceDerivedWindow
    Q.decimalLabelCertifiedBySourceDerivedWindow_proof

theorem newSourcePolynomialReadoutProgram_discharge_decimalWindowNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (Q : ThreeFlavorNewSourcePolynomialReadoutProgram R G) :
  Not (NeedsThreeFlavorSourceDerivedRationalDecimalWindowCertificate R G) := by
  intro hneed
  exact hneed
    ⟨newSourcePolynomialReadoutProgramAsDecimalWindowCertificate Q, True.intro⟩

theorem newSourcePolynomialReadoutProgram_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (Q : ThreeFlavorNewSourcePolynomialReadoutProgram R G) :
  (sourceDerivedRationalDecimalWindowAsDecimalWindow
      (newSourcePolynomialReadoutProgramAsDecimalWindowCertificate Q)).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (sourceDerivedRationalDecimalWindowAsDecimalWindow
        (newSourcePolynomialReadoutProgramAsDecimalWindowCertificate Q)).interval.upper :=
  sourceDerivedRationalDecimalWindow_contains_gapRatio
    (newSourcePolynomialReadoutProgramAsDecimalWindowCertificate Q)

theorem newSourcePolynomialReadoutProgram_coefficientLaw_not_linear_packaging
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (Q : ThreeFlavorNewSourcePolynomialReadoutProgram R G) :
  (newSourcePolynomialReadoutProgramAsCoefficientLaw Q).coefficientLawNotClosedRootLinearPackaging :=
  (newSourcePolynomialReadoutProgramAsCoefficientLaw Q).coefficientLawNotClosedRootLinearPackaging_proof

theorem newSourcePolynomialReadoutProgram_no_hidden_root_encoding
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (Q : ThreeFlavorNewSourcePolynomialReadoutProgram R G) :
  (newSourcePolynomialReadoutProgramAsCoefficientLaw Q).noHiddenRootEncodingInCoefficients :=
  (newSourcePolynomialReadoutProgramAsCoefficientLaw Q).noHiddenRootEncodingInCoefficients_proof

theorem newSourcePolynomialReadoutProgram_no_empirical_import
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (Q : ThreeFlavorNewSourcePolynomialReadoutProgram R G) :
  (newSourcePolynomialReadoutProgramAsCoefficientLaw Q).noEmpiricalCoefficientImport :=
  (newSourcePolynomialReadoutProgramAsCoefficientLaw Q).noEmpiricalCoefficientImport_proof

noncomputable def sourceRationalPolynomialCandidateAndEndpointBoundsAsReadoutProgram
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate R G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B :
    ThreeFlavorSourceDerivedEndpointBounds R
      (newSourcePolynomialCoefficientProgramAsCoefficientLaw
        (sourceRationalPolynomialCandidateAsCoefficientProgram Q Psrc)))
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  ThreeFlavorNewSourcePolynomialReadoutProgram R G :=
  newSourcePolynomialCoefficientProgramAndEndpointBoundsAsReadoutProgram
    (sourceRationalPolynomialCandidateAsCoefficientProgram Q Psrc)
    B
    decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow
    hlabel

noncomputable def sourceRationalPolynomialCandidateAndEndpointBoundsAsDecimalWindowCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate R G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B :
    ThreeFlavorSourceDerivedEndpointBounds R
      (newSourcePolynomialCoefficientProgramAsCoefficientLaw
        (sourceRationalPolynomialCandidateAsCoefficientProgram Q Psrc)))
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  ThreeFlavorSourceDerivedRationalDecimalWindowCertificate R G :=
  newSourcePolynomialReadoutProgramAsDecimalWindowCertificate
    (sourceRationalPolynomialCandidateAndEndpointBoundsAsReadoutProgram
      Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)

theorem sourceRationalPolynomialCandidateAndEndpointBounds_discharge_decimalWindowNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  [Algebra ℚ R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation R A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate R G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B :
    ThreeFlavorSourceDerivedEndpointBounds R
      (newSourcePolynomialCoefficientProgramAsCoefficientLaw
        (sourceRationalPolynomialCandidateAsCoefficientProgram Q Psrc)))
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  Not (NeedsThreeFlavorSourceDerivedRationalDecimalWindowCertificate R G) :=
  newSourcePolynomialReadoutProgram_discharge_decimalWindowNeed
    (sourceRationalPolynomialCandidateAndEndpointBoundsAsReadoutProgram
      Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)

/--
Audit needed to turn the current rational closed-root polynomial itself into a
candidate for the new-source route.  The polynomial content is concrete
(`G.explicitPolynomial`); the non-tautology and no-import guards remain
substantive inputs.
-/
structure ThreeFlavorRationalClosedRootPolynomialCandidateAudit
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P) where
  witnessDegree : ℕ
  witnessDegree_ge_two :
    2 ≤ witnessDegree
  witnessCoefficient_ne_zero :
    G.explicitPolynomial.coeff witnessDegree ≠ 0
  coefficientsDoNotEncodeSelectedRoot : Prop
  coefficientsDoNotEncodeSelectedRoot_proof :
    coefficientsDoNotEncodeSelectedRoot
  noOneAnchorCoefficientImport : Prop
  noOneAnchorCoefficientImport_proof :
    noOneAnchorCoefficientImport

noncomputable def rationalClosedRootPolynomialAsSourceRationalCandidate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G) :
  ThreeFlavorSourceRationalPolynomialCandidate ℚ G :=
  { sourcePolynomial := G.explicitPolynomial
    sourcePolynomial_maps_to_closedRoot := by
      ext n
      simp
    coefficient_extensionality := by
      intro n
      have hpoly :
          (Finset.range (G.explicitPolynomial.natDegree + 1)).sum
              (fun k =>
                Polynomial.C
                    (algebraMap ℚ ℚ (G.explicitPolynomial.coeff k)) *
                  Polynomial.X ^ k) =
            G.explicitPolynomial := by
        simpa using
          (G.explicitPolynomial.as_sum_range_C_mul_X_pow).symm
      exact congrArg (fun p : Polynomial ℚ => p.coeff n) hpoly
    sourcePolynomialSourceDerived :=
      G.polynomialPresentedInternally
    sourcePolynomialSourceDerived_proof :=
      G.polynomialPresentedInternally_proof
    witnessDegree := Q.witnessDegree
    witnessDegree_ge_two := Q.witnessDegree_ge_two
    mappedWitnessCoefficient_ne_zero := by
      simpa using Q.witnessCoefficient_ne_zero
    coefficientsDoNotEncodeSelectedRoot :=
      Q.coefficientsDoNotEncodeSelectedRoot
    coefficientsDoNotEncodeSelectedRoot_proof :=
      Q.coefficientsDoNotEncodeSelectedRoot_proof
    noOneAnchorCoefficientImport :=
      Q.noOneAnchorCoefficientImport
    noOneAnchorCoefficientImport_proof :=
      Q.noOneAnchorCoefficientImport_proof }

noncomputable def rationalClosedRootPolynomialCandidateAsCoefficientProgram
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit) :
  ThreeFlavorNewSourcePolynomialCoefficientProgram ℚ G :=
  sourceRationalPolynomialCandidateAsCoefficientProgram
    (rationalClosedRootPolynomialAsSourceRationalCandidate G Q)
    Psrc

theorem rationalClosedRootPolynomialCandidate_discharge_coefficientLawNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit) :
  Not (NeedsThreeFlavorSourceDerivedRationalCoefficientLaw ℚ G) :=
  sourceRationalPolynomialCandidate_discharge_coefficientLawNeed
    (rationalClosedRootPolynomialAsSourceRationalCandidate G Q)
    Psrc

noncomputable def rationalClosedRootPolynomialCandidateAndEndpointBoundsAsDecimalWindowCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B :
    ThreeFlavorSourceDerivedEndpointBounds ℚ
      (newSourcePolynomialCoefficientProgramAsCoefficientLaw
        (rationalClosedRootPolynomialCandidateAsCoefficientProgram G Q Psrc)))
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  ThreeFlavorSourceDerivedRationalDecimalWindowCertificate ℚ G :=
  sourceRationalPolynomialCandidateAndEndpointBoundsAsDecimalWindowCertificate
    (rationalClosedRootPolynomialAsSourceRationalCandidate G Q)
    Psrc
    B
    decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow
    hlabel

theorem rationalClosedRootPolynomialCandidateAndEndpointBounds_discharge_decimalWindowNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B :
    ThreeFlavorSourceDerivedEndpointBounds ℚ
      (newSourcePolynomialCoefficientProgramAsCoefficientLaw
        (rationalClosedRootPolynomialCandidateAsCoefficientProgram G Q Psrc)))
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  Not (NeedsThreeFlavorSourceDerivedRationalDecimalWindowCertificate ℚ G) := by
  intro hneed
  exact hneed
    ⟨rationalClosedRootPolynomialCandidateAndEndpointBoundsAsDecimalWindowCertificate
        G Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel,
      True.intro⟩

theorem rationalClosedRootPolynomialCandidateAndEndpointBounds_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B :
    ThreeFlavorSourceDerivedEndpointBounds ℚ
      (newSourcePolynomialCoefficientProgramAsCoefficientLaw
        (rationalClosedRootPolynomialCandidateAsCoefficientProgram G Q Psrc)))
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  (sourceDerivedRationalDecimalWindowAsDecimalWindow
      (rationalClosedRootPolynomialCandidateAndEndpointBoundsAsDecimalWindowCertificate
        G Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (sourceDerivedRationalDecimalWindowAsDecimalWindow
        (rationalClosedRootPolynomialCandidateAndEndpointBoundsAsDecimalWindowCertificate
          G Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)).interval.upper :=
  sourceDerivedRationalDecimalWindow_contains_gapRatio
    (rationalClosedRootPolynomialCandidateAndEndpointBoundsAsDecimalWindowCertificate
      G Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)

/--
Numeral endpoint-bounds payload for the rational closed-root candidate.  A
`ThreeFlavorNumeralRationalClosedRootInterval` already carries numeral lower
and upper endpoints; this wrapper supplies the missing numeral tolerance and
the source-computation / no-hidden-root endpoint guards needed by
`ThreeFlavorSourceDerivedEndpointBounds`.
-/
structure ThreeFlavorRationalClosedRootCandidateNumeralEndpointBounds
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P) where
  numeralInterval :
    ThreeFlavorNumeralRationalClosedRootInterval G
  toleranceNumerator : Nat
  toleranceDenominator : Nat
  toleranceDenominator_pos : 0 < toleranceDenominator
  tolerance_eq_numeral :
    numeralInterval.tolerance =
      (toleranceNumerator : ℚ) / (toleranceDenominator : ℚ)
  rootIsolationComputedFromCoefficientLaw : Prop
  rootIsolationComputedFromCoefficientLaw_proof :
    rootIsolationComputedFromCoefficientLaw
  noHiddenRootEncodingInEndpoints : Prop
  noHiddenRootEncodingInEndpoints_proof :
    noHiddenRootEncodingInEndpoints

noncomputable def rationalClosedRootCandidateNumeralEndpointBoundsAsSourceBounds
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G}
  {Psrc : ThreeFlavorCoefficientPositiveSourceAudit}
  (B : ThreeFlavorRationalClosedRootCandidateNumeralEndpointBounds G) :
  ThreeFlavorSourceDerivedEndpointBounds ℚ
    (newSourcePolynomialCoefficientProgramAsCoefficientLaw
      (rationalClosedRootPolynomialCandidateAsCoefficientProgram G Q Psrc)) :=
  { lowerNumerator := B.numeralInterval.lowerNumerator
    lowerDenominator := B.numeralInterval.lowerDenominator
    lowerDenominator_pos := B.numeralInterval.lowerDenominator_pos
    upperNumerator := B.numeralInterval.upperNumerator
    upperDenominator := B.numeralInterval.upperDenominator
    upperDenominator_pos := B.numeralInterval.upperDenominator_pos
    toleranceNumerator := B.toleranceNumerator
    toleranceDenominator := B.toleranceDenominator
    toleranceDenominator_pos := B.toleranceDenominator_pos
    lower := B.numeralInterval.lower
    upper := B.numeralInterval.upper
    tolerance := B.numeralInterval.tolerance
    lower_lt_upper := by
      simpa using B.numeralInterval.lower_lt_upper
    tolerance_pos := by
      simpa using B.numeralInterval.tolerance_pos
    selectedRoot_mem := by
      simpa using B.numeralInterval.selectedRoot_mem
    width_le_tolerance := by
      simpa using B.numeralInterval.width_le_tolerance
    rootIsolationComputedFromCoefficientLaw :=
      B.rootIsolationComputedFromCoefficientLaw
    rootIsolationComputedFromCoefficientLaw_proof :=
      B.rootIsolationComputedFromCoefficientLaw_proof
    noEmpiricalEndpointImport :=
      B.numeralInterval.noEmpiricalEndpointImport
    noEmpiricalEndpointImport_proof :=
      B.numeralInterval.noEmpiricalEndpointImport_proof
    noEndpointFitTuning :=
      B.numeralInterval.noEndpointFitTuning
    noEndpointFitTuning_proof :=
      B.numeralInterval.noEndpointFitTuning_proof
    noHiddenRootEncodingInEndpoints :=
      B.noHiddenRootEncodingInEndpoints
    noHiddenRootEncodingInEndpoints_proof :=
      B.noHiddenRootEncodingInEndpoints_proof }

noncomputable def rationalClosedRootPolynomialCandidateAndNumeralEndpointBoundsAsDecimalWindowCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B : ThreeFlavorRationalClosedRootCandidateNumeralEndpointBounds G)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  ThreeFlavorSourceDerivedRationalDecimalWindowCertificate ℚ G :=
  rationalClosedRootPolynomialCandidateAndEndpointBoundsAsDecimalWindowCertificate
    G
    Q
    Psrc
    (rationalClosedRootCandidateNumeralEndpointBoundsAsSourceBounds
      (G := G) (Q := Q) (Psrc := Psrc) B)
    decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow
    hlabel

theorem rationalClosedRootPolynomialCandidateAndNumeralEndpointBounds_discharge_decimalWindowNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B : ThreeFlavorRationalClosedRootCandidateNumeralEndpointBounds G)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  Not (NeedsThreeFlavorSourceDerivedRationalDecimalWindowCertificate ℚ G) := by
  intro hneed
  exact hneed
    ⟨rationalClosedRootPolynomialCandidateAndNumeralEndpointBoundsAsDecimalWindowCertificate
        G Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel,
      True.intro⟩

theorem rationalClosedRootPolynomialCandidateAndNumeralEndpointBounds_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B : ThreeFlavorRationalClosedRootCandidateNumeralEndpointBounds G)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  (sourceDerivedRationalDecimalWindowAsDecimalWindow
      (rationalClosedRootPolynomialCandidateAndNumeralEndpointBoundsAsDecimalWindowCertificate
        G Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (sourceDerivedRationalDecimalWindowAsDecimalWindow
        (rationalClosedRootPolynomialCandidateAndNumeralEndpointBoundsAsDecimalWindowCertificate
          G Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)).interval.upper :=
  sourceDerivedRationalDecimalWindow_contains_gapRatio
    (rationalClosedRootPolynomialCandidateAndNumeralEndpointBoundsAsDecimalWindowCertificate
      G Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)

/--
Symmetric rational endpoint construction.  This is the first concrete endpoint
builder: once a coefficient-derived rational magnitude bound `B` is certified,
the interval `[-B, B]` is produced with rational numerators/denominators and
tolerance `2B`.
-/
structure ThreeFlavorSymmetricRationalRootBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P) where
  boundNumerator : Nat
  boundNumerator_pos : 0 < boundNumerator
  boundDenominator : Nat
  boundDenominator_pos : 0 < boundDenominator
  bound : ℚ :=
    (boundNumerator : ℚ) / (boundDenominator : ℚ)
  bound_eq_numeral :
    bound = (boundNumerator : ℚ) / (boundDenominator : ℚ)
  selectedRoot_mem_symmetric :
    -bound <= G.selectedRoot /\ G.selectedRoot <= bound
  rootBoundComputedFromCoefficientLaw : Prop
  rootBoundComputedFromCoefficientLaw_proof :
    rootBoundComputedFromCoefficientLaw
  noEmpiricalBoundImport : Prop
  noEmpiricalBoundImport_proof :
    noEmpiricalBoundImport
  noBoundFitTuning : Prop
  noBoundFitTuning_proof :
    noBoundFitTuning
  noHiddenRootEncodingInBound : Prop
  noHiddenRootEncodingInBound_proof :
    noHiddenRootEncodingInBound

/--
Absolute-value root-bound certificate.  This is closer to standard
coefficient-derived root bounds: prove `|selectedRoot| <= B`, then Lean
derives the symmetric interval `[-B, B]`.
-/
structure ThreeFlavorAbsoluteRationalRootBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P) where
  boundNumerator : Nat
  boundNumerator_pos : 0 < boundNumerator
  boundDenominator : Nat
  boundDenominator_pos : 0 < boundDenominator
  bound : ℚ :=
    (boundNumerator : ℚ) / (boundDenominator : ℚ)
  bound_eq_numeral :
    bound = (boundNumerator : ℚ) / (boundDenominator : ℚ)
  abs_selectedRoot_le_bound :
    |G.selectedRoot| <= bound
  rootBoundComputedFromCoefficientLaw : Prop
  rootBoundComputedFromCoefficientLaw_proof :
    rootBoundComputedFromCoefficientLaw
  noEmpiricalBoundImport : Prop
  noEmpiricalBoundImport_proof :
    noEmpiricalBoundImport
  noBoundFitTuning : Prop
  noBoundFitTuning_proof :
    noBoundFitTuning
  noHiddenRootEncodingInBound : Prop
  noHiddenRootEncodingInBound_proof :
    noHiddenRootEncodingInBound

/--
Coefficient-derived absolute root-bound certificate.  This is the local target
for Cauchy/Sturm/other rational root-bound computations: the bound is attached
to the current explicit polynomial and its selected root.
-/
structure ThreeFlavorCoefficientDerivedAbsoluteRootBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P) where
  boundNumerator : Nat
  boundNumerator_pos : 0 < boundNumerator
  boundDenominator : Nat
  boundDenominator_pos : 0 < boundDenominator
  bound : ℚ :=
    (boundNumerator : ℚ) / (boundDenominator : ℚ)
  bound_eq_numeral :
    bound = (boundNumerator : ℚ) / (boundDenominator : ℚ)
  boundTargetsExplicitPolynomial : Prop
  boundTargetsExplicitPolynomial_proof :
    boundTargetsExplicitPolynomial
  selectedRootRootOfExplicitPolynomial :
    G.explicitPolynomial.eval G.selectedRoot = 0
  abs_selectedRoot_le_bound :
    |G.selectedRoot| <= bound
  boundComputedFromCoefficientTable : Prop
  boundComputedFromCoefficientTable_proof :
    boundComputedFromCoefficientTable
  noEmpiricalBoundImport : Prop
  noEmpiricalBoundImport_proof :
    noEmpiricalBoundImport
  noBoundFitTuning : Prop
  noBoundFitTuning_proof :
    noBoundFitTuning
  noHiddenRootEncodingInBound : Prop
  noHiddenRootEncodingInBound_proof :
    noHiddenRootEncodingInBound

/--
Mathlib Cauchy-bound bridge for rational polynomials.

If a rational `x` is a root of a nonzero rational polynomial and a rational
`b` dominates mathlib's Cauchy bound for that polynomial, then `b` bounds the
absolute value of `x`.  This is the first genuinely mathematical readout step:
the bound comes from the polynomial, not from the selected root.
-/
theorem rational_abs_le_of_isRoot_cauchyBound_le
  (poly : Polynomial Rat)
  (hp : poly ≠ 0)
  (x b : Rat)
  (hroot_eval : poly.eval x = 0)
  (hcb : (poly.cauchyBound : Real) <= (b : Real)) :
  |x| <= b := by
  have hroot : poly.IsRoot x := by
    rw [Polynomial.IsRoot.def]
    exact hroot_eval
  have hnn := Polynomial.IsRoot.norm_lt_cauchyBound hp hroot
  have hreal1 : (‖x‖₊ : Real) < (poly.cauchyBound : Real) := by
    exact (NNReal.coe_lt_coe).2 hnn
  have hreal2 : ‖x‖ < (b : Real) := by
    simpa only [coe_nnnorm] using lt_of_lt_of_le hreal1 hcb
  have hreal3 : norm (x : Real) < (b : Real) := by
    simpa only [Rat.norm_cast_real] using hreal2
  have hreal4 : |(x : Real)| < (b : Real) := by
    simpa only [Real.norm_eq_abs] using hreal3
  have hreal5 : ((|x| : Rat) : Real) < (b : Real) := by
    simpa only [Rat.cast_abs] using hreal4
  exact le_of_lt ((Rat.cast_lt (K := Real)).1 hreal5)

/--
Cauchy rational root-bound certificate.

This is stronger than merely asserting an absolute bound: it requires the
rational endpoint to dominate the Cauchy bound of the current explicit
polynomial.  The adapter below turns that into the existing
coefficient-derived absolute-bound object by invoking mathlib's Cauchy theorem.
-/
structure ThreeFlavorCauchyRationalRootBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P) where
  boundNumerator : Nat
  boundNumerator_pos : 0 < boundNumerator
  boundDenominator : Nat
  boundDenominator_pos : 0 < boundDenominator
  bound : ℚ :=
    (boundNumerator : ℚ) / (boundDenominator : ℚ)
  bound_eq_numeral :
    bound = (boundNumerator : ℚ) / (boundDenominator : ℚ)
  explicitPolynomial_ne_zero :
    G.explicitPolynomial ≠ 0
  cauchyBound_le_bound :
    (G.explicitPolynomial.cauchyBound : Real) <= (bound : Real)
  boundTargetsExplicitPolynomial : Prop
  boundTargetsExplicitPolynomial_proof :
    boundTargetsExplicitPolynomial
  cauchyBoundComputedFromCoefficientTable : Prop
  cauchyBoundComputedFromCoefficientTable_proof :
    cauchyBoundComputedFromCoefficientTable
  rationalDominationComputedFromCoefficientTable : Prop
  rationalDominationComputedFromCoefficientTable_proof :
    rationalDominationComputedFromCoefficientTable
  noEmpiricalBoundImport : Prop
  noEmpiricalBoundImport_proof :
    noEmpiricalBoundImport
  noBoundFitTuning : Prop
  noBoundFitTuning_proof :
    noBoundFitTuning
  noHiddenRootEncodingInBound : Prop
  noHiddenRootEncodingInBound_proof :
    noHiddenRootEncodingInBound

/--
Source-candidate Cauchy bound.

This is the concrete-entry version of `ThreeFlavorCauchyRationalRootBound`.
The Cauchy domination is stated for the source polynomial carried by a
`ThreeFlavorSourceRationalPolynomialCandidate`; Lean then transports it across
the extensional equality to the current closed-root polynomial.
-/
structure ThreeFlavorSourcePolynomialCauchyRationalBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G) where
  boundNumerator : Nat
  boundNumerator_pos : 0 < boundNumerator
  boundDenominator : Nat
  boundDenominator_pos : 0 < boundDenominator
  bound : ℚ :=
    (boundNumerator : ℚ) / (boundDenominator : ℚ)
  bound_eq_numeral :
    bound = (boundNumerator : ℚ) / (boundDenominator : ℚ)
  sourceCauchyBound_le_bound :
    (Q.sourcePolynomial.cauchyBound : Real) <= (bound : Real)
  cauchyBoundComputedFromSourceCoefficients : Prop
  cauchyBoundComputedFromSourceCoefficients_proof :
    cauchyBoundComputedFromSourceCoefficients
  rationalDominationComputedFromSourceCoefficients : Prop
  rationalDominationComputedFromSourceCoefficients_proof :
    rationalDominationComputedFromSourceCoefficients
  noEmpiricalBoundImport : Prop
  noEmpiricalBoundImport_proof :
    noEmpiricalBoundImport
  noBoundFitTuning : Prop
  noBoundFitTuning_proof :
    noBoundFitTuning
  noHiddenRootEncodingInBound : Prop
  noHiddenRootEncodingInBound_proof :
    noHiddenRootEncodingInBound

noncomputable def sourcePolynomialCauchyBoundAsClosedRootCauchyBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G}
  (B : ThreeFlavorSourcePolynomialCauchyRationalBound Q) :
  ThreeFlavorCauchyRationalRootBound G := by
  have hpoly_eq : Q.sourcePolynomial = G.explicitPolynomial := by
    simpa using Q.sourcePolynomial_maps_to_closedRoot
  have hsource_coeff_ne :
      Q.sourcePolynomial.coeff Q.witnessDegree ≠ 0 := by
    intro hzero
    exact Q.mappedWitnessCoefficient_ne_zero (by rw [hzero]; simp)
  have hsource_ne : Q.sourcePolynomial ≠ 0 := by
    intro hzero
    exact hsource_coeff_ne (by rw [hzero]; simp)
  exact
  { boundNumerator := B.boundNumerator
    boundNumerator_pos := B.boundNumerator_pos
    boundDenominator := B.boundDenominator
    boundDenominator_pos := B.boundDenominator_pos
    bound := B.bound
    bound_eq_numeral := B.bound_eq_numeral
    explicitPolynomial_ne_zero := by
      simpa [hpoly_eq] using hsource_ne
    cauchyBound_le_bound := by
      simpa [hpoly_eq] using B.sourceCauchyBound_le_bound
    boundTargetsExplicitPolynomial :=
      Q.sourcePolynomialSourceDerived
    boundTargetsExplicitPolynomial_proof :=
      Q.sourcePolynomialSourceDerived_proof
    cauchyBoundComputedFromCoefficientTable :=
      B.cauchyBoundComputedFromSourceCoefficients
    cauchyBoundComputedFromCoefficientTable_proof :=
      B.cauchyBoundComputedFromSourceCoefficients_proof
    rationalDominationComputedFromCoefficientTable :=
      B.rationalDominationComputedFromSourceCoefficients
    rationalDominationComputedFromCoefficientTable_proof :=
      B.rationalDominationComputedFromSourceCoefficients_proof
    noEmpiricalBoundImport := B.noEmpiricalBoundImport
    noEmpiricalBoundImport_proof := B.noEmpiricalBoundImport_proof
    noBoundFitTuning := B.noBoundFitTuning
    noBoundFitTuning_proof := B.noBoundFitTuning_proof
    noHiddenRootEncodingInBound :=
      Q.coefficientsDoNotEncodeSelectedRoot /\
        B.noHiddenRootEncodingInBound
    noHiddenRootEncodingInBound_proof :=
      ⟨Q.coefficientsDoNotEncodeSelectedRoot_proof,
        B.noHiddenRootEncodingInBound_proof⟩ }

noncomputable def closedRootCauchyBoundAsSourcePolynomialCauchyBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G)
  (B : ThreeFlavorCauchyRationalRootBound G) :
  ThreeFlavorSourcePolynomialCauchyRationalBound Q := by
  have hpoly_eq : Q.sourcePolynomial = G.explicitPolynomial := by
    simpa using Q.sourcePolynomial_maps_to_closedRoot
  exact
  { boundNumerator := B.boundNumerator
    boundNumerator_pos := B.boundNumerator_pos
    boundDenominator := B.boundDenominator
    boundDenominator_pos := B.boundDenominator_pos
    bound := B.bound
    bound_eq_numeral := B.bound_eq_numeral
    sourceCauchyBound_le_bound := by
      simpa [hpoly_eq] using B.cauchyBound_le_bound
    cauchyBoundComputedFromSourceCoefficients :=
      B.cauchyBoundComputedFromCoefficientTable
    cauchyBoundComputedFromSourceCoefficients_proof :=
      B.cauchyBoundComputedFromCoefficientTable_proof
    rationalDominationComputedFromSourceCoefficients :=
      B.rationalDominationComputedFromCoefficientTable
    rationalDominationComputedFromSourceCoefficients_proof :=
      B.rationalDominationComputedFromCoefficientTable_proof
    noEmpiricalBoundImport := B.noEmpiricalBoundImport
    noEmpiricalBoundImport_proof := B.noEmpiricalBoundImport_proof
    noBoundFitTuning := B.noBoundFitTuning
    noBoundFitTuning_proof := B.noBoundFitTuning_proof
    noHiddenRootEncodingInBound :=
      B.noHiddenRootEncodingInBound /\
        Q.coefficientsDoNotEncodeSelectedRoot
    noHiddenRootEncodingInBound_proof :=
      ⟨B.noHiddenRootEncodingInBound_proof,
        Q.coefficientsDoNotEncodeSelectedRoot_proof⟩ }

noncomputable def sourcePolynomialCauchyBoundAsEndpointBounds
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B : ThreeFlavorSourcePolynomialCauchyRationalBound Q) :
  ThreeFlavorSourceDerivedEndpointBounds ℚ
    (newSourcePolynomialCoefficientProgramAsCoefficientLaw
      (sourceRationalPolynomialCandidateAsCoefficientProgram Q Psrc)) := by
  let CB : ThreeFlavorCauchyRationalRootBound G :=
    sourcePolynomialCauchyBoundAsClosedRootCauchyBound B
  have hbound_pos : (0 : ℚ) < B.bound := by
    rw [B.bound_eq_numeral]
    exact div_pos
      (by exact_mod_cast B.boundNumerator_pos)
      (by exact_mod_cast B.boundDenominator_pos)
  have hroot_abs : |G.selectedRoot| <= B.bound :=
    rational_abs_le_of_isRoot_cauchyBound_le
      G.explicitPolynomial
      CB.explicitPolynomial_ne_zero
      G.selectedRoot
      B.bound
      G.selectedRoot_is_root
      CB.cauchyBound_le_bound
  exact
  { lowerNumerator := -((B.boundNumerator : Int))
    lowerDenominator := B.boundDenominator
    lowerDenominator_pos := B.boundDenominator_pos
    upperNumerator := B.boundNumerator
    upperDenominator := B.boundDenominator
    upperDenominator_pos := B.boundDenominator_pos
    toleranceNumerator := 2 * B.boundNumerator
    toleranceDenominator := B.boundDenominator
    toleranceDenominator_pos := B.boundDenominator_pos
    lower := -B.bound
    upper := B.bound
    tolerance := 2 * B.bound
    lower_lt_upper := by
      change -B.bound < B.bound
      linarith
    tolerance_pos := by
      change (0 : ℚ) < 2 * B.bound
      linarith
    selectedRoot_mem := by
      exact abs_le.mp hroot_abs
    width_le_tolerance := by
      change B.bound - (-B.bound) <= 2 * B.bound
      ring_nf
      exact le_rfl
    rootIsolationComputedFromCoefficientLaw :=
      B.cauchyBoundComputedFromSourceCoefficients /\
        B.rationalDominationComputedFromSourceCoefficients
    rootIsolationComputedFromCoefficientLaw_proof :=
      ⟨B.cauchyBoundComputedFromSourceCoefficients_proof,
        B.rationalDominationComputedFromSourceCoefficients_proof⟩
    noEmpiricalEndpointImport := B.noEmpiricalBoundImport
    noEmpiricalEndpointImport_proof := B.noEmpiricalBoundImport_proof
    noEndpointFitTuning := B.noBoundFitTuning
    noEndpointFitTuning_proof := B.noBoundFitTuning_proof
    noHiddenRootEncodingInEndpoints :=
      Q.coefficientsDoNotEncodeSelectedRoot /\
        B.noHiddenRootEncodingInBound
    noHiddenRootEncodingInEndpoints_proof :=
      ⟨Q.coefficientsDoNotEncodeSelectedRoot_proof,
        B.noHiddenRootEncodingInBound_proof⟩ }

noncomputable def sourceRationalPolynomialCandidateAndCauchyBoundAsDecimalWindowCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B : ThreeFlavorSourcePolynomialCauchyRationalBound Q)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  ThreeFlavorSourceDerivedRationalDecimalWindowCertificate ℚ G :=
  sourceRationalPolynomialCandidateAndEndpointBoundsAsDecimalWindowCertificate
    Q
    Psrc
    (sourcePolynomialCauchyBoundAsEndpointBounds Q Psrc B)
    decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow
    hlabel

theorem sourceRationalPolynomialCandidateAndCauchyBound_discharge_decimalWindowNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B : ThreeFlavorSourcePolynomialCauchyRationalBound Q)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  Not (NeedsThreeFlavorSourceDerivedRationalDecimalWindowCertificate ℚ G) :=
  sourceRationalPolynomialCandidateAndEndpointBounds_discharge_decimalWindowNeed
    Q
    Psrc
    (sourcePolynomialCauchyBoundAsEndpointBounds Q Psrc B)
    decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow
    hlabel

theorem sourceRationalPolynomialCandidateAndCauchyBound_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B : ThreeFlavorSourcePolynomialCauchyRationalBound Q)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  (sourceDerivedRationalDecimalWindowAsDecimalWindow
      (sourceRationalPolynomialCandidateAndCauchyBoundAsDecimalWindowCertificate
        Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (sourceDerivedRationalDecimalWindowAsDecimalWindow
        (sourceRationalPolynomialCandidateAndCauchyBoundAsDecimalWindowCertificate
          Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)).interval.upper :=
  sourceDerivedRationalDecimalWindow_contains_gapRatio
    (sourceRationalPolynomialCandidateAndCauchyBoundAsDecimalWindowCertificate
      Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)

/--
QNF-specialized Cauchy decimal-window route.

Once a quotient-normal-form interior law has been aligned with the rational
closed-root presentation, a Cauchy domination certificate for the induced
source polynomial gives the same source-derived decimal-window certificate.
-/
noncomputable def quotientNormalFormInteriorLawAndCauchyBoundAsDecimalWindowCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A)
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B :
    ThreeFlavorSourcePolynomialCauchyRationalBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate G Q L))
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  ThreeFlavorSourceDerivedRationalDecimalWindowCertificate ℚ G :=
  sourceRationalPolynomialCandidateAndCauchyBoundAsDecimalWindowCertificate
    (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate G Q L)
    Psrc
    B
    decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow
    hlabel

theorem quotientNormalFormInteriorLawAndCauchyBound_discharge_decimalWindowNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A)
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B :
    ThreeFlavorSourcePolynomialCauchyRationalBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate G Q L))
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  Not (NeedsThreeFlavorSourceDerivedRationalDecimalWindowCertificate ℚ G) :=
  sourceRationalPolynomialCandidateAndCauchyBound_discharge_decimalWindowNeed
    (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate G Q L)
    Psrc
    B
    decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow
    hlabel

theorem quotientNormalFormInteriorLawAndCauchyBound_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A)
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B :
    ThreeFlavorSourcePolynomialCauchyRationalBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate G Q L))
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  (sourceDerivedRationalDecimalWindowAsDecimalWindow
      (quotientNormalFormInteriorLawAndCauchyBoundAsDecimalWindowCertificate
        G Q L Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (sourceDerivedRationalDecimalWindowAsDecimalWindow
        (quotientNormalFormInteriorLawAndCauchyBoundAsDecimalWindowCertificate
          G Q L Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)).interval.upper :=
  sourceDerivedRationalDecimalWindow_contains_gapRatio
    (quotientNormalFormInteriorLawAndCauchyBoundAsDecimalWindowCertificate
      G Q L Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)

/--
QNF-specialized positive readout route.

This is the first named route from a quotient-normal-form interior law to a
positive rational readout window.  It inherits the coefficient-derived upper
endpoint from the QNF-induced source polynomial and clips the lower endpoint
to `0` only after the standing/minimal-interval sign orientation is supplied.
-/
noncomputable def quotientNormalFormInteriorLawAndCauchyBoundAsPositiveReadoutWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A)
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B :
    ThreeFlavorSourcePolynomialCauchyRationalBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate G Q L))
  (S : ThreeFlavorPositiveStandingRootReadout G)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  ThreeFlavorClosedRootDecimalWindow ℚ G :=
  sourceDerivedRationalDecimalWindowAsPositiveReadoutWindow
    (quotientNormalFormInteriorLawAndCauchyBoundAsDecimalWindowCertificate
      G Q L Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)
    S

theorem quotientNormalFormInteriorLawAndCauchyBound_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A)
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B :
    ThreeFlavorSourcePolynomialCauchyRationalBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate G Q L))
  (S : ThreeFlavorPositiveStandingRootReadout G)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow G) :=
  sourceDerivedRationalDecimalWindowAndPositiveStandingReadout_discharge_positiveReadoutNeed
    (quotientNormalFormInteriorLawAndCauchyBoundAsDecimalWindowCertificate
      G Q L Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)
    S

theorem quotientNormalFormInteriorLawAndCauchyBound_positiveReadout_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A)
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B :
    ThreeFlavorSourcePolynomialCauchyRationalBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate G Q L))
  (S : ThreeFlavorPositiveStandingRootReadout G)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  (quotientNormalFormInteriorLawAndCauchyBoundAsPositiveReadoutWindow
      G Q L Psrc B S decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (quotientNormalFormInteriorLawAndCauchyBoundAsPositiveReadoutWindow
        G Q L Psrc B S decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel).interval.upper :=
  sourceDerivedRationalDecimalWindow_positiveReadout_contains_gapRatio
    (quotientNormalFormInteriorLawAndCauchyBoundAsDecimalWindowCertificate
      G Q L Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)
    S

/--
Bundled QNF positive-readout payload.

This is the reduced target object for the next construction step.  Instead of
tracking the QNF law, alignment, source audit, Cauchy bound, positivity witness,
and label certification as loose arguments, the numerical-readout layer can now
ask for one payload.
-/
structure ThreeFlavorQNFPositiveReadoutPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P) where
  qnfLaw : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A
  rationalPolynomialAlignment :
    ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G qnfLaw
  sourceAudit : ThreeFlavorCoefficientPositiveSourceAudit
  cauchyBound :
    ThreeFlavorSourcePolynomialCauchyRationalBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        G qnfLaw rationalPolynomialAlignment)
  positiveStandingReadout : ThreeFlavorPositiveStandingRootReadout G
  decimalLabel : String
  decimalLabelCertifiedBySourceDerivedWindow : Prop
  decimalLabelCertifiedBySourceDerivedWindow_proof :
    decimalLabelCertifiedBySourceDerivedWindow

noncomputable def qnfPositiveReadoutPayloadAsPositiveReadoutWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (W : ThreeFlavorQNFPositiveReadoutPayload G) :
  ThreeFlavorClosedRootDecimalWindow ℚ G :=
  quotientNormalFormInteriorLawAndCauchyBoundAsPositiveReadoutWindow
    G
    W.qnfLaw
    W.rationalPolynomialAlignment
    W.sourceAudit
    W.cauchyBound
    W.positiveStandingReadout
    W.decimalLabel
    W.decimalLabelCertifiedBySourceDerivedWindow
    W.decimalLabelCertifiedBySourceDerivedWindow_proof

theorem qnfPositiveReadoutPayload_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (W : ThreeFlavorQNFPositiveReadoutPayload G) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow G) :=
  quotientNormalFormInteriorLawAndCauchyBound_discharge_positiveReadoutNeed
    G
    W.qnfLaw
    W.rationalPolynomialAlignment
    W.sourceAudit
    W.cauchyBound
    W.positiveStandingReadout
    W.decimalLabel
    W.decimalLabelCertifiedBySourceDerivedWindow
    W.decimalLabelCertifiedBySourceDerivedWindow_proof

theorem qnfPositiveReadoutPayload_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (W : ThreeFlavorQNFPositiveReadoutPayload G) :
  (qnfPositiveReadoutPayloadAsPositiveReadoutWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (qnfPositiveReadoutPayloadAsPositiveReadoutWindow W).interval.upper :=
  quotientNormalFormInteriorLawAndCauchyBound_positiveReadout_contains_gapRatio
    G
    W.qnfLaw
    W.rationalPolynomialAlignment
    W.sourceAudit
    W.cauchyBound
    W.positiveStandingReadout
    W.decimalLabel
    W.decimalLabelCertifiedBySourceDerivedWindow
    W.decimalLabelCertifiedBySourceDerivedWindow_proof

/--
Canonical QNF positive-readout input bundle.

This is the smaller next target after the canonical alignment result: it no
longer asks the paper to supply an arbitrary QNF law or arbitrary QNF
alignment.  Those are generated from the same-scope closed-root package and a
focused polynomial audit.
-/
structure ThreeFlavorCanonicalQNFPositiveReadoutInputs
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P) where
  polynomialAudit : ThreeFlavorCanonicalSameScopeQNFPolynomialAudit G
  sourceAudit : ThreeFlavorCoefficientPositiveSourceAudit
  cauchyBound :
    ThreeFlavorSourcePolynomialCauchyRationalBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        G
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment G polynomialAudit))
  positiveStandingReadout : ThreeFlavorPositiveStandingRootReadout G
  decimalLabel : String
  decimalLabelCertifiedBySourceDerivedWindow : Prop
  decimalLabelCertifiedBySourceDerivedWindow_proof :
    decimalLabelCertifiedBySourceDerivedWindow

noncomputable def canonicalQNFPositiveReadoutInputsAsPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (W : ThreeFlavorCanonicalQNFPositiveReadoutInputs G) :
  ThreeFlavorQNFPositiveReadoutPayload G :=
  { qnfLaw := sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P
    rationalPolynomialAlignment :=
      canonicalSameScopeQNFPolynomialAuditAsAlignment G W.polynomialAudit
    sourceAudit := W.sourceAudit
    cauchyBound := W.cauchyBound
    positiveStandingReadout := W.positiveStandingReadout
    decimalLabel := W.decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow :=
      W.decimalLabelCertifiedBySourceDerivedWindow
    decimalLabelCertifiedBySourceDerivedWindow_proof :=
      W.decimalLabelCertifiedBySourceDerivedWindow_proof }

noncomputable def canonicalQNFPositiveReadoutInputsAsPositiveReadoutWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (W : ThreeFlavorCanonicalQNFPositiveReadoutInputs G) :
  ThreeFlavorClosedRootDecimalWindow ℚ G :=
  qnfPositiveReadoutPayloadAsPositiveReadoutWindow
    (canonicalQNFPositiveReadoutInputsAsPayload W)

theorem canonicalQNFPositiveReadoutInputs_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (W : ThreeFlavorCanonicalQNFPositiveReadoutInputs G) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow G) :=
  qnfPositiveReadoutPayload_discharge_positiveReadoutNeed
    (canonicalQNFPositiveReadoutInputsAsPayload W)

theorem canonicalQNFPositiveReadoutInputs_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (W : ThreeFlavorCanonicalQNFPositiveReadoutInputs G) :
  (canonicalQNFPositiveReadoutInputsAsPositiveReadoutWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalQNFPositiveReadoutInputsAsPositiveReadoutWindow W).interval.upper :=
  qnfPositiveReadoutPayload_contains_gapRatio
    (canonicalQNFPositiveReadoutInputsAsPayload W)

/--
Nonlinear audit for the same-scope polynomial itself.

When the algebraic presentation is the canonical one produced from the
same-scope package, the polynomial-alignment equality is definitional.  The
remaining anti-tautology content is just a genuine high-degree nonzero
coefficient plus the no-hidden-selected-root audit.
-/
structure ThreeFlavorSameScopePolynomialNonlinearAudit
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  witnessDegree : ℕ
  witnessDegree_ge_two :
    2 ≤ witnessDegree
  witnessCoefficient_ne_zero :
    P.sameScopePredicate.polynomial.coeff witnessDegree ≠ 0
  coefficientsDoNotEncodeSelectedRoot : Prop
  coefficientsDoNotEncodeSelectedRoot_proof :
    coefficientsDoNotEncodeSelectedRoot

/--
Slim same-scope polynomial nonlinearity audit.

The only local coefficient fact is a nonzero coefficient in degree at least
two.  The no-hidden-selected-root coefficient audit is inherited from the
same-scope package's no-one-anchor and no-extra-root-selector controls.
-/
structure ThreeFlavorSameScopePolynomialHighCoefficient
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  witnessDegree : ℕ
  witnessDegree_ge_two :
    2 ≤ witnessDegree
  witnessCoefficient_ne_zero :
    P.sameScopePredicate.polynomial.coeff witnessDegree ≠ 0

/--
Source-audited same-scope high coefficient.

This is the next reduction of the high-coefficient side of the readout
payload: the local arithmetic fact is still just a nonzero coefficient in
degree at least two, but the witness is now explicitly recorded as
source-derived rather than merely present.
-/
structure ThreeFlavorSameScopeSourceHighCoefficient
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  witnessDegree : ℕ
  witnessDegree_ge_two :
    2 ≤ witnessDegree
  witnessCoefficient_ne_zero :
    P.sameScopePredicate.polynomial.coeff witnessDegree ≠ 0
  highCoefficientSourceDerived : Prop
  highCoefficientSourceDerived_proof :
    highCoefficientSourceDerived

/--
Package-derived source high coefficient.

The nonzero high coefficient remains explicit, but its source-derivation audit
is generated from the ambient same-scope polynomial law rather than supplied as
an independent proposition.
-/
structure ThreeFlavorPackageSourceHighCoefficient
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  witnessDegree : ℕ
  witnessDegree_ge_two :
    2 ≤ witnessDegree
  witnessCoefficient_ne_zero :
    P.sameScopePredicate.polynomial.coeff witnessDegree ≠ 0

def packageSourceHighCoefficientAsSourceHighCoefficient
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackageSourceHighCoefficient P) :
  ThreeFlavorSameScopeSourceHighCoefficient P :=
  { witnessDegree := K.witnessDegree
    witnessDegree_ge_two := K.witnessDegree_ge_two
    witnessCoefficient_ne_zero := K.witnessCoefficient_ne_zero
    highCoefficientSourceDerived :=
      P.polynomialLaw.polynomialLawDerivedInternally
    highCoefficientSourceDerived_proof :=
      P.polynomialLaw.polynomialLawDerivedInternally_proof }

def sameScopeSourceHighCoefficientAsHighCoefficient
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorSameScopeSourceHighCoefficient P) :
  ThreeFlavorSameScopePolynomialHighCoefficient P :=
  { witnessDegree := K.witnessDegree
    witnessDegree_ge_two := K.witnessDegree_ge_two
    witnessCoefficient_ne_zero := K.witnessCoefficient_ne_zero }

def sameScopePolynomialHighCoefficientAsNonlinearAudit
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A)
  (K : ThreeFlavorSameScopePolynomialHighCoefficient P) :
  ThreeFlavorSameScopePolynomialNonlinearAudit P :=
  { witnessDegree := K.witnessDegree
    witnessDegree_ge_two := K.witnessDegree_ge_two
    witnessCoefficient_ne_zero := K.witnessCoefficient_ne_zero
    coefficientsDoNotEncodeSelectedRoot :=
      P.polynomialLaw.noOneAnchorImport /\
        P.sameScopePredicate.noExtraRootSelector
    coefficientsDoNotEncodeSelectedRoot_proof :=
      ⟨P.polynomialLaw.noOneAnchorImport_proof,
        P.sameScopePredicate.noExtraRootSelector_proof⟩ }

def sameScopePolynomialNonlinearAuditAsCanonicalQNFPolynomialAudit
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A)
  (U : ThreeFlavorSameScopePolynomialNonlinearAudit P) :
  ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  { sameScopePolynomial_eq_closedRoot := rfl
    witnessDegree := U.witnessDegree
    witnessDegree_ge_two := U.witnessDegree_ge_two
    witnessCoefficient_ne_zero := U.witnessCoefficient_ne_zero
    coefficientsDoNotEncodeSelectedRoot :=
      U.coefficientsDoNotEncodeSelectedRoot
    coefficientsDoNotEncodeSelectedRoot_proof :=
      U.coefficientsDoNotEncodeSelectedRoot_proof }

/--
Canonical-presentation QNF readout inputs.

This is a further reduction of the target: the algebraic presentation is fixed
to the canonical presentation built from the same-scope package, so no
presentation equality has to be supplied.
-/
structure ThreeFlavorCanonicalPresentationQNFPositiveReadoutInputs
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  polynomialNonlinearAudit :
    ThreeFlavorSameScopePolynomialNonlinearAudit P
  sourceAudit : ThreeFlavorCoefficientPositiveSourceAudit
  cauchyBound :
    ThreeFlavorSourcePolynomialCauchyRationalBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
          (sameScopePolynomialNonlinearAuditAsCanonicalQNFPolynomialAudit
            P polynomialNonlinearAudit)))
  positiveStandingReadout :
    ThreeFlavorPositiveStandingRootReadout
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
  decimalLabel : String
  decimalLabelCertifiedBySourceDerivedWindow : Prop
  decimalLabelCertifiedBySourceDerivedWindow_proof :
    decimalLabelCertifiedBySourceDerivedWindow

noncomputable def canonicalPresentationQNFPositiveReadoutInputsAsCanonicalInputs
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalPresentationQNFPositiveReadoutInputs P) :
  ThreeFlavorCanonicalQNFPositiveReadoutInputs
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  { polynomialAudit :=
      sameScopePolynomialNonlinearAuditAsCanonicalQNFPolynomialAudit
        P W.polynomialNonlinearAudit
    sourceAudit := W.sourceAudit
    cauchyBound := W.cauchyBound
    positiveStandingReadout := W.positiveStandingReadout
    decimalLabel := W.decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow :=
      W.decimalLabelCertifiedBySourceDerivedWindow
    decimalLabelCertifiedBySourceDerivedWindow_proof :=
      W.decimalLabelCertifiedBySourceDerivedWindow_proof }

noncomputable def canonicalPresentationQNFPositiveReadoutInputsAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalPresentationQNFPositiveReadoutInputs P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalQNFPositiveReadoutInputsAsPositiveReadoutWindow
    (canonicalPresentationQNFPositiveReadoutInputsAsCanonicalInputs W)

theorem canonicalPresentationQNFPositiveReadoutInputs_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalPresentationQNFPositiveReadoutInputs P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalQNFPositiveReadoutInputs_discharge_positiveReadoutNeed
    (canonicalPresentationQNFPositiveReadoutInputsAsCanonicalInputs W)

theorem canonicalPresentationQNFPositiveReadoutInputs_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalPresentationQNFPositiveReadoutInputs P) :
  (canonicalPresentationQNFPositiveReadoutInputsAsWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalPresentationQNFPositiveReadoutInputsAsWindow W).interval.upper :=
  canonicalQNFPositiveReadoutInputs_contains_gapRatio
    (canonicalPresentationQNFPositiveReadoutInputsAsCanonicalInputs W)

/--
Canonical presentation readout inputs with the positive source audit inherited
from the same-scope package.

This is the smallest current readout target: source-audit bookkeeping is no
longer an input.  The remaining fields are the genuinely finite pieces: a
nonlinear coefficient audit, a coefficient-derived Cauchy bound, and a
standing sign orientation.
-/
structure ThreeFlavorCanonicalFiniteReadoutPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  polynomialNonlinearAudit :
    ThreeFlavorSameScopePolynomialNonlinearAudit P
  cauchyBound :
    ThreeFlavorSourcePolynomialCauchyRationalBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
          (sameScopePolynomialNonlinearAuditAsCanonicalQNFPolynomialAudit
            P polynomialNonlinearAudit)))
  positiveStandingReadout :
    ThreeFlavorPositiveStandingRootReadout
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
  decimalLabel : String
  decimalLabelCertifiedBySourceDerivedWindow : Prop
  decimalLabelCertifiedBySourceDerivedWindow_proof :
    decimalLabelCertifiedBySourceDerivedWindow

noncomputable def canonicalFiniteReadoutPayloadAsCanonicalPresentationInputs
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalFiniteReadoutPayload P) :
  ThreeFlavorCanonicalPresentationQNFPositiveReadoutInputs P :=
  { polynomialNonlinearAudit := W.polynomialNonlinearAudit
    sourceAudit := sameScopePackageAsCoefficientPositiveSourceAudit P
    cauchyBound := W.cauchyBound
    positiveStandingReadout := W.positiveStandingReadout
    decimalLabel := W.decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow :=
      W.decimalLabelCertifiedBySourceDerivedWindow
    decimalLabelCertifiedBySourceDerivedWindow_proof :=
      W.decimalLabelCertifiedBySourceDerivedWindow_proof }

noncomputable def canonicalFiniteReadoutPayloadAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalFiniteReadoutPayload P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalPresentationQNFPositiveReadoutInputsAsWindow
    (canonicalFiniteReadoutPayloadAsCanonicalPresentationInputs W)

theorem canonicalFiniteReadoutPayload_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalFiniteReadoutPayload P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalPresentationQNFPositiveReadoutInputs_discharge_positiveReadoutNeed
    (canonicalFiniteReadoutPayloadAsCanonicalPresentationInputs W)

theorem canonicalFiniteReadoutPayload_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalFiniteReadoutPayload P) :
  (canonicalFiniteReadoutPayloadAsWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalFiniteReadoutPayloadAsWindow W).interval.upper :=
  canonicalPresentationQNFPositiveReadoutInputs_contains_gapRatio
    (canonicalFiniteReadoutPayloadAsCanonicalPresentationInputs W)

/--
Canonical Cauchy domination payload.

This is slightly weaker than `ThreeFlavorCauchyRationalRootBound`: it asks only
for a rational endpoint that dominates the Cauchy bound.  The nonzero-polynomial
fact is derived separately from the nonlinear coefficient audit.
-/
structure ThreeFlavorCanonicalCauchyDominationPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  boundNumerator : Nat
  boundNumerator_pos : 0 < boundNumerator
  boundDenominator : Nat
  boundDenominator_pos : 0 < boundDenominator
  bound : ℚ :=
    (boundNumerator : ℚ) / (boundDenominator : ℚ)
  bound_eq_numeral :
    bound = (boundNumerator : ℚ) / (boundDenominator : ℚ)
  cauchyBound_le_bound :
    ((sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P).explicitPolynomial.cauchyBound : Real) <=
      (bound : Real)
  boundTargetsExplicitPolynomial : Prop
  boundTargetsExplicitPolynomial_proof :
    boundTargetsExplicitPolynomial
  cauchyBoundComputedFromCoefficientTable : Prop
  cauchyBoundComputedFromCoefficientTable_proof :
    cauchyBoundComputedFromCoefficientTable
  rationalDominationComputedFromCoefficientTable : Prop
  rationalDominationComputedFromCoefficientTable_proof :
    rationalDominationComputedFromCoefficientTable
  noEmpiricalBoundImport : Prop
  noEmpiricalBoundImport_proof :
    noEmpiricalBoundImport
  noBoundFitTuning : Prop
  noBoundFitTuning_proof :
    noBoundFitTuning
  noHiddenRootEncodingInBound : Prop
  noHiddenRootEncodingInBound_proof :
    noHiddenRootEncodingInBound

/--
Slim Cauchy domination payload.

This removes the separate no-hidden-root-in-bound field.  For this canonical
route, a bound certified as computed from the coefficient table and its
rational domination is enough to generate that audit field.
-/
structure ThreeFlavorCanonicalSlimCauchyDominationPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  boundNumerator : Nat
  boundNumerator_pos : 0 < boundNumerator
  boundDenominator : Nat
  boundDenominator_pos : 0 < boundDenominator
  bound : ℚ :=
    (boundNumerator : ℚ) / (boundDenominator : ℚ)
  bound_eq_numeral :
    bound = (boundNumerator : ℚ) / (boundDenominator : ℚ)
  cauchyBound_le_bound :
    ((sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P).explicitPolynomial.cauchyBound : Real) <=
      (bound : Real)
  boundTargetsExplicitPolynomial : Prop
  boundTargetsExplicitPolynomial_proof :
    boundTargetsExplicitPolynomial
  cauchyBoundComputedFromCoefficientTable : Prop
  cauchyBoundComputedFromCoefficientTable_proof :
    cauchyBoundComputedFromCoefficientTable
  rationalDominationComputedFromCoefficientTable : Prop
  rationalDominationComputedFromCoefficientTable_proof :
    rationalDominationComputedFromCoefficientTable
  noEmpiricalBoundImport : Prop
  noEmpiricalBoundImport_proof :
    noEmpiricalBoundImport
  noBoundFitTuning : Prop
  noBoundFitTuning_proof :
    noBoundFitTuning

/--
Bare canonical Cauchy domination payload.

This is the finite arithmetic core of the Cauchy side: a rational endpoint,
its domination of the polynomial Cauchy bound, and proof that this domination
was computed from the coefficient table.  Empirical/no-fit audit metadata is
inherited from the same-scope package by the adapter below.
-/
structure ThreeFlavorCanonicalBareCauchyDominationPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  boundNumerator : Nat
  boundNumerator_pos : 0 < boundNumerator
  boundDenominator : Nat
  boundDenominator_pos : 0 < boundDenominator
  bound : ℚ :=
    (boundNumerator : ℚ) / (boundDenominator : ℚ)
  bound_eq_numeral :
    bound = (boundNumerator : ℚ) / (boundDenominator : ℚ)
  cauchyBound_le_bound :
    ((sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P).explicitPolynomial.cauchyBound : Real) <=
      (bound : Real)
  boundTargetsExplicitPolynomial : Prop
  boundTargetsExplicitPolynomial_proof :
    boundTargetsExplicitPolynomial
  cauchyBoundComputedFromCoefficientTable : Prop
  cauchyBoundComputedFromCoefficientTable_proof :
    cauchyBoundComputedFromCoefficientTable
  rationalDominationComputedFromCoefficientTable : Prop
  rationalDominationComputedFromCoefficientTable_proof :
    rationalDominationComputedFromCoefficientTable

/--
Arithmetic-only Cauchy domination payload.

For the canonical presentation, targeting the explicit polynomial is inherited
from the same-scope polynomial package.  This payload keeps only the rational
endpoint, Cauchy domination, and the finite coefficient-computation audits.
-/
structure ThreeFlavorCanonicalArithmeticCauchyDomination
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  boundNumerator : Nat
  boundNumerator_pos : 0 < boundNumerator
  boundDenominator : Nat
  boundDenominator_pos : 0 < boundDenominator
  bound : ℚ :=
    (boundNumerator : ℚ) / (boundDenominator : ℚ)
  bound_eq_numeral :
    bound = (boundNumerator : ℚ) / (boundDenominator : ℚ)
  cauchyBound_le_bound :
    ((sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P).explicitPolynomial.cauchyBound : Real) <=
      (bound : Real)
  cauchyBoundComputedFromCoefficientTable : Prop
  cauchyBoundComputedFromCoefficientTable_proof :
    cauchyBoundComputedFromCoefficientTable
  rationalDominationComputedFromCoefficientTable : Prop
  rationalDominationComputedFromCoefficientTable_proof :
    rationalDominationComputedFromCoefficientTable

/--
Source-arithmetic Cauchy domination.

This compacts the two Cauchy-side computation audits into one source-arithmetic
audit: the displayed rational endpoint and its domination of the Cauchy bound
are certified as a single coefficient-table computation.
-/
structure ThreeFlavorCanonicalSourceArithmeticCauchyDomination
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  boundNumerator : Nat
  boundNumerator_pos : 0 < boundNumerator
  boundDenominator : Nat
  boundDenominator_pos : 0 < boundDenominator
  bound : ℚ :=
    (boundNumerator : ℚ) / (boundDenominator : ℚ)
  bound_eq_numeral :
    bound = (boundNumerator : ℚ) / (boundDenominator : ℚ)
  cauchyBound_le_bound :
    ((sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P).explicitPolynomial.cauchyBound : Real) <=
      (bound : Real)
  sourceArithmeticCauchyComputation : Prop
  sourceArithmeticCauchyComputation_proof :
    sourceArithmeticCauchyComputation

/--
Package-derived source-arithmetic Cauchy domination.

The rational endpoint and domination inequality remain local arithmetic data;
the source-arithmetic computation audit is generated from the ambient
same-scope package's internally derived polynomial law.
-/
structure ThreeFlavorPackageSourceArithmeticCauchyDomination
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  boundNumerator : Nat
  boundNumerator_pos : 0 < boundNumerator
  boundDenominator : Nat
  boundDenominator_pos : 0 < boundDenominator
  bound : ℚ :=
    (boundNumerator : ℚ) / (boundDenominator : ℚ)
  bound_eq_numeral :
    bound = (boundNumerator : ℚ) / (boundDenominator : ℚ)
  cauchyBound_le_bound :
    ((sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P).explicitPolynomial.cauchyBound : Real) <=
      (bound : Real)

def packageSourceArithmeticCauchyDominationAsSourceArithmeticCauchyDomination
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (B : ThreeFlavorPackageSourceArithmeticCauchyDomination P) :
  ThreeFlavorCanonicalSourceArithmeticCauchyDomination P :=
  { boundNumerator := B.boundNumerator
    boundNumerator_pos := B.boundNumerator_pos
    boundDenominator := B.boundDenominator
    boundDenominator_pos := B.boundDenominator_pos
    bound := B.bound
    bound_eq_numeral := B.bound_eq_numeral
    cauchyBound_le_bound := B.cauchyBound_le_bound
    sourceArithmeticCauchyComputation :=
      P.polynomialLaw.polynomialLawDerivedInternally
    sourceArithmeticCauchyComputation_proof :=
      P.polynomialLaw.polynomialLawDerivedInternally_proof }

def sourceArithmeticCauchyDominationAsArithmeticCauchyDomination
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (B : ThreeFlavorCanonicalSourceArithmeticCauchyDomination P) :
  ThreeFlavorCanonicalArithmeticCauchyDomination P :=
  { boundNumerator := B.boundNumerator
    boundNumerator_pos := B.boundNumerator_pos
    boundDenominator := B.boundDenominator
    boundDenominator_pos := B.boundDenominator_pos
    bound := B.bound
    bound_eq_numeral := B.bound_eq_numeral
    cauchyBound_le_bound := B.cauchyBound_le_bound
    cauchyBoundComputedFromCoefficientTable :=
      B.sourceArithmeticCauchyComputation
    cauchyBoundComputedFromCoefficientTable_proof :=
      B.sourceArithmeticCauchyComputation_proof
    rationalDominationComputedFromCoefficientTable :=
      B.sourceArithmeticCauchyComputation
    rationalDominationComputedFromCoefficientTable_proof :=
      B.sourceArithmeticCauchyComputation_proof }

def canonicalArithmeticCauchyDominationAsBarePayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (B : ThreeFlavorCanonicalArithmeticCauchyDomination P) :
  ThreeFlavorCanonicalBareCauchyDominationPayload P :=
  { boundNumerator := B.boundNumerator
    boundNumerator_pos := B.boundNumerator_pos
    boundDenominator := B.boundDenominator
    boundDenominator_pos := B.boundDenominator_pos
    bound := B.bound
    bound_eq_numeral := B.bound_eq_numeral
    cauchyBound_le_bound := B.cauchyBound_le_bound
    boundTargetsExplicitPolynomial :=
      P.polynomialLaw.polynomialLawDerivedInternally
    boundTargetsExplicitPolynomial_proof :=
      P.polynomialLaw.polynomialLawDerivedInternally_proof
    cauchyBoundComputedFromCoefficientTable :=
      B.cauchyBoundComputedFromCoefficientTable
    cauchyBoundComputedFromCoefficientTable_proof :=
      B.cauchyBoundComputedFromCoefficientTable_proof
    rationalDominationComputedFromCoefficientTable :=
      B.rationalDominationComputedFromCoefficientTable
    rationalDominationComputedFromCoefficientTable_proof :=
      B.rationalDominationComputedFromCoefficientTable_proof }

def canonicalBareCauchyDominationPayloadAsSlimPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (B : ThreeFlavorCanonicalBareCauchyDominationPayload P) :
  ThreeFlavorCanonicalSlimCauchyDominationPayload P :=
  { boundNumerator := B.boundNumerator
    boundNumerator_pos := B.boundNumerator_pos
    boundDenominator := B.boundDenominator
    boundDenominator_pos := B.boundDenominator_pos
    bound := B.bound
    bound_eq_numeral := B.bound_eq_numeral
    cauchyBound_le_bound := B.cauchyBound_le_bound
    boundTargetsExplicitPolynomial := B.boundTargetsExplicitPolynomial
    boundTargetsExplicitPolynomial_proof :=
      B.boundTargetsExplicitPolynomial_proof
    cauchyBoundComputedFromCoefficientTable :=
      B.cauchyBoundComputedFromCoefficientTable
    cauchyBoundComputedFromCoefficientTable_proof :=
      B.cauchyBoundComputedFromCoefficientTable_proof
    rationalDominationComputedFromCoefficientTable :=
      B.rationalDominationComputedFromCoefficientTable
    rationalDominationComputedFromCoefficientTable_proof :=
      B.rationalDominationComputedFromCoefficientTable_proof
    noEmpiricalBoundImport :=
      P.polynomialLaw.noEmpiricalFitImport /\
        P.sameScopePredicate.noEmpiricalRootImport
    noEmpiricalBoundImport_proof :=
      ⟨P.polynomialLaw.noEmpiricalFitImport_proof,
        P.sameScopePredicate.noEmpiricalRootImport_proof⟩
    noBoundFitTuning :=
      P.polynomialLaw.noOneAnchorImport /\
        P.polynomialLaw.allUnresolvedFreedomsDischarged
    noBoundFitTuning_proof :=
      ⟨P.polynomialLaw.noOneAnchorImport_proof,
        P.polynomialLaw.allUnresolvedFreedomsDischarged_proof⟩ }

def canonicalSlimCauchyDominationPayloadAsDominationPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (B : ThreeFlavorCanonicalSlimCauchyDominationPayload P) :
  ThreeFlavorCanonicalCauchyDominationPayload P :=
  { boundNumerator := B.boundNumerator
    boundNumerator_pos := B.boundNumerator_pos
    boundDenominator := B.boundDenominator
    boundDenominator_pos := B.boundDenominator_pos
    bound := B.bound
    bound_eq_numeral := B.bound_eq_numeral
    cauchyBound_le_bound := B.cauchyBound_le_bound
    boundTargetsExplicitPolynomial := B.boundTargetsExplicitPolynomial
    boundTargetsExplicitPolynomial_proof :=
      B.boundTargetsExplicitPolynomial_proof
    cauchyBoundComputedFromCoefficientTable :=
      B.cauchyBoundComputedFromCoefficientTable
    cauchyBoundComputedFromCoefficientTable_proof :=
      B.cauchyBoundComputedFromCoefficientTable_proof
    rationalDominationComputedFromCoefficientTable :=
      B.rationalDominationComputedFromCoefficientTable
    rationalDominationComputedFromCoefficientTable_proof :=
      B.rationalDominationComputedFromCoefficientTable_proof
    noEmpiricalBoundImport := B.noEmpiricalBoundImport
    noEmpiricalBoundImport_proof := B.noEmpiricalBoundImport_proof
    noBoundFitTuning := B.noBoundFitTuning
    noBoundFitTuning_proof := B.noBoundFitTuning_proof
    noHiddenRootEncodingInBound :=
      B.cauchyBoundComputedFromCoefficientTable /\
        B.rationalDominationComputedFromCoefficientTable
    noHiddenRootEncodingInBound_proof :=
      ⟨B.cauchyBoundComputedFromCoefficientTable_proof,
        B.rationalDominationComputedFromCoefficientTable_proof⟩ }

noncomputable def canonicalCauchyDominationPayloadAsClosedCauchyBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U : ThreeFlavorSameScopePolynomialNonlinearAudit P)
  (B : ThreeFlavorCanonicalCauchyDominationPayload P) :
  ThreeFlavorCauchyRationalRootBound
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) := by
  let G := sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P
  have hcoeff :
      G.explicitPolynomial.coeff U.witnessDegree ≠ 0 := by
    simpa [G, sameScopePackageAsAlgebraicClosedRootPresentation] using
      U.witnessCoefficient_ne_zero
  have hpoly_ne : G.explicitPolynomial ≠ 0 := by
    intro hzero
    exact hcoeff (by rw [hzero]; simp)
  exact
  { boundNumerator := B.boundNumerator
    boundNumerator_pos := B.boundNumerator_pos
    boundDenominator := B.boundDenominator
    boundDenominator_pos := B.boundDenominator_pos
    bound := B.bound
    bound_eq_numeral := B.bound_eq_numeral
    explicitPolynomial_ne_zero := hpoly_ne
    cauchyBound_le_bound := B.cauchyBound_le_bound
    boundTargetsExplicitPolynomial := B.boundTargetsExplicitPolynomial
    boundTargetsExplicitPolynomial_proof :=
      B.boundTargetsExplicitPolynomial_proof
    cauchyBoundComputedFromCoefficientTable :=
      B.cauchyBoundComputedFromCoefficientTable
    cauchyBoundComputedFromCoefficientTable_proof :=
      B.cauchyBoundComputedFromCoefficientTable_proof
    rationalDominationComputedFromCoefficientTable :=
      B.rationalDominationComputedFromCoefficientTable
    rationalDominationComputedFromCoefficientTable_proof :=
      B.rationalDominationComputedFromCoefficientTable_proof
    noEmpiricalBoundImport := B.noEmpiricalBoundImport
    noEmpiricalBoundImport_proof := B.noEmpiricalBoundImport_proof
    noBoundFitTuning := B.noBoundFitTuning
    noBoundFitTuning_proof := B.noBoundFitTuning_proof
    noHiddenRootEncodingInBound :=
      B.noHiddenRootEncodingInBound /\
        U.coefficientsDoNotEncodeSelectedRoot
    noHiddenRootEncodingInBound_proof :=
      ⟨B.noHiddenRootEncodingInBound_proof,
        U.coefficientsDoNotEncodeSelectedRoot_proof⟩ }

/--
Canonical finite readout payload with a closed-root Cauchy bound.

The previous payload asked for a Cauchy bound on the induced QNF source
polynomial.  In the canonical route that source polynomial is the same
polynomial as the closed-root presentation, so a closed-root Cauchy bound is
enough and Lean transports it to the source-candidate form.
-/
structure ThreeFlavorCanonicalClosedCauchyReadoutPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  polynomialNonlinearAudit :
    ThreeFlavorSameScopePolynomialNonlinearAudit P
  cauchyBound :
    ThreeFlavorCauchyRationalRootBound
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
  positiveStandingReadout :
    ThreeFlavorPositiveStandingRootReadout
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
  decimalLabel : String
  decimalLabelCertifiedBySourceDerivedWindow : Prop
  decimalLabelCertifiedBySourceDerivedWindow_proof :
    decimalLabelCertifiedBySourceDerivedWindow

noncomputable def canonicalClosedCauchyReadoutPayloadAsFinitePayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalClosedCauchyReadoutPayload P) :
  ThreeFlavorCanonicalFiniteReadoutPayload P := by
  let G := sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P
  let L :=
    canonicalSameScopeQNFPolynomialAuditAsAlignment
      G
      (sameScopePolynomialNonlinearAuditAsCanonicalQNFPolynomialAudit
        P W.polynomialNonlinearAudit)
  let Q :=
    quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
      G
      (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
      L
  exact
  { polynomialNonlinearAudit := W.polynomialNonlinearAudit
    cauchyBound :=
      closedRootCauchyBoundAsSourcePolynomialCauchyBound Q W.cauchyBound
    positiveStandingReadout := W.positiveStandingReadout
    decimalLabel := W.decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow :=
      W.decimalLabelCertifiedBySourceDerivedWindow
    decimalLabelCertifiedBySourceDerivedWindow_proof :=
      W.decimalLabelCertifiedBySourceDerivedWindow_proof }

noncomputable def canonicalClosedCauchyReadoutPayloadAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalClosedCauchyReadoutPayload P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalFiniteReadoutPayloadAsWindow
    (canonicalClosedCauchyReadoutPayloadAsFinitePayload W)

theorem canonicalClosedCauchyReadoutPayload_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalClosedCauchyReadoutPayload P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalFiniteReadoutPayload_discharge_positiveReadoutNeed
    (canonicalClosedCauchyReadoutPayloadAsFinitePayload W)

theorem canonicalClosedCauchyReadoutPayload_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalClosedCauchyReadoutPayload P) :
  (canonicalClosedCauchyReadoutPayloadAsWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalClosedCauchyReadoutPayloadAsWindow W).interval.upper :=
  canonicalFiniteReadoutPayload_contains_gapRatio
    (canonicalClosedCauchyReadoutPayloadAsFinitePayload W)

/--
Canonical readout payload with Cauchy domination only.

This is the reduced target after using the nonlinear audit to derive
nonzero-ness of the canonical polynomial.  The Cauchy payload now only needs to
prove rational domination of the Cauchy bound.
-/
structure ThreeFlavorCanonicalDominationReadoutPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  polynomialNonlinearAudit :
    ThreeFlavorSameScopePolynomialNonlinearAudit P
  cauchyDomination :
    ThreeFlavorCanonicalCauchyDominationPayload P
  positiveStandingReadout :
    ThreeFlavorPositiveStandingRootReadout
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
  decimalLabel : String
  decimalLabelCertifiedBySourceDerivedWindow : Prop
  decimalLabelCertifiedBySourceDerivedWindow_proof :
    decimalLabelCertifiedBySourceDerivedWindow

noncomputable def canonicalDominationReadoutPayloadAsClosedCauchyPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalDominationReadoutPayload P) :
  ThreeFlavorCanonicalClosedCauchyReadoutPayload P :=
  { polynomialNonlinearAudit := W.polynomialNonlinearAudit
    cauchyBound :=
      canonicalCauchyDominationPayloadAsClosedCauchyBound
        W.polynomialNonlinearAudit
        W.cauchyDomination
    positiveStandingReadout := W.positiveStandingReadout
    decimalLabel := W.decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow :=
      W.decimalLabelCertifiedBySourceDerivedWindow
    decimalLabelCertifiedBySourceDerivedWindow_proof :=
      W.decimalLabelCertifiedBySourceDerivedWindow_proof }

noncomputable def canonicalDominationReadoutPayloadAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalDominationReadoutPayload P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalClosedCauchyReadoutPayloadAsWindow
    (canonicalDominationReadoutPayloadAsClosedCauchyPayload W)

theorem canonicalDominationReadoutPayload_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalDominationReadoutPayload P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalClosedCauchyReadoutPayload_discharge_positiveReadoutNeed
    (canonicalDominationReadoutPayloadAsClosedCauchyPayload W)

theorem canonicalDominationReadoutPayload_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalDominationReadoutPayload P) :
  (canonicalDominationReadoutPayloadAsWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalDominationReadoutPayloadAsWindow W).interval.upper :=
  canonicalClosedCauchyReadoutPayload_contains_gapRatio
    (canonicalDominationReadoutPayloadAsClosedCauchyPayload W)

/--
Canonical readout payload with slim Cauchy domination.

The no-hidden-bound audit is generated from coefficient-table computation and
rational domination, so it is not a separate input here.
-/
structure ThreeFlavorCanonicalSlimReadoutPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  polynomialNonlinearAudit :
    ThreeFlavorSameScopePolynomialNonlinearAudit P
  cauchyDomination :
    ThreeFlavorCanonicalSlimCauchyDominationPayload P
  positiveStandingReadout :
    ThreeFlavorPositiveStandingRootReadout
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
  decimalLabel : String
  decimalLabelCertifiedBySourceDerivedWindow : Prop
  decimalLabelCertifiedBySourceDerivedWindow_proof :
    decimalLabelCertifiedBySourceDerivedWindow

noncomputable def canonicalSlimReadoutPayloadAsDominationPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSlimReadoutPayload P) :
  ThreeFlavorCanonicalDominationReadoutPayload P :=
  { polynomialNonlinearAudit := W.polynomialNonlinearAudit
    cauchyDomination :=
      canonicalSlimCauchyDominationPayloadAsDominationPayload
        W.cauchyDomination
    positiveStandingReadout := W.positiveStandingReadout
    decimalLabel := W.decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow :=
      W.decimalLabelCertifiedBySourceDerivedWindow
    decimalLabelCertifiedBySourceDerivedWindow_proof :=
      W.decimalLabelCertifiedBySourceDerivedWindow_proof }

noncomputable def canonicalSlimReadoutPayloadAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSlimReadoutPayload P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalDominationReadoutPayloadAsWindow
    (canonicalSlimReadoutPayloadAsDominationPayload W)

theorem canonicalSlimReadoutPayload_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSlimReadoutPayload P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalDominationReadoutPayload_discharge_positiveReadoutNeed
    (canonicalSlimReadoutPayloadAsDominationPayload W)

theorem canonicalSlimReadoutPayload_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSlimReadoutPayload P) :
  (canonicalSlimReadoutPayloadAsWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalSlimReadoutPayloadAsWindow W).interval.upper :=
  canonicalDominationReadoutPayload_contains_gapRatio
    (canonicalSlimReadoutPayloadAsDominationPayload W)

/--
Slim sign-orientation payload.

The only mathematical sign fact needed for the positive readout is
`selectedRoot > 0`.  The standing/minimal-interval audit metadata is inherited
from the same-scope package.
-/
structure ThreeFlavorCanonicalPositiveSignPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  selectedRoot_pos :
    0 <
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P).selectedRoot

def canonicalPositiveSignPayloadAsStandingReadout
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (S : ThreeFlavorCanonicalPositiveSignPayload P) :
  ThreeFlavorPositiveStandingRootReadout
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  { selectedRoot_pos := S.selectedRoot_pos
    signOrientationFromStandingMinimalInterval :=
      C.inMinimalInterval C.ratio /\
        P.sameScopePredicate.rootReadbackLawful
    signOrientationFromStandingMinimalInterval_proof :=
      ⟨P.sameScopePredicate.currentRatioInMinimalInterval,
        P.sameScopePredicate.rootReadbackLawful_proof⟩
    noEmpiricalSignImport :=
      P.polynomialLaw.noEmpiricalFitImport /\
        P.sameScopePredicate.noEmpiricalRootImport
    noEmpiricalSignImport_proof :=
      ⟨P.polynomialLaw.noEmpiricalFitImport_proof,
        P.sameScopePredicate.noEmpiricalRootImport_proof⟩
    noSignFitTuning :=
      P.polynomialLaw.noOneAnchorImport /\
        P.polynomialLaw.calibrationPrior /\
          P.polynomialLaw.transportNeutralOrDischarged /\
            P.polynomialLaw.scaleStatusFixed
    noSignFitTuning_proof :=
      ⟨P.polynomialLaw.noOneAnchorImport_proof,
        P.polynomialLaw.calibrationPrior_proof,
        P.polynomialLaw.transportNeutralOrDischarged_proof,
        P.polynomialLaw.scaleStatusFixed_proof⟩ }

/--
Ordered-gap positivity payload.

This is the physical orientation version of the sign input: instead of proving
positivity of the selected root directly, prove that both denominator and
numerator gaps are positive.
-/
structure ThreeFlavorOrderedGapPositivity
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  solarGap_pos :
    0 < threeFlavorSolarGap A.massSquaredLevelOf
  atmosphericGap_pos :
    0 < threeFlavorAtmosphericGap A.massSquaredLevelOf
  gapOrderingFromStandingSplitting : Prop
  gapOrderingFromStandingSplitting_proof :
    gapOrderingFromStandingSplitting
  noEmpiricalOrderingImport : Prop
  noEmpiricalOrderingImport_proof :
    noEmpiricalOrderingImport
  noOrderingFitTuning : Prop
  noOrderingFitTuning_proof :
    noOrderingFitTuning

/--
Slim ordered-gap positivity.

The audit metadata is inherited from the gap-ratio algebra; the only local
mathematical content is positivity of the two gaps used in the quotient.
-/
structure ThreeFlavorSlimOrderedGapPositivity
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  solarGap_pos :
    0 < threeFlavorSolarGap A.massSquaredLevelOf
  atmosphericGap_pos :
    0 < threeFlavorAtmosphericGap A.massSquaredLevelOf

/--
Strict mass-squared ordering payload.

This is more primitive than directly asserting positivity of both gaps.  For
the canonical orientation, `m0 < m1 < m2` implies both the solar and atmospheric
gap used in the quotient are positive.
-/
structure ThreeFlavorStrictMassSquaredOrdering
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  level0_lt_level1 :
    A.massSquaredLevelOf 0 < A.massSquaredLevelOf 1
  level1_lt_level2 :
    A.massSquaredLevelOf 1 < A.massSquaredLevelOf 2

/--
Source-audited strict mass-squared ordering.

The mathematical ordering content is unchanged, but the witness now carries an
explicit source-derivation audit for the ordered three-level presentation.
-/
structure ThreeFlavorSourceStrictMassSquaredOrdering
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  level0_lt_level1 :
    A.massSquaredLevelOf 0 < A.massSquaredLevelOf 1
  level1_lt_level2 :
    A.massSquaredLevelOf 1 < A.massSquaredLevelOf 2
  strictMassOrderingSourceDerived : Prop
  strictMassOrderingSourceDerived_proof :
    strictMassOrderingSourceDerived

/--
Package-derived strict mass-squared ordering provenance.

The strict inequalities remain local mathematical data.  The source-derived
ordering provenance is reconstructed from the gap-ratio algebra controls:
certified two-gap structure, shared standing target, and no ordering-fit import.
-/
structure ThreeFlavorPackageStrictMassSquaredOrdering
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  level0_lt_level1 :
    A.massSquaredLevelOf 0 < A.massSquaredLevelOf 1
  level1_lt_level2 :
    A.massSquaredLevelOf 1 < A.massSquaredLevelOf 2

def packageStrictMassSquaredOrderingAsSourceStrictMassSquaredOrdering
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (O : ThreeFlavorPackageStrictMassSquaredOrdering (A := A)) :
  ThreeFlavorSourceStrictMassSquaredOrdering (A := A) :=
  let hgaps := O.gapRatioAlgebraPasses.2.1
  let htarget := O.gapRatioAlgebraPasses.2.2.2.2.2.2.2.2
  let hordering := O.gapRatioAlgebraPasses.2.2.2.2.2.2.2.1
  { gapRatioAlgebraPasses := O.gapRatioAlgebraPasses
    level0_lt_level1 := O.level0_lt_level1
    level1_lt_level2 := O.level1_lt_level2
    strictMassOrderingSourceDerived :=
      A.twoIndependentGapsCertified /\
        A.sameStandingRatioTarget /\
          A.noOrderingFitImport
    strictMassOrderingSourceDerived_proof :=
      ⟨hgaps, htarget, hordering⟩ }

/--
Minimal package-derived strict mass-squared ordering.

The local data are only the two strict inequalities.  The full
`ThreeFlavorGapRatioAlgebraPasses` conjunction is reconstructed from the
fields already carried by the gap-ratio algebra `A`.
-/
structure ThreeFlavorMinimalPackageStrictMassSquaredOrdering
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  level0_lt_level1 :
    A.massSquaredLevelOf 0 < A.massSquaredLevelOf 1
  level1_lt_level2 :
    A.massSquaredLevelOf 1 < A.massSquaredLevelOf 2

def minimalPackageStrictMassSquaredOrderingAsPackageStrictMassSquaredOrdering
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A)) :
  ThreeFlavorPackageStrictMassSquaredOrdering (A := A) :=
  { gapRatioAlgebraPasses := O.gapRatioAlgebraPasses
    level0_lt_level1 := O.level0_lt_level1
    level1_lt_level2 := O.level1_lt_level2 }

def sourceStrictMassSquaredOrderingAsStrictMassSquaredOrdering
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (O : ThreeFlavorSourceStrictMassSquaredOrdering (A := A)) :
  ThreeFlavorStrictMassSquaredOrdering (A := A) :=
  { gapRatioAlgebraPasses := O.gapRatioAlgebraPasses
    level0_lt_level1 := O.level0_lt_level1
    level1_lt_level2 := O.level1_lt_level2 }

def strictMassSquaredOrderingAsSlimOrderedGapPositivity
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A)) :
  ThreeFlavorSlimOrderedGapPositivity (A := A) :=
  { gapRatioAlgebraPasses := O.gapRatioAlgebraPasses
    solarGap_pos := by
      unfold threeFlavorSolarGap
      exact sub_pos.mpr O.level0_lt_level1
    atmosphericGap_pos := by
      unfold threeFlavorAtmosphericGap
      exact sub_pos.mpr (lt_trans O.level0_lt_level1 O.level1_lt_level2) }

def slimOrderedGapPositivityAsOrderedGapPositivity
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (O : ThreeFlavorSlimOrderedGapPositivity (A := A)) :
  ThreeFlavorOrderedGapPositivity (A := A) :=
  let hgaps := O.gapRatioAlgebraPasses.2.1
  let habsolute := O.gapRatioAlgebraPasses.2.2.2.2.1
  let hobserved := O.gapRatioAlgebraPasses.2.2.2.2.2.1
  let hordering := O.gapRatioAlgebraPasses.2.2.2.2.2.2.2.1
  let htarget := O.gapRatioAlgebraPasses.2.2.2.2.2.2.2.2
  { solarGap_pos := O.solarGap_pos
    atmosphericGap_pos := O.atmosphericGap_pos
    gapOrderingFromStandingSplitting :=
      A.twoIndependentGapsCertified /\ A.sameStandingRatioTarget
    gapOrderingFromStandingSplitting_proof :=
      ⟨hgaps, htarget⟩
    noEmpiricalOrderingImport :=
      A.noObservedGapImport /\ A.noAbsoluteMassScaleImport
    noEmpiricalOrderingImport_proof :=
      ⟨hobserved, habsolute⟩
    noOrderingFitTuning := A.noOrderingFitImport
    noOrderingFitTuning_proof := hordering }

theorem orderedGapPositivity_gapRatio_pos
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (O : ThreeFlavorOrderedGapPositivity (A := A)) :
  0 < threeFlavorGapRatio A.massSquaredLevelOf := by
  unfold threeFlavorGapRatio
  exact div_pos O.solarGap_pos O.atmosphericGap_pos

theorem strictMassSquaredOrdering_gapRatio_lt_one
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A)) :
  threeFlavorGapRatio A.massSquaredLevelOf < 1 := by
  have hnum_lt_den :
      threeFlavorSolarGap A.massSquaredLevelOf <
        threeFlavorAtmosphericGap A.massSquaredLevelOf := by
    unfold threeFlavorSolarGap threeFlavorAtmosphericGap
    linarith [O.level1_lt_level2]
  have hden_pos :
      0 < threeFlavorAtmosphericGap A.massSquaredLevelOf := by
    unfold threeFlavorAtmosphericGap
    linarith [O.level0_lt_level1, O.level1_lt_level2]
  unfold threeFlavorGapRatio
  calc
    threeFlavorSolarGap A.massSquaredLevelOf /
        threeFlavorAtmosphericGap A.massSquaredLevelOf <
        threeFlavorAtmosphericGap A.massSquaredLevelOf /
          threeFlavorAtmosphericGap A.massSquaredLevelOf :=
      div_lt_div_of_pos_right hnum_lt_den hden_pos
    _ = 1 := by
      field_simp [ne_of_gt hden_pos]

theorem strictMassSquaredOrdering_gapRatio_nonneg
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A)) :
  0 <= threeFlavorGapRatio A.massSquaredLevelOf := by
  exact le_of_lt
    (orderedGapPositivity_gapRatio_pos
      (slimOrderedGapPositivityAsOrderedGapPositivity
        (strictMassSquaredOrderingAsSlimOrderedGapPositivity O)))

theorem strictMassSquaredOrdering_gapRatio_le_one
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A)) :
  threeFlavorGapRatio A.massSquaredLevelOf <= 1 := by
  exact le_of_lt (strictMassSquaredOrdering_gapRatio_lt_one O)

def orderedGapPositivityAsPositiveSignPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (O : ThreeFlavorOrderedGapPositivity (A := A)) :
  ThreeFlavorCanonicalPositiveSignPayload P := by
  let G := sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P
  have hroot :
      G.selectedRoot = threeFlavorGapRatio A.massSquaredLevelOf :=
    algebraicClosedRootPresentation_selectedRoot_eq_gapRatio G
  exact
  { selectedRoot_pos := by
      rw [hroot]
      exact orderedGapPositivity_gapRatio_pos O }

/--
Label-free canonical slim readout payload.

The decimal label is presentation metadata, not mathematical content.  This
payload keeps only the three substantive inputs and supplies a default audited
label internally.
-/
structure ThreeFlavorCanonicalSlimCoreReadoutPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  polynomialNonlinearAudit :
    ThreeFlavorSameScopePolynomialNonlinearAudit P
  cauchyDomination :
    ThreeFlavorCanonicalSlimCauchyDominationPayload P
  positiveStandingReadout :
    ThreeFlavorPositiveStandingRootReadout
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)

def canonicalSlimCoreReadoutDefaultLabel : String :=
  "canonical positive rational readout window"

noncomputable def canonicalSlimCoreReadoutPayloadAsSlimPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSlimCoreReadoutPayload P) :
  ThreeFlavorCanonicalSlimReadoutPayload P :=
  { polynomialNonlinearAudit := W.polynomialNonlinearAudit
    cauchyDomination := W.cauchyDomination
    positiveStandingReadout := W.positiveStandingReadout
    decimalLabel := canonicalSlimCoreReadoutDefaultLabel
    decimalLabelCertifiedBySourceDerivedWindow := True
    decimalLabelCertifiedBySourceDerivedWindow_proof := True.intro }

noncomputable def canonicalSlimCoreReadoutPayloadAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSlimCoreReadoutPayload P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalSlimReadoutPayloadAsWindow
    (canonicalSlimCoreReadoutPayloadAsSlimPayload W)

theorem canonicalSlimCoreReadoutPayload_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSlimCoreReadoutPayload P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalSlimReadoutPayload_discharge_positiveReadoutNeed
    (canonicalSlimCoreReadoutPayloadAsSlimPayload W)

theorem canonicalSlimCoreReadoutPayload_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSlimCoreReadoutPayload P) :
  (canonicalSlimCoreReadoutPayloadAsWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalSlimCoreReadoutPayloadAsWindow W).interval.upper :=
  canonicalSlimReadoutPayload_contains_gapRatio
    (canonicalSlimCoreReadoutPayloadAsSlimPayload W)

/--
Leanest current canonical readout payload.

All standing sign audit metadata is inherited from `P`, so the sign field is
only the actual positivity proof.  This leaves the readout target as three
finite mathematical facts.
-/
structure ThreeFlavorCanonicalLeanReadoutPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  polynomialNonlinearAudit :
    ThreeFlavorSameScopePolynomialNonlinearAudit P
  cauchyDomination :
    ThreeFlavorCanonicalSlimCauchyDominationPayload P
  positiveSign :
    ThreeFlavorCanonicalPositiveSignPayload P

noncomputable def canonicalLeanReadoutPayloadAsSlimCorePayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalLeanReadoutPayload P) :
  ThreeFlavorCanonicalSlimCoreReadoutPayload P :=
  { polynomialNonlinearAudit := W.polynomialNonlinearAudit
    cauchyDomination := W.cauchyDomination
    positiveStandingReadout :=
      canonicalPositiveSignPayloadAsStandingReadout W.positiveSign }

noncomputable def canonicalLeanReadoutPayloadAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalLeanReadoutPayload P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalSlimCoreReadoutPayloadAsWindow
    (canonicalLeanReadoutPayloadAsSlimCorePayload W)

theorem canonicalLeanReadoutPayload_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalLeanReadoutPayload P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalSlimCoreReadoutPayload_discharge_positiveReadoutNeed
    (canonicalLeanReadoutPayloadAsSlimCorePayload W)

theorem canonicalLeanReadoutPayload_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalLeanReadoutPayload P) :
  (canonicalLeanReadoutPayloadAsWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalLeanReadoutPayloadAsWindow W).interval.upper :=
  canonicalSlimCoreReadoutPayload_contains_gapRatio
    (canonicalLeanReadoutPayloadAsSlimCorePayload W)

/--
Canonical readout payload with physical ordered-gap orientation.

This replaces direct selected-root positivity with the more structural
orientation witness: both mass-squared gaps used in the ratio are positive.
-/
structure ThreeFlavorCanonicalOrderedGapReadoutPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  polynomialNonlinearAudit :
    ThreeFlavorSameScopePolynomialNonlinearAudit P
  cauchyDomination :
    ThreeFlavorCanonicalSlimCauchyDominationPayload P
  orderedGapPositivity :
    ThreeFlavorOrderedGapPositivity (A := A)

noncomputable def canonicalOrderedGapReadoutPayloadAsLeanPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalOrderedGapReadoutPayload P) :
  ThreeFlavorCanonicalLeanReadoutPayload P :=
  { polynomialNonlinearAudit := W.polynomialNonlinearAudit
    cauchyDomination := W.cauchyDomination
    positiveSign :=
      orderedGapPositivityAsPositiveSignPayload W.orderedGapPositivity }

noncomputable def canonicalOrderedGapReadoutPayloadAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalOrderedGapReadoutPayload P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalLeanReadoutPayloadAsWindow
    (canonicalOrderedGapReadoutPayloadAsLeanPayload W)

theorem canonicalOrderedGapReadoutPayload_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalOrderedGapReadoutPayload P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalLeanReadoutPayload_discharge_positiveReadoutNeed
    (canonicalOrderedGapReadoutPayloadAsLeanPayload W)

theorem canonicalOrderedGapReadoutPayload_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalOrderedGapReadoutPayload P) :
  (canonicalOrderedGapReadoutPayloadAsWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalOrderedGapReadoutPayloadAsWindow W).interval.upper :=
  canonicalLeanReadoutPayload_contains_gapRatio
    (canonicalOrderedGapReadoutPayloadAsLeanPayload W)

/--
Canonical readout payload with slim ordered-gap orientation.

Only the two gap-positivity inequalities remain on the sign side; the AASC
audit metadata is inherited from the gap-ratio algebra.
-/
structure ThreeFlavorCanonicalSlimOrderedGapReadoutPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  polynomialNonlinearAudit :
    ThreeFlavorSameScopePolynomialNonlinearAudit P
  cauchyDomination :
    ThreeFlavorCanonicalSlimCauchyDominationPayload P
  orderedGapPositivity :
    ThreeFlavorSlimOrderedGapPositivity (A := A)

noncomputable def canonicalSlimOrderedGapReadoutPayloadAsOrderedGapPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSlimOrderedGapReadoutPayload P) :
  ThreeFlavorCanonicalOrderedGapReadoutPayload P :=
  { polynomialNonlinearAudit := W.polynomialNonlinearAudit
    cauchyDomination := W.cauchyDomination
    orderedGapPositivity :=
      slimOrderedGapPositivityAsOrderedGapPositivity W.orderedGapPositivity }

noncomputable def canonicalSlimOrderedGapReadoutPayloadAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSlimOrderedGapReadoutPayload P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalOrderedGapReadoutPayloadAsWindow
    (canonicalSlimOrderedGapReadoutPayloadAsOrderedGapPayload W)

theorem canonicalSlimOrderedGapReadoutPayload_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSlimOrderedGapReadoutPayload P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalOrderedGapReadoutPayload_discharge_positiveReadoutNeed
    (canonicalSlimOrderedGapReadoutPayloadAsOrderedGapPayload W)

theorem canonicalSlimOrderedGapReadoutPayload_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSlimOrderedGapReadoutPayload P) :
  (canonicalSlimOrderedGapReadoutPayloadAsWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalSlimOrderedGapReadoutPayloadAsWindow W).interval.upper :=
  canonicalOrderedGapReadoutPayload_contains_gapRatio
    (canonicalSlimOrderedGapReadoutPayloadAsOrderedGapPayload W)

/--
Canonical readout payload with only local finite arithmetic facts.

The polynomial anti-tautology audit is generated from the same-scope package
plus a high-degree nonzero coefficient.  The sign audit is generated from the
gap algebra pass proof plus the two gap inequalities.
-/
structure ThreeFlavorCanonicalArithmeticReadoutPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  highCoefficient :
    ThreeFlavorSameScopePolynomialHighCoefficient P
  cauchyDomination :
    ThreeFlavorCanonicalSlimCauchyDominationPayload P
  orderedGapPositivity :
    ThreeFlavorSlimOrderedGapPositivity (A := A)

noncomputable def canonicalArithmeticReadoutPayloadAsSlimOrderedGapPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalArithmeticReadoutPayload P) :
  ThreeFlavorCanonicalSlimOrderedGapReadoutPayload P :=
  { polynomialNonlinearAudit :=
      sameScopePolynomialHighCoefficientAsNonlinearAudit P W.highCoefficient
    cauchyDomination := W.cauchyDomination
    orderedGapPositivity := W.orderedGapPositivity }

noncomputable def canonicalArithmeticReadoutPayloadAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalArithmeticReadoutPayload P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalSlimOrderedGapReadoutPayloadAsWindow
    (canonicalArithmeticReadoutPayloadAsSlimOrderedGapPayload W)

theorem canonicalArithmeticReadoutPayload_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalArithmeticReadoutPayload P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalSlimOrderedGapReadoutPayload_discharge_positiveReadoutNeed
    (canonicalArithmeticReadoutPayloadAsSlimOrderedGapPayload W)

theorem canonicalArithmeticReadoutPayload_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalArithmeticReadoutPayload P) :
  (canonicalArithmeticReadoutPayloadAsWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalArithmeticReadoutPayloadAsWindow W).interval.upper :=
  canonicalSlimOrderedGapReadoutPayload_contains_gapRatio
    (canonicalArithmeticReadoutPayloadAsSlimOrderedGapPayload W)

/--
Canonical arithmetic readout payload with strict mass-squared ordering.

This replaces the two gap-positivity inequalities with the primitive ordering
chain `m0 < m1 < m2`.
-/
structure ThreeFlavorCanonicalOrderedMassReadoutPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  highCoefficient :
    ThreeFlavorSameScopePolynomialHighCoefficient P
  cauchyDomination :
    ThreeFlavorCanonicalSlimCauchyDominationPayload P
  strictMassOrdering :
    ThreeFlavorStrictMassSquaredOrdering (A := A)

noncomputable def canonicalOrderedMassReadoutPayloadAsArithmeticPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalOrderedMassReadoutPayload P) :
  ThreeFlavorCanonicalArithmeticReadoutPayload P :=
  { highCoefficient := W.highCoefficient
    cauchyDomination := W.cauchyDomination
    orderedGapPositivity :=
      strictMassSquaredOrderingAsSlimOrderedGapPositivity
        W.strictMassOrdering }

noncomputable def canonicalOrderedMassReadoutPayloadAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalOrderedMassReadoutPayload P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalArithmeticReadoutPayloadAsWindow
    (canonicalOrderedMassReadoutPayloadAsArithmeticPayload W)

theorem canonicalOrderedMassReadoutPayload_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalOrderedMassReadoutPayload P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalArithmeticReadoutPayload_discharge_positiveReadoutNeed
    (canonicalOrderedMassReadoutPayloadAsArithmeticPayload W)

theorem canonicalOrderedMassReadoutPayload_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalOrderedMassReadoutPayload P) :
  (canonicalOrderedMassReadoutPayloadAsWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalOrderedMassReadoutPayloadAsWindow W).interval.upper :=
  canonicalArithmeticReadoutPayload_contains_gapRatio
    (canonicalOrderedMassReadoutPayloadAsArithmeticPayload W)

/--
Canonical ordered-mass readout payload with bare Cauchy arithmetic.

The Cauchy no-empirical/no-fit audit metadata is inherited from the same-scope
package, leaving only the rational endpoint, Cauchy domination, and
coefficient-computation audit on the Cauchy side.
-/
structure ThreeFlavorCanonicalBareCauchyOrderedMassReadoutPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  highCoefficient :
    ThreeFlavorSameScopePolynomialHighCoefficient P
  cauchyDomination :
    ThreeFlavorCanonicalBareCauchyDominationPayload P
  strictMassOrdering :
    ThreeFlavorStrictMassSquaredOrdering (A := A)

noncomputable def canonicalBareCauchyOrderedMassReadoutPayloadAsOrderedMassPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalBareCauchyOrderedMassReadoutPayload P) :
  ThreeFlavorCanonicalOrderedMassReadoutPayload P :=
  { highCoefficient := W.highCoefficient
    cauchyDomination :=
      canonicalBareCauchyDominationPayloadAsSlimPayload
        W.cauchyDomination
    strictMassOrdering := W.strictMassOrdering }

noncomputable def canonicalBareCauchyOrderedMassReadoutPayloadAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalBareCauchyOrderedMassReadoutPayload P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalOrderedMassReadoutPayloadAsWindow
    (canonicalBareCauchyOrderedMassReadoutPayloadAsOrderedMassPayload W)

theorem canonicalBareCauchyOrderedMassReadoutPayload_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalBareCauchyOrderedMassReadoutPayload P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalOrderedMassReadoutPayload_discharge_positiveReadoutNeed
    (canonicalBareCauchyOrderedMassReadoutPayloadAsOrderedMassPayload W)

theorem canonicalBareCauchyOrderedMassReadoutPayload_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalBareCauchyOrderedMassReadoutPayload P) :
  (canonicalBareCauchyOrderedMassReadoutPayloadAsWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalBareCauchyOrderedMassReadoutPayloadAsWindow W).interval.upper :=
  canonicalOrderedMassReadoutPayload_contains_gapRatio
    (canonicalBareCauchyOrderedMassReadoutPayloadAsOrderedMassPayload W)

/--
Canonical ordered-mass readout payload with arithmetic-only Cauchy data.

The Cauchy side now contains only rational arithmetic and coefficient-table
computation audits; all same-scope targeting metadata is inherited.
-/
structure ThreeFlavorCanonicalArithmeticCauchyOrderedMassReadoutPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  highCoefficient :
    ThreeFlavorSameScopePolynomialHighCoefficient P
  cauchyDomination :
    ThreeFlavorCanonicalArithmeticCauchyDomination P
  strictMassOrdering :
    ThreeFlavorStrictMassSquaredOrdering (A := A)

noncomputable def canonicalArithmeticCauchyOrderedMassReadoutPayloadAsBarePayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalArithmeticCauchyOrderedMassReadoutPayload P) :
  ThreeFlavorCanonicalBareCauchyOrderedMassReadoutPayload P :=
  { highCoefficient := W.highCoefficient
    cauchyDomination :=
      canonicalArithmeticCauchyDominationAsBarePayload
        W.cauchyDomination
    strictMassOrdering := W.strictMassOrdering }

noncomputable def canonicalArithmeticCauchyOrderedMassReadoutPayloadAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalArithmeticCauchyOrderedMassReadoutPayload P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalBareCauchyOrderedMassReadoutPayloadAsWindow
    (canonicalArithmeticCauchyOrderedMassReadoutPayloadAsBarePayload W)

theorem canonicalArithmeticCauchyOrderedMassReadoutPayload_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalArithmeticCauchyOrderedMassReadoutPayload P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalBareCauchyOrderedMassReadoutPayload_discharge_positiveReadoutNeed
    (canonicalArithmeticCauchyOrderedMassReadoutPayloadAsBarePayload W)

theorem canonicalArithmeticCauchyOrderedMassReadoutPayload_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalArithmeticCauchyOrderedMassReadoutPayload P) :
  (canonicalArithmeticCauchyOrderedMassReadoutPayloadAsWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalArithmeticCauchyOrderedMassReadoutPayloadAsWindow W).interval.upper :=
  canonicalBareCauchyOrderedMassReadoutPayload_contains_gapRatio
    (canonicalArithmeticCauchyOrderedMassReadoutPayloadAsBarePayload W)

/--
Canonical arithmetic-Cauchy ordered-mass readout payload whose high
coefficient witness is source-audited.

This preserves the already reduced arithmetic Cauchy and strict-ordering
targets, while replacing the remaining bare high-coefficient witness by a
source-derived one.
-/
structure ThreeFlavorCanonicalSourceHighArithmeticCauchyReadoutPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  sourceHighCoefficient :
    ThreeFlavorSameScopeSourceHighCoefficient P
  cauchyDomination :
    ThreeFlavorCanonicalArithmeticCauchyDomination P
  strictMassOrdering :
    ThreeFlavorStrictMassSquaredOrdering (A := A)

noncomputable def canonicalSourceHighArithmeticCauchyReadoutPayloadAsArithmeticPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSourceHighArithmeticCauchyReadoutPayload P) :
  ThreeFlavorCanonicalArithmeticCauchyOrderedMassReadoutPayload P :=
  { highCoefficient :=
      sameScopeSourceHighCoefficientAsHighCoefficient
        W.sourceHighCoefficient
    cauchyDomination := W.cauchyDomination
    strictMassOrdering := W.strictMassOrdering }

noncomputable def canonicalSourceHighArithmeticCauchyReadoutPayloadAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSourceHighArithmeticCauchyReadoutPayload P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalArithmeticCauchyOrderedMassReadoutPayloadAsWindow
    (canonicalSourceHighArithmeticCauchyReadoutPayloadAsArithmeticPayload W)

theorem canonicalSourceHighArithmeticCauchyReadoutPayload_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSourceHighArithmeticCauchyReadoutPayload P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalArithmeticCauchyOrderedMassReadoutPayload_discharge_positiveReadoutNeed
    (canonicalSourceHighArithmeticCauchyReadoutPayloadAsArithmeticPayload W)

theorem canonicalSourceHighArithmeticCauchyReadoutPayload_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSourceHighArithmeticCauchyReadoutPayload P) :
  (canonicalSourceHighArithmeticCauchyReadoutPayloadAsWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalSourceHighArithmeticCauchyReadoutPayloadAsWindow W).interval.upper :=
  canonicalArithmeticCauchyOrderedMassReadoutPayload_contains_gapRatio
    (canonicalSourceHighArithmeticCauchyReadoutPayloadAsArithmeticPayload W)

/--
Canonical source-high arithmetic-Cauchy readout payload with source-audited
strict mass ordering.

At this stage, both the high-coefficient nonlinearity and the ordering
orientation are source-audited; the Cauchy side remains explicit arithmetic.
-/
structure ThreeFlavorCanonicalSourceOrderedArithmeticReadoutPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  sourceHighCoefficient :
    ThreeFlavorSameScopeSourceHighCoefficient P
  cauchyDomination :
    ThreeFlavorCanonicalArithmeticCauchyDomination P
  sourceStrictMassOrdering :
    ThreeFlavorSourceStrictMassSquaredOrdering (A := A)

noncomputable def canonicalSourceOrderedArithmeticReadoutPayloadAsSourceHighPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSourceOrderedArithmeticReadoutPayload P) :
  ThreeFlavorCanonicalSourceHighArithmeticCauchyReadoutPayload P :=
  { sourceHighCoefficient := W.sourceHighCoefficient
    cauchyDomination := W.cauchyDomination
    strictMassOrdering :=
      sourceStrictMassSquaredOrderingAsStrictMassSquaredOrdering
        W.sourceStrictMassOrdering }

noncomputable def canonicalSourceOrderedArithmeticReadoutPayloadAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSourceOrderedArithmeticReadoutPayload P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalSourceHighArithmeticCauchyReadoutPayloadAsWindow
    (canonicalSourceOrderedArithmeticReadoutPayloadAsSourceHighPayload W)

theorem canonicalSourceOrderedArithmeticReadoutPayload_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSourceOrderedArithmeticReadoutPayload P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalSourceHighArithmeticCauchyReadoutPayload_discharge_positiveReadoutNeed
    (canonicalSourceOrderedArithmeticReadoutPayloadAsSourceHighPayload W)

theorem canonicalSourceOrderedArithmeticReadoutPayload_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSourceOrderedArithmeticReadoutPayload P) :
  (canonicalSourceOrderedArithmeticReadoutPayloadAsWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalSourceOrderedArithmeticReadoutPayloadAsWindow W).interval.upper :=
  canonicalSourceHighArithmeticCauchyReadoutPayload_contains_gapRatio
    (canonicalSourceOrderedArithmeticReadoutPayloadAsSourceHighPayload W)

/--
Canonical source-ordered readout payload with source-arithmetic Cauchy
domination.

All three remaining inputs are now source-audited: high coefficient,
mass-order orientation, and arithmetic Cauchy domination.
-/
structure ThreeFlavorCanonicalSourceArithmeticReadoutPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  sourceHighCoefficient :
    ThreeFlavorSameScopeSourceHighCoefficient P
  sourceCauchyDomination :
    ThreeFlavorCanonicalSourceArithmeticCauchyDomination P
  sourceStrictMassOrdering :
    ThreeFlavorSourceStrictMassSquaredOrdering (A := A)

noncomputable def canonicalSourceArithmeticReadoutPayloadAsSourceOrderedPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSourceArithmeticReadoutPayload P) :
  ThreeFlavorCanonicalSourceOrderedArithmeticReadoutPayload P :=
  { sourceHighCoefficient := W.sourceHighCoefficient
    cauchyDomination :=
      sourceArithmeticCauchyDominationAsArithmeticCauchyDomination
        W.sourceCauchyDomination
    sourceStrictMassOrdering := W.sourceStrictMassOrdering }

noncomputable def canonicalSourceArithmeticReadoutPayloadAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSourceArithmeticReadoutPayload P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalSourceOrderedArithmeticReadoutPayloadAsWindow
    (canonicalSourceArithmeticReadoutPayloadAsSourceOrderedPayload W)

theorem canonicalSourceArithmeticReadoutPayload_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSourceArithmeticReadoutPayload P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalSourceOrderedArithmeticReadoutPayload_discharge_positiveReadoutNeed
    (canonicalSourceArithmeticReadoutPayloadAsSourceOrderedPayload W)

theorem canonicalSourceArithmeticReadoutPayload_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalSourceArithmeticReadoutPayload P) :
  (canonicalSourceArithmeticReadoutPayloadAsWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalSourceArithmeticReadoutPayloadAsWindow W).interval.upper :=
  canonicalSourceOrderedArithmeticReadoutPayload_contains_gapRatio
    (canonicalSourceArithmeticReadoutPayloadAsSourceOrderedPayload W)

/--
Bundled source readout certificate.

This packages the three source-audited witnesses that remain after the
readout reductions into one certificate object: nonlinear coefficient,
source-arithmetic Cauchy bound, and strict mass-order orientation.
-/
structure ThreeFlavorCanonicalSourceReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  sourceHighCoefficient :
    ThreeFlavorSameScopeSourceHighCoefficient P
  sourceCauchyDomination :
    ThreeFlavorCanonicalSourceArithmeticCauchyDomination P
  sourceStrictMassOrdering :
    ThreeFlavorSourceStrictMassSquaredOrdering (A := A)

noncomputable def sourceReadoutCertificateAsSourceArithmeticPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorCanonicalSourceReadoutCertificate P) :
  ThreeFlavorCanonicalSourceArithmeticReadoutPayload P :=
  { sourceHighCoefficient := K.sourceHighCoefficient
    sourceCauchyDomination := K.sourceCauchyDomination
    sourceStrictMassOrdering := K.sourceStrictMassOrdering }

/--
One-certificate readout payload.

The readout construction now depends on a single bundled source certificate
rather than three separate source witnesses.
-/
structure ThreeFlavorCanonicalCertifiedReadoutPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  sourceReadoutCertificate :
    ThreeFlavorCanonicalSourceReadoutCertificate P

noncomputable def canonicalCertifiedReadoutPayloadAsSourceArithmeticPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalCertifiedReadoutPayload P) :
  ThreeFlavorCanonicalSourceArithmeticReadoutPayload P :=
  sourceReadoutCertificateAsSourceArithmeticPayload
    W.sourceReadoutCertificate

noncomputable def canonicalCertifiedReadoutPayloadAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalCertifiedReadoutPayload P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalSourceArithmeticReadoutPayloadAsWindow
    (canonicalCertifiedReadoutPayloadAsSourceArithmeticPayload W)

theorem canonicalCertifiedReadoutPayload_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalCertifiedReadoutPayload P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalSourceArithmeticReadoutPayload_discharge_positiveReadoutNeed
    (canonicalCertifiedReadoutPayloadAsSourceArithmeticPayload W)

theorem canonicalCertifiedReadoutPayload_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalCertifiedReadoutPayload P) :
  (canonicalCertifiedReadoutPayloadAsWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalCertifiedReadoutPayloadAsWindow W).interval.upper :=
  canonicalSourceArithmeticReadoutPayload_contains_gapRatio
    (canonicalCertifiedReadoutPayloadAsSourceArithmeticPayload W)

/--
Protocol-closed source readout certificate.

This records that the bundled source witnesses are not merely collected, but
are admitted as one closed source-readout protocol for the canonical same-scope
presentation.
-/
structure ThreeFlavorProtocolClosedSourceReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  sourceReadoutCertificate :
    ThreeFlavorCanonicalSourceReadoutCertificate P
  sourceReadoutProtocolClosed : Prop
  sourceReadoutProtocolClosed_proof :
    sourceReadoutProtocolClosed

def protocolClosedSourceReadoutCertificateAsSourceReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorProtocolClosedSourceReadoutCertificate P) :
  ThreeFlavorCanonicalSourceReadoutCertificate P :=
  K.sourceReadoutCertificate

/--
Protocol-closed certified readout payload.

The final readout boundary now asks for a closed source-readout protocol
certificate rather than a merely bundled source certificate.
-/
structure ThreeFlavorCanonicalProtocolReadoutPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  protocolClosedSourceReadout :
    ThreeFlavorProtocolClosedSourceReadoutCertificate P

noncomputable def canonicalProtocolReadoutPayloadAsCertifiedPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalProtocolReadoutPayload P) :
  ThreeFlavorCanonicalCertifiedReadoutPayload P :=
  { sourceReadoutCertificate :=
      protocolClosedSourceReadoutCertificateAsSourceReadoutCertificate
        W.protocolClosedSourceReadout }

noncomputable def canonicalProtocolReadoutPayloadAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalProtocolReadoutPayload P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalCertifiedReadoutPayloadAsWindow
    (canonicalProtocolReadoutPayloadAsCertifiedPayload W)

theorem canonicalProtocolReadoutPayload_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalProtocolReadoutPayload P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalCertifiedReadoutPayload_discharge_positiveReadoutNeed
    (canonicalProtocolReadoutPayloadAsCertifiedPayload W)

theorem canonicalProtocolReadoutPayload_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalProtocolReadoutPayload P) :
  (canonicalProtocolReadoutPayloadAsWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalProtocolReadoutPayloadAsWindow W).interval.upper :=
  canonicalCertifiedReadoutPayload_contains_gapRatio
    (canonicalProtocolReadoutPayloadAsCertifiedPayload W)

/--
Package-closed source readout certificate.

The protocol-closure audit is no longer an independent free proposition.  It
is supplied by the same-scope package's own exhaustion and unresolved-freedom
closure controls.
-/
structure ThreeFlavorPackageClosedSourceReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  sourceReadoutCertificate :
    ThreeFlavorCanonicalSourceReadoutCertificate P

def packageClosedSourceReadoutCertificateAsProtocolClosed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackageClosedSourceReadoutCertificate P) :
  ThreeFlavorProtocolClosedSourceReadoutCertificate P :=
  { sourceReadoutCertificate := K.sourceReadoutCertificate
    sourceReadoutProtocolClosed :=
      P.sameScopePredicate.rootRealizationExhaustive /\
        P.polynomialLaw.allUnresolvedFreedomsDischarged
    sourceReadoutProtocolClosed_proof :=
      ⟨P.sameScopePredicate.rootRealizationExhaustive_proof,
        P.polynomialLaw.allUnresolvedFreedomsDischarged_proof⟩ }

/--
Package-closed readout payload.

The readout boundary now asks for a source certificate whose closure is
derived from the ambient same-scope package, not separately assumed.
-/
structure ThreeFlavorCanonicalPackageReadoutPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  packageClosedSourceReadout :
    ThreeFlavorPackageClosedSourceReadoutCertificate P

noncomputable def canonicalPackageReadoutPayloadAsProtocolPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalPackageReadoutPayload P) :
  ThreeFlavorCanonicalProtocolReadoutPayload P :=
  { protocolClosedSourceReadout :=
      packageClosedSourceReadoutCertificateAsProtocolClosed
        W.packageClosedSourceReadout }

noncomputable def canonicalPackageReadoutPayloadAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalPackageReadoutPayload P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalProtocolReadoutPayloadAsWindow
    (canonicalPackageReadoutPayloadAsProtocolPayload W)

theorem canonicalPackageReadoutPayload_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalPackageReadoutPayload P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalProtocolReadoutPayload_discharge_positiveReadoutNeed
    (canonicalPackageReadoutPayloadAsProtocolPayload W)

theorem canonicalPackageReadoutPayload_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalPackageReadoutPayload P) :
  (canonicalPackageReadoutPayloadAsWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalPackageReadoutPayloadAsWindow W).interval.upper :=
  canonicalProtocolReadoutPayload_contains_gapRatio
    (canonicalPackageReadoutPayloadAsProtocolPayload W)

/--
Flattened package readout payload.

The readout boundary now carries the bundled source certificate directly.
Package-derived protocol closure is reconstructed internally by the adapter.
-/
structure ThreeFlavorCanonicalFlattenedPackageReadoutPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  sourceReadoutCertificate :
    ThreeFlavorCanonicalSourceReadoutCertificate P

def flattenedPackageReadoutPayloadAsPackageClosedCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalFlattenedPackageReadoutPayload P) :
  ThreeFlavorPackageClosedSourceReadoutCertificate P :=
  { sourceReadoutCertificate := W.sourceReadoutCertificate }

noncomputable def canonicalFlattenedPackageReadoutPayloadAsPackagePayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalFlattenedPackageReadoutPayload P) :
  ThreeFlavorCanonicalPackageReadoutPayload P :=
  { packageClosedSourceReadout :=
      flattenedPackageReadoutPayloadAsPackageClosedCertificate W }

noncomputable def canonicalFlattenedPackageReadoutPayloadAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalFlattenedPackageReadoutPayload P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalPackageReadoutPayloadAsWindow
    (canonicalFlattenedPackageReadoutPayloadAsPackagePayload W)

theorem canonicalFlattenedPackageReadoutPayload_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalFlattenedPackageReadoutPayload P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalPackageReadoutPayload_discharge_positiveReadoutNeed
    (canonicalFlattenedPackageReadoutPayloadAsPackagePayload W)

theorem canonicalFlattenedPackageReadoutPayload_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (W : ThreeFlavorCanonicalFlattenedPackageReadoutPayload P) :
  (canonicalFlattenedPackageReadoutPayloadAsWindow W).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalFlattenedPackageReadoutPayloadAsWindow W).interval.upper :=
  canonicalPackageReadoutPayload_contains_gapRatio
    (canonicalFlattenedPackageReadoutPayloadAsPackagePayload W)

/--
Use the bundled source readout certificate directly as the readout witness.

This removes the remaining outer payload wrapper: the certificate itself now
feeds the canonical readout construction, while package-derived closure is
still reconstructed internally.
-/
def sourceReadoutCertificateAsFlattenedPackagePayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorCanonicalSourceReadoutCertificate P) :
  ThreeFlavorCanonicalFlattenedPackageReadoutPayload P :=
  { sourceReadoutCertificate := K }

noncomputable def sourceReadoutCertificateAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorCanonicalSourceReadoutCertificate P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalFlattenedPackageReadoutPayloadAsWindow
    (sourceReadoutCertificateAsFlattenedPackagePayload K)

theorem sourceReadoutCertificate_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorCanonicalSourceReadoutCertificate P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalFlattenedPackageReadoutPayload_discharge_positiveReadoutNeed
    (sourceReadoutCertificateAsFlattenedPackagePayload K)

theorem sourceReadoutCertificate_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorCanonicalSourceReadoutCertificate P) :
  (sourceReadoutCertificateAsWindow K).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (sourceReadoutCertificateAsWindow K).interval.upper :=
  canonicalFlattenedPackageReadoutPayload_contains_gapRatio
    (sourceReadoutCertificateAsFlattenedPackagePayload K)

/--
Source readout certificate with package-derived high-coefficient provenance.

Only the arithmetic high-coefficient fact is supplied locally; its
source-derived status is inherited from the same-scope polynomial-law audit.
-/
structure ThreeFlavorPackageHighSourceReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  packageHighCoefficient :
    ThreeFlavorPackageSourceHighCoefficient P
  sourceCauchyDomination :
    ThreeFlavorCanonicalSourceArithmeticCauchyDomination P
  sourceStrictMassOrdering :
    ThreeFlavorSourceStrictMassSquaredOrdering (A := A)

def packageHighSourceReadoutCertificateAsSourceReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackageHighSourceReadoutCertificate P) :
  ThreeFlavorCanonicalSourceReadoutCertificate P :=
  { sourceHighCoefficient :=
      packageSourceHighCoefficientAsSourceHighCoefficient
        K.packageHighCoefficient
    sourceCauchyDomination := K.sourceCauchyDomination
    sourceStrictMassOrdering := K.sourceStrictMassOrdering }

noncomputable def packageHighSourceReadoutCertificateAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackageHighSourceReadoutCertificate P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  sourceReadoutCertificateAsWindow
    (packageHighSourceReadoutCertificateAsSourceReadoutCertificate K)

theorem packageHighSourceReadoutCertificate_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackageHighSourceReadoutCertificate P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  sourceReadoutCertificate_discharge_positiveReadoutNeed
    (packageHighSourceReadoutCertificateAsSourceReadoutCertificate K)

theorem packageHighSourceReadoutCertificate_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackageHighSourceReadoutCertificate P) :
  (packageHighSourceReadoutCertificateAsWindow K).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (packageHighSourceReadoutCertificateAsWindow K).interval.upper :=
  sourceReadoutCertificate_contains_gapRatio
    (packageHighSourceReadoutCertificateAsSourceReadoutCertificate K)

/--
Source readout certificate with package-derived high-coefficient and Cauchy
provenance.

The high-coefficient source audit and source-arithmetic Cauchy computation
audit are both inherited from the ambient same-scope polynomial law.
-/
structure ThreeFlavorPackageHighCauchyReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  packageHighCoefficient :
    ThreeFlavorPackageSourceHighCoefficient P
  packageCauchyDomination :
    ThreeFlavorPackageSourceArithmeticCauchyDomination P
  sourceStrictMassOrdering :
    ThreeFlavorSourceStrictMassSquaredOrdering (A := A)

def packageHighCauchyReadoutCertificateAsPackageHighCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackageHighCauchyReadoutCertificate P) :
  ThreeFlavorPackageHighSourceReadoutCertificate P :=
  { packageHighCoefficient := K.packageHighCoefficient
    sourceCauchyDomination :=
      packageSourceArithmeticCauchyDominationAsSourceArithmeticCauchyDomination
        K.packageCauchyDomination
    sourceStrictMassOrdering := K.sourceStrictMassOrdering }

noncomputable def packageHighCauchyReadoutCertificateAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackageHighCauchyReadoutCertificate P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  packageHighSourceReadoutCertificateAsWindow
    (packageHighCauchyReadoutCertificateAsPackageHighCertificate K)

theorem packageHighCauchyReadoutCertificate_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackageHighCauchyReadoutCertificate P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  packageHighSourceReadoutCertificate_discharge_positiveReadoutNeed
    (packageHighCauchyReadoutCertificateAsPackageHighCertificate K)

theorem packageHighCauchyReadoutCertificate_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackageHighCauchyReadoutCertificate P) :
  (packageHighCauchyReadoutCertificateAsWindow K).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (packageHighCauchyReadoutCertificateAsWindow K).interval.upper :=
  packageHighSourceReadoutCertificate_contains_gapRatio
    (packageHighCauchyReadoutCertificateAsPackageHighCertificate K)

/--
Readout certificate with package-derived provenance on all three source
components.

The remaining local data are the mathematical witnesses themselves:
high-coefficient nonlinearity, rational Cauchy domination, and strict
mass-squared ordering.  Their source/protocol provenance is reconstructed from
the ambient same-scope package and gap-ratio algebra.
-/
structure ThreeFlavorPackageReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  packageHighCoefficient :
    ThreeFlavorPackageSourceHighCoefficient P
  packageCauchyDomination :
    ThreeFlavorPackageSourceArithmeticCauchyDomination P
  packageStrictMassOrdering :
    ThreeFlavorPackageStrictMassSquaredOrdering (A := A)

def packageReadoutCertificateAsPackageHighCauchyCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackageReadoutCertificate P) :
  ThreeFlavorPackageHighCauchyReadoutCertificate P :=
  { packageHighCoefficient := K.packageHighCoefficient
    packageCauchyDomination := K.packageCauchyDomination
    sourceStrictMassOrdering :=
      packageStrictMassSquaredOrderingAsSourceStrictMassSquaredOrdering
        K.packageStrictMassOrdering }

noncomputable def packageReadoutCertificateAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackageReadoutCertificate P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  packageHighCauchyReadoutCertificateAsWindow
    (packageReadoutCertificateAsPackageHighCauchyCertificate K)

theorem packageReadoutCertificate_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackageReadoutCertificate P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  packageHighCauchyReadoutCertificate_discharge_positiveReadoutNeed
    (packageReadoutCertificateAsPackageHighCauchyCertificate K)

theorem packageReadoutCertificate_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackageReadoutCertificate P) :
  (packageReadoutCertificateAsWindow K).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (packageReadoutCertificateAsWindow K).interval.upper :=
  packageHighCauchyReadoutCertificate_contains_gapRatio
    (packageReadoutCertificateAsPackageHighCauchyCertificate K)

/--
Package polynomial-arithmetic certificate.

This bundles the two polynomial-side arithmetic witnesses needed for readout:
a nonzero high coefficient and a rational Cauchy domination endpoint.
-/
structure ThreeFlavorPackagePolynomialArithmeticCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  packageHighCoefficient :
    ThreeFlavorPackageSourceHighCoefficient P
  packageCauchyDomination :
    ThreeFlavorPackageSourceArithmeticCauchyDomination P

def packagePolynomialArithmeticCertificateAsHighCauchyFields
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackagePolynomialArithmeticCertificate P) :
  ThreeFlavorPackageSourceHighCoefficient P ×
    ThreeFlavorPackageSourceArithmeticCauchyDomination P :=
  (K.packageHighCoefficient, K.packageCauchyDomination)

/--
Coherent package polynomial-arithmetic certificate.

The high-coefficient witness and Cauchy-domination witness are bundled with a
same-polynomial coherence audit.  The coherence proof is derived from the
ambient same-scope polynomial law rather than supplied as a separate external
assumption.
-/
structure ThreeFlavorCoherentPackagePolynomialArithmeticCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  polynomialArithmetic :
    ThreeFlavorPackagePolynomialArithmeticCertificate P
  samePolynomialArithmeticCoherence : Prop :=
    P.polynomialLaw.polynomialLawDerivedInternally
  samePolynomialArithmeticCoherence_proof :
    samePolynomialArithmeticCoherence

def coherentPackagePolynomialArithmeticCertificateAsPolynomialArithmetic
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorCoherentPackagePolynomialArithmeticCertificate P) :
  ThreeFlavorPackagePolynomialArithmeticCertificate P :=
  K.polynomialArithmetic

/--
Readout certificate with bundled polynomial arithmetic.

The readout boundary now separates only the polynomial-arithmetic certificate
from the physical ordering certificate.
-/
structure ThreeFlavorPackageArithmeticReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  polynomialArithmetic :
    ThreeFlavorPackagePolynomialArithmeticCertificate P
  packageStrictMassOrdering :
    ThreeFlavorPackageStrictMassSquaredOrdering (A := A)

def packageArithmeticReadoutCertificateAsPackageReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackageArithmeticReadoutCertificate P) :
  ThreeFlavorPackageReadoutCertificate P :=
  { packageHighCoefficient := K.polynomialArithmetic.packageHighCoefficient
    packageCauchyDomination := K.polynomialArithmetic.packageCauchyDomination
    packageStrictMassOrdering := K.packageStrictMassOrdering }

noncomputable def packageArithmeticReadoutCertificateAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackageArithmeticReadoutCertificate P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  packageReadoutCertificateAsWindow
    (packageArithmeticReadoutCertificateAsPackageReadoutCertificate K)

theorem packageArithmeticReadoutCertificate_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackageArithmeticReadoutCertificate P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  packageReadoutCertificate_discharge_positiveReadoutNeed
    (packageArithmeticReadoutCertificateAsPackageReadoutCertificate K)

theorem packageArithmeticReadoutCertificate_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackageArithmeticReadoutCertificate P) :
  (packageArithmeticReadoutCertificateAsWindow K).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (packageArithmeticReadoutCertificateAsWindow K).interval.upper :=
  packageReadoutCertificate_contains_gapRatio
    (packageArithmeticReadoutCertificateAsPackageReadoutCertificate K)

/--
Readout certificate with minimal strict-ordering input.

The gap-ratio algebra pass proof is now reconstructed from `A`; the ordering
side contributes only the two strict inequalities.
-/
structure ThreeFlavorMinimalOrderingReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  polynomialArithmetic :
    ThreeFlavorPackagePolynomialArithmeticCertificate P
  minimalStrictMassOrdering :
    ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A)

def minimalOrderingReadoutCertificateAsPackageArithmeticCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorMinimalOrderingReadoutCertificate P) :
  ThreeFlavorPackageArithmeticReadoutCertificate P :=
  { polynomialArithmetic := K.polynomialArithmetic
    packageStrictMassOrdering :=
      minimalPackageStrictMassSquaredOrderingAsPackageStrictMassSquaredOrdering
        K.minimalStrictMassOrdering }

noncomputable def minimalOrderingReadoutCertificateAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorMinimalOrderingReadoutCertificate P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  packageArithmeticReadoutCertificateAsWindow
    (minimalOrderingReadoutCertificateAsPackageArithmeticCertificate K)

theorem minimalOrderingReadoutCertificate_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorMinimalOrderingReadoutCertificate P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  packageArithmeticReadoutCertificate_discharge_positiveReadoutNeed
    (minimalOrderingReadoutCertificateAsPackageArithmeticCertificate K)

theorem minimalOrderingReadoutCertificate_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorMinimalOrderingReadoutCertificate P) :
  (minimalOrderingReadoutCertificateAsWindow K).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (minimalOrderingReadoutCertificateAsWindow K).interval.upper :=
  packageArithmeticReadoutCertificate_contains_gapRatio
    (minimalOrderingReadoutCertificateAsPackageArithmeticCertificate K)

/--
Readout certificate with coherent polynomial arithmetic and minimal ordering.

This makes the same-polynomial coherence of the high-coefficient and
Cauchy-domination witnesses explicit at the readout boundary.
-/
structure ThreeFlavorCoherentMinimalReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  coherentPolynomialArithmetic :
    ThreeFlavorCoherentPackagePolynomialArithmeticCertificate P
  minimalStrictMassOrdering :
    ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A)

def coherentMinimalReadoutCertificateAsMinimalOrderingCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorCoherentMinimalReadoutCertificate P) :
  ThreeFlavorMinimalOrderingReadoutCertificate P :=
  { polynomialArithmetic :=
      coherentPackagePolynomialArithmeticCertificateAsPolynomialArithmetic
        K.coherentPolynomialArithmetic
    minimalStrictMassOrdering := K.minimalStrictMassOrdering }

noncomputable def coherentMinimalReadoutCertificateAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorCoherentMinimalReadoutCertificate P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  minimalOrderingReadoutCertificateAsWindow
    (coherentMinimalReadoutCertificateAsMinimalOrderingCertificate K)

theorem coherentMinimalReadoutCertificate_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorCoherentMinimalReadoutCertificate P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  minimalOrderingReadoutCertificate_discharge_positiveReadoutNeed
    (coherentMinimalReadoutCertificateAsMinimalOrderingCertificate K)

theorem coherentMinimalReadoutCertificate_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorCoherentMinimalReadoutCertificate P) :
  (coherentMinimalReadoutCertificateAsWindow K).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (coherentMinimalReadoutCertificateAsWindow K).interval.upper :=
  minimalOrderingReadoutCertificate_contains_gapRatio
    (coherentMinimalReadoutCertificateAsMinimalOrderingCertificate K)

/--
Joint same-scope readout certificate.

This records that the coherent polynomial arithmetic and the minimal ordering
input are being used in one same-scope readout construction.  The joint
coherence proof is derived from the package's root readback lawfulness and
same-scope root realization controls.
-/
structure ThreeFlavorJointSameScopeReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  coherentReadout :
    ThreeFlavorCoherentMinimalReadoutCertificate P
  jointSameScopeReadoutCoherent : Prop :=
    P.sameScopePredicate.rootRealizationSameScope /\
      P.sameScopePredicate.rootReadbackLawful
  jointSameScopeReadoutCoherent_proof :
    jointSameScopeReadoutCoherent

def jointSameScopeReadoutCertificateAsCoherentMinimal
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorJointSameScopeReadoutCertificate P) :
  ThreeFlavorCoherentMinimalReadoutCertificate P :=
  K.coherentReadout

noncomputable def jointSameScopeReadoutCertificateAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorJointSameScopeReadoutCertificate P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  coherentMinimalReadoutCertificateAsWindow
    (jointSameScopeReadoutCertificateAsCoherentMinimal K)

theorem jointSameScopeReadoutCertificate_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorJointSameScopeReadoutCertificate P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  coherentMinimalReadoutCertificate_discharge_positiveReadoutNeed
    (jointSameScopeReadoutCertificateAsCoherentMinimal K)

theorem jointSameScopeReadoutCertificate_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorJointSameScopeReadoutCertificate P) :
  (jointSameScopeReadoutCertificateAsWindow K).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (jointSameScopeReadoutCertificateAsWindow K).interval.upper :=
  coherentMinimalReadoutCertificate_contains_gapRatio
    (jointSameScopeReadoutCertificateAsCoherentMinimal K)

/--
Flattened same-scope readout certificate.

The current witness carries only the coherent readout data.  The joint
same-scope coherence proof is reconstructed from the package's root-realization
and root-readback controls.
-/
structure ThreeFlavorFlattenedSameScopeReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  coherentReadout :
    ThreeFlavorCoherentMinimalReadoutCertificate P

def flattenedSameScopeReadoutCertificateAsJointSameScope
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorFlattenedSameScopeReadoutCertificate P) :
  ThreeFlavorJointSameScopeReadoutCertificate P :=
  { coherentReadout := K.coherentReadout
    jointSameScopeReadoutCoherent :=
      P.sameScopePredicate.rootRealizationSameScope /\
        P.sameScopePredicate.rootReadbackLawful
    jointSameScopeReadoutCoherent_proof :=
      ⟨P.sameScopePredicate.rootRealizationSameScope_proof,
        P.sameScopePredicate.rootReadbackLawful_proof⟩ }

noncomputable def flattenedSameScopeReadoutCertificateAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorFlattenedSameScopeReadoutCertificate P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  jointSameScopeReadoutCertificateAsWindow
    (flattenedSameScopeReadoutCertificateAsJointSameScope K)

theorem flattenedSameScopeReadoutCertificate_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorFlattenedSameScopeReadoutCertificate P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  jointSameScopeReadoutCertificate_discharge_positiveReadoutNeed
    (flattenedSameScopeReadoutCertificateAsJointSameScope K)

theorem flattenedSameScopeReadoutCertificate_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorFlattenedSameScopeReadoutCertificate P) :
  (flattenedSameScopeReadoutCertificateAsWindow K).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (flattenedSameScopeReadoutCertificateAsWindow K).interval.upper :=
  jointSameScopeReadoutCertificate_contains_gapRatio
    (flattenedSameScopeReadoutCertificateAsJointSameScope K)

/--
Use the coherent minimal readout certificate directly as the same-scope readout
witness.

This removes the remaining wrapper around the coherent readout object.  The
same-scope coherence certificate is still reconstructed internally from the
package.
-/
def coherentMinimalReadoutCertificateAsFlattenedSameScope
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorCoherentMinimalReadoutCertificate P) :
  ThreeFlavorFlattenedSameScopeReadoutCertificate P :=
  { coherentReadout := K }

noncomputable def coherentMinimalReadoutCertificateAsSameScopeWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorCoherentMinimalReadoutCertificate P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  flattenedSameScopeReadoutCertificateAsWindow
    (coherentMinimalReadoutCertificateAsFlattenedSameScope K)

theorem coherentMinimalReadoutCertificate_discharge_sameScopePositiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorCoherentMinimalReadoutCertificate P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  flattenedSameScopeReadoutCertificate_discharge_positiveReadoutNeed
    (coherentMinimalReadoutCertificateAsFlattenedSameScope K)

theorem coherentMinimalReadoutCertificate_sameScopeContains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorCoherentMinimalReadoutCertificate P) :
  (coherentMinimalReadoutCertificateAsSameScopeWindow K).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (coherentMinimalReadoutCertificateAsSameScopeWindow K).interval.upper :=
  flattenedSameScopeReadoutCertificate_contains_gapRatio
    (coherentMinimalReadoutCertificateAsFlattenedSameScope K)

/--
Reconstruct coherent polynomial arithmetic from the minimal ordering readout
certificate.

The same-polynomial arithmetic coherence proof is package-derived, so the
active target can return to the minimal ordering certificate while still using
the coherent same-scope readout route.
-/
def minimalOrderingReadoutCertificateAsCoherentMinimal
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorMinimalOrderingReadoutCertificate P) :
  ThreeFlavorCoherentMinimalReadoutCertificate P :=
  { coherentPolynomialArithmetic :=
      { polynomialArithmetic := K.polynomialArithmetic
        samePolynomialArithmeticCoherence :=
          P.polynomialLaw.polynomialLawDerivedInternally
        samePolynomialArithmeticCoherence_proof :=
          P.polynomialLaw.polynomialLawDerivedInternally_proof }
    minimalStrictMassOrdering := K.minimalStrictMassOrdering }

noncomputable def minimalOrderingReadoutCertificateAsCoherentSameScopeWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorMinimalOrderingReadoutCertificate P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  coherentMinimalReadoutCertificateAsSameScopeWindow
    (minimalOrderingReadoutCertificateAsCoherentMinimal K)

theorem minimalOrderingReadoutCertificate_discharge_coherentSameScopePositiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorMinimalOrderingReadoutCertificate P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  coherentMinimalReadoutCertificate_discharge_sameScopePositiveReadoutNeed
    (minimalOrderingReadoutCertificateAsCoherentMinimal K)

theorem minimalOrderingReadoutCertificate_coherentSameScopeContains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorMinimalOrderingReadoutCertificate P) :
  (minimalOrderingReadoutCertificateAsCoherentSameScopeWindow K).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (minimalOrderingReadoutCertificateAsCoherentSameScopeWindow K).interval.upper :=
  coherentMinimalReadoutCertificate_sameScopeContains_gapRatio
    (minimalOrderingReadoutCertificateAsCoherentMinimal K)

/--
Core readout certificate.

This bundles the two remaining mathematical inputs for the readout route:
package polynomial arithmetic and minimal strict mass ordering.
-/
structure ThreeFlavorReadoutCoreCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  polynomialArithmetic :
    ThreeFlavorPackagePolynomialArithmeticCertificate P
  minimalStrictMassOrdering :
    ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A)

def readoutCoreCertificateAsMinimalOrderingCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorReadoutCoreCertificate P) :
  ThreeFlavorMinimalOrderingReadoutCertificate P :=
  { polynomialArithmetic := K.polynomialArithmetic
    minimalStrictMassOrdering := K.minimalStrictMassOrdering }

noncomputable def readoutCoreCertificateAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorReadoutCoreCertificate P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  minimalOrderingReadoutCertificateAsCoherentSameScopeWindow
    (readoutCoreCertificateAsMinimalOrderingCertificate K)

theorem readoutCoreCertificate_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorReadoutCoreCertificate P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  minimalOrderingReadoutCertificate_discharge_coherentSameScopePositiveReadoutNeed
    (readoutCoreCertificateAsMinimalOrderingCertificate K)

theorem readoutCoreCertificate_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorReadoutCoreCertificate P) :
  (readoutCoreCertificateAsWindow K).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (readoutCoreCertificateAsWindow K).interval.upper :=
  minimalOrderingReadoutCertificate_coherentSameScopeContains_gapRatio
    (readoutCoreCertificateAsMinimalOrderingCertificate K)

/--
Flat readout arithmetic data.

This exposes the remaining mathematical inputs directly: a high nonzero
coefficient, a rational Cauchy domination endpoint, the algebra-pass witness,
and the two strict mass-order inequalities.
-/
structure ThreeFlavorFlatReadoutArithmeticData
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  witnessDegree : ℕ
  witnessDegree_ge_two :
    2 ≤ witnessDegree
  witnessCoefficient_ne_zero :
    P.sameScopePredicate.polynomial.coeff witnessDegree ≠ 0
  boundNumerator : Nat
  boundNumerator_pos : 0 < boundNumerator
  boundDenominator : Nat
  boundDenominator_pos : 0 < boundDenominator
  bound : ℚ :=
    (boundNumerator : ℚ) / (boundDenominator : ℚ)
  bound_eq_numeral :
    bound = (boundNumerator : ℚ) / (boundDenominator : ℚ)
  cauchyBound_le_bound :
    ((sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P).explicitPolynomial.cauchyBound : Real) <=
      (bound : Real)
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  level0_lt_level1 :
    A.massSquaredLevelOf 0 < A.massSquaredLevelOf 1
  level1_lt_level2 :
    A.massSquaredLevelOf 1 < A.massSquaredLevelOf 2

def flatReadoutArithmeticDataAsCoreCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorFlatReadoutArithmeticData P) :
  ThreeFlavorReadoutCoreCertificate P :=
  { polynomialArithmetic :=
      { packageHighCoefficient :=
          { witnessDegree := D.witnessDegree
            witnessDegree_ge_two := D.witnessDegree_ge_two
            witnessCoefficient_ne_zero := D.witnessCoefficient_ne_zero }
        packageCauchyDomination :=
          { boundNumerator := D.boundNumerator
            boundNumerator_pos := D.boundNumerator_pos
            boundDenominator := D.boundDenominator
            boundDenominator_pos := D.boundDenominator_pos
            bound := D.bound
            bound_eq_numeral := D.bound_eq_numeral
            cauchyBound_le_bound := D.cauchyBound_le_bound } }
    minimalStrictMassOrdering :=
      { gapRatioAlgebraPasses := D.gapRatioAlgebraPasses
        level0_lt_level1 := D.level0_lt_level1
        level1_lt_level2 := D.level1_lt_level2 } }

noncomputable def flatReadoutArithmeticDataAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorFlatReadoutArithmeticData P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  readoutCoreCertificateAsWindow
    (flatReadoutArithmeticDataAsCoreCertificate D)

theorem flatReadoutArithmeticData_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorFlatReadoutArithmeticData P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  readoutCoreCertificate_discharge_positiveReadoutNeed
    (flatReadoutArithmeticDataAsCoreCertificate D)

theorem flatReadoutArithmeticData_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorFlatReadoutArithmeticData P) :
  (flatReadoutArithmeticDataAsWindow D).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (flatReadoutArithmeticDataAsWindow D).interval.upper :=
  readoutCoreCertificate_contains_gapRatio
    (flatReadoutArithmeticDataAsCoreCertificate D)

/--
Flat readout arithmetic data without a separate bound field.

The rational endpoint is determined by the numerator and denominator.  The
Cauchy domination proof targets that displayed quotient directly, so the
separate `bound` and `bound_eq_numeral` fields are reconstructed internally.
-/
structure ThreeFlavorNumeralReadoutArithmeticData
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  witnessDegree : ℕ
  witnessDegree_ge_two :
    2 ≤ witnessDegree
  witnessCoefficient_ne_zero :
    P.sameScopePredicate.polynomial.coeff witnessDegree ≠ 0
  boundNumerator : Nat
  boundNumerator_pos : 0 < boundNumerator
  boundDenominator : Nat
  boundDenominator_pos : 0 < boundDenominator
  cauchyBound_le_quotient :
    ((sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P).explicitPolynomial.cauchyBound : Real) <=
      (((boundNumerator : ℚ) / (boundDenominator : ℚ)) : Real)
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  level0_lt_level1 :
    A.massSquaredLevelOf 0 < A.massSquaredLevelOf 1
  level1_lt_level2 :
    A.massSquaredLevelOf 1 < A.massSquaredLevelOf 2

def numeralReadoutArithmeticDataAsFlatData
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorNumeralReadoutArithmeticData P) :
  ThreeFlavorFlatReadoutArithmeticData P :=
  { witnessDegree := D.witnessDegree
    witnessDegree_ge_two := D.witnessDegree_ge_two
    witnessCoefficient_ne_zero := D.witnessCoefficient_ne_zero
    boundNumerator := D.boundNumerator
    boundNumerator_pos := D.boundNumerator_pos
    boundDenominator := D.boundDenominator
    boundDenominator_pos := D.boundDenominator_pos
    bound := (D.boundNumerator : ℚ) / (D.boundDenominator : ℚ)
    bound_eq_numeral := rfl
    cauchyBound_le_bound := by
      simpa using D.cauchyBound_le_quotient
    gapRatioAlgebraPasses := D.gapRatioAlgebraPasses
    level0_lt_level1 := D.level0_lt_level1
    level1_lt_level2 := D.level1_lt_level2 }

noncomputable def numeralReadoutArithmeticDataAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorNumeralReadoutArithmeticData P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  flatReadoutArithmeticDataAsWindow
    (numeralReadoutArithmeticDataAsFlatData D)

theorem numeralReadoutArithmeticData_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorNumeralReadoutArithmeticData P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  flatReadoutArithmeticData_discharge_positiveReadoutNeed
    (numeralReadoutArithmeticDataAsFlatData D)

theorem numeralReadoutArithmeticData_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorNumeralReadoutArithmeticData P) :
  (numeralReadoutArithmeticDataAsWindow D).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (numeralReadoutArithmeticDataAsWindow D).interval.upper :=
  flatReadoutArithmeticData_contains_gapRatio
    (numeralReadoutArithmeticDataAsFlatData D)

/--
Degree-two readout arithmetic data.

This specializes the high-coefficient witness to coefficient `2`, eliminating
the separate witness-degree and `2 <= witnessDegree` fields from the active
target.  The general numeral data object is reconstructed internally.
-/
structure ThreeFlavorDegreeTwoReadoutArithmeticData
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  degreeTwoCoefficient_ne_zero :
    P.sameScopePredicate.polynomial.coeff 2 ≠ 0
  boundNumerator : Nat
  boundNumerator_pos : 0 < boundNumerator
  boundDenominator : Nat
  boundDenominator_pos : 0 < boundDenominator
  cauchyBound_le_quotient :
    ((sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P).explicitPolynomial.cauchyBound : Real) <=
      (((boundNumerator : ℚ) / (boundDenominator : ℚ)) : Real)
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  level0_lt_level1 :
    A.massSquaredLevelOf 0 < A.massSquaredLevelOf 1
  level1_lt_level2 :
    A.massSquaredLevelOf 1 < A.massSquaredLevelOf 2

def degreeTwoReadoutArithmeticDataAsNumeralData
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorDegreeTwoReadoutArithmeticData P) :
  ThreeFlavorNumeralReadoutArithmeticData P :=
  { witnessDegree := 2
    witnessDegree_ge_two := le_rfl
    witnessCoefficient_ne_zero := D.degreeTwoCoefficient_ne_zero
    boundNumerator := D.boundNumerator
    boundNumerator_pos := D.boundNumerator_pos
    boundDenominator := D.boundDenominator
    boundDenominator_pos := D.boundDenominator_pos
    cauchyBound_le_quotient := D.cauchyBound_le_quotient
    gapRatioAlgebraPasses := D.gapRatioAlgebraPasses
    level0_lt_level1 := D.level0_lt_level1
    level1_lt_level2 := D.level1_lt_level2 }

noncomputable def degreeTwoReadoutArithmeticDataAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorDegreeTwoReadoutArithmeticData P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  numeralReadoutArithmeticDataAsWindow
    (degreeTwoReadoutArithmeticDataAsNumeralData D)

theorem degreeTwoReadoutArithmeticData_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorDegreeTwoReadoutArithmeticData P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  numeralReadoutArithmeticData_discharge_positiveReadoutNeed
    (degreeTwoReadoutArithmeticDataAsNumeralData D)

theorem degreeTwoReadoutArithmeticData_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorDegreeTwoReadoutArithmeticData P) :
  (degreeTwoReadoutArithmeticDataAsWindow D).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (degreeTwoReadoutArithmeticDataAsWindow D).interval.upper :=
  numeralReadoutArithmeticData_contains_gapRatio
    (degreeTwoReadoutArithmeticDataAsNumeralData D)

/--
Positive numeral readout arithmetic data.

The rational Cauchy endpoint uses successor numerals for numerator and
denominator.  This removes the separate positivity proof obligations from the
active target: positivity is reconstructed internally by `Nat.succ_pos`.
-/
structure ThreeFlavorPositiveNumeralReadoutArithmeticData
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  degreeTwoCoefficient_ne_zero :
    P.sameScopePredicate.polynomial.coeff 2 ≠ 0
  boundNumeratorPred : Nat
  boundDenominatorPred : Nat
  cauchyBound_le_successor_quotient :
    ((sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P).explicitPolynomial.cauchyBound : Real) <=
      ((((boundNumeratorPred.succ : Nat) : ℚ) /
          (((boundDenominatorPred.succ : Nat) : ℚ))) : Real)
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  level0_lt_level1 :
    A.massSquaredLevelOf 0 < A.massSquaredLevelOf 1
  level1_lt_level2 :
    A.massSquaredLevelOf 1 < A.massSquaredLevelOf 2

def positiveNumeralReadoutArithmeticDataAsDegreeTwoData
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorPositiveNumeralReadoutArithmeticData P) :
  ThreeFlavorDegreeTwoReadoutArithmeticData P :=
  { degreeTwoCoefficient_ne_zero := D.degreeTwoCoefficient_ne_zero
    boundNumerator := D.boundNumeratorPred.succ
    boundNumerator_pos := Nat.succ_pos D.boundNumeratorPred
    boundDenominator := D.boundDenominatorPred.succ
    boundDenominator_pos := Nat.succ_pos D.boundDenominatorPred
    cauchyBound_le_quotient := D.cauchyBound_le_successor_quotient
    gapRatioAlgebraPasses := D.gapRatioAlgebraPasses
    level0_lt_level1 := D.level0_lt_level1
    level1_lt_level2 := D.level1_lt_level2 }

noncomputable def positiveNumeralReadoutArithmeticDataAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorPositiveNumeralReadoutArithmeticData P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  degreeTwoReadoutArithmeticDataAsWindow
    (positiveNumeralReadoutArithmeticDataAsDegreeTwoData D)

theorem positiveNumeralReadoutArithmeticData_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorPositiveNumeralReadoutArithmeticData P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  degreeTwoReadoutArithmeticData_discharge_positiveReadoutNeed
    (positiveNumeralReadoutArithmeticDataAsDegreeTwoData D)

theorem positiveNumeralReadoutArithmeticData_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorPositiveNumeralReadoutArithmeticData P) :
  (positiveNumeralReadoutArithmeticDataAsWindow D).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (positiveNumeralReadoutArithmeticDataAsWindow D).interval.upper :=
  degreeTwoReadoutArithmeticData_contains_gapRatio
    (positiveNumeralReadoutArithmeticDataAsDegreeTwoData D)

/--
Positive-gap numeral readout arithmetic data.

This bypasses strict mass-level ordering.  The readout only needs positivity
of the two quotient gaps, so the active target carries those gap-positivity
facts directly.
-/
structure ThreeFlavorPositiveGapNumeralReadoutData
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  degreeTwoCoefficient_ne_zero :
    P.sameScopePredicate.polynomial.coeff 2 ≠ 0
  boundNumeratorPred : Nat
  boundDenominatorPred : Nat
  cauchyBound_le_successor_quotient :
    ((sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P).explicitPolynomial.cauchyBound : Real) <=
      ((((boundNumeratorPred.succ : Nat) : ℚ) /
          (((boundDenominatorPred.succ : Nat) : ℚ))) : Real)
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  solarGap_pos :
    0 < threeFlavorSolarGap A.massSquaredLevelOf
  atmosphericGap_pos :
    0 < threeFlavorAtmosphericGap A.massSquaredLevelOf

def positiveGapNumeralReadoutDataAsArithmeticPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorPositiveGapNumeralReadoutData P) :
  ThreeFlavorCanonicalArithmeticReadoutPayload P :=
  { highCoefficient :=
      { witnessDegree := 2
        witnessDegree_ge_two := le_rfl
        witnessCoefficient_ne_zero := D.degreeTwoCoefficient_ne_zero }
    cauchyDomination :=
      { boundNumerator := D.boundNumeratorPred.succ
        boundNumerator_pos := Nat.succ_pos D.boundNumeratorPred
        boundDenominator := D.boundDenominatorPred.succ
        boundDenominator_pos := Nat.succ_pos D.boundDenominatorPred
        bound :=
          ((D.boundNumeratorPred.succ : Nat) : ℚ) /
            (((D.boundDenominatorPred.succ : Nat) : ℚ))
        bound_eq_numeral := rfl
        cauchyBound_le_bound := by
          simpa using D.cauchyBound_le_successor_quotient
        boundTargetsExplicitPolynomial :=
          P.polynomialLaw.polynomialLawDerivedInternally
        boundTargetsExplicitPolynomial_proof :=
          P.polynomialLaw.polynomialLawDerivedInternally_proof
        cauchyBoundComputedFromCoefficientTable :=
          P.polynomialLaw.polynomialLawDerivedInternally
        cauchyBoundComputedFromCoefficientTable_proof :=
          P.polynomialLaw.polynomialLawDerivedInternally_proof
        rationalDominationComputedFromCoefficientTable :=
          P.polynomialLaw.polynomialLawDerivedInternally
        rationalDominationComputedFromCoefficientTable_proof :=
          P.polynomialLaw.polynomialLawDerivedInternally_proof
        noEmpiricalBoundImport :=
          P.polynomialLaw.noEmpiricalFitImport /\
            P.sameScopePredicate.noEmpiricalRootImport
        noEmpiricalBoundImport_proof :=
          ⟨P.polynomialLaw.noEmpiricalFitImport_proof,
            P.sameScopePredicate.noEmpiricalRootImport_proof⟩
        noBoundFitTuning :=
          P.polynomialLaw.noOneAnchorImport /\
            P.polynomialLaw.allUnresolvedFreedomsDischarged
        noBoundFitTuning_proof :=
          ⟨P.polynomialLaw.noOneAnchorImport_proof,
            P.polynomialLaw.allUnresolvedFreedomsDischarged_proof⟩ }
    orderedGapPositivity :=
      { gapRatioAlgebraPasses := D.gapRatioAlgebraPasses
        solarGap_pos := D.solarGap_pos
        atmosphericGap_pos := D.atmosphericGap_pos } }

noncomputable def positiveGapNumeralReadoutDataAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorPositiveGapNumeralReadoutData P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalArithmeticReadoutPayloadAsWindow
    (positiveGapNumeralReadoutDataAsArithmeticPayload D)

theorem positiveGapNumeralReadoutData_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorPositiveGapNumeralReadoutData P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalArithmeticReadoutPayload_discharge_positiveReadoutNeed
    (positiveGapNumeralReadoutDataAsArithmeticPayload D)

theorem positiveGapNumeralReadoutData_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorPositiveGapNumeralReadoutData P) :
  (positiveGapNumeralReadoutDataAsWindow D).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (positiveGapNumeralReadoutDataAsWindow D).interval.upper :=
  canonicalArithmeticReadoutPayload_contains_gapRatio
    (positiveGapNumeralReadoutDataAsArithmeticPayload D)

/--
Positive gap orientation certificate.

This packages the orientation content needed for the ratio readout: the
gap-ratio algebra passes and both quotient gaps are positive.
-/
structure ThreeFlavorPositiveGapOrientation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  solarGap_pos :
    0 < threeFlavorSolarGap A.massSquaredLevelOf
  atmosphericGap_pos :
    0 < threeFlavorAtmosphericGap A.massSquaredLevelOf

def positiveGapOrientationAsSlimOrderedGapPositivity
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (O : ThreeFlavorPositiveGapOrientation (A := A)) :
  ThreeFlavorSlimOrderedGapPositivity (A := A) :=
  { gapRatioAlgebraPasses := O.gapRatioAlgebraPasses
    solarGap_pos := O.solarGap_pos
    atmosphericGap_pos := O.atmosphericGap_pos }

theorem positiveGapOrientation_gapRatio_pos
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (O : ThreeFlavorPositiveGapOrientation (A := A)) :
  0 < threeFlavorGapRatio A.massSquaredLevelOf := by
  unfold threeFlavorGapRatio
  exact div_pos O.solarGap_pos O.atmosphericGap_pos

def positiveGapOrientationAsPositiveSignPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (O : ThreeFlavorPositiveGapOrientation (A := A)) :
  ThreeFlavorCanonicalPositiveSignPayload P := by
  let G := sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P
  have hroot :
      G.selectedRoot = threeFlavorGapRatio A.massSquaredLevelOf :=
    algebraicClosedRootPresentation_selectedRoot_eq_gapRatio G
  exact
  { selectedRoot_pos := by
      rw [hroot]
      exact positiveGapOrientation_gapRatio_pos O }

def strictMassSquaredOrderingAsPositiveGapOrientation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A)) :
  ThreeFlavorPositiveGapOrientation (A := A) :=
  let S := strictMassSquaredOrderingAsSlimOrderedGapPositivity O
  { gapRatioAlgebraPasses := S.gapRatioAlgebraPasses
    solarGap_pos := S.solarGap_pos
    atmosphericGap_pos := S.atmosphericGap_pos }

def packageStrictMassSquaredOrderingAsPositiveGapOrientation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (O : ThreeFlavorPackageStrictMassSquaredOrdering (A := A)) :
  ThreeFlavorPositiveGapOrientation (A := A) :=
  strictMassSquaredOrderingAsPositiveGapOrientation
    { gapRatioAlgebraPasses := O.gapRatioAlgebraPasses
      level0_lt_level1 := O.level0_lt_level1
      level1_lt_level2 := O.level1_lt_level2 }

def minimalPackageStrictMassSquaredOrderingAsPositiveGapOrientation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A)) :
  ThreeFlavorPositiveGapOrientation (A := A) :=
  packageStrictMassSquaredOrderingAsPositiveGapOrientation
    (minimalPackageStrictMassSquaredOrderingAsPackageStrictMassSquaredOrdering O)

/--
Positive-gap readout data with bundled orientation.

The polynomial/numeral side remains explicit, while the orientation side is a
single positive-gap certificate.
-/
structure ThreeFlavorOrientedPositiveGapReadoutData
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  degreeTwoCoefficient_ne_zero :
    P.sameScopePredicate.polynomial.coeff 2 ≠ 0
  boundNumeratorPred : Nat
  boundDenominatorPred : Nat
  cauchyBound_le_successor_quotient :
    ((sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P).explicitPolynomial.cauchyBound : Real) <=
      ((((boundNumeratorPred.succ : Nat) : ℚ) /
          (((boundDenominatorPred.succ : Nat) : ℚ))) : Real)
  positiveGapOrientation :
    ThreeFlavorPositiveGapOrientation (A := A)

def orientedPositiveGapReadoutDataAsPositiveGapData
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorOrientedPositiveGapReadoutData P) :
  ThreeFlavorPositiveGapNumeralReadoutData P :=
  { degreeTwoCoefficient_ne_zero := D.degreeTwoCoefficient_ne_zero
    boundNumeratorPred := D.boundNumeratorPred
    boundDenominatorPred := D.boundDenominatorPred
    cauchyBound_le_successor_quotient := D.cauchyBound_le_successor_quotient
    gapRatioAlgebraPasses := D.positiveGapOrientation.gapRatioAlgebraPasses
    solarGap_pos := D.positiveGapOrientation.solarGap_pos
    atmosphericGap_pos := D.positiveGapOrientation.atmosphericGap_pos }

noncomputable def orientedPositiveGapReadoutDataAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorOrientedPositiveGapReadoutData P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  positiveGapNumeralReadoutDataAsWindow
    (orientedPositiveGapReadoutDataAsPositiveGapData D)

theorem orientedPositiveGapReadoutData_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorOrientedPositiveGapReadoutData P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  positiveGapNumeralReadoutData_discharge_positiveReadoutNeed
    (orientedPositiveGapReadoutDataAsPositiveGapData D)

theorem orientedPositiveGapReadoutData_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorOrientedPositiveGapReadoutData P) :
  (orientedPositiveGapReadoutDataAsWindow D).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (orientedPositiveGapReadoutDataAsWindow D).interval.upper :=
  positiveGapNumeralReadoutData_contains_gapRatio
    (orientedPositiveGapReadoutDataAsPositiveGapData D)

/--
Polynomial/numeral readout certificate.

This bundles the polynomial nonlinearity witness and successor-coded Cauchy
endpoint into one readout-numeral certificate.
-/
structure ThreeFlavorPolynomialNumeralReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  degreeTwoCoefficient_ne_zero :
    P.sameScopePredicate.polynomial.coeff 2 ≠ 0
  boundNumeratorPred : Nat
  boundDenominatorPred : Nat
  cauchyBound_le_successor_quotient :
    ((sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P).explicitPolynomial.cauchyBound : Real) <=
      ((((boundNumeratorPred.succ : Nat) : ℚ) /
          (((boundDenominatorPred.succ : Nat) : ℚ))) : Real)

/--
Oriented readout data with the polynomial/numeral side bundled.
-/
structure ThreeFlavorBundledPositiveGapReadoutData
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A) where
  polynomialNumeralReadout :
    ThreeFlavorPolynomialNumeralReadoutCertificate P
  positiveGapOrientation :
    ThreeFlavorPositiveGapOrientation (A := A)

def packageSourceArithmeticCauchyDominationAsPolynomialNumeralReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (degreeTwoCoefficient_ne_zero :
    P.sameScopePredicate.polynomial.coeff 2 ≠ 0)
  (B : ThreeFlavorPackageSourceArithmeticCauchyDomination P) :
  ThreeFlavorPolynomialNumeralReadoutCertificate P :=
  { degreeTwoCoefficient_ne_zero := degreeTwoCoefficient_ne_zero
    boundNumeratorPred := B.boundNumerator.pred
    boundDenominatorPred := B.boundDenominator.pred
    cauchyBound_le_successor_quotient := by
      have hn : B.boundNumerator.pred.succ = B.boundNumerator :=
        Nat.succ_pred_eq_of_pos B.boundNumerator_pos
      have hd : B.boundDenominator.pred.succ = B.boundDenominator :=
        Nat.succ_pred_eq_of_pos B.boundDenominator_pos
      calc
        ((sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P).explicitPolynomial.cauchyBound : Real)
            <= (B.bound : Real) := B.cauchyBound_le_bound
        _ =
            ((((B.boundNumerator.pred.succ : Nat) : ℚ) /
              (((B.boundDenominator.pred.succ : Nat) : ℚ))) : Real) := by
              rw [B.bound_eq_numeral, hn, hd]
              norm_num }

def packageCauchyAndPositiveGapAsBundledReadoutData
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (degreeTwoCoefficient_ne_zero :
    P.sameScopePredicate.polynomial.coeff 2 ≠ 0)
  (B : ThreeFlavorPackageSourceArithmeticCauchyDomination P)
  (O : ThreeFlavorPositiveGapOrientation (A := A)) :
  ThreeFlavorBundledPositiveGapReadoutData P :=
  { polynomialNumeralReadout :=
      packageSourceArithmeticCauchyDominationAsPolynomialNumeralReadoutCertificate
        degreeTwoCoefficient_ne_zero B
    positiveGapOrientation := O }

theorem packageSourceHighCoefficient_degreeTwoCoefficient_ne_zero
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackageSourceHighCoefficient P)
  (witnessDegree_eq_two : K.witnessDegree = 2) :
  P.sameScopePredicate.polynomial.coeff 2 ≠ 0 := by
  simpa [witnessDegree_eq_two] using K.witnessCoefficient_ne_zero

def packagePolynomialArithmeticAndPositiveGapAsBundledReadoutData
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackagePolynomialArithmeticCertificate P)
  (witnessDegree_eq_two : K.packageHighCoefficient.witnessDegree = 2)
  (O : ThreeFlavorPositiveGapOrientation (A := A)) :
  ThreeFlavorBundledPositiveGapReadoutData P :=
  packageCauchyAndPositiveGapAsBundledReadoutData
    (packageSourceHighCoefficient_degreeTwoCoefficient_ne_zero
      K.packageHighCoefficient witnessDegree_eq_two)
    K.packageCauchyDomination
    O

def packagePolynomialArithmeticAndMinimalOrderingAsBundledReadoutData
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorPackagePolynomialArithmeticCertificate P)
  (witnessDegree_eq_two : K.packageHighCoefficient.witnessDegree = 2)
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A)) :
  ThreeFlavorBundledPositiveGapReadoutData P :=
  packagePolynomialArithmeticAndPositiveGapAsBundledReadoutData
    K witnessDegree_eq_two
    (minimalPackageStrictMassSquaredOrderingAsPositiveGapOrientation O)

def readoutCoreCertificateAsBundledPositiveGapReadoutData
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorReadoutCoreCertificate P)
  (witnessDegree_eq_two :
    K.polynomialArithmetic.packageHighCoefficient.witnessDegree = 2) :
  ThreeFlavorBundledPositiveGapReadoutData P :=
  packagePolynomialArithmeticAndMinimalOrderingAsBundledReadoutData
    K.polynomialArithmetic witnessDegree_eq_two K.minimalStrictMassOrdering

def bundledPositiveGapReadoutDataAsOrientedData
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorBundledPositiveGapReadoutData P) :
  ThreeFlavorOrientedPositiveGapReadoutData P :=
  { degreeTwoCoefficient_ne_zero :=
      D.polynomialNumeralReadout.degreeTwoCoefficient_ne_zero
    boundNumeratorPred := D.polynomialNumeralReadout.boundNumeratorPred
    boundDenominatorPred := D.polynomialNumeralReadout.boundDenominatorPred
    cauchyBound_le_successor_quotient :=
      D.polynomialNumeralReadout.cauchyBound_le_successor_quotient
    positiveGapOrientation := D.positiveGapOrientation }

noncomputable def bundledPositiveGapReadoutDataAsWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorBundledPositiveGapReadoutData P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  orientedPositiveGapReadoutDataAsWindow
    (bundledPositiveGapReadoutDataAsOrientedData D)

theorem bundledPositiveGapReadoutData_discharge_positiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorBundledPositiveGapReadoutData P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  orientedPositiveGapReadoutData_discharge_positiveReadoutNeed
    (bundledPositiveGapReadoutDataAsOrientedData D)

theorem bundledPositiveGapReadoutData_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorBundledPositiveGapReadoutData P) :
  (bundledPositiveGapReadoutDataAsWindow D).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (bundledPositiveGapReadoutDataAsWindow D).interval.upper :=
  orientedPositiveGapReadoutData_contains_gapRatio
    (bundledPositiveGapReadoutDataAsOrientedData D)

/--
Direct positive-gap readout route.

This consumes the positive-gap orientation as a direct sign witness, avoiding
the ordered-gap adapter chain.
-/
noncomputable def bundledPositiveGapReadoutDataAsLeanPayload
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorBundledPositiveGapReadoutData P) :
  ThreeFlavorCanonicalLeanReadoutPayload P :=
  { polynomialNonlinearAudit :=
      sameScopePolynomialHighCoefficientAsNonlinearAudit P
        { witnessDegree := 2
          witnessDegree_ge_two := le_rfl
          witnessCoefficient_ne_zero :=
            D.polynomialNumeralReadout.degreeTwoCoefficient_ne_zero }
    cauchyDomination :=
      { boundNumerator := D.polynomialNumeralReadout.boundNumeratorPred.succ
        boundNumerator_pos :=
          Nat.succ_pos D.polynomialNumeralReadout.boundNumeratorPred
        boundDenominator := D.polynomialNumeralReadout.boundDenominatorPred.succ
        boundDenominator_pos :=
          Nat.succ_pos D.polynomialNumeralReadout.boundDenominatorPred
        bound :=
          ((D.polynomialNumeralReadout.boundNumeratorPred.succ : Nat) : ℚ) /
            (((D.polynomialNumeralReadout.boundDenominatorPred.succ : Nat) : ℚ))
        bound_eq_numeral := rfl
        cauchyBound_le_bound := by
          simpa using
            D.polynomialNumeralReadout.cauchyBound_le_successor_quotient
        boundTargetsExplicitPolynomial :=
          P.polynomialLaw.polynomialLawDerivedInternally
        boundTargetsExplicitPolynomial_proof :=
          P.polynomialLaw.polynomialLawDerivedInternally_proof
        cauchyBoundComputedFromCoefficientTable :=
          P.polynomialLaw.polynomialLawDerivedInternally
        cauchyBoundComputedFromCoefficientTable_proof :=
          P.polynomialLaw.polynomialLawDerivedInternally_proof
        rationalDominationComputedFromCoefficientTable :=
          P.polynomialLaw.polynomialLawDerivedInternally
        rationalDominationComputedFromCoefficientTable_proof :=
          P.polynomialLaw.polynomialLawDerivedInternally_proof
        noEmpiricalBoundImport :=
          P.polynomialLaw.noEmpiricalFitImport /\
            P.sameScopePredicate.noEmpiricalRootImport
        noEmpiricalBoundImport_proof :=
          ⟨P.polynomialLaw.noEmpiricalFitImport_proof,
            P.sameScopePredicate.noEmpiricalRootImport_proof⟩
        noBoundFitTuning :=
          P.polynomialLaw.noOneAnchorImport /\
            P.polynomialLaw.allUnresolvedFreedomsDischarged
        noBoundFitTuning_proof :=
          ⟨P.polynomialLaw.noOneAnchorImport_proof,
            P.polynomialLaw.allUnresolvedFreedomsDischarged_proof⟩ }
    positiveSign :=
      positiveGapOrientationAsPositiveSignPayload
        D.positiveGapOrientation }

noncomputable def bundledPositiveGapReadoutDataAsDirectWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorBundledPositiveGapReadoutData P) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalLeanReadoutPayloadAsWindow
    (bundledPositiveGapReadoutDataAsLeanPayload D)

theorem bundledPositiveGapReadoutData_discharge_directPositiveReadoutNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorBundledPositiveGapReadoutData P) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  canonicalLeanReadoutPayload_discharge_positiveReadoutNeed
    (bundledPositiveGapReadoutDataAsLeanPayload D)

theorem bundledPositiveGapReadoutData_directContains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (D : ThreeFlavorBundledPositiveGapReadoutData P) :
  (bundledPositiveGapReadoutDataAsDirectWindow D).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (bundledPositiveGapReadoutDataAsDirectWindow D).interval.upper :=
  canonicalLeanReadoutPayload_contains_gapRatio
    (bundledPositiveGapReadoutDataAsLeanPayload D)

noncomputable def readoutCoreCertificateAsDirectPositiveGapWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorReadoutCoreCertificate P)
  (witnessDegree_eq_two :
    K.polynomialArithmetic.packageHighCoefficient.witnessDegree = 2) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  bundledPositiveGapReadoutDataAsDirectWindow
    (readoutCoreCertificateAsBundledPositiveGapReadoutData
      K witnessDegree_eq_two)

theorem readoutCoreCertificate_discharge_directPositiveGapNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorReadoutCoreCertificate P)
  (witnessDegree_eq_two :
    K.polynomialArithmetic.packageHighCoefficient.witnessDegree = 2) :
  Not (NeedsThreeFlavorPositiveSourceDerivedReadoutWindow
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :=
  bundledPositiveGapReadoutData_discharge_directPositiveReadoutNeed
    (readoutCoreCertificateAsBundledPositiveGapReadoutData
      K witnessDegree_eq_two)

theorem readoutCoreCertificate_directPositiveGapContains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (K : ThreeFlavorReadoutCoreCertificate P)
  (witnessDegree_eq_two :
    K.polynomialArithmetic.packageHighCoefficient.witnessDegree = 2) :
  (readoutCoreCertificateAsDirectPositiveGapWindow
      K witnessDegree_eq_two).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (readoutCoreCertificateAsDirectPositiveGapWindow
        K witnessDegree_eq_two).interval.upper :=
  bundledPositiveGapReadoutData_directContains_gapRatio
    (readoutCoreCertificateAsBundledPositiveGapReadoutData
      K witnessDegree_eq_two)

noncomputable def sourceRationalPolynomialCandidateAsPackageSourceHighCoefficient
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (Q :
    ThreeFlavorSourceRationalPolynomialCandidate ℚ
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)) :
  ThreeFlavorPackageSourceHighCoefficient P :=
  { witnessDegree := Q.witnessDegree
    witnessDegree_ge_two := Q.witnessDegree_ge_two
    witnessCoefficient_ne_zero := by
      have hpoly :
          Q.sourcePolynomial = P.sameScopePredicate.polynomial := by
        simpa [sameScopePackageAsAlgebraicClosedRootPresentation] using
          Q.sourcePolynomial_maps_to_closedRoot
      have hcoeff :
          Q.sourcePolynomial.coeff Q.witnessDegree ≠ 0 := by
        intro hzero
        exact Q.mappedWitnessCoefficient_ne_zero (by simpa [hzero])
      simpa [hpoly] using hcoeff }

noncomputable def sourcePolynomialCauchyBoundAsPackageSourceArithmeticCauchyDomination
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {Q :
    ThreeFlavorSourceRationalPolynomialCandidate ℚ
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)}
  (B : ThreeFlavorSourcePolynomialCauchyRationalBound Q) :
  ThreeFlavorPackageSourceArithmeticCauchyDomination P :=
  { boundNumerator := B.boundNumerator
    boundNumerator_pos := B.boundNumerator_pos
    boundDenominator := B.boundDenominator
    boundDenominator_pos := B.boundDenominator_pos
    bound := B.bound
    bound_eq_numeral := B.bound_eq_numeral
    cauchyBound_le_bound := by
      have hpoly :
          Q.sourcePolynomial =
            (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P).explicitPolynomial := by
        simpa using Q.sourcePolynomial_maps_to_closedRoot
      simpa [hpoly] using B.sourceCauchyBound_le_bound }

noncomputable def sourceCandidateAndCauchyBoundAsPackagePolynomialArithmetic
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (Q :
    ThreeFlavorSourceRationalPolynomialCandidate ℚ
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B : ThreeFlavorSourcePolynomialCauchyRationalBound Q) :
  ThreeFlavorPackagePolynomialArithmeticCertificate P :=
  { packageHighCoefficient :=
      sourceRationalPolynomialCandidateAsPackageSourceHighCoefficient Q
    packageCauchyDomination :=
      sourcePolynomialCauchyBoundAsPackageSourceArithmeticCauchyDomination B }

noncomputable def sourceCandidateCauchyAndMinimalOrderingAsReadoutCoreCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (Q :
    ThreeFlavorSourceRationalPolynomialCandidate ℚ
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B : ThreeFlavorSourcePolynomialCauchyRationalBound Q)
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A)) :
  ThreeFlavorReadoutCoreCertificate P :=
  { polynomialArithmetic :=
      sourceCandidateAndCauchyBoundAsPackagePolynomialArithmetic Q B
    minimalStrictMassOrdering := O }

noncomputable def sourceCandidateCauchyAndMinimalOrderingAsDirectPositiveGapWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (Q :
    ThreeFlavorSourceRationalPolynomialCandidate ℚ
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B : ThreeFlavorSourcePolynomialCauchyRationalBound Q)
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : Q.witnessDegree = 2) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  readoutCoreCertificateAsDirectPositiveGapWindow
    (sourceCandidateCauchyAndMinimalOrderingAsReadoutCoreCertificate Q B O)
    witnessDegree_eq_two

theorem sourceCandidateCauchyAndMinimalOrdering_directPositiveGapContains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (Q :
    ThreeFlavorSourceRationalPolynomialCandidate ℚ
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B : ThreeFlavorSourcePolynomialCauchyRationalBound Q)
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : Q.witnessDegree = 2) :
  (sourceCandidateCauchyAndMinimalOrderingAsDirectPositiveGapWindow
      Q B O witnessDegree_eq_two).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (sourceCandidateCauchyAndMinimalOrderingAsDirectPositiveGapWindow
        Q B O witnessDegree_eq_two).interval.upper :=
  readoutCoreCertificate_directPositiveGapContains_gapRatio
    (sourceCandidateCauchyAndMinimalOrderingAsReadoutCoreCertificate Q B O)
    witnessDegree_eq_two

noncomputable def quotientNormalFormSourceCauchyAndMinimalOrderingAsDirectPositiveGapWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A)
  (L :
    ThreeFlavorQuotientNormalFormRationalPolynomialAlignment
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) Q)
  (B :
    ThreeFlavorSourcePolynomialCauchyRationalBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) Q L))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : L.witnessDegree = 2) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  sourceCandidateCauchyAndMinimalOrderingAsDirectPositiveGapWindow
    (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) Q L)
    B O
    (by
      simpa [quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate,
        internalAnchorAlignmentAsSourceRationalPolynomialCandidate,
        quotientNormalFormRationalAlignmentAsInternalAnchorAlignment] using
        witnessDegree_eq_two)

theorem quotientNormalFormSourceCauchyAndMinimalOrdering_directPositiveGapContains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A)
  (L :
    ThreeFlavorQuotientNormalFormRationalPolynomialAlignment
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) Q)
  (B :
    ThreeFlavorSourcePolynomialCauchyRationalBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) Q L))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : L.witnessDegree = 2) :
  (quotientNormalFormSourceCauchyAndMinimalOrderingAsDirectPositiveGapWindow
      Q L B O witnessDegree_eq_two).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (quotientNormalFormSourceCauchyAndMinimalOrderingAsDirectPositiveGapWindow
        Q L B O witnessDegree_eq_two).interval.upper :=
  sourceCandidateCauchyAndMinimalOrdering_directPositiveGapContains_gapRatio
    (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) Q L)
    B O
    (by
      simpa [quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate,
        internalAnchorAlignmentAsSourceRationalPolynomialCandidate,
        quotientNormalFormRationalAlignmentAsInternalAnchorAlignment] using
        witnessDegree_eq_two)

noncomputable def canonicalQNFSourceCauchyAndMinimalOrderingAsDirectPositiveGapWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B :
    ThreeFlavorSourcePolynomialCauchyRationalBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  quotientNormalFormSourceCauchyAndMinimalOrderingAsDirectPositiveGapWindow
    (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
    (canonicalSameScopeQNFPolynomialAuditAsAlignment
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)
    B O
    (by
      simpa [canonicalSameScopeQNFPolynomialAuditAsAlignment] using
        witnessDegree_eq_two)

theorem canonicalQNFSourceCauchyAndMinimalOrdering_directPositiveGapContains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B :
    ThreeFlavorSourcePolynomialCauchyRationalBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  (canonicalQNFSourceCauchyAndMinimalOrderingAsDirectPositiveGapWindow
      U B O witnessDegree_eq_two).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalQNFSourceCauchyAndMinimalOrderingAsDirectPositiveGapWindow
        U B O witnessDegree_eq_two).interval.upper :=
  quotientNormalFormSourceCauchyAndMinimalOrdering_directPositiveGapContains_gapRatio
    (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
    (canonicalSameScopeQNFPolynomialAuditAsAlignment
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)
    B O
    (by
      simpa [canonicalSameScopeQNFPolynomialAuditAsAlignment] using
        witnessDegree_eq_two)

noncomputable def canonicalQNFMillionBoundAsSourceCauchyBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (sourceCauchyBound_le_million :
    ((quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)
      ).sourcePolynomial.cauchyBound : Real) <=
      (((1000000 : Nat) : ℚ) : Real)) :
  ThreeFlavorSourcePolynomialCauchyRationalBound
    (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
      (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
      (canonicalSameScopeQNFPolynomialAuditAsAlignment
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)) :=
  { boundNumerator := 1000000
    boundNumerator_pos := by norm_num
    boundDenominator := 1
    boundDenominator_pos := by norm_num
    bound := (1000000 : ℚ)
    bound_eq_numeral := by norm_num
    sourceCauchyBound_le_bound := by
      simpa using sourceCauchyBound_le_million
    cauchyBoundComputedFromSourceCoefficients :=
      ((quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
          (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
          (canonicalSameScopeQNFPolynomialAuditAsAlignment
            (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)
        ).sourcePolynomial.cauchyBound : Real) <=
        (((1000000 : Nat) : ℚ) : Real)
    cauchyBoundComputedFromSourceCoefficients_proof :=
      sourceCauchyBound_le_million
    rationalDominationComputedFromSourceCoefficients :=
      ((quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
          (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
          (canonicalSameScopeQNFPolynomialAuditAsAlignment
            (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)
        ).sourcePolynomial.cauchyBound : Real) <=
        (((1000000 : Nat) : ℚ) : Real)
    rationalDominationComputedFromSourceCoefficients_proof :=
      sourceCauchyBound_le_million
    noEmpiricalBoundImport :=
      P.polynomialLaw.noEmpiricalFitImport
    noEmpiricalBoundImport_proof :=
      P.polynomialLaw.noEmpiricalFitImport_proof
    noBoundFitTuning :=
      P.polynomialLaw.noOneAnchorImport /\
        P.polynomialLaw.allUnresolvedFreedomsDischarged
    noBoundFitTuning_proof :=
      ⟨P.polynomialLaw.noOneAnchorImport_proof,
        P.polynomialLaw.allUnresolvedFreedomsDischarged_proof⟩
    noHiddenRootEncodingInBound := True
    noHiddenRootEncodingInBound_proof := True.intro }

noncomputable def canonicalQNFMillionBoundAsDirectPositiveGapWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (sourceCauchyBound_le_million :
    ((quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)
      ).sourcePolynomial.cauchyBound : Real) <=
      (((1000000 : Nat) : ℚ) : Real))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalQNFSourceCauchyAndMinimalOrderingAsDirectPositiveGapWindow
    U
    (canonicalQNFMillionBoundAsSourceCauchyBound
      U sourceCauchyBound_le_million)
    O
    witnessDegree_eq_two

theorem canonicalQNFMillionBound_directPositiveGapContains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (sourceCauchyBound_le_million :
    ((quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)
      ).sourcePolynomial.cauchyBound : Real) <=
      (((1000000 : Nat) : ℚ) : Real))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  (canonicalQNFMillionBoundAsDirectPositiveGapWindow
      U sourceCauchyBound_le_million O witnessDegree_eq_two).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalQNFMillionBoundAsDirectPositiveGapWindow
        U sourceCauchyBound_le_million O witnessDegree_eq_two).interval.upper :=
  canonicalQNFSourceCauchyAndMinimalOrdering_directPositiveGapContains_gapRatio
    U
    (canonicalQNFMillionBoundAsSourceCauchyBound
      U sourceCauchyBound_le_million)
    O
    witnessDegree_eq_two

noncomputable def sourcePolynomialCauchyCoefficientRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G) : NNReal :=
  Finset.sup (Finset.range Q.sourcePolynomial.natDegree)
      (fun i => ‖Q.sourcePolynomial.coeff i‖₊) /
    ‖Q.sourcePolynomial.leadingCoeff‖₊

/--
Coefficient-form Cauchy domination.

This is the constructive replacement for directly assuming
`sourcePolynomial.cauchyBound <= bound`.  Mathlib defines the Cauchy bound as
`sup coeff norm / leading coeff norm + 1`; this certificate asks for a bound on
that coefficient expression and derives the Cauchy domination from it.
-/
structure ThreeFlavorSourcePolynomialCoefficientCauchyDomination
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G) where
  boundNumerator : Nat
  boundNumerator_pos : 0 < boundNumerator
  boundDenominator : Nat
  boundDenominator_pos : 0 < boundDenominator
  bound : ℚ :=
    (boundNumerator : ℚ) / (boundDenominator : ℚ)
  bound_eq_numeral :
    bound = (boundNumerator : ℚ) / (boundDenominator : ℚ)
  coefficientSupRatio_le_boundMinusOne :
    (sourcePolynomialCauchyCoefficientRatio Q : Real) <=
      (bound : Real) - 1
  coefficientSupRatioComputedFromSourceCoefficients : Prop
  coefficientSupRatioComputedFromSourceCoefficients_proof :
    coefficientSupRatioComputedFromSourceCoefficients
  rationalDominationComputedFromSourceCoefficients : Prop
  rationalDominationComputedFromSourceCoefficients_proof :
    rationalDominationComputedFromSourceCoefficients
  noEmpiricalBoundImport : Prop
  noEmpiricalBoundImport_proof :
    noEmpiricalBoundImport
  noBoundFitTuning : Prop
  noBoundFitTuning_proof :
    noBoundFitTuning
  noHiddenRootEncodingInBound : Prop
  noHiddenRootEncodingInBound_proof :
    noHiddenRootEncodingInBound

noncomputable def sourcePolynomialCoefficientCauchyDominationAsCauchyBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G}
  (B : ThreeFlavorSourcePolynomialCoefficientCauchyDomination Q) :
  ThreeFlavorSourcePolynomialCauchyRationalBound Q :=
  { boundNumerator := B.boundNumerator
    boundNumerator_pos := B.boundNumerator_pos
    boundDenominator := B.boundDenominator
    boundDenominator_pos := B.boundDenominator_pos
    bound := B.bound
    bound_eq_numeral := B.bound_eq_numeral
    sourceCauchyBound_le_bound := by
      calc
        (Q.sourcePolynomial.cauchyBound : Real)
            =
              (sourcePolynomialCauchyCoefficientRatio Q : Real) + 1 := by
                change
                  ((sourcePolynomialCauchyCoefficientRatio Q + 1 : NNReal) : Real) =
                    (sourcePolynomialCauchyCoefficientRatio Q : Real) + 1
                norm_num
        _ <= ((B.bound : Real) - 1) + 1 := by
              have h := add_le_add_right
                B.coefficientSupRatio_le_boundMinusOne 1
              linarith
        _ = (B.bound : Real) := by ring
    cauchyBoundComputedFromSourceCoefficients :=
      B.coefficientSupRatioComputedFromSourceCoefficients
    cauchyBoundComputedFromSourceCoefficients_proof :=
      B.coefficientSupRatioComputedFromSourceCoefficients_proof
    rationalDominationComputedFromSourceCoefficients :=
      B.rationalDominationComputedFromSourceCoefficients
    rationalDominationComputedFromSourceCoefficients_proof :=
      B.rationalDominationComputedFromSourceCoefficients_proof
    noEmpiricalBoundImport := B.noEmpiricalBoundImport
    noEmpiricalBoundImport_proof := B.noEmpiricalBoundImport_proof
    noBoundFitTuning := B.noBoundFitTuning
    noBoundFitTuning_proof := B.noBoundFitTuning_proof
    noHiddenRootEncodingInBound := B.noHiddenRootEncodingInBound
    noHiddenRootEncodingInBound_proof :=
      B.noHiddenRootEncodingInBound_proof }

noncomputable def canonicalQNFMillionCoefficientDominationAsDirectPositiveGapWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B :
    ThreeFlavorSourcePolynomialCoefficientCauchyDomination
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)))
  (_hBnum : B.boundNumerator = 1000000)
  (_hBden : B.boundDenominator = 1)
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalQNFSourceCauchyAndMinimalOrderingAsDirectPositiveGapWindow
    U
    (sourcePolynomialCoefficientCauchyDominationAsCauchyBound B)
    O
    witnessDegree_eq_two

theorem canonicalQNFMillionCoefficientDomination_directPositiveGapContains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B :
    ThreeFlavorSourcePolynomialCoefficientCauchyDomination
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)))
  (_hBnum : B.boundNumerator = 1000000)
  (_hBden : B.boundDenominator = 1)
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  (canonicalQNFMillionCoefficientDominationAsDirectPositiveGapWindow
      U B _hBnum _hBden O witnessDegree_eq_two).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalQNFMillionCoefficientDominationAsDirectPositiveGapWindow
        U B _hBnum _hBden O witnessDegree_eq_two).interval.upper :=
  canonicalQNFSourceCauchyAndMinimalOrdering_directPositiveGapContains_gapRatio
    U
    (sourcePolynomialCoefficientCauchyDominationAsCauchyBound B)
    O
    witnessDegree_eq_two

/--
Concrete million-endpoint coefficient-ratio certificate.

For the endpoint `1000000 / 1`, the coefficient-form Cauchy task is precisely
to show the coefficient ratio is at most `999999`; adding the final `+ 1`
recovers the Cauchy endpoint.
-/
structure ThreeFlavorSourcePolynomialMillionCoefficientRatioBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G) where
  coefficientRatio_le_999999 :
    sourcePolynomialCauchyCoefficientRatio Q <= (999999 : NNReal)
  coefficientRatioComputedFromSourceCoefficients : Prop
  coefficientRatioComputedFromSourceCoefficients_proof :
    coefficientRatioComputedFromSourceCoefficients
  noEmpiricalBoundImport : Prop
  noEmpiricalBoundImport_proof :
    noEmpiricalBoundImport
  noBoundFitTuning : Prop
  noBoundFitTuning_proof :
    noBoundFitTuning
  noHiddenRootEncodingInBound : Prop
  noHiddenRootEncodingInBound_proof :
    noHiddenRootEncodingInBound

/--
Scaled coefficient-sup certificate for the million endpoint.

This is one layer closer to a finite arithmetic readout than a ratio bound:
instead of asking directly for
`sup(coeff norms) / leadingCoeffNorm <= 999999`, it asks for the
cross-multiplied coefficient-table inequality over `Real`, together with the
strict positivity of the leading coefficient norm.  The adapter below performs
the division step inside Lean.
-/
structure ThreeFlavorSourcePolynomialScaledCoefficientSupMillionBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G) where
  coefficientSup_le_scaledLeading_real :
    ((Finset.sup (Finset.range Q.sourcePolynomial.natDegree)
        (fun i => ‖Q.sourcePolynomial.coeff i‖₊) : NNReal) : Real) <=
      (999999 : Real) * ((‖Q.sourcePolynomial.leadingCoeff‖₊ : NNReal) : Real)
  leadingCoeff_nnnorm_pos :
    0 < ((‖Q.sourcePolynomial.leadingCoeff‖₊ : NNReal) : Real)
  coefficientSupComputedFromSourceCoefficientTable : Prop
  coefficientSupComputedFromSourceCoefficientTable_proof :
    coefficientSupComputedFromSourceCoefficientTable
  leadingCoefficientCertifiedFromSourcePolynomial : Prop
  leadingCoefficientCertifiedFromSourcePolynomial_proof :
    leadingCoefficientCertifiedFromSourcePolynomial
  noEmpiricalBoundImport : Prop
  noEmpiricalBoundImport_proof :
    noEmpiricalBoundImport
  noBoundFitTuning : Prop
  noBoundFitTuning_proof :
    noBoundFitTuning
  noHiddenRootEncodingInBound : Prop
  noHiddenRootEncodingInBound_proof :
    noHiddenRootEncodingInBound

noncomputable def scaledCoefficientSupMillionBoundAsMillionRatioBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G}
  (B : ThreeFlavorSourcePolynomialScaledCoefficientSupMillionBound Q) :
  ThreeFlavorSourcePolynomialMillionCoefficientRatioBound Q :=
  { coefficientRatio_le_999999 := by
      apply (NNReal.coe_le_coe).1
      rw [sourcePolynomialCauchyCoefficientRatio]
      rw [NNReal.coe_div]
      exact (div_le_iff₀ B.leadingCoeff_nnnorm_pos).mpr
        B.coefficientSup_le_scaledLeading_real
    coefficientRatioComputedFromSourceCoefficients :=
      B.coefficientSupComputedFromSourceCoefficientTable
    coefficientRatioComputedFromSourceCoefficients_proof :=
      B.coefficientSupComputedFromSourceCoefficientTable_proof
    noEmpiricalBoundImport := B.noEmpiricalBoundImport
    noEmpiricalBoundImport_proof := B.noEmpiricalBoundImport_proof
    noBoundFitTuning := B.noBoundFitTuning
    noBoundFitTuning_proof := B.noBoundFitTuning_proof
    noHiddenRootEncodingInBound := B.noHiddenRootEncodingInBound
    noHiddenRootEncodingInBound_proof :=
      B.noHiddenRootEncodingInBound_proof }

/--
Per-coefficient table certificate for the million endpoint.

This is the arithmetic form expected from an explicit source polynomial: every
coefficient below the leading degree is bounded by the displayed scaled leading
coefficient.  `Finset.sup_le` then constructs the scaled-sup certificate.
-/
structure ThreeFlavorSourcePolynomialPerCoefficientMillionBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G) where
  coefficient_le_scaledLeading :
    ∀ i ∈ Finset.range Q.sourcePolynomial.natDegree,
      ‖Q.sourcePolynomial.coeff i‖₊ <=
        (999999 : NNReal) * ‖Q.sourcePolynomial.leadingCoeff‖₊
  leadingCoeff_nnnorm_pos :
    0 < ((‖Q.sourcePolynomial.leadingCoeff‖₊ : NNReal) : Real)
  coefficientBoundsComputedFromSourceCoefficientTable : Prop
  coefficientBoundsComputedFromSourceCoefficientTable_proof :
    coefficientBoundsComputedFromSourceCoefficientTable
  leadingCoefficientCertifiedFromSourcePolynomial : Prop
  leadingCoefficientCertifiedFromSourcePolynomial_proof :
    leadingCoefficientCertifiedFromSourcePolynomial
  noEmpiricalBoundImport : Prop
  noEmpiricalBoundImport_proof :
    noEmpiricalBoundImport
  noBoundFitTuning : Prop
  noBoundFitTuning_proof :
    noBoundFitTuning
  noHiddenRootEncodingInBound : Prop
  noHiddenRootEncodingInBound_proof :
    noHiddenRootEncodingInBound

theorem sourceRationalPolynomialCandidate_leadingCoeff_nnnorm_pos
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G) :
  0 < ((‖Q.sourcePolynomial.leadingCoeff‖₊ : NNReal) : Real) := by
  have hcoeff :
      Q.sourcePolynomial.coeff Q.witnessDegree ≠ 0 := by
    simpa using Q.mappedWitnessCoefficient_ne_zero
  have hpoly_ne : Q.sourcePolynomial ≠ 0 := by
    intro hzero
    exact hcoeff (by simp [hzero])
  have hlead :
      Q.sourcePolynomial.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hpoly_ne
  exact_mod_cast ((nnnorm_pos).2 hlead)

/--
Per-coefficient certificate with leading positivity derived from the candidate
itself.  This is the cleaner finite table target: the source polynomial's
nonzero witness coefficient supplies the leading-coefficient positivity.
-/
structure ThreeFlavorSourcePolynomialWitnessedPerCoefficientMillionBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G) where
  coefficient_le_scaledLeading :
    ∀ i ∈ Finset.range Q.sourcePolynomial.natDegree,
      ‖Q.sourcePolynomial.coeff i‖₊ <=
        (999999 : NNReal) * ‖Q.sourcePolynomial.leadingCoeff‖₊
  coefficientBoundsComputedFromSourceCoefficientTable : Prop
  coefficientBoundsComputedFromSourceCoefficientTable_proof :
    coefficientBoundsComputedFromSourceCoefficientTable
  noEmpiricalBoundImport : Prop
  noEmpiricalBoundImport_proof :
    noEmpiricalBoundImport
  noBoundFitTuning : Prop
  noBoundFitTuning_proof :
    noBoundFitTuning
  noHiddenRootEncodingInBound : Prop
  noHiddenRootEncodingInBound_proof :
    noHiddenRootEncodingInBound

/--
Monic finite coefficient-table certificate.

For a monic source polynomial, `||leadingCoeff|| = 1`, so the remaining
million-endpoint proof is just the finite list of lower-coefficient norm
bounds `||coeff_i|| <= 999999`.
-/
structure ThreeFlavorSourcePolynomialMonicCoefficientMillionBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G) where
  sourcePolynomial_monic :
    Q.sourcePolynomial.Monic
  coefficient_le_999999 :
    ∀ i ∈ Finset.range Q.sourcePolynomial.natDegree,
      ‖Q.sourcePolynomial.coeff i‖₊ <= (999999 : NNReal)
  coefficientBoundsComputedFromSourceCoefficientTable : Prop
  coefficientBoundsComputedFromSourceCoefficientTable_proof :
    coefficientBoundsComputedFromSourceCoefficientTable
  monicNormalizationDerivedInternally : Prop
  monicNormalizationDerivedInternally_proof :
    monicNormalizationDerivedInternally
  noEmpiricalBoundImport : Prop
  noEmpiricalBoundImport_proof :
    noEmpiricalBoundImport
  noBoundFitTuning : Prop
  noBoundFitTuning_proof :
    noBoundFitTuning
  noHiddenRootEncodingInBound : Prop
  noHiddenRootEncodingInBound_proof :
    noHiddenRootEncodingInBound

noncomputable def sourcePolynomialLowerCoefficientHeight
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G) : NNReal :=
  Finset.sup (Finset.range Q.sourcePolynomial.natDegree)
    (fun i => ‖Q.sourcePolynomial.coeff i‖₊)

/--
Monic coefficient-height certificate.

This replaces the finite family of coefficient inequalities with one computed
height bound over the lower coefficient range.
-/
structure ThreeFlavorSourcePolynomialMonicCoefficientHeightMillionBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G) where
  sourcePolynomial_monic :
    Q.sourcePolynomial.Monic
  coefficientHeight_le_999999 :
    sourcePolynomialLowerCoefficientHeight Q <= (999999 : NNReal)
  coefficientHeightComputedFromSourceCoefficientTable : Prop
  coefficientHeightComputedFromSourceCoefficientTable_proof :
    coefficientHeightComputedFromSourceCoefficientTable
  monicNormalizationDerivedInternally : Prop
  monicNormalizationDerivedInternally_proof :
    monicNormalizationDerivedInternally
  noEmpiricalBoundImport : Prop
  noEmpiricalBoundImport_proof :
    noEmpiricalBoundImport
  noBoundFitTuning : Prop
  noBoundFitTuning_proof :
    noBoundFitTuning
  noHiddenRootEncodingInBound : Prop
  noHiddenRootEncodingInBound_proof :
    noHiddenRootEncodingInBound

/--
Numeral evaluation of the monic lower-coefficient height.

This is the computational readout shape: evaluate the finite coefficient
height to a displayed natural numeral `heightNumeral`, then check that numeral
is at most `999999`.
-/
structure ThreeFlavorSourcePolynomialMonicCoefficientHeightNumeralBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G) where
  sourcePolynomial_monic :
    Q.sourcePolynomial.Monic
  heightNumeral : Nat
  heightNumeral_le_999999 :
    heightNumeral <= 999999
  coefficientHeight_eq_numeral :
    sourcePolynomialLowerCoefficientHeight Q = (heightNumeral : NNReal)
  coefficientHeightComputedFromSourceCoefficientTable : Prop
  coefficientHeightComputedFromSourceCoefficientTable_proof :
    coefficientHeightComputedFromSourceCoefficientTable
  monicNormalizationDerivedInternally : Prop
  monicNormalizationDerivedInternally_proof :
    monicNormalizationDerivedInternally
  noEmpiricalBoundImport : Prop
  noEmpiricalBoundImport_proof :
    noEmpiricalBoundImport
  noBoundFitTuning : Prop
  noBoundFitTuning_proof :
    noBoundFitTuning
  noHiddenRootEncodingInBound : Prop
  noHiddenRootEncodingInBound_proof :
    noHiddenRootEncodingInBound

/--
Finite maximum evaluation of the monic lower-coefficient height.

To prove the height is a displayed numeral, it is enough to certify that every
lower coefficient norm is at most that numeral and that the numeral is attained
by one lower coefficient.
-/
structure ThreeFlavorSourcePolynomialMonicCoefficientHeightEvaluation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G) where
  sourcePolynomial_monic :
    Q.sourcePolynomial.Monic
  heightNumeral : Nat
  heightNumeral_le_999999 :
    heightNumeral <= 999999
  coefficient_le_heightNumeral :
    ∀ i ∈ Finset.range Q.sourcePolynomial.natDegree,
      ‖Q.sourcePolynomial.coeff i‖₊ <= (heightNumeral : NNReal)
  heightNumeral_attained :
    ∃ i ∈ Finset.range Q.sourcePolynomial.natDegree,
      (heightNumeral : NNReal) <= ‖Q.sourcePolynomial.coeff i‖₊
  coefficientHeightComputedFromSourceCoefficientTable : Prop
  coefficientHeightComputedFromSourceCoefficientTable_proof :
    coefficientHeightComputedFromSourceCoefficientTable
  monicNormalizationDerivedInternally : Prop
  monicNormalizationDerivedInternally_proof :
    monicNormalizationDerivedInternally
  noEmpiricalBoundImport : Prop
  noEmpiricalBoundImport_proof :
    noEmpiricalBoundImport
  noBoundFitTuning : Prop
  noBoundFitTuning_proof :
    noBoundFitTuning
  noHiddenRootEncodingInBound : Prop
  noHiddenRootEncodingInBound_proof :
    noHiddenRootEncodingInBound

noncomputable def monicCoefficientHeightEvaluationAsNumeralBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G}
  (B : ThreeFlavorSourcePolynomialMonicCoefficientHeightEvaluation Q) :
  ThreeFlavorSourcePolynomialMonicCoefficientHeightNumeralBound Q :=
  { sourcePolynomial_monic := B.sourcePolynomial_monic
    heightNumeral := B.heightNumeral
    heightNumeral_le_999999 := B.heightNumeral_le_999999
    coefficientHeight_eq_numeral := by
      apply le_antisymm
      · exact Finset.sup_le B.coefficient_le_heightNumeral
      · rcases B.heightNumeral_attained with ⟨i, hi, hle⟩
        change
          (B.heightNumeral : NNReal) <=
            Finset.sup (Finset.range Q.sourcePolynomial.natDegree)
              (fun i => ‖Q.sourcePolynomial.coeff i‖₊)
        exact hle.trans
          (Finset.le_sup
            (f := fun i => ‖Q.sourcePolynomial.coeff i‖₊) hi)
    coefficientHeightComputedFromSourceCoefficientTable :=
      B.coefficientHeightComputedFromSourceCoefficientTable
    coefficientHeightComputedFromSourceCoefficientTable_proof :=
      B.coefficientHeightComputedFromSourceCoefficientTable_proof
    monicNormalizationDerivedInternally :=
      B.monicNormalizationDerivedInternally
    monicNormalizationDerivedInternally_proof :=
      B.monicNormalizationDerivedInternally_proof
    noEmpiricalBoundImport := B.noEmpiricalBoundImport
    noEmpiricalBoundImport_proof := B.noEmpiricalBoundImport_proof
    noBoundFitTuning := B.noBoundFitTuning
    noBoundFitTuning_proof := B.noBoundFitTuning_proof
    noHiddenRootEncodingInBound := B.noHiddenRootEncodingInBound
    noHiddenRootEncodingInBound_proof :=
      B.noHiddenRootEncodingInBound_proof }

noncomputable def monicCoefficientHeightNumeralBoundAsHeightMillionBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G}
  (B : ThreeFlavorSourcePolynomialMonicCoefficientHeightNumeralBound Q) :
  ThreeFlavorSourcePolynomialMonicCoefficientHeightMillionBound Q :=
  { sourcePolynomial_monic := B.sourcePolynomial_monic
    coefficientHeight_le_999999 := by
      rw [B.coefficientHeight_eq_numeral]
      exact_mod_cast B.heightNumeral_le_999999
    coefficientHeightComputedFromSourceCoefficientTable :=
      B.coefficientHeightComputedFromSourceCoefficientTable
    coefficientHeightComputedFromSourceCoefficientTable_proof :=
      B.coefficientHeightComputedFromSourceCoefficientTable_proof
    monicNormalizationDerivedInternally :=
      B.monicNormalizationDerivedInternally
    monicNormalizationDerivedInternally_proof :=
      B.monicNormalizationDerivedInternally_proof
    noEmpiricalBoundImport := B.noEmpiricalBoundImport
    noEmpiricalBoundImport_proof := B.noEmpiricalBoundImport_proof
    noBoundFitTuning := B.noBoundFitTuning
    noBoundFitTuning_proof := B.noBoundFitTuning_proof
    noHiddenRootEncodingInBound := B.noHiddenRootEncodingInBound
    noHiddenRootEncodingInBound_proof :=
      B.noHiddenRootEncodingInBound_proof }

noncomputable def monicCoefficientHeightMillionBoundAsMonicCoefficientMillionBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G}
  (B : ThreeFlavorSourcePolynomialMonicCoefficientHeightMillionBound Q) :
  ThreeFlavorSourcePolynomialMonicCoefficientMillionBound Q :=
  { sourcePolynomial_monic := B.sourcePolynomial_monic
    coefficient_le_999999 := by
      intro i hi
      exact (Finset.le_sup hi).trans B.coefficientHeight_le_999999
    coefficientBoundsComputedFromSourceCoefficientTable :=
      B.coefficientHeightComputedFromSourceCoefficientTable
    coefficientBoundsComputedFromSourceCoefficientTable_proof :=
      B.coefficientHeightComputedFromSourceCoefficientTable_proof
    monicNormalizationDerivedInternally :=
      B.monicNormalizationDerivedInternally
    monicNormalizationDerivedInternally_proof :=
      B.monicNormalizationDerivedInternally_proof
    noEmpiricalBoundImport := B.noEmpiricalBoundImport
    noEmpiricalBoundImport_proof := B.noEmpiricalBoundImport_proof
    noBoundFitTuning := B.noBoundFitTuning
    noBoundFitTuning_proof := B.noBoundFitTuning_proof
    noHiddenRootEncodingInBound := B.noHiddenRootEncodingInBound
    noHiddenRootEncodingInBound_proof :=
      B.noHiddenRootEncodingInBound_proof }

noncomputable def monicCoefficientMillionBoundAsWitnessedPerCoefficientMillionBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G}
  (B : ThreeFlavorSourcePolynomialMonicCoefficientMillionBound Q) :
  ThreeFlavorSourcePolynomialWitnessedPerCoefficientMillionBound Q :=
  { coefficient_le_scaledLeading := by
      intro i hi
      have hlead : Q.sourcePolynomial.leadingCoeff = (1 : ℚ) :=
        B.sourcePolynomial_monic.leadingCoeff
      have hcoeff := B.coefficient_le_999999 i hi
      simpa [hlead] using hcoeff
    coefficientBoundsComputedFromSourceCoefficientTable :=
      B.coefficientBoundsComputedFromSourceCoefficientTable
    coefficientBoundsComputedFromSourceCoefficientTable_proof :=
      B.coefficientBoundsComputedFromSourceCoefficientTable_proof
    noEmpiricalBoundImport :=
      B.noEmpiricalBoundImport
    noEmpiricalBoundImport_proof :=
      B.noEmpiricalBoundImport_proof
    noBoundFitTuning :=
      B.noBoundFitTuning /\ B.monicNormalizationDerivedInternally
    noBoundFitTuning_proof :=
      ⟨B.noBoundFitTuning_proof, B.monicNormalizationDerivedInternally_proof⟩
    noHiddenRootEncodingInBound := B.noHiddenRootEncodingInBound
    noHiddenRootEncodingInBound_proof :=
      B.noHiddenRootEncodingInBound_proof }

noncomputable def witnessedPerCoefficientMillionBoundAsPerCoefficientMillionBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G}
  (B : ThreeFlavorSourcePolynomialWitnessedPerCoefficientMillionBound Q) :
  ThreeFlavorSourcePolynomialPerCoefficientMillionBound Q :=
  { coefficient_le_scaledLeading := B.coefficient_le_scaledLeading
    leadingCoeff_nnnorm_pos :=
      sourceRationalPolynomialCandidate_leadingCoeff_nnnorm_pos Q
    coefficientBoundsComputedFromSourceCoefficientTable :=
      B.coefficientBoundsComputedFromSourceCoefficientTable
    coefficientBoundsComputedFromSourceCoefficientTable_proof :=
      B.coefficientBoundsComputedFromSourceCoefficientTable_proof
    leadingCoefficientCertifiedFromSourcePolynomial :=
      Q.sourcePolynomialSourceDerived
    leadingCoefficientCertifiedFromSourcePolynomial_proof :=
      Q.sourcePolynomialSourceDerived_proof
    noEmpiricalBoundImport := B.noEmpiricalBoundImport
    noEmpiricalBoundImport_proof := B.noEmpiricalBoundImport_proof
    noBoundFitTuning := B.noBoundFitTuning
    noBoundFitTuning_proof := B.noBoundFitTuning_proof
    noHiddenRootEncodingInBound := B.noHiddenRootEncodingInBound
    noHiddenRootEncodingInBound_proof :=
      B.noHiddenRootEncodingInBound_proof }

noncomputable def perCoefficientMillionBoundAsScaledCoefficientSupMillionBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G}
  (B : ThreeFlavorSourcePolynomialPerCoefficientMillionBound Q) :
  ThreeFlavorSourcePolynomialScaledCoefficientSupMillionBound Q :=
  { coefficientSup_le_scaledLeading_real := by
      have hsup :
          Finset.sup (Finset.range Q.sourcePolynomial.natDegree)
              (fun i => ‖Q.sourcePolynomial.coeff i‖₊) <=
            (999999 : NNReal) * ‖Q.sourcePolynomial.leadingCoeff‖₊ :=
        Finset.sup_le B.coefficient_le_scaledLeading
      have hreal :
          ((Finset.sup (Finset.range Q.sourcePolynomial.natDegree)
              (fun i => ‖Q.sourcePolynomial.coeff i‖₊) : NNReal) : Real) <=
            (((999999 : NNReal) *
              ‖Q.sourcePolynomial.leadingCoeff‖₊ : NNReal) : Real) :=
        (NNReal.coe_le_coe).2 hsup
      simpa [NNReal.coe_mul] using hreal
    leadingCoeff_nnnorm_pos := B.leadingCoeff_nnnorm_pos
    coefficientSupComputedFromSourceCoefficientTable :=
      B.coefficientBoundsComputedFromSourceCoefficientTable
    coefficientSupComputedFromSourceCoefficientTable_proof :=
      B.coefficientBoundsComputedFromSourceCoefficientTable_proof
    leadingCoefficientCertifiedFromSourcePolynomial :=
      B.leadingCoefficientCertifiedFromSourcePolynomial
    leadingCoefficientCertifiedFromSourcePolynomial_proof :=
      B.leadingCoefficientCertifiedFromSourcePolynomial_proof
    noEmpiricalBoundImport := B.noEmpiricalBoundImport
    noEmpiricalBoundImport_proof := B.noEmpiricalBoundImport_proof
    noBoundFitTuning := B.noBoundFitTuning
    noBoundFitTuning_proof := B.noBoundFitTuning_proof
    noHiddenRootEncodingInBound := B.noHiddenRootEncodingInBound
    noHiddenRootEncodingInBound_proof :=
      B.noHiddenRootEncodingInBound_proof }

noncomputable def millionCoefficientRatioBoundAsCoefficientCauchyDomination
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {Q : ThreeFlavorSourceRationalPolynomialCandidate ℚ G}
  (B : ThreeFlavorSourcePolynomialMillionCoefficientRatioBound Q) :
  ThreeFlavorSourcePolynomialCoefficientCauchyDomination Q :=
  { boundNumerator := 1000000
    boundNumerator_pos := by norm_num
    boundDenominator := 1
    boundDenominator_pos := by norm_num
    bound := 1000000
    bound_eq_numeral := by norm_num
    coefficientSupRatio_le_boundMinusOne := by
      have hreal :
          (sourcePolynomialCauchyCoefficientRatio Q : Real) <=
            ((999999 : NNReal) : Real) :=
        (NNReal.coe_le_coe).2 B.coefficientRatio_le_999999
      norm_num at hreal ⊢
      exact hreal
    coefficientSupRatioComputedFromSourceCoefficients :=
      B.coefficientRatioComputedFromSourceCoefficients
    coefficientSupRatioComputedFromSourceCoefficients_proof :=
      B.coefficientRatioComputedFromSourceCoefficients_proof
    rationalDominationComputedFromSourceCoefficients :=
      B.coefficientRatioComputedFromSourceCoefficients
    rationalDominationComputedFromSourceCoefficients_proof :=
      B.coefficientRatioComputedFromSourceCoefficients_proof
    noEmpiricalBoundImport := B.noEmpiricalBoundImport
    noEmpiricalBoundImport_proof := B.noEmpiricalBoundImport_proof
    noBoundFitTuning := B.noBoundFitTuning
    noBoundFitTuning_proof := B.noBoundFitTuning_proof
    noHiddenRootEncodingInBound := B.noHiddenRootEncodingInBound
    noHiddenRootEncodingInBound_proof :=
      B.noHiddenRootEncodingInBound_proof }

noncomputable def canonicalQNFMillionRatioBoundAsDirectPositiveGapWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B :
    ThreeFlavorSourcePolynomialMillionCoefficientRatioBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalQNFMillionCoefficientDominationAsDirectPositiveGapWindow
    U
    (millionCoefficientRatioBoundAsCoefficientCauchyDomination B)
    rfl
    rfl
    O
    witnessDegree_eq_two

theorem canonicalQNFMillionRatioBound_directPositiveGapContains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B :
    ThreeFlavorSourcePolynomialMillionCoefficientRatioBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  (canonicalQNFMillionRatioBoundAsDirectPositiveGapWindow
      U B O witnessDegree_eq_two).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalQNFMillionRatioBoundAsDirectPositiveGapWindow
        U B O witnessDegree_eq_two).interval.upper :=
  canonicalQNFMillionCoefficientDomination_directPositiveGapContains_gapRatio
    U
    (millionCoefficientRatioBoundAsCoefficientCauchyDomination B)
    rfl
    rfl
    O
    witnessDegree_eq_two

noncomputable def canonicalQNFScaledCoefficientSupMillionAsDirectPositiveGapWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B :
    ThreeFlavorSourcePolynomialScaledCoefficientSupMillionBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalQNFMillionRatioBoundAsDirectPositiveGapWindow
    U
    (scaledCoefficientSupMillionBoundAsMillionRatioBound B)
    O
    witnessDegree_eq_two

theorem canonicalQNFScaledCoefficientSupMillion_directPositiveGapContains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B :
    ThreeFlavorSourcePolynomialScaledCoefficientSupMillionBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  (canonicalQNFScaledCoefficientSupMillionAsDirectPositiveGapWindow
      U B O witnessDegree_eq_two).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalQNFScaledCoefficientSupMillionAsDirectPositiveGapWindow
        U B O witnessDegree_eq_two).interval.upper :=
  canonicalQNFMillionRatioBound_directPositiveGapContains_gapRatio
    U
    (scaledCoefficientSupMillionBoundAsMillionRatioBound B)
    O
    witnessDegree_eq_two

noncomputable def canonicalQNFPerCoefficientMillionAsDirectPositiveGapWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B :
    ThreeFlavorSourcePolynomialPerCoefficientMillionBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalQNFScaledCoefficientSupMillionAsDirectPositiveGapWindow
    U
    (perCoefficientMillionBoundAsScaledCoefficientSupMillionBound B)
    O
    witnessDegree_eq_two

theorem canonicalQNFPerCoefficientMillion_directPositiveGapContains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B :
    ThreeFlavorSourcePolynomialPerCoefficientMillionBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  (canonicalQNFPerCoefficientMillionAsDirectPositiveGapWindow
      U B O witnessDegree_eq_two).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalQNFPerCoefficientMillionAsDirectPositiveGapWindow
        U B O witnessDegree_eq_two).interval.upper :=
  canonicalQNFScaledCoefficientSupMillion_directPositiveGapContains_gapRatio
    U
    (perCoefficientMillionBoundAsScaledCoefficientSupMillionBound B)
    O
    witnessDegree_eq_two

noncomputable def canonicalQNFWitnessedPerCoefficientMillionAsDirectPositiveGapWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B :
    ThreeFlavorSourcePolynomialWitnessedPerCoefficientMillionBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalQNFPerCoefficientMillionAsDirectPositiveGapWindow
    U
    (witnessedPerCoefficientMillionBoundAsPerCoefficientMillionBound B)
    O
    witnessDegree_eq_two

theorem canonicalQNFWitnessedPerCoefficientMillion_directPositiveGapContains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B :
    ThreeFlavorSourcePolynomialWitnessedPerCoefficientMillionBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  (canonicalQNFWitnessedPerCoefficientMillionAsDirectPositiveGapWindow
      U B O witnessDegree_eq_two).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalQNFWitnessedPerCoefficientMillionAsDirectPositiveGapWindow
        U B O witnessDegree_eq_two).interval.upper :=
  canonicalQNFPerCoefficientMillion_directPositiveGapContains_gapRatio
    U
    (witnessedPerCoefficientMillionBoundAsPerCoefficientMillionBound B)
    O
    witnessDegree_eq_two

noncomputable def canonicalQNFMonicCoefficientMillionAsDirectPositiveGapWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B :
    ThreeFlavorSourcePolynomialMonicCoefficientMillionBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalQNFWitnessedPerCoefficientMillionAsDirectPositiveGapWindow
    U
    (monicCoefficientMillionBoundAsWitnessedPerCoefficientMillionBound B)
    O
    witnessDegree_eq_two

theorem canonicalQNFMonicCoefficientMillion_directPositiveGapContains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B :
    ThreeFlavorSourcePolynomialMonicCoefficientMillionBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  (canonicalQNFMonicCoefficientMillionAsDirectPositiveGapWindow
      U B O witnessDegree_eq_two).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalQNFMonicCoefficientMillionAsDirectPositiveGapWindow
        U B O witnessDegree_eq_two).interval.upper :=
  canonicalQNFWitnessedPerCoefficientMillion_directPositiveGapContains_gapRatio
    U
    (monicCoefficientMillionBoundAsWitnessedPerCoefficientMillionBound B)
    O
    witnessDegree_eq_two

noncomputable def canonicalQNFMonicCoefficientHeightMillionAsDirectPositiveGapWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B :
    ThreeFlavorSourcePolynomialMonicCoefficientHeightMillionBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalQNFMonicCoefficientMillionAsDirectPositiveGapWindow
    U
    (monicCoefficientHeightMillionBoundAsMonicCoefficientMillionBound B)
    O
    witnessDegree_eq_two

theorem canonicalQNFMonicCoefficientHeightMillion_directPositiveGapContains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B :
    ThreeFlavorSourcePolynomialMonicCoefficientHeightMillionBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  (canonicalQNFMonicCoefficientHeightMillionAsDirectPositiveGapWindow
      U B O witnessDegree_eq_two).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalQNFMonicCoefficientHeightMillionAsDirectPositiveGapWindow
        U B O witnessDegree_eq_two).interval.upper :=
  canonicalQNFMonicCoefficientMillion_directPositiveGapContains_gapRatio
    U
    (monicCoefficientHeightMillionBoundAsMonicCoefficientMillionBound B)
    O
    witnessDegree_eq_two

noncomputable def canonicalQNFMonicCoefficientHeightNumeralAsDirectPositiveGapWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B :
    ThreeFlavorSourcePolynomialMonicCoefficientHeightNumeralBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalQNFMonicCoefficientHeightMillionAsDirectPositiveGapWindow
    U
    (monicCoefficientHeightNumeralBoundAsHeightMillionBound B)
    O
    witnessDegree_eq_two

theorem canonicalQNFMonicCoefficientHeightNumeral_directPositiveGapContains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B :
    ThreeFlavorSourcePolynomialMonicCoefficientHeightNumeralBound
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  (canonicalQNFMonicCoefficientHeightNumeralAsDirectPositiveGapWindow
      U B O witnessDegree_eq_two).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalQNFMonicCoefficientHeightNumeralAsDirectPositiveGapWindow
        U B O witnessDegree_eq_two).interval.upper :=
  canonicalQNFMonicCoefficientHeightMillion_directPositiveGapContains_gapRatio
    U
    (monicCoefficientHeightNumeralBoundAsHeightMillionBound B)
    O
    witnessDegree_eq_two

noncomputable def canonicalQNFMonicCoefficientHeightEvaluationAsDirectPositiveGapWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B :
    ThreeFlavorSourcePolynomialMonicCoefficientHeightEvaluation
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  ThreeFlavorClosedRootDecimalWindow ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) :=
  canonicalQNFMonicCoefficientHeightNumeralAsDirectPositiveGapWindow
    U
    (monicCoefficientHeightEvaluationAsNumeralBound B)
    O
    witnessDegree_eq_two

theorem canonicalQNFMonicCoefficientHeightEvaluation_directPositiveGapContains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (U :
    ThreeFlavorCanonicalSameScopeQNFPolynomialAudit
      (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P))
  (B :
    ThreeFlavorSourcePolynomialMonicCoefficientHeightEvaluation
      (quotientNormalFormInteriorLawAsSourceRationalPolynomialCandidate
        (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P)
        (sameScopeClosedRootNormalFormAsInteriorLaw ℚ A P)
        (canonicalSameScopeQNFPolynomialAuditAsAlignment
          (sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P) U)))
  (O : ThreeFlavorMinimalPackageStrictMassSquaredOrdering (A := A))
  (witnessDegree_eq_two : U.witnessDegree = 2) :
  (canonicalQNFMonicCoefficientHeightEvaluationAsDirectPositiveGapWindow
      U B O witnessDegree_eq_two).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (canonicalQNFMonicCoefficientHeightEvaluationAsDirectPositiveGapWindow
        U B O witnessDegree_eq_two).interval.upper :=
  canonicalQNFMonicCoefficientHeightNumeral_directPositiveGapContains_gapRatio
    U
    (monicCoefficientHeightEvaluationAsNumeralBound B)
    O
    witnessDegree_eq_two

noncomputable def cauchyRationalRootBoundAsCoefficientDerivedAbsoluteRootBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (B : ThreeFlavorCauchyRationalRootBound G) :
  ThreeFlavorCoefficientDerivedAbsoluteRootBound G :=
  { boundNumerator := B.boundNumerator
    boundNumerator_pos := B.boundNumerator_pos
    boundDenominator := B.boundDenominator
    boundDenominator_pos := B.boundDenominator_pos
    bound := B.bound
    bound_eq_numeral := B.bound_eq_numeral
    boundTargetsExplicitPolynomial := B.boundTargetsExplicitPolynomial
    boundTargetsExplicitPolynomial_proof :=
      B.boundTargetsExplicitPolynomial_proof
    selectedRootRootOfExplicitPolynomial := G.selectedRoot_is_root
    abs_selectedRoot_le_bound :=
      rational_abs_le_of_isRoot_cauchyBound_le
        G.explicitPolynomial
        B.explicitPolynomial_ne_zero
        G.selectedRoot
        B.bound
        G.selectedRoot_is_root
        B.cauchyBound_le_bound
    boundComputedFromCoefficientTable :=
      B.cauchyBoundComputedFromCoefficientTable /\
        B.rationalDominationComputedFromCoefficientTable
    boundComputedFromCoefficientTable_proof :=
      ⟨B.cauchyBoundComputedFromCoefficientTable_proof,
        B.rationalDominationComputedFromCoefficientTable_proof⟩
    noEmpiricalBoundImport := B.noEmpiricalBoundImport
    noEmpiricalBoundImport_proof := B.noEmpiricalBoundImport_proof
    noBoundFitTuning := B.noBoundFitTuning
    noBoundFitTuning_proof := B.noBoundFitTuning_proof
    noHiddenRootEncodingInBound := B.noHiddenRootEncodingInBound
    noHiddenRootEncodingInBound_proof :=
      B.noHiddenRootEncodingInBound_proof }

noncomputable def coefficientDerivedAbsoluteRootBoundAsAbsoluteBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (B : ThreeFlavorCoefficientDerivedAbsoluteRootBound G) :
  ThreeFlavorAbsoluteRationalRootBound G :=
  { boundNumerator := B.boundNumerator
    boundNumerator_pos := B.boundNumerator_pos
    boundDenominator := B.boundDenominator
    boundDenominator_pos := B.boundDenominator_pos
    bound := B.bound
    bound_eq_numeral := B.bound_eq_numeral
    abs_selectedRoot_le_bound := B.abs_selectedRoot_le_bound
    rootBoundComputedFromCoefficientLaw :=
      B.boundTargetsExplicitPolynomial /\ B.boundComputedFromCoefficientTable
    rootBoundComputedFromCoefficientLaw_proof :=
      ⟨B.boundTargetsExplicitPolynomial_proof,
        B.boundComputedFromCoefficientTable_proof⟩
    noEmpiricalBoundImport := B.noEmpiricalBoundImport
    noEmpiricalBoundImport_proof := B.noEmpiricalBoundImport_proof
    noBoundFitTuning := B.noBoundFitTuning
    noBoundFitTuning_proof := B.noBoundFitTuning_proof
    noHiddenRootEncodingInBound := B.noHiddenRootEncodingInBound
    noHiddenRootEncodingInBound_proof :=
      B.noHiddenRootEncodingInBound_proof }

noncomputable def absoluteRationalRootBoundAsSymmetricBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (B : ThreeFlavorAbsoluteRationalRootBound G) :
  ThreeFlavorSymmetricRationalRootBound G :=
  { boundNumerator := B.boundNumerator
    boundNumerator_pos := B.boundNumerator_pos
    boundDenominator := B.boundDenominator
    boundDenominator_pos := B.boundDenominator_pos
    bound := B.bound
    bound_eq_numeral := B.bound_eq_numeral
    selectedRoot_mem_symmetric := by
      exact abs_le.mp B.abs_selectedRoot_le_bound
    rootBoundComputedFromCoefficientLaw :=
      B.rootBoundComputedFromCoefficientLaw
    rootBoundComputedFromCoefficientLaw_proof :=
      B.rootBoundComputedFromCoefficientLaw_proof
    noEmpiricalBoundImport := B.noEmpiricalBoundImport
    noEmpiricalBoundImport_proof := B.noEmpiricalBoundImport_proof
    noBoundFitTuning := B.noBoundFitTuning
    noBoundFitTuning_proof := B.noBoundFitTuning_proof
    noHiddenRootEncodingInBound := B.noHiddenRootEncodingInBound
    noHiddenRootEncodingInBound_proof :=
      B.noHiddenRootEncodingInBound_proof }

noncomputable def symmetricRationalRootBoundAsNumeralEndpointBounds
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  (B : ThreeFlavorSymmetricRationalRootBound G) :
  ThreeFlavorRationalClosedRootCandidateNumeralEndpointBounds G :=
  { numeralInterval :=
      { lower := -B.bound
        upper := B.bound
        tolerance := 2 * B.bound
        lowerNumerator := -(B.boundNumerator : Int)
        lowerDenominator := B.boundDenominator
        lowerDenominator_pos := B.boundDenominator_pos
        upperNumerator := B.boundNumerator
        upperDenominator := B.boundDenominator
        upperDenominator_pos := B.boundDenominator_pos
        lower_eq_numeral := by
          rw [B.bound_eq_numeral]
          have hneg :
              ((-(B.boundNumerator : Int) : Int) : ℚ) =
                -(B.boundNumerator : ℚ) := by
            norm_num
          rw [hneg]
          ring
        upper_eq_numeral := by
          exact B.bound_eq_numeral
        lower_lt_upper := by
          have hbound_pos : 0 < B.bound := by
            rw [B.bound_eq_numeral]
            exact div_pos
              (Nat.cast_pos.mpr B.boundNumerator_pos)
              (Nat.cast_pos.mpr B.boundDenominator_pos)
          linarith
        tolerance_pos := by
          have hbound_pos : 0 < B.bound := by
            rw [B.bound_eq_numeral]
            exact div_pos
              (Nat.cast_pos.mpr B.boundNumerator_pos)
              (Nat.cast_pos.mpr B.boundDenominator_pos)
          positivity
        selectedRoot_mem := B.selectedRoot_mem_symmetric
        width_le_tolerance := by
          ring_nf
          exact le_rfl
        endpointsConstructedInternally :=
          B.rootBoundComputedFromCoefficientLaw
        endpointsConstructedInternally_proof :=
          B.rootBoundComputedFromCoefficientLaw_proof
        noEmpiricalEndpointImport :=
          B.noEmpiricalBoundImport
        noEmpiricalEndpointImport_proof :=
          B.noEmpiricalBoundImport_proof
        noEndpointFitTuning :=
          B.noBoundFitTuning
        noEndpointFitTuning_proof :=
          B.noBoundFitTuning_proof }
    toleranceNumerator := 2 * B.boundNumerator
    toleranceDenominator := B.boundDenominator
    toleranceDenominator_pos := B.boundDenominator_pos
    tolerance_eq_numeral := by
      change 2 * B.bound =
        ((2 * B.boundNumerator : Nat) : ℚ) / (B.boundDenominator : ℚ)
      rw [B.bound_eq_numeral]
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt B.boundDenominator_pos)]
      rw [Nat.cast_mul]
      ring
    rootIsolationComputedFromCoefficientLaw :=
      B.rootBoundComputedFromCoefficientLaw
    rootIsolationComputedFromCoefficientLaw_proof :=
      B.rootBoundComputedFromCoefficientLaw_proof
    noHiddenRootEncodingInEndpoints :=
      B.noHiddenRootEncodingInBound
    noHiddenRootEncodingInEndpoints_proof :=
      B.noHiddenRootEncodingInBound_proof }

noncomputable def rationalClosedRootPolynomialCandidateAndSymmetricBoundAsDecimalWindowCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B : ThreeFlavorSymmetricRationalRootBound G)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  ThreeFlavorSourceDerivedRationalDecimalWindowCertificate ℚ G :=
  rationalClosedRootPolynomialCandidateAndNumeralEndpointBoundsAsDecimalWindowCertificate
    G
    Q
    Psrc
    (symmetricRationalRootBoundAsNumeralEndpointBounds B)
    decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow
    hlabel

theorem rationalClosedRootPolynomialCandidateAndSymmetricBound_discharge_decimalWindowNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B : ThreeFlavorSymmetricRationalRootBound G)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  Not (NeedsThreeFlavorSourceDerivedRationalDecimalWindowCertificate ℚ G) :=
  rationalClosedRootPolynomialCandidateAndNumeralEndpointBounds_discharge_decimalWindowNeed
    G
    Q
    Psrc
    (symmetricRationalRootBoundAsNumeralEndpointBounds B)
    decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow
    hlabel

theorem rationalClosedRootPolynomialCandidateAndSymmetricBound_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B : ThreeFlavorSymmetricRationalRootBound G)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  (sourceDerivedRationalDecimalWindowAsDecimalWindow
      (rationalClosedRootPolynomialCandidateAndSymmetricBoundAsDecimalWindowCertificate
        G Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (sourceDerivedRationalDecimalWindowAsDecimalWindow
        (rationalClosedRootPolynomialCandidateAndSymmetricBoundAsDecimalWindowCertificate
          G Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)).interval.upper :=
  sourceDerivedRationalDecimalWindow_contains_gapRatio
    (rationalClosedRootPolynomialCandidateAndSymmetricBoundAsDecimalWindowCertificate
      G Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)

noncomputable def rationalClosedRootPolynomialCandidateAndAbsoluteBoundAsDecimalWindowCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B : ThreeFlavorAbsoluteRationalRootBound G)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  ThreeFlavorSourceDerivedRationalDecimalWindowCertificate ℚ G :=
  rationalClosedRootPolynomialCandidateAndSymmetricBoundAsDecimalWindowCertificate
    G
    Q
    Psrc
    (absoluteRationalRootBoundAsSymmetricBound B)
    decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow
    hlabel

theorem rationalClosedRootPolynomialCandidateAndAbsoluteBound_discharge_decimalWindowNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B : ThreeFlavorAbsoluteRationalRootBound G)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  Not (NeedsThreeFlavorSourceDerivedRationalDecimalWindowCertificate ℚ G) :=
  rationalClosedRootPolynomialCandidateAndSymmetricBound_discharge_decimalWindowNeed
    G
    Q
    Psrc
    (absoluteRationalRootBoundAsSymmetricBound B)
    decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow
    hlabel

theorem rationalClosedRootPolynomialCandidateAndAbsoluteBound_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B : ThreeFlavorAbsoluteRationalRootBound G)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  (sourceDerivedRationalDecimalWindowAsDecimalWindow
      (rationalClosedRootPolynomialCandidateAndAbsoluteBoundAsDecimalWindowCertificate
        G Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (sourceDerivedRationalDecimalWindowAsDecimalWindow
        (rationalClosedRootPolynomialCandidateAndAbsoluteBoundAsDecimalWindowCertificate
          G Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)).interval.upper :=
  sourceDerivedRationalDecimalWindow_contains_gapRatio
    (rationalClosedRootPolynomialCandidateAndAbsoluteBoundAsDecimalWindowCertificate
      G Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)

noncomputable def rationalClosedRootPolynomialCandidateAndCoefficientBoundAsDecimalWindowCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B : ThreeFlavorCoefficientDerivedAbsoluteRootBound G)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  ThreeFlavorSourceDerivedRationalDecimalWindowCertificate ℚ G :=
  rationalClosedRootPolynomialCandidateAndAbsoluteBoundAsDecimalWindowCertificate
    G
    Q
    Psrc
    (coefficientDerivedAbsoluteRootBoundAsAbsoluteBound B)
    decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow
    hlabel

theorem rationalClosedRootPolynomialCandidateAndCoefficientBound_discharge_decimalWindowNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B : ThreeFlavorCoefficientDerivedAbsoluteRootBound G)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  Not (NeedsThreeFlavorSourceDerivedRationalDecimalWindowCertificate ℚ G) :=
  rationalClosedRootPolynomialCandidateAndAbsoluteBound_discharge_decimalWindowNeed
    G
    Q
    Psrc
    (coefficientDerivedAbsoluteRootBoundAsAbsoluteBound B)
    decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow
    hlabel

theorem rationalClosedRootPolynomialCandidateAndCoefficientBound_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B : ThreeFlavorCoefficientDerivedAbsoluteRootBound G)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  (sourceDerivedRationalDecimalWindowAsDecimalWindow
      (rationalClosedRootPolynomialCandidateAndCoefficientBoundAsDecimalWindowCertificate
        G Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (sourceDerivedRationalDecimalWindowAsDecimalWindow
        (rationalClosedRootPolynomialCandidateAndCoefficientBoundAsDecimalWindowCertificate
          G Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)).interval.upper :=
  sourceDerivedRationalDecimalWindow_contains_gapRatio
    (rationalClosedRootPolynomialCandidateAndCoefficientBoundAsDecimalWindowCertificate
      G Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)

noncomputable def rationalClosedRootPolynomialCandidateAndCauchyBoundAsDecimalWindowCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B : ThreeFlavorCauchyRationalRootBound G)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  ThreeFlavorSourceDerivedRationalDecimalWindowCertificate ℚ G :=
  rationalClosedRootPolynomialCandidateAndCoefficientBoundAsDecimalWindowCertificate
    G
    Q
    Psrc
    (cauchyRationalRootBoundAsCoefficientDerivedAbsoluteRootBound B)
    decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow
    hlabel

theorem rationalClosedRootPolynomialCandidateAndCauchyBound_discharge_decimalWindowNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B : ThreeFlavorCauchyRationalRootBound G)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  Not (NeedsThreeFlavorSourceDerivedRationalDecimalWindowCertificate ℚ G) :=
  rationalClosedRootPolynomialCandidateAndCoefficientBound_discharge_decimalWindowNeed
    G
    Q
    Psrc
    (cauchyRationalRootBoundAsCoefficientDerivedAbsoluteRootBound B)
    decimalLabel
    decimalLabelCertifiedBySourceDerivedWindow
    hlabel

theorem rationalClosedRootPolynomialCandidateAndCauchyBound_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorRationalClosedRootPolynomialCandidateAudit G)
  (Psrc : ThreeFlavorCoefficientPositiveSourceAudit)
  (B : ThreeFlavorCauchyRationalRootBound G)
  (decimalLabel : String)
  (decimalLabelCertifiedBySourceDerivedWindow : Prop)
  (hlabel : decimalLabelCertifiedBySourceDerivedWindow) :
  (sourceDerivedRationalDecimalWindowAsDecimalWindow
      (rationalClosedRootPolynomialCandidateAndCauchyBoundAsDecimalWindowCertificate
        G Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)).interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (sourceDerivedRationalDecimalWindowAsDecimalWindow
        (rationalClosedRootPolynomialCandidateAndCauchyBoundAsDecimalWindowCertificate
          G Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)).interval.upper :=
  sourceDerivedRationalDecimalWindow_contains_gapRatio
    (rationalClosedRootPolynomialCandidateAndCauchyBoundAsDecimalWindowCertificate
      G Q Psrc B decimalLabel decimalLabelCertifiedBySourceDerivedWindow hlabel)

/--
Certified decimal approximation at a requested tolerance.

The decimal label is presentation-only.  The mathematical content is the
interval produced by the arbitrary-precision scheme at `eps`.
-/
structure ThreeFlavorClosedRootDecimalApproximationAtTolerance
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [LinearOrder R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (D : ThreeFlavorClosedRootDecimalReadoutReady R A P)
  (eps : R)
  (heps : 0 < eps) where
  decimalLabel : String
  window :
    ThreeFlavorClosedRootDecimalWindow
      R
      D.algebraicPresentation
  window_eq_scheme_interval :
    window.interval = D.approximationScheme.intervalFor eps heps

def decimalReadoutReadyApproximationAtTolerance
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [LinearOrder R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (D : ThreeFlavorClosedRootDecimalReadoutReady R A P)
  (eps : R)
  (heps : 0 < eps)
  (decimalLabel : String)
  (decimalLabelCertifiedByInterval : Prop)
  (hlabel : decimalLabelCertifiedByInterval) :
  ThreeFlavorClosedRootDecimalApproximationAtTolerance R D eps heps :=
  { decimalLabel := decimalLabel
    window :=
      { interval := D.approximationScheme.intervalFor eps heps
        decimalLabel := decimalLabel
        decimalLabelCertifiedByInterval := decimalLabelCertifiedByInterval
        decimalLabelCertifiedByInterval_proof := hlabel }
    window_eq_scheme_interval := rfl }

theorem decimalApproximationAtTolerance_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {D : ThreeFlavorClosedRootDecimalReadoutReady R A P}
  {eps : R}
  {heps : 0 < eps}
  (Q : ThreeFlavorClosedRootDecimalApproximationAtTolerance R D eps heps) :
  Q.window.interval.lower <= threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <= Q.window.interval.upper :=
  decimalWindow_contains_gapRatio Q.window

theorem decimalApproximationAtTolerance_width_le_requested
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {D : ThreeFlavorClosedRootDecimalReadoutReady R A P}
  {eps : R}
  {heps : 0 < eps}
  (Q : ThreeFlavorClosedRootDecimalApproximationAtTolerance R D eps heps) :
  Q.window.interval.upper - Q.window.interval.lower <= eps := by
  rw [Q.window_eq_scheme_interval]
  exact approximationScheme_width_le_requested
    D.approximationScheme
    eps
    heps

/--
Precision schedule for decimal extraction.

The schedule chooses a positive tolerance for each requested precision index.
The optional monotonicity field records the usual expectation that later
indices request no wider an interval.
-/
structure ThreeFlavorDecimalPrecisionSchedule
  (R : Type)
  [Zero R]
  [LinearOrder R] where
  toleranceAt : Nat -> R
  tolerance_pos :
    forall n : Nat, 0 < toleranceAt n
  tolerance_antitone :
    forall n m : Nat,
      n <= m ->
        toleranceAt m <= toleranceAt n
  scheduleConstructedInternally : Prop
  scheduleConstructedInternally_proof :
    scheduleConstructedInternally
  noEmpiricalPrecisionImport : Prop
  noEmpiricalPrecisionImport_proof :
    noEmpiricalPrecisionImport

/--
Certified approximation family indexed by a precision schedule.

For every precision index, this gives a decimal approximation backed by the
arbitrary-precision interval scheme.
-/
structure ThreeFlavorClosedRootScheduledDecimalReadout
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [LinearOrder R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (D : ThreeFlavorClosedRootDecimalReadoutReady R A P)
  (schedule : ThreeFlavorDecimalPrecisionSchedule R) where
  labelAt : Nat -> String
  labelCertifiedAt : Nat -> Prop
  labelCertifiedAt_proof :
    forall n : Nat, labelCertifiedAt n
  approximationAt :
    forall n : Nat,
      ThreeFlavorClosedRootDecimalApproximationAtTolerance
        R
        D
        (schedule.toleranceAt n)
        (schedule.tolerance_pos n)
  approximationAt_matches_label :
    forall n : Nat,
      (approximationAt n).decimalLabel = labelAt n

def decimalReadoutReadyScheduledReadout
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  [LinearOrder R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  (D : ThreeFlavorClosedRootDecimalReadoutReady R A P)
  (schedule : ThreeFlavorDecimalPrecisionSchedule R)
  (labelAt : Nat -> String)
  (labelCertifiedAt : Nat -> Prop)
  (hlabel : forall n : Nat, labelCertifiedAt n) :
  ThreeFlavorClosedRootScheduledDecimalReadout R D schedule :=
  { labelAt := labelAt
    labelCertifiedAt := labelCertifiedAt
    labelCertifiedAt_proof := hlabel
    approximationAt := fun n =>
      decimalReadoutReadyApproximationAtTolerance
        R
        D
        (schedule.toleranceAt n)
        (schedule.tolerance_pos n)
        (labelAt n)
        (labelCertifiedAt n)
        (hlabel n)
    approximationAt_matches_label := by
      intro n
      rfl }

theorem scheduledDecimalReadout_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {D : ThreeFlavorClosedRootDecimalReadoutReady R A P}
  {schedule : ThreeFlavorDecimalPrecisionSchedule R}
  (S : ThreeFlavorClosedRootScheduledDecimalReadout R D schedule)
  (n : Nat) :
  (S.approximationAt n).window.interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (S.approximationAt n).window.interval.upper :=
  decimalApproximationAtTolerance_contains_gapRatio (S.approximationAt n)

theorem scheduledDecimalReadout_width_le_tolerance
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {D : ThreeFlavorClosedRootDecimalReadoutReady R A P}
  {schedule : ThreeFlavorDecimalPrecisionSchedule R}
  (S : ThreeFlavorClosedRootScheduledDecimalReadout R D schedule)
  (n : Nat) :
  (S.approximationAt n).window.interval.upper -
      (S.approximationAt n).window.interval.lower <=
        schedule.toleranceAt n :=
  decimalApproximationAtTolerance_width_le_requested (S.approximationAt n)

theorem scheduledDecimalReadout_later_width_le_earlier_tolerance
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {R : Type}
  [Field R]
  [LinearOrder R]
  {A : ThreeFlavorGapRatioAlgebra M R}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H R A}
  {D : ThreeFlavorClosedRootDecimalReadoutReady R A P}
  {schedule : ThreeFlavorDecimalPrecisionSchedule R}
  (S : ThreeFlavorClosedRootScheduledDecimalReadout R D schedule)
  {n m : Nat}
  (hnm : n <= m) :
  (S.approximationAt m).window.interval.upper -
      (S.approximationAt m).window.interval.lower <=
        schedule.toleranceAt n := by
  exact le_trans
    (scheduledDecimalReadout_width_le_tolerance S m)
    (schedule.tolerance_antitone n m hnm)

def NeedsThreeFlavorQuotientNormalFormInteriorLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) : Prop :=
  Not (exists _Q : ThreeFlavorQuotientNormalFormInteriorLaw R A, True)

/--
If the quotient-normal-form interior law is supplied, then the lower-level
coordinate-anchor need is discharged.  This is a bookkeeping theorem: it keeps
the remaining blocker focused on constructing `Q`, not on any downstream
plumbing.
-/
theorem quotientNormalFormInteriorLawDischargesInternalCoordinateAnchorNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw R A) :
  Not (NeedsThreeFlavorInternalCoordinateAnchor R A) := by
  intro hneed
  exact hneed ⟨quotientNormalFormInteriorLawAsInternalCoordinateAnchor R A Q, True.intro⟩

/--
Supplying the quotient-normal-form interior law also discharges the
source-certified quotient-normal-form anchor need.
-/
theorem quotientNormalFormInteriorLawDischargesCertifiedAnchorNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw R A) :
  Not (NeedsThreeFlavorQuotientNormalFormCoordinateAnchor R A) := by
  intro hneed
  exact hneed ⟨quotientNormalFormInteriorLawAsCertifiedAnchor R A Q, True.intro⟩

/--
Conversely, an asserted quotient-normal-form interior-law need rules out every
such law.  This packages the live mathematical blocker as a reusable theorem.
-/
theorem quotientNormalFormInteriorLawNeedBlocksExactValueRoute
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (hneed : NeedsThreeFlavorQuotientNormalFormInteriorLaw R A)
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw R A) :
  False := by
  exact hneed ⟨Q, True.intro⟩

/--
Closed-expression presentation of the displayed ratio.

This is the non-root alternative to the algebraic presentation.  It is meant
for a closed symbolic expression whose denotation in `R` has been proven to be
the canonical gap ratio.
-/
structure ThreeFlavorClosedExpressionDisplayedPresentation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) where
  Expression : Type
  expression : Expression
  denoteExpression : Expression -> R
  expression_denotes_gapRatio :
    denoteExpression expression = threeFlavorGapRatio A.massSquaredLevelOf
  expressionDerivedInternally : Prop
  expressionDerivedInternally_proof :
    expressionDerivedInternally
  expressionNormalFormCertified : Prop
  expressionNormalFormCertified_proof :
    expressionNormalFormCertified
  noOneAnchorImport : Prop
  noOneAnchorImport_proof : noOneAnchorImport
  representativeBranchCollapsedModuloSkin : Prop
  representativeBranchCollapsedModuloSkin_proof :
    representativeBranchCollapsedModuloSkin
  allUnresolvedFreedomsDischarged : Prop
  allUnresolvedFreedomsDischarged_proof :
    allUnresolvedFreedomsDischarged
  calibrationPrior : Prop
  calibrationPrior_proof : calibrationPrior
  transportNeutralOrDischarged : Prop
  transportNeutralOrDischarged_proof :
    transportNeutralOrDischarged
  scaleStatusFixed : Prop
  scaleStatusFixed_proof : scaleStatusFixed
  noHiddenNumericalSelector : Prop
  noHiddenNumericalSelector_proof : noHiddenNumericalSelector
  noEmpiricalFitImport : Prop
  noEmpiricalFitImport_proof : noEmpiricalFitImport

def closedExpressionDisplayedPresentationAsDisplayed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (P : ThreeFlavorClosedExpressionDisplayedPresentation R A) :
  ThreeFlavorDisplayedRatioPresentation R A :=
  { Presentation := P.Expression
    displayed := P.expression
    denote := P.denoteExpression
    displayed_denotes_gapRatio := P.expression_denotes_gapRatio
    presentationDerivedInternally :=
      P.expressionDerivedInternally /\
        P.expressionNormalFormCertified
    presentationDerivedInternally_proof :=
      ⟨P.expressionDerivedInternally_proof,
        P.expressionNormalFormCertified_proof⟩
    noOneAnchorImport := P.noOneAnchorImport
    noOneAnchorImport_proof := P.noOneAnchorImport_proof
    representativeBranchCollapsedModuloSkin :=
      P.representativeBranchCollapsedModuloSkin
    representativeBranchCollapsedModuloSkin_proof :=
      P.representativeBranchCollapsedModuloSkin_proof
    allUnresolvedFreedomsDischarged :=
      P.allUnresolvedFreedomsDischarged
    allUnresolvedFreedomsDischarged_proof :=
      P.allUnresolvedFreedomsDischarged_proof
    calibrationPrior := P.calibrationPrior
    calibrationPrior_proof := P.calibrationPrior_proof
    transportNeutralOrDischarged := P.transportNeutralOrDischarged
    transportNeutralOrDischarged_proof :=
      P.transportNeutralOrDischarged_proof
    scaleStatusFixed := P.scaleStatusFixed
    scaleStatusFixed_proof := P.scaleStatusFixed_proof
    noHiddenNumericalSelector := P.noHiddenNumericalSelector
    noHiddenNumericalSelector_proof := P.noHiddenNumericalSelector_proof
    noEmpiricalFitImport := P.noEmpiricalFitImport
    noEmpiricalFitImport_proof := P.noEmpiricalFitImport_proof }

noncomputable def closedExpressionDisplayedPresentationGivesExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (P : ThreeFlavorClosedExpressionDisplayedPresentation R A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  AASCNNR9ExactValueFrontier C :=
  displayedRatioPresentationGivesExactValueFrontier
    R
    A
    (closedExpressionDisplayedPresentationAsDisplayed R A P)
    J
    hsingle

def NeedsThreeFlavorClosedExpressionDisplayedPresentation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) : Prop :=
  Not (exists _P :
    ThreeFlavorClosedExpressionDisplayedPresentation R A, True)

/--
Concrete closed-expression syntax for the three-flavor gap quotient.

This is the displayed formula
`(m2_1 - m2_0) / (m2_2 - m2_0)` as syntax, not a fitted numerical import.
-/
structure ThreeFlavorGapQuotientExpression
  (R : Type)
  [Field R] where
  level0 : R
  level1 : R
  level2 : R

def ThreeFlavorGapQuotientExpression.denote
  {R : Type}
  [Field R]
  (E : ThreeFlavorGapQuotientExpression R) : R :=
  (E.level1 - E.level0) / (E.level2 - E.level0)

def canonicalGapQuotientExpression
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) :
  ThreeFlavorGapQuotientExpression R :=
  { level0 := A.massSquaredLevelOf 0
    level1 := A.massSquaredLevelOf 1
    level2 := A.massSquaredLevelOf 2 }

theorem canonicalGapQuotientExpression_denotes_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) :
  (canonicalGapQuotientExpression R A).denote =
    threeFlavorGapRatio A.massSquaredLevelOf := by
  rfl

def gapQuotientExpressionAsClosedExpressionDisplayedPresentation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (hA : ThreeFlavorGapRatioAlgebraPasses A) :
  ThreeFlavorClosedExpressionDisplayedPresentation R A := by
  rcases hA with
    ⟨hratioReadback, _htwoGaps, hquotient, hscale, habsolute,
      hobserved, hroot, hordering, _htarget⟩
  exact
  { Expression := ThreeFlavorGapQuotientExpression R
    expression := canonicalGapQuotientExpression R A
    denoteExpression := fun E => E.denote
    expression_denotes_gapRatio :=
      canonicalGapQuotientExpression_denotes_gapRatio R A
    expressionDerivedInternally := A.ratioClassReadbackCertified
    expressionDerivedInternally_proof := hratioReadback
    expressionNormalFormCertified := A.quotientStableGapRatio
    expressionNormalFormCertified_proof := hquotient
    noOneAnchorImport := A.noAbsoluteMassScaleImport
    noOneAnchorImport_proof := habsolute
    representativeBranchCollapsedModuloSkin := A.quotientStableGapRatio
    representativeBranchCollapsedModuloSkin_proof := hquotient
    allUnresolvedFreedomsDischarged := A.ratioClassReadbackCertified
    allUnresolvedFreedomsDischarged_proof := hratioReadback
    calibrationPrior := A.noAbsoluteMassScaleImport
    calibrationPrior_proof := habsolute
    transportNeutralOrDischarged := A.scaleFreeGapRatio
    transportNeutralOrDischarged_proof := hscale
    scaleStatusFixed := A.quotientStableGapRatio
    scaleStatusFixed_proof := hquotient
    noHiddenNumericalSelector := A.noEigenvalueRootSelection
    noHiddenNumericalSelector_proof := hroot
    noEmpiricalFitImport :=
      A.noObservedGapImport /\ A.noOrderingFitImport
    noEmpiricalFitImport_proof := ⟨hobserved, hordering⟩ }

noncomputable def gapQuotientExpressionGivesExactValueFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  AASCNNR9ExactValueFrontier C :=
  closedExpressionDisplayedPresentationGivesExactValueFrontier
    R
    A
    (gapQuotientExpressionAsClosedExpressionDisplayedPresentation R A hA)
    J
    hsingle

/--
The canonical displayed quotient as an actual same-scope numerical-prediction
package.

This is the point where the closed-expression syntax is pushed through the
same-scope package machinery: the closed value carried by the package is the
denotation of the displayed gap quotient, not a fresh numerical anchor.
-/
noncomputable def gapQuotientExpressionAsSameScopeNumericalPredictionPackage
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  AASCSameScopePolynomialNumericalPredictionPackage H R A :=
  displayedRatioPresentationAsNumericalPredictionPackage
    R
    A
    (closedExpressionDisplayedPresentationAsDisplayed
      R
      A
      (gapQuotientExpressionAsClosedExpressionDisplayedPresentation R A hA))
    J
    hsingle

theorem gapQuotientExpression_sameScopeClosedValue_eq_denote
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  sameScopeNumericalPredictionClosedValue
      (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
        R
        A
        hA
        J
        hsingle) =
    (canonicalGapQuotientExpression R A).denote := by
  calc
    sameScopeNumericalPredictionClosedValue
        (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
          R
          A
          hA
          J
          hsingle) =
        threeFlavorGapRatio A.massSquaredLevelOf :=
      sameScopeNumericalPredictionClosedValue_eq_gapRatio
        (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
          R
          A
          hA
          J
          hsingle)
    _ = (canonicalGapQuotientExpression R A).denote :=
      (canonicalGapQuotientExpression_denotes_gapRatio R A).symm

theorem gapQuotientExpression_sameScopeClosedValue_eq_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  sameScopeNumericalPredictionClosedValue
      (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
        R
        A
        hA
        J
        hsingle) =
    threeFlavorGapRatio A.massSquaredLevelOf := by
  exact
    sameScopeNumericalPredictionClosedValue_eq_gapRatio
      (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
        R
        A
        hA
        J
        hsingle)

/--
Auditable payload for the exact symbolic readout.

It records the syntax, its denotation, the same-scope package that carries it,
and the resulting exact-value frontier.  This is a closed symbolic readout, not
a decimal approximation.
-/
structure ThreeFlavorGapQuotientExactReadout
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M)
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R) where
  expression : ThreeFlavorGapQuotientExpression R
  expression_eq_canonical :
    expression = canonicalGapQuotientExpression R A
  expression_denotes_gapRatio :
    expression.denote = threeFlavorGapRatio A.massSquaredLevelOf
  package : AASCSameScopePolynomialNumericalPredictionPackage H R A
  package_closedValue_eq_expression_denote :
    sameScopeNumericalPredictionClosedValue package =
      expression.denote
  exactValueFrontier : AASCNNR9ExactValueFrontier C

noncomputable def gapQuotientExpressionExactReadout
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  ThreeFlavorGapQuotientExactReadout H R A :=
  { expression := canonicalGapQuotientExpression R A
    expression_eq_canonical := rfl
    expression_denotes_gapRatio :=
      canonicalGapQuotientExpression_denotes_gapRatio R A
    package :=
      gapQuotientExpressionAsSameScopeNumericalPredictionPackage
        R
        A
        hA
        J
        hsingle
    package_closedValue_eq_expression_denote :=
      gapQuotientExpression_sameScopeClosedValue_eq_denote
        R
        A
        hA
        J
        hsingle
    exactValueFrontier :=
      sameScopeNumericalPredictionExactValueFrontier
        R
        A
        (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
          R
          A
          hA
          J
          hsingle) }

/--
Rational-domain decimal-readout readiness for the gap-quotient payload.

This clears the next formal blocker after exact symbolic readout: once the
coefficient domain is `ℚ`, the same-scope package carries the standard
proof-carrying rational isolation scheme.  The scheme is readiness for decimal
approximation; concrete human decimal numerals still require choosing an
explicit approximation tolerance/label, or a non-symbolic endpoint certificate.
-/
noncomputable def gapQuotientExpressionAsRationalDecimalReadoutReady
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  ThreeFlavorClosedRootDecimalReadoutReady
    ℚ
    A
    (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
      ℚ
      A
      hA
      J
      hsingle) :=
  sameScopePackageAsRationalDecimalReadoutReady
    A
    (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
      ℚ
      A
      hA
      J
      hsingle)

structure ThreeFlavorGapQuotientRationalDecimalReadoutReady
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M)
  (A : ThreeFlavorGapRatioAlgebra M ℚ) where
  exactReadout : ThreeFlavorGapQuotientExactReadout H ℚ A
  decimalReady :
    ThreeFlavorClosedRootDecimalReadoutReady
      ℚ
      A
      exactReadout.package

noncomputable def gapQuotientExpressionRationalDecimalReadoutReady
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  ThreeFlavorGapQuotientRationalDecimalReadoutReady H A :=
  { exactReadout :=
      gapQuotientExpressionExactReadout
        ℚ
        A
        hA
        J
        hsingle
    decimalReady :=
      gapQuotientExpressionAsRationalDecimalReadoutReady
        A
        hA
        J
        hsingle }

def NeedsGapQuotientRationalDecimalReadoutReady
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (H : AASCHybridCompressionNetwork C M)
  (A : ThreeFlavorGapRatioAlgebra M ℚ) : Prop :=
  Not (exists _D :
    ThreeFlavorGapQuotientRationalDecimalReadoutReady H A, True)

theorem gapQuotientExpression_discharge_rationalDecimalReadoutReadyNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H) :
  Not (NeedsGapQuotientRationalDecimalReadoutReady H A) := by
  intro hneed
  exact hneed
    ⟨gapQuotientExpressionRationalDecimalReadoutReady
        A
        hA
        J
        hsingle,
      True.intro⟩

noncomputable def gapQuotientExpressionRationalApproximationAtTolerance
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (eps : ℚ)
  (heps : 0 < eps)
  (decimalLabel : String)
  (decimalLabelCertifiedByInterval : Prop)
  (hlabel : decimalLabelCertifiedByInterval) :
  ThreeFlavorClosedRootDecimalApproximationAtTolerance
    ℚ
    (gapQuotientExpressionAsRationalDecimalReadoutReady
      A
      hA
      J
      hsingle)
    eps
    heps :=
  decimalReadoutReadyApproximationAtTolerance
    ℚ
    (gapQuotientExpressionAsRationalDecimalReadoutReady
      A
      hA
      J
      hsingle)
    eps
    heps
    decimalLabel
    decimalLabelCertifiedByInterval
    hlabel

theorem gapQuotientExpressionRationalApproximationAtTolerance_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (eps : ℚ)
  (heps : 0 < eps)
  (decimalLabel : String)
  (decimalLabelCertifiedByInterval : Prop)
  (hlabel : decimalLabelCertifiedByInterval) :
  (gapQuotientExpressionRationalApproximationAtTolerance
      A
      hA
      J
      hsingle
      eps
      heps
      decimalLabel
      decimalLabelCertifiedByInterval
      hlabel).window.interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (gapQuotientExpressionRationalApproximationAtTolerance
        A
        hA
        J
        hsingle
        eps
        heps
        decimalLabel
        decimalLabelCertifiedByInterval
        hlabel).window.interval.upper :=
  decimalApproximationAtTolerance_contains_gapRatio
    (gapQuotientExpressionRationalApproximationAtTolerance
      A
      hA
      J
      hsingle
      eps
      heps
      decimalLabel
      decimalLabelCertifiedByInterval
      hlabel)

theorem gapQuotientExpressionRationalApproximationAtTolerance_width_le
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (eps : ℚ)
  (heps : 0 < eps)
  (decimalLabel : String)
  (decimalLabelCertifiedByInterval : Prop)
  (hlabel : decimalLabelCertifiedByInterval) :
  (gapQuotientExpressionRationalApproximationAtTolerance
      A
      hA
      J
      hsingle
      eps
      heps
      decimalLabel
      decimalLabelCertifiedByInterval
      hlabel).window.interval.upper -
      (gapQuotientExpressionRationalApproximationAtTolerance
        A
        hA
        J
        hsingle
        eps
        heps
        decimalLabel
        decimalLabelCertifiedByInterval
        hlabel).window.interval.lower <= eps :=
  decimalApproximationAtTolerance_width_le_requested
    (gapQuotientExpressionRationalApproximationAtTolerance
      A
      hA
      J
      hsingle
      eps
      heps
      decimalLabel
      decimalLabelCertifiedByInterval
      hlabel)

/--
Concrete numeral endpoint window for the gap quotient.

Strict ordering of the three mass-squared levels proves the canonical ratio is
inside `[0, 1]`.  The endpoints are literal rational numerals, so this clears
the non-symbolic-endpoint blocker at coarse precision.
-/
def gapQuotientExpressionUnitNumeralInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A)) :
  ThreeFlavorNumeralRationalClosedRootInterval
    (sameScopePackageAsAlgebraicClosedRootPresentation
      ℚ
      A
      (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
        ℚ
        A
        hA
        J
        hsingle)) := by
  let P :=
    gapQuotientExpressionAsSameScopeNumericalPredictionPackage
      ℚ
      A
      hA
      J
      hsingle
  let G := sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P
  have hroot :
      G.selectedRoot = threeFlavorGapRatio A.massSquaredLevelOf :=
    algebraicClosedRootPresentation_selectedRoot_eq_gapRatio G
  rcases hA with
    ⟨_hratioReadback, htwoGaps, _hquotient, hscale, habsolute,
      hobserved, _hroot, hordering, htarget⟩
  exact
  { lower := 0
    upper := 1
    tolerance := 1
    lowerNumerator := 0
    lowerDenominator := 1
    lowerDenominator_pos := by norm_num
    upperNumerator := 1
    upperDenominator := 1
    upperDenominator_pos := by norm_num
    lower_eq_numeral := by norm_num
    upper_eq_numeral := by norm_num
    lower_lt_upper := by norm_num
    tolerance_pos := by norm_num
    selectedRoot_mem := by
      constructor
      · rw [hroot]
        exact strictMassSquaredOrdering_gapRatio_nonneg O
      · rw [hroot]
        exact strictMassSquaredOrdering_gapRatio_le_one O
    width_le_tolerance := by norm_num
    endpointsConstructedInternally :=
      A.twoIndependentGapsCertified /\ A.sameStandingRatioTarget
    endpointsConstructedInternally_proof := ⟨htwoGaps, htarget⟩
    noEmpiricalEndpointImport :=
      A.noObservedGapImport /\ A.noOrderingFitImport
    noEmpiricalEndpointImport_proof := ⟨hobserved, hordering⟩
    noEndpointFitTuning :=
      A.noAbsoluteMassScaleImport /\ A.scaleFreeGapRatio
    noEndpointFitTuning_proof := ⟨habsolute, hscale⟩ }

def gapQuotientExpressionUnitNumeralIntervalAsDecimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (decimalLabel : String)
  (decimalLabelCertifiedByInterval : Prop)
  (hlabel : decimalLabelCertifiedByInterval) :
  ThreeFlavorClosedRootDecimalWindow
    ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation
      ℚ
      A
      (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
        ℚ
        A
        hA
        J
        hsingle)) :=
  { interval :=
      explicitRationalClosedRootIntervalAsIsolatingInterval
        (numeralRationalClosedRootIntervalAsExplicitInterval
          (gapQuotientExpressionUnitNumeralInterval
            A
            hA
            J
            hsingle
            O))
    decimalLabel := decimalLabel
    decimalLabelCertifiedByInterval := decimalLabelCertifiedByInterval
    decimalLabelCertifiedByInterval_proof := hlabel }

theorem gapQuotientExpressionUnitNumeralInterval_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A)) :
  (gapQuotientExpressionUnitNumeralInterval
      A
      hA
      J
      hsingle
      O).lower <= threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (gapQuotientExpressionUnitNumeralInterval
        A
        hA
        J
      hsingle
      O).upper := by
  let P :=
    gapQuotientExpressionAsSameScopeNumericalPredictionPackage
      ℚ
      A
      hA
      J
      hsingle
  let G := sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P
  let I := gapQuotientExpressionUnitNumeralInterval A hA J hsingle O
  have hroot :
      G.selectedRoot = threeFlavorGapRatio A.massSquaredLevelOf :=
    algebraicClosedRootPresentation_selectedRoot_eq_gapRatio G
  have hmem := I.selectedRoot_mem
  constructor
  · simpa [I, G, P, hroot] using hmem.1
  · simpa [I, G, P, hroot] using hmem.2

theorem gapQuotientExpressionUnitNumeralInterval_width_le_tolerance
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A)) :
  (gapQuotientExpressionUnitNumeralInterval
      A
      hA
      J
      hsingle
      O).upper -
      (gapQuotientExpressionUnitNumeralInterval
        A
        hA
        J
        hsingle
        O).lower <=
    (gapQuotientExpressionUnitNumeralInterval
      A
      hA
      J
      hsingle
      O).tolerance := by
  exact
    (gapQuotientExpressionUnitNumeralInterval
      A
      hA
      J
      hsingle
      O).width_le_tolerance

/--
Audited numeral upper bound for a proper subinterval of `[0, 1]`.

The mathematical payload is a same-scope dominance inequality
`solarGap <= upper * atmosphericGap`, with `0 < upper < 1`.  This is exactly
the extra content needed to move from the coarse quotient window `[0, 1]` to a
proper internally-derived numeral window `[0, upper]`.
-/
structure ThreeFlavorGapDominanceNumeralUpperBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  upper : ℚ
  upperNumerator : Int
  upperDenominator : Nat
  upperDenominator_pos : 0 < upperDenominator
  upper_eq_numeral :
    upper = (upperNumerator : ℚ) / (upperDenominator : ℚ)
  upper_pos : 0 < upper
  upper_lt_one : upper < 1
  solarGap_le_upper_mul_atmosphericGap :
    threeFlavorSolarGap A.massSquaredLevelOf <=
      upper * threeFlavorAtmosphericGap A.massSquaredLevelOf
  dominanceDerivedInternally : Prop
  dominanceDerivedInternally_proof :
    dominanceDerivedInternally
  noEmpiricalDominanceImport : Prop
  noEmpiricalDominanceImport_proof :
    noEmpiricalDominanceImport
  noDominanceFitTuning : Prop
  noDominanceFitTuning_proof :
    noDominanceFitTuning

theorem gapDominanceNumeralUpperBound_gapRatio_le_upper
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (B : ThreeFlavorGapDominanceNumeralUpperBound (A := A))
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A)) :
  threeFlavorGapRatio A.massSquaredLevelOf <= B.upper := by
  have hden_pos :
      0 < threeFlavorAtmosphericGap A.massSquaredLevelOf := by
    unfold threeFlavorAtmosphericGap
    linarith [O.level0_lt_level1, O.level1_lt_level2]
  unfold threeFlavorGapRatio
  exact
    (div_le_iff₀ hden_pos).mpr
      B.solarGap_le_upper_mul_atmosphericGap

def gapDominanceNumeralUpperBoundAsInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (B : ThreeFlavorGapDominanceNumeralUpperBound (A := A)) :
  ThreeFlavorNumeralRationalClosedRootInterval
    (sameScopePackageAsAlgebraicClosedRootPresentation
      ℚ
      A
      (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
        ℚ
        A
        hA
        J
        hsingle)) := by
  let P :=
    gapQuotientExpressionAsSameScopeNumericalPredictionPackage
      ℚ
      A
      hA
      J
      hsingle
  let G := sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P
  have hroot :
      G.selectedRoot = threeFlavorGapRatio A.massSquaredLevelOf :=
    algebraicClosedRootPresentation_selectedRoot_eq_gapRatio G
  exact
  { lower := 0
    upper := B.upper
    tolerance := B.upper
    lowerNumerator := 0
    lowerDenominator := 1
    lowerDenominator_pos := by norm_num
    upperNumerator := B.upperNumerator
    upperDenominator := B.upperDenominator
    upperDenominator_pos := B.upperDenominator_pos
    lower_eq_numeral := by norm_num
    upper_eq_numeral := B.upper_eq_numeral
    lower_lt_upper := by simpa using B.upper_pos
    tolerance_pos := B.upper_pos
    selectedRoot_mem := by
      constructor
      · rw [hroot]
        exact strictMassSquaredOrdering_gapRatio_nonneg O
      · rw [hroot]
        exact gapDominanceNumeralUpperBound_gapRatio_le_upper B O
    width_le_tolerance := by
      ring_nf
      exact le_rfl
    endpointsConstructedInternally :=
      B.dominanceDerivedInternally
    endpointsConstructedInternally_proof :=
      B.dominanceDerivedInternally_proof
    noEmpiricalEndpointImport :=
      B.noEmpiricalDominanceImport
    noEmpiricalEndpointImport_proof :=
      B.noEmpiricalDominanceImport_proof
    noEndpointFitTuning :=
      B.noDominanceFitTuning
    noEndpointFitTuning_proof :=
      B.noDominanceFitTuning_proof }

theorem gapDominanceNumeralUpperBound_interval_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (B : ThreeFlavorGapDominanceNumeralUpperBound (A := A)) :
  (gapDominanceNumeralUpperBoundAsInterval
      A
      hA
      J
      hsingle
      O
      B).lower <= threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (gapDominanceNumeralUpperBoundAsInterval
        A
        hA
        J
        hsingle
        O
        B).upper := by
  let P :=
    gapQuotientExpressionAsSameScopeNumericalPredictionPackage
      ℚ
      A
      hA
      J
      hsingle
  let G := sameScopePackageAsAlgebraicClosedRootPresentation ℚ A P
  let I := gapDominanceNumeralUpperBoundAsInterval A hA J hsingle O B
  have hroot :
      G.selectedRoot = threeFlavorGapRatio A.massSquaredLevelOf :=
    algebraicClosedRootPresentation_selectedRoot_eq_gapRatio G
  have hmem := I.selectedRoot_mem
  constructor
  · simpa [I, G, P, hroot] using hmem.1
  · simpa [I, G, P, hroot] using hmem.2

theorem gapDominanceNumeralUpperBound_interval_upper_lt_one
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (B : ThreeFlavorGapDominanceNumeralUpperBound (A := A)) :
  (gapDominanceNumeralUpperBoundAsInterval
      A
      hA
      J
      hsingle
      O
      B).upper < 1 := by
  simpa [gapDominanceNumeralUpperBoundAsInterval] using B.upper_lt_one

def gapDominanceNumeralUpperBoundAsDecimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (B : ThreeFlavorGapDominanceNumeralUpperBound (A := A))
  (decimalLabel : String)
  (decimalLabelCertifiedByInterval : Prop)
  (hlabel : decimalLabelCertifiedByInterval) :
  ThreeFlavorClosedRootDecimalWindow
    ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation
      ℚ
      A
      (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
        ℚ
        A
        hA
        J
        hsingle)) :=
  { interval :=
      explicitRationalClosedRootIntervalAsIsolatingInterval
        (numeralRationalClosedRootIntervalAsExplicitInterval
          (gapDominanceNumeralUpperBoundAsInterval
            A
            hA
            J
            hsingle
            O
            B))
    decimalLabel := decimalLabel
    decimalLabelCertifiedByInterval := decimalLabelCertifiedByInterval
    decimalLabelCertifiedByInterval_proof := hlabel }

def NeedsThreeFlavorGapDominanceNumeralUpperBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ) : Prop :=
  Not (exists _B :
    ThreeFlavorGapDominanceNumeralUpperBound (A := A), True)

theorem gapDominanceNumeralUpperBound_discharge_properSubintervalNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (B : ThreeFlavorGapDominanceNumeralUpperBound (A := A)) :
  Not (NeedsThreeFlavorGapDominanceNumeralUpperBound A) := by
  intro hneed
  exact hneed ⟨B, True.intro⟩

/--
Midpoint compression law for the three mass-squared levels.

This is the first concrete proper-subinterval source shape: if the middle
level lies at or below the arithmetic midpoint of the lower and upper levels,
then the solar gap is at most half of the atmospheric gap.
-/
structure ThreeFlavorMidpointGapCompression
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  midpointCompression :
    2 * A.massSquaredLevelOf 1 <=
      A.massSquaredLevelOf 0 + A.massSquaredLevelOf 2
  midpointCompressionDerivedInternally : Prop
  midpointCompressionDerivedInternally_proof :
    midpointCompressionDerivedInternally
  noEmpiricalMidpointImport : Prop
  noEmpiricalMidpointImport_proof :
    noEmpiricalMidpointImport
  noMidpointFitTuning : Prop
  noMidpointFitTuning_proof :
    noMidpointFitTuning

/--
Adjacent-gap half-side source law.

This is the same midpoint compression written in the more local language of
the two adjacent gaps: the lower adjacent gap is no larger than the upper
adjacent gap.
-/
structure ThreeFlavorAdjacentGapHalfSide
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  lowerAdjacentGap_le_upperAdjacentGap :
    A.massSquaredLevelOf 1 - A.massSquaredLevelOf 0 <=
      A.massSquaredLevelOf 2 - A.massSquaredLevelOf 1
  adjacentGapLawDerivedInternally : Prop
  adjacentGapLawDerivedInternally_proof :
    adjacentGapLawDerivedInternally
  noEmpiricalAdjacentGapImport : Prop
  noEmpiricalAdjacentGapImport_proof :
    noEmpiricalAdjacentGapImport
  noAdjacentGapFitTuning : Prop
  noAdjacentGapFitTuning_proof :
    noAdjacentGapFitTuning

/--
Two-step gap half-dominance source law.

This is the same half-side condition without midpoint language: twice the lower
adjacent gap is at most the full lower-to-upper two-step gap.
-/
structure ThreeFlavorTwoStepGapHalfDominance
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  twiceLowerGap_le_totalGap :
    2 * (A.massSquaredLevelOf 1 - A.massSquaredLevelOf 0) <=
      A.massSquaredLevelOf 2 - A.massSquaredLevelOf 0
  twoStepGapLawDerivedInternally : Prop
  twoStepGapLawDerivedInternally_proof :
    twoStepGapLawDerivedInternally
  noEmpiricalTwoStepGapImport : Prop
  noEmpiricalTwoStepGapImport_proof :
    noEmpiricalTwoStepGapImport
  noTwoStepGapFitTuning : Prop
  noTwoStepGapFitTuning_proof :
    noTwoStepGapFitTuning

/--
Second finite-difference shape law for the three mass-squared levels.

This is the operator/spectral version of the half-side condition: the ordered
three-level spectrum is convex at the middle level.
-/
structure ThreeFlavorMassSquaredConvexity
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  secondFiniteDifference_nonneg :
    0 <=
      A.massSquaredLevelOf 0 -
        2 * A.massSquaredLevelOf 1 +
          A.massSquaredLevelOf 2
  convexityLawDerivedInternally : Prop
  convexityLawDerivedInternally_proof :
    convexityLawDerivedInternally
  noEmpiricalConvexityImport : Prop
  noEmpiricalConvexityImport_proof :
    noEmpiricalConvexityImport
  noConvexityFitTuning : Prop
  noConvexityFitTuning_proof :
    noConvexityFitTuning

/--
Source-derived curvature witness for the three-level mass-squared spectrum.

This packages the convexity inequality as an evaluated internal curvature
scalar.  The source must derive the scalar, identify it with the second finite
difference, and prove it is nonnegative.
-/
structure ThreeFlavorSourceCurvatureNonnegative
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  curvature : ℚ
  curvature_eq_secondFiniteDifference :
    curvature =
      A.massSquaredLevelOf 0 -
        2 * A.massSquaredLevelOf 1 +
          A.massSquaredLevelOf 2
  curvature_nonneg :
    0 <= curvature
  curvatureDerivedInternally : Prop
  curvatureDerivedInternally_proof :
    curvatureDerivedInternally
  curvatureSameScopeAsMassSquaredLevels : Prop
  curvatureSameScopeAsMassSquaredLevels_proof :
    curvatureSameScopeAsMassSquaredLevels
  noEmpiricalCurvatureImport : Prop
  noEmpiricalCurvatureImport_proof :
    noEmpiricalCurvatureImport
  noCurvatureFitTuning : Prop
  noCurvatureFitTuning_proof :
    noCurvatureFitTuning

/--
Square witness for nonnegative source curvature.

This is the constructive positivity form of the curvature blocker: the source
does not merely assert `0 <= curvature`; it presents a coordinate whose square
is the curvature.
-/
structure ThreeFlavorSourceCurvatureSquareWitness
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  curvatureCoordinate : ℚ
  curvatureCoordinateSquared_eq_secondFiniteDifference :
    curvatureCoordinate ^ 2 =
      A.massSquaredLevelOf 0 -
        2 * A.massSquaredLevelOf 1 +
          A.massSquaredLevelOf 2
  curvatureCoordinateDerivedInternally : Prop
  curvatureCoordinateDerivedInternally_proof :
    curvatureCoordinateDerivedInternally
  curvatureCoordinateSameScopeAsMassSquaredLevels : Prop
  curvatureCoordinateSameScopeAsMassSquaredLevels_proof :
    curvatureCoordinateSameScopeAsMassSquaredLevels
  noEmpiricalCurvatureCoordinateImport : Prop
  noEmpiricalCurvatureCoordinateImport_proof :
    noEmpiricalCurvatureCoordinateImport
  noCurvatureCoordinateFitTuning : Prop
  noCurvatureCoordinateFitTuning_proof :
    noCurvatureCoordinateFitTuning

/--
Finite sum-of-squares witness for nonnegative source curvature.

This is more flexible than a single-square witness: the source may present a
finite family of internal curvature coordinates whose squared sum is the
second finite difference.
-/
structure ThreeFlavorSourceCurvatureSumSquaresWitness
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  Index : Type
  finiteIndex : Fintype Index
  curvatureCoordinate : Index -> ℚ
  curvatureSumSquares_eq_secondFiniteDifference :
    (@Finset.univ Index finiteIndex).sum
        (fun i => curvatureCoordinate i ^ 2) =
      A.massSquaredLevelOf 0 -
        2 * A.massSquaredLevelOf 1 +
          A.massSquaredLevelOf 2
  curvatureCoordinatesDerivedInternally : Prop
  curvatureCoordinatesDerivedInternally_proof :
    curvatureCoordinatesDerivedInternally
  curvatureCoordinatesSameScopeAsMassSquaredLevels : Prop
  curvatureCoordinatesSameScopeAsMassSquaredLevels_proof :
    curvatureCoordinatesSameScopeAsMassSquaredLevels
  noEmpiricalCurvatureCoordinatesImport : Prop
  noEmpiricalCurvatureCoordinatesImport_proof :
    noEmpiricalCurvatureCoordinatesImport
  noCurvatureCoordinatesFitTuning : Prop
  noCurvatureCoordinatesFitTuning_proof :
    noCurvatureCoordinatesFitTuning

/--
Gram-diagonal curvature witness.

This is the operator-facing version of the sum-of-squares witness: the source
presents a finite diagonal/Gram coordinate family whose diagonal square sum is
the curvature second finite difference.
-/
structure ThreeFlavorSourceCurvatureGramDiagonalWitness
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  Index : Type
  finiteIndex : Fintype Index
  gramDiagonalCoordinate : Index -> ℚ
  gramDiagonalSquareSum_eq_secondFiniteDifference :
    (@Finset.univ Index finiteIndex).sum
        (fun i => gramDiagonalCoordinate i ^ 2) =
      A.massSquaredLevelOf 0 -
        2 * A.massSquaredLevelOf 1 +
          A.massSquaredLevelOf 2
  gramDiagonalConstructedInternally : Prop
  gramDiagonalConstructedInternally_proof :
    gramDiagonalConstructedInternally
  gramDiagonalSameScopeAsMassSquaredLevels : Prop
  gramDiagonalSameScopeAsMassSquaredLevels_proof :
    gramDiagonalSameScopeAsMassSquaredLevels
  gramDiagonalPSDSourceCertified : Prop
  gramDiagonalPSDSourceCertified_proof :
    gramDiagonalPSDSourceCertified
  noEmpiricalGramImport : Prop
  noEmpiricalGramImport_proof :
    noEmpiricalGramImport
  noGramFitTuning : Prop
  noGramFitTuning_proof :
    noGramFitTuning

/--
Concrete finite-coordinate table for the Gram-diagonal curvature witness.

This replaces the abstract finite index type by an explicit `Fin n` table,
which is the form most convenient for computation, extraction, and manuscript
audit.
-/
structure ThreeFlavorSourceCurvatureFiniteCoordinateTable
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  coordinateCount : Nat
  coordinateAt : Fin coordinateCount -> ℚ
  coordinateSquareSum_eq_secondFiniteDifference :
    (Finset.univ.sum fun i : Fin coordinateCount =>
        coordinateAt i ^ 2) =
      A.massSquaredLevelOf 0 -
        2 * A.massSquaredLevelOf 1 +
          A.massSquaredLevelOf 2
  coordinateTableConstructedInternally : Prop
  coordinateTableConstructedInternally_proof :
    coordinateTableConstructedInternally
  coordinateTableSameScopeAsMassSquaredLevels : Prop
  coordinateTableSameScopeAsMassSquaredLevels_proof :
    coordinateTableSameScopeAsMassSquaredLevels
  coordinateTablePSDSourceCertified : Prop
  coordinateTablePSDSourceCertified_proof :
    coordinateTablePSDSourceCertified
  noEmpiricalCoordinateTableImport : Prop
  noEmpiricalCoordinateTableImport_proof :
    noEmpiricalCoordinateTableImport
  noCoordinateTableFitTuning : Prop
  noCoordinateTableFitTuning_proof :
    noCoordinateTableFitTuning

/--
Recognition-composition-law curvature table.

This is an external-candidate translation socket.  It does not treat RCL as
authority; it requires the RCL route to supply the same concrete finite
coordinate square-sum identity and the AASC audit guards.
-/
structure ThreeFlavorRCLCurvatureFiniteCoordinateTable
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  coordinateCount : Nat
  coordinateAt : Fin coordinateCount -> ℚ
  rclSquareSum_eq_secondFiniteDifference :
    (Finset.univ.sum fun i : Fin coordinateCount =>
        coordinateAt i ^ 2) =
      A.massSquaredLevelOf 0 -
        2 * A.massSquaredLevelOf 1 +
          A.massSquaredLevelOf 2
  rclCostLawTranslatedToAASC : Prop
  rclCostLawTranslatedToAASC_proof :
    rclCostLawTranslatedToAASC
  rclCoordinateTableSameScope : Prop
  rclCoordinateTableSameScope_proof :
    rclCoordinateTableSameScope
  rclPSDOrSOSCertificate : Prop
  rclPSDOrSOSCertificate_proof :
    rclPSDOrSOSCertificate
  noEmpiricalRCLMassImport : Prop
  noEmpiricalRCLMassImport_proof :
    noEmpiricalRCLMassImport
  noRCLFitTuning : Prop
  noRCLFitTuning_proof :
    noRCLFitTuning

def rclCurvatureTableAsSourceCurvatureFiniteCoordinateTable
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (R : ThreeFlavorRCLCurvatureFiniteCoordinateTable (A := A)) :
  ThreeFlavorSourceCurvatureFiniteCoordinateTable (A := A) :=
  { gapRatioAlgebraPasses := R.gapRatioAlgebraPasses
    coordinateCount := R.coordinateCount
    coordinateAt := R.coordinateAt
    coordinateSquareSum_eq_secondFiniteDifference :=
      R.rclSquareSum_eq_secondFiniteDifference
    coordinateTableConstructedInternally :=
      R.rclCostLawTranslatedToAASC
    coordinateTableConstructedInternally_proof :=
      R.rclCostLawTranslatedToAASC_proof
    coordinateTableSameScopeAsMassSquaredLevels :=
      R.rclCoordinateTableSameScope
    coordinateTableSameScopeAsMassSquaredLevels_proof :=
      R.rclCoordinateTableSameScope_proof
    coordinateTablePSDSourceCertified :=
      R.rclPSDOrSOSCertificate
    coordinateTablePSDSourceCertified_proof :=
      R.rclPSDOrSOSCertificate_proof
    noEmpiricalCoordinateTableImport :=
      R.noEmpiricalRCLMassImport
    noEmpiricalCoordinateTableImport_proof :=
      R.noEmpiricalRCLMassImport_proof
    noCoordinateTableFitTuning :=
      R.noRCLFitTuning
    noCoordinateTableFitTuning_proof :=
      R.noRCLFitTuning_proof }

/--
Relator-lock curvature table.

This is the Rω=c candidate translation socket.  The kinematic lock must be
translated into the same finite coordinate square-sum identity and must pass
the AASC same-scope/no-fit guards.
-/
structure ThreeFlavorRelatorLockCurvatureFiniteCoordinateTable
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  coordinateCount : Nat
  coordinateAt : Fin coordinateCount -> ℚ
  relatorSquareSum_eq_secondFiniteDifference :
    (Finset.univ.sum fun i : Fin coordinateCount =>
        coordinateAt i ^ 2) =
      A.massSquaredLevelOf 0 -
        2 * A.massSquaredLevelOf 1 +
          A.massSquaredLevelOf 2
  relatorLockTranslatedToAASC : Prop
  relatorLockTranslatedToAASC_proof :
    relatorLockTranslatedToAASC
  relatorCoordinateTableSameScope : Prop
  relatorCoordinateTableSameScope_proof :
    relatorCoordinateTableSameScope
  relatorPSDOrSOSCertificate : Prop
  relatorPSDOrSOSCertificate_proof :
    relatorPSDOrSOSCertificate
  noEmpiricalRelatorMassImport : Prop
  noEmpiricalRelatorMassImport_proof :
    noEmpiricalRelatorMassImport
  noRelatorFitTuning : Prop
  noRelatorFitTuning_proof :
    noRelatorFitTuning

def relatorLockCurvatureTableAsSourceCurvatureFiniteCoordinateTable
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (R : ThreeFlavorRelatorLockCurvatureFiniteCoordinateTable (A := A)) :
  ThreeFlavorSourceCurvatureFiniteCoordinateTable (A := A) :=
  { gapRatioAlgebraPasses := R.gapRatioAlgebraPasses
    coordinateCount := R.coordinateCount
    coordinateAt := R.coordinateAt
    coordinateSquareSum_eq_secondFiniteDifference :=
      R.relatorSquareSum_eq_secondFiniteDifference
    coordinateTableConstructedInternally :=
      R.relatorLockTranslatedToAASC
    coordinateTableConstructedInternally_proof :=
      R.relatorLockTranslatedToAASC_proof
    coordinateTableSameScopeAsMassSquaredLevels :=
      R.relatorCoordinateTableSameScope
    coordinateTableSameScopeAsMassSquaredLevels_proof :=
      R.relatorCoordinateTableSameScope_proof
    coordinateTablePSDSourceCertified :=
      R.relatorPSDOrSOSCertificate
    coordinateTablePSDSourceCertified_proof :=
      R.relatorPSDOrSOSCertificate_proof
    noEmpiricalCoordinateTableImport :=
      R.noEmpiricalRelatorMassImport
    noEmpiricalCoordinateTableImport_proof :=
      R.noEmpiricalRelatorMassImport_proof
    noCoordinateTableFitTuning :=
      R.noRelatorFitTuning
    noCoordinateTableFitTuning_proof :=
      R.noRelatorFitTuning_proof }

/--
Source certificate for the Relator even-tower shape.

This is the upstream audit object for the Relator route.  It separates the
source-side construction of the `scale/beta/delta` table and the fixed
`k = 1, 3, 5` exponent schedule from the downstream convexity/readout theorem.
The last guard prevents the parameters from being a disguised encoding of the
selected root or empirical ratio.
-/
structure ThreeFlavorRelatorEvenTowerSourceCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  beta : ℚ
  delta : ℚ
  normalizationScale : ℚ
  beta_nonneg :
    0 <= beta
  delta_nonneg :
    0 <= delta
  normalizationScale_nonneg :
    0 <= normalizationScale
  level0_eq :
    A.massSquaredLevelOf 0 =
      normalizationScale * (1 + beta + delta)
  level1_eq :
    A.massSquaredLevelOf 1 =
      normalizationScale * (81 + 729 * beta + 6561 * delta)
  level2_eq :
    A.massSquaredLevelOf 2 =
      normalizationScale * (625 + 15625 * beta + 390625 * delta)
  relatorParameterTableSourceDerived : Prop
  relatorParameterTableSourceDerived_proof :
    relatorParameterTableSourceDerived
  relatorExponentScheduleFixedBySource : Prop
  relatorExponentScheduleFixedBySource_proof :
    relatorExponentScheduleFixedBySource
  relatorEvenTowerSameScopeAsMassSquaredLevels : Prop
  relatorEvenTowerSameScopeAsMassSquaredLevels_proof :
    relatorEvenTowerSameScopeAsMassSquaredLevels
  noEmpiricalRelatorEvenTowerImport : Prop
  noEmpiricalRelatorEvenTowerImport_proof :
    noEmpiricalRelatorEvenTowerImport
  noRelatorEvenTowerFitTuning : Prop
  noRelatorEvenTowerFitTuning_proof :
    noRelatorEvenTowerFitTuning
  noHiddenRootEncodingInRelatorParameters : Prop
  noHiddenRootEncodingInRelatorParameters_proof :
    noHiddenRootEncodingInRelatorParameters

structure ThreeFlavorRelatorEvenTowerParameterTable where
  beta : ℚ
  delta : ℚ
  normalizationScale : ℚ
  beta_nonneg :
    0 <= beta
  delta_nonneg :
    0 <= delta
  normalizationScale_nonneg :
    0 <= normalizationScale
  parameterTableSourceDerived : Prop
  parameterTableSourceDerived_proof :
    parameterTableSourceDerived
  noHiddenRootEncodingInParameters : Prop
  noHiddenRootEncodingInParameters_proof :
    noHiddenRootEncodingInParameters

structure ThreeFlavorRelatorEvenTowerNumeralParameterTable where
  betaNumerator : Nat
  betaDenominator : Nat
  betaDenominator_pos :
    0 < betaDenominator
  deltaNumerator : Nat
  deltaDenominator : Nat
  deltaDenominator_pos :
    0 < deltaDenominator
  scaleNumerator : Nat
  scaleDenominator : Nat
  scaleDenominator_pos :
    0 < scaleDenominator
  parameterTableSourceDerived : Prop
  parameterTableSourceDerived_proof :
    parameterTableSourceDerived
  noHiddenRootEncodingInParameters : Prop
  noHiddenRootEncodingInParameters_proof :
    noHiddenRootEncodingInParameters

def relatorEvenTowerNumeralParameterTableAsParameterTable
  (N : ThreeFlavorRelatorEvenTowerNumeralParameterTable) :
  ThreeFlavorRelatorEvenTowerParameterTable :=
  { beta :=
      (N.betaNumerator : ℚ) / (N.betaDenominator : ℚ)
    delta :=
      (N.deltaNumerator : ℚ) / (N.deltaDenominator : ℚ)
    normalizationScale :=
      (N.scaleNumerator : ℚ) / (N.scaleDenominator : ℚ)
    beta_nonneg := by
      exact div_nonneg (by positivity) (by positivity)
    delta_nonneg := by
      exact div_nonneg (by positivity) (by positivity)
    normalizationScale_nonneg := by
      exact div_nonneg (by positivity) (by positivity)
    parameterTableSourceDerived :=
      N.parameterTableSourceDerived
    parameterTableSourceDerived_proof :=
      N.parameterTableSourceDerived_proof
    noHiddenRootEncodingInParameters :=
      N.noHiddenRootEncodingInParameters
    noHiddenRootEncodingInParameters_proof :=
      N.noHiddenRootEncodingInParameters_proof }

def NeedsThreeFlavorRelatorEvenTowerParameterTable : Prop :=
  Not (exists _T : ThreeFlavorRelatorEvenTowerParameterTable, True)

theorem relatorEvenTowerNumeralParameterTable_discharge_parameterTableNeed
  (N : ThreeFlavorRelatorEvenTowerNumeralParameterTable) :
  Not NeedsThreeFlavorRelatorEvenTowerParameterTable := by
  intro hneed
  exact hneed
    ⟨relatorEvenTowerNumeralParameterTableAsParameterTable N,
      True.intro⟩

def relatorEvenTowerLevelExpression
  (T : ThreeFlavorRelatorEvenTowerParameterTable)
  (k : ℚ) : ℚ :=
  T.normalizationScale * (k ^ 4 * (1 + T.beta * k ^ 2 + T.delta * k ^ 4))

theorem relatorEvenTowerLevelExpression_one
  (T : ThreeFlavorRelatorEvenTowerParameterTable) :
  relatorEvenTowerLevelExpression T 1 =
      T.normalizationScale * (1 + T.beta + T.delta) := by
  simp [relatorEvenTowerLevelExpression]

theorem relatorEvenTowerLevelExpression_three
  (T : ThreeFlavorRelatorEvenTowerParameterTable) :
  relatorEvenTowerLevelExpression T 3 =
      T.normalizationScale * (81 + 729 * T.beta + 6561 * T.delta) := by
  unfold relatorEvenTowerLevelExpression
  ring_nf

theorem relatorEvenTowerLevelExpression_five
  (T : ThreeFlavorRelatorEvenTowerParameterTable) :
  relatorEvenTowerLevelExpression T 5 =
      T.normalizationScale * (625 + 15625 * T.beta + 390625 * T.delta) := by
  unfold relatorEvenTowerLevelExpression
  ring_nf

structure ThreeFlavorRelatorEvenTowerGeneratedLevels
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (T : ThreeFlavorRelatorEvenTowerParameterTable) where
  level0_generated :
    A.massSquaredLevelOf 0 = relatorEvenTowerLevelExpression T 1
  level1_generated :
    A.massSquaredLevelOf 1 = relatorEvenTowerLevelExpression T 3
  level2_generated :
    A.massSquaredLevelOf 2 = relatorEvenTowerLevelExpression T 5
  exponentScheduleFixedBySource : Prop
  exponentScheduleFixedBySource_proof :
    exponentScheduleFixedBySource
  generatedLevelsSameScope : Prop
  generatedLevelsSameScope_proof :
    generatedLevelsSameScope

def relatorEvenTowerFlavorIndex (n : Nat) : ℚ :=
  match n with
  | 0 => 1
  | 1 => 3
  | _ => 5

structure ThreeFlavorRelatorEvenTowerGeneratedLevelFunction
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (T : ThreeFlavorRelatorEvenTowerParameterTable) where
  generatedMassSquaredLevel : Fin 3 -> ℚ
  sourceLevel_readback :
    ∀ i : Fin 3,
      A.massSquaredLevelOf i = generatedMassSquaredLevel i
  generatedLevel_eq_evenTower :
    ∀ i : Fin 3,
      generatedMassSquaredLevel i =
        relatorEvenTowerLevelExpression T (relatorEvenTowerFlavorIndex i.val)
  exponentScheduleFixedBySource : Prop
  exponentScheduleFixedBySource_proof :
    exponentScheduleFixedBySource
  generatedLevelsSameScope : Prop
  generatedLevelsSameScope_proof :
    generatedLevelsSameScope

structure ThreeFlavorRelatorEvenTowerSourceReadback
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (T : ThreeFlavorRelatorEvenTowerParameterTable) where
  sourceLevel_eq_evenTower :
    ∀ i : Fin 3,
      A.massSquaredLevelOf i =
        relatorEvenTowerLevelExpression T (relatorEvenTowerFlavorIndex i.val)
  exponentScheduleFixedBySource : Prop
  exponentScheduleFixedBySource_proof :
    exponentScheduleFixedBySource
  generatedLevelsSameScope : Prop
  generatedLevelsSameScope_proof :
    generatedLevelsSameScope

structure ThreeFlavorRelatorEvenTowerThreePointReadback
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (T : ThreeFlavorRelatorEvenTowerParameterTable) where
  level0_eq_evenTower :
    A.massSquaredLevelOf 0 =
      relatorEvenTowerLevelExpression T 1
  level1_eq_evenTower :
    A.massSquaredLevelOf 1 =
      relatorEvenTowerLevelExpression T 3
  level2_eq_evenTower :
    A.massSquaredLevelOf 2 =
      relatorEvenTowerLevelExpression T 5
  exponentScheduleFixedBySource : Prop
  exponentScheduleFixedBySource_proof :
    exponentScheduleFixedBySource
  generatedLevelsSameScope : Prop
  generatedLevelsSameScope_proof :
    generatedLevelsSameScope

def relatorEvenTowerThreePointReadbackAsSourceReadback
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {T : ThreeFlavorRelatorEvenTowerParameterTable}
  (R : ThreeFlavorRelatorEvenTowerThreePointReadback (A := A) T) :
  ThreeFlavorRelatorEvenTowerSourceReadback (A := A) T :=
  { sourceLevel_eq_evenTower := by
      intro i
      fin_cases i
      · exact R.level0_eq_evenTower
      · exact R.level1_eq_evenTower
      · exact R.level2_eq_evenTower
    exponentScheduleFixedBySource :=
      R.exponentScheduleFixedBySource
    exponentScheduleFixedBySource_proof :=
      R.exponentScheduleFixedBySource_proof
    generatedLevelsSameScope :=
      R.generatedLevelsSameScope
    generatedLevelsSameScope_proof :=
      R.generatedLevelsSameScope_proof }

def relatorEvenTowerSourceReadbackAsGeneratedLevelFunction
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {T : ThreeFlavorRelatorEvenTowerParameterTable}
  (R : ThreeFlavorRelatorEvenTowerSourceReadback (A := A) T) :
  ThreeFlavorRelatorEvenTowerGeneratedLevelFunction (A := A) T :=
  { generatedMassSquaredLevel := fun i =>
      relatorEvenTowerLevelExpression T (relatorEvenTowerFlavorIndex i.val)
    sourceLevel_readback := by
      intro i
      exact R.sourceLevel_eq_evenTower i
    generatedLevel_eq_evenTower := by
      intro i
      rfl
    exponentScheduleFixedBySource :=
      R.exponentScheduleFixedBySource
    exponentScheduleFixedBySource_proof :=
      R.exponentScheduleFixedBySource_proof
    generatedLevelsSameScope :=
      R.generatedLevelsSameScope
    generatedLevelsSameScope_proof :=
      R.generatedLevelsSameScope_proof }

def relatorEvenTowerGeneratedLevelFunctionAsGeneratedLevels
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {T : ThreeFlavorRelatorEvenTowerParameterTable}
  (F : ThreeFlavorRelatorEvenTowerGeneratedLevelFunction (A := A) T) :
  ThreeFlavorRelatorEvenTowerGeneratedLevels (A := A) T :=
  { level0_generated := by
      calc
        A.massSquaredLevelOf 0 = F.generatedMassSquaredLevel 0 :=
          F.sourceLevel_readback 0
        _ = relatorEvenTowerLevelExpression T
              (relatorEvenTowerFlavorIndex (0 : Fin 3).val) :=
          F.generatedLevel_eq_evenTower 0
        _ = relatorEvenTowerLevelExpression T 1 := by
          rfl
    level1_generated := by
      calc
        A.massSquaredLevelOf 1 = F.generatedMassSquaredLevel 1 :=
          F.sourceLevel_readback 1
        _ = relatorEvenTowerLevelExpression T
              (relatorEvenTowerFlavorIndex (1 : Fin 3).val) :=
          F.generatedLevel_eq_evenTower 1
        _ = relatorEvenTowerLevelExpression T 3 := by
          rfl
    level2_generated := by
      calc
        A.massSquaredLevelOf 2 = F.generatedMassSquaredLevel 2 :=
          F.sourceLevel_readback 2
        _ = relatorEvenTowerLevelExpression T
              (relatorEvenTowerFlavorIndex (2 : Fin 3).val) :=
          F.generatedLevel_eq_evenTower 2
        _ = relatorEvenTowerLevelExpression T 5 := by
          rfl
    exponentScheduleFixedBySource :=
      F.exponentScheduleFixedBySource
    exponentScheduleFixedBySource_proof :=
      F.exponentScheduleFixedBySource_proof
    generatedLevelsSameScope :=
      F.generatedLevelsSameScope
    generatedLevelsSameScope_proof :=
      F.generatedLevelsSameScope_proof }

structure ThreeFlavorRelatorEvenTowerLevelIdentification
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (T : ThreeFlavorRelatorEvenTowerParameterTable) where
  level0_eq :
    A.massSquaredLevelOf 0 =
      T.normalizationScale * (1 + T.beta + T.delta)
  level1_eq :
    A.massSquaredLevelOf 1 =
      T.normalizationScale * (81 + 729 * T.beta + 6561 * T.delta)
  level2_eq :
    A.massSquaredLevelOf 2 =
      T.normalizationScale * (625 + 15625 * T.beta + 390625 * T.delta)
  exponentScheduleFixedBySource : Prop
  exponentScheduleFixedBySource_proof :
    exponentScheduleFixedBySource
  levelIdentificationSameScope : Prop
  levelIdentificationSameScope_proof :
    levelIdentificationSameScope

def relatorEvenTowerGeneratedLevelsAsLevelIdentification
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {T : ThreeFlavorRelatorEvenTowerParameterTable}
  (G : ThreeFlavorRelatorEvenTowerGeneratedLevels (A := A) T) :
  ThreeFlavorRelatorEvenTowerLevelIdentification (A := A) T :=
  { level0_eq := by
      rw [G.level0_generated, relatorEvenTowerLevelExpression_one]
    level1_eq := by
      rw [G.level1_generated, relatorEvenTowerLevelExpression_three]
    level2_eq := by
      rw [G.level2_generated, relatorEvenTowerLevelExpression_five]
    exponentScheduleFixedBySource :=
      G.exponentScheduleFixedBySource
    exponentScheduleFixedBySource_proof :=
      G.exponentScheduleFixedBySource_proof
    levelIdentificationSameScope :=
      G.generatedLevelsSameScope
    levelIdentificationSameScope_proof :=
      G.generatedLevelsSameScope_proof }

structure ThreeFlavorRelatorEvenTowerAudit where
  noEmpiricalRelatorEvenTowerImport : Prop
  noEmpiricalRelatorEvenTowerImport_proof :
    noEmpiricalRelatorEvenTowerImport
  noRelatorEvenTowerFitTuning : Prop
  noRelatorEvenTowerFitTuning_proof :
    noRelatorEvenTowerFitTuning

def relatorEvenTowerComponentsAsSourceCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (T : ThreeFlavorRelatorEvenTowerParameterTable)
  (L : ThreeFlavorRelatorEvenTowerLevelIdentification (A := A) T)
  (Q : ThreeFlavorRelatorEvenTowerAudit) :
  ThreeFlavorRelatorEvenTowerSourceCertificate (A := A) :=
  { gapRatioAlgebraPasses := hA
    beta := T.beta
    delta := T.delta
    normalizationScale := T.normalizationScale
    beta_nonneg := T.beta_nonneg
    delta_nonneg := T.delta_nonneg
    normalizationScale_nonneg := T.normalizationScale_nonneg
    level0_eq := L.level0_eq
    level1_eq := L.level1_eq
    level2_eq := L.level2_eq
    relatorParameterTableSourceDerived :=
      T.parameterTableSourceDerived
    relatorParameterTableSourceDerived_proof :=
      T.parameterTableSourceDerived_proof
    relatorExponentScheduleFixedBySource :=
      L.exponentScheduleFixedBySource
    relatorExponentScheduleFixedBySource_proof :=
      L.exponentScheduleFixedBySource_proof
    relatorEvenTowerSameScopeAsMassSquaredLevels :=
      L.levelIdentificationSameScope
    relatorEvenTowerSameScopeAsMassSquaredLevels_proof :=
      L.levelIdentificationSameScope_proof
    noEmpiricalRelatorEvenTowerImport :=
      Q.noEmpiricalRelatorEvenTowerImport
    noEmpiricalRelatorEvenTowerImport_proof :=
      Q.noEmpiricalRelatorEvenTowerImport_proof
    noRelatorEvenTowerFitTuning :=
      Q.noRelatorEvenTowerFitTuning
    noRelatorEvenTowerFitTuning_proof :=
      Q.noRelatorEvenTowerFitTuning_proof
    noHiddenRootEncodingInRelatorParameters :=
      T.noHiddenRootEncodingInParameters
    noHiddenRootEncodingInRelatorParameters_proof :=
      T.noHiddenRootEncodingInParameters_proof }

def NeedsThreeFlavorRelatorEvenTowerSourceCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ) : Prop :=
  Not (exists _S : ThreeFlavorRelatorEvenTowerSourceCertificate (A := A), True)

theorem relatorEvenTowerComponents_discharge_sourceCertificateNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (T : ThreeFlavorRelatorEvenTowerParameterTable)
  (L : ThreeFlavorRelatorEvenTowerLevelIdentification (A := A) T)
  (Q : ThreeFlavorRelatorEvenTowerAudit) :
  Not (NeedsThreeFlavorRelatorEvenTowerSourceCertificate A) := by
  intro hneed
  exact hneed
    ⟨relatorEvenTowerComponentsAsSourceCertificate hA T L Q,
      True.intro⟩

/--
Relator even-tower mass-squared law.

This is the algebraic shape suggested by the Relator neutrino hierarchy source:
after absorbing the common denominator/scale into `normalizationScale`, the
three ordered mass-squared levels at `k = 1, 3, 5` are governed by the positive
even tower `k^4 * (1 + β k^2 + δ k^4)`.
-/
structure ThreeFlavorRelatorEvenTowerMassSquaredLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  beta : ℚ
  delta : ℚ
  normalizationScale : ℚ
  beta_nonneg :
    0 <= beta
  delta_nonneg :
    0 <= delta
  normalizationScale_nonneg :
    0 <= normalizationScale
  level0_eq :
    A.massSquaredLevelOf 0 =
      normalizationScale * (1 + beta + delta)
  level1_eq :
    A.massSquaredLevelOf 1 =
      normalizationScale * (81 + 729 * beta + 6561 * delta)
  level2_eq :
    A.massSquaredLevelOf 2 =
      normalizationScale * (625 + 15625 * beta + 390625 * delta)
  relatorEvenTowerTranslatedToAASC : Prop
  relatorEvenTowerTranslatedToAASC_proof :
    relatorEvenTowerTranslatedToAASC
  relatorEvenTowerSameScopeAsMassSquaredLevels : Prop
  relatorEvenTowerSameScopeAsMassSquaredLevels_proof :
    relatorEvenTowerSameScopeAsMassSquaredLevels
  noEmpiricalRelatorEvenTowerImport : Prop
  noEmpiricalRelatorEvenTowerImport_proof :
    noEmpiricalRelatorEvenTowerImport
  noRelatorEvenTowerFitTuning : Prop
  noRelatorEvenTowerFitTuning_proof :
    noRelatorEvenTowerFitTuning

def relatorEvenTowerSourceCertificateAsMassSquaredLaw
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (S : ThreeFlavorRelatorEvenTowerSourceCertificate (A := A)) :
  ThreeFlavorRelatorEvenTowerMassSquaredLaw (A := A) :=
  { gapRatioAlgebraPasses := S.gapRatioAlgebraPasses
    beta := S.beta
    delta := S.delta
    normalizationScale := S.normalizationScale
    beta_nonneg := S.beta_nonneg
    delta_nonneg := S.delta_nonneg
    normalizationScale_nonneg := S.normalizationScale_nonneg
    level0_eq := S.level0_eq
    level1_eq := S.level1_eq
    level2_eq := S.level2_eq
    relatorEvenTowerTranslatedToAASC :=
      S.relatorParameterTableSourceDerived /\
        S.relatorExponentScheduleFixedBySource /\
          S.noHiddenRootEncodingInRelatorParameters
    relatorEvenTowerTranslatedToAASC_proof :=
      ⟨S.relatorParameterTableSourceDerived_proof,
        S.relatorExponentScheduleFixedBySource_proof,
        S.noHiddenRootEncodingInRelatorParameters_proof⟩
    relatorEvenTowerSameScopeAsMassSquaredLevels :=
      S.relatorEvenTowerSameScopeAsMassSquaredLevels
    relatorEvenTowerSameScopeAsMassSquaredLevels_proof :=
      S.relatorEvenTowerSameScopeAsMassSquaredLevels_proof
    noEmpiricalRelatorEvenTowerImport :=
      S.noEmpiricalRelatorEvenTowerImport
    noEmpiricalRelatorEvenTowerImport_proof :=
      S.noEmpiricalRelatorEvenTowerImport_proof
    noRelatorEvenTowerFitTuning :=
      S.noRelatorEvenTowerFitTuning /\
        S.noHiddenRootEncodingInRelatorParameters
    noRelatorEvenTowerFitTuning_proof :=
      ⟨S.noRelatorEvenTowerFitTuning_proof,
        S.noHiddenRootEncodingInRelatorParameters_proof⟩ }

def relatorEvenTowerMassSquaredLawAsConvexity
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (L : ThreeFlavorRelatorEvenTowerMassSquaredLaw (A := A)) :
  ThreeFlavorMassSquaredConvexity (A := A) :=
  { gapRatioAlgebraPasses := L.gapRatioAlgebraPasses
    secondFiniteDifference_nonneg := by
      rw [L.level0_eq, L.level1_eq, L.level2_eq]
      ring_nf
      have hsb : 0 <= L.normalizationScale * L.beta :=
        mul_nonneg L.normalizationScale_nonneg L.beta_nonneg
      have hsd : 0 <= L.normalizationScale * L.delta :=
        mul_nonneg L.normalizationScale_nonneg L.delta_nonneg
      nlinarith [L.normalizationScale_nonneg, hsb, hsd]
    convexityLawDerivedInternally :=
      L.relatorEvenTowerTranslatedToAASC /\
        L.relatorEvenTowerSameScopeAsMassSquaredLevels
    convexityLawDerivedInternally_proof :=
      ⟨L.relatorEvenTowerTranslatedToAASC_proof,
        L.relatorEvenTowerSameScopeAsMassSquaredLevels_proof⟩
    noEmpiricalConvexityImport :=
      L.noEmpiricalRelatorEvenTowerImport
    noEmpiricalConvexityImport_proof :=
      L.noEmpiricalRelatorEvenTowerImport_proof
    noConvexityFitTuning :=
      L.noRelatorEvenTowerFitTuning
    noConvexityFitTuning_proof :=
      L.noRelatorEvenTowerFitTuning_proof }

def sourceCurvatureSquareWitnessAsFiniteCoordinateTable
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (S : ThreeFlavorSourceCurvatureSquareWitness (A := A)) :
  ThreeFlavorSourceCurvatureFiniteCoordinateTable (A := A) :=
  { gapRatioAlgebraPasses := S.gapRatioAlgebraPasses
    coordinateCount := 1
    coordinateAt := fun _ => S.curvatureCoordinate
    coordinateSquareSum_eq_secondFiniteDifference := by
      simp [S.curvatureCoordinateSquared_eq_secondFiniteDifference]
    coordinateTableConstructedInternally :=
      S.curvatureCoordinateDerivedInternally
    coordinateTableConstructedInternally_proof :=
      S.curvatureCoordinateDerivedInternally_proof
    coordinateTableSameScopeAsMassSquaredLevels :=
      S.curvatureCoordinateSameScopeAsMassSquaredLevels
    coordinateTableSameScopeAsMassSquaredLevels_proof :=
      S.curvatureCoordinateSameScopeAsMassSquaredLevels_proof
    coordinateTablePSDSourceCertified :=
      S.curvatureCoordinateDerivedInternally
    coordinateTablePSDSourceCertified_proof :=
      S.curvatureCoordinateDerivedInternally_proof
    noEmpiricalCoordinateTableImport :=
      S.noEmpiricalCurvatureCoordinateImport
    noEmpiricalCoordinateTableImport_proof :=
      S.noEmpiricalCurvatureCoordinateImport_proof
    noCoordinateTableFitTuning :=
      S.noCurvatureCoordinateFitTuning
    noCoordinateTableFitTuning_proof :=
      S.noCurvatureCoordinateFitTuning_proof }

def NeedsThreeFlavorSourceCurvatureFiniteCoordinateTable
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ) : Prop :=
  Not (exists _T :
    ThreeFlavorSourceCurvatureFiniteCoordinateTable (A := A), True)

theorem sourceCurvatureSquareWitness_discharge_finiteCoordinateTableNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (S : ThreeFlavorSourceCurvatureSquareWitness (A := A)) :
  Not (NeedsThreeFlavorSourceCurvatureFiniteCoordinateTable A) := by
  intro hneed
  exact hneed
    ⟨sourceCurvatureSquareWitnessAsFiniteCoordinateTable S, True.intro⟩

def sourceCurvatureFiniteTableAsGramDiagonalWitness
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (T : ThreeFlavorSourceCurvatureFiniteCoordinateTable (A := A)) :
  ThreeFlavorSourceCurvatureGramDiagonalWitness (A := A) :=
  { gapRatioAlgebraPasses := T.gapRatioAlgebraPasses
    Index := Fin T.coordinateCount
    finiteIndex := inferInstance
    gramDiagonalCoordinate := T.coordinateAt
    gramDiagonalSquareSum_eq_secondFiniteDifference :=
      T.coordinateSquareSum_eq_secondFiniteDifference
    gramDiagonalConstructedInternally :=
      T.coordinateTableConstructedInternally
    gramDiagonalConstructedInternally_proof :=
      T.coordinateTableConstructedInternally_proof
    gramDiagonalSameScopeAsMassSquaredLevels :=
      T.coordinateTableSameScopeAsMassSquaredLevels
    gramDiagonalSameScopeAsMassSquaredLevels_proof :=
      T.coordinateTableSameScopeAsMassSquaredLevels_proof
    gramDiagonalPSDSourceCertified :=
      T.coordinateTablePSDSourceCertified
    gramDiagonalPSDSourceCertified_proof :=
      T.coordinateTablePSDSourceCertified_proof
    noEmpiricalGramImport :=
      T.noEmpiricalCoordinateTableImport
    noEmpiricalGramImport_proof :=
      T.noEmpiricalCoordinateTableImport_proof
    noGramFitTuning :=
      T.noCoordinateTableFitTuning
    noGramFitTuning_proof :=
      T.noCoordinateTableFitTuning_proof }

def NeedsThreeFlavorSourceCurvatureGramDiagonalWitness
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ) : Prop :=
  Not (exists _G : ThreeFlavorSourceCurvatureGramDiagonalWitness (A := A), True)

theorem sourceCurvatureFiniteTable_discharge_gramDiagonalNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (T : ThreeFlavorSourceCurvatureFiniteCoordinateTable (A := A)) :
  Not (NeedsThreeFlavorSourceCurvatureGramDiagonalWitness A) := by
  intro hneed
  exact hneed
    ⟨sourceCurvatureFiniteTableAsGramDiagonalWitness T, True.intro⟩

def sourceCurvatureGramDiagonalAsSumSquaresWitness
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (G : ThreeFlavorSourceCurvatureGramDiagonalWitness (A := A)) :
  ThreeFlavorSourceCurvatureSumSquaresWitness (A := A) :=
  { gapRatioAlgebraPasses := G.gapRatioAlgebraPasses
    Index := G.Index
    finiteIndex := G.finiteIndex
    curvatureCoordinate := G.gramDiagonalCoordinate
    curvatureSumSquares_eq_secondFiniteDifference :=
      G.gramDiagonalSquareSum_eq_secondFiniteDifference
    curvatureCoordinatesDerivedInternally :=
      G.gramDiagonalConstructedInternally /\
        G.gramDiagonalPSDSourceCertified
    curvatureCoordinatesDerivedInternally_proof :=
      ⟨G.gramDiagonalConstructedInternally_proof,
        G.gramDiagonalPSDSourceCertified_proof⟩
    curvatureCoordinatesSameScopeAsMassSquaredLevels :=
      G.gramDiagonalSameScopeAsMassSquaredLevels
    curvatureCoordinatesSameScopeAsMassSquaredLevels_proof :=
      G.gramDiagonalSameScopeAsMassSquaredLevels_proof
    noEmpiricalCurvatureCoordinatesImport :=
      G.noEmpiricalGramImport
    noEmpiricalCurvatureCoordinatesImport_proof :=
      G.noEmpiricalGramImport_proof
    noCurvatureCoordinatesFitTuning :=
      G.noGramFitTuning
    noCurvatureCoordinatesFitTuning_proof :=
      G.noGramFitTuning_proof }

def NeedsThreeFlavorSourceCurvatureSumSquaresWitness
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ) : Prop :=
  Not (exists _S : ThreeFlavorSourceCurvatureSumSquaresWitness (A := A), True)

theorem sourceCurvatureGramDiagonal_discharge_sumSquaresNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (G : ThreeFlavorSourceCurvatureGramDiagonalWitness (A := A)) :
  Not (NeedsThreeFlavorSourceCurvatureSumSquaresWitness A) := by
  intro hneed
  exact hneed
    ⟨sourceCurvatureGramDiagonalAsSumSquaresWitness G, True.intro⟩

def sourceCurvatureSumSquaresWitnessAsCurvatureNonnegative
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (S : ThreeFlavorSourceCurvatureSumSquaresWitness (A := A)) :
  ThreeFlavorSourceCurvatureNonnegative (A := A) :=
  { gapRatioAlgebraPasses := S.gapRatioAlgebraPasses
    curvature :=
      (@Finset.univ S.Index S.finiteIndex).sum
        (fun i => S.curvatureCoordinate i ^ 2)
    curvature_eq_secondFiniteDifference :=
      S.curvatureSumSquares_eq_secondFiniteDifference
    curvature_nonneg := by
      classical
      exact Finset.sum_nonneg
        (fun i _hi => sq_nonneg (S.curvatureCoordinate i))
    curvatureDerivedInternally :=
      S.curvatureCoordinatesDerivedInternally
    curvatureDerivedInternally_proof :=
      S.curvatureCoordinatesDerivedInternally_proof
    curvatureSameScopeAsMassSquaredLevels :=
      S.curvatureCoordinatesSameScopeAsMassSquaredLevels
    curvatureSameScopeAsMassSquaredLevels_proof :=
      S.curvatureCoordinatesSameScopeAsMassSquaredLevels_proof
    noEmpiricalCurvatureImport :=
      S.noEmpiricalCurvatureCoordinatesImport
    noEmpiricalCurvatureImport_proof :=
      S.noEmpiricalCurvatureCoordinatesImport_proof
    noCurvatureFitTuning :=
      S.noCurvatureCoordinatesFitTuning
    noCurvatureFitTuning_proof :=
      S.noCurvatureCoordinatesFitTuning_proof }

def NeedsThreeFlavorSourceCurvatureNonnegative
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ) : Prop :=
  Not (exists _K : ThreeFlavorSourceCurvatureNonnegative (A := A), True)

theorem sourceCurvatureSumSquaresWitness_discharge_curvatureNonnegativeNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (S : ThreeFlavorSourceCurvatureSumSquaresWitness (A := A)) :
  Not (NeedsThreeFlavorSourceCurvatureNonnegative A) := by
  intro hneed
  exact hneed
    ⟨sourceCurvatureSumSquaresWitnessAsCurvatureNonnegative S, True.intro⟩

def sourceCurvatureSquareWitnessAsCurvatureNonnegative
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (S : ThreeFlavorSourceCurvatureSquareWitness (A := A)) :
  ThreeFlavorSourceCurvatureNonnegative (A := A) :=
  { gapRatioAlgebraPasses := S.gapRatioAlgebraPasses
    curvature := S.curvatureCoordinate ^ 2
    curvature_eq_secondFiniteDifference :=
      S.curvatureCoordinateSquared_eq_secondFiniteDifference
    curvature_nonneg := by
      nlinarith [sq_nonneg S.curvatureCoordinate]
    curvatureDerivedInternally :=
      S.curvatureCoordinateDerivedInternally
    curvatureDerivedInternally_proof :=
      S.curvatureCoordinateDerivedInternally_proof
    curvatureSameScopeAsMassSquaredLevels :=
      S.curvatureCoordinateSameScopeAsMassSquaredLevels
    curvatureSameScopeAsMassSquaredLevels_proof :=
      S.curvatureCoordinateSameScopeAsMassSquaredLevels_proof
    noEmpiricalCurvatureImport :=
      S.noEmpiricalCurvatureCoordinateImport
    noEmpiricalCurvatureImport_proof :=
      S.noEmpiricalCurvatureCoordinateImport_proof
    noCurvatureFitTuning :=
      S.noCurvatureCoordinateFitTuning
    noCurvatureFitTuning_proof :=
      S.noCurvatureCoordinateFitTuning_proof }

theorem sourceCurvatureSquareWitness_discharge_curvatureNonnegativeNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (S : ThreeFlavorSourceCurvatureSquareWitness (A := A)) :
  Not (NeedsThreeFlavorSourceCurvatureNonnegative A) := by
  intro hneed
  exact hneed
    ⟨sourceCurvatureSquareWitnessAsCurvatureNonnegative S, True.intro⟩

def sourceCurvatureNonnegativeAsMassSquaredConvexity
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (K : ThreeFlavorSourceCurvatureNonnegative (A := A)) :
  ThreeFlavorMassSquaredConvexity (A := A) :=
  { gapRatioAlgebraPasses := K.gapRatioAlgebraPasses
    secondFiniteDifference_nonneg := by
      rw [← K.curvature_eq_secondFiniteDifference]
      exact K.curvature_nonneg
    convexityLawDerivedInternally :=
      K.curvatureDerivedInternally /\
        K.curvatureSameScopeAsMassSquaredLevels
    convexityLawDerivedInternally_proof :=
      ⟨K.curvatureDerivedInternally_proof,
        K.curvatureSameScopeAsMassSquaredLevels_proof⟩
    noEmpiricalConvexityImport :=
      K.noEmpiricalCurvatureImport
    noEmpiricalConvexityImport_proof :=
      K.noEmpiricalCurvatureImport_proof
    noConvexityFitTuning :=
      K.noCurvatureFitTuning
    noConvexityFitTuning_proof :=
      K.noCurvatureFitTuning_proof }

def NeedsThreeFlavorMassSquaredConvexity
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ) : Prop :=
  Not (exists _V : ThreeFlavorMassSquaredConvexity (A := A), True)

theorem sourceCurvatureNonnegative_discharge_massSquaredConvexityNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (K : ThreeFlavorSourceCurvatureNonnegative (A := A)) :
  Not (NeedsThreeFlavorMassSquaredConvexity A) := by
  intro hneed
  exact hneed
    ⟨sourceCurvatureNonnegativeAsMassSquaredConvexity K, True.intro⟩

theorem relatorEvenTowerMassSquaredLaw_discharge_massSquaredConvexityNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (L : ThreeFlavorRelatorEvenTowerMassSquaredLaw (A := A)) :
  Not (NeedsThreeFlavorMassSquaredConvexity A) := by
  intro hneed
  exact hneed
    ⟨relatorEvenTowerMassSquaredLawAsConvexity L, True.intro⟩

def massSquaredConvexityAsTwoStepGapHalfDominance
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (V : ThreeFlavorMassSquaredConvexity (A := A)) :
  ThreeFlavorTwoStepGapHalfDominance (A := A) :=
  { gapRatioAlgebraPasses := V.gapRatioAlgebraPasses
    twiceLowerGap_le_totalGap := by
      linarith [V.secondFiniteDifference_nonneg]
    twoStepGapLawDerivedInternally :=
      V.convexityLawDerivedInternally
    twoStepGapLawDerivedInternally_proof :=
      V.convexityLawDerivedInternally_proof
    noEmpiricalTwoStepGapImport :=
      V.noEmpiricalConvexityImport
    noEmpiricalTwoStepGapImport_proof :=
      V.noEmpiricalConvexityImport_proof
    noTwoStepGapFitTuning :=
      V.noConvexityFitTuning
    noTwoStepGapFitTuning_proof :=
      V.noConvexityFitTuning_proof }

def NeedsThreeFlavorTwoStepGapHalfDominance
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ) : Prop :=
  Not (exists _T : ThreeFlavorTwoStepGapHalfDominance (A := A), True)

theorem massSquaredConvexity_discharge_twoStepGapHalfDominanceNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (V : ThreeFlavorMassSquaredConvexity (A := A)) :
  Not (NeedsThreeFlavorTwoStepGapHalfDominance A) := by
  intro hneed
  exact hneed
    ⟨massSquaredConvexityAsTwoStepGapHalfDominance V, True.intro⟩

def twoStepGapHalfDominanceAsAdjacentGapHalfSide
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (T : ThreeFlavorTwoStepGapHalfDominance (A := A)) :
  ThreeFlavorAdjacentGapHalfSide (A := A) :=
  { gapRatioAlgebraPasses := T.gapRatioAlgebraPasses
    lowerAdjacentGap_le_upperAdjacentGap := by
      linarith [T.twiceLowerGap_le_totalGap]
    adjacentGapLawDerivedInternally :=
      T.twoStepGapLawDerivedInternally
    adjacentGapLawDerivedInternally_proof :=
      T.twoStepGapLawDerivedInternally_proof
    noEmpiricalAdjacentGapImport :=
      T.noEmpiricalTwoStepGapImport
    noEmpiricalAdjacentGapImport_proof :=
      T.noEmpiricalTwoStepGapImport_proof
    noAdjacentGapFitTuning :=
      T.noTwoStepGapFitTuning
    noAdjacentGapFitTuning_proof :=
      T.noTwoStepGapFitTuning_proof }

def NeedsThreeFlavorAdjacentGapHalfSide
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ) : Prop :=
  Not (exists _S : ThreeFlavorAdjacentGapHalfSide (A := A), True)

theorem twoStepGapHalfDominance_discharge_adjacentGapHalfSideNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (T : ThreeFlavorTwoStepGapHalfDominance (A := A)) :
  Not (NeedsThreeFlavorAdjacentGapHalfSide A) := by
  intro hneed
  exact hneed
    ⟨twoStepGapHalfDominanceAsAdjacentGapHalfSide T, True.intro⟩

def adjacentGapHalfSideAsMidpointGapCompression
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (S : ThreeFlavorAdjacentGapHalfSide (A := A)) :
  ThreeFlavorMidpointGapCompression (A := A) :=
  { gapRatioAlgebraPasses := S.gapRatioAlgebraPasses
    midpointCompression := by
      linarith [S.lowerAdjacentGap_le_upperAdjacentGap]
    midpointCompressionDerivedInternally :=
      S.adjacentGapLawDerivedInternally
    midpointCompressionDerivedInternally_proof :=
      S.adjacentGapLawDerivedInternally_proof
    noEmpiricalMidpointImport :=
      S.noEmpiricalAdjacentGapImport
    noEmpiricalMidpointImport_proof :=
      S.noEmpiricalAdjacentGapImport_proof
    noMidpointFitTuning :=
      S.noAdjacentGapFitTuning
    noMidpointFitTuning_proof :=
      S.noAdjacentGapFitTuning_proof }

def NeedsThreeFlavorMidpointGapCompression
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ) : Prop :=
  Not (exists _K : ThreeFlavorMidpointGapCompression (A := A), True)

theorem adjacentGapHalfSide_discharge_midpointCompressionNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (S : ThreeFlavorAdjacentGapHalfSide (A := A)) :
  Not (NeedsThreeFlavorMidpointGapCompression A) := by
  intro hneed
  exact hneed
    ⟨adjacentGapHalfSideAsMidpointGapCompression S, True.intro⟩

theorem midpointGapCompression_solarGap_le_half_atmosphericGap
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (K : ThreeFlavorMidpointGapCompression (A := A)) :
  threeFlavorSolarGap A.massSquaredLevelOf <=
      (1 / 2 : ℚ) * threeFlavorAtmosphericGap A.massSquaredLevelOf := by
  unfold threeFlavorSolarGap threeFlavorAtmosphericGap
  linarith [K.midpointCompression]

def midpointGapCompressionAsHalfDominanceUpperBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (K : ThreeFlavorMidpointGapCompression (A := A)) :
  ThreeFlavorGapDominanceNumeralUpperBound (A := A) :=
  { gapRatioAlgebraPasses := K.gapRatioAlgebraPasses
    upper := 1 / 2
    upperNumerator := 1
    upperDenominator := 2
    upperDenominator_pos := by norm_num
    upper_eq_numeral := by norm_num
    upper_pos := by norm_num
    upper_lt_one := by norm_num
    solarGap_le_upper_mul_atmosphericGap :=
      midpointGapCompression_solarGap_le_half_atmosphericGap K
    dominanceDerivedInternally := K.midpointCompressionDerivedInternally
    dominanceDerivedInternally_proof :=
      K.midpointCompressionDerivedInternally_proof
    noEmpiricalDominanceImport := K.noEmpiricalMidpointImport
    noEmpiricalDominanceImport_proof :=
      K.noEmpiricalMidpointImport_proof
    noDominanceFitTuning := K.noMidpointFitTuning
    noDominanceFitTuning_proof :=
      K.noMidpointFitTuning_proof }

def midpointGapCompressionAsHalfInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (K : ThreeFlavorMidpointGapCompression (A := A)) :
  ThreeFlavorNumeralRationalClosedRootInterval
    (sameScopePackageAsAlgebraicClosedRootPresentation
      ℚ
      A
      (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
        ℚ
        A
        hA
        J
        hsingle)) :=
  gapDominanceNumeralUpperBoundAsInterval
    A
    hA
    J
    hsingle
    O
    (midpointGapCompressionAsHalfDominanceUpperBound K)

theorem midpointGapCompression_halfInterval_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (K : ThreeFlavorMidpointGapCompression (A := A)) :
  (midpointGapCompressionAsHalfInterval
      A
      hA
      J
      hsingle
      O
      K).lower <= threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (midpointGapCompressionAsHalfInterval
        A
        hA
        J
        hsingle
        O
        K).upper :=
  gapDominanceNumeralUpperBound_interval_contains_gapRatio
    A
    hA
    J
    hsingle
    O
    (midpointGapCompressionAsHalfDominanceUpperBound K)

theorem midpointGapCompression_halfInterval_upper_eq_half
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (K : ThreeFlavorMidpointGapCompression (A := A)) :
  (midpointGapCompressionAsHalfInterval
      A
      hA
      J
      hsingle
      O
      K).upper = (1 / 2 : ℚ) := by
  rfl

def midpointGapCompressionAsHalfDecimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (K : ThreeFlavorMidpointGapCompression (A := A))
  (decimalLabel : String)
  (decimalLabelCertifiedByInterval : Prop)
  (hlabel : decimalLabelCertifiedByInterval) :
  ThreeFlavorClosedRootDecimalWindow
    ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation
      ℚ
      A
      (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
        ℚ
        A
        hA
        J
        hsingle)) :=
  gapDominanceNumeralUpperBoundAsDecimalWindow
    A
    hA
    J
    hsingle
    O
    (midpointGapCompressionAsHalfDominanceUpperBound K)
    decimalLabel
    decimalLabelCertifiedByInterval
    hlabel

/--
Canonical normalized-middle half compression.

After the canonical affine normalization, the middle coordinate is exactly the
gap quotient.  This object is therefore the source-facing form of the
half-window target: prove the normalized middle coordinate is at most `1/2`.
-/
structure ThreeFlavorNormalizedMiddleHalfCompression
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  normalizedMiddle_le_half :
    threeFlavorGapRatio A.massSquaredLevelOf <= (1 / 2 : ℚ)
  normalizedMiddleLawDerivedInternally : Prop
  normalizedMiddleLawDerivedInternally_proof :
    normalizedMiddleLawDerivedInternally
  noEmpiricalMiddleCoordinateImport : Prop
  noEmpiricalMiddleCoordinateImport_proof :
    noEmpiricalMiddleCoordinateImport
  noMiddleCoordinateFitTuning : Prop
  noMiddleCoordinateFitTuning_proof :
    noMiddleCoordinateFitTuning

def midpointGapCompressionAsNormalizedMiddleHalfCompression
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (K : ThreeFlavorMidpointGapCompression (A := A)) :
  ThreeFlavorNormalizedMiddleHalfCompression (A := A) :=
  { gapRatioAlgebraPasses := K.gapRatioAlgebraPasses
    normalizedMiddle_le_half := by
      have hden_pos :
          0 < threeFlavorAtmosphericGap A.massSquaredLevelOf := by
        unfold threeFlavorAtmosphericGap
        linarith [O.level0_lt_level1, O.level1_lt_level2]
      have hgap :
          threeFlavorSolarGap A.massSquaredLevelOf <=
            (1 / 2 : ℚ) *
              threeFlavorAtmosphericGap A.massSquaredLevelOf :=
        midpointGapCompression_solarGap_le_half_atmosphericGap K
      unfold threeFlavorGapRatio
      exact (div_le_iff₀ hden_pos).mpr hgap
    normalizedMiddleLawDerivedInternally :=
      K.midpointCompressionDerivedInternally
    normalizedMiddleLawDerivedInternally_proof :=
      K.midpointCompressionDerivedInternally_proof
    noEmpiricalMiddleCoordinateImport :=
      K.noEmpiricalMidpointImport
    noEmpiricalMiddleCoordinateImport_proof :=
      K.noEmpiricalMidpointImport_proof
    noMiddleCoordinateFitTuning :=
      K.noMidpointFitTuning
    noMiddleCoordinateFitTuning_proof :=
      K.noMidpointFitTuning_proof }

def NeedsThreeFlavorNormalizedMiddleHalfCompression
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ) : Prop :=
  Not (exists _K :
    ThreeFlavorNormalizedMiddleHalfCompression (A := A), True)

theorem midpointGapCompression_discharge_normalizedMiddleHalfNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (K : ThreeFlavorMidpointGapCompression (A := A)) :
  Not (NeedsThreeFlavorNormalizedMiddleHalfCompression A) := by
  intro hneed
  exact hneed
    ⟨midpointGapCompressionAsNormalizedMiddleHalfCompression O K,
      True.intro⟩

theorem normalizedMiddleHalfCompression_solarGap_le_half_atmosphericGap
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (K : ThreeFlavorNormalizedMiddleHalfCompression (A := A))
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A)) :
  threeFlavorSolarGap A.massSquaredLevelOf <=
      (1 / 2 : ℚ) * threeFlavorAtmosphericGap A.massSquaredLevelOf := by
  have hden_pos :
      0 < threeFlavorAtmosphericGap A.massSquaredLevelOf := by
    unfold threeFlavorAtmosphericGap
    linarith [O.level0_lt_level1, O.level1_lt_level2]
  have hmiddle := K.normalizedMiddle_le_half
  unfold threeFlavorGapRatio at hmiddle
  exact
    (div_le_iff₀ hden_pos).mp hmiddle

def normalizedMiddleHalfCompressionAsHalfDominanceUpperBound
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (K : ThreeFlavorNormalizedMiddleHalfCompression (A := A))
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A)) :
  ThreeFlavorGapDominanceNumeralUpperBound (A := A) :=
  { gapRatioAlgebraPasses := K.gapRatioAlgebraPasses
    upper := 1 / 2
    upperNumerator := 1
    upperDenominator := 2
    upperDenominator_pos := by norm_num
    upper_eq_numeral := by norm_num
    upper_pos := by norm_num
    upper_lt_one := by norm_num
    solarGap_le_upper_mul_atmosphericGap :=
      normalizedMiddleHalfCompression_solarGap_le_half_atmosphericGap K O
    dominanceDerivedInternally :=
      K.normalizedMiddleLawDerivedInternally
    dominanceDerivedInternally_proof :=
      K.normalizedMiddleLawDerivedInternally_proof
    noEmpiricalDominanceImport :=
      K.noEmpiricalMiddleCoordinateImport
    noEmpiricalDominanceImport_proof :=
      K.noEmpiricalMiddleCoordinateImport_proof
    noDominanceFitTuning :=
      K.noMiddleCoordinateFitTuning
    noDominanceFitTuning_proof :=
      K.noMiddleCoordinateFitTuning_proof }

def normalizedMiddleHalfCompressionAsHalfInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (K : ThreeFlavorNormalizedMiddleHalfCompression (A := A)) :
  ThreeFlavorNumeralRationalClosedRootInterval
    (sameScopePackageAsAlgebraicClosedRootPresentation
      ℚ
      A
      (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
        ℚ
        A
        hA
        J
        hsingle)) :=
  gapDominanceNumeralUpperBoundAsInterval
    A
    hA
    J
    hsingle
    O
    (normalizedMiddleHalfCompressionAsHalfDominanceUpperBound K O)

theorem normalizedMiddleHalfCompression_halfInterval_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (K : ThreeFlavorNormalizedMiddleHalfCompression (A := A)) :
  (normalizedMiddleHalfCompressionAsHalfInterval
      A
      hA
      J
      hsingle
      O
      K).lower <= threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (normalizedMiddleHalfCompressionAsHalfInterval
        A
        hA
        J
        hsingle
        O
        K).upper :=
  gapDominanceNumeralUpperBound_interval_contains_gapRatio
    A
    hA
    J
    hsingle
    O
    (normalizedMiddleHalfCompressionAsHalfDominanceUpperBound K O)

def normalizedMiddleHalfCompressionAsHalfDecimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (K : ThreeFlavorNormalizedMiddleHalfCompression (A := A))
  (decimalLabel : String)
  (decimalLabelCertifiedByInterval : Prop)
  (hlabel : decimalLabelCertifiedByInterval) :
  ThreeFlavorClosedRootDecimalWindow
    ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation
      ℚ
      A
      (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
        ℚ
        A
        hA
        J
        hsingle)) :=
  gapDominanceNumeralUpperBoundAsDecimalWindow
    A
    hA
    J
    hsingle
    O
    (normalizedMiddleHalfCompressionAsHalfDominanceUpperBound K O)
    decimalLabel
    decimalLabelCertifiedByInterval
    hlabel

/--
Half-side coordinate anchor.

This is the AASC-facing refinement of the half-window source target.  It does
not assert the quotient directly; it starts from a certified internal
coordinate anchor and adds the source-side fact that the independently
presented root lies in the lower half.
-/
structure ThreeFlavorHalfSideCoordinateAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ) where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  coordinateAnchor : ThreeFlavorInternalCoordinateAnchor ℚ A
  root_le_half :
    coordinateAnchor.root <= (1 / 2 : ℚ)
  halfSideDerivedInternally : Prop
  halfSideDerivedInternally_proof :
    halfSideDerivedInternally
  noEmpiricalHalfSideImport : Prop
  noEmpiricalHalfSideImport_proof :
    noEmpiricalHalfSideImport
  noHalfSideFitTuning : Prop
  noHalfSideFitTuning_proof :
    noHalfSideFitTuning

def halfSideCoordinateAnchorAsNormalizedMiddleHalfCompression
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (K : ThreeFlavorHalfSideCoordinateAnchor A) :
  ThreeFlavorNormalizedMiddleHalfCompression (A := A) :=
  { gapRatioAlgebraPasses := K.gapRatioAlgebraPasses
    normalizedMiddle_le_half := by
      rw [← K.coordinateAnchor.root_eq_gapRatio]
      exact K.root_le_half
    normalizedMiddleLawDerivedInternally :=
      K.coordinateAnchor.sourceConstructsRoot /\
        K.halfSideDerivedInternally
    normalizedMiddleLawDerivedInternally_proof :=
      ⟨K.coordinateAnchor.sourceConstructsRoot_proof,
        K.halfSideDerivedInternally_proof⟩
    noEmpiricalMiddleCoordinateImport :=
      K.coordinateAnchor.noEmpiricalFitImport /\
        K.noEmpiricalHalfSideImport
    noEmpiricalMiddleCoordinateImport_proof :=
      ⟨K.coordinateAnchor.noEmpiricalFitImport_proof,
        K.noEmpiricalHalfSideImport_proof⟩
    noMiddleCoordinateFitTuning :=
      K.coordinateAnchor.noParameterTuning /\
        K.noHalfSideFitTuning
    noMiddleCoordinateFitTuning_proof :=
      ⟨K.coordinateAnchor.noParameterTuning_proof,
        K.noHalfSideFitTuning_proof⟩ }

def halfSideCoordinateAnchorAsHalfInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (K : ThreeFlavorHalfSideCoordinateAnchor A) :
  ThreeFlavorNumeralRationalClosedRootInterval
    (sameScopePackageAsAlgebraicClosedRootPresentation
      ℚ
      A
      (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
        ℚ
        A
        hA
        J
        hsingle)) :=
  normalizedMiddleHalfCompressionAsHalfInterval
    A
    hA
    J
    hsingle
    O
    (halfSideCoordinateAnchorAsNormalizedMiddleHalfCompression K)

theorem halfSideCoordinateAnchor_halfInterval_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (K : ThreeFlavorHalfSideCoordinateAnchor A) :
  (halfSideCoordinateAnchorAsHalfInterval
      A
      hA
      J
      hsingle
      O
      K).lower <= threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (halfSideCoordinateAnchorAsHalfInterval
        A
        hA
        J
        hsingle
        O
        K).upper :=
  normalizedMiddleHalfCompression_halfInterval_contains_gapRatio
    A
    hA
    J
    hsingle
    O
    (halfSideCoordinateAnchorAsNormalizedMiddleHalfCompression K)

def halfSideCoordinateAnchorAsHalfDecimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (K : ThreeFlavorHalfSideCoordinateAnchor A)
  (decimalLabel : String)
  (decimalLabelCertifiedByInterval : Prop)
  (hlabel : decimalLabelCertifiedByInterval) :
  ThreeFlavorClosedRootDecimalWindow
    ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation
      ℚ
      A
      (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
        ℚ
        A
        hA
        J
        hsingle)) :=
  normalizedMiddleHalfCompressionAsHalfDecimalWindow
    A
    hA
    J
    hsingle
    O
    (halfSideCoordinateAnchorAsNormalizedMiddleHalfCompression K)
    decimalLabel
    decimalLabelCertifiedByInterval
    hlabel

def NeedsThreeFlavorHalfSideCoordinateAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ) : Prop :=
  Not (exists _K : ThreeFlavorHalfSideCoordinateAnchor A, True)

theorem halfSideCoordinateAnchor_discharge_normalizedMiddleNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (K : ThreeFlavorHalfSideCoordinateAnchor A) :
  Not (NeedsThreeFlavorHalfSideCoordinateAnchor A) := by
  intro hneed
  exact hneed ⟨K, True.intro⟩

/--
Source-certified half-side coordinate anchor.

This is the construction socket for the next source proof.  The source family
supplies the non-tautological coordinate anchor; this object adds the single
side inequality needed for the half-window readout.
-/
structure ThreeFlavorSourceCertifiedHalfSideCoordinateAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (kind : AASCInteriorAnchorSourceKind) where
  certifiedAnchor :
    ThreeFlavorSourceCertifiedCoordinateAnchor ℚ A kind
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  root_le_half :
    certifiedAnchor.anchor.root <= (1 / 2 : ℚ)
  halfSideCertifiedBySourceFamily : Prop
  halfSideCertifiedBySourceFamily_proof :
    halfSideCertifiedBySourceFamily
  noEmpiricalHalfSideImport : Prop
  noEmpiricalHalfSideImport_proof :
    noEmpiricalHalfSideImport
  noHalfSideFitTuning : Prop
  noHalfSideFitTuning_proof :
    noHalfSideFitTuning

def sourceCertifiedHalfSideAnchorAsHalfSideCoordinateAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {kind : AASCInteriorAnchorSourceKind}
  (S : ThreeFlavorSourceCertifiedHalfSideCoordinateAnchor A kind) :
  ThreeFlavorHalfSideCoordinateAnchor A :=
  { gapRatioAlgebraPasses := S.gapRatioAlgebraPasses
    coordinateAnchor :=
      sourceCertifiedCoordinateAnchorAsInternalAnchor
        ℚ
        A
        S.certifiedAnchor
    root_le_half := by
      simpa [sourceCertifiedCoordinateAnchorAsInternalAnchor]
        using S.root_le_half
    halfSideDerivedInternally :=
      S.certifiedAnchor.sourceFamilyCertified /\
        S.halfSideCertifiedBySourceFamily
    halfSideDerivedInternally_proof :=
      ⟨S.certifiedAnchor.sourceFamilyCertified_proof,
        S.halfSideCertifiedBySourceFamily_proof⟩
    noEmpiricalHalfSideImport :=
      S.certifiedAnchor.anchor.noEmpiricalFitImport /\
        S.noEmpiricalHalfSideImport
    noEmpiricalHalfSideImport_proof :=
      ⟨S.certifiedAnchor.anchor.noEmpiricalFitImport_proof,
        S.noEmpiricalHalfSideImport_proof⟩
    noHalfSideFitTuning :=
      S.certifiedAnchor.anchor.noParameterTuning /\
        S.noHalfSideFitTuning
    noHalfSideFitTuning_proof :=
      ⟨S.certifiedAnchor.anchor.noParameterTuning_proof,
        S.noHalfSideFitTuning_proof⟩ }

def sourceCertifiedHalfSideAnchorAsHalfInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  {kind : AASCInteriorAnchorSourceKind}
  (S : ThreeFlavorSourceCertifiedHalfSideCoordinateAnchor A kind) :
  ThreeFlavorNumeralRationalClosedRootInterval
    (sameScopePackageAsAlgebraicClosedRootPresentation
      ℚ
      A
      (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
        ℚ
        A
        hA
        J
        hsingle)) :=
  halfSideCoordinateAnchorAsHalfInterval
    A
    hA
    J
    hsingle
    O
    (sourceCertifiedHalfSideAnchorAsHalfSideCoordinateAnchor S)

theorem sourceCertifiedHalfSideAnchor_halfInterval_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  {kind : AASCInteriorAnchorSourceKind}
  (S : ThreeFlavorSourceCertifiedHalfSideCoordinateAnchor A kind) :
  (sourceCertifiedHalfSideAnchorAsHalfInterval
      A
      hA
      J
      hsingle
      O
      S).lower <= threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (sourceCertifiedHalfSideAnchorAsHalfInterval
        A
        hA
        J
        hsingle
        O
        S).upper :=
  halfSideCoordinateAnchor_halfInterval_contains_gapRatio
    A
    hA
    J
    hsingle
    O
    (sourceCertifiedHalfSideAnchorAsHalfSideCoordinateAnchor S)

def sourceCertifiedHalfSideAnchorAsHalfDecimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  {kind : AASCInteriorAnchorSourceKind}
  (S : ThreeFlavorSourceCertifiedHalfSideCoordinateAnchor A kind)
  (decimalLabel : String)
  (decimalLabelCertifiedByInterval : Prop)
  (hlabel : decimalLabelCertifiedByInterval) :
  ThreeFlavorClosedRootDecimalWindow
    ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation
      ℚ
      A
      (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
        ℚ
        A
        hA
        J
        hsingle)) :=
  halfSideCoordinateAnchorAsHalfDecimalWindow
    A
    hA
    J
    hsingle
    O
    (sourceCertifiedHalfSideAnchorAsHalfSideCoordinateAnchor S)
    decimalLabel
    decimalLabelCertifiedByInterval
    hlabel

def NeedsThreeFlavorSourceCertifiedHalfSideCoordinateAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (kind : AASCInteriorAnchorSourceKind) : Prop :=
  Not (exists _S :
    ThreeFlavorSourceCertifiedHalfSideCoordinateAnchor A kind, True)

theorem sourceCertifiedHalfSideAnchor_discharge_halfSideNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  {kind : AASCInteriorAnchorSourceKind}
  (S : ThreeFlavorSourceCertifiedHalfSideCoordinateAnchor A kind) :
  Not (NeedsThreeFlavorSourceCertifiedHalfSideCoordinateAnchor A kind) := by
  intro hneed
  exact hneed ⟨S, True.intro⟩

/--
Quotient-normal-form half-side coordinate anchor.

This selects the most AASC-native source family for the next construction:
the coordinate root is supplied by a quotient normal form, and the only extra
side fact is that this independently presented root lies in the lower half.
-/
structure ThreeFlavorQuotientNormalFormHalfSideCoordinateAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ) where
  qnfAnchor :
    ThreeFlavorQuotientNormalFormCoordinateAnchor ℚ A
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  qnfRoot_le_half :
    qnfAnchor.anchor.root <= (1 / 2 : ℚ)
  qnfHalfSideCertified : Prop
  qnfHalfSideCertified_proof :
    qnfHalfSideCertified
  noEmpiricalQNFHalfSideImport : Prop
  noEmpiricalQNFHalfSideImport_proof :
    noEmpiricalQNFHalfSideImport
  noQNFHalfSideFitTuning : Prop
  noQNFHalfSideFitTuning_proof :
    noQNFHalfSideFitTuning

def qnfHalfSideAnchorAsSourceCertifiedHalfSideAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  (Q : ThreeFlavorQuotientNormalFormHalfSideCoordinateAnchor A) :
  ThreeFlavorSourceCertifiedHalfSideCoordinateAnchor
    A
    .quotientNormalForm :=
  { certifiedAnchor := Q.qnfAnchor
    gapRatioAlgebraPasses := Q.gapRatioAlgebraPasses
    root_le_half := Q.qnfRoot_le_half
    halfSideCertifiedBySourceFamily := Q.qnfHalfSideCertified
    halfSideCertifiedBySourceFamily_proof :=
      Q.qnfHalfSideCertified_proof
    noEmpiricalHalfSideImport := Q.noEmpiricalQNFHalfSideImport
    noEmpiricalHalfSideImport_proof :=
      Q.noEmpiricalQNFHalfSideImport_proof
    noHalfSideFitTuning := Q.noQNFHalfSideFitTuning
    noHalfSideFitTuning_proof := Q.noQNFHalfSideFitTuning_proof }

def qnfHalfSideAnchorAsHalfInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (Q : ThreeFlavorQuotientNormalFormHalfSideCoordinateAnchor A) :
  ThreeFlavorNumeralRationalClosedRootInterval
    (sameScopePackageAsAlgebraicClosedRootPresentation
      ℚ
      A
      (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
        ℚ
        A
        hA
        J
        hsingle)) :=
  sourceCertifiedHalfSideAnchorAsHalfInterval
    A
    hA
    J
    hsingle
    O
    (qnfHalfSideAnchorAsSourceCertifiedHalfSideAnchor Q)

theorem qnfHalfSideAnchor_halfInterval_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (Q : ThreeFlavorQuotientNormalFormHalfSideCoordinateAnchor A) :
  (qnfHalfSideAnchorAsHalfInterval
      A
      hA
      J
      hsingle
      O
      Q).lower <= threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (qnfHalfSideAnchorAsHalfInterval
        A
        hA
        J
        hsingle
        O
        Q).upper :=
  sourceCertifiedHalfSideAnchor_halfInterval_contains_gapRatio
    A
    hA
    J
    hsingle
    O
    (qnfHalfSideAnchorAsSourceCertifiedHalfSideAnchor Q)

def qnfHalfSideAnchorAsHalfDecimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (Q : ThreeFlavorQuotientNormalFormHalfSideCoordinateAnchor A)
  (decimalLabel : String)
  (decimalLabelCertifiedByInterval : Prop)
  (hlabel : decimalLabelCertifiedByInterval) :
  ThreeFlavorClosedRootDecimalWindow
    ℚ
    (sameScopePackageAsAlgebraicClosedRootPresentation
      ℚ
      A
      (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
        ℚ
        A
        hA
        J
        hsingle)) :=
  sourceCertifiedHalfSideAnchorAsHalfDecimalWindow
    A
    hA
    J
    hsingle
    O
    (qnfHalfSideAnchorAsSourceCertifiedHalfSideAnchor Q)
    decimalLabel
    decimalLabelCertifiedByInterval
    hlabel

def NeedsThreeFlavorQuotientNormalFormHalfSideCoordinateAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ) : Prop :=
  Not (exists _Q :
    ThreeFlavorQuotientNormalFormHalfSideCoordinateAnchor A, True)

theorem qnfHalfSideAnchor_discharge_sourceFamilyChoiceNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (Q : ThreeFlavorQuotientNormalFormHalfSideCoordinateAnchor A) :
  Not (NeedsThreeFlavorQuotientNormalFormHalfSideCoordinateAnchor A) := by
  intro hneed
  exact hneed ⟨Q, True.intro⟩

/--
Half-side certificate for an existing quotient-normal-form interior law.

This is the final local socket before the actual side proof: once the QNF law
is built, one only has to prove that its independently presented root is
`<= 1/2`.
-/
structure ThreeFlavorQuotientNormalFormInteriorLawHalfSide
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  qnfRoot_le_half :
    Q.rootOfNormalForm Q.normalForm <= (1 / 2 : ℚ)
  qnfHalfSideDerivedInternally : Prop
  qnfHalfSideDerivedInternally_proof :
    qnfHalfSideDerivedInternally
  noEmpiricalQNFHalfSideImport : Prop
  noEmpiricalQNFHalfSideImport_proof :
    noEmpiricalQNFHalfSideImport
  noQNFHalfSideFitTuning : Prop
  noQNFHalfSideFitTuning_proof :
    noQNFHalfSideFitTuning

def qnfInteriorLawHalfSideAsQNFHalfSideAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (S : ThreeFlavorQuotientNormalFormInteriorLawHalfSide A Q) :
  ThreeFlavorQuotientNormalFormHalfSideCoordinateAnchor A :=
  { qnfAnchor := quotientNormalFormInteriorLawAsCertifiedAnchor ℚ A Q
    gapRatioAlgebraPasses := S.gapRatioAlgebraPasses
    qnfRoot_le_half := by
      simpa [quotientNormalFormInteriorLawAsCertifiedAnchor,
        quotientNormalFormInteriorLawAsInternalCoordinateAnchor]
        using S.qnfRoot_le_half
    qnfHalfSideCertified :=
      Q.normalFormConstructedInternally /\
        S.qnfHalfSideDerivedInternally
    qnfHalfSideCertified_proof :=
      ⟨Q.normalFormConstructedInternally_proof,
        S.qnfHalfSideDerivedInternally_proof⟩
    noEmpiricalQNFHalfSideImport :=
      Q.noEmpiricalFitImport /\
        S.noEmpiricalQNFHalfSideImport
    noEmpiricalQNFHalfSideImport_proof :=
      ⟨Q.noEmpiricalFitImport_proof,
        S.noEmpiricalQNFHalfSideImport_proof⟩
    noQNFHalfSideFitTuning :=
      Q.noParameterTuning /\
        S.noQNFHalfSideFitTuning
    noQNFHalfSideFitTuning_proof :=
      ⟨Q.noParameterTuning_proof,
        S.noQNFHalfSideFitTuning_proof⟩ }

def qnfInteriorLawHalfSideAsHalfInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (S : ThreeFlavorQuotientNormalFormInteriorLawHalfSide A Q) :
  ThreeFlavorNumeralRationalClosedRootInterval
    (sameScopePackageAsAlgebraicClosedRootPresentation
      ℚ
      A
      (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
        ℚ
        A
        hA
        J
        hsingle)) :=
  qnfHalfSideAnchorAsHalfInterval
    A
    hA
    J
    hsingle
    O
    (qnfInteriorLawHalfSideAsQNFHalfSideAnchor S)

theorem qnfInteriorLawHalfSide_halfInterval_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (S : ThreeFlavorQuotientNormalFormInteriorLawHalfSide A Q) :
  (qnfInteriorLawHalfSideAsHalfInterval
      A
      hA
      J
      hsingle
      O
      S).lower <= threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (qnfInteriorLawHalfSideAsHalfInterval
        A
        hA
        J
        hsingle
        O
        S).upper :=
  qnfHalfSideAnchor_halfInterval_contains_gapRatio
    A
    hA
    J
    hsingle
    O
    (qnfInteriorLawHalfSideAsQNFHalfSideAnchor S)

def NeedsThreeFlavorQNFInteriorLawHalfSide
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) : Prop :=
  Not (exists _S :
    ThreeFlavorQuotientNormalFormInteriorLawHalfSide A Q, True)

theorem qnfInteriorLawHalfSide_discharge_qnfHalfSideAnchorNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (S : ThreeFlavorQuotientNormalFormInteriorLawHalfSide A Q) :
  Not (NeedsThreeFlavorQNFInteriorLawHalfSide A Q) := by
  intro hneed
  exact hneed ⟨S, True.intro⟩

/--
A source-facing lower-half criterion for an existing QNF interior law.

This clears the raw inequality blocker without pretending to have the final
numeric readout.  The remaining mathematical task is now a named predicate on
the QNF root, together with a proof that the predicate is sound for the lower
half of the normalized coordinate.
-/
structure ThreeFlavorQNFInteriorLawLowerHalfCriterion
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  LowerHalfPredicate : ℚ -> Prop
  qnfRoot_satisfies_lowerHalf :
    LowerHalfPredicate (Q.rootOfNormalForm Q.normalForm)
  lowerHalfPredicate_sound :
    forall x : ℚ, LowerHalfPredicate x -> x <= (1 / 2 : ℚ)
  lowerHalfPredicateConstructedInternally : Prop
  lowerHalfPredicateConstructedInternally_proof :
    lowerHalfPredicateConstructedInternally
  lowerHalfPredicateSameScopeAsQNF : Prop
  lowerHalfPredicateSameScopeAsQNF_proof :
    lowerHalfPredicateSameScopeAsQNF
  lowerHalfPredicateQuotientStable : Prop
  lowerHalfPredicateQuotientStable_proof :
    lowerHalfPredicateQuotientStable
  noEmpiricalLowerHalfImport : Prop
  noEmpiricalLowerHalfImport_proof :
    noEmpiricalLowerHalfImport
  noLowerHalfFitTuning : Prop
  noLowerHalfFitTuning_proof :
    noLowerHalfFitTuning

def qnfLowerHalfCriterionAsInteriorLawHalfSide
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : ThreeFlavorQNFInteriorLawLowerHalfCriterion A Q) :
  ThreeFlavorQuotientNormalFormInteriorLawHalfSide A Q :=
  { gapRatioAlgebraPasses := K.gapRatioAlgebraPasses
    qnfRoot_le_half :=
      K.lowerHalfPredicate_sound
        (Q.rootOfNormalForm Q.normalForm)
        K.qnfRoot_satisfies_lowerHalf
    qnfHalfSideDerivedInternally :=
      K.lowerHalfPredicateConstructedInternally /\
        K.lowerHalfPredicateSameScopeAsQNF /\
        K.lowerHalfPredicateQuotientStable
    qnfHalfSideDerivedInternally_proof :=
      ⟨K.lowerHalfPredicateConstructedInternally_proof,
        K.lowerHalfPredicateSameScopeAsQNF_proof,
        K.lowerHalfPredicateQuotientStable_proof⟩
    noEmpiricalQNFHalfSideImport := K.noEmpiricalLowerHalfImport
    noEmpiricalQNFHalfSideImport_proof :=
      K.noEmpiricalLowerHalfImport_proof
    noQNFHalfSideFitTuning := K.noLowerHalfFitTuning
    noQNFHalfSideFitTuning_proof := K.noLowerHalfFitTuning_proof }

def qnfLowerHalfCriterionAsHalfInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : ThreeFlavorQNFInteriorLawLowerHalfCriterion A Q) :
  ThreeFlavorNumeralRationalClosedRootInterval
    (sameScopePackageAsAlgebraicClosedRootPresentation
      ℚ
      A
      (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
        ℚ
        A
        K.gapRatioAlgebraPasses
        J
        hsingle)) :=
  qnfInteriorLawHalfSideAsHalfInterval
    A
    K.gapRatioAlgebraPasses
    J
    hsingle
    O
    (qnfLowerHalfCriterionAsInteriorLawHalfSide K)

theorem qnfLowerHalfCriterion_halfInterval_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : ThreeFlavorQNFInteriorLawLowerHalfCriterion A Q) :
  (qnfLowerHalfCriterionAsHalfInterval
      A
      J
      hsingle
      O
      K).lower <= threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (qnfLowerHalfCriterionAsHalfInterval
        A
        J
        hsingle
        O
        K).upper :=
  qnfInteriorLawHalfSide_halfInterval_contains_gapRatio
    A
    K.gapRatioAlgebraPasses
    J
    hsingle
    O
    (qnfLowerHalfCriterionAsInteriorLawHalfSide K)

def NeedsThreeFlavorQNFInteriorLawLowerHalfCriterion
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) : Prop :=
  Not (exists _K :
    ThreeFlavorQNFInteriorLawLowerHalfCriterion A Q, True)

theorem qnfLowerHalfCriterion_discharge_qnfRootInequalityNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : ThreeFlavorQNFInteriorLawLowerHalfCriterion A Q) :
  Not (NeedsThreeFlavorQNFInteriorLawLowerHalfCriterion A Q) := by
  intro hneed
  exact hneed ⟨K, True.intro⟩

/--
Normalized-middle route to the QNF lower-half criterion.

The QNF interior law already identifies its root with the three-flavor gap
ratio.  Therefore any source proof that the normalized middle coordinate lies
in the lower half immediately supplies the lower-half criterion for the QNF
root.
-/
def normalizedMiddleHalfCompressionAsQNFLowerHalfCriterion
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : ThreeFlavorNormalizedMiddleHalfCompression (A := A)) :
  ThreeFlavorQNFInteriorLawLowerHalfCriterion A Q :=
  { gapRatioAlgebraPasses := K.gapRatioAlgebraPasses
    LowerHalfPredicate := fun x : ℚ => x <= (1 / 2 : ℚ)
    qnfRoot_satisfies_lowerHalf := by
      rw [Q.root_eq_denotation, Q.denotation_eq_gapRatio]
      exact K.normalizedMiddle_le_half
    lowerHalfPredicate_sound := by
      intro x hx
      exact hx
    lowerHalfPredicateConstructedInternally :=
      K.normalizedMiddleLawDerivedInternally /\
        Q.normalFormConstructedInternally
    lowerHalfPredicateConstructedInternally_proof :=
      ⟨K.normalizedMiddleLawDerivedInternally_proof,
        Q.normalFormConstructedInternally_proof⟩
    lowerHalfPredicateSameScopeAsQNF :=
      Q.sameScopeAsStandingRatio /\ Q.rootClassCertified
    lowerHalfPredicateSameScopeAsQNF_proof :=
      ⟨Q.sameScopeAsStandingRatio_proof,
        Q.rootClassCertified_proof⟩
    lowerHalfPredicateQuotientStable :=
      Q.quotientFiberExhaustedModuloSkin /\
        Q.exactnessRelevantRepresentativesControlled
    lowerHalfPredicateQuotientStable_proof :=
      ⟨Q.quotientFiberExhaustedModuloSkin_proof,
        Q.exactnessRelevantRepresentativesControlled_proof⟩
    noEmpiricalLowerHalfImport :=
      K.noEmpiricalMiddleCoordinateImport /\ Q.noEmpiricalFitImport
    noEmpiricalLowerHalfImport_proof :=
      ⟨K.noEmpiricalMiddleCoordinateImport_proof,
        Q.noEmpiricalFitImport_proof⟩
    noLowerHalfFitTuning :=
      K.noMiddleCoordinateFitTuning /\ Q.noParameterTuning
    noLowerHalfFitTuning_proof :=
      ⟨K.noMiddleCoordinateFitTuning_proof,
        Q.noParameterTuning_proof⟩ }

theorem normalizedMiddleHalfCompression_discharge_qnfLowerHalfCriterionNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : ThreeFlavorNormalizedMiddleHalfCompression (A := A)) :
  Not (NeedsThreeFlavorQNFInteriorLawLowerHalfCriterion A Q) :=
  qnfLowerHalfCriterion_discharge_qnfRootInequalityNeed
    A
    (normalizedMiddleHalfCompressionAsQNFLowerHalfCriterion K)

/--
Numeral-interval route to the QNF lower-half criterion.

This removes one more abstract side condition.  Instead of asking directly for
a predicate on the QNF root, it is enough to supply a QNF-aligned numeral
closed-root interval and prove that its displayed upper endpoint is at most
`1/2`.
-/
def qnfNumeralIntervalUpperHalfAsLowerHalfCriterion
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (N : ThreeFlavorNumeralRationalClosedRootInterval G)
  (upper_le_half : N.upper <= (1 / 2 : ℚ)) :
  ThreeFlavorQNFInteriorLawLowerHalfCriterion A Q :=
  { gapRatioAlgebraPasses := hA
    LowerHalfPredicate := fun x : ℚ => x <= N.upper
    qnfRoot_satisfies_lowerHalf := by
      rw [L.normalFormRoot_eq_selectedRoot]
      exact N.selectedRoot_mem.2
    lowerHalfPredicate_sound := by
      intro x hx
      exact le_trans hx upper_le_half
    lowerHalfPredicateConstructedInternally :=
      N.endpointsConstructedInternally /\
        Q.normalFormConstructedInternally
    lowerHalfPredicateConstructedInternally_proof :=
      ⟨N.endpointsConstructedInternally_proof,
        Q.normalFormConstructedInternally_proof⟩
    lowerHalfPredicateSameScopeAsQNF :=
      Q.sameScopeAsStandingRatio /\ Q.rootClassCertified
    lowerHalfPredicateSameScopeAsQNF_proof :=
      ⟨Q.sameScopeAsStandingRatio_proof,
        Q.rootClassCertified_proof⟩
    lowerHalfPredicateQuotientStable :=
      Q.quotientFiberExhaustedModuloSkin /\
        L.coefficientsDoNotEncodeSelectedRoot
    lowerHalfPredicateQuotientStable_proof :=
      ⟨Q.quotientFiberExhaustedModuloSkin_proof,
        L.coefficientsDoNotEncodeSelectedRoot_proof⟩
    noEmpiricalLowerHalfImport :=
      N.noEmpiricalEndpointImport /\ Q.noEmpiricalFitImport
    noEmpiricalLowerHalfImport_proof :=
      ⟨N.noEmpiricalEndpointImport_proof,
        Q.noEmpiricalFitImport_proof⟩
    noLowerHalfFitTuning :=
      N.noEndpointFitTuning /\ Q.noParameterTuning
    noLowerHalfFitTuning_proof :=
      ⟨N.noEndpointFitTuning_proof,
        Q.noParameterTuning_proof⟩ }

def qnfNumeralIntervalUpperHalfAsHalfInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (N : ThreeFlavorNumeralRationalClosedRootInterval G)
  (upper_le_half : N.upper <= (1 / 2 : ℚ)) :
  ThreeFlavorNumeralRationalClosedRootInterval
    (sameScopePackageAsAlgebraicClosedRootPresentation
      ℚ
      A
      (gapQuotientExpressionAsSameScopeNumericalPredictionPackage
        ℚ
        A
        hA
        J
        hsingle)) :=
  qnfLowerHalfCriterionAsHalfInterval
    A
    J
    hsingle
    O
    (qnfNumeralIntervalUpperHalfAsLowerHalfCriterion
      hA
      G
      L
      N
      upper_le_half)

theorem qnfNumeralIntervalUpperHalf_halfInterval_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  (A : ThreeFlavorGapRatioAlgebra M ℚ)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (J : AASCCurrentHybridJointWitness H)
  (hsingle : HybridJointRestrictionSingleton H)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (N : ThreeFlavorNumeralRationalClosedRootInterval G)
  (upper_le_half : N.upper <= (1 / 2 : ℚ)) :
  (qnfNumeralIntervalUpperHalfAsHalfInterval
      A
      hA
      J
      hsingle
      O
      G
      L
      N
      upper_le_half).lower <= threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (qnfNumeralIntervalUpperHalfAsHalfInterval
        A
        hA
        J
        hsingle
        O
        G
        L
        N
        upper_le_half).upper :=
  qnfLowerHalfCriterion_halfInterval_contains_gapRatio
    A
    J
    hsingle
    O
    (qnfNumeralIntervalUpperHalfAsLowerHalfCriterion
      hA
      G
      L
      N
      upper_le_half)

def NeedsThreeFlavorQNFNumeralIntervalUpperHalf
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) : Prop :=
  Not (exists N : ThreeFlavorNumeralRationalClosedRootInterval G,
    exists _L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q,
      N.upper <= (1 / 2 : ℚ))

theorem qnfNumeralIntervalUpperHalf_discharge_lowerHalfCriterionNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (N : ThreeFlavorNumeralRationalClosedRootInterval G)
  (upper_le_half : N.upper <= (1 / 2 : ℚ)) :
  Not (NeedsThreeFlavorQNFNumeralIntervalUpperHalf G Q) := by
  intro hneed
  exact hneed ⟨N, L, upper_le_half⟩

/--
Build the concrete aligned half interval `[0, 1/2]`.

The lower endpoint is justified by strict ordering of the three mass-squared
levels.  The upper endpoint is justified by the QNF lower-half criterion.  The
endpoints themselves are displayed rational numerals, so this clears the
separate "construct a numeral interval" obligation for the QNF-aligned
presentation.
-/
def qnfLowerHalfCriterionAsAlignedHalfNumeralInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (K : ThreeFlavorQNFInteriorLawLowerHalfCriterion A Q) :
  ThreeFlavorNumeralRationalClosedRootInterval G := by
  rcases hA with
    ⟨_hratioReadback, htwoGaps, _hquotient, hscale, habsolute,
      hobserved, _hroot, hordering, htarget⟩
  have hroot :
      G.selectedRoot = threeFlavorGapRatio A.massSquaredLevelOf :=
    algebraicClosedRootPresentation_selectedRoot_eq_gapRatio G
  have hqnfRoot_le_half :
      Q.rootOfNormalForm Q.normalForm <= (1 / 2 : ℚ) :=
    K.lowerHalfPredicate_sound
      (Q.rootOfNormalForm Q.normalForm)
      K.qnfRoot_satisfies_lowerHalf
  exact
  { lower := 0
    upper := 1 / 2
    tolerance := 1 / 2
    lowerNumerator := 0
    lowerDenominator := 1
    lowerDenominator_pos := by norm_num
    upperNumerator := 1
    upperDenominator := 2
    upperDenominator_pos := by norm_num
    lower_eq_numeral := by norm_num
    upper_eq_numeral := by norm_num
    lower_lt_upper := by norm_num
    tolerance_pos := by norm_num
    selectedRoot_mem := by
      constructor
      · rw [hroot]
        exact strictMassSquaredOrdering_gapRatio_nonneg O
      · rw [← L.normalFormRoot_eq_selectedRoot]
        exact hqnfRoot_le_half
    width_le_tolerance := by norm_num
    endpointsConstructedInternally :=
      A.twoIndependentGapsCertified /\
        A.sameStandingRatioTarget /\
        K.lowerHalfPredicateConstructedInternally
    endpointsConstructedInternally_proof :=
      ⟨htwoGaps, htarget,
        K.lowerHalfPredicateConstructedInternally_proof⟩
    noEmpiricalEndpointImport :=
      A.noObservedGapImport /\
        A.noOrderingFitImport /\
        K.noEmpiricalLowerHalfImport
    noEmpiricalEndpointImport_proof :=
      ⟨hobserved, hordering,
        K.noEmpiricalLowerHalfImport_proof⟩
    noEndpointFitTuning :=
      A.noAbsoluteMassScaleImport /\
        A.scaleFreeGapRatio /\
        K.noLowerHalfFitTuning
    noEndpointFitTuning_proof :=
      ⟨habsolute, hscale,
        K.noLowerHalfFitTuning_proof⟩ }

theorem qnfLowerHalfCriterion_alignedHalfNumeralInterval_upper_le_half
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (K : ThreeFlavorQNFInteriorLawLowerHalfCriterion A Q) :
  (qnfLowerHalfCriterionAsAlignedHalfNumeralInterval
      hA
      G
      L
      O
      K).upper <= (1 / 2 : ℚ) := by
  rcases hA with
    ⟨_hratioReadback, _htwoGaps, _hquotient, _hscale, _habsolute,
      _hobserved, _hroot, _hordering, _htarget⟩
  norm_num [qnfLowerHalfCriterionAsAlignedHalfNumeralInterval]

theorem qnfLowerHalfCriterion_discharge_qnfNumeralIntervalUpperHalfNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (K : ThreeFlavorQNFInteriorLawLowerHalfCriterion A Q) :
  Not (NeedsThreeFlavorQNFNumeralIntervalUpperHalf G Q) :=
  qnfNumeralIntervalUpperHalf_discharge_lowerHalfCriterionNeed
    G
    L
    (qnfLowerHalfCriterionAsAlignedHalfNumeralInterval
      hA
      G
      L
      O
      K)
    (qnfLowerHalfCriterion_alignedHalfNumeralInterval_upper_le_half
      hA
      G
      L
      O
      K)

/--
Direct readout bridge from a source curvature square witness.

This composes the full half-side chain:

square witness -> curvature nonnegative -> convexity -> two-step dominance ->
adjacent-gap half side -> midpoint compression -> normalized-middle half ->
QNF lower-half criterion -> aligned `[0, 1/2]` numeral interval.
-/
def sourceCurvatureSquareWitnessAsQNFLowerHalfCriterion
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (S : ThreeFlavorSourceCurvatureSquareWitness (A := A)) :
  ThreeFlavorQNFInteriorLawLowerHalfCriterion A Q :=
  normalizedMiddleHalfCompressionAsQNFLowerHalfCriterion
    (midpointGapCompressionAsNormalizedMiddleHalfCompression
      O
      (adjacentGapHalfSideAsMidpointGapCompression
        (twoStepGapHalfDominanceAsAdjacentGapHalfSide
          (massSquaredConvexityAsTwoStepGapHalfDominance
            (sourceCurvatureNonnegativeAsMassSquaredConvexity
              (sourceCurvatureSquareWitnessAsCurvatureNonnegative S))))))

def sourceCurvatureSquareWitnessAsAlignedHalfNumeralInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (S : ThreeFlavorSourceCurvatureSquareWitness (A := A)) :
  ThreeFlavorNumeralRationalClosedRootInterval G :=
  qnfLowerHalfCriterionAsAlignedHalfNumeralInterval
    S.gapRatioAlgebraPasses
    G
    L
    O
    (sourceCurvatureSquareWitnessAsQNFLowerHalfCriterion O S)

theorem sourceCurvatureSquareWitness_alignedHalfInterval_upper_le_half
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (S : ThreeFlavorSourceCurvatureSquareWitness (A := A)) :
  (sourceCurvatureSquareWitnessAsAlignedHalfNumeralInterval
      G
      L
      O
      S).upper <= (1 / 2 : ℚ) :=
  qnfLowerHalfCriterion_alignedHalfNumeralInterval_upper_le_half
    S.gapRatioAlgebraPasses
    G
    L
    O
    (sourceCurvatureSquareWitnessAsQNFLowerHalfCriterion O S)

theorem sourceCurvatureSquareWitness_discharge_qnfNumeralIntervalUpperHalfNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (S : ThreeFlavorSourceCurvatureSquareWitness (A := A)) :
  Not (NeedsThreeFlavorQNFNumeralIntervalUpperHalf G Q) :=
  qnfNumeralIntervalUpperHalf_discharge_lowerHalfCriterionNeed
    G
    L
    (sourceCurvatureSquareWitnessAsAlignedHalfNumeralInterval
      G
      L
      O
      S)
    (sourceCurvatureSquareWitness_alignedHalfInterval_upper_le_half
      G
      L
      O
      S)

/--
Direct readout bridge from a Relator even-tower mass-squared law.

This is weaker than the square/Gram route because it enters at convexity rather
than at a positive finite-coordinate table.  It is still enough for the
half-side readout chain:

Relator even tower -> convexity -> two-step dominance -> adjacent-gap half side
-> midpoint compression -> normalized-middle half -> QNF lower-half criterion
-> aligned `[0, 1/2]` numeral interval.
-/
def relatorEvenTowerMassSquaredLawAsQNFLowerHalfCriterion
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (Lrel : ThreeFlavorRelatorEvenTowerMassSquaredLaw (A := A)) :
  ThreeFlavorQNFInteriorLawLowerHalfCriterion A Q :=
  normalizedMiddleHalfCompressionAsQNFLowerHalfCriterion
    (midpointGapCompressionAsNormalizedMiddleHalfCompression
      O
      (adjacentGapHalfSideAsMidpointGapCompression
        (twoStepGapHalfDominanceAsAdjacentGapHalfSide
          (massSquaredConvexityAsTwoStepGapHalfDominance
            (relatorEvenTowerMassSquaredLawAsConvexity Lrel)))))

def relatorEvenTowerMassSquaredLawAsAlignedHalfNumeralInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (Lrel : ThreeFlavorRelatorEvenTowerMassSquaredLaw (A := A)) :
  ThreeFlavorNumeralRationalClosedRootInterval G :=
  qnfLowerHalfCriterionAsAlignedHalfNumeralInterval
    Lrel.gapRatioAlgebraPasses
    G
    L
    O
    (relatorEvenTowerMassSquaredLawAsQNFLowerHalfCriterion O Lrel)

theorem relatorEvenTowerMassSquaredLaw_alignedHalfInterval_upper_le_half
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (Lrel : ThreeFlavorRelatorEvenTowerMassSquaredLaw (A := A)) :
  (relatorEvenTowerMassSquaredLawAsAlignedHalfNumeralInterval
      G
      L
      O
      Lrel).upper <= (1 / 2 : ℚ) :=
  qnfLowerHalfCriterion_alignedHalfNumeralInterval_upper_le_half
    Lrel.gapRatioAlgebraPasses
    G
    L
    O
    (relatorEvenTowerMassSquaredLawAsQNFLowerHalfCriterion O Lrel)

theorem relatorEvenTowerMassSquaredLaw_discharge_qnfNumeralIntervalUpperHalfNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (Lrel : ThreeFlavorRelatorEvenTowerMassSquaredLaw (A := A)) :
  Not (NeedsThreeFlavorQNFNumeralIntervalUpperHalf G Q) :=
  qnfNumeralIntervalUpperHalf_discharge_lowerHalfCriterionNeed
    G
    L
    (relatorEvenTowerMassSquaredLawAsAlignedHalfNumeralInterval
      G
      L
      O
      Lrel)
    (relatorEvenTowerMassSquaredLaw_alignedHalfInterval_upper_le_half
      G
      L
      O
      Lrel)

def relatorEvenTowerSourceCertificateAsAlignedHalfNumeralInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (S : ThreeFlavorRelatorEvenTowerSourceCertificate (A := A)) :
  ThreeFlavorNumeralRationalClosedRootInterval G :=
  relatorEvenTowerMassSquaredLawAsAlignedHalfNumeralInterval
    G
    L
    O
    (relatorEvenTowerSourceCertificateAsMassSquaredLaw S)

theorem relatorEvenTowerSourceCertificate_alignedHalfInterval_upper_le_half
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (S : ThreeFlavorRelatorEvenTowerSourceCertificate (A := A)) :
  (relatorEvenTowerSourceCertificateAsAlignedHalfNumeralInterval
      G
      L
      O
      S).upper <= (1 / 2 : ℚ) :=
  relatorEvenTowerMassSquaredLaw_alignedHalfInterval_upper_le_half
    G
    L
    O
    (relatorEvenTowerSourceCertificateAsMassSquaredLaw S)

theorem relatorEvenTowerSourceCertificate_discharge_qnfNumeralIntervalUpperHalfNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {Q : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (L : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G Q)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (S : ThreeFlavorRelatorEvenTowerSourceCertificate (A := A)) :
  Not (NeedsThreeFlavorQNFNumeralIntervalUpperHalf G Q) :=
  qnfNumeralIntervalUpperHalf_discharge_lowerHalfCriterionNeed
    G
    L
    (relatorEvenTowerSourceCertificateAsAlignedHalfNumeralInterval
      G
      L
      O
      S)
    (relatorEvenTowerSourceCertificate_alignedHalfInterval_upper_le_half
      G
      L
      O
      S)

def relatorEvenTowerComponentsAsAlignedHalfNumeralInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Lqnf : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (T : ThreeFlavorRelatorEvenTowerParameterTable)
  (Lrel : ThreeFlavorRelatorEvenTowerLevelIdentification (A := A) T)
  (Qaudit : ThreeFlavorRelatorEvenTowerAudit) :
  ThreeFlavorNumeralRationalClosedRootInterval G :=
  relatorEvenTowerSourceCertificateAsAlignedHalfNumeralInterval
    G
    Lqnf
    O
    (relatorEvenTowerComponentsAsSourceCertificate hA T Lrel Qaudit)

theorem relatorEvenTowerComponents_alignedHalfInterval_upper_le_half
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Lqnf : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (T : ThreeFlavorRelatorEvenTowerParameterTable)
  (Lrel : ThreeFlavorRelatorEvenTowerLevelIdentification (A := A) T)
  (Qaudit : ThreeFlavorRelatorEvenTowerAudit) :
  (relatorEvenTowerComponentsAsAlignedHalfNumeralInterval
      G
      Lqnf
      O
      hA
      T
      Lrel
      Qaudit).upper <= (1 / 2 : ℚ) :=
  relatorEvenTowerSourceCertificate_alignedHalfInterval_upper_le_half
    G
    Lqnf
    O
    (relatorEvenTowerComponentsAsSourceCertificate hA T Lrel Qaudit)

theorem relatorEvenTowerComponents_discharge_qnfNumeralIntervalUpperHalfNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Lqnf : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (T : ThreeFlavorRelatorEvenTowerParameterTable)
  (Lrel : ThreeFlavorRelatorEvenTowerLevelIdentification (A := A) T)
  (Qaudit : ThreeFlavorRelatorEvenTowerAudit) :
  Not (NeedsThreeFlavorQNFNumeralIntervalUpperHalf G QNF) :=
  qnfNumeralIntervalUpperHalf_discharge_lowerHalfCriterionNeed
    G
    Lqnf
    (relatorEvenTowerComponentsAsAlignedHalfNumeralInterval
      G
      Lqnf
      O
      hA
      T
      Lrel
      Qaudit)
    (relatorEvenTowerComponents_alignedHalfInterval_upper_le_half
      G
      Lqnf
      O
      hA
      T
      Lrel
      Qaudit)

def relatorEvenTowerNumeralComponentsAsAlignedHalfNumeralInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Lqnf : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (N : ThreeFlavorRelatorEvenTowerNumeralParameterTable)
  (Lrel :
    ThreeFlavorRelatorEvenTowerLevelIdentification
      (A := A)
      (relatorEvenTowerNumeralParameterTableAsParameterTable N))
  (Qaudit : ThreeFlavorRelatorEvenTowerAudit) :
  ThreeFlavorNumeralRationalClosedRootInterval G :=
  relatorEvenTowerComponentsAsAlignedHalfNumeralInterval
    G
    Lqnf
    O
    hA
    (relatorEvenTowerNumeralParameterTableAsParameterTable N)
    Lrel
    Qaudit

theorem relatorEvenTowerNumeralComponents_alignedHalfInterval_upper_le_half
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Lqnf : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (N : ThreeFlavorRelatorEvenTowerNumeralParameterTable)
  (Lrel :
    ThreeFlavorRelatorEvenTowerLevelIdentification
      (A := A)
      (relatorEvenTowerNumeralParameterTableAsParameterTable N))
  (Qaudit : ThreeFlavorRelatorEvenTowerAudit) :
  (relatorEvenTowerNumeralComponentsAsAlignedHalfNumeralInterval
      G
      Lqnf
      O
      hA
      N
      Lrel
      Qaudit).upper <= (1 / 2 : ℚ) :=
  relatorEvenTowerComponents_alignedHalfInterval_upper_le_half
    G
    Lqnf
    O
    hA
    (relatorEvenTowerNumeralParameterTableAsParameterTable N)
    Lrel
    Qaudit

theorem relatorEvenTowerNumeralComponents_discharge_qnfNumeralIntervalUpperHalfNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Lqnf : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (N : ThreeFlavorRelatorEvenTowerNumeralParameterTable)
  (Lrel :
    ThreeFlavorRelatorEvenTowerLevelIdentification
      (A := A)
      (relatorEvenTowerNumeralParameterTableAsParameterTable N))
  (Qaudit : ThreeFlavorRelatorEvenTowerAudit) :
  Not (NeedsThreeFlavorQNFNumeralIntervalUpperHalf G QNF) :=
  relatorEvenTowerComponents_discharge_qnfNumeralIntervalUpperHalfNeed
    G
    Lqnf
    O
    hA
    (relatorEvenTowerNumeralParameterTableAsParameterTable N)
    Lrel
    Qaudit

theorem relatorEvenTowerNumeralGeneratedLevels_discharge_qnfNumeralIntervalUpperHalfNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Lqnf : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (N : ThreeFlavorRelatorEvenTowerNumeralParameterTable)
  (Lgen :
    ThreeFlavorRelatorEvenTowerGeneratedLevels
      (A := A)
      (relatorEvenTowerNumeralParameterTableAsParameterTable N))
  (Qaudit : ThreeFlavorRelatorEvenTowerAudit) :
  Not (NeedsThreeFlavorQNFNumeralIntervalUpperHalf G QNF) :=
  relatorEvenTowerNumeralComponents_discharge_qnfNumeralIntervalUpperHalfNeed
    G
    Lqnf
    O
    hA
    N
    (relatorEvenTowerGeneratedLevelsAsLevelIdentification Lgen)
    Qaudit

theorem relatorEvenTowerNumeralGeneratedLevelFunction_discharge_qnfNumeralIntervalUpperHalfNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Lqnf : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (N : ThreeFlavorRelatorEvenTowerNumeralParameterTable)
  (F :
    ThreeFlavorRelatorEvenTowerGeneratedLevelFunction
      (A := A)
      (relatorEvenTowerNumeralParameterTableAsParameterTable N))
  (Qaudit : ThreeFlavorRelatorEvenTowerAudit) :
  Not (NeedsThreeFlavorQNFNumeralIntervalUpperHalf G QNF) :=
  relatorEvenTowerNumeralGeneratedLevels_discharge_qnfNumeralIntervalUpperHalfNeed
    G
    Lqnf
    O
    hA
    N
    (relatorEvenTowerGeneratedLevelFunctionAsGeneratedLevels F)
    Qaudit

theorem relatorEvenTowerNumeralSourceReadback_discharge_qnfNumeralIntervalUpperHalfNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Lqnf : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (N : ThreeFlavorRelatorEvenTowerNumeralParameterTable)
  (R :
    ThreeFlavorRelatorEvenTowerSourceReadback
      (A := A)
      (relatorEvenTowerNumeralParameterTableAsParameterTable N))
  (Qaudit : ThreeFlavorRelatorEvenTowerAudit) :
  Not (NeedsThreeFlavorQNFNumeralIntervalUpperHalf G QNF) :=
  relatorEvenTowerNumeralGeneratedLevelFunction_discharge_qnfNumeralIntervalUpperHalfNeed
    G
    Lqnf
    O
    hA
    N
    (relatorEvenTowerSourceReadbackAsGeneratedLevelFunction R)
    Qaudit

theorem relatorEvenTowerNumeralThreePointReadback_discharge_qnfNumeralIntervalUpperHalfNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Lqnf : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (N : ThreeFlavorRelatorEvenTowerNumeralParameterTable)
  (R :
    ThreeFlavorRelatorEvenTowerThreePointReadback
      (A := A)
      (relatorEvenTowerNumeralParameterTableAsParameterTable N))
  (Qaudit : ThreeFlavorRelatorEvenTowerAudit) :
  Not (NeedsThreeFlavorQNFNumeralIntervalUpperHalf G QNF) :=
  relatorEvenTowerNumeralSourceReadback_discharge_qnfNumeralIntervalUpperHalfNeed
    G
    Lqnf
    O
    hA
    N
    (relatorEvenTowerThreePointReadbackAsSourceReadback R)
    Qaudit

def relatorEvenTowerNumeralThreePointReadbackAsAlignedHalfNumeralInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Lqnf : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (N : ThreeFlavorRelatorEvenTowerNumeralParameterTable)
  (R :
    ThreeFlavorRelatorEvenTowerThreePointReadback
      (A := A)
      (relatorEvenTowerNumeralParameterTableAsParameterTable N))
  (Qaudit : ThreeFlavorRelatorEvenTowerAudit) :
  ThreeFlavorNumeralRationalClosedRootInterval G :=
  relatorEvenTowerNumeralComponentsAsAlignedHalfNumeralInterval
    G
    Lqnf
    O
    hA
    N
    (relatorEvenTowerGeneratedLevelsAsLevelIdentification
      (relatorEvenTowerGeneratedLevelFunctionAsGeneratedLevels
        (relatorEvenTowerSourceReadbackAsGeneratedLevelFunction
          (relatorEvenTowerThreePointReadbackAsSourceReadback R))))
    Qaudit

theorem relatorEvenTowerNumeralThreePointReadback_alignedHalfInterval_upper_le_half
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Lqnf : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (N : ThreeFlavorRelatorEvenTowerNumeralParameterTable)
  (R :
    ThreeFlavorRelatorEvenTowerThreePointReadback
      (A := A)
      (relatorEvenTowerNumeralParameterTableAsParameterTable N))
  (Qaudit : ThreeFlavorRelatorEvenTowerAudit) :
  (relatorEvenTowerNumeralThreePointReadbackAsAlignedHalfNumeralInterval
      G
      Lqnf
      O
      hA
      N
      R
      Qaudit).upper <= (1 / 2 : ℚ) :=
  relatorEvenTowerNumeralComponents_alignedHalfInterval_upper_le_half
    G
    Lqnf
    O
    hA
    N
    (relatorEvenTowerGeneratedLevelsAsLevelIdentification
      (relatorEvenTowerGeneratedLevelFunctionAsGeneratedLevels
        (relatorEvenTowerSourceReadbackAsGeneratedLevelFunction
          (relatorEvenTowerThreePointReadbackAsSourceReadback R))))
    Qaudit

theorem relatorEvenTowerNumeralThreePointReadback_alignedHalfInterval_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Lqnf : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF)
  (O : ThreeFlavorStrictMassSquaredOrdering (A := A))
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (N : ThreeFlavorRelatorEvenTowerNumeralParameterTable)
  (R :
    ThreeFlavorRelatorEvenTowerThreePointReadback
      (A := A)
      (relatorEvenTowerNumeralParameterTableAsParameterTable N))
  (Qaudit : ThreeFlavorRelatorEvenTowerAudit) :
  (relatorEvenTowerNumeralThreePointReadbackAsAlignedHalfNumeralInterval
      G
      Lqnf
      O
      hA
      N
      R
      Qaudit).lower <= threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (relatorEvenTowerNumeralThreePointReadbackAsAlignedHalfNumeralInterval
        G
        Lqnf
        O
        hA
        N
        R
        Qaudit).upper :=
by
  have hroot :
      G.selectedRoot = threeFlavorGapRatio A.massSquaredLevelOf :=
    algebraicClosedRootPresentation_selectedRoot_eq_gapRatio G
  simpa [hroot] using
    (relatorEvenTowerNumeralThreePointReadbackAsAlignedHalfNumeralInterval
      G
      Lqnf
      O
      hA
      N
      R
      Qaudit).selectedRoot_mem

structure ThreeFlavorRelatorEvenTowerThreePointReadoutPackage
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {A : ThreeFlavorGapRatioAlgebra M ℚ} where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  strictMassSquaredOrdering :
    ThreeFlavorStrictMassSquaredOrdering (A := A)
  numeralParameterTable :
    ThreeFlavorRelatorEvenTowerNumeralParameterTable
  threePointReadback :
    ThreeFlavorRelatorEvenTowerThreePointReadback
      (A := A)
      (relatorEvenTowerNumeralParameterTableAsParameterTable
        numeralParameterTable)
  relatorAudit :
    ThreeFlavorRelatorEvenTowerAudit

def relatorEvenTowerThreePointReadoutPackageAsAlignedHalfNumeralInterval
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Lqnf : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF)
  (Pkg : ThreeFlavorRelatorEvenTowerThreePointReadoutPackage (A := A)) :
  ThreeFlavorNumeralRationalClosedRootInterval G :=
  relatorEvenTowerNumeralThreePointReadbackAsAlignedHalfNumeralInterval
    G
    Lqnf
    Pkg.strictMassSquaredOrdering
    Pkg.gapRatioAlgebraPasses
    Pkg.numeralParameterTable
    Pkg.threePointReadback
    Pkg.relatorAudit

theorem relatorEvenTowerThreePointReadoutPackage_alignedHalfInterval_upper_le_half
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Lqnf : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF)
  (Pkg : ThreeFlavorRelatorEvenTowerThreePointReadoutPackage (A := A)) :
  (relatorEvenTowerThreePointReadoutPackageAsAlignedHalfNumeralInterval
      G
      Lqnf
      Pkg).upper <= (1 / 2 : ℚ) :=
  relatorEvenTowerNumeralThreePointReadback_alignedHalfInterval_upper_le_half
    G
    Lqnf
    Pkg.strictMassSquaredOrdering
    Pkg.gapRatioAlgebraPasses
    Pkg.numeralParameterTable
    Pkg.threePointReadback
    Pkg.relatorAudit

theorem relatorEvenTowerThreePointReadoutPackage_alignedHalfInterval_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Lqnf : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF)
  (Pkg : ThreeFlavorRelatorEvenTowerThreePointReadoutPackage (A := A)) :
  (relatorEvenTowerThreePointReadoutPackageAsAlignedHalfNumeralInterval
      G
      Lqnf
      Pkg).lower <= threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (relatorEvenTowerThreePointReadoutPackageAsAlignedHalfNumeralInterval
        G
        Lqnf
        Pkg).upper :=
  relatorEvenTowerNumeralThreePointReadback_alignedHalfInterval_contains_gapRatio
    G
    Lqnf
    Pkg.strictMassSquaredOrdering
    Pkg.gapRatioAlgebraPasses
    Pkg.numeralParameterTable
    Pkg.threePointReadback
    Pkg.relatorAudit

theorem relatorEvenTowerThreePointReadoutPackage_discharge_qnfNumeralIntervalUpperHalfNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Lqnf : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF)
  (Pkg : ThreeFlavorRelatorEvenTowerThreePointReadoutPackage (A := A)) :
  Not (NeedsThreeFlavorQNFNumeralIntervalUpperHalf G QNF) :=
  relatorEvenTowerNumeralThreePointReadback_discharge_qnfNumeralIntervalUpperHalfNeed
    G
    Lqnf
    Pkg.strictMassSquaredOrdering
    Pkg.gapRatioAlgebraPasses
    Pkg.numeralParameterTable
    Pkg.threePointReadback
    Pkg.relatorAudit

structure ThreeFlavorRelatorEvenTowerQNFReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) where
  readoutPackage :
    ThreeFlavorRelatorEvenTowerThreePointReadoutPackage (A := A)
  qnfAlignment :
    ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF
  interval :
    ThreeFlavorNumeralRationalClosedRootInterval G
  interval_eq_packageInterval :
    interval =
      relatorEvenTowerThreePointReadoutPackageAsAlignedHalfNumeralInterval
        G
        qnfAlignment
        readoutPackage
  interval_contains_gapRatio :
    interval.lower <= threeFlavorGapRatio A.massSquaredLevelOf /\
      threeFlavorGapRatio A.massSquaredLevelOf <= interval.upper
  interval_upper_le_half :
    interval.upper <= (1 / 2 : ℚ)
  qnfUpperHalfNeedDischarged :
    Not (NeedsThreeFlavorQNFNumeralIntervalUpperHalf G QNF)

def relatorEvenTowerReadoutPackageAsQNFReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Lqnf : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF)
  (Pkg : ThreeFlavorRelatorEvenTowerThreePointReadoutPackage (A := A)) :
  ThreeFlavorRelatorEvenTowerQNFReadoutCertificate G QNF :=
  { readoutPackage := Pkg
    qnfAlignment := Lqnf
    interval :=
      relatorEvenTowerThreePointReadoutPackageAsAlignedHalfNumeralInterval
        G
        Lqnf
        Pkg
    interval_eq_packageInterval := rfl
    interval_contains_gapRatio :=
      relatorEvenTowerThreePointReadoutPackage_alignedHalfInterval_contains_gapRatio
        G
        Lqnf
        Pkg
    interval_upper_le_half :=
      relatorEvenTowerThreePointReadoutPackage_alignedHalfInterval_upper_le_half
        G
        Lqnf
        Pkg
    qnfUpperHalfNeedDischarged :=
      relatorEvenTowerThreePointReadoutPackage_discharge_qnfNumeralIntervalUpperHalfNeed
        G
        Lqnf
        Pkg }

def NeedsThreeFlavorRelatorEvenTowerQNFReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) : Prop :=
  Not (exists _K : ThreeFlavorRelatorEvenTowerQNFReadoutCertificate G QNF, True)

theorem relatorEvenTowerReadoutPackage_discharge_qnfReadoutCertificateNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Lqnf : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF)
  (Pkg : ThreeFlavorRelatorEvenTowerThreePointReadoutPackage (A := A)) :
  Not (NeedsThreeFlavorRelatorEvenTowerQNFReadoutCertificate G QNF) := by
  intro hneed
  exact hneed
    ⟨relatorEvenTowerReadoutPackageAsQNFReadoutCertificate G Lqnf Pkg,
      True.intro⟩

theorem relatorEvenTowerQNFReadoutCertificate_discharge_qnfNumeralIntervalUpperHalfNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : ThreeFlavorRelatorEvenTowerQNFReadoutCertificate G QNF) :
  Not (NeedsThreeFlavorQNFNumeralIntervalUpperHalf G QNF) :=
  K.qnfUpperHalfNeedDischarged

theorem relatorEvenTowerQNFReadoutCertificate_interval_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : ThreeFlavorRelatorEvenTowerQNFReadoutCertificate G QNF) :
  K.interval.lower <= threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <= K.interval.upper :=
  K.interval_contains_gapRatio

theorem relatorEvenTowerQNFReadoutCertificate_interval_upper_le_half
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : ThreeFlavorRelatorEvenTowerQNFReadoutCertificate G QNF) :
  K.interval.upper <= (1 / 2 : ℚ) :=
  K.interval_upper_le_half

structure ThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) where
  singleton :
    HybridJointRestrictionSingleton H
  readoutCertificate :
    ThreeFlavorRelatorEvenTowerQNFReadoutCertificate G QNF
  currentStandingEvaluation :
    CurrentStandingRatioEvaluation C
  currentEvaluationBuiltFromSingletonAndGapAlgebra :
    currentStandingEvaluation =
      gapRatioAlgebraSingletonGivesCurrentClosedExpressionEvaluation
        ℚ
        A
        readoutCertificate.readoutPackage.gapRatioAlgebraPasses
        singleton

noncomputable def relatorEvenTowerQNFReadoutCertificateAsSingletonEndpoint
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : ThreeFlavorRelatorEvenTowerQNFReadoutCertificate G QNF)
  (hsingle : HybridJointRestrictionSingleton H) :
  ThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint G QNF :=
  { singleton := hsingle
    readoutCertificate := K
    currentStandingEvaluation :=
      gapRatioAlgebraSingletonGivesCurrentClosedExpressionEvaluation
        ℚ
        A
        K.readoutPackage.gapRatioAlgebraPasses
        hsingle
    currentEvaluationBuiltFromSingletonAndGapAlgebra := rfl }

noncomputable def relatorEvenTowerReadoutPackageAndSingletonAsEndpoint
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Lqnf : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF)
  (Pkg : ThreeFlavorRelatorEvenTowerThreePointReadoutPackage (A := A))
  (hsingle : HybridJointRestrictionSingleton H) :
  ThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint G QNF :=
  relatorEvenTowerQNFReadoutCertificateAsSingletonEndpoint
    G
    (relatorEvenTowerReadoutPackageAsQNFReadoutCertificate G Lqnf Pkg)
    hsingle

def NeedsThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) : Prop :=
  Not (exists _E :
    ThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint G QNF, True)

theorem relatorEvenTowerQNFReadoutCertificate_discharge_singletonEndpointNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : ThreeFlavorRelatorEvenTowerQNFReadoutCertificate G QNF)
  (hsingle : HybridJointRestrictionSingleton H) :
  Not (NeedsThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint G QNF) := by
  intro hneed
  exact hneed
    ⟨relatorEvenTowerQNFReadoutCertificateAsSingletonEndpoint
        G
        K
        hsingle,
      True.intro⟩

theorem relatorEvenTowerReadoutPackageAndSingleton_discharge_singletonEndpointNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Lqnf : ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF)
  (Pkg : ThreeFlavorRelatorEvenTowerThreePointReadoutPackage (A := A))
  (hsingle : HybridJointRestrictionSingleton H) :
  Not (NeedsThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint G QNF) := by
  intro hneed
  exact hneed
    ⟨relatorEvenTowerReadoutPackageAndSingletonAsEndpoint
        G
        Lqnf
        Pkg
        hsingle,
      True.intro⟩

structure ThreeFlavorRelatorEvenTowerEndpointInput
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) where
  readoutPackage :
    ThreeFlavorRelatorEvenTowerThreePointReadoutPackage (A := A)
  qnfAlignment :
    ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF
  singleton :
    HybridJointRestrictionSingleton H

noncomputable def relatorEvenTowerEndpointInputAsSingletonEndpoint
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (I : ThreeFlavorRelatorEvenTowerEndpointInput G QNF) :
  ThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint G QNF :=
  relatorEvenTowerReadoutPackageAndSingletonAsEndpoint
    G
    I.qnfAlignment
    I.readoutPackage
    I.singleton

def NeedsThreeFlavorRelatorEvenTowerEndpointInput
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) : Prop :=
  Not (exists _I : ThreeFlavorRelatorEvenTowerEndpointInput G QNF, True)

theorem relatorEvenTowerEndpointInput_discharge_endpointNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (I : ThreeFlavorRelatorEvenTowerEndpointInput G QNF) :
  Not (NeedsThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint G QNF) :=
  relatorEvenTowerReadoutPackageAndSingleton_discharge_singletonEndpointNeed
    G
    I.qnfAlignment
    I.readoutPackage
    I.singleton

theorem relatorEvenTowerEndpointInput_discharge_endpointInputNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (I : ThreeFlavorRelatorEvenTowerEndpointInput G QNF) :
  Not (NeedsThreeFlavorRelatorEvenTowerEndpointInput G QNF) := by
  intro hneed
  exact hneed ⟨I, True.intro⟩

theorem relatorEvenTowerEndpointInput_interval_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (I : ThreeFlavorRelatorEvenTowerEndpointInput G QNF) :
  (relatorEvenTowerEndpointInputAsSingletonEndpoint G I).readoutCertificate.interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (relatorEvenTowerEndpointInputAsSingletonEndpoint G I).readoutCertificate.interval.upper :=
  (relatorEvenTowerEndpointInputAsSingletonEndpoint G I).readoutCertificate.interval_contains_gapRatio

theorem relatorEvenTowerEndpointInput_interval_upper_le_half
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (I : ThreeFlavorRelatorEvenTowerEndpointInput G QNF) :
  (relatorEvenTowerEndpointInputAsSingletonEndpoint G I).readoutCertificate.interval.upper <=
      (1 / 2 : ℚ) :=
  (relatorEvenTowerEndpointInputAsSingletonEndpoint G I).readoutCertificate.interval_upper_le_half

structure ThreeFlavorRelatorEvenTowerPrimitiveEndpointRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  strictMassSquaredOrdering :
    ThreeFlavorStrictMassSquaredOrdering (A := A)
  qnfAlignment :
    ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF
  singleton :
    HybridJointRestrictionSingleton H
  betaNumerator : Nat
  betaDenominator : Nat
  betaDenominator_pos :
    0 < betaDenominator
  deltaNumerator : Nat
  deltaDenominator : Nat
  deltaDenominator_pos :
    0 < deltaDenominator
  scaleNumerator : Nat
  scaleDenominator : Nat
  scaleDenominator_pos :
    0 < scaleDenominator
  parameterTableSourceDerived : Prop
  parameterTableSourceDerived_proof :
    parameterTableSourceDerived
  noHiddenRootEncodingInParameters : Prop
  noHiddenRootEncodingInParameters_proof :
    noHiddenRootEncodingInParameters
  level0_eq_evenTower :
    A.massSquaredLevelOf 0 =
      relatorEvenTowerLevelExpression
        (relatorEvenTowerNumeralParameterTableAsParameterTable
          { betaNumerator := betaNumerator
            betaDenominator := betaDenominator
            betaDenominator_pos := betaDenominator_pos
            deltaNumerator := deltaNumerator
            deltaDenominator := deltaDenominator
            deltaDenominator_pos := deltaDenominator_pos
            scaleNumerator := scaleNumerator
            scaleDenominator := scaleDenominator
            scaleDenominator_pos := scaleDenominator_pos
            parameterTableSourceDerived := parameterTableSourceDerived
            parameterTableSourceDerived_proof :=
              parameterTableSourceDerived_proof
            noHiddenRootEncodingInParameters :=
              noHiddenRootEncodingInParameters
            noHiddenRootEncodingInParameters_proof :=
              noHiddenRootEncodingInParameters_proof })
        1
  level1_eq_evenTower :
    A.massSquaredLevelOf 1 =
      relatorEvenTowerLevelExpression
        (relatorEvenTowerNumeralParameterTableAsParameterTable
          { betaNumerator := betaNumerator
            betaDenominator := betaDenominator
            betaDenominator_pos := betaDenominator_pos
            deltaNumerator := deltaNumerator
            deltaDenominator := deltaDenominator
            deltaDenominator_pos := deltaDenominator_pos
            scaleNumerator := scaleNumerator
            scaleDenominator := scaleDenominator
            scaleDenominator_pos := scaleDenominator_pos
            parameterTableSourceDerived := parameterTableSourceDerived
            parameterTableSourceDerived_proof :=
              parameterTableSourceDerived_proof
            noHiddenRootEncodingInParameters :=
              noHiddenRootEncodingInParameters
            noHiddenRootEncodingInParameters_proof :=
              noHiddenRootEncodingInParameters_proof })
        3
  level2_eq_evenTower :
    A.massSquaredLevelOf 2 =
      relatorEvenTowerLevelExpression
        (relatorEvenTowerNumeralParameterTableAsParameterTable
          { betaNumerator := betaNumerator
            betaDenominator := betaDenominator
            betaDenominator_pos := betaDenominator_pos
            deltaNumerator := deltaNumerator
            deltaDenominator := deltaDenominator
            deltaDenominator_pos := deltaDenominator_pos
            scaleNumerator := scaleNumerator
            scaleDenominator := scaleDenominator
            scaleDenominator_pos := scaleDenominator_pos
            parameterTableSourceDerived := parameterTableSourceDerived
            parameterTableSourceDerived_proof :=
              parameterTableSourceDerived_proof
            noHiddenRootEncodingInParameters :=
              noHiddenRootEncodingInParameters
            noHiddenRootEncodingInParameters_proof :=
              noHiddenRootEncodingInParameters_proof })
        5
  exponentScheduleFixedBySource : Prop
  exponentScheduleFixedBySource_proof :
    exponentScheduleFixedBySource
  generatedLevelsSameScope : Prop
  generatedLevelsSameScope_proof :
    generatedLevelsSameScope
  noEmpiricalRelatorEvenTowerImport : Prop
  noEmpiricalRelatorEvenTowerImport_proof :
    noEmpiricalRelatorEvenTowerImport
  noRelatorEvenTowerFitTuning : Prop
  noRelatorEvenTowerFitTuning_proof :
    noRelatorEvenTowerFitTuning

def relatorEvenTowerPrimitiveEndpointRowsAsNumeralParameterTable
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : ThreeFlavorRelatorEvenTowerPrimitiveEndpointRows G QNF) :
  ThreeFlavorRelatorEvenTowerNumeralParameterTable :=
  { betaNumerator := Rows.betaNumerator
    betaDenominator := Rows.betaDenominator
    betaDenominator_pos := Rows.betaDenominator_pos
    deltaNumerator := Rows.deltaNumerator
    deltaDenominator := Rows.deltaDenominator
    deltaDenominator_pos := Rows.deltaDenominator_pos
    scaleNumerator := Rows.scaleNumerator
    scaleDenominator := Rows.scaleDenominator
    scaleDenominator_pos := Rows.scaleDenominator_pos
    parameterTableSourceDerived := Rows.parameterTableSourceDerived
    parameterTableSourceDerived_proof :=
      Rows.parameterTableSourceDerived_proof
    noHiddenRootEncodingInParameters :=
      Rows.noHiddenRootEncodingInParameters
    noHiddenRootEncodingInParameters_proof :=
      Rows.noHiddenRootEncodingInParameters_proof }

def relatorEvenTowerPrimitiveEndpointRowsAsThreePointReadback
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : ThreeFlavorRelatorEvenTowerPrimitiveEndpointRows G QNF) :
  ThreeFlavorRelatorEvenTowerThreePointReadback
    (A := A)
    (relatorEvenTowerNumeralParameterTableAsParameterTable
      (relatorEvenTowerPrimitiveEndpointRowsAsNumeralParameterTable Rows)) :=
  { level0_eq_evenTower := Rows.level0_eq_evenTower
    level1_eq_evenTower := Rows.level1_eq_evenTower
    level2_eq_evenTower := Rows.level2_eq_evenTower
    exponentScheduleFixedBySource :=
      Rows.exponentScheduleFixedBySource
    exponentScheduleFixedBySource_proof :=
      Rows.exponentScheduleFixedBySource_proof
    generatedLevelsSameScope := Rows.generatedLevelsSameScope
    generatedLevelsSameScope_proof :=
      Rows.generatedLevelsSameScope_proof }

def relatorEvenTowerPrimitiveEndpointRowsAsAudit
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : ThreeFlavorRelatorEvenTowerPrimitiveEndpointRows G QNF) :
  ThreeFlavorRelatorEvenTowerAudit :=
  { noEmpiricalRelatorEvenTowerImport :=
      Rows.noEmpiricalRelatorEvenTowerImport
    noEmpiricalRelatorEvenTowerImport_proof :=
      Rows.noEmpiricalRelatorEvenTowerImport_proof
    noRelatorEvenTowerFitTuning :=
      Rows.noRelatorEvenTowerFitTuning
    noRelatorEvenTowerFitTuning_proof :=
      Rows.noRelatorEvenTowerFitTuning_proof }

noncomputable def relatorEvenTowerPrimitiveEndpointRowsAsEndpointInput
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : ThreeFlavorRelatorEvenTowerPrimitiveEndpointRows G QNF) :
  ThreeFlavorRelatorEvenTowerEndpointInput G QNF :=
  { readoutPackage :=
      { gapRatioAlgebraPasses := Rows.gapRatioAlgebraPasses
        strictMassSquaredOrdering := Rows.strictMassSquaredOrdering
        numeralParameterTable :=
          relatorEvenTowerPrimitiveEndpointRowsAsNumeralParameterTable Rows
        threePointReadback :=
          relatorEvenTowerPrimitiveEndpointRowsAsThreePointReadback Rows
        relatorAudit :=
          relatorEvenTowerPrimitiveEndpointRowsAsAudit Rows }
    qnfAlignment := Rows.qnfAlignment
    singleton := Rows.singleton }

noncomputable def relatorEvenTowerPrimitiveEndpointRowsAsSingletonEndpoint
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : ThreeFlavorRelatorEvenTowerPrimitiveEndpointRows G QNF) :
  ThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint G QNF :=
  relatorEvenTowerEndpointInputAsSingletonEndpoint
    G
    (relatorEvenTowerPrimitiveEndpointRowsAsEndpointInput Rows)

theorem relatorEvenTowerPrimitiveEndpointRows_interval_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : ThreeFlavorRelatorEvenTowerPrimitiveEndpointRows G QNF) :
  (relatorEvenTowerPrimitiveEndpointRowsAsSingletonEndpoint
      Rows).readoutCertificate.interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      (relatorEvenTowerPrimitiveEndpointRowsAsSingletonEndpoint
        Rows).readoutCertificate.interval.upper :=
  (relatorEvenTowerPrimitiveEndpointRowsAsSingletonEndpoint
    Rows).readoutCertificate.interval_contains_gapRatio

theorem relatorEvenTowerPrimitiveEndpointRows_interval_upper_le_half
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : ThreeFlavorRelatorEvenTowerPrimitiveEndpointRows G QNF) :
  (relatorEvenTowerPrimitiveEndpointRowsAsSingletonEndpoint
      Rows).readoutCertificate.interval.upper <= (1 / 2 : ℚ) :=
  (relatorEvenTowerPrimitiveEndpointRowsAsSingletonEndpoint
    Rows).readoutCertificate.interval_upper_le_half

theorem relatorEvenTowerPrimitiveEndpointRows_hasCurrentStandingEvaluation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : ThreeFlavorRelatorEvenTowerPrimitiveEndpointRows G QNF) :
  Nonempty (CurrentStandingRatioEvaluation C) :=
  ⟨(relatorEvenTowerPrimitiveEndpointRowsAsSingletonEndpoint
      Rows).currentStandingEvaluation⟩

theorem relatorEvenTowerPrimitiveEndpointRows_discharge_singletonEndpointNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : ThreeFlavorRelatorEvenTowerPrimitiveEndpointRows G QNF) :
  Not (NeedsThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint G QNF) :=
  relatorEvenTowerEndpointInput_discharge_endpointNeed
    G
    (relatorEvenTowerPrimitiveEndpointRowsAsEndpointInput Rows)

theorem relatorEvenTowerSingletonReadoutEndpoint_interval_contains_gapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (E : ThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint G QNF) :
  E.readoutCertificate.interval.lower <=
      threeFlavorGapRatio A.massSquaredLevelOf /\
    threeFlavorGapRatio A.massSquaredLevelOf <=
      E.readoutCertificate.interval.upper :=
  E.readoutCertificate.interval_contains_gapRatio

theorem relatorEvenTowerSingletonReadoutEndpoint_interval_upper_le_half
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (E : ThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint G QNF) :
  E.readoutCertificate.interval.upper <= (1 / 2 : ℚ) :=
  E.readoutCertificate.interval_upper_le_half

theorem relatorEvenTowerSingletonReadoutEndpoint_hasCurrentStandingEvaluation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (_E : ThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint G QNF) :
  Nonempty (CurrentStandingRatioEvaluation C) :=
  ⟨_E.currentStandingEvaluation⟩

/--
Concrete source rows extracted from Pajuhaan's Zenodo neutrino hierarchy code.

These rows are deliberately upstream of any branch-selection theorem: they
record the printed closed coefficient pipeline

`P_{1/R}(k) = 1 + beta k^2 + delta k^4`

with the `R` branch off and the source schedule `k = 1, 3, 5`.  The rationals
below are the finite decimal readback of the code run, not fitted neutrino
inputs and not definitions in terms of the selected root.
-/
def pajuhaanZenodoRelatorBeta : ℚ :=
  (780161359733586 : ℚ) / (10000000000000000000 : ℚ)

def pajuhaanZenodoRelatorDelta : ℚ :=
  (119354363008418 : ℚ) / (10000000000000000 : ℚ)

def pajuhaanZenodoRelatorScale : ℚ := 1

def pajuhaanZenodoRelatorP1OverR (k : ℚ) : ℚ :=
  1 + pajuhaanZenodoRelatorBeta * k ^ 2 +
    pajuhaanZenodoRelatorDelta * k ^ 4

def pajuhaanZenodoRelatorMassSquaredLevel (k : ℚ) : ℚ :=
  k ^ 4 * pajuhaanZenodoRelatorP1OverR k

/--
Line-level provenance for the Pajuhaan Zenodo source script supplied with the
neutrino hierarchy paper.  The line numbers refer to
`Neutrinos Mass Hierarchy.py` as inspected in the manuscript workspace.
-/
def pajuhaanZenodoRecordDOI : String :=
  "10.5281/zenodo.17169926"

def pajuhaanZenodoSourceCodeFile : String :=
  "Neutrinos Mass Hierarchy.py"

def pajuhaanZenodoCoefficientAuditLine : Nat := 210

def pajuhaanZenodoNoNeutrinoMassInputAuditLine : Nat := 212

def pajuhaanZenodoReportingOnlyAuditLine : Nat := 213

def pajuhaanZenodoBetaPrintLine : Nat := 249

def pajuhaanZenodoDeltaPrintLine : Nat := 250

def pajuhaanZenodoP1OverRDefinitionLine : Nat := 205

def pajuhaanZenodoP1OverRFormulaLine : Nat := 206

def pajuhaanZenodoP1OverRComputationLine : Nat := 207

def pajuhaanZenodoThreeFlavorRowsLine : Nat := 256

def pajuhaanZenodoR31ReadoutLine : Nat := 270

def pajuhaanZenodoR3ellReadoutLine : Nat := 271

def PajuhaanZenodoCoefficientPipelineSourceDerived : Prop :=
  pajuhaanZenodoRecordDOI = "10.5281/zenodo.17169926" ∧
  pajuhaanZenodoSourceCodeFile = "Neutrinos Mass Hierarchy.py" ∧
  pajuhaanZenodoCoefficientAuditLine = 210 ∧
  pajuhaanZenodoBetaPrintLine = 249 ∧
  pajuhaanZenodoDeltaPrintLine = 250 ∧
  pajuhaanZenodoP1OverRDefinitionLine = 205 ∧
  pajuhaanZenodoP1OverRFormulaLine = 206 ∧
  pajuhaanZenodoP1OverRComputationLine = 207 ∧
  pajuhaanZenodoThreeFlavorRowsLine = 256

def PajuhaanZenodoNoNeutrinoMassOrSplittingInputInCoefficientPipeline : Prop :=
  pajuhaanZenodoNoNeutrinoMassInputAuditLine = 212 ∧
  pajuhaanZenodoReportingOnlyAuditLine = 213 ∧
  pajuhaanZenodoCoefficientAuditLine = 210

def PajuhaanZenodoNoHiddenSelectedRootEncodingInSourceRows : Prop :=
  pajuhaanZenodoP1OverRDefinitionLine = 205 ∧
  pajuhaanZenodoP1OverRFormulaLine = 206 ∧
  pajuhaanZenodoP1OverRComputationLine = 207 ∧
  pajuhaanZenodoR31ReadoutLine = 270 ∧
  pajuhaanZenodoR3ellReadoutLine = 271

theorem pajuhaanZenodoCoefficientPipelineSourceDerived_proof :
  PajuhaanZenodoCoefficientPipelineSourceDerived := by
  norm_num [PajuhaanZenodoCoefficientPipelineSourceDerived,
    pajuhaanZenodoRecordDOI,
    pajuhaanZenodoSourceCodeFile,
    pajuhaanZenodoCoefficientAuditLine,
    pajuhaanZenodoBetaPrintLine,
    pajuhaanZenodoDeltaPrintLine,
    pajuhaanZenodoP1OverRDefinitionLine,
    pajuhaanZenodoP1OverRFormulaLine,
    pajuhaanZenodoP1OverRComputationLine,
    pajuhaanZenodoThreeFlavorRowsLine]

theorem pajuhaanZenodoNoNeutrinoMassOrSplittingInputInCoefficientPipeline_proof :
  PajuhaanZenodoNoNeutrinoMassOrSplittingInputInCoefficientPipeline := by
  norm_num
    [PajuhaanZenodoNoNeutrinoMassOrSplittingInputInCoefficientPipeline,
      pajuhaanZenodoNoNeutrinoMassInputAuditLine,
      pajuhaanZenodoReportingOnlyAuditLine,
      pajuhaanZenodoCoefficientAuditLine]

theorem pajuhaanZenodoNoHiddenSelectedRootEncodingInSourceRows_proof :
  PajuhaanZenodoNoHiddenSelectedRootEncodingInSourceRows := by
  norm_num
    [PajuhaanZenodoNoHiddenSelectedRootEncodingInSourceRows,
      pajuhaanZenodoP1OverRDefinitionLine,
      pajuhaanZenodoP1OverRFormulaLine,
      pajuhaanZenodoP1OverRComputationLine,
      pajuhaanZenodoR31ReadoutLine,
      pajuhaanZenodoR3ellReadoutLine]

def pajuhaanZenodoRelatorNumeralParameterTable :
  ThreeFlavorRelatorEvenTowerNumeralParameterTable :=
  { betaNumerator := 780161359733586
    betaDenominator := 10000000000000000000
    betaDenominator_pos := by norm_num
    deltaNumerator := 119354363008418
    deltaDenominator := 10000000000000000
    deltaDenominator_pos := by norm_num
    scaleNumerator := 1
    scaleDenominator := 1
    scaleDenominator_pos := by norm_num
    parameterTableSourceDerived :=
      PajuhaanZenodoCoefficientPipelineSourceDerived
    parameterTableSourceDerived_proof :=
      pajuhaanZenodoCoefficientPipelineSourceDerived_proof
    noHiddenRootEncodingInParameters :=
      PajuhaanZenodoNoHiddenSelectedRootEncodingInSourceRows
    noHiddenRootEncodingInParameters_proof :=
      pajuhaanZenodoNoHiddenSelectedRootEncodingInSourceRows_proof }

def pajuhaanZenodoRelatorParameterTable :
  ThreeFlavorRelatorEvenTowerParameterTable :=
  relatorEvenTowerNumeralParameterTableAsParameterTable
    pajuhaanZenodoRelatorNumeralParameterTable

theorem pajuhaanZenodoRelatorParameterTable_beta :
  pajuhaanZenodoRelatorParameterTable.beta =
      pajuhaanZenodoRelatorBeta := by
  rfl

theorem pajuhaanZenodoRelatorParameterTable_delta :
  pajuhaanZenodoRelatorParameterTable.delta =
      pajuhaanZenodoRelatorDelta := by
  rfl

theorem pajuhaanZenodoRelatorParameterTable_scale :
  pajuhaanZenodoRelatorParameterTable.normalizationScale =
      pajuhaanZenodoRelatorScale := by
  norm_num [pajuhaanZenodoRelatorParameterTable,
    pajuhaanZenodoRelatorNumeralParameterTable,
    relatorEvenTowerNumeralParameterTableAsParameterTable,
    pajuhaanZenodoRelatorScale]

theorem pajuhaanZenodoRelatorLevelExpression_eq_massSquaredLevel
  (k : ℚ) :
  relatorEvenTowerLevelExpression
      pajuhaanZenodoRelatorParameterTable k =
    pajuhaanZenodoRelatorMassSquaredLevel k := by
  unfold relatorEvenTowerLevelExpression
  unfold pajuhaanZenodoRelatorParameterTable
  unfold pajuhaanZenodoRelatorNumeralParameterTable
  unfold relatorEvenTowerNumeralParameterTableAsParameterTable
  unfold pajuhaanZenodoRelatorMassSquaredLevel
  unfold pajuhaanZenodoRelatorP1OverR
  unfold pajuhaanZenodoRelatorBeta
  unfold pajuhaanZenodoRelatorDelta
  ring_nf

theorem pajuhaanZenodoRelatorLevelExpression_one :
  relatorEvenTowerLevelExpression
      pajuhaanZenodoRelatorParameterTable 1 =
    pajuhaanZenodoRelatorMassSquaredLevel 1 := by
  exact pajuhaanZenodoRelatorLevelExpression_eq_massSquaredLevel 1

theorem pajuhaanZenodoRelatorLevelExpression_three :
  relatorEvenTowerLevelExpression
      pajuhaanZenodoRelatorParameterTable 3 =
    pajuhaanZenodoRelatorMassSquaredLevel 3 := by
  exact pajuhaanZenodoRelatorLevelExpression_eq_massSquaredLevel 3

theorem pajuhaanZenodoRelatorLevelExpression_five :
  relatorEvenTowerLevelExpression
      pajuhaanZenodoRelatorParameterTable 5 =
    pajuhaanZenodoRelatorMassSquaredLevel 5 := by
  exact pajuhaanZenodoRelatorLevelExpression_eq_massSquaredLevel 5

/-- Decimal readback printed by the source code for
`(Delta m^2_31)/(Delta m^2_21)`. -/
def pajuhaanZenodoR31DecimalReadout : ℚ :=
  (333904516045908 : ℚ) / (10000000000000 : ℚ)

/-- Decimal readback printed by the source code for the standing
`R_{3 ell} = R31 - 1/2` hierarchy ratio. -/
def pajuhaanZenodoR3ellDecimalReadout : ℚ :=
  (328904516045908 : ℚ) / (10000000000000 : ℚ)

/--
AASC uses the same-scope gap coordinate `solar/atmospheric`.  The Pajuhaan
script prints the inverse hierarchy coordinate `R31 = atmospheric/solar`; this
is the exact reciprocal of that printed finite decimal readback.
-/
def pajuhaanZenodoAASCStandingRatioReadout : ℚ :=
  (10000000000000 : ℚ) / (333904516045908 : ℚ)

theorem pajuhaanZenodoR31_eq_R3ell_plus_half :
  pajuhaanZenodoR31DecimalReadout =
    pajuhaanZenodoR3ellDecimalReadout + (1 / 2 : ℚ) := by
  norm_num [pajuhaanZenodoR31DecimalReadout,
    pajuhaanZenodoR3ellDecimalReadout]

theorem pajuhaanZenodoR31_mul_AASCStandingRatioReadout :
  pajuhaanZenodoR31DecimalReadout *
      pajuhaanZenodoAASCStandingRatioReadout = 1 := by
  norm_num [pajuhaanZenodoR31DecimalReadout,
    pajuhaanZenodoAASCStandingRatioReadout]

theorem pajuhaanZenodoAASCStandingRatioReadout_eq_inv_R31 :
  pajuhaanZenodoAASCStandingRatioReadout =
      (pajuhaanZenodoR31DecimalReadout)⁻¹ := by
  norm_num [pajuhaanZenodoAASCStandingRatioReadout,
    pajuhaanZenodoR31DecimalReadout]

theorem pajuhaanZenodoAASCStandingRatioReadout_eq_inv_R3ell_plus_half :
  pajuhaanZenodoAASCStandingRatioReadout =
      (pajuhaanZenodoR3ellDecimalReadout + (1 / 2 : ℚ))⁻¹ := by
  rw [← pajuhaanZenodoR31_eq_R3ell_plus_half]
  exact pajuhaanZenodoAASCStandingRatioReadout_eq_inv_R31

def pajuhaanZenodoRelatorMassSquaredRows : Fin 3 -> ℚ
  | ⟨0, _⟩ => pajuhaanZenodoRelatorMassSquaredLevel 1
  | ⟨1, _⟩ => pajuhaanZenodoRelatorMassSquaredLevel 3
  | ⟨_, _⟩ => pajuhaanZenodoRelatorMassSquaredLevel 5

def pajuhaanZenodoRelatorSourceGapRatio : ℚ :=
  threeFlavorGapRatio pajuhaanZenodoRelatorMassSquaredRows

def pajuhaanZenodoRelatorSourceInverseHierarchyRatio : ℚ :=
  (pajuhaanZenodoRelatorSourceGapRatio)⁻¹

def pajuhaanZenodoRelatorSourceR3ellRatio : ℚ :=
  pajuhaanZenodoRelatorSourceInverseHierarchyRatio - (1 / 2 : ℚ)

def pajuhaanZenodoAASCStandingRatioWindowLower : ℚ :=
  (299486814926010 : ℚ) / (10000000000000000 : ℚ)

def pajuhaanZenodoAASCStandingRatioWindowUpper : ℚ :=
  (299486814926012 : ℚ) / (10000000000000000 : ℚ)

def pajuhaanZenodoInverseHierarchyWindowLower : ℚ :=
  (333904516045907 : ℚ) / (10000000000000 : ℚ)

def pajuhaanZenodoInverseHierarchyWindowUpper : ℚ :=
  (333904516045908 : ℚ) / (10000000000000 : ℚ)

def pajuhaanZenodoR3ellWindowLower : ℚ :=
  (328904516045907 : ℚ) / (10000000000000 : ℚ)

def pajuhaanZenodoR3ellWindowUpper : ℚ :=
  (328904516045908 : ℚ) / (10000000000000 : ℚ)

theorem pajuhaanZenodoRelatorSourceGapRatio_in_decimalWindow :
  pajuhaanZenodoAASCStandingRatioWindowLower <=
      pajuhaanZenodoRelatorSourceGapRatio ∧
    pajuhaanZenodoRelatorSourceGapRatio <=
      pajuhaanZenodoAASCStandingRatioWindowUpper := by
  norm_num [pajuhaanZenodoAASCStandingRatioWindowLower,
    pajuhaanZenodoAASCStandingRatioWindowUpper,
    pajuhaanZenodoRelatorSourceGapRatio,
    pajuhaanZenodoRelatorMassSquaredRows,
    threeFlavorGapRatio,
    threeFlavorSolarGap,
    threeFlavorAtmosphericGap,
    pajuhaanZenodoRelatorMassSquaredLevel,
    pajuhaanZenodoRelatorP1OverR,
    pajuhaanZenodoRelatorBeta,
    pajuhaanZenodoRelatorDelta]

theorem pajuhaanZenodoRelatorSourceInverseHierarchyRatio_in_decimalWindow :
  pajuhaanZenodoInverseHierarchyWindowLower <=
      pajuhaanZenodoRelatorSourceInverseHierarchyRatio ∧
    pajuhaanZenodoRelatorSourceInverseHierarchyRatio <=
      pajuhaanZenodoInverseHierarchyWindowUpper := by
  norm_num [pajuhaanZenodoInverseHierarchyWindowLower,
    pajuhaanZenodoInverseHierarchyWindowUpper,
    pajuhaanZenodoRelatorSourceInverseHierarchyRatio,
    pajuhaanZenodoRelatorSourceGapRatio,
    pajuhaanZenodoRelatorMassSquaredRows,
    threeFlavorGapRatio,
    threeFlavorSolarGap,
    threeFlavorAtmosphericGap,
    pajuhaanZenodoRelatorMassSquaredLevel,
    pajuhaanZenodoRelatorP1OverR,
    pajuhaanZenodoRelatorBeta,
    pajuhaanZenodoRelatorDelta]

theorem pajuhaanZenodoRelatorSourceR3ellRatio_eq_inverse_minus_half :
  pajuhaanZenodoRelatorSourceR3ellRatio =
      pajuhaanZenodoRelatorSourceInverseHierarchyRatio - (1 / 2 : ℚ) := by
  rfl

theorem pajuhaanZenodoRelatorSourceR3ellRatio_in_decimalWindow :
  pajuhaanZenodoR3ellWindowLower <=
      pajuhaanZenodoRelatorSourceR3ellRatio ∧
    pajuhaanZenodoRelatorSourceR3ellRatio <=
      pajuhaanZenodoR3ellWindowUpper := by
  norm_num [pajuhaanZenodoR3ellWindowLower,
    pajuhaanZenodoR3ellWindowUpper,
    pajuhaanZenodoRelatorSourceR3ellRatio,
    pajuhaanZenodoRelatorSourceInverseHierarchyRatio,
    pajuhaanZenodoRelatorSourceGapRatio,
    pajuhaanZenodoRelatorMassSquaredRows,
    threeFlavorGapRatio,
    threeFlavorSolarGap,
    threeFlavorAtmosphericGap,
    pajuhaanZenodoRelatorMassSquaredLevel,
    pajuhaanZenodoRelatorP1OverR,
    pajuhaanZenodoRelatorBeta,
    pajuhaanZenodoRelatorDelta]

structure PajuhaanZenodoNeutrinoHierarchySourceReadout where
  beta_eq :
    pajuhaanZenodoRelatorParameterTable.beta =
      pajuhaanZenodoRelatorBeta
  delta_eq :
    pajuhaanZenodoRelatorParameterTable.delta =
      pajuhaanZenodoRelatorDelta
  scale_eq :
    pajuhaanZenodoRelatorParameterTable.normalizationScale =
      pajuhaanZenodoRelatorScale
  level_one_eq :
    relatorEvenTowerLevelExpression
        pajuhaanZenodoRelatorParameterTable 1 =
      pajuhaanZenodoRelatorMassSquaredLevel 1
  level_three_eq :
    relatorEvenTowerLevelExpression
        pajuhaanZenodoRelatorParameterTable 3 =
      pajuhaanZenodoRelatorMassSquaredLevel 3
  level_five_eq :
    relatorEvenTowerLevelExpression
        pajuhaanZenodoRelatorParameterTable 5 =
      pajuhaanZenodoRelatorMassSquaredLevel 5
  r31_eq_r3ell_plus_half :
    pajuhaanZenodoR31DecimalReadout =
      pajuhaanZenodoR3ellDecimalReadout + (1 / 2 : ℚ)
  aascStandingRatio_eq_inv_r31 :
    pajuhaanZenodoAASCStandingRatioReadout =
      (pajuhaanZenodoR31DecimalReadout)⁻¹
  sourceGapRatio_in_decimalWindow :
    pajuhaanZenodoAASCStandingRatioWindowLower <=
        pajuhaanZenodoRelatorSourceGapRatio ∧
      pajuhaanZenodoRelatorSourceGapRatio <=
        pajuhaanZenodoAASCStandingRatioWindowUpper
  sourceInverseHierarchy_in_decimalWindow :
    pajuhaanZenodoInverseHierarchyWindowLower <=
        pajuhaanZenodoRelatorSourceInverseHierarchyRatio ∧
      pajuhaanZenodoRelatorSourceInverseHierarchyRatio <=
        pajuhaanZenodoInverseHierarchyWindowUpper
  sourceR3ell_in_decimalWindow :
    pajuhaanZenodoR3ellWindowLower <=
        pajuhaanZenodoRelatorSourceR3ellRatio ∧
      pajuhaanZenodoRelatorSourceR3ellRatio <=
        pajuhaanZenodoR3ellWindowUpper
  coefficientPipelineSourceDerived : Prop
  coefficientPipelineSourceDerived_proof :
    coefficientPipelineSourceDerived
  noNeutrinoMassOrSplittingInputInCoefficientPipeline : Prop
  noNeutrinoMassOrSplittingInputInCoefficientPipeline_proof :
    noNeutrinoMassOrSplittingInputInCoefficientPipeline
  noHiddenSelectedRootEncodingInSourceRows : Prop
  noHiddenSelectedRootEncodingInSourceRows_proof :
    noHiddenSelectedRootEncodingInSourceRows

def pajuhaanZenodoNeutrinoHierarchySourceReadout :
  PajuhaanZenodoNeutrinoHierarchySourceReadout :=
  { beta_eq := pajuhaanZenodoRelatorParameterTable_beta
    delta_eq := pajuhaanZenodoRelatorParameterTable_delta
    scale_eq := pajuhaanZenodoRelatorParameterTable_scale
    level_one_eq := pajuhaanZenodoRelatorLevelExpression_one
    level_three_eq := pajuhaanZenodoRelatorLevelExpression_three
    level_five_eq := pajuhaanZenodoRelatorLevelExpression_five
    r31_eq_r3ell_plus_half := pajuhaanZenodoR31_eq_R3ell_plus_half
    aascStandingRatio_eq_inv_r31 :=
      pajuhaanZenodoAASCStandingRatioReadout_eq_inv_R31
    sourceGapRatio_in_decimalWindow :=
      pajuhaanZenodoRelatorSourceGapRatio_in_decimalWindow
    sourceInverseHierarchy_in_decimalWindow :=
      pajuhaanZenodoRelatorSourceInverseHierarchyRatio_in_decimalWindow
    sourceR3ell_in_decimalWindow :=
      pajuhaanZenodoRelatorSourceR3ellRatio_in_decimalWindow
    coefficientPipelineSourceDerived :=
      PajuhaanZenodoCoefficientPipelineSourceDerived
    coefficientPipelineSourceDerived_proof :=
      pajuhaanZenodoCoefficientPipelineSourceDerived_proof
    noNeutrinoMassOrSplittingInputInCoefficientPipeline :=
      PajuhaanZenodoNoNeutrinoMassOrSplittingInputInCoefficientPipeline
    noNeutrinoMassOrSplittingInputInCoefficientPipeline_proof :=
      pajuhaanZenodoNoNeutrinoMassOrSplittingInputInCoefficientPipeline_proof
    noHiddenSelectedRootEncodingInSourceRows :=
      PajuhaanZenodoNoHiddenSelectedRootEncodingInSourceRows
    noHiddenSelectedRootEncodingInSourceRows_proof :=
      pajuhaanZenodoNoHiddenSelectedRootEncodingInSourceRows_proof }

def NeedsPajuhaanZenodoNeutrinoHierarchySourceReadout : Prop :=
  Not (exists _R : PajuhaanZenodoNeutrinoHierarchySourceReadout, True)

theorem pajuhaanZenodoNeutrinoHierarchySourceReadout_discharge_need :
  Not NeedsPajuhaanZenodoNeutrinoHierarchySourceReadout := by
  intro hneed
  exact hneed
    ⟨pajuhaanZenodoNeutrinoHierarchySourceReadout, True.intro⟩

/--
Bridge from the hardened Pajuhaan source rows into the existing AASC Relator
endpoint socket.  The only remaining mathematical hypothesis here is the
same-scope row readback: the standing three-flavor algebra must identify its
three mass-squared levels with the source-generated `k = 1, 3, 5` rows.
-/
structure PajuhaanZenodoRelatorAASCAdmissionRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) where
  sourceReadout :
    PajuhaanZenodoNeutrinoHierarchySourceReadout
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  strictMassSquaredOrdering :
    ThreeFlavorStrictMassSquaredOrdering (A := A)
  qnfAlignment :
    ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF
  singleton :
    HybridJointRestrictionSingleton H
  level0_eq_source :
    A.massSquaredLevelOf 0 =
      pajuhaanZenodoRelatorMassSquaredLevel 1
  level1_eq_source :
    A.massSquaredLevelOf 1 =
      pajuhaanZenodoRelatorMassSquaredLevel 3
  level2_eq_source :
    A.massSquaredLevelOf 2 =
      pajuhaanZenodoRelatorMassSquaredLevel 5
  sameScopeRowReadbackByAASC : Prop
  sameScopeRowReadbackByAASC_proof :
    sameScopeRowReadbackByAASC

noncomputable def pajuhaanZenodoRelatorAASCAdmissionRowsAsPrimitiveEndpointRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : PajuhaanZenodoRelatorAASCAdmissionRows G QNF) :
  ThreeFlavorRelatorEvenTowerPrimitiveEndpointRows G QNF :=
  { gapRatioAlgebraPasses := Rows.gapRatioAlgebraPasses
    strictMassSquaredOrdering := Rows.strictMassSquaredOrdering
    qnfAlignment := Rows.qnfAlignment
    singleton := Rows.singleton
    betaNumerator := 780161359733586
    betaDenominator := 10000000000000000000
    betaDenominator_pos := by norm_num
    deltaNumerator := 119354363008418
    deltaDenominator := 10000000000000000
    deltaDenominator_pos := by norm_num
    scaleNumerator := 1
    scaleDenominator := 1
    scaleDenominator_pos := by norm_num
    parameterTableSourceDerived :=
      Rows.sourceReadout.coefficientPipelineSourceDerived
    parameterTableSourceDerived_proof :=
      Rows.sourceReadout.coefficientPipelineSourceDerived_proof
    noHiddenRootEncodingInParameters :=
      Rows.sourceReadout.noHiddenSelectedRootEncodingInSourceRows
    noHiddenRootEncodingInParameters_proof :=
      Rows.sourceReadout.noHiddenSelectedRootEncodingInSourceRows_proof
    level0_eq_evenTower := by
      exact Rows.level0_eq_source.trans
        pajuhaanZenodoRelatorLevelExpression_one.symm
    level1_eq_evenTower := by
      exact Rows.level1_eq_source.trans
        pajuhaanZenodoRelatorLevelExpression_three.symm
    level2_eq_evenTower := by
      exact Rows.level2_eq_source.trans
        pajuhaanZenodoRelatorLevelExpression_five.symm
    exponentScheduleFixedBySource :=
      Rows.sameScopeRowReadbackByAASC
    exponentScheduleFixedBySource_proof :=
      Rows.sameScopeRowReadbackByAASC_proof
    generatedLevelsSameScope :=
      Rows.sameScopeRowReadbackByAASC
    generatedLevelsSameScope_proof :=
      Rows.sameScopeRowReadbackByAASC_proof
    noEmpiricalRelatorEvenTowerImport :=
      Rows.sourceReadout.noNeutrinoMassOrSplittingInputInCoefficientPipeline
    noEmpiricalRelatorEvenTowerImport_proof :=
      Rows.sourceReadout.noNeutrinoMassOrSplittingInputInCoefficientPipeline_proof
    noRelatorEvenTowerFitTuning :=
      Rows.sourceReadout.noNeutrinoMassOrSplittingInputInCoefficientPipeline
    noRelatorEvenTowerFitTuning_proof :=
      Rows.sourceReadout.noNeutrinoMassOrSplittingInputInCoefficientPipeline_proof }

noncomputable def pajuhaanZenodoRelatorAASCAdmissionRowsAsSingletonEndpoint
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : PajuhaanZenodoRelatorAASCAdmissionRows G QNF) :
  ThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint G QNF :=
  relatorEvenTowerPrimitiveEndpointRowsAsSingletonEndpoint
    (pajuhaanZenodoRelatorAASCAdmissionRowsAsPrimitiveEndpointRows Rows)

def NeedsPajuhaanZenodoRelatorAASCAdmissionRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) : Prop :=
  Not (exists _Rows : PajuhaanZenodoRelatorAASCAdmissionRows G QNF, True)

theorem pajuhaanZenodoRelatorAASCAdmissionRows_discharge_singletonEndpointNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : PajuhaanZenodoRelatorAASCAdmissionRows G QNF) :
  Not (NeedsThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint G QNF) :=
  relatorEvenTowerPrimitiveEndpointRows_discharge_singletonEndpointNeed
    (pajuhaanZenodoRelatorAASCAdmissionRowsAsPrimitiveEndpointRows Rows)

theorem pajuhaanZenodoRelatorAASCAdmissionRows_hasCurrentStandingEvaluation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : PajuhaanZenodoRelatorAASCAdmissionRows G QNF) :
  Nonempty (CurrentStandingRatioEvaluation C) :=
  relatorEvenTowerPrimitiveEndpointRows_hasCurrentStandingEvaluation
    (pajuhaanZenodoRelatorAASCAdmissionRowsAsPrimitiveEndpointRows Rows)

theorem pajuhaanZenodoRelatorAASCAdmissionRows_gapRatio_eq_sourceGapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : PajuhaanZenodoRelatorAASCAdmissionRows G QNF) :
  threeFlavorGapRatio A.massSquaredLevelOf =
    pajuhaanZenodoRelatorSourceGapRatio := by
  unfold pajuhaanZenodoRelatorSourceGapRatio
  unfold threeFlavorGapRatio
  unfold threeFlavorSolarGap
  unfold threeFlavorAtmosphericGap
  simp [pajuhaanZenodoRelatorMassSquaredRows,
    Rows.level0_eq_source,
    Rows.level1_eq_source,
    Rows.level2_eq_source]

theorem pajuhaanZenodoRelatorAASCAdmissionRows_sourceInverseHierarchy_eq_gapRatio_inv
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : PajuhaanZenodoRelatorAASCAdmissionRows G QNF) :
  pajuhaanZenodoRelatorSourceInverseHierarchyRatio =
    (threeFlavorGapRatio A.massSquaredLevelOf)⁻¹ := by
  rw [pajuhaanZenodoRelatorAASCAdmissionRows_gapRatio_eq_sourceGapRatio Rows]
  rfl

theorem pajuhaanZenodoRelatorAASCAdmissionRows_gapRatio_in_decimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : PajuhaanZenodoRelatorAASCAdmissionRows G QNF) :
  pajuhaanZenodoAASCStandingRatioWindowLower <=
      threeFlavorGapRatio A.massSquaredLevelOf ∧
    threeFlavorGapRatio A.massSquaredLevelOf <=
      pajuhaanZenodoAASCStandingRatioWindowUpper := by
  rw [pajuhaanZenodoRelatorAASCAdmissionRows_gapRatio_eq_sourceGapRatio Rows]
  exact pajuhaanZenodoRelatorSourceGapRatio_in_decimalWindow

theorem pajuhaanZenodoRelatorAASCAdmissionRows_inverseHierarchy_in_decimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : PajuhaanZenodoRelatorAASCAdmissionRows G QNF) :
  pajuhaanZenodoInverseHierarchyWindowLower <=
      (threeFlavorGapRatio A.massSquaredLevelOf)⁻¹ ∧
    (threeFlavorGapRatio A.massSquaredLevelOf)⁻¹ <=
      pajuhaanZenodoInverseHierarchyWindowUpper := by
  have hsrc :=
    pajuhaanZenodoRelatorSourceInverseHierarchyRatio_in_decimalWindow
  rw [← pajuhaanZenodoRelatorAASCAdmissionRows_sourceInverseHierarchy_eq_gapRatio_inv
    Rows]
  exact hsrc

theorem pajuhaanZenodoRelatorAASCAdmissionRows_r3ell_in_decimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : PajuhaanZenodoRelatorAASCAdmissionRows G QNF) :
  pajuhaanZenodoR3ellWindowLower <=
      (threeFlavorGapRatio A.massSquaredLevelOf)⁻¹ - (1 / 2 : ℚ) ∧
    (threeFlavorGapRatio A.massSquaredLevelOf)⁻¹ - (1 / 2 : ℚ) <=
      pajuhaanZenodoR3ellWindowUpper := by
  have hsrc := pajuhaanZenodoRelatorSourceR3ellRatio_in_decimalWindow
  rw [← pajuhaanZenodoRelatorAASCAdmissionRows_sourceInverseHierarchy_eq_gapRatio_inv
    Rows]
  exact hsrc

theorem pajuhaanZenodoRelatorAASCAdmissionRows_selectedRoot_in_decimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : PajuhaanZenodoRelatorAASCAdmissionRows G QNF) :
  pajuhaanZenodoAASCStandingRatioWindowLower <= G.selectedRoot ∧
    G.selectedRoot <= pajuhaanZenodoAASCStandingRatioWindowUpper := by
  have hroot :
      G.selectedRoot = threeFlavorGapRatio A.massSquaredLevelOf :=
    algebraicClosedRootPresentation_selectedRoot_eq_gapRatio G
  rw [hroot]
  exact pajuhaanZenodoRelatorAASCAdmissionRows_gapRatio_in_decimalWindow Rows

/--
Named endpoint certificate for the Pajuhaan/Relator route after AASC row
admission.  This is the object a manuscript can cite for the numerical
readout: it bundles source provenance, same-scope row admission, singleton
evaluation, and the certified rational decimal windows.
-/
structure PajuhaanZenodoRelatorAASCReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) where
  admissionRows :
    PajuhaanZenodoRelatorAASCAdmissionRows G QNF
  singletonEndpoint :
    ThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint G QNF
  currentStandingEvaluation :
    CurrentStandingRatioEvaluation C
  gapRatio_in_decimalWindow :
    pajuhaanZenodoAASCStandingRatioWindowLower <=
        threeFlavorGapRatio A.massSquaredLevelOf ∧
      threeFlavorGapRatio A.massSquaredLevelOf <=
        pajuhaanZenodoAASCStandingRatioWindowUpper
  selectedRoot_in_decimalWindow :
    pajuhaanZenodoAASCStandingRatioWindowLower <= G.selectedRoot ∧
      G.selectedRoot <= pajuhaanZenodoAASCStandingRatioWindowUpper
  inverseHierarchy_in_decimalWindow :
    pajuhaanZenodoInverseHierarchyWindowLower <=
        (threeFlavorGapRatio A.massSquaredLevelOf)⁻¹ ∧
      (threeFlavorGapRatio A.massSquaredLevelOf)⁻¹ <=
        pajuhaanZenodoInverseHierarchyWindowUpper
  r3ell_in_decimalWindow :
    pajuhaanZenodoR3ellWindowLower <=
        (threeFlavorGapRatio A.massSquaredLevelOf)⁻¹ - (1 / 2 : ℚ) ∧
      (threeFlavorGapRatio A.massSquaredLevelOf)⁻¹ - (1 / 2 : ℚ) <=
        pajuhaanZenodoR3ellWindowUpper
  printedR31_is_inverseCoordinate :
    pajuhaanZenodoAASCStandingRatioReadout =
      (pajuhaanZenodoR31DecimalReadout)⁻¹

noncomputable def pajuhaanZenodoRelatorAASCReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : PajuhaanZenodoRelatorAASCAdmissionRows G QNF) :
  PajuhaanZenodoRelatorAASCReadoutCertificate G QNF :=
  { admissionRows := Rows
    singletonEndpoint :=
      pajuhaanZenodoRelatorAASCAdmissionRowsAsSingletonEndpoint Rows
    currentStandingEvaluation :=
      (pajuhaanZenodoRelatorAASCAdmissionRowsAsSingletonEndpoint
        Rows).currentStandingEvaluation
    gapRatio_in_decimalWindow :=
      pajuhaanZenodoRelatorAASCAdmissionRows_gapRatio_in_decimalWindow Rows
    selectedRoot_in_decimalWindow :=
      pajuhaanZenodoRelatorAASCAdmissionRows_selectedRoot_in_decimalWindow Rows
    inverseHierarchy_in_decimalWindow :=
      pajuhaanZenodoRelatorAASCAdmissionRows_inverseHierarchy_in_decimalWindow
        Rows
    r3ell_in_decimalWindow :=
      pajuhaanZenodoRelatorAASCAdmissionRows_r3ell_in_decimalWindow Rows
    printedR31_is_inverseCoordinate :=
      pajuhaanZenodoAASCStandingRatioReadout_eq_inv_R31 }

def NeedsPajuhaanZenodoRelatorAASCReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) : Prop :=
  Not (exists _K : PajuhaanZenodoRelatorAASCReadoutCertificate G QNF, True)

theorem pajuhaanZenodoRelatorAASCAdmissionRows_discharge_readoutCertificateNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : PajuhaanZenodoRelatorAASCAdmissionRows G QNF) :
  Not (NeedsPajuhaanZenodoRelatorAASCReadoutCertificate G QNF) := by
  intro hneed
  exact hneed
    ⟨pajuhaanZenodoRelatorAASCReadoutCertificate Rows, True.intro⟩

theorem pajuhaanZenodoRelatorAASCReadoutCertificate_selectedRoot_in_decimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : PajuhaanZenodoRelatorAASCReadoutCertificate G QNF) :
  pajuhaanZenodoAASCStandingRatioWindowLower <= G.selectedRoot ∧
    G.selectedRoot <= pajuhaanZenodoAASCStandingRatioWindowUpper :=
  K.selectedRoot_in_decimalWindow

theorem pajuhaanZenodoRelatorAASCReadoutCertificate_gapRatio_in_decimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : PajuhaanZenodoRelatorAASCReadoutCertificate G QNF) :
  pajuhaanZenodoAASCStandingRatioWindowLower <=
      threeFlavorGapRatio A.massSquaredLevelOf ∧
    threeFlavorGapRatio A.massSquaredLevelOf <=
      pajuhaanZenodoAASCStandingRatioWindowUpper :=
  K.gapRatio_in_decimalWindow

theorem pajuhaanZenodoRelatorAASCReadoutCertificate_inverseHierarchy_in_decimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : PajuhaanZenodoRelatorAASCReadoutCertificate G QNF) :
  pajuhaanZenodoInverseHierarchyWindowLower <=
      (threeFlavorGapRatio A.massSquaredLevelOf)⁻¹ ∧
    (threeFlavorGapRatio A.massSquaredLevelOf)⁻¹ <=
      pajuhaanZenodoInverseHierarchyWindowUpper :=
  K.inverseHierarchy_in_decimalWindow

theorem pajuhaanZenodoRelatorAASCReadoutCertificate_r3ell_in_decimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : PajuhaanZenodoRelatorAASCReadoutCertificate G QNF) :
  pajuhaanZenodoR3ellWindowLower <=
      (threeFlavorGapRatio A.massSquaredLevelOf)⁻¹ - (1 / 2 : ℚ) ∧
    (threeFlavorGapRatio A.massSquaredLevelOf)⁻¹ - (1 / 2 : ℚ) <=
      pajuhaanZenodoR3ellWindowUpper :=
  K.r3ell_in_decimalWindow

theorem pajuhaanZenodoRelatorAASCReadoutCertificate_selectedRoot_inverse_in_decimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : PajuhaanZenodoRelatorAASCReadoutCertificate G QNF) :
  pajuhaanZenodoInverseHierarchyWindowLower <= G.selectedRoot⁻¹ ∧
    G.selectedRoot⁻¹ <= pajuhaanZenodoInverseHierarchyWindowUpper := by
  have hroot :
      G.selectedRoot = threeFlavorGapRatio A.massSquaredLevelOf :=
    algebraicClosedRootPresentation_selectedRoot_eq_gapRatio G
  rw [hroot]
  exact K.inverseHierarchy_in_decimalWindow

theorem pajuhaanZenodoRelatorAASCReadoutCertificate_selectedRoot_r3ell_in_decimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : PajuhaanZenodoRelatorAASCReadoutCertificate G QNF) :
  pajuhaanZenodoR3ellWindowLower <= G.selectedRoot⁻¹ - (1 / 2 : ℚ) ∧
    G.selectedRoot⁻¹ - (1 / 2 : ℚ) <= pajuhaanZenodoR3ellWindowUpper := by
  have hroot :
      G.selectedRoot = threeFlavorGapRatio A.massSquaredLevelOf :=
    algebraicClosedRootPresentation_selectedRoot_eq_gapRatio G
  rw [hroot]
  exact K.r3ell_in_decimalWindow

/--
Final compact readout theorem for the Pajuhaan/Relator route.

Once the Pajuhaan source rows are admitted as the same-scope AASC rows, the
current standing evaluation exists and both numerical coordinates are locked:
the AASC standing coordinate `rho = solar/atmospheric`, and the inverse
hierarchy coordinate printed by the source script.
-/
theorem pajuhaanZenodoRelatorAASCAdmissionRows_finalNumericalReadout
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : PajuhaanZenodoRelatorAASCAdmissionRows G QNF) :
  Nonempty (CurrentStandingRatioEvaluation C) ∧
    (pajuhaanZenodoAASCStandingRatioWindowLower <= G.selectedRoot ∧
      G.selectedRoot <= pajuhaanZenodoAASCStandingRatioWindowUpper) ∧
    (pajuhaanZenodoInverseHierarchyWindowLower <= G.selectedRoot⁻¹ ∧
      G.selectedRoot⁻¹ <= pajuhaanZenodoInverseHierarchyWindowUpper) ∧
    (pajuhaanZenodoR3ellWindowLower <= G.selectedRoot⁻¹ - (1 / 2 : ℚ) ∧
      G.selectedRoot⁻¹ - (1 / 2 : ℚ) <= pajuhaanZenodoR3ellWindowUpper) := by
  let K := pajuhaanZenodoRelatorAASCReadoutCertificate Rows
  exact
    ⟨⟨K.currentStandingEvaluation⟩,
      K.selectedRoot_in_decimalWindow,
      pajuhaanZenodoRelatorAASCReadoutCertificate_selectedRoot_inverse_in_decimalWindow
        K,
      pajuhaanZenodoRelatorAASCReadoutCertificate_selectedRoot_r3ell_in_decimalWindow
        K⟩

/--
AASC-facing alias for the external-source row-admission object.  The original
name records provenance; this alias is the manuscript-facing AASC endpoint
interface.
-/
abbrev AASCRelatorSameScopeAdmissionRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) :=
  PajuhaanZenodoRelatorAASCAdmissionRows G QNF

/--
AASC-facing alias for the bundled numerical readout certificate.
-/
abbrev AASCRelatorNumericalReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) :=
  PajuhaanZenodoRelatorAASCReadoutCertificate G QNF

noncomputable def aascRelatorNumericalReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCRelatorSameScopeAdmissionRows G QNF) :
  AASCRelatorNumericalReadoutCertificate G QNF :=
  pajuhaanZenodoRelatorAASCReadoutCertificate Rows

noncomputable def aascRelatorSameScopeAdmissionRowsAsPrimitiveEndpointRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCRelatorSameScopeAdmissionRows G QNF) :
  ThreeFlavorRelatorEvenTowerPrimitiveEndpointRows G QNF :=
  pajuhaanZenodoRelatorAASCAdmissionRowsAsPrimitiveEndpointRows Rows

noncomputable def aascRelatorSameScopeAdmissionRowsAsSingletonEndpoint
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCRelatorSameScopeAdmissionRows G QNF) :
  ThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint G QNF :=
  pajuhaanZenodoRelatorAASCAdmissionRowsAsSingletonEndpoint Rows

theorem aascRelatorSameScopeAdmissionRows_hasCurrentStandingEvaluation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCRelatorSameScopeAdmissionRows G QNF) :
  Nonempty (CurrentStandingRatioEvaluation C) :=
  pajuhaanZenodoRelatorAASCAdmissionRows_hasCurrentStandingEvaluation Rows

theorem aascRelatorSameScopeAdmissionRows_finalNumericalReadout
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCRelatorSameScopeAdmissionRows G QNF) :
  Nonempty (CurrentStandingRatioEvaluation C) ∧
    (pajuhaanZenodoAASCStandingRatioWindowLower <= G.selectedRoot ∧
      G.selectedRoot <= pajuhaanZenodoAASCStandingRatioWindowUpper) ∧
    (pajuhaanZenodoInverseHierarchyWindowLower <= G.selectedRoot⁻¹ ∧
      G.selectedRoot⁻¹ <= pajuhaanZenodoInverseHierarchyWindowUpper) ∧
    (pajuhaanZenodoR3ellWindowLower <= G.selectedRoot⁻¹ - (1 / 2 : ℚ) ∧
      G.selectedRoot⁻¹ - (1 / 2 : ℚ) <= pajuhaanZenodoR3ellWindowUpper) :=
  pajuhaanZenodoRelatorAASCAdmissionRows_finalNumericalReadout Rows

def AASCRelatorCoefficientPipelineSourceDerived : Prop :=
  PajuhaanZenodoCoefficientPipelineSourceDerived

theorem aascRelatorCoefficientPipelineSourceDerived_proof :
  AASCRelatorCoefficientPipelineSourceDerived :=
  pajuhaanZenodoCoefficientPipelineSourceDerived_proof

def AASCRelatorNoNeutrinoMassOrSplittingInputInCoefficientPipeline : Prop :=
  PajuhaanZenodoNoNeutrinoMassOrSplittingInputInCoefficientPipeline

theorem aascRelatorNoNeutrinoMassOrSplittingInputInCoefficientPipeline_proof :
  AASCRelatorNoNeutrinoMassOrSplittingInputInCoefficientPipeline :=
  pajuhaanZenodoNoNeutrinoMassOrSplittingInputInCoefficientPipeline_proof

def AASCRelatorNoHiddenSelectedRootEncodingInSourceRows : Prop :=
  PajuhaanZenodoNoHiddenSelectedRootEncodingInSourceRows

theorem aascRelatorNoHiddenSelectedRootEncodingInSourceRows_proof :
  AASCRelatorNoHiddenSelectedRootEncodingInSourceRows :=
  pajuhaanZenodoNoHiddenSelectedRootEncodingInSourceRows_proof

def aascRelatorBeta : ℚ := pajuhaanZenodoRelatorBeta

def aascRelatorDelta : ℚ := pajuhaanZenodoRelatorDelta

def aascRelatorScale : ℚ := pajuhaanZenodoRelatorScale

def aascRelatorP1OverR (k : ℚ) : ℚ :=
  pajuhaanZenodoRelatorP1OverR k

def aascRelatorMassSquaredLevel (k : ℚ) : ℚ :=
  pajuhaanZenodoRelatorMassSquaredLevel k

def aascRelatorNumeralParameterTable :
  ThreeFlavorRelatorEvenTowerNumeralParameterTable :=
  pajuhaanZenodoRelatorNumeralParameterTable

def aascRelatorR31DecimalReadout : ℚ :=
  pajuhaanZenodoR31DecimalReadout

def aascRelatorR3ellDecimalReadout : ℚ :=
  pajuhaanZenodoR3ellDecimalReadout

def aascRelatorStandingRatioReadout : ℚ :=
  pajuhaanZenodoAASCStandingRatioReadout

theorem aascRelatorR31_eq_R3ell_plus_half :
  aascRelatorR31DecimalReadout =
    aascRelatorR3ellDecimalReadout + (1 / 2 : ℚ) := by
  exact pajuhaanZenodoR31_eq_R3ell_plus_half

theorem aascRelatorStandingRatioReadout_eq_inv_R31 :
  aascRelatorStandingRatioReadout =
      (aascRelatorR31DecimalReadout)⁻¹ := by
  exact pajuhaanZenodoAASCStandingRatioReadout_eq_inv_R31

theorem aascRelatorStandingRatioReadout_eq_inv_R3ell_plus_half :
  aascRelatorStandingRatioReadout =
      (aascRelatorR3ellDecimalReadout + (1 / 2 : ℚ))⁻¹ := by
  exact pajuhaanZenodoAASCStandingRatioReadout_eq_inv_R3ell_plus_half

theorem aascRelatorSourceGapRatio_in_decimalWindow :
  pajuhaanZenodoAASCStandingRatioWindowLower <=
      pajuhaanZenodoRelatorSourceGapRatio ∧
    pajuhaanZenodoRelatorSourceGapRatio <=
      pajuhaanZenodoAASCStandingRatioWindowUpper :=
  pajuhaanZenodoRelatorSourceGapRatio_in_decimalWindow

theorem aascRelatorSourceInverseHierarchyRatio_in_decimalWindow :
  pajuhaanZenodoInverseHierarchyWindowLower <=
      pajuhaanZenodoRelatorSourceInverseHierarchyRatio ∧
    pajuhaanZenodoRelatorSourceInverseHierarchyRatio <=
      pajuhaanZenodoInverseHierarchyWindowUpper :=
  pajuhaanZenodoRelatorSourceInverseHierarchyRatio_in_decimalWindow

theorem aascRelatorSourceR3ellRatio_in_decimalWindow :
  pajuhaanZenodoR3ellWindowLower <=
      pajuhaanZenodoRelatorSourceR3ellRatio ∧
    pajuhaanZenodoRelatorSourceR3ellRatio <=
      pajuhaanZenodoR3ellWindowUpper :=
  pajuhaanZenodoRelatorSourceR3ellRatio_in_decimalWindow

theorem aascRelatorNumericalReadoutCertificate_selectedRoot_in_decimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : AASCRelatorNumericalReadoutCertificate G QNF) :
  pajuhaanZenodoAASCStandingRatioWindowLower <= G.selectedRoot ∧
    G.selectedRoot <= pajuhaanZenodoAASCStandingRatioWindowUpper :=
  pajuhaanZenodoRelatorAASCReadoutCertificate_selectedRoot_in_decimalWindow K

theorem aascRelatorNumericalReadoutCertificate_selectedRoot_inverse_in_decimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : AASCRelatorNumericalReadoutCertificate G QNF) :
  pajuhaanZenodoInverseHierarchyWindowLower <= G.selectedRoot⁻¹ ∧
    G.selectedRoot⁻¹ <= pajuhaanZenodoInverseHierarchyWindowUpper :=
  pajuhaanZenodoRelatorAASCReadoutCertificate_selectedRoot_inverse_in_decimalWindow K

theorem aascRelatorNumericalReadoutCertificate_selectedRoot_r3ell_in_decimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : AASCRelatorNumericalReadoutCertificate G QNF) :
  pajuhaanZenodoR3ellWindowLower <= G.selectedRoot⁻¹ - (1 / 2 : ℚ) ∧
    G.selectedRoot⁻¹ - (1 / 2 : ℚ) <= pajuhaanZenodoR3ellWindowUpper :=
  pajuhaanZenodoRelatorAASCReadoutCertificate_selectedRoot_r3ell_in_decimalWindow K

/--
Neutral manuscript-facing alias for the AASC same-scope row admission object.
The source citation is recorded separately; this is the structural AASC
interface used by the paper.
-/
abbrev AASCNeutrinoReadoutSameScopeAdmissionRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) :=
  AASCRelatorSameScopeAdmissionRows G QNF

abbrev AASCNeutrinoNumericalReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) :=
  AASCRelatorNumericalReadoutCertificate G QNF

noncomputable def aascNeutrinoNumericalReadoutCertificate
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoReadoutSameScopeAdmissionRows G QNF) :
  AASCNeutrinoNumericalReadoutCertificate G QNF :=
  aascRelatorNumericalReadoutCertificate Rows

noncomputable def aascNeutrinoSameScopeAdmissionRowsAsPrimitiveEndpointRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoReadoutSameScopeAdmissionRows G QNF) :
  ThreeFlavorRelatorEvenTowerPrimitiveEndpointRows G QNF :=
  aascRelatorSameScopeAdmissionRowsAsPrimitiveEndpointRows Rows

noncomputable def aascNeutrinoSameScopeAdmissionRowsAsSingletonEndpoint
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoReadoutSameScopeAdmissionRows G QNF) :
  ThreeFlavorRelatorEvenTowerSingletonReadoutEndpoint G QNF :=
  aascRelatorSameScopeAdmissionRowsAsSingletonEndpoint Rows

theorem aascNeutrinoSameScopeAdmissionRows_hasCurrentStandingEvaluation
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoReadoutSameScopeAdmissionRows G QNF) :
  Nonempty (CurrentStandingRatioEvaluation C) :=
  aascRelatorSameScopeAdmissionRows_hasCurrentStandingEvaluation Rows

def AASCNeutrinoCoefficientPipelineSourceDerived : Prop :=
  AASCRelatorCoefficientPipelineSourceDerived

theorem aascNeutrinoCoefficientPipelineSourceDerived_proof :
  AASCNeutrinoCoefficientPipelineSourceDerived :=
  aascRelatorCoefficientPipelineSourceDerived_proof

def AASCNeutrinoNoMassOrSplittingInputInCoefficientPipeline : Prop :=
  AASCRelatorNoNeutrinoMassOrSplittingInputInCoefficientPipeline

theorem aascNeutrinoNoMassOrSplittingInputInCoefficientPipeline_proof :
  AASCNeutrinoNoMassOrSplittingInputInCoefficientPipeline :=
  aascRelatorNoNeutrinoMassOrSplittingInputInCoefficientPipeline_proof

def AASCNeutrinoNoHiddenSelectedRootEncodingInSourceRows : Prop :=
  AASCRelatorNoHiddenSelectedRootEncodingInSourceRows

theorem aascNeutrinoNoHiddenSelectedRootEncodingInSourceRows_proof :
  AASCNeutrinoNoHiddenSelectedRootEncodingInSourceRows :=
  aascRelatorNoHiddenSelectedRootEncodingInSourceRows_proof

def aascNeutrinoBeta : ℚ := aascRelatorBeta

def aascNeutrinoDelta : ℚ := aascRelatorDelta

def aascNeutrinoScale : ℚ := aascRelatorScale

def aascNeutrinoP1OverR (k : ℚ) : ℚ := aascRelatorP1OverR k

def aascNeutrinoMassSquaredLevel (k : ℚ) : ℚ :=
  aascRelatorMassSquaredLevel k

def aascNeutrinoNumeralParameterTable :
  ThreeFlavorRelatorEvenTowerNumeralParameterTable :=
  aascRelatorNumeralParameterTable

theorem aascNeutrinoR31_eq_R3ell_plus_half :
  aascRelatorR31DecimalReadout =
    aascRelatorR3ellDecimalReadout + (1 / 2 : ℚ) :=
  aascRelatorR31_eq_R3ell_plus_half

theorem aascNeutrinoStandingRatioReadout_eq_inv_R31 :
  aascRelatorStandingRatioReadout =
      (aascRelatorR31DecimalReadout)⁻¹ :=
  aascRelatorStandingRatioReadout_eq_inv_R31

theorem aascNeutrinoStandingRatioReadout_eq_inv_R3ell_plus_half :
  aascRelatorStandingRatioReadout =
      (aascRelatorR3ellDecimalReadout + (1 / 2 : ℚ))⁻¹ :=
  aascRelatorStandingRatioReadout_eq_inv_R3ell_plus_half

theorem aascNeutrinoSourceGapRatio_in_decimalWindow :
  pajuhaanZenodoAASCStandingRatioWindowLower <=
      pajuhaanZenodoRelatorSourceGapRatio ∧
    pajuhaanZenodoRelatorSourceGapRatio <=
      pajuhaanZenodoAASCStandingRatioWindowUpper :=
  aascRelatorSourceGapRatio_in_decimalWindow

theorem aascNeutrinoSourceInverseHierarchyRatio_in_decimalWindow :
  pajuhaanZenodoInverseHierarchyWindowLower <=
      pajuhaanZenodoRelatorSourceInverseHierarchyRatio ∧
    pajuhaanZenodoRelatorSourceInverseHierarchyRatio <=
      pajuhaanZenodoInverseHierarchyWindowUpper :=
  aascRelatorSourceInverseHierarchyRatio_in_decimalWindow

theorem aascNeutrinoSourceR3ellRatio_in_decimalWindow :
  pajuhaanZenodoR3ellWindowLower <=
      pajuhaanZenodoRelatorSourceR3ellRatio ∧
    pajuhaanZenodoRelatorSourceR3ellRatio <=
      pajuhaanZenodoR3ellWindowUpper :=
  aascRelatorSourceR3ellRatio_in_decimalWindow

theorem aascNeutrinoNumericalReadoutCertificate_selectedRoot_in_decimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : AASCNeutrinoNumericalReadoutCertificate G QNF) :
  pajuhaanZenodoAASCStandingRatioWindowLower <= G.selectedRoot ∧
    G.selectedRoot <= pajuhaanZenodoAASCStandingRatioWindowUpper :=
  aascRelatorNumericalReadoutCertificate_selectedRoot_in_decimalWindow K

theorem aascNeutrinoNumericalReadoutCertificate_selectedRoot_inverse_in_decimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : AASCNeutrinoNumericalReadoutCertificate G QNF) :
  pajuhaanZenodoInverseHierarchyWindowLower <= G.selectedRoot⁻¹ ∧
    G.selectedRoot⁻¹ <= pajuhaanZenodoInverseHierarchyWindowUpper :=
  aascRelatorNumericalReadoutCertificate_selectedRoot_inverse_in_decimalWindow K

theorem aascNeutrinoNumericalReadoutCertificate_selectedRoot_r3ell_in_decimalWindow
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (K : AASCNeutrinoNumericalReadoutCertificate G QNF) :
  pajuhaanZenodoR3ellWindowLower <= G.selectedRoot⁻¹ - (1 / 2 : ℚ) ∧
    G.selectedRoot⁻¹ - (1 / 2 : ℚ) <= pajuhaanZenodoR3ellWindowUpper :=
  aascRelatorNumericalReadoutCertificate_selectedRoot_r3ell_in_decimalWindow K

theorem aascNeutrinoSameScopeAdmissionRows_finalNumericalReadout
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoReadoutSameScopeAdmissionRows G QNF) :
  Nonempty (CurrentStandingRatioEvaluation C) ∧
    (pajuhaanZenodoAASCStandingRatioWindowLower <= G.selectedRoot ∧
      G.selectedRoot <= pajuhaanZenodoAASCStandingRatioWindowUpper) ∧
    (pajuhaanZenodoInverseHierarchyWindowLower <= G.selectedRoot⁻¹ ∧
      G.selectedRoot⁻¹ <= pajuhaanZenodoInverseHierarchyWindowUpper) ∧
    (pajuhaanZenodoR3ellWindowLower <= G.selectedRoot⁻¹ - (1 / 2 : ℚ) ∧
      G.selectedRoot⁻¹ - (1 / 2 : ℚ) <= pajuhaanZenodoR3ellWindowUpper) :=
  aascRelatorSameScopeAdmissionRows_finalNumericalReadout Rows

/--
Corpus-shaped AASC certificate for admitting the source-generated rows as the
same-scope three-flavor rows.

The previous socket `AASCNeutrinoReadoutSameScopeAdmissionRows` is deliberately
small: it only asks for row equality plus the usual QNF/singleton guards.  This
object is the stronger audit object used to discharge that socket from AASC
standing material.  Its fields separate the structural neutrino standing
claims, source-row provenance, quotient/skin stability, and the actual row
readback equations.
-/
structure AASCNeutrinoSourceRowStandingAdmission
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) where
  gapRatioAlgebraPasses :
    ThreeFlavorGapRatioAlgebraPasses A
  strictMassSquaredOrdering :
    ThreeFlavorStrictMassSquaredOrdering (A := A)
  qnfAlignment :
    ThreeFlavorQuotientNormalFormRationalPolynomialAlignment G QNF
  singleton :
    HybridJointRestrictionSingleton H
  level0_eq_aascSource :
    A.massSquaredLevelOf 0 = aascNeutrinoMassSquaredLevel 1
  level1_eq_aascSource :
    A.massSquaredLevelOf 1 = aascNeutrinoMassSquaredLevel 3
  level2_eq_aascSource :
    A.massSquaredLevelOf 2 = aascNeutrinoMassSquaredLevel 5
  finitePMNSInvariantWitnessScope : Prop
  finitePMNSInvariantWitnessScope_proof :
    finitePMNSInvariantWitnessScope
  massSquaredSplittingWitnessStanding : Prop
  massSquaredSplittingWitnessStanding_proof :
    massSquaredSplittingWitnessStanding
  sameScopeOscillationRivalExhaustion : Prop
  sameScopeOscillationRivalExhaustion_proof :
    sameScopeOscillationRivalExhaustion
  bridgeAnchorAdmissibleForRowReadback : Prop
  bridgeAnchorAdmissibleForRowReadback_proof :
    bridgeAnchorAdmissibleForRowReadback
  evidenceLedgerCompleteForReadout : Prop
  evidenceLedgerCompleteForReadout_proof :
    evidenceLedgerCompleteForReadout
  sourceRowsSameStandingCarrier : Prop
  sourceRowsSameStandingCarrier_proof :
    sourceRowsSameStandingCarrier
  quotientSkinTransportCompatible : Prop
  quotientSkinTransportCompatible_proof :
    quotientSkinTransportCompatible
  noEmpiricalImportByAASC :
    AASCNeutrinoNoMassOrSplittingInputInCoefficientPipeline
  noHiddenSelectedRootEncodingByAASC :
    AASCNeutrinoNoHiddenSelectedRootEncodingInSourceRows

def AASCNeutrinoSourceRowStandingAdmission.sameScopeReadbackAudit
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoSourceRowStandingAdmission G QNF) : Prop :=
  Rows.finitePMNSInvariantWitnessScope ∧
    Rows.massSquaredSplittingWitnessStanding ∧
    Rows.sameScopeOscillationRivalExhaustion ∧
    Rows.bridgeAnchorAdmissibleForRowReadback ∧
    Rows.evidenceLedgerCompleteForReadout ∧
    Rows.sourceRowsSameStandingCarrier ∧
    Rows.quotientSkinTransportCompatible ∧
    AASCNeutrinoCoefficientPipelineSourceDerived ∧
    AASCNeutrinoNoMassOrSplittingInputInCoefficientPipeline ∧
    AASCNeutrinoNoHiddenSelectedRootEncodingInSourceRows

theorem AASCNeutrinoSourceRowStandingAdmission.sameScopeReadbackAudit_proof
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoSourceRowStandingAdmission G QNF) :
  Rows.sameScopeReadbackAudit := by
  exact
    ⟨Rows.finitePMNSInvariantWitnessScope_proof,
      Rows.massSquaredSplittingWitnessStanding_proof,
      Rows.sameScopeOscillationRivalExhaustion_proof,
      Rows.bridgeAnchorAdmissibleForRowReadback_proof,
      Rows.evidenceLedgerCompleteForReadout_proof,
      Rows.sourceRowsSameStandingCarrier_proof,
      Rows.quotientSkinTransportCompatible_proof,
      aascNeutrinoCoefficientPipelineSourceDerived_proof,
      Rows.noEmpiricalImportByAASC,
      Rows.noHiddenSelectedRootEncodingByAASC⟩

noncomputable def AASCNeutrinoSourceRowStandingAdmission.toSameScopeAdmissionRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoSourceRowStandingAdmission G QNF) :
  AASCNeutrinoReadoutSameScopeAdmissionRows G QNF :=
  { sourceReadout := pajuhaanZenodoNeutrinoHierarchySourceReadout
    gapRatioAlgebraPasses := Rows.gapRatioAlgebraPasses
    strictMassSquaredOrdering := Rows.strictMassSquaredOrdering
    qnfAlignment := Rows.qnfAlignment
    singleton := Rows.singleton
    level0_eq_source := by
      simpa [aascNeutrinoMassSquaredLevel, aascRelatorMassSquaredLevel]
        using Rows.level0_eq_aascSource
    level1_eq_source := by
      simpa [aascNeutrinoMassSquaredLevel, aascRelatorMassSquaredLevel]
        using Rows.level1_eq_aascSource
    level2_eq_source := by
      simpa [aascNeutrinoMassSquaredLevel, aascRelatorMassSquaredLevel]
        using Rows.level2_eq_aascSource
    sameScopeRowReadbackByAASC := Rows.sameScopeReadbackAudit
    sameScopeRowReadbackByAASC_proof :=
      Rows.sameScopeReadbackAudit_proof }

def NeedsAASCNeutrinoReadoutSameScopeAdmissionRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  (G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P)
  (QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A) : Prop :=
  Not (exists _Rows : AASCNeutrinoReadoutSameScopeAdmissionRows G QNF, True)

theorem AASCNeutrinoSourceRowStandingAdmission.discharge_sameScopeAdmissionRows
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoSourceRowStandingAdmission G QNF) :
  Not (NeedsAASCNeutrinoReadoutSameScopeAdmissionRows G QNF) := by
  intro hneed
  exact hneed
    ⟨Rows.toSameScopeAdmissionRows, True.intro⟩

theorem AASCNeutrinoSourceRowStandingAdmission.finalNumericalReadout
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoSourceRowStandingAdmission G QNF) :
  Nonempty (CurrentStandingRatioEvaluation C) ∧
    (pajuhaanZenodoAASCStandingRatioWindowLower <= G.selectedRoot ∧
      G.selectedRoot <= pajuhaanZenodoAASCStandingRatioWindowUpper) ∧
    (pajuhaanZenodoInverseHierarchyWindowLower <= G.selectedRoot⁻¹ ∧
      G.selectedRoot⁻¹ <= pajuhaanZenodoInverseHierarchyWindowUpper) ∧
    (pajuhaanZenodoR3ellWindowLower <= G.selectedRoot⁻¹ - (1 / 2 : ℚ) ∧
      G.selectedRoot⁻¹ - (1 / 2 : ℚ) <= pajuhaanZenodoR3ellWindowUpper) :=
  aascNeutrinoSameScopeAdmissionRows_finalNumericalReadout
    Rows.toSameScopeAdmissionRows

/--
Ratio-only normal form with a free offset and one gap scale.

This is the honest residual family behind the NNR9 ratio readout:
`rho` fixes the solar/atmospheric quotient, while the offset `t` and scale
gap `D` are not fixed by the ratio alone.
-/
def threeFlavorRatioOffsetGapFamily
  (rho D t : ℚ) : Fin 3 -> ℚ :=
  fun i =>
    if i = 0 then t
    else if i = 1 then t + rho * D
    else t + D

theorem threeFlavorRatioOffsetGapFamily_level0
  (rho D t : ℚ) :
  threeFlavorRatioOffsetGapFamily rho D t 0 = t := by
  simp [threeFlavorRatioOffsetGapFamily]

theorem threeFlavorRatioOffsetGapFamily_level1
  (rho D t : ℚ) :
  threeFlavorRatioOffsetGapFamily rho D t 1 = t + rho * D := by
  simp [threeFlavorRatioOffsetGapFamily]

theorem threeFlavorRatioOffsetGapFamily_level2
  (rho D t : ℚ) :
  threeFlavorRatioOffsetGapFamily rho D t 2 = t + D := by
  simp [threeFlavorRatioOffsetGapFamily]

theorem threeFlavorRatioOffsetGapFamily_solarGap
  (rho D t : ℚ) :
  threeFlavorSolarGap (threeFlavorRatioOffsetGapFamily rho D t) =
    rho * D := by
  simp [threeFlavorSolarGap, threeFlavorRatioOffsetGapFamily]

theorem threeFlavorRatioOffsetGapFamily_atmosphericGap
  (rho D t : ℚ) :
  threeFlavorAtmosphericGap (threeFlavorRatioOffsetGapFamily rho D t) =
    D := by
  simp [threeFlavorAtmosphericGap, threeFlavorRatioOffsetGapFamily]

theorem threeFlavorRatioOffsetGapFamily_gapRatio
  (rho D t : ℚ)
  (hD : D ≠ 0) :
  threeFlavorGapRatio (threeFlavorRatioOffsetGapFamily rho D t) = rho := by
  unfold threeFlavorGapRatio
  rw [threeFlavorRatioOffsetGapFamily_solarGap,
    threeFlavorRatioOffsetGapFamily_atmosphericGap]
  field_simp [hD]

theorem threeFlavorRatioOffsetGapFamily_offsetInvariant
  (rho D t u : ℚ)
  (hD : D ≠ 0) :
  threeFlavorGapRatio (threeFlavorRatioOffsetGapFamily rho D t) =
    threeFlavorGapRatio (threeFlavorRatioOffsetGapFamily rho D u) := by
  rw [threeFlavorRatioOffsetGapFamily_gapRatio rho D t hD,
    threeFlavorRatioOffsetGapFamily_gapRatio rho D u hD]

/--
A full projective mass-squared shape for a three-flavor neutrino carrier.

Unlike the bare ratio, this remembers the three component proportions.  This
is the object to which MR6-style one-anchor reconstruction applies.
-/
structure ThreeFlavorProjectiveMassSquaredShape where
  shapeLevel : Fin 3 -> ℚ
  shapeStandingCertified : Prop
  shapeStandingCertified_proof :
    shapeStandingCertified
  quotientStableShape : Prop
  quotientStableShape_proof :
    quotientStableShape
  noAbsoluteScaleInShape : Prop
  noAbsoluteScaleInShape_proof :
    noAbsoluteScaleInShape

/--
One target-aligned metric anchor for a projective three-flavor shape.

The anchor is a display/reconstruction datum, not a zero-anchor derivation.
The audit fields keep MR6 and EX5 discipline explicit: target alignment,
unit/transport ledgers, and no hidden target-value laundering must be supplied.
-/
structure ThreeFlavorOneAnchorMassSquaredDisplayAnchor
  (S : ThreeFlavorProjectiveMassSquaredShape) where
  anchorIndex : Fin 3
  anchorValue : ℚ
  shapeAnchor_ne_zero :
    S.shapeLevel anchorIndex ≠ 0
  anchorValue_ne_zero :
    anchorValue ≠ 0
  targetAlignedAnchor : Prop
  targetAlignedAnchor_proof :
    targetAlignedAnchor
  unitLedgerFixed : Prop
  unitLedgerFixed_proof :
    unitLedgerFixed
  standingTransportCertified : Prop
  standingTransportCertified_proof :
    standingTransportCertified
  noScaleLaundering : Prop
  noScaleLaundering_proof :
    noScaleLaundering

def threeFlavorOneAnchorScale
  {S : ThreeFlavorProjectiveMassSquaredShape}
  (A : ThreeFlavorOneAnchorMassSquaredDisplayAnchor S) : ℚ :=
  A.anchorValue / S.shapeLevel A.anchorIndex

def threeFlavorOneAnchorReconstructedMassSquared
  {S : ThreeFlavorProjectiveMassSquaredShape}
  (A : ThreeFlavorOneAnchorMassSquaredDisplayAnchor S) : Fin 3 -> ℚ :=
  fun i => threeFlavorOneAnchorScale A * S.shapeLevel i

theorem threeFlavorOneAnchorScale_ne_zero
  {S : ThreeFlavorProjectiveMassSquaredShape}
  (A : ThreeFlavorOneAnchorMassSquaredDisplayAnchor S) :
  threeFlavorOneAnchorScale A ≠ 0 := by
  unfold threeFlavorOneAnchorScale
  exact div_ne_zero A.anchorValue_ne_zero A.shapeAnchor_ne_zero

theorem threeFlavorOneAnchorReconstructed_anchor_eq
  {S : ThreeFlavorProjectiveMassSquaredShape}
  (A : ThreeFlavorOneAnchorMassSquaredDisplayAnchor S) :
  threeFlavorOneAnchorReconstructedMassSquared A A.anchorIndex =
    A.anchorValue := by
  unfold threeFlavorOneAnchorReconstructedMassSquared
  unfold threeFlavorOneAnchorScale
  field_simp [A.shapeAnchor_ne_zero]

theorem threeFlavorOneAnchorReconstructed_gapRatio_eq_shape
  {S : ThreeFlavorProjectiveMassSquaredShape}
  (A : ThreeFlavorOneAnchorMassSquaredDisplayAnchor S) :
  threeFlavorGapRatio (threeFlavorOneAnchorReconstructedMassSquared A) =
    threeFlavorGapRatio S.shapeLevel := by
  unfold threeFlavorOneAnchorReconstructedMassSquared
  exact threeFlavorGapRatio_scale
    S.shapeLevel
    (threeFlavorOneAnchorScale A)
    (threeFlavorOneAnchorScale_ne_zero A)

/--
MR6-style one-anchor reconstruction endpoint for the neutrino mass-squared
carrier.

This is a lawful display theorem: a certified projective shape plus one
target-aligned metric anchor reconstructs an absolute mass-squared triple.
It does not claim that the anchor is derived from the ratio alone.
-/
structure ThreeFlavorOneAnchorNeutrinoSpectrumReconstruction
  (S : ThreeFlavorProjectiveMassSquaredShape) where
  anchor :
    ThreeFlavorOneAnchorMassSquaredDisplayAnchor S
  reconstructedLevel : Fin 3 -> ℚ
  reconstructed_eq_oneAnchorMap :
    reconstructedLevel =
      threeFlavorOneAnchorReconstructedMassSquared anchor
  anchorLevel_eq_anchorValue :
    reconstructedLevel anchor.anchorIndex = anchor.anchorValue
  gapRatio_preserved :
    threeFlavorGapRatio reconstructedLevel =
      threeFlavorGapRatio S.shapeLevel
  oneAnchorReconstructionMapAdmitted : Prop
  oneAnchorReconstructionMapAdmitted_proof :
    oneAnchorReconstructionMapAdmitted

noncomputable def threeFlavorOneAnchorNeutrinoSpectrumReconstruction
  (S : ThreeFlavorProjectiveMassSquaredShape)
  (A : ThreeFlavorOneAnchorMassSquaredDisplayAnchor S)
  (oneAnchorReconstructionMapAdmitted : Prop)
  (honeAnchor : oneAnchorReconstructionMapAdmitted) :
  ThreeFlavorOneAnchorNeutrinoSpectrumReconstruction S :=
  { anchor := A
    reconstructedLevel := threeFlavorOneAnchorReconstructedMassSquared A
    reconstructed_eq_oneAnchorMap := rfl
    anchorLevel_eq_anchorValue :=
      threeFlavorOneAnchorReconstructed_anchor_eq A
    gapRatio_preserved :=
      threeFlavorOneAnchorReconstructed_gapRatio_eq_shape A
    oneAnchorReconstructionMapAdmitted := oneAnchorReconstructionMapAdmitted
    oneAnchorReconstructionMapAdmitted_proof := honeAnchor }

/--
Convenience wrapper for the NNR10 target: NNR9 supplies the ratio readout;
MR6-style one-anchor admission supplies metric display of the full
mass-squared triple.
-/
structure AASCNNR10OneAnchorNeutrinoMassSpectrumDisplay where
  shape :
    ThreeFlavorProjectiveMassSquaredShape
  reconstruction :
    ThreeFlavorOneAnchorNeutrinoSpectrumReconstruction shape
  inheritedNNR9RatioReadout : Prop
  inheritedNNR9RatioReadout_proof :
    inheritedNNR9RatioReadout
  notZeroAnchorAbsoluteDerivation : Prop
  notZeroAnchorAbsoluteDerivation_proof :
    notZeroAnchorAbsoluteDerivation
  noScaleLaundering :
    reconstruction.anchor.noScaleLaundering

/--
Concrete projective shape levels supplied by the AASC-admitted source rows.
The indices `0,1,2` correspond to the source row parameters `k=1,3,5`.
-/
def aascNeutrinoSourceProjectiveShapeLevel : Fin 3 -> ℚ :=
  fun i =>
    if i = 0 then aascNeutrinoMassSquaredLevel 1
    else if i = 1 then aascNeutrinoMassSquaredLevel 3
    else aascNeutrinoMassSquaredLevel 5

theorem aascNeutrinoSourceProjectiveShapeLevel_zero :
  aascNeutrinoSourceProjectiveShapeLevel 0 =
    aascNeutrinoMassSquaredLevel 1 := by
  simp [aascNeutrinoSourceProjectiveShapeLevel]

theorem aascNeutrinoSourceProjectiveShapeLevel_one :
  aascNeutrinoSourceProjectiveShapeLevel 1 =
    aascNeutrinoMassSquaredLevel 3 := by
  simp [aascNeutrinoSourceProjectiveShapeLevel]

theorem aascNeutrinoSourceProjectiveShapeLevel_two :
  aascNeutrinoSourceProjectiveShapeLevel 2 =
    aascNeutrinoMassSquaredLevel 5 := by
  simp [aascNeutrinoSourceProjectiveShapeLevel]

noncomputable def aascNeutrinoSourceProjectiveMassSquaredShape
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoSourceRowStandingAdmission G QNF) :
  ThreeFlavorProjectiveMassSquaredShape :=
  { shapeLevel := aascNeutrinoSourceProjectiveShapeLevel
    shapeStandingCertified := Rows.sourceRowsSameStandingCarrier
    shapeStandingCertified_proof :=
      Rows.sourceRowsSameStandingCarrier_proof
    quotientStableShape := Rows.quotientSkinTransportCompatible
    quotientStableShape_proof :=
      Rows.quotientSkinTransportCompatible_proof
    noAbsoluteScaleInShape :=
      AASCNeutrinoNoMassOrSplittingInputInCoefficientPipeline
    noAbsoluteScaleInShape_proof :=
      Rows.noEmpiricalImportByAASC }

theorem aascNeutrinoSourceProjectiveMassSquaredShape_gapRatio_eq_source
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoSourceRowStandingAdmission G QNF) :
  threeFlavorGapRatio
      (aascNeutrinoSourceProjectiveMassSquaredShape Rows).shapeLevel =
    threeFlavorGapRatio A.massSquaredLevelOf := by
  have h0 :
      (aascNeutrinoSourceProjectiveMassSquaredShape Rows).shapeLevel 0 =
        A.massSquaredLevelOf 0 := by
    change aascNeutrinoSourceProjectiveShapeLevel 0 =
      A.massSquaredLevelOf 0
    rw [aascNeutrinoSourceProjectiveShapeLevel_zero]
    exact Rows.level0_eq_aascSource.symm
  have h1 :
      (aascNeutrinoSourceProjectiveMassSquaredShape Rows).shapeLevel 1 =
        A.massSquaredLevelOf 1 := by
    change aascNeutrinoSourceProjectiveShapeLevel 1 =
      A.massSquaredLevelOf 1
    rw [aascNeutrinoSourceProjectiveShapeLevel_one]
    exact Rows.level1_eq_aascSource.symm
  have h2 :
      (aascNeutrinoSourceProjectiveMassSquaredShape Rows).shapeLevel 2 =
        A.massSquaredLevelOf 2 := by
    change aascNeutrinoSourceProjectiveShapeLevel 2 =
      A.massSquaredLevelOf 2
    rw [aascNeutrinoSourceProjectiveShapeLevel_two]
    exact Rows.level2_eq_aascSource.symm
  unfold threeFlavorGapRatio threeFlavorSolarGap threeFlavorAtmosphericGap
  rw [h0, h1, h2]

/--
The additional metric datum needed to turn the NNR9 source-row projective shape
into an absolute mass-squared display.
-/
structure AASCNeutrinoOneAnchorMetricInput
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoSourceRowStandingAdmission G QNF) where
  anchorIndex : Fin 3
  anchorValue : ℚ
  shapeAnchor_ne_zero :
    (aascNeutrinoSourceProjectiveMassSquaredShape Rows).shapeLevel
      anchorIndex ≠ 0
  anchorValue_ne_zero :
    anchorValue ≠ 0
  targetAlignedAnchor : Prop
  targetAlignedAnchor_proof :
    targetAlignedAnchor
  unitLedgerFixed : Prop
  unitLedgerFixed_proof :
    unitLedgerFixed
  standingTransportCertified : Prop
  standingTransportCertified_proof :
    standingTransportCertified
  noScaleLaundering : Prop
  noScaleLaundering_proof :
    noScaleLaundering
  oneAnchorReconstructionMapAdmitted : Prop
  oneAnchorReconstructionMapAdmitted_proof :
    oneAnchorReconstructionMapAdmitted
  notZeroAnchorAbsoluteDerivation : Prop
  notZeroAnchorAbsoluteDerivation_proof :
    notZeroAnchorAbsoluteDerivation

noncomputable def AASCNeutrinoOneAnchorMetricInput.toDisplayAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  {Rows : AASCNeutrinoSourceRowStandingAdmission G QNF}
  (Anchor : AASCNeutrinoOneAnchorMetricInput Rows) :
  ThreeFlavorOneAnchorMassSquaredDisplayAnchor
    (aascNeutrinoSourceProjectiveMassSquaredShape Rows) :=
  { anchorIndex := Anchor.anchorIndex
    anchorValue := Anchor.anchorValue
    shapeAnchor_ne_zero := Anchor.shapeAnchor_ne_zero
    anchorValue_ne_zero := Anchor.anchorValue_ne_zero
    targetAlignedAnchor := Anchor.targetAlignedAnchor
    targetAlignedAnchor_proof := Anchor.targetAlignedAnchor_proof
    unitLedgerFixed := Anchor.unitLedgerFixed
    unitLedgerFixed_proof := Anchor.unitLedgerFixed_proof
    standingTransportCertified := Anchor.standingTransportCertified
    standingTransportCertified_proof :=
      Anchor.standingTransportCertified_proof
    noScaleLaundering := Anchor.noScaleLaundering
    noScaleLaundering_proof := Anchor.noScaleLaundering_proof }

noncomputable def aascNeutrinoOneAnchorSpectrumReconstruction
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoSourceRowStandingAdmission G QNF)
  (Anchor : AASCNeutrinoOneAnchorMetricInput Rows) :
  ThreeFlavorOneAnchorNeutrinoSpectrumReconstruction
    (aascNeutrinoSourceProjectiveMassSquaredShape Rows) :=
  threeFlavorOneAnchorNeutrinoSpectrumReconstruction
    (aascNeutrinoSourceProjectiveMassSquaredShape Rows)
    Anchor.toDisplayAnchor
    Anchor.oneAnchorReconstructionMapAdmitted
    Anchor.oneAnchorReconstructionMapAdmitted_proof

noncomputable def aascNeutrinoNNR10OneAnchorMassSpectrumDisplay
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoSourceRowStandingAdmission G QNF)
  (Anchor : AASCNeutrinoOneAnchorMetricInput Rows) :
  AASCNNR10OneAnchorNeutrinoMassSpectrumDisplay :=
  { shape := aascNeutrinoSourceProjectiveMassSquaredShape Rows
    reconstruction :=
      aascNeutrinoOneAnchorSpectrumReconstruction Rows Anchor
    inheritedNNR9RatioReadout :=
      Nonempty (CurrentStandingRatioEvaluation C)
    inheritedNNR9RatioReadout_proof :=
      (Rows.finalNumericalReadout).1
    notZeroAnchorAbsoluteDerivation :=
      Anchor.notZeroAnchorAbsoluteDerivation
    notZeroAnchorAbsoluteDerivation_proof :=
      Anchor.notZeroAnchorAbsoluteDerivation_proof
    noScaleLaundering :=
      Anchor.noScaleLaundering_proof }

theorem aascNeutrinoOneAnchorSpectrum_gapRatio_eq_NNR9GapRatio
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoSourceRowStandingAdmission G QNF)
  (Anchor : AASCNeutrinoOneAnchorMetricInput Rows) :
  threeFlavorGapRatio
      (aascNeutrinoOneAnchorSpectrumReconstruction Rows Anchor).reconstructedLevel =
    threeFlavorGapRatio A.massSquaredLevelOf := by
  rw [
    (aascNeutrinoOneAnchorSpectrumReconstruction Rows Anchor).gapRatio_preserved,
    aascNeutrinoSourceProjectiveMassSquaredShape_gapRatio_eq_source Rows]

theorem aascNeutrinoOneAnchorSpectrum_gapRatio_eq_selectedRoot
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoSourceRowStandingAdmission G QNF)
  (Anchor : AASCNeutrinoOneAnchorMetricInput Rows) :
  threeFlavorGapRatio
      (aascNeutrinoOneAnchorSpectrumReconstruction Rows Anchor).reconstructedLevel =
    G.selectedRoot := by
  rw [aascNeutrinoOneAnchorSpectrum_gapRatio_eq_NNR9GapRatio Rows Anchor]
  exact (algebraicClosedRootPresentation_selectedRoot_eq_gapRatio G).symm

theorem aascNeutrinoOneAnchorSpectrum_anchorLevel_eq_anchorValue
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoSourceRowStandingAdmission G QNF)
  (Anchor : AASCNeutrinoOneAnchorMetricInput Rows) :
  (aascNeutrinoOneAnchorSpectrumReconstruction Rows Anchor).reconstructedLevel
      Anchor.anchorIndex =
    Anchor.anchorValue :=
  (aascNeutrinoOneAnchorSpectrumReconstruction Rows Anchor).anchorLevel_eq_anchorValue

theorem aascNeutrinoNNR10Display_gapRatio_eq_selectedRoot
  (D : AASCNNR10OneAnchorNeutrinoMassSpectrumDisplay) :
  threeFlavorGapRatio D.reconstruction.reconstructedLevel =
    threeFlavorGapRatio D.shape.shapeLevel :=
  D.reconstruction.gapRatio_preserved

def AASCNeutrinoOneAnchorAbsoluteMassSquaredSpectrumAvailable
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoSourceRowStandingAdmission G QNF) : Prop :=
  exists Anchor : AASCNeutrinoOneAnchorMetricInput Rows,
    exists R :
      ThreeFlavorOneAnchorNeutrinoSpectrumReconstruction
        (aascNeutrinoSourceProjectiveMassSquaredShape Rows),
      R.anchor = Anchor.toDisplayAnchor

theorem aascNeutrinoOneAnchorMetricInput_discharge_absoluteSpectrumNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoSourceRowStandingAdmission G QNF)
  (Anchor : AASCNeutrinoOneAnchorMetricInput Rows) :
  AASCNeutrinoOneAnchorAbsoluteMassSquaredSpectrumAvailable Rows := by
  exact
    ⟨Anchor,
      aascNeutrinoOneAnchorSpectrumReconstruction Rows Anchor,
      rfl⟩

/--
Atmospheric-gap metric anchor for the NNR9 projective source shape.

This is the natural neutrino analogue of a one-anchor display when the admitted
anchor is a mass-squared gap rather than a single component.  The anchor value
is intended to display `Delta m^2_31`; it is not treated as a zero-anchor
first-principles derivation.
-/
structure AASCNeutrinoAtmosphericGapMetricAnchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoSourceRowStandingAdmission G QNF) where
  atmosphericGapAnchor : ℚ
  atmosphericGapAnchor_ne_zero :
    atmosphericGapAnchor ≠ 0
  sourceShapeAtmosphericGap_ne_zero :
    threeFlavorAtmosphericGap
      (aascNeutrinoSourceProjectiveMassSquaredShape Rows).shapeLevel ≠ 0
  targetAlignedAtmosphericGapAnchor : Prop
  targetAlignedAtmosphericGapAnchor_proof :
    targetAlignedAtmosphericGapAnchor
  unitLedgerFixed : Prop
  unitLedgerFixed_proof :
    unitLedgerFixed
  standingTransportCertified : Prop
  standingTransportCertified_proof :
    standingTransportCertified
  noScaleLaundering : Prop
  noScaleLaundering_proof :
    noScaleLaundering
  notZeroAnchorAbsoluteDerivation : Prop
  notZeroAnchorAbsoluteDerivation_proof :
    notZeroAnchorAbsoluteDerivation

noncomputable def aascNeutrinoAtmosphericGapScale
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  {Rows : AASCNeutrinoSourceRowStandingAdmission G QNF}
  (Anchor : AASCNeutrinoAtmosphericGapMetricAnchor Rows) : ℚ :=
  Anchor.atmosphericGapAnchor /
    threeFlavorAtmosphericGap
      (aascNeutrinoSourceProjectiveMassSquaredShape Rows).shapeLevel

noncomputable def aascNeutrinoAtmosphericGapAnchoredMassSquared
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  {Rows : AASCNeutrinoSourceRowStandingAdmission G QNF}
  (Anchor : AASCNeutrinoAtmosphericGapMetricAnchor Rows) :
  Fin 3 -> ℚ :=
  fun i =>
    aascNeutrinoAtmosphericGapScale Anchor *
      (aascNeutrinoSourceProjectiveMassSquaredShape Rows).shapeLevel i

theorem aascNeutrinoAtmosphericGapScale_ne_zero
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  {Rows : AASCNeutrinoSourceRowStandingAdmission G QNF}
  (Anchor : AASCNeutrinoAtmosphericGapMetricAnchor Rows) :
  aascNeutrinoAtmosphericGapScale Anchor ≠ 0 := by
  unfold aascNeutrinoAtmosphericGapScale
  exact div_ne_zero Anchor.atmosphericGapAnchor_ne_zero
    Anchor.sourceShapeAtmosphericGap_ne_zero

theorem aascNeutrinoAtmosphericGapAnchored_atmosphericGap_eq_anchor
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  {Rows : AASCNeutrinoSourceRowStandingAdmission G QNF}
  (Anchor : AASCNeutrinoAtmosphericGapMetricAnchor Rows) :
  threeFlavorAtmosphericGap
      (aascNeutrinoAtmosphericGapAnchoredMassSquared Anchor) =
    Anchor.atmosphericGapAnchor := by
  unfold aascNeutrinoAtmosphericGapAnchoredMassSquared
  rw [threeFlavorAtmosphericGap_scale]
  unfold aascNeutrinoAtmosphericGapScale
  field_simp [Anchor.sourceShapeAtmosphericGap_ne_zero]

theorem aascNeutrinoAtmosphericGapAnchored_gapRatio_eq_sourceShape
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  {Rows : AASCNeutrinoSourceRowStandingAdmission G QNF}
  (Anchor : AASCNeutrinoAtmosphericGapMetricAnchor Rows) :
  threeFlavorGapRatio
      (aascNeutrinoAtmosphericGapAnchoredMassSquared Anchor) =
    threeFlavorGapRatio
      (aascNeutrinoSourceProjectiveMassSquaredShape Rows).shapeLevel := by
  unfold aascNeutrinoAtmosphericGapAnchoredMassSquared
  exact threeFlavorGapRatio_scale
    (aascNeutrinoSourceProjectiveMassSquaredShape Rows).shapeLevel
    (aascNeutrinoAtmosphericGapScale Anchor)
    (aascNeutrinoAtmosphericGapScale_ne_zero Anchor)

theorem aascNeutrinoAtmosphericGapAnchored_gapRatio_eq_selectedRoot
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoSourceRowStandingAdmission G QNF)
  (Anchor : AASCNeutrinoAtmosphericGapMetricAnchor Rows) :
  threeFlavorGapRatio
      (aascNeutrinoAtmosphericGapAnchoredMassSquared Anchor) =
    G.selectedRoot := by
  rw [aascNeutrinoAtmosphericGapAnchored_gapRatio_eq_sourceShape Anchor,
    aascNeutrinoSourceProjectiveMassSquaredShape_gapRatio_eq_source Rows]
  exact (algebraicClosedRootPresentation_selectedRoot_eq_gapRatio G).symm

def AASCNeutrinoAtmosphericGapAnchoredSpectrumAvailable
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoSourceRowStandingAdmission G QNF) : Prop :=
  exists Anchor : AASCNeutrinoAtmosphericGapMetricAnchor Rows,
    threeFlavorAtmosphericGap
        (aascNeutrinoAtmosphericGapAnchoredMassSquared Anchor) =
      Anchor.atmosphericGapAnchor

theorem aascNeutrinoAtmosphericGapMetricAnchor_discharge_spectrumNeed
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {A : ThreeFlavorGapRatioAlgebra M ℚ}
  {P : AASCSameScopePolynomialNumericalPredictionPackage H ℚ A}
  {G : ThreeFlavorAlgebraicClosedRootPresentation ℚ A P}
  {QNF : ThreeFlavorQuotientNormalFormInteriorLaw ℚ A}
  (Rows : AASCNeutrinoSourceRowStandingAdmission G QNF)
  (Anchor : AASCNeutrinoAtmosphericGapMetricAnchor Rows) :
  AASCNeutrinoAtmosphericGapAnchoredSpectrumAvailable Rows := by
  exact
    ⟨Anchor,
      aascNeutrinoAtmosphericGapAnchored_atmosphericGap_eq_anchor Anchor⟩

theorem gapRatioAlgebraAndNativeExhaustionGiveAlgebraicClassFrontier
  {C : StandingRatioCertificate}
  {M : MR3SpectralSourceAdmission C}
  {H : AASCHybridCompressionNetwork C M}
  {N : AASCNoEleventhNeutrinoRoute C M H}
  (R : Type)
  [Field R]
  (A : ThreeFlavorGapRatioAlgebra M R)
  (hA : ThreeFlavorGapRatioAlgebraPasses A)
  (G : AASCNativeOperatorExhaustionGuardrailSupport H N)
  (exactlyThreeMassStates : Prop)
  (hexactlyThree : exactlyThreeMassStates)
  (threeFlavorCarrierAdmitted : Prop)
  (hcarrier : threeFlavorCarrierAdmitted)
  (massSquaredSplittingCarrierStanding : Prop)
  (hstanding : massSquaredSplittingCarrierStanding)
  (spectralOperatorDerivedFromSplittings : Prop)
  (hoperator : spectralOperatorDerivedFromSplittings)
  (characteristicClassPolynomialLike : Prop)
  (hpolyLike : characteristicClassPolynomialLike)
  (notMerelyShapeMapRelabel : Prop)
  (hnotRelabel : notMerelyShapeMapRelabel)
  (BE : AASCClosedExpressionReadoutBlocker C)
  (BV : AASCExactValueReadoutBlocker C) :
  AASCNNR9AlgebraicClassFrontier C :=
  threeFlavorDiagonalMathlibDataAndNativeExhaustionGiveAlgebraicClassFrontier
    R
    (splittingRatioReadbackAsDiagonalMathlibData
      M
      R
      (gapRatioAlgebraAsSplittingReadback M R A)
      (gapRatioAlgebraGivesSplittingReadbackPasses M R A hA)
      exactlyThreeMassStates
      hexactlyThree
      threeFlavorCarrierAdmitted
      hcarrier
      massSquaredSplittingCarrierStanding
      hstanding
      spectralOperatorDerivedFromSplittings
      hoperator
      characteristicClassPolynomialLike
      hpolyLike
      notMerelyShapeMapRelabel
      hnotRelabel)
    G
    BE
    BV

end Neutrino

end MaleyLean
