import TraceEuclidean.V15HunterProjection

/-!
# Hunter projection in arbitrary positive rank

This module generalizes the centered lattice used in the cubic and quartic
arguments.  For a basis indexed by `Fin (n + 1)`, its last `n` vectors
project to a basis of the orthogonal complement of the first vector, and
integral coordinates lift canonically back to the original lattice.
-/

namespace TraceEuclidean
noncomputable section
open scoped RealInnerProductSpace
open MeasureTheory Module Submodule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ}

/-- The last `n` basis vectors after orthogonal projection away from the first
basis vector. -/
def v15HunterGeneralProjectedFamily
    (b : Basis (Fin (n + 1)) ℝ E) : Fin n → (ℝ ∙ b 0)ᗮ :=
  fun i => v15HunterCenterLinearMap (b 0)
    (inner_self_ne_zero.mpr (b.ne_zero 0)) (b i.succ)

/-- Projecting the last `n` vectors along the first vector preserves linear
independence. -/
theorem v15HunterGeneralProjectedFamily_linearIndependent
    (b : Basis (Fin (n + 1)) ℝ E) :
    LinearIndependent ℝ (v15HunterGeneralProjectedFamily b) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  let e := b 0
  let X := ∑ j : Fin n, g j • b j.succ
  have hmap :
      v15HunterCenterLinearMap e
          (inner_self_ne_zero.mpr (b.ne_zero 0)) X = 0 := by
    dsimp only [X]
    rw [map_sum]
    simp_rw [map_smul]
    exact hg
  have hcenter : v15HunterCenter e X = 0 := by
    exact congrArg Subtype.val hmap
  let r : ℝ := inner ℝ e X / inner ℝ e e
  have hx : X = r • e := by
    exact sub_eq_zero.mp hcenter
  let g' : Fin (n + 1) → ℝ := Fin.cons (-r) g
  have hsum : ∑ k : Fin (n + 1), g' k • b k = 0 := by
    rw [Fin.sum_univ_succ]
    change (-r) • e + X = 0
    rw [hx]
    simp
  have hz := Fintype.linearIndependent_iff.mp b.linearIndependent g' hsum i.succ
  simpa [g'] using hz

variable [FiniteDimensional ℝ E]

/-- The projected family as a basis of the orthogonal complement. -/
noncomputable def v15HunterGeneralProjectedBasis
    (b : Basis (Fin (n + 1)) ℝ E) :
    Basis (Fin n) ℝ ((ℝ ∙ b 0)ᗮ) := by
  letI : Fact (finrank ℝ E = n + 1) := ⟨by
    simpa using finrank_eq_card_basis b⟩
  exact basisOfLinearIndependentOfCardEqFinrank'
    (v15HunterGeneralProjectedFamily b)
    (v15HunterGeneralProjectedFamily_linearIndependent b) (by
    rw [Fintype.card_fin,
      Submodule.finrank_orthogonal_span_singleton (n := n) (b.ne_zero 0)])

/-- The projected basis has the expected centered vectors. -/
@[simp]
theorem v15HunterGeneralProjectedBasis_apply
    (b : Basis (Fin (n + 1)) ℝ E) (i : Fin n) :
    v15HunterGeneralProjectedBasis b i = v15HunterGeneralProjectedFamily b i := by
  simp [v15HunterGeneralProjectedBasis, coe_basisOfLinearIndependentOfCardEqFinrank']

/-- The full integral lattice spanned by the projected basis. -/
abbrev v15HunterGeneralProjectedLattice
    (b : Basis (Fin (n + 1)) ℝ E) :
    Submodule ℤ ((ℝ ∙ b 0)ᗮ) :=
  span ℤ (Set.range (v15HunterGeneralProjectedBasis b))

section IntegralLift

variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

/-- Lift projected integral coordinates using the corresponding last `n`
vectors of the original integral basis. -/
noncomputable def v15HunterGeneralIntegralLift
    (bz : Basis (Fin (n + 1)) ℤ L)
    (x : v15HunterGeneralProjectedLattice (bz.ofZLatticeBasis ℝ)) : L :=
  let b := bz.ofZLatticeBasis ℝ
  let c := ((v15HunterGeneralProjectedBasis b).restrictScalars ℤ).repr x
  ∑ i : Fin n, c i • bz i.succ

/-- Centering an original tail vector gives its projected basis vector. -/
theorem v15HunterGeneralCenterLinearMap_basis_succ
    (b : Basis (Fin (n + 1)) ℝ E) (i : Fin n) :
    v15HunterCenterLinearMap (b 0)
        (inner_self_ne_zero.mpr (b.ne_zero 0)) (b i.succ) =
      v15HunterGeneralProjectedBasis b i := by
  rw [v15HunterGeneralProjectedBasis_apply]
  rfl

/-- The integral lift maps back to the supplied projected-lattice vector under
orthogonal centering. -/
theorem v15HunterGeneralIntegralLift_center
    (bz : Basis (Fin (n + 1)) ℤ L)
    (x : v15HunterGeneralProjectedLattice (bz.ofZLatticeBasis ℝ)) :
    v15HunterCenterLinearMap ((bz.ofZLatticeBasis ℝ) 0)
        (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
        (((v15HunterGeneralIntegralLift bz x : L) : E)) =
      ((x : v15HunterGeneralProjectedLattice (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ) := by
  let b := bz.ofZLatticeBasis ℝ
  let c := ((v15HunterGeneralProjectedBasis b).restrictScalars ℤ).repr x
  have hcenter : ∀ i : Fin n,
      v15HunterCenterLinearMap ((bz.ofZLatticeBasis ℝ) 0)
          (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
          (b i.succ) = v15HunterGeneralProjectedBasis b i := by
    intro i
    simpa [b] using v15HunterGeneralCenterLinearMap_basis_succ b i
  have hcoe : (((v15HunterGeneralIntegralLift bz x : L) : E)) =
      ∑ i : Fin n, (c i : ℝ) • b i.succ := by
    simp [v15HunterGeneralIntegralLift, b, c, Int.cast_smul_eq_zsmul]
  rw [hcoe, map_sum]
  simp_rw [map_smul]
  simp_rw [hcenter]
  have hx :
      ∑ i : Fin n, c i •
          ((v15HunterGeneralProjectedBasis b).restrictScalars ℤ) i = x :=
    ((v15HunterGeneralProjectedBasis b).restrictScalars ℤ).sum_repr x
  have hxval :
      ∑ i : Fin n, c i • v15HunterGeneralProjectedBasis b i =
        ((x : v15HunterGeneralProjectedLattice b) : (ℝ ∙ b 0)ᗮ) := by
    have hcoeSum :
        (((∑ i : Fin n, c i •
            ((v15HunterGeneralProjectedBasis b).restrictScalars ℤ) i) :
              v15HunterGeneralProjectedLattice b) : (ℝ ∙ b 0)ᗮ) =
          ∑ i : Fin n, c i • v15HunterGeneralProjectedBasis b i := by
      apply Subtype.ext
      simp [Basis.restrictScalars_apply]
    rw [← hcoeSum]
    exact congrArg Subtype.val hx
  simpa only [Int.cast_smul_eq_zsmul] using hxval

end IntegralLift

/-- Replace every tail vector by its centered vector while retaining the first
vector. -/
def v15HunterGeneralOrthogonalizedFamily
    (b : Basis (Fin (n + 1)) ℝ E) :
    Fin (n + 1) → E :=
  Fin.cons (b 0) (fun i => v15HunterCenter (b 0) (b i.succ))

omit [FiniteDimensional ℝ E] in
/-- Centering the tail vectors is a determinant-one change of basis. -/
theorem v15HunterGeneralOrthogonalizedFamily_det
    (b : Basis (Fin (n + 1)) ℝ E) :
    b.det (v15HunterGeneralOrthogonalizedFamily b) = 1 := by
  have htail :
      (b.toMatrix (v15HunterGeneralOrthogonalizedFamily b)).submatrix Fin.succ Fin.succ =
        (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    by_cases hij : i = j
    · simp [Basis.toMatrix_apply, v15HunterGeneralOrthogonalizedFamily, v15HunterCenter,
        Matrix.one_apply, hij]
    · simp [Basis.toMatrix_apply, v15HunterGeneralOrthogonalizedFamily, v15HunterCenter,
        hij]
  have hzero : b.toMatrix (v15HunterGeneralOrthogonalizedFamily b) 0 0 = 1 := by
    simp [Basis.toMatrix_apply, v15HunterGeneralOrthogonalizedFamily]
  have hsucc : ∀ i : Fin n,
      b.toMatrix (v15HunterGeneralOrthogonalizedFamily b) i.succ 0 = 0 := by
    intro i
    simp [Basis.toMatrix_apply, v15HunterGeneralOrthogonalizedFamily]
  rw [Basis.det_apply, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  rw [hzero]
  simp only [Fin.val_zero, pow_zero, one_mul]
  rw [Fin.succAbove_zero]
  rw [htail]
  simp [hsucc]

omit [FiniteDimensional ℝ E] in
/-- The determinant-one orthogonalized family as a basis of the full space. -/
noncomputable def v15HunterGeneralOrthogonalizedBasis
    (b : Basis (Fin (n + 1)) ℝ E) : Basis (Fin (n + 1)) ℝ E := by
  have hunit : IsUnit (b.det (v15HunterGeneralOrthogonalizedFamily b)) := by
    rw [v15HunterGeneralOrthogonalizedFamily_det]
    exact isUnit_one
  have hbasis := (b.is_basis_iff_det).mpr hunit
  exact Basis.mk hbasis.1 hbasis.2.ge

omit [FiniteDimensional ℝ E] in
/-- Evaluation of the orthogonalized basis. -/
@[simp]
theorem v15HunterGeneralOrthogonalizedBasis_apply
    (b : Basis (Fin (n + 1)) ℝ E) (i : Fin (n + 1)) :
    v15HunterGeneralOrthogonalizedBasis b i = v15HunterGeneralOrthogonalizedFamily b i := by
  simp [v15HunterGeneralOrthogonalizedBasis]

/-- The determinant-one orthogonalization preserves the Gram determinant. -/
theorem v15_gram_det_generalOrthogonalizedBasis_eq
    (b : Basis (Fin (n + 1)) ℝ E) :
    (Matrix.gram ℝ (v15HunterGeneralOrthogonalizedBasis b)).det =
      (Matrix.gram ℝ b).det := by
  let o := v15OrthonormalBasisOfBasis b
  rw [← v15_abs_det_basis_sq_eq_det_gram (v15HunterGeneralOrthogonalizedBasis b) o]
  rw [← v15_abs_det_basis_sq_eq_det_gram b o]
  have htransition : b.det (v15HunterGeneralOrthogonalizedBasis b) = 1 := by
    have hcoe : (v15HunterGeneralOrthogonalizedBasis b : Fin (n + 1) → E) =
        v15HunterGeneralOrthogonalizedFamily b := by
      funext i
      exact v15HunterGeneralOrthogonalizedBasis_apply b i
    rw [hcoe]
    exact v15HunterGeneralOrthogonalizedFamily_det b
  have hdet : o.toBasis.det (v15HunterGeneralOrthogonalizedBasis b) =
      o.toBasis.det b := by
    calc
      o.toBasis.det (v15HunterGeneralOrthogonalizedBasis b) =
        o.toBasis.det b * b.det (v15HunterGeneralOrthogonalizedBasis b) :=
        (Basis.det_mul_det o.toBasis b (v15HunterGeneralOrthogonalizedBasis b)).symm
      _ = o.toBasis.det b := by rw [htransition, mul_one]
  rw [hdet]

/-- The orthogonalized Gram determinant splits into its first direction and
the projected Gram determinant. -/
theorem v15_gram_det_generalOrthogonalizedBasis_block
    (b : Basis (Fin (n + 1)) ℝ E) :
    (Matrix.gram ℝ (v15HunterGeneralOrthogonalizedBasis b)).det =
      inner ℝ (b 0) (b 0) *
        (Matrix.gram ℝ (v15HunterGeneralProjectedBasis b)).det := by
  have hcoe : (v15HunterGeneralOrthogonalizedBasis b : Fin (n + 1) → E) =
      v15HunterGeneralOrthogonalizedFamily b := by
    funext i
    exact v15HunterGeneralOrthogonalizedBasis_apply b i
  rw [hcoe]
  let G := Matrix.gram ℝ (v15HunterGeneralOrthogonalizedFamily b)
  have he : inner ℝ (b 0) (b 0) ≠ 0 :=
    inner_self_ne_zero.mpr (b.ne_zero 0)
  have htail : G.submatrix Fin.succ Fin.succ =
      Matrix.gram ℝ (v15HunterGeneralProjectedBasis b) := by
    ext i j
    change inner ℝ (v15HunterCenter (b 0) (b i.succ))
        (v15HunterCenter (b 0) (b j.succ)) =
      inner ℝ (v15HunterGeneralProjectedBasis b i)
        (v15HunterGeneralProjectedBasis b j)
    rw [v15HunterGeneralProjectedBasis_apply,
      v15HunterGeneralProjectedBasis_apply]
    rfl
  have hzero : G 0 0 = inner ℝ (b 0) (b 0) := by
    simp [G, Matrix.gram_apply, v15HunterGeneralOrthogonalizedFamily]
  have hsucc : ∀ i : Fin n, G i.succ 0 = 0 := by
    intro i
    simp [G, Matrix.gram_apply, v15HunterGeneralOrthogonalizedFamily,
      real_inner_comm, v15_inner_center_left (b 0) (b i.succ) he]
  change G.det = _
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, hzero]
  simp only [Fin.val_zero, pow_zero, one_mul]
  rw [Fin.succAbove_zero, htail]
  simp [hsucc]

/-- General Gram-determinant form of the orthogonal projection formula. -/
theorem v15_det_gram_generalProjectedBasis_mul_inner_self
    (b : Basis (Fin (n + 1)) ℝ E) :
    (Matrix.gram ℝ (v15HunterGeneralProjectedBasis b)).det *
        inner ℝ (b 0) (b 0) =
      (Matrix.gram ℝ b).det := by
  rw [mul_comm]
  rw [← v15_gram_det_generalOrthogonalizedBasis_block b]
  exact v15_gram_det_generalOrthogonalizedBasis_eq b

variable [MeasurableSpace E] [BorelSpace E]

/-- General squared-covolume formula for projection away from a primitive
one-dimensional direction. -/
theorem v15HunterGeneralProjectedLattice_covolume_sq_mul_inner_self
    (b : Basis (Fin (n + 1)) ℝ E) :
    ZLattice.covolume (v15HunterGeneralProjectedLattice b) ^ 2 *
        inner ℝ (b 0) (b 0) =
      ZLattice.covolume (span ℤ (Set.range b)) ^ 2 := by
  rw [v15_covolume_span_basis_sq_eq_det_gram
    (v15HunterGeneralProjectedBasis b)
    (v15OrthonormalBasisOfBasis (v15HunterGeneralProjectedBasis b))]
  rw [v15_covolume_span_basis_sq_eq_det_gram
    b (v15OrthonormalBasisOfBasis b)]
  exact v15_det_gram_generalProjectedBasis_mul_inner_self b

end
end TraceEuclidean
