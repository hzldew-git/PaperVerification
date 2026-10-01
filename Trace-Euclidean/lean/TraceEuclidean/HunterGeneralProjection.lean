import TraceEuclidean.HunterProjection

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
def hunterGeneralProjectedFamily
    (b : Basis (Fin (n + 1)) ℝ E) : Fin n → (ℝ ∙ b 0)ᗮ :=
  fun i => hunterCenterLinearMap (b 0)
    (inner_self_ne_zero.mpr (b.ne_zero 0)) (b i.succ)

/-- Projecting the last `n` vectors along the first vector preserves linear
independence. -/
theorem hunterGeneralProjectedFamily_linearIndependent
    (b : Basis (Fin (n + 1)) ℝ E) :
    LinearIndependent ℝ (hunterGeneralProjectedFamily b) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  let e := b 0
  let X := ∑ j : Fin n, g j • b j.succ
  have hmap :
      hunterCenterLinearMap e
          (inner_self_ne_zero.mpr (b.ne_zero 0)) X = 0 := by
    dsimp only [X]
    rw [map_sum]
    simp_rw [map_smul]
    exact hg
  have hcenter : hunterCenter e X = 0 := by
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
noncomputable def hunterGeneralProjectedBasis
    (b : Basis (Fin (n + 1)) ℝ E) :
    Basis (Fin n) ℝ ((ℝ ∙ b 0)ᗮ) := by
  letI : Fact (finrank ℝ E = n + 1) := ⟨by
    simpa using finrank_eq_card_basis b⟩
  exact basisOfLinearIndependentOfCardEqFinrank'
    (hunterGeneralProjectedFamily b)
    (hunterGeneralProjectedFamily_linearIndependent b) (by
    rw [Fintype.card_fin,
      Submodule.finrank_orthogonal_span_singleton (n := n) (b.ne_zero 0)])

/-- The projected basis has the expected centered vectors. -/
@[simp]
theorem hunterGeneralProjectedBasis_apply
    (b : Basis (Fin (n + 1)) ℝ E) (i : Fin n) :
    hunterGeneralProjectedBasis b i = hunterGeneralProjectedFamily b i := by
  simp [hunterGeneralProjectedBasis, coe_basisOfLinearIndependentOfCardEqFinrank']

/-- The full integral lattice spanned by the projected basis. -/
abbrev hunterGeneralProjectedLattice
    (b : Basis (Fin (n + 1)) ℝ E) :
    Submodule ℤ ((ℝ ∙ b 0)ᗮ) :=
  span ℤ (Set.range (hunterGeneralProjectedBasis b))

section IntegralLift

variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

/-- Lift projected integral coordinates using the corresponding last `n`
vectors of the original integral basis. -/
noncomputable def hunterGeneralIntegralLift
    (bz : Basis (Fin (n + 1)) ℤ L)
    (x : hunterGeneralProjectedLattice (bz.ofZLatticeBasis ℝ)) : L :=
  let b := bz.ofZLatticeBasis ℝ
  let c := ((hunterGeneralProjectedBasis b).restrictScalars ℤ).repr x
  ∑ i : Fin n, c i • bz i.succ

/-- Centering an original tail vector gives its projected basis vector. -/
theorem hunterGeneralCenterLinearMap_basis_succ
    (b : Basis (Fin (n + 1)) ℝ E) (i : Fin n) :
    hunterCenterLinearMap (b 0)
        (inner_self_ne_zero.mpr (b.ne_zero 0)) (b i.succ) =
      hunterGeneralProjectedBasis b i := by
  rw [hunterGeneralProjectedBasis_apply]
  rfl

/-- The integral lift maps back to the supplied projected-lattice vector under
orthogonal centering. -/
theorem hunterGeneralIntegralLift_center
    (bz : Basis (Fin (n + 1)) ℤ L)
    (x : hunterGeneralProjectedLattice (bz.ofZLatticeBasis ℝ)) :
    hunterCenterLinearMap ((bz.ofZLatticeBasis ℝ) 0)
        (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
        (((hunterGeneralIntegralLift bz x : L) : E)) =
      ((x : hunterGeneralProjectedLattice (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ) := by
  let b := bz.ofZLatticeBasis ℝ
  let c := ((hunterGeneralProjectedBasis b).restrictScalars ℤ).repr x
  have hcenter : ∀ i : Fin n,
      hunterCenterLinearMap ((bz.ofZLatticeBasis ℝ) 0)
          (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
          (b i.succ) = hunterGeneralProjectedBasis b i := by
    intro i
    simpa [b] using hunterGeneralCenterLinearMap_basis_succ b i
  have hcoe : (((hunterGeneralIntegralLift bz x : L) : E)) =
      ∑ i : Fin n, (c i : ℝ) • b i.succ := by
    simp [hunterGeneralIntegralLift, b, c, Int.cast_smul_eq_zsmul]
  rw [hcoe, map_sum]
  simp_rw [map_smul]
  simp_rw [hcenter]
  have hx :
      ∑ i : Fin n, c i •
          ((hunterGeneralProjectedBasis b).restrictScalars ℤ) i = x :=
    ((hunterGeneralProjectedBasis b).restrictScalars ℤ).sum_repr x
  have hxval :
      ∑ i : Fin n, c i • hunterGeneralProjectedBasis b i =
        ((x : hunterGeneralProjectedLattice b) : (ℝ ∙ b 0)ᗮ) := by
    have hcoeSum :
        (((∑ i : Fin n, c i •
            ((hunterGeneralProjectedBasis b).restrictScalars ℤ) i) :
              hunterGeneralProjectedLattice b) : (ℝ ∙ b 0)ᗮ) =
          ∑ i : Fin n, c i • hunterGeneralProjectedBasis b i := by
      apply Subtype.ext
      simp [Basis.restrictScalars_apply]
    rw [← hcoeSum]
    exact congrArg Subtype.val hx
  simpa only [Int.cast_smul_eq_zsmul] using hxval

end IntegralLift

/-- Replace every tail vector by its centered vector while retaining the first
vector. -/
def hunterGeneralOrthogonalizedFamily
    (b : Basis (Fin (n + 1)) ℝ E) :
    Fin (n + 1) → E :=
  Fin.cons (b 0) (fun i => hunterCenter (b 0) (b i.succ))

omit [FiniteDimensional ℝ E] in
/-- Centering the tail vectors is a determinant-one change of basis. -/
theorem hunterGeneralOrthogonalizedFamily_det
    (b : Basis (Fin (n + 1)) ℝ E) :
    b.det (hunterGeneralOrthogonalizedFamily b) = 1 := by
  have htail :
      (b.toMatrix (hunterGeneralOrthogonalizedFamily b)).submatrix Fin.succ Fin.succ =
        (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    by_cases hij : i = j
    · simp [Basis.toMatrix_apply, hunterGeneralOrthogonalizedFamily, hunterCenter,
        Matrix.one_apply, hij]
    · simp [Basis.toMatrix_apply, hunterGeneralOrthogonalizedFamily, hunterCenter,
        hij]
  have hzero : b.toMatrix (hunterGeneralOrthogonalizedFamily b) 0 0 = 1 := by
    simp [Basis.toMatrix_apply, hunterGeneralOrthogonalizedFamily]
  have hsucc : ∀ i : Fin n,
      b.toMatrix (hunterGeneralOrthogonalizedFamily b) i.succ 0 = 0 := by
    intro i
    simp [Basis.toMatrix_apply, hunterGeneralOrthogonalizedFamily]
  rw [Basis.det_apply, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  rw [hzero]
  simp only [Fin.val_zero, pow_zero, one_mul]
  rw [Fin.succAbove_zero]
  rw [htail]
  simp [hsucc]

omit [FiniteDimensional ℝ E] in
/-- The determinant-one orthogonalized family as a basis of the full space. -/
noncomputable def hunterGeneralOrthogonalizedBasis
    (b : Basis (Fin (n + 1)) ℝ E) : Basis (Fin (n + 1)) ℝ E := by
  have hunit : IsUnit (b.det (hunterGeneralOrthogonalizedFamily b)) := by
    rw [hunterGeneralOrthogonalizedFamily_det]
    exact isUnit_one
  have hbasis := (b.is_basis_iff_det).mpr hunit
  exact Basis.mk hbasis.1 hbasis.2.ge

omit [FiniteDimensional ℝ E] in
/-- Evaluation of the orthogonalized basis. -/
@[simp]
theorem hunterGeneralOrthogonalizedBasis_apply
    (b : Basis (Fin (n + 1)) ℝ E) (i : Fin (n + 1)) :
    hunterGeneralOrthogonalizedBasis b i = hunterGeneralOrthogonalizedFamily b i := by
  simp [hunterGeneralOrthogonalizedBasis]

/-- The determinant-one orthogonalization preserves the Gram determinant. -/
theorem gram_det_generalOrthogonalizedBasis_eq
    (b : Basis (Fin (n + 1)) ℝ E) :
    (Matrix.gram ℝ (hunterGeneralOrthogonalizedBasis b)).det =
      (Matrix.gram ℝ b).det := by
  let o := orthonormalBasisOfBasis b
  rw [← abs_det_basis_sq_eq_det_gram (hunterGeneralOrthogonalizedBasis b) o]
  rw [← abs_det_basis_sq_eq_det_gram b o]
  have htransition : b.det (hunterGeneralOrthogonalizedBasis b) = 1 := by
    have hcoe : (hunterGeneralOrthogonalizedBasis b : Fin (n + 1) → E) =
        hunterGeneralOrthogonalizedFamily b := by
      funext i
      exact hunterGeneralOrthogonalizedBasis_apply b i
    rw [hcoe]
    exact hunterGeneralOrthogonalizedFamily_det b
  have hdet : o.toBasis.det (hunterGeneralOrthogonalizedBasis b) =
      o.toBasis.det b := by
    calc
      o.toBasis.det (hunterGeneralOrthogonalizedBasis b) =
        o.toBasis.det b * b.det (hunterGeneralOrthogonalizedBasis b) :=
        (Basis.det_mul_det o.toBasis b (hunterGeneralOrthogonalizedBasis b)).symm
      _ = o.toBasis.det b := by rw [htransition, mul_one]
  rw [hdet]

/-- The orthogonalized Gram determinant splits into its first direction and
the projected Gram determinant. -/
theorem gram_det_generalOrthogonalizedBasis_block
    (b : Basis (Fin (n + 1)) ℝ E) :
    (Matrix.gram ℝ (hunterGeneralOrthogonalizedBasis b)).det =
      inner ℝ (b 0) (b 0) *
        (Matrix.gram ℝ (hunterGeneralProjectedBasis b)).det := by
  have hcoe : (hunterGeneralOrthogonalizedBasis b : Fin (n + 1) → E) =
      hunterGeneralOrthogonalizedFamily b := by
    funext i
    exact hunterGeneralOrthogonalizedBasis_apply b i
  rw [hcoe]
  let G := Matrix.gram ℝ (hunterGeneralOrthogonalizedFamily b)
  have he : inner ℝ (b 0) (b 0) ≠ 0 :=
    inner_self_ne_zero.mpr (b.ne_zero 0)
  have htail : G.submatrix Fin.succ Fin.succ =
      Matrix.gram ℝ (hunterGeneralProjectedBasis b) := by
    ext i j
    change inner ℝ (hunterCenter (b 0) (b i.succ))
        (hunterCenter (b 0) (b j.succ)) =
      inner ℝ (hunterGeneralProjectedBasis b i)
        (hunterGeneralProjectedBasis b j)
    rw [hunterGeneralProjectedBasis_apply,
      hunterGeneralProjectedBasis_apply]
    rfl
  have hzero : G 0 0 = inner ℝ (b 0) (b 0) := by
    simp [G, Matrix.gram_apply, hunterGeneralOrthogonalizedFamily]
  have hsucc : ∀ i : Fin n, G i.succ 0 = 0 := by
    intro i
    simp [G, Matrix.gram_apply, hunterGeneralOrthogonalizedFamily,
      real_inner_comm, inner_center_left (b 0) (b i.succ) he]
  change G.det = _
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, hzero]
  simp only [Fin.val_zero, pow_zero, one_mul]
  rw [Fin.succAbove_zero, htail]
  simp [hsucc]

/-- General Gram-determinant form of the orthogonal projection formula. -/
theorem det_gram_generalProjectedBasis_mul_inner_self
    (b : Basis (Fin (n + 1)) ℝ E) :
    (Matrix.gram ℝ (hunterGeneralProjectedBasis b)).det *
        inner ℝ (b 0) (b 0) =
      (Matrix.gram ℝ b).det := by
  rw [mul_comm]
  rw [← gram_det_generalOrthogonalizedBasis_block b]
  exact gram_det_generalOrthogonalizedBasis_eq b

variable [MeasurableSpace E] [BorelSpace E]

/-- General squared-covolume formula for projection away from a primitive
one-dimensional direction. -/
theorem hunterGeneralProjectedLattice_covolume_sq_mul_inner_self
    (b : Basis (Fin (n + 1)) ℝ E) :
    ZLattice.covolume (hunterGeneralProjectedLattice b) ^ 2 *
        inner ℝ (b 0) (b 0) =
      ZLattice.covolume (span ℤ (Set.range b)) ^ 2 := by
  rw [covolume_span_basis_sq_eq_det_gram
    (hunterGeneralProjectedBasis b)
    (orthonormalBasisOfBasis (hunterGeneralProjectedBasis b))]
  rw [covolume_span_basis_sq_eq_det_gram
    b (orthonormalBasisOfBasis b)]
  exact det_gram_generalProjectedBasis_mul_inner_self b

end
end TraceEuclidean
