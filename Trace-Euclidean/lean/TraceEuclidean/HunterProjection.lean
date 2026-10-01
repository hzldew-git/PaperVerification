import TraceEuclidean.HunterNumberField
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# Projection determinant for the cubic Hunter argument

This module isolates the Euclidean determinant identity behind Hunter's
degree-three projection.  Centering two vectors along a nonzero vector `e`
divides the squared three-dimensional volume by `‖e‖^2`.
-/

namespace TraceEuclidean

noncomputable section

open scoped RealInnerProductSpace

open MeasureTheory Module Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Remove the component of `x` parallel to a nonisotropic vector `e`. -/
def hunterCenter (e x : E) : E :=
  x - (inner ℝ e x / inner ℝ e e) • e

/-- The centered vector is perpendicular to the centering direction. -/
theorem inner_center_left (e x : E) (he : inner ℝ e e ≠ 0) :
    inner ℝ e (hunterCenter e x) = 0 := by
  simp only [hunterCenter, inner_sub_right, inner_smul_right]
  field_simp
  ring_nf

/-- Inner products of centered vectors are given by the Schur complement of
the one-dimensional Gram block. -/
theorem inner_center_center (e x y : E) (he : inner ℝ e e ≠ 0) :
    inner ℝ (hunterCenter e x) (hunterCenter e y) =
      inner ℝ x y - inner ℝ e x * inner ℝ e y / inner ℝ e e := by
  simp only [hunterCenter, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right]
  rw [real_inner_comm x e, real_inner_comm y e]
  field_simp
  ring

/-- Orthogonal centering along a nonzero direction, as a real linear map into
the orthogonal complement. -/
noncomputable def hunterCenterLinearMap (e : E)
    (he : inner ℝ e e ≠ 0) : E →ₗ[ℝ] (ℝ ∙ e)ᗮ where
  toFun x := ⟨hunterCenter e x,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      (inner_center_left e x he)⟩
  map_add' x y := by
    apply Subtype.ext
    simp [hunterCenter, inner_add_right, add_div, add_smul]
    abel
  map_smul' c x := by
    apply Subtype.ext
    simp [hunterCenter, inner_smul_right, smul_sub, smul_smul,
      mul_div_assoc]

@[simp]
theorem hunterCenterLinearMap_apply (e : E)
    (he : inner ℝ e e ≠ 0) (x : E) :
    ((hunterCenterLinearMap e he x : (ℝ ∙ e)ᗮ) : E) =
      hunterCenter e x :=
  rfl

/-- Centering the distinguished direction itself gives zero. -/
@[simp]
theorem hunterCenterLinearMap_self (e : E)
    (he : inner ℝ e e ≠ 0) :
    hunterCenterLinearMap e he e = 0 := by
  apply Subtype.ext
  change hunterCenter e e = 0
  rw [hunterCenter, div_self he]
  simp

/-- Every scalar multiple of the distinguished direction is killed by the
centering map. -/
@[simp]
theorem hunterCenterLinearMap_smul_self (e : E)
    (he : inner ℝ e e ≠ 0) (r : ℝ) :
    hunterCenterLinearMap e he (r • e) = 0 := by
  rw [map_smul, hunterCenterLinearMap_self]
  simp

/-- Centering two vectors along `e` gives the exact Gram-determinant
factorization used in the projected-lattice covolume formula. -/
theorem det_gram_center_pair_mul_inner_self
    (e x y : E) (he : inner ℝ e e ≠ 0) :
    (Matrix.gram ℝ ![hunterCenter e x, hunterCenter e y]).det *
        inner ℝ e e =
      (Matrix.gram ℝ ![e, x, y]).det := by
  have hxy : Matrix.vecHead (Matrix.vecTail ![x, y]) = y := rfl
  simp only [Matrix.det_fin_two, Matrix.det_fin_three, Matrix.gram_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_fin_one, hxy,
    inner_center_center e x x he,
    inner_center_center e x y he,
    inner_center_center e y x he,
    inner_center_center e y y he]
  rw [real_inner_comm x e, real_inner_comm y e, real_inner_comm y x]
  field_simp
  ring

section Covolume

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [DecidableEq ι] in
/-- An orthonormal fundamental parallelepiped has real volume one. -/
theorem volume_real_fundamentalDomain_orthonormal
    (o : OrthonormalBasis ι ℝ E) :
    volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
  rw [MeasureTheory.measureReal_def]
  rw [MeasureTheory.measure_congr
    (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
  simpa using congrArg ENNReal.toReal o.volume_parallelepiped

/-- The covolume of the integral span of a real basis is the absolute
determinant of that basis in orthonormal coordinates. -/
theorem covolume_span_basis_eq_abs_det
    (b : Basis ι ℝ E) (o : OrthonormalBasis ι ℝ E) :
    ZLattice.covolume (span ℤ (Set.range b)) =
      |o.toBasis.det b| := by
  rw [ZLattice.covolume_eq_det_mul_measureReal
    (span ℤ (Set.range b)) volume (b.restrictScalars ℤ) o.toBasis]
  have hdet :
      o.toBasis.det (((↑) : span ℤ (Set.range b) → E) ∘
        (b.restrictScalars ℤ)) = o.toBasis.det b := by
    congr 1
    funext i
    exact Basis.restrictScalars_apply ℤ b i
  rw [hdet, volume_real_fundamentalDomain_orthonormal o, mul_one]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The squared absolute determinant of a basis is its Gram determinant. -/
theorem abs_det_basis_sq_eq_det_gram
    (b : Basis ι ℝ E) (o : OrthonormalBasis ι ℝ E) :
    |o.toBasis.det b| ^ 2 = (Matrix.gram ℝ b).det := by
  let f : E →ₗ[ℝ] E :=
    (o.toBasis.equiv b (Equiv.refl ι)).toLinearMap
  have h := LinearMap.normDet_sq_eq_det_gram f o
  have hf : (fun i ↦ f (o i)) = b := by
    funext i
    dsimp only [f]
    exact o.toBasis.equiv_apply i b (Equiv.refl ι)
  rw [hf] at h
  rw [LinearMap.normDet_eq_abs_det] at h
  simpa [f, Basis.det_basis] using h

/-- Gram determinant form of the covolume of a basis lattice. -/
theorem covolume_span_basis_sq_eq_det_gram
    (b : Basis ι ℝ E) (o : OrthonormalBasis ι ℝ E) :
    ZLattice.covolume (span ℤ (Set.range b)) ^ 2 =
      (Matrix.gram ℝ b).det := by
  rw [covolume_span_basis_eq_abs_det b o]
  exact abs_det_basis_sq_eq_det_gram b o

end Covolume

section ProjectedBasis

variable [FiniteDimensional ℝ E]

/-- The two centered basis vectors, regarded as vectors in the orthogonal
complement of the first basis vector. -/
def hunterProjectedPair (b : Basis (Fin 3) ℝ E) :
    Fin 2 → (ℝ ∙ b 0)ᗮ :=
  let he : inner ℝ (b 0) (b 0) ≠ 0 :=
    inner_self_ne_zero.mpr (b.ne_zero 0)
  ![⟨hunterCenter (b 0) (b 1),
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        (inner_center_left (b 0) (b 1) he)⟩,
    ⟨hunterCenter (b 0) (b 2),
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        (inner_center_left (b 0) (b 2) he)⟩]

omit [FiniteDimensional ℝ E] in
/-- Exact determinant relation for the projected pair attached to a
three-dimensional basis. -/
theorem det_gram_projectedPair_mul_inner_self
    (b : Basis (Fin 3) ℝ E) :
    (Matrix.gram ℝ (hunterProjectedPair b)).det *
        inner ℝ (b 0) (b 0) =
      (Matrix.gram ℝ b).det := by
  let he : inner ℝ (b 0) (b 0) ≠ 0 :=
    inner_self_ne_zero.mpr (b.ne_zero 0)
  change
    (Matrix.gram ℝ
      (fun i ↦ ((hunterProjectedPair b i : (ℝ ∙ b 0)ᗮ) : E))).det *
        inner ℝ (b 0) (b 0) =
      (Matrix.gram ℝ b).det
  have hpair :
      (fun i ↦ ((hunterProjectedPair b i : (ℝ ∙ b 0)ᗮ) : E)) =
        ![hunterCenter (b 0) (b 1), hunterCenter (b 0) (b 2)] := by
    funext i
    fin_cases i <;> rfl
  have hb : (b : Fin 3 → E) = ![b 0, b 1, b 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hpair, hb]
  exact det_gram_center_pair_mul_inner_self (b 0) (b 1) (b 2) he

omit [FiniteDimensional ℝ E] in
/-- The projected pair is linearly independent. -/
theorem hunterProjectedPair_linearIndependent
    (b : Basis (Fin 3) ℝ E) :
    LinearIndependent ℝ (hunterProjectedPair b) := by
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  intro hzero
  have hfull : (Matrix.gram ℝ b).det ≠ 0 :=
    Matrix.det_gram_ne_zero_iff_linearIndependent.mpr b.linearIndependent
  apply hfull
  rw [← det_gram_projectedPair_mul_inner_self b, hzero, zero_mul]

/-- The centered pair as a real basis of the orthogonal complement. -/
noncomputable def hunterProjectedBasis
    (b : Basis (Fin 3) ℝ E) : Basis (Fin 2) ℝ ((ℝ ∙ b 0)ᗮ) := by
  letI : Fact (finrank ℝ E = 2 + 1) := ⟨by
    simpa using finrank_eq_card_basis b⟩
  exact basisOfLinearIndependentOfCardEqFinrank
    (hunterProjectedPair_linearIndependent b) (by
      rw [Fintype.card_fin,
        Submodule.finrank_orthogonal_span_singleton (n := 2) (b.ne_zero 0)])

omit [FiniteDimensional ℝ E] in
@[simp]
theorem hunterProjectedBasis_apply
    (b : Basis (Fin 3) ℝ E) (i : Fin 2) :
    hunterProjectedBasis b i = hunterProjectedPair b i := by
  simp [hunterProjectedBasis]

/-- The full rank-two integral lattice generated by the centered pair. -/
abbrev hunterProjectedLattice (b : Basis (Fin 3) ℝ E) :
    Submodule ℤ ((ℝ ∙ b 0)ᗮ) :=
  span ℤ (Set.range (hunterProjectedBasis b))

/-- Reindex the standard orthonormal basis by the index type of any supplied
real basis. -/
noncomputable def orthonormalBasisOfBasis
    {ι : Type*} [Fintype ι] (b : Basis ι ℝ E) :
    OrthonormalBasis ι ℝ E :=
  (stdOrthonormalBasis ℝ E).reindex
    (Fintype.equivOfCardEq (by simpa using finrank_eq_card_basis b))

section IntegralLift

variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

/-- Lift an integral vector in the centered rank-two lattice by using the same
two integral coordinates on the last two vectors of the original lattice
basis. -/
noncomputable def hunterIntegralLift
    (bz : Basis (Fin 3) ℤ L)
    (x : hunterProjectedLattice (bz.ofZLatticeBasis ℝ)) : L :=
  let b := bz.ofZLatticeBasis ℝ
  let c := ((hunterProjectedBasis b).restrictScalars ℤ).repr x
  ∑ i : Fin 2, c i • bz i.succ

omit [FiniteDimensional ℝ E] in
/-- Centering a lifted basis vector gives the corresponding projected basis
vector. -/
theorem hunterCenterLinearMap_basis_succ
    (b : Basis (Fin 3) ℝ E) (i : Fin 2) :
    hunterCenterLinearMap (b 0)
        (inner_self_ne_zero.mpr (b.ne_zero 0)) (b i.succ) =
      hunterProjectedBasis b i := by
  apply Subtype.ext
  rw [hunterProjectedBasis_apply]
  fin_cases i <;> rfl

/-- The integral lift maps back to the original projected-lattice vector under
orthogonal centering. -/
theorem hunterIntegralLift_center
    (bz : Basis (Fin 3) ℤ L)
    (x : hunterProjectedLattice (bz.ofZLatticeBasis ℝ)) :
    hunterCenterLinearMap ((bz.ofZLatticeBasis ℝ) 0)
        (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
        (((hunterIntegralLift bz x : L) : E)) =
      ((x : hunterProjectedLattice (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ) := by
  let b := bz.ofZLatticeBasis ℝ
  let c := ((hunterProjectedBasis b).restrictScalars ℤ).repr x
  have hcenter : ∀ i : Fin 2,
      hunterCenterLinearMap ((bz.ofZLatticeBasis ℝ) 0)
          (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
          (b i.succ) = hunterProjectedBasis b i := by
    intro i
    simpa [b] using hunterCenterLinearMap_basis_succ b i
  have hcoe : (((hunterIntegralLift bz x : L) : E)) =
      ∑ i : Fin 2, (c i : ℝ) • b i.succ := by
    simp [hunterIntegralLift, b, c, Int.cast_smul_eq_zsmul]
  rw [hcoe, map_sum]
  simp_rw [map_smul]
  simp_rw [hcenter]
  have hx :
      ∑ i : Fin 2, c i •
          ((hunterProjectedBasis b).restrictScalars ℤ) i = x :=
    ((hunterProjectedBasis b).restrictScalars ℤ).sum_repr x
  have hxval :
      ∑ i : Fin 2, c i • hunterProjectedBasis b i =
        ((x : hunterProjectedLattice b) : (ℝ ∙ b 0)ᗮ) := by
    have hcoeSum :
        (((∑ i : Fin 2, c i •
            ((hunterProjectedBasis b).restrictScalars ℤ) i) :
              hunterProjectedLattice b) : (ℝ ∙ b 0)ᗮ) =
          ∑ i : Fin 2, c i • hunterProjectedBasis b i := by
      apply Subtype.ext
      simp [Basis.restrictScalars_apply]
    rw [← hcoeSum]
    exact congrArg Subtype.val hx
  simpa only [Int.cast_smul_eq_zsmul] using hxval

end IntegralLift

variable [MeasurableSpace E] [BorelSpace E]

/-- Squared covolume form of the exact projection formula. -/
theorem hunterProjectedLattice_covolume_sq_mul_inner_self
    (b : Basis (Fin 3) ℝ E) :
    ZLattice.covolume (hunterProjectedLattice b) ^ 2 *
        inner ℝ (b 0) (b 0) =
      ZLattice.covolume (span ℤ (Set.range b)) ^ 2 := by
  rw [covolume_span_basis_sq_eq_det_gram
    (hunterProjectedBasis b)
    (orthonormalBasisOfBasis (hunterProjectedBasis b))]
  rw [covolume_span_basis_sq_eq_det_gram
    b (orthonormalBasisOfBasis b)]
  have hpb :
      (hunterProjectedBasis b : Fin 2 → (ℝ ∙ b 0)ᗮ) =
        hunterProjectedPair b := by
    funext i
    exact hunterProjectedBasis_apply b i
  rw [hpb]
  exact det_gram_projectedPair_mul_inner_self b

/-- If the distinguished basis vector has squared norm three, orthogonal
projection divides the covolume by `sqrt(3)`. -/
theorem hunterProjectedLattice_covolume_eq_div_sqrt_three
    (b : Basis (Fin 3) ℝ E)
    (hinner : inner ℝ (b 0) (b 0) = 3) :
    ZLattice.covolume (hunterProjectedLattice b) =
      ZLattice.covolume (span ℤ (Set.range b)) / Real.sqrt 3 := by
  have hsq := hunterProjectedLattice_covolume_sq_mul_inner_self b
  rw [hinner] at hsq
  have hprojPos : 0 < ZLattice.covolume (hunterProjectedLattice b) :=
    ZLattice.covolume_pos (hunterProjectedLattice b)
  have hfullPos : 0 < ZLattice.covolume (span ℤ (Set.range b)) :=
    ZLattice.covolume_pos (span ℤ (Set.range b))
  have hsqrtPos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  apply (eq_div_iff hsqrtPos.ne').2
  have hsquares :
      (ZLattice.covolume (hunterProjectedLattice b) * Real.sqrt 3) ^ 2 =
        ZLattice.covolume (span ℤ (Set.range b)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    exact hsq
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsquares with h | h
  · exact h
  · nlinarith [mul_pos hprojPos hsqrtPos]

/-- A three-dimensional basis whose first vector has squared norm three and
whose basis lattice has covolume below seven produces the Hunter short vector
in its centered rank-two lattice. -/
theorem hunterProjectedLattice_shortVector
    (b : Basis (Fin 3) ℝ E)
    (hinner : inner ℝ (b 0) (b 0) = 3)
    (hcov : ZLattice.covolume (span ℤ (Set.range b)) < 7) :
    ∃ x : hunterProjectedLattice b, x ≠ 0 ∧
      3 * ‖((x : hunterProjectedLattice b) : (ℝ ∙ b 0)ᗮ)‖ ^ 2 < 16 := by
  have hfin : Module.finrank ℝ ((ℝ ∙ b 0)ᗮ) = 2 := by
    simpa using finrank_eq_card_basis (hunterProjectedBasis b)
  have hcovProjected :
      ZLattice.covolume (hunterProjectedLattice b) <
        7 / Real.sqrt 3 := by
    rw [hunterProjectedLattice_covolume_eq_div_sqrt_three b hinner]
    exact div_lt_div_of_pos_right hcov (Real.sqrt_pos.2 (by norm_num))
  exact hunter_shortVector_of_covolume_lt_of_finrank_eq_two
    (hunterProjectedLattice b) hfin hcovProjected

end ProjectedBasis

end

end TraceEuclidean
