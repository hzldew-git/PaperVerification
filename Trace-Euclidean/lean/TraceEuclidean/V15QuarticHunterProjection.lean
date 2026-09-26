import TraceEuclidean.V15HunterProjection
import TraceEuclidean.V15QuarticPowerBasis
import TraceEuclidean.V15QuarticHunterGeometry

/-!
# Projection determinant for the quartic Hunter argument

This module proves the linear-algebraic part of Hunter's degree-four
projection. Centering the last three vectors of a four-dimensional basis
along its first vector produces a basis of the three-dimensional orthogonal
complement, and divides the covolume by the norm of the first vector.
-/

namespace TraceEuclidean

noncomputable section

open scoped RealInnerProductSpace

open MeasureTheory Module Submodule

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Centering three vectors along `e` gives the exact Gram-determinant
factorization used in the quartic projected-lattice covolume formula. -/
theorem v15_det_gram_center_triple_mul_inner_self
    (e x y z : E) (he : inner ℝ e e ≠ 0) :
    (Matrix.gram ℝ ![v15HunterCenter e x, v15HunterCenter e y,
        v15HunterCenter e z]).det * inner ℝ e e =
      (Matrix.gram ℝ ![e, x, y, z]).det := by
  have hcenterTail :
      Matrix.vecHead
          (Matrix.vecTail ![v15HunterCenter e y, v15HunterCenter e z]) =
        v15HunterCenter e z := rfl
  have htail : Matrix.vecHead (Matrix.vecTail ![x, y, z]) = y := rfl
  have htailTail :
      Matrix.vecHead (Matrix.vecTail (Matrix.vecTail ![x, y, z])) = z := rfl
  simp only [Matrix.det_fin_three, v15_det_fin_four, Matrix.gram_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, hcenterTail, htail, htailTail,
    v15_inner_center_center e x x he,
    v15_inner_center_center e x y he,
    v15_inner_center_center e x z he,
    v15_inner_center_center e y x he,
    v15_inner_center_center e y y he,
    v15_inner_center_center e y z he,
    v15_inner_center_center e z x he,
    v15_inner_center_center e z y he,
    v15_inner_center_center e z z he]
  rw [real_inner_comm x e, real_inner_comm y e, real_inner_comm z e,
    real_inner_comm y x, real_inner_comm z x, real_inner_comm z y]
  field_simp
  ring

section ProjectedBasis

variable [FiniteDimensional ℝ E]

/-- The three centered basis vectors, regarded as vectors in the orthogonal
complement of the first basis vector. -/
def v15QuarticHunterProjectedTriple (b : Basis (Fin 4) ℝ E) :
    Fin 3 → (ℝ ∙ b 0)ᗮ :=
  let he : inner ℝ (b 0) (b 0) ≠ 0 :=
    inner_self_ne_zero.mpr (b.ne_zero 0)
  ![⟨v15HunterCenter (b 0) (b 1),
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        (v15_inner_center_left (b 0) (b 1) he)⟩,
    ⟨v15HunterCenter (b 0) (b 2),
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        (v15_inner_center_left (b 0) (b 2) he)⟩,
    ⟨v15HunterCenter (b 0) (b 3),
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        (v15_inner_center_left (b 0) (b 3) he)⟩]

omit [FiniteDimensional ℝ E] in
/-- Exact determinant relation for the projected triple attached to a
four-dimensional basis. -/
theorem v15_det_gram_quarticProjectedTriple_mul_inner_self
    (b : Basis (Fin 4) ℝ E) :
    (Matrix.gram ℝ (v15QuarticHunterProjectedTriple b)).det *
        inner ℝ (b 0) (b 0) =
      (Matrix.gram ℝ b).det := by
  let he : inner ℝ (b 0) (b 0) ≠ 0 :=
    inner_self_ne_zero.mpr (b.ne_zero 0)
  change
    (Matrix.gram ℝ
      (fun i ↦ ((v15QuarticHunterProjectedTriple b i : (ℝ ∙ b 0)ᗮ) : E))).det *
        inner ℝ (b 0) (b 0) =
      (Matrix.gram ℝ b).det
  have htriple :
      (fun i ↦ ((v15QuarticHunterProjectedTriple b i : (ℝ ∙ b 0)ᗮ) : E)) =
        ![v15HunterCenter (b 0) (b 1), v15HunterCenter (b 0) (b 2),
          v15HunterCenter (b 0) (b 3)] := by
    funext i
    fin_cases i <;> rfl
  have hb : (b : Fin 4 → E) = ![b 0, b 1, b 2, b 3] := by
    funext i
    fin_cases i <;> rfl
  rw [htriple, hb]
  exact v15_det_gram_center_triple_mul_inner_self
    (b 0) (b 1) (b 2) (b 3) he

omit [FiniteDimensional ℝ E] in
/-- The projected triple is linearly independent. -/
theorem v15QuarticHunterProjectedTriple_linearIndependent
    (b : Basis (Fin 4) ℝ E) :
    LinearIndependent ℝ (v15QuarticHunterProjectedTriple b) := by
  apply Matrix.linearIndependent_of_det_gram_ne_zero
  intro hzero
  have hfull : (Matrix.gram ℝ b).det ≠ 0 :=
    Matrix.det_gram_ne_zero_iff_linearIndependent.mpr b.linearIndependent
  apply hfull
  rw [← v15_det_gram_quarticProjectedTriple_mul_inner_self b,
    hzero, zero_mul]

/-- The centered triple as a real basis of the orthogonal complement. -/
noncomputable def v15QuarticHunterProjectedBasis
    (b : Basis (Fin 4) ℝ E) : Basis (Fin 3) ℝ ((ℝ ∙ b 0)ᗮ) := by
  letI : Fact (finrank ℝ E = 3 + 1) := ⟨by
    simpa using finrank_eq_card_basis b⟩
  exact basisOfLinearIndependentOfCardEqFinrank
    (v15QuarticHunterProjectedTriple_linearIndependent b) (by
      rw [Fintype.card_fin,
        Submodule.finrank_orthogonal_span_singleton (n := 3) (b.ne_zero 0)])

omit [FiniteDimensional ℝ E] in
@[simp]
theorem v15QuarticHunterProjectedBasis_apply
    (b : Basis (Fin 4) ℝ E) (i : Fin 3) :
    v15QuarticHunterProjectedBasis b i =
      v15QuarticHunterProjectedTriple b i := by
  simp [v15QuarticHunterProjectedBasis]

/-- The full rank-three integral lattice generated by the centered triple. -/
abbrev v15QuarticHunterProjectedLattice (b : Basis (Fin 4) ℝ E) :
    Submodule ℤ ((ℝ ∙ b 0)ᗮ) :=
  span ℤ (Set.range (v15QuarticHunterProjectedBasis b))

section IntegralLift

variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

/-- Lift an integral vector in the centered rank-three lattice by using the
same three integral coordinates on the last three vectors of the original
lattice basis. -/
noncomputable def v15QuarticHunterIntegralLift
    (bz : Basis (Fin 4) ℤ L)
    (x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ)) : L :=
  let b := bz.ofZLatticeBasis ℝ
  let c := ((v15QuarticHunterProjectedBasis b).restrictScalars ℤ).repr x
  ∑ i : Fin 3, c i • bz i.succ

@[simp]
theorem v15QuarticHunterIntegralLift_zsmul
    (bz : Basis (Fin 4) ℤ L) (n : ℤ)
    (x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ)) :
    v15QuarticHunterIntegralLift bz (n • x) =
      n • v15QuarticHunterIntegralLift bz x := by
  simp [v15QuarticHunterIntegralLift, Finset.smul_sum, smul_smul]

omit [FiniteDimensional ℝ E] in
/-- Centering a lifted quartic basis vector gives the corresponding
projected basis vector. -/
theorem v15QuarticHunterCenterLinearMap_basis_succ
    (b : Basis (Fin 4) ℝ E) (i : Fin 3) :
    v15HunterCenterLinearMap (b 0)
        (inner_self_ne_zero.mpr (b.ne_zero 0)) (b i.succ) =
      v15QuarticHunterProjectedBasis b i := by
  apply Subtype.ext
  rw [v15QuarticHunterProjectedBasis_apply]
  fin_cases i <;> rfl

/-- The quartic integral lift maps back to the original projected-lattice
vector under orthogonal centering. -/
theorem v15QuarticHunterIntegralLift_center
    (bz : Basis (Fin 4) ℤ L)
    (x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ)) :
    v15HunterCenterLinearMap ((bz.ofZLatticeBasis ℝ) 0)
        (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
        (((v15QuarticHunterIntegralLift bz x : L) : E)) =
      ((x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ) := by
  let b := bz.ofZLatticeBasis ℝ
  let c := ((v15QuarticHunterProjectedBasis b).restrictScalars ℤ).repr x
  have hcenter : ∀ i : Fin 3,
      v15HunterCenterLinearMap ((bz.ofZLatticeBasis ℝ) 0)
          (inner_self_ne_zero.mpr ((bz.ofZLatticeBasis ℝ).ne_zero 0))
          (b i.succ) = v15QuarticHunterProjectedBasis b i := by
    intro i
    simpa [b] using v15QuarticHunterCenterLinearMap_basis_succ b i
  have hcoe : (((v15QuarticHunterIntegralLift bz x : L) : E)) =
      ∑ i : Fin 3, (c i : ℝ) • b i.succ := by
    simp [v15QuarticHunterIntegralLift, b, c, Int.cast_smul_eq_zsmul]
  rw [hcoe, map_sum]
  simp_rw [map_smul]
  simp_rw [hcenter]
  have hx :
      ∑ i : Fin 3, c i •
          ((v15QuarticHunterProjectedBasis b).restrictScalars ℤ) i = x :=
    ((v15QuarticHunterProjectedBasis b).restrictScalars ℤ).sum_repr x
  have hxval :
      ∑ i : Fin 3, c i • v15QuarticHunterProjectedBasis b i =
        ((x : v15QuarticHunterProjectedLattice b) : (ℝ ∙ b 0)ᗮ) := by
    have hcoeSum :
        (((∑ i : Fin 3, c i •
            ((v15QuarticHunterProjectedBasis b).restrictScalars ℤ) i) :
              v15QuarticHunterProjectedLattice b) : (ℝ ∙ b 0)ᗮ) =
          ∑ i : Fin 3, c i • v15QuarticHunterProjectedBasis b i := by
      apply Subtype.ext
      simp [Basis.restrictScalars_apply]
    rw [← hcoeSum]
    exact congrArg Subtype.val hx
  simpa only [Int.cast_smul_eq_zsmul] using hxval

end IntegralLift

variable [MeasurableSpace E] [BorelSpace E]

/-- Squared covolume form of the exact quartic projection formula. -/
theorem v15QuarticHunterProjectedLattice_covolume_sq_mul_inner_self
    (b : Basis (Fin 4) ℝ E) :
    ZLattice.covolume (v15QuarticHunterProjectedLattice b) ^ 2 *
        inner ℝ (b 0) (b 0) =
      ZLattice.covolume (span ℤ (Set.range b)) ^ 2 := by
  rw [v15_covolume_span_basis_sq_eq_det_gram
    (v15QuarticHunterProjectedBasis b)
    (v15OrthonormalBasisOfBasis (v15QuarticHunterProjectedBasis b))]
  rw [v15_covolume_span_basis_sq_eq_det_gram
    b (v15OrthonormalBasisOfBasis b)]
  have hpb :
      (v15QuarticHunterProjectedBasis b : Fin 3 → (ℝ ∙ b 0)ᗮ) =
        v15QuarticHunterProjectedTriple b := by
    funext i
    exact v15QuarticHunterProjectedBasis_apply b i
  rw [hpb]
  exact v15_det_gram_quarticProjectedTriple_mul_inner_self b

/-- If the distinguished basis vector has squared norm four, orthogonal
projection divides the covolume by two. -/
theorem v15QuarticHunterProjectedLattice_covolume_eq_div_two
    (b : Basis (Fin 4) ℝ E)
    (hinner : inner ℝ (b 0) (b 0) = 4) :
    ZLattice.covolume (v15QuarticHunterProjectedLattice b) =
      ZLattice.covolume (span ℤ (Set.range b)) / 2 := by
  have hsq :=
    v15QuarticHunterProjectedLattice_covolume_sq_mul_inner_self b
  rw [hinner] at hsq
  have hprojPos :
      0 < ZLattice.covolume (v15QuarticHunterProjectedLattice b) :=
    ZLattice.covolume_pos (v15QuarticHunterProjectedLattice b)
  have hfullPos : 0 < ZLattice.covolume (span ℤ (Set.range b)) :=
    ZLattice.covolume_pos (span ℤ (Set.range b))
  apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
  have hsquares :
      (ZLattice.covolume (v15QuarticHunterProjectedLattice b) * 2) ^ 2 =
        ZLattice.covolume (span ℤ (Set.range b)) ^ 2 := by
    nlinarith
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsquares with h | h
  · exact h
  · nlinarith

/-- The exact three-dimensional Hermite input needed by the quartic Hunter
argument, written without cube roots. It is equivalent to the sharp bound
`γ₃³ = 2` for a lattice presented by a real basis. -/
def V15HermiteThreeInput : Prop :=
  ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (c : Basis (Fin 3) ℝ V),
      ∃ x : span ℤ (Set.range c), x ≠ 0 ∧
        ‖((x : span ℤ (Set.range c)) : V)‖ ^ 6 ≤
          2 * ZLattice.covolume (span ℤ (Set.range c)) ^ 2

/-- The sharp three-dimensional Hermite input and a full covolume square
below `725` produce the strict quartic Hunter spread bound. -/
theorem v15QuarticHunterProjectedLattice_shortVector
    (hHermite : V15HermiteThreeInput.{u})
    (b : Basis (Fin 4) ℝ E)
    (hinner : inner ℝ (b 0) (b 0) = 4)
    (hcov : ZLattice.covolume (span ℤ (Set.range b)) ^ 2 < 725) :
    ∃ x : v15QuarticHunterProjectedLattice b, x ≠ 0 ∧
      4 * ‖((x : v15QuarticHunterProjectedLattice b) : (ℝ ∙ b 0)ᗮ)‖ ^ 2 < 29 := by
  rcases hHermite ↥((ℝ ∙ b 0)ᗮ) (v15QuarticHunterProjectedBasis b) with
    ⟨x, hx, hshort⟩
  refine ⟨x, hx, ?_⟩
  have hsq :=
    v15QuarticHunterProjectedLattice_covolume_sq_mul_inner_self b
  rw [hinner] at hsq
  let r : ℝ :=
    ‖((x : v15QuarticHunterProjectedLattice b) : (ℝ ∙ b 0)ᗮ)‖
  have hr : 0 ≤ r := norm_nonneg _
  have hcube : (4 * r ^ 2) ^ 3 < (29 : ℝ) ^ 3 := by
    have hr6 : r ^ 6 ≤
        2 * ZLattice.covolume (v15QuarticHunterProjectedLattice b) ^ 2 := by
      simpa [r] using hshort
    nlinarith [sq_nonneg
      (ZLattice.covolume (v15QuarticHunterProjectedLattice b)),
      sq_nonneg (ZLattice.covolume (span ℤ (Set.range b)))]
  exact lt_of_pow_lt_pow_left₀ 3 (by norm_num : (0 : ℝ) ≤ 29) hcube

/-- The elementary three-dimensional Minkowski ball gives the weaker short
vector bound used by the enlarged quartic coefficient search. -/
theorem v15QuarticHunterProjectedLattice_shortVector_minkowski
    (b : Basis (Fin 4) ℝ E)
    (hinner : inner ℝ (b 0) (b 0) = 4)
    (hcov : ZLattice.covolume (span ℤ (Set.range b)) ^ 2 < 725) :
    ∃ x : v15QuarticHunterProjectedLattice b, x ≠ 0 ∧
      4 * ‖((x : v15QuarticHunterProjectedLattice b) :
        (ℝ ∙ b 0)ᗮ)‖ ^ 2 < 35 := by
  have hfin : Module.finrank ℝ ((ℝ ∙ b 0)ᗮ) = 3 := by
    simpa using finrank_eq_card_basis (v15QuarticHunterProjectedBasis b)
  have hfullPos : 0 < ZLattice.covolume (span ℤ (Set.range b)) :=
    ZLattice.covolume_pos (span ℤ (Set.range b))
  have hfull : ZLattice.covolume (span ℤ (Set.range b)) <
      Real.sqrt 725 := by
    rw [← sq_lt_sq₀ hfullPos.le (Real.sqrt_nonneg 725)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 725)]
    exact hcov
  have hprojected :
      ZLattice.covolume (v15QuarticHunterProjectedLattice b) <
        Real.sqrt 725 / 2 := by
    rw [v15QuarticHunterProjectedLattice_covolume_eq_div_two b hinner]
    exact div_lt_div_of_pos_right hfull (by norm_num)
  exact
    v15_quartic_hunter_shortVector_of_covolume_lt_of_finrank_eq_three
      (v15QuarticHunterProjectedLattice b) hfin hprojected

end ProjectedBasis

end

end TraceEuclidean
