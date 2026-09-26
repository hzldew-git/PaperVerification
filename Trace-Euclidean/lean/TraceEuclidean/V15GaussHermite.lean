import TraceEuclidean.V15GaussBasis
import TraceEuclidean.V15HunterProjection

/-!
# The sharp binary Hermite bound from Gauss reduction

Gauss reduction gives the sharp two-dimensional estimate

`3 * ||v||^4 <= 4 * covolume(L)^2`

whenever a positive integral multiple of the Gram form is integer valued.
The scaled integral formulation is the one needed for the quotient of the
quartic Hunter lattice by a quadratic-subfield direction.
-/

namespace TraceEuclidean

noncomputable section

open MeasureTheory Module Submodule
open scoped RealInnerProductSpace

universe u

/-- Gauss reduction implies the sharp binary Hermite inequality for a
lattice whose Gram form becomes integral after multiplication by a positive
integer. -/
theorem v15_exists_shortVector_gauss_of_scaled_integral_gram
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (Bstart : Basis (Fin 2) ℤ L)
    (scale : ℕ) (hscale : 0 < scale)
    (Q : L → ℕ) (C : L → L → ℤ)
    (hneg : ∀ x, Q (-x) = Q x)
    (hadd : ∀ x y, (Q (x + y) : ℤ) =
      (Q x : ℤ) + (Q y : ℤ) + 2 * C x y)
    (hsub : ∀ x y, (Q (x - y) : ℤ) =
      (Q x : ℤ) + (Q y : ℤ) - 2 * C x y)
    (hCneg : ∀ x y, C x (-y) = -C x y)
    (hQ : ∀ x, (Q x : ℝ) = scale * ‖((x : L) : V)‖ ^ 2)
    (hC : ∀ x y, (C x y : ℝ) =
      scale * inner ℝ (((x : L) : V)) (((y : L) : V))) :
    ∃ x : L, x ≠ 0 ∧
      3 * ‖((x : L) : V)‖ ^ 4 ≤ 4 * ZLattice.covolume L ^ 2 := by
  obtain ⟨B, horder, hCnonneg, hCupper⟩ :=
    v15_exists_gauss_basis Bstart Q C hneg hadd hsub hCneg
  refine ⟨B 0, B.ne_zero 0, ?_⟩
  let b : Basis (Fin 2) ℝ V := B.ofZLatticeBasis ℝ
  have hb0 : b 0 = ((B 0 : L) : V) := by
    exact B.ofZLatticeBasis_apply ℝ L 0
  have hb1 : b 1 = ((B 1 : L) : V) := by
    exact B.ofZLatticeBasis_apply ℝ L 1
  have hcov : ZLattice.covolume L ^ 2 = (Matrix.gram ℝ b).det := by
    rw [← B.ofZLatticeBasis_span ℝ]
    exact v15_covolume_span_basis_sq_eq_det_gram b
      (v15OrthonormalBasisOfBasis b)
  have hdet : (Matrix.gram ℝ b).det =
      inner ℝ (b 0) (b 0) * inner ℝ (b 1) (b 1) -
        inner ℝ (b 0) (b 1) ^ 2 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.gram_apply]
    rw [real_inner_comm (b 1) (b 0)]
    ring
  let A : ℝ := Q (B 0)
  let D : ℝ := Q (B 1)
  let R : ℝ := C (B 0) (B 1)
  have hA : A = scale * ‖((B 0 : L) : V)‖ ^ 2 := by
    simpa [A] using hQ (B 0)
  have hD : D = scale * ‖((B 1 : L) : V)‖ ^ 2 := by
    simpa [D] using hQ (B 1)
  have hR : R = scale * inner ℝ (((B 0 : L) : V)) (((B 1 : L) : V)) := by
    simpa [R] using hC (B 0) (B 1)
  have horderR : A ≤ D := by
    change (Q (B 0) : ℝ) ≤ (Q (B 1) : ℝ)
    exact_mod_cast horder
  have hRnonneg : 0 ≤ R := by
    change (0 : ℝ) ≤ (C (B 0) (B 1) : ℝ)
    exact_mod_cast hCnonneg
  have hRupper : 2 * R ≤ A := by
    change (2 : ℝ) * (C (B 0) (B 1) : ℝ) ≤ (Q (B 0) : ℝ)
    exact_mod_cast hCupper
  have hA_nonneg : 0 ≤ A := by positivity
  have hscaledDet :
      A * D - R ^ 2 = (scale : ℝ) ^ 2 * ZLattice.covolume L ^ 2 := by
    rw [hcov, hdet, hb0, hb1, hA, hD, hR]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  have hgauss : 3 * A ^ 2 ≤ 4 * (A * D - R ^ 2) := by
    nlinarith
  have hscaleR : 0 < (scale : ℝ) := by exact_mod_cast hscale
  rw [hscaledDet, hA] at hgauss
  nlinarith [sq_pos_of_pos hscaleR]

/-- Choice-free interface to the preceding theorem.  It is enough to know
that one positive integral multiple of every lattice inner product is an
integer. -/
theorem v15_exists_shortVector_gauss_of_scaled_inner_integral
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (Bstart : Basis (Fin 2) ℤ L)
    (scale : ℕ) (hscale : 0 < scale)
    (hIntegral : ∀ x y : L, ∃ z : ℤ,
      (z : ℝ) = scale * inner ℝ (((x : L) : V)) (((y : L) : V))) :
    ∃ x : L, x ≠ 0 ∧
      3 * ‖((x : L) : V)‖ ^ 4 ≤ 4 * ZLattice.covolume L ^ 2 := by
  classical
  let C : L → L → ℤ := fun x y ↦ Classical.choose (hIntegral x y)
  have hC : ∀ x y : L, (C x y : ℝ) =
      scale * inner ℝ (((x : L) : V)) (((y : L) : V)) := by
    intro x y
    exact Classical.choose_spec (hIntegral x y)
  have hCdiag_nonneg : ∀ x : L, 0 ≤ C x x := by
    intro x
    have hreal : (0 : ℝ) ≤ (C x x : ℝ) := by
      rw [hC]
      exact mul_nonneg (by exact_mod_cast hscale.le) (real_inner_self_nonneg)
    exact_mod_cast hreal
  let Q : L → ℕ := fun x ↦ (C x x).toNat
  have hQint : ∀ x : L, (Q x : ℤ) = C x x := by
    intro x
    simp [Q, Int.toNat_of_nonneg (hCdiag_nonneg x)]
  have hQinner : ∀ x : L, (Q x : ℝ) =
      scale * inner ℝ (((x : L) : V)) (((x : L) : V)) := by
    intro x
    rw [show (Q x : ℝ) = ((Q x : ℤ) : ℝ) by norm_cast, hQint, hC]
  have hQ : ∀ x : L, (Q x : ℝ) =
      scale * ‖((x : L) : V)‖ ^ 2 := by
    intro x
    rw [hQinner, real_inner_self_eq_norm_sq]
  have hneg : ∀ x : L, Q (-x) = Q x := by
    intro x
    apply Nat.cast_injective (R := ℝ)
    rw [hQinner, hQinner]
    simp
  have hadd : ∀ x y : L, (Q (x + y) : ℤ) =
      (Q x : ℤ) + (Q y : ℤ) + 2 * C x y := by
    intro x y
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [hQinner, hQinner, hQinner, hC]
    simp only [Submodule.coe_add, inner_add_left, inner_add_right]
    rw [real_inner_comm (((y : L) : V)) (((x : L) : V))]
    ring
  have hsub : ∀ x y : L, (Q (x - y) : ℤ) =
      (Q x : ℤ) + (Q y : ℤ) - 2 * C x y := by
    intro x y
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [hQinner, hQinner, hQinner, hC]
    simp only [Submodule.coe_sub, inner_sub_left, inner_sub_right]
    rw [real_inner_comm (((y : L) : V)) (((x : L) : V))]
    ring
  have hCneg : ∀ x y : L, C x (-y) = -C x y := by
    intro x y
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [hC, hC]
    simp
  exact v15_exists_shortVector_gauss_of_scaled_integral_gram
    L Bstart scale hscale Q C hneg hadd hsub hCneg hQ hC

/-- Projecting a rank-three integral lattice along a basis vector preserves
integrality after multiplying the Gram form by `scale^2 * d`, where `d` is
the squared norm of the distinguished vector. -/
theorem v15_hunterProjectedLattice_scaled_inner_integral
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (B : Basis (Fin 3) ℤ L)
    (scale d : ℕ) (hscale : 0 < scale) (hd : 0 < d)
    (hinner : inner ℝ ((B.ofZLatticeBasis ℝ) 0)
      ((B.ofZLatticeBasis ℝ) 0) = d)
    (hIntegral : ∀ x y : L, ∃ z : ℤ,
      (z : ℝ) = scale * inner ℝ (((x : L) : V)) (((y : L) : V))) :
    ∀ x y : v15HunterProjectedLattice (B.ofZLatticeBasis ℝ),
      ∃ z : ℤ, (z : ℝ) = (scale ^ 2 * d) *
        inner ℝ
          (((x : v15HunterProjectedLattice (B.ofZLatticeBasis ℝ)) :
            (ℝ ∙ (B.ofZLatticeBasis ℝ) 0)ᗮ))
          (((y : v15HunterProjectedLattice (B.ofZLatticeBasis ℝ)) :
            (ℝ ∙ (B.ofZLatticeBasis ℝ) 0)ᗮ)) := by
  intro x y
  let b := B.ofZLatticeBasis ℝ
  let ux : L := B 0
  let vx : L := v15HunterIntegralLift B x
  let vy : L := v15HunterIntegralLift B y
  obtain ⟨A, hA⟩ := hIntegral vx vy
  obtain ⟨R, hR⟩ := hIntegral ux vx
  obtain ⟨S, hS⟩ := hIntegral ux vy
  refine ⟨((scale * d : ℕ) : ℤ) * A - R * S, ?_⟩
  have hu : (((ux : L) : V)) = b 0 := by
    exact (B.ofZLatticeBasis_apply ℝ L 0).symm
  have hxcenter := v15HunterIntegralLift_center B x
  have hycenter := v15HunterIntegralLift_center B y
  have hscaleR : (scale : ℝ) ≠ 0 := by exact_mod_cast hscale.ne'
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hbinner : inner ℝ (b 0) (b 0) ≠ 0 := by
    rw [hinner]
    exact_mod_cast hd.ne'
  push_cast
  rw [hA, hR, hS, hu]
  change ((scale : ℝ) * d) *
      (scale * inner ℝ (((vx : L) : V)) (((vy : L) : V))) -
        scale * inner ℝ (b 0) (((vx : L) : V)) *
          (scale * inner ℝ (b 0) (((vy : L) : V))) = _
  rw [show (((x : v15HunterProjectedLattice b) :
      (ℝ ∙ b 0)ᗮ)) =
        v15HunterCenterLinearMap (b 0)
          (inner_self_ne_zero.mpr (b.ne_zero 0)) (((vx : L) : V)) by
      exact hxcenter.symm]
  rw [show (((y : v15HunterProjectedLattice b) :
      (ℝ ∙ b 0)ᗮ)) =
        v15HunterCenterLinearMap (b 0)
          (inner_self_ne_zero.mpr (b.ne_zero 0)) (((vy : L) : V)) by
      exact hycenter.symm]
  change _ = (scale : ℝ) ^ 2 * d *
    inner ℝ (v15HunterCenter (b 0) (((vx : L) : V)))
      (v15HunterCenter (b 0) (((vy : L) : V)))
  rw [v15_inner_center_center _ _ _ hbinner]
  rw [hinner]
  field_simp

/-- The projected rank-two lattice therefore satisfies the sharp Gauss
short-vector estimate. -/
theorem v15_exists_hunterProjected_shortVector_gauss
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (B : Basis (Fin 3) ℤ L)
    (scale d : ℕ) (hscale : 0 < scale) (hd : 0 < d)
    (hinner : inner ℝ ((B.ofZLatticeBasis ℝ) 0)
      ((B.ofZLatticeBasis ℝ) 0) = d)
    (hIntegral : ∀ x y : L, ∃ z : ℤ,
      (z : ℝ) = scale * inner ℝ (((x : L) : V)) (((y : L) : V))) :
    ∃ x : v15HunterProjectedLattice (B.ofZLatticeBasis ℝ), x ≠ 0 ∧
      3 * ‖((x : v15HunterProjectedLattice (B.ofZLatticeBasis ℝ)) :
        (ℝ ∙ (B.ofZLatticeBasis ℝ) 0)ᗮ)‖ ^ 4 ≤
          4 * ZLattice.covolume
            (v15HunterProjectedLattice (B.ofZLatticeBasis ℝ)) ^ 2 := by
  let projectedBasis :=
    (v15HunterProjectedBasis (B.ofZLatticeBasis ℝ)).restrictScalars ℤ
  have hProjectedIntegral :
      ∀ x y : v15HunterProjectedLattice (B.ofZLatticeBasis ℝ),
        ∃ z : ℤ, (z : ℝ) = ((scale ^ 2 * d : ℕ) : ℝ) *
          inner ℝ
            (((x : v15HunterProjectedLattice (B.ofZLatticeBasis ℝ)) :
              (ℝ ∙ (B.ofZLatticeBasis ℝ) 0)ᗮ))
            (((y : v15HunterProjectedLattice (B.ofZLatticeBasis ℝ)) :
              (ℝ ∙ (B.ofZLatticeBasis ℝ) 0)ᗮ)) := by
    intro x y
    obtain ⟨z, hz⟩ :=
      v15_hunterProjectedLattice_scaled_inner_integral
        L B scale d hscale hd hinner hIntegral x y
    refine ⟨z, ?_⟩
    rw [hz]
    push_cast
    rfl
  exact v15_exists_shortVector_gauss_of_scaled_inner_integral
    (v15HunterProjectedLattice (B.ofZLatticeBasis ℝ)) projectedBasis
    (scale ^ 2 * d) (by positivity)
    hProjectedIntegral

end

end TraceEuclidean
