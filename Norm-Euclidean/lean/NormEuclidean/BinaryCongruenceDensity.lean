import NormEuclidean.LocalNormDensity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Actual binary Gram congruence counts

The solutions are literal matrices satisfying `transpose M * G * M = G`,
where `G = diag(1,-d)`. They are parametrized by the actual norm-one group
and the determinant equation `d * delta² = d`. This keeps the extra
determinant choices visible at ramified and dyadic levels.
-/

noncomputable section

namespace NormEuclidean.BinaryCongruenceDensity

open LocalNormCayley
open scoped Matrix QuadraticAlgebra

variable {R : Type*} [CommRing R]

/-- The binary norm model's actual integral Gram matrix. -/
def gram (d : R) : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, -d]

/-- Matrices preserving the Gram matrix over the coefficient ring itself. -/
def Solutions (R : Type*) [CommRing R] (d : R) :=
  {M : Matrix (Fin 2) (Fin 2) R // M.transpose * gram d * M = gram d}

/-- The determinant constraint, retaining annihilator contributions. -/
def Determinants (R : Type*) [CommRing R] (d : R) := {t : R // d * t ^ 2 = d}

/-- All three independent matrix equations, with no invertibility premise. -/
theorem matrix_iff (d : R) (M : Matrix (Fin 2) (Fin 2) R) :
    M.transpose * gram d * M = gram d ↔
      M 0 0 ^ 2 - d * M 1 0 ^ 2 = 1 ∧
      M 0 0 * M 0 1 - d * M 1 0 * M 1 1 = 0 ∧
      M 0 1 ^ 2 - d * M 1 1 ^ 2 = -d := by
  constructor
  · intro h
    have h00 := congrArg (fun A ↦ A 0 0) h
    have h01 := congrArg (fun A ↦ A 0 1) h
    have h11 := congrArg (fun A ↦ A 1 1) h
    simp [gram, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h11
    exact ⟨by linear_combination h00, by linear_combination h01, by linear_combination h11⟩
  · rintro ⟨h00, h01, h11⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gram, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination h00
    · linear_combination h01
    · linear_combination h01
    · linear_combination h11

private theorem second_column (d : R) (M : Solutions R d) :
    M.val 0 1 = d * M.val 1 0 * M.val.det ∧
      M.val 1 1 = M.val 0 0 * M.val.det := by
  obtain ⟨ha, hm, _⟩ := (matrix_iff d M.val).mp M.property
  simp only [Matrix.det_fin_two]
  constructor
  · linear_combination -M.val 0 1 * ha + M.val 0 0 * hm
  · linear_combination -M.val 1 1 * ha + M.val 1 0 * hm

/-- The determinant condition follows from the literal matrix equation. -/
theorem determinant_eq (d : R) (M : Solutions R d) : d * M.val.det ^ 2 = d := by
  obtain ⟨ha, hm, hb⟩ := (matrix_iff d M.val).mp M.property
  simp only [Matrix.det_fin_two]
  linear_combination -(M.val 0 1 ^ 2 - d * M.val 1 1 ^ 2) * ha - hb +
    (M.val 0 0 * M.val 0 1 - d * M.val 1 0 * M.val 1 1) * hm

/-- Exact classification of all congruence solutions, even for nonunit parameters. -/
def solutionEquiv (d : R) : Solutions R d ≃ NormOne R d × Determinants R d where
  toFun M := (mk d (M.val 0 0) (M.val 1 0) ((matrix_iff d M.val).mp M.property).1,
    ⟨M.val.det, determinant_eq d M⟩)
  invFun p := ⟨!![p.1.val.re, d * p.1.val.im * p.2.val;
    p.1.val.im, p.1.val.re * p.2.val], (matrix_iff d _).mpr (by
      dsimp
      refine ⟨norm_eq d p.1, ?_, ?_⟩
      · ring
      · linear_combination -d * p.2.val ^ 2 * norm_eq d p.1 - p.2.property)⟩
  left_inv M := by
    have hb := (second_column d M).1
    have he := (second_column d M).2
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact hb.symm
    · rfl
    · exact he.symm
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext; rfl
    · apply Subtype.ext
      dsimp
      rw [Matrix.det_fin_two]
      change (p.1.val.re * (p.1.val.re * p.2.val) -
        (d * p.1.val.im * p.2.val) * p.1.val.im) = p.2.val
      linear_combination p.2.val * norm_eq d p.1

/-- The exact count retains the determinant factor at every congruence level. -/
theorem solutions_card (d : R) :
    Nat.card (Solutions R d) = Nat.card (NormOne R d) * Nat.card (Determinants R d) := by
  rw [Nat.card_congr (solutionEquiv d), Nat.card_prod]

/-- Full Gram self-count with the binary orthogonal normalization. -/
def selfDensity (R : Type*) [CommRing R] (d : R) : ℝ :=
  (Nat.card (Solutions R d) : ℝ) / (2 * Nat.card R)

/-- The normalization exposes exactly which determinant count is still needed. -/
theorem selfDensity_eq (d : R) : selfDensity R d =
    LocalNormDensity.density R d * ((Nat.card (Determinants R d) : ℝ) / 2) := by
  unfold selfDensity LocalNormDensity.density
  rw [solutions_card, Nat.cast_mul]
  ring

/-- The actual annihilator ideal of the parameter. -/
def annihilator (d : R) : Ideal R := (Ideal.span ({d} : Set R)).annihilator

/-- Membership in the parameter's annihilator. -/
theorem mem_annihilator (d x : R) : x ∈ annihilator d ↔ d * x = 0 := by
  rw [annihilator, Submodule.mem_annihilator_span_singleton]
  simp only [smul_eq_mul, mul_comm]

private theorem determinant_branches [IsLocalRing R] (d : R) (h2 : IsUnit (2 : R))
    (t : Determinants R d) : d * (t.val - 1) = 0 ∨ d * (t.val + 1) = 0 := by
  have hp : IsUnit (t.val + 1) ∨ IsUnit (1 - t.val) :=
    IsLocalRing.isUnit_or_isUnit_of_isUnit_add (by convert h2 using 1; ring)
  rcases hp with h | h
  · left
    apply h.mul_right_cancel
    linear_combination t.property
  · right
    apply h.mul_right_cancel
    linear_combination -t.property

/-- At odd local levels with nonzero parameter the determinant choices are
exactly the two translates of its annihilator ideal. -/
def determinantEquiv [IsLocalRing R] (d : R) (hd : d ≠ 0) (h2 : IsUnit (2 : R)) :
    (Bool × annihilator d) ≃ Determinants R d :=
  Equiv.ofBijective (fun p ↦ ⟨(if p.1 then 1 else -1) + p.2.val, by
    have hx := (mem_annihilator d p.2.val).mp p.2.property
    cases p.1
    · dsimp
      linear_combination (p.2.val - 2) * hx
    · dsimp
      linear_combination (p.2.val + 2) * hx⟩) (by
    constructor
    · rintro ⟨b, x⟩ ⟨c, y⟩ h
      have he := congrArg Subtype.val h
      have hx := (mem_annihilator d x.val).mp x.property
      have hy := (mem_annihilator d y.val).mp y.property
      have hneq : d ≠ -d := by
        intro h
        apply hd
        apply h2.mul_left_cancel
        linear_combination h
      cases b <;> cases c
      · refine Prod.ext rfl ?_
        apply Subtype.ext
        dsimp at he
        linear_combination he
      · exfalso
        apply hneq
        dsimp at he
        linear_combination -d * he + hx - hy
      · exfalso
        apply hneq
        dsimp at he
        linear_combination d * he - hx + hy
      · refine Prod.ext rfl ?_
        apply Subtype.ext
        dsimp at he
        linear_combination he
    · intro t
      rcases determinant_branches d h2 t with ht | ht
      · refine ⟨(true, ⟨t.val - 1, (mem_annihilator _ _).mpr ht⟩), ?_⟩
        apply Subtype.ext
        dsimp
        ring
      · refine ⟨(false, ⟨t.val + 1, (mem_annihilator _ _).mpr ht⟩), ?_⟩
        apply Subtype.ext
        dsimp
        ring)

/-- The complete odd-level determinant count, including ramified corrections. -/
theorem determinants_card [IsLocalRing R] (d : R) (hd : d ≠ 0)
    (h2 : IsUnit (2 : R)) :
    Nat.card (Determinants R d) = 2 * Nat.card (annihilator d) := by
  rw [← Nat.card_congr (determinantEquiv d hd h2), Nat.card_prod,
    Nat.card_eq_fintype_card]
  rfl

/-- The annihilator of a unit parameter is trivial. -/
theorem annihilator_card_of_unit (d : R) (hd : IsUnit d) : Nat.card (annihilator d) = 1 := by
  have he : annihilator d = ⊥ := by
    ext x
    rw [mem_annihilator, Submodule.mem_bot]
    exact ⟨fun h ↦ hd.mul_left_cancel (by simpa using h), fun h ↦ by simp [h]⟩
  rw [he]
  exact Nat.card_unique

/-- The odd self-density of the norm model retains its exact annihilator factor. -/
theorem selfDensity_odd [IsLocalRing R] (d : R) (hd : d ≠ 0) (h2 : IsUnit (2 : R)) :
    selfDensity R d = LocalNormDensity.density R d * Nat.card (annihilator d) := by
  rw [selfDensity_eq, determinants_card d hd h2, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- For a unit parameter, the full orthogonal normalization equals the norm-one density. -/
theorem selfDensity_unimodular [IsLocalRing R] (d : R) (hd : IsUnit d)
    (h2 : IsUnit (2 : R)) : selfDensity R d = LocalNormDensity.density R d := by
  rw [selfDensity_odd d hd.ne_zero h2, annihilator_card_of_unit d hd, Nat.cast_one, mul_one]

/-- At odd unimodular levels every counted matrix is genuinely invertible. -/
theorem solution_isUnit [IsLocalRing R] (d : R) (hd : IsUnit d)
    (M : Solutions R d) : IsUnit M.val := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  have h : M.val.det ^ 2 = 1 := hd.mul_left_cancel (by simpa using determinant_eq d M)
  exact ⟨⟨M.val.det, M.val.det, by simpa only [pow_two] using h,
    by simpa only [pow_two] using h⟩, rfl⟩

end NormEuclidean.BinaryCongruenceDensity
