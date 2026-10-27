import NormEuclidean.ChapterX.VolumeIdeal
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# The bounded-value end of 103:3

Actual small vectors give a finite set of integral nonzero quadratic values.
The archimedean estimates allow indefinite forms and complex embeddings.
This module does not construct a small vector in every bounded-volume lattice;
that is the remaining arithmetic existence input in the anisotropic argument.
-/

noncomputable section

namespace NormEuclidean.BoundedRepresentedValues

open Module

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]

/-- Quadratic values in an arbitrary vector frame use the literal half-polar Gram matrix. -/
theorem quadratic_sum (Q : QuadraticForm K V) (n : ℕ) (b : Fin n → V) (a : Fin n → K) :
    Q (∑ i, a i • b i) = ∑ i, ∑ j, a i * a j * halfPolar Q (b i) (b j) := by
  rw [← halfPolar_self]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, mul_assoc]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [halfPolar_comm Q (b j) (b i)]

/-- A fixed field frame has one finite bound for all conjugates of its Gram entries. -/
theorem exists_gram_conjugate_bound (Q : QuadraticForm K V) (n : ℕ) (b : Fin n → V) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (φ : K →+* ℂ) (i j : Fin n),
      ‖φ (halfPolar Q (b i) (b j))‖ ≤ M := by
  let f : (K →+* ℂ) × Fin n × Fin n → ℝ :=
    fun p ↦ ‖p.1 (halfPolar Q (b p.2.1) (b p.2.2))‖
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro φ i j
  exact (hM (Set.mem_range_self (φ, i, j))).trans (le_max_left _ _)

/-- Uniform coordinate bounds give a quadratic-value bound at every complex
embedding. Positivity or total reality of the quadratic form is not assumed. -/
theorem quadratic_conjugate_bound (Q : QuadraticForm K V) (n : ℕ)
    (b : Fin n → V) (a : Fin n → K) (φ : K →+* ℂ) (M C : ℝ)
    (hC : 0 ≤ C) (hM : ∀ i j : Fin n, ‖φ (halfPolar Q (b i) (b j))‖ ≤ M)
    (ha : ∀ i : Fin n, ‖φ (a i)‖ ≤ C) :
    ‖φ (Q (∑ i, a i • b i))‖ ≤ (n : ℝ) ^ 2 * M * C ^ 2 := by
  rw [quadratic_sum]
  simp only [map_sum]
  calc
    ‖∑ i, ∑ j, φ (a i * a j * halfPolar Q (b i) (b j))‖ ≤
        ∑ i, ‖∑ j, φ (a i * a j * halfPolar Q (b i) (b j))‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖φ (a i * a j * halfPolar Q (b i) (b j))‖ :=
      Finset.sum_le_sum (fun i _ ↦ norm_sum_le _ _)
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, M * C ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hcoef : ‖φ (a i)‖ * ‖φ (a j)‖ ≤ C * C :=
        mul_le_mul (ha i) (ha j) (norm_nonneg _) hC
      have htotal := mul_le_mul hcoef (hM i j)
        (norm_nonneg (φ (halfPolar Q (b i) (b j)))) (mul_nonneg hC hC)
      calc
        ‖φ (a i * a j * halfPolar Q (b i) (b j))‖ =
            ‖φ (a i)‖ * ‖φ (a j)‖ * ‖φ (halfPolar Q (b i) (b j))‖ := by
          simp only [map_mul, norm_mul]
        _ ≤ (C * C) * M := htotal
        _ = M * C ^ 2 := by ring
    _ = (n : ℝ) ^ 2 * M * C ^ 2 := by simp; ring

/-- A single actual finite set covers all nonzero integral values obtained
from small vectors in this fixed field basis. Small-vector existence in each
bounded-volume lattice is not a premise or conclusion of this theorem. -/
theorem exists_finite_values_of_small_vectors (Q : QuadraticForm K V) (n : ℕ)
    (b : Basis (Fin n) K V) (C : ℝ) (hC : 0 ≤ C)
    (hanis : ∀ x : V, Q x = 0 → x = 0) :
    ∃ Φ : Set K, Φ.Finite ∧ 0 ∉ Φ ∧
      ∀ (L : Lattice (integerSubring K) Q) (x : V), x ∈ L.carrier → x ≠ 0 →
        (∀ (φ : K →+* ℂ) (i : Fin n), ‖φ (b.repr x i)‖ ≤ C) → Q x ∈ Φ := by
  obtain ⟨M, _, hM⟩ := exists_gram_conjugate_bound Q n b
  let D := (n : ℝ) ^ 2 * M * C ^ 2
  let Φ : Set K := {a | IsIntegral ℤ a ∧ (∀ φ : K →+* ℂ, ‖φ a‖ ≤ D) ∧ a ≠ 0}
  have hΦ : Φ.Finite := (NumberField.Embeddings.finite_of_norm_le K ℂ D).subset
    (fun _ ha ↦ ⟨ha.1, ha.2.1⟩)
  refine ⟨Φ, hΦ, (by simp [Φ]), ?_⟩
  intro L x hx hx0 hsmall
  refine ⟨(mem_integerSubring K _).mp (L.integral x hx), ?_, fun h ↦ hx0 (hanis x h)⟩
  intro φ
  have h := quadratic_conjugate_bound Q n b (fun i ↦ b.repr x i) φ M C hC
    (hM φ) (hsmall φ)
  simpa only [b.sum_repr] using h

end NormEuclidean.BoundedRepresentedValues
