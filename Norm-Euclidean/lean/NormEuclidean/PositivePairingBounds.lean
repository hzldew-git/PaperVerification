import NormEuclidean.ScaleIdeal
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# Archimedean bounds for integral polar pairings

Nonnegative values at every real embedding imply the exact polar
Cauchy--Schwarz inequality. No archimedean inequality is assumed as a
classification interface. Over a totally real field, finite possible
diagonal values then give finitely many possible integral polar entries.
-/

noncomputable section

namespace NormEuclidean.PositivePairingBounds

open scoped NumberField

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]

/-- Nonnegativity of every global vector at every real embedding.
Positive definiteness at real completions implies this property. -/
def TotallyNonnegative (Q : QuadraticForm K V) : Prop :=
  ∀ (σ : K →+* ℝ) (x : V), 0 ≤ σ (Q x)

/-- Strict positive values of nonzero global vectors at every real embedding. -/
def TotallyPositive (Q : QuadraticForm K V) : Prop :=
  ∀ (σ : K →+* ℝ) (x : V), x ≠ 0 → 0 < σ (Q x)

/-- Strict real positivity includes nonnegativity at the zero vector. -/
theorem TotallyPositive.nonnegative {Q : QuadraticForm K V} (h : TotallyPositive Q) :
    TotallyNonnegative Q := by
  intro σ x
  by_cases hx : x = 0
  · simp [hx]
  · exact (h σ x hx).le

/-- Over a totally real number field strict positivity is not vacuous and implies anisotropy. -/
theorem TotallyPositive.anisotropic [NumberField.IsTotallyReal K]
    {Q : QuadraticForm K V} (h : TotallyPositive Q) : Q.Anisotropic := by
  classical
  let φ : K →+* ℂ := Classical.choice inferInstance
  let σ := (NumberField.IsTotallyReal.complexEmbedding_isReal φ).embedding
  intro x hx
  by_contra hx0
  have hp := h σ x hx0
  simpa [hx] using hp

omit [NumberField K] in
/-- An identity with no denominator, using the actual polar form. -/
theorem polar_discriminant_identity (Q : QuadraticForm K V) (x y : V) :
    Q ((2 * Q y) • x - Q.polarBilin x y • y) =
      Q y * (4 * Q x * Q y - Q.polarBilin x y ^ 2) := by
  rw [sub_eq_add_neg, QuadraticMap.map_add (Q : V → K), Q.map_smul, Q.map_neg,
    Q.map_smul, Q.polar_smul_left, Q.polar_neg_right, Q.polar_smul_right]
  change _ + _ + _ * -(_ * Q.polarBilin x y) = _
  simp only [smul_eq_mul]
  ring

/-- The polar Cauchy--Schwarz inequality follows from nonnegative quadratic values. -/
theorem polar_sq_le (Q : QuadraticForm K V) (hA : Q.Anisotropic)
    (hpos : TotallyNonnegative Q) (σ : K →+* ℝ) (x y : V) :
    σ (Q.polarBilin x y) ^ 2 ≤ 4 * σ (Q x) * σ (Q y) := by
  by_cases hy : y = 0
  · simp [hy]
  have hQy : Q y ≠ 0 := fun h ↦ hy (hA y h)
  have hσy : 0 < σ (Q y) := lt_of_le_of_ne (hpos σ y)
    (Ne.symm (fun h ↦ hQy (σ.injective (h.trans σ.map_zero.symm))))
  have hz := hpos σ ((2 * Q y) • x - Q.polarBilin x y • y)
  rw [polar_discriminant_identity] at hz
  simp only [map_mul, map_sub, map_pow, map_ofNat] at hz
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hz hσy)

/-- The sum of the two diagonal values bounds the absolute polar entry. -/
theorem abs_polar_le (Q : QuadraticForm K V) (hA : Q.Anisotropic)
    (hpos : TotallyNonnegative Q) (σ : K →+* ℝ) (x y : V) :
    |σ (Q.polarBilin x y)| ≤ σ (Q x) + σ (Q y) := by
  have h := polar_sq_le Q hA hpos σ x y
  have hx := hpos σ x
  have hy := hpos σ y
  have hd := sq_nonneg (σ (Q x) - σ (Q y))
  apply abs_le.mpr
  constructor <;> nlinarith

/-- A finite set of diagonal values gives one bound at all complex embeddings. -/
theorem finite_values_bound (Φ : Set K) (hΦ : Φ.Finite) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Φ, ∀ φ : K →+* ℂ, ‖φ a‖ ≤ C := by
  classical
  letI : Finite Φ := hΦ
  let f : Φ × (K →+* ℂ) → ℝ := fun p ↦ ‖p.2 p.1.val‖
  obtain ⟨C, hC⟩ := (Set.finite_range f).bddAbove
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro a ha φ
  exact (hC (Set.mem_range_self (⟨a, ha⟩, φ))).trans (le_max_left _ _)

/-- The possible integral polar entries are finite, uniformly over all such forms and lattices.
No mass formula or finiteness-of-lattice-classes assumption is used. -/
theorem exists_finite_polar_values [NumberField.IsTotallyReal K]
    (Φ : Set K) (hΦ : Φ.Finite) :
    ∃ Ψ : Set K, Ψ.Finite ∧
      ∀ (W : Type*) [AddCommGroup W] [Module K W] (Q : QuadraticForm K W)
        (L : Lattice (integerSubring K) Q), Q.Anisotropic → TotallyNonnegative Q →
        ∀ x ∈ L.carrier, ∀ y ∈ L.carrier, Q x ∈ Φ → Q y ∈ Φ → Q.polarBilin x y ∈ Ψ := by
  obtain ⟨C, hC, hbound⟩ := finite_values_bound Φ hΦ
  let Ψ : Set K := {a | IsIntegral ℤ a ∧ ∀ φ : K →+* ℂ, ‖φ a‖ ≤ 2 * C}
  refine ⟨Ψ, NumberField.Embeddings.finite_of_norm_le K ℂ (2 * C), ?_⟩
  intro W _ _ Q L hA hpos x hx y hy hxΦ hyΦ
  refine ⟨(mem_integerSubring K _).mp (Hyperbolic.polar_mem L.carrier L.integral hx hy), ?_⟩
  intro φ
  let hreal := NumberField.IsTotallyReal.complexEmbedding_isReal φ
  let σ := hreal.embedding
  have hφ (a : K) : (σ a : ℂ) = φ a :=
    NumberField.ComplexEmbedding.IsReal.coe_embedding_apply hreal a
  have hnorm (a : K) : ‖φ a‖ = |σ a| := by
    rw [← hφ, Complex.norm_real, Real.norm_eq_abs]
  have hxC : σ (Q x) ≤ C := (le_abs_self _).trans
    ((hnorm _ ▸ hbound (Q x) hxΦ φ))
  have hyC : σ (Q y) ≤ C := (le_abs_self _).trans
    ((hnorm _ ▸ hbound (Q y) hyΦ φ))
  rw [hnorm]
  exact (abs_polar_le Q hA hpos σ x y).trans (by linarith)

end NormEuclidean.PositivePairingBounds
