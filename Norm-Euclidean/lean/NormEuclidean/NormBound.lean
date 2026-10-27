import NormEuclidean.NormIdeal
import NormEuclidean.NondivisibleVector

/-!
# The rank-independent bound on the norm ideal

The half-vector argument uses freeness only as a finitely generated
abelian group, never freeness over the ring of integers.

This proves the first and final assertions of manuscript reference manuscript Lemma 4.1. The
stronger rank-at-least-three assertion that the norm ideal is the unit ideal
is not proved here; it depends on the later class-number and ADC arguments.
-/

namespace NormEuclidean

open scoped NumberField

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

/-- Homogeneity of the actual field norm for the rational scalar four. -/
theorem fieldAbsNorm_four_mul (a : K) :
    fieldAbsNorm K ((4 : K) * a) = (4 : ℚ) ^ Module.finrank ℚ K * fieldAbsNorm K a := by
  rw [fieldAbsNorm_mul]
  congr 1
  have hn : Algebra.norm ℚ (4 : K) = (4 : ℚ) ^ Module.finrank ℚ K := by
    simpa using (Algebra.norm_algebraMap (R := ℚ) (S := K) (4 : ℚ))
  simp only [fieldAbsNorm, hn, abs_pow, abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 4)]

/-- A vector not divisible by two in the lattice gives a nonzero short value. -/
theorem exists_small_norm_value_of_not_two_divisible
    (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    {w₀ : V} (hw₀ : w₀ ∈ L.carrier)
    (hdiv : ∀ y ∈ L.carrier, w₀ ≠ (2 : K) • y) :
    ∃ w : L.carrier, Q w ≠ 0 ∧
      fieldAbsNorm K (Q w) < (4 : ℚ) ^ Module.finrank ℚ K := by
  let x : V := (2 : K)⁻¹ • w₀
  obtain ⟨y, hy, hxy⟩ := hE x
  let w : V := w₀ - (2 : K) • y
  have hw : w ∈ L.carrier := L.carrier.sub_mem hw₀
    (by
      change (((2 : integerSubring K) : K) • y) ∈ L.carrier
      exact L.carrier.smul_mem (2 : integerSubring K) hy)
  have hwne : w ≠ 0 := fun heq => hdiv y hy (sub_eq_zero.mp heq)
  have hQw : Q w ≠ 0 := fun heq => hwne (hA w heq)
  have htwo : (2 : K) ≠ 0 := by norm_num
  have hscale : w = (2 : K) • (x - y) := by
    dsimp [w, x]
    rw [smul_sub, smul_smul, mul_inv_cancel₀ htwo, one_smul]
  have hQ : Q w = (4 : K) * Q (x - y) := by
    rw [hscale, Q.map_smul]
    norm_num [smul_eq_mul]
  refine ⟨⟨w, hw⟩, hQw, ?_⟩
  change fieldAbsNorm K (Q w) < _
  rw [hQ, fieldAbsNorm_four_mul]
  change fieldAbsNorm K (Q (x - y)) < 1 at hxy
  have hp : (0 : ℚ) < (4 : ℚ) ^ Module.finrank ℚ K := by positivity
  simpa only [mul_one] using mul_lt_mul_of_pos_left hxy hp

/-- Lemma 4.1 (reference manuscript), the bound valid for every positive rank, including nonfree lattices. -/
theorem normIdeal_absNorm_lt [Nontrivial V]
    (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier) :
    Ideal.absNorm L.normIdeal < 4 ^ Module.finrank ℚ K := by
  obtain ⟨w₀, hw₀, hdiv⟩ := L.exists_not_two_smul
  obtain ⟨w, hw, hbound⟩ :=
    exists_small_norm_value_of_not_two_divisible Q L hA hE hw₀ hdiv
  have hle := L.normIdeal_absNorm_le w hw
  exact_mod_cast hle.trans_lt hbound

/-- The norm ideal of a positive-rank anisotropic integral lattice is nonzero. -/
theorem normIdeal_ne_bot [Nontrivial V]
    (L : Lattice (integerSubring K) Q) (hA : Q.Anisotropic) :
    L.normIdeal ≠ ⊥ := by
  obtain ⟨w₀, hw₀, hdiv⟩ := L.exists_not_two_smul
  have hw₀ne : w₀ ≠ 0 := by
    simpa only [smul_zero] using hdiv 0 L.carrier.zero_mem
  intro hbot
  have hmem := L.normValue_mem_normIdeal ⟨w₀, hw₀⟩
  rw [hbot, Ideal.mem_bot] at hmem
  have hQ : Q w₀ = 0 := congrArg ((↑) : 𝓞 K → K) hmem
  exact hw₀ne (hA w₀ hQ)

/-- A fixed number field admits only finitely many integral ideals satisfying
this norm bound. In particular this bounds the possible norm ideals uniformly
in the ambient dimension and quadratic form. -/
theorem finite_bounded_normIdeals (K : Type*) [Field K] [NumberField K] :
    {I : Ideal (𝓞 K) | Ideal.absNorm I < 4 ^ Module.finrank ℚ K}.Finite :=
  (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) (4 ^ Module.finrank ℚ K)).subset
    fun _ h => Nat.le_of_lt h

/-- For a fixed number field, the possible norm ideals of positive-rank
norm-Euclidean lattices (over the given ambient space) form a finite set. -/
theorem finite_normIdeals [Nontrivial V] :
    {I : Ideal (𝓞 K) | ∃ Q : QuadraticForm K V,
      ∃ L : Lattice (integerSubring K) Q,
      Q.Anisotropic ∧ HasNumberFieldApproximation Q L.carrier ∧ L.normIdeal = I}.Finite := by
  apply (finite_bounded_normIdeals K).subset
  rintro I ⟨Q, L, hA, hE, rfl⟩
  exact normIdeal_absNorm_lt Q L hA hE

/-- The same finiteness conclusion for an arbitrary family, allowing its
ambient spaces and ranks to vary. -/
theorem finite_normIdeals_family {ι : Type*} (W : ι → Type*)
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] [∀ i, Nontrivial (W i)]
    (q : ∀ i, QuadraticForm K (W i)) (L : ∀ i, Lattice (integerSubring K) (q i))
    (hA : ∀ i, (q i).Anisotropic)
    (hE : ∀ i, HasNumberFieldApproximation (q i) (L i).carrier) :
    (Set.range fun i => (L i).normIdeal).Finite := by
  apply (finite_bounded_normIdeals K).subset
  rintro I ⟨i, rfl⟩
  exact normIdeal_absNorm_lt (q i) (L i) (hA i) (hE i)

end NormEuclidean
