import NormEuclidean.GeneralContent
import Mathlib.Algebra.Algebra.Operations
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Membership in an ideal multiple of a lattice

The key identity is proved for arbitrary modules over a Dedekind domain,
without using a pseudobasis: membership in `I L` is equivalent to all
scalars in `I⁻¹` sending the vector into `L`.
-/

namespace NormEuclidean.GeneralContent

open scoped nonZeroDivisors

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K} [IsFractionRing R K] [IsDedekindDomain R]

/-- Intrinsic ideal-multiple membership, requiring no freeness or finite generation. -/
theorem mem_ideal_smul_iff (L : Submodule R V) (I : FractionalIdeal R⁰ K)
    (hI : I ≠ 0) (x : V) :
    x ∈ (I : Submodule R K) • L ↔ ∀ a ∈ I⁻¹, a • x ∈ L := by
  constructor
  · intro hx a ha
    refine Submodule.smul_induction_on (p := fun v => a • v ∈ L) hx ?_ ?_
    · intro r hr v hv
      have har : a * r ∈ (1 : FractionalIdeal R⁰ K) := by
        simpa only [inv_mul_cancel₀ hI] using (FractionalIdeal.mul_mem_mul ha hr)
      have harR : a * r ∈ R := (Hyperbolic.mem_one_fractionalIdeal _).mp har
      have hmem := L.smul_mem (⟨a * r, harR⟩ : R) hv
      change (a * r) • v ∈ L at hmem
      simpa only [smul_smul] using hmem
    · intro u v hu hv
      simpa only [smul_add] using L.add_mem hu hv
  · intro hx
    have h1 : (1 : K) ∈ (I : Submodule R K) • ((I⁻¹ : FractionalIdeal R⁰ K) : Submodule R K) := by
      change (1 : K) ∈ (I : Submodule R K) *
        ((I⁻¹ : FractionalIdeal R⁰ K) : Submodule R K)
      rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hI]
      exact (Hyperbolic.mem_one_fractionalIdeal _).mpr R.one_mem
    have h : (1 : K) • x ∈ (I : Submodule R K) • L := by
      refine Submodule.smul_induction_on
        (p := fun r : K => r • x ∈ (I : Submodule R K) • L) h1 ?_ ?_
      · intro a ha b hb
        simpa only [smul_eq_mul, mul_smul] using
          (Submodule.smul_mem_smul ha (hx b hb))
      · intro a b ha hb
        simpa only [add_smul] using (((I : Submodule R K) • L).add_mem ha hb)
    simpa only [one_smul] using h

/-- Proposition 2.1(ii), including the zero vector, for an arbitrary
finite full lattice over a Dedekind subring. -/
theorem mem_ideal_smul_iff_content_le (L : Submodule R V) (hL : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤)
    (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) (x : V) :
    x ∈ (I : Submodule R K) • L ↔ contentIdeal L hL x ≤ I := by
  by_cases hx : x = 0
  · subst x
    simp
  rw [contentIdeal_of_ne_zero L hL x hx,
    FractionalIdeal.inv_le_comm (coefficientIdeal_ne_zero L hL hfull x hx) hI,
    mem_ideal_smul_iff L I hI x]
  constructor
  · intro h a ha
    exact h a ha
  · intro h a ha
    exact h ha

end NormEuclidean.GeneralContent
