import NormEuclidean.GeneralContent

/-!
# Quadratic integrality on ideal multiples

These are the algebraic ideal-containment calculations used in Step 1 of
Theorem 1.2 (reference manuscript). They do not assume a lattice basis or classic integrality.
The polar form is twice the manuscript's associated bilinear form.
-/

namespace NormEuclidean

open QuadraticMap
open scoped nonZeroDivisors

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K}
variable (Q : QuadraticForm K V) (L : Submodule R V)

/-- Polar values on two ideal multiples lie in the product ideal. -/
theorem polar_mem_ideal_mul (hQ : ∀ v ∈ L, Q v ∈ R)
    (I J : FractionalIdeal R⁰ K) {x y : V}
    (hx : x ∈ (I : Submodule R K) • L)
    (hy : y ∈ (J : Submodule R K) • L) : polar Q x y ∈ I * J := by
  have h : ∀ y ∈ (J : Submodule R K) • L, polar Q x y ∈ I * J := by
    refine Submodule.smul_induction_on
      (p := fun x => ∀ y ∈ (J : Submodule R K) • L, polar Q x y ∈ I * J) hx ?_ ?_
    · intro r hr v hv y hy
      refine Submodule.smul_induction_on
        (p := fun y => polar Q (r • v) y ∈ I * J) hy ?_ ?_
      · intro s hs w hw
        have hp := Hyperbolic.polar_mem L hQ hv hw
        have hrs : r * s ∈ I * J := FractionalIdeal.mul_mem_mul hr hs
        have hm := ((I * J : FractionalIdeal R⁰ K) : Submodule R K).smul_mem
          (⟨polar Q v w, hp⟩ : R) hrs
        change polar Q (r • v) (s • w) ∈
          ((I * J : FractionalIdeal R⁰ K) : Submodule R K)
        convert hm using 1
        simp only [Q.polar_smul_left, Q.polar_smul_right, smul_eq_mul, Subring.smul_def]
        ring
      · intro u w hu hw
        rw [Q.polar_add_right]
        exact ((I * J : FractionalIdeal R⁰ K) : Submodule R K).add_mem hu hw
    · intro u v hu hv y hy
      rw [Q.polar_add_left]
      exact ((I * J : FractionalIdeal R⁰ K) : Submodule R K).add_mem (hu y hy) (hv y hy)
  exact h y hy

/-- Integrality of `Q` on `L` implies `Q(I L) ⊆ I²`, also for nonfree lattices. -/
theorem quadratic_mem_ideal_square (hQ : ∀ v ∈ L, Q v ∈ R)
    (I : FractionalIdeal R⁰ K) {x : V} (hx : x ∈ (I : Submodule R K) • L) :
    Q x ∈ I ^ 2 := by
  have h : Q x ∈ I * I ∧ x ∈ (I : Submodule R K) • L := by
    refine Submodule.smul_induction_on
      (p := fun x => Q x ∈ I * I ∧ x ∈ (I : Submodule R K) • L) hx ?_ ?_
    · intro r hr v hv
      refine ⟨?_, Submodule.smul_mem_smul hr hv⟩
      have hrr : r * r ∈ I * I := FractionalIdeal.mul_mem_mul hr hr
      have hm := ((I * I : FractionalIdeal R⁰ K) : Submodule R K).smul_mem
        (⟨Q v, hQ v hv⟩ : R) hrr
      change Q (r • v) ∈ ((I * I : FractionalIdeal R⁰ K) : Submodule R K)
      convert hm using 1
      simp only [Q.map_smul, smul_eq_mul, Subring.smul_def]
      ring
    · intro u v hu hv
      refine ⟨?_, ((I : Submodule R K) • L).add_mem hu.2 hv.2⟩
      rw [QuadraticMap.map_add (Q : V → K) u v]
      exact ((I * I : FractionalIdeal R⁰ K) : Submodule R K).add_mem (((I * I : FractionalIdeal R⁰ K) : Submodule R K).add_mem hu.1 hv.1)
        (polar_mem_ideal_mul Q L hQ I I hu.2 hv.2)
  simpa only [pow_two] using h.1

end NormEuclidean
