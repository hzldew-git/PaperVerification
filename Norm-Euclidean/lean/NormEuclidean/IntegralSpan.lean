import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Algebra.Ring.Subring.Basic

namespace NormEuclidean

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K}

/-- Integrality of the full polar form on generators extends to their integral span.
No assumption about the invertibility of two in the subring is needed. -/
theorem polar_mem_subring_of_mem_span
    (Q : QuadraticForm K V) (S : Set V)
    (hP : ∀ x ∈ S, ∀ y ∈ S, QuadraticMap.polar Q x y ∈ R)
    {x y : V} (hx : x ∈ Submodule.span R S) (hy : y ∈ Submodule.span R S) :
    QuadraticMap.polar Q x y ∈ R := by
  have hgen (a : V) (ha : a ∈ S) : QuadraticMap.polar Q a y ∈ R := by
    induction hy using Submodule.span_induction with
    | mem b hb => exact hP a ha b hb
    | zero => simp
    | add b c hb hc ihb ihc =>
      simpa only [QuadraticMap.polar_add_right] using R.add_mem ihb ihc
    | smul r b hb ih =>
      change QuadraticMap.polar Q a ((r : K) • b) ∈ R
      simpa only [QuadraticMap.polar_smul_right, smul_eq_mul] using R.mul_mem r.property ih
  induction hx using Submodule.span_induction with
  | mem a ha => exact hgen a ha
  | zero => simp
  | add a b ha hb iha ihb =>
    simpa only [QuadraticMap.polar_add_left] using R.add_mem iha ihb
  | smul r a ha ih =>
    change QuadraticMap.polar Q ((r : K) • a) y ∈ R
    simpa only [QuadraticMap.polar_smul_left, smul_eq_mul] using R.mul_mem r.property ih

/-- Quadratic and full polar integrality on generators imply quadratic integrality
on their integral span, including at primes above two. -/
theorem quadratic_mem_subring_of_mem_span
    (Q : QuadraticForm K V) (S : Set V)
    (hQ : ∀ x ∈ S, Q x ∈ R)
    (hP : ∀ x ∈ S, ∀ y ∈ S, QuadraticMap.polar Q x y ∈ R)
    {x : V} (hx : x ∈ Submodule.span R S) : Q x ∈ R := by
  induction hx using Submodule.span_induction with
  | mem a ha => exact hQ a ha
  | zero => simp
  | add a b ha hb iha ihb =>
    rw [QuadraticMap.map_add Q a b]
    exact R.add_mem (R.add_mem iha ihb) (polar_mem_subring_of_mem_span Q S hP ha hb)
  | smul r a ha ih =>
    change Q ((r : K) • a) ∈ R
    rw [Q.map_smul, smul_eq_mul]
    exact R.mul_mem (R.mul_mem r.property r.property) ih

end NormEuclidean
