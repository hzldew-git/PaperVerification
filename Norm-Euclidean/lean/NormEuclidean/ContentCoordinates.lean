import NormEuclidean.ContentMembership

/-!
# Content in a supplied pseudobasis

For a lattice whose membership is described by nonzero fractional coordinate
ideals in a vector-space basis, its intrinsic content is the sum of the
coordinate principal ideals multiplied by the inverse coordinate ideals.
The result does not assume that the lattice is free or that the coefficient
ring is principal, and does not claim existence of a pseudobasis.
-/

namespace NormEuclidean.GeneralContent

open scoped nonZeroDivisors
open scoped BigOperators

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K} [IsFractionRing R K] [IsDedekindDomain R]

private theorem fractionalIdeal_sum_le_iff {ι : Type*} (s : Finset ι)
    (f : ι → FractionalIdeal R⁰ K) (J : FractionalIdeal R⁰ K) :
    (∑ i ∈ s, f i) ≤ J ↔ ∀ i ∈ s, f i ≤ J := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, ← FractionalIdeal.sup_eq_add, sup_le_iff, ih,
      Finset.mem_insert, forall_eq_or_imp]

/-- Multiplying a lattice with a supplied pseudobasis multiplies each of its
coordinate ideals by the same nonzero fractional ideal. -/
theorem mem_ideal_smul_iff_coordinates {ι : Type*} (b : Module.Basis ι K V)
    (A : ι → FractionalIdeal R⁰ K) (L : Submodule R V)
    (hcoord : ∀ v, v ∈ L ↔ ∀ i, b.repr v i ∈ A i)
    (J : FractionalIdeal R⁰ K) (hJ : J ≠ 0) (x : V) :
    x ∈ (J : Submodule R K) • L ↔ ∀ i, b.repr x i ∈ J * A i := by
  rw [mem_ideal_smul_iff L J hJ x]
  constructor
  · intro hx i
    change b.repr x i ∈ ((J * A i : FractionalIdeal R⁰ K) : Submodule R K)
    rw [FractionalIdeal.coe_mul]
    change b.repr x i ∈ (J : Submodule R K) • (A i : Submodule R K)
    rw [mem_ideal_smul_iff (A i : Submodule R K) J hJ]
    intro a ha
    have h := (hcoord (a • x)).mp (hx a ha) i
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul,
      FractionalIdeal.mem_coe] using h
  · intro hx a ha
    apply (hcoord (a • x)).mpr
    intro i
    have hxi : b.repr x i ∈ (J : Submodule R K) • (A i : Submodule R K) := by
      change b.repr x i ∈ (J : Submodule R K) * (A i : Submodule R K)
      rw [← FractionalIdeal.coe_mul]
      exact hx i
    have h := (mem_ideal_smul_iff (A i : Submodule R K) J hJ (b.repr x i)).mp hxi a ha
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul,
      FractionalIdeal.mem_coe] using h

private theorem coordinate_sum_le_iff {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K V) (A : ι → FractionalIdeal R⁰ K) (hA : ∀ i, A i ≠ 0)
    (x : V) (J : FractionalIdeal R⁰ K) :
    (∑ i, FractionalIdeal.spanSingleton R⁰ (b.repr x i) * (A i)⁻¹) ≤ J ↔
      ∀ i, b.repr x i ∈ J * A i := by
  classical
  rw [fractionalIdeal_sum_le_iff]
  simp only [Finset.mem_univ, forall_true_left]
  apply forall_congr'
  intro i
  constructor
  · intro h
    rw [← FractionalIdeal.spanSingleton_le_iff_mem]
    have hmul := mul_le_mul_right h (A i)
    have hleft : A i *
        (FractionalIdeal.spanSingleton R⁰ (b.repr x i) * (A i)⁻¹) =
        FractionalIdeal.spanSingleton R⁰ (b.repr x i) := by
      calc
        A i * (FractionalIdeal.spanSingleton R⁰ (b.repr x i) * (A i)⁻¹) =
            FractionalIdeal.spanSingleton R⁰ (b.repr x i) * (A i * (A i)⁻¹) := by
              ac_rfl
        _ = FractionalIdeal.spanSingleton R⁰ (b.repr x i) := by
          rw [mul_inv_cancel₀ (hA i), mul_one]
    rw [hleft, mul_comm (A i) J] at hmul
    exact hmul
  · intro hx
    have hle : FractionalIdeal.spanSingleton R⁰ (b.repr x i) ≤ J * A i :=
      FractionalIdeal.spanSingleton_le_iff_mem.mpr hx
    have hmul := mul_le_mul_right hle (A i)⁻¹
    simpa [mul_comm, mul_left_comm, mul_assoc, mul_inv_cancel₀ (hA i)] using hmul

/-- Proposition 2.1(i), conditional on an actual coordinate description of the
lattice by a supplied pseudobasis. This formula includes the zero vector. -/
theorem contentIdeal_eq_sum_coordinates {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K V) (A : ι → FractionalIdeal R⁰ K) (hA : ∀ i, A i ≠ 0)
    (L : Submodule R V) (hL : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤)
    (hcoord : ∀ v, v ∈ L ↔ ∀ i, b.repr v i ∈ A i) (x : V) :
    contentIdeal L hL x =
      ∑ i, FractionalIdeal.spanSingleton R⁰ (b.repr x i) * (A i)⁻¹ := by
  classical
  by_cases hx : x = 0
  · subst x
    simp
  let S := ∑ i, FractionalIdeal.spanSingleton R⁰ (b.repr x i) * (A i)⁻¹
  have hS : S ≠ 0 := by
    intro hzero
    have hcoords := (coordinate_sum_le_iff b A hA x 0).mp (le_of_eq hzero)
    apply hx
    apply b.repr.injective
    ext i
    have h := hcoords i
    simpa using h
  have hbound (J : FractionalIdeal R⁰ K) (hJ : J ≠ 0) :
      contentIdeal L hL x ≤ J ↔ S ≤ J := by
    rw [← mem_ideal_smul_iff_content_le L hL hfull J hJ x,
      mem_ideal_smul_iff_coordinates b A L hcoord J hJ x]
    exact (coordinate_sum_le_iff b A hA x J).symm
  apply le_antisymm
  · exact (hbound S hS).mpr le_rfl
  · exact (hbound _ (contentIdeal_ne_zero L hL hfull x hx)).mp le_rfl

end NormEuclidean.GeneralContent
