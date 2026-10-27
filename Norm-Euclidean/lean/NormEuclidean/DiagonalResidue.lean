import NormEuclidean.FiniteFieldIsotropy
import NormEuclidean.ContentMembership

/-!
# Lifting a residue-field isotropic vector in an integral diagonal frame

The supplied frame need not be an integral basis of the lattice. A scalar
clearing its coordinate denominators suffices away from that scalar.
-/

namespace NormEuclidean

open Module
open scoped nonZeroDivisors BigOperators

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K}

/-- Coordinates of vectors in the integral span of a field basis are integral. -/
theorem basis_repr_mem_subring_of_mem_span {ι : Type*}
    (b : Basis ι K V) {v : V} (hv : v ∈ Submodule.span R (Set.range b))
    (i : ι) : b.repr v i ∈ R := by
  classical
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨j, rfl⟩ := hv
    simp only [b.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  | zero => simp
  | add x y hx hy hxi hyi =>
    simpa only [map_add, Finsupp.add_apply] using R.add_mem hxi hyi
  | smul a x hx hxi =>
    change b.repr ((a : K) • x) i ∈ R
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using R.mul_mem a.property hxi

/-- A denominator-clearing scalar takes every coordinate of an ideal multiple
of a lattice into that same fractional ideal. -/
theorem scaled_basis_coordinate_mem_of_mem_ideal_smul {ι : Type*}
    (b : Basis ι K V) (L : Submodule R V) (t : R)
    (htL : ∀ v ∈ L, (t : K) • v ∈ Submodule.span R (Set.range b))
    (I : FractionalIdeal R⁰ K) {w : V}
    (hw : w ∈ (I : Submodule R K) • L) (i : ι) :
    (t : K) * b.repr w i ∈ I := by
  refine Submodule.smul_induction_on
    (p := fun v => (t : K) * b.repr v i ∈ I) hw ?_ ?_
  · intro a ha v hv
    have hc : (t : K) * b.repr v i ∈ R := by
      simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using
        basis_repr_mem_subring_of_mem_span b (htL v hv) i
    have hm := (I : Submodule R K).smul_mem (⟨(t : K) * b.repr v i, hc⟩ : R) ha
    change ((t : K) * b.repr v i) * a ∈ I at hm
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_left_comm, mul_comm,
      mul_assoc] using hm
  · intro u v hu hv
    simpa only [map_add, Finsupp.add_apply, mul_add] using
      (show (t : K) * b.repr u i + (t : K) * b.repr v i ∈ I from
        (FractionalIdeal.mem_coe.mp ((I : Submodule R K).add_mem hu hv)))

/-- A nonzero isotropic vector of the diagonal residue form lifts to a vector
outside the prime multiple of the lattice. This adapter is independent of the
rank and of finiteness or characteristic assumptions on the residue field. -/
theorem exists_nondivisible_isotropic_mod_prime_of_residue_vector
    {ι : Type*} [Fintype ι] (Q : QuadraticForm K V) (L : Submodule R V)
    (b : Basis ι K V) (hb : ∀ i, b i ∈ L) (c : ι → R)
    (hdiag : ∀ x : ι → K, Q (b.equivFun.symm x) = ∑ i, (c i : K) * x i ^ 2)
    (t : R) (htL : ∀ v ∈ L, (t : K) • v ∈ Submodule.span R (Set.range b))
    (p : Ideal R) [p.IsPrime] (ht : t ∉ p)
    (x : ι → R ⧸ p) (hx : x ≠ 0)
    (hQx : (QuadraticMap.weightedSumSquares (R ⧸ p)
      (fun i => (Ideal.Quotient.mk p) (c i))) x = 0) :
    ∃ w ∈ L, w ∉ ((p : FractionalIdeal R⁰ K) : Submodule R K) • L ∧
      Q w ∈ (p : FractionalIdeal R⁰ K) := by
  classical
  choose r hr using fun i => Ideal.Quotient.mk_surjective (x i)
  let w := b.equivFun.symm (fun i => (r i : K))
  have hwcoord (i : ι) : b.repr w i = (r i : K) := by
    change b.equivFun w i = (r i : K)
    exact congrFun (b.equivFun.apply_symm_apply _) i
  refine ⟨w, ?_, ?_, ?_⟩
  · rw [show w = ∑ i, (r i : K) • b i from b.equivFun_symm_apply _]
    exact L.sum_mem fun i hi => L.smul_mem (r i) (hb i)
  · intro hw
    apply hx
    funext i
    have hi := scaled_basis_coordinate_mem_of_mem_ideal_smul b L t htL
      (p : FractionalIdeal R⁰ K) hw i
    rw [hwcoord] at hi
    obtain ⟨s, hs, heq⟩ := (FractionalIdeal.mem_coeIdeal R⁰).mp hi
    have hmul : t * r i ∈ p := by
      have hsr : s = t * r i := by
        apply Subtype.val_injective
        exact heq
      simpa only [hsr] using hs
    have hri : r i ∈ p := (Ideal.IsPrime.mem_or_mem inferInstance hmul).resolve_left ht
    exact (hr i).symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hri)
  · have hsum : ∑ i, c i * r i ^ 2 ∈ p := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hval : ∑ i, (Ideal.Quotient.mk p) (c i) * x i ^ 2 = 0 := by
        simpa only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, pow_two]
          using hQx
      simpa only [map_sum, map_mul, map_pow, hr] using hval
    apply (FractionalIdeal.mem_coeIdeal R⁰).mpr
    refine ⟨∑ i, c i * r i ^ 2, hsum, ?_⟩
    rw [show w = b.equivFun.symm (fun i => (r i : K)) from rfl, hdiag]
    simp only [map_sum, map_mul, map_pow]
    rfl

/-- A finite odd residue field supplies a vector in the lattice that is
isotropic modulo the prime but does not lie in the prime multiple of the
lattice. Only an integral diagonal frame and a good coordinate denominator
are required. -/
theorem exists_nondivisible_isotropic_mod_prime_of_diagonal_frame
    {ι : Type*} [Fintype ι] (Q : QuadraticForm K V) (L : Submodule R V)
    (b : Basis ι K V) (hb : ∀ i, b i ∈ L) (c : ι → R)
    (hdiag : ∀ x : ι → K, Q (b.equivFun.symm x) = ∑ i, (c i : K) * x i ^ 2)
    (t : R) (htL : ∀ v ∈ L, (t : K) • v ∈ Submodule.span R (Set.range b))
    (p : Ideal R) [p.IsMaximal] [Finite (R ⧸ p)]
    (htwo : (2 : R) ∉ p) (ht : t ∉ p) (hdim : 3 ≤ Fintype.card ι) :
    ∃ w ∈ L, w ∉ ((p : FractionalIdeal R⁰ K) : Submodule R K) • L ∧
      Q w ∈ (p : FractionalIdeal R⁰ K) := by
  classical
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  let q := Ideal.Quotient.mk p
  let Qbar : QuadraticForm (R ⧸ p) (ι → R ⧸ p) :=
    QuadraticMap.weightedSumSquares (R ⧸ p) (fun i => q (c i))
  have htwo' : (2 : R ⧸ p) ≠ 0 := by
    intro h
    apply htwo
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_ofNat] using h
  obtain ⟨x, hx, hQx⟩ := quadraticForm_exists_nonzero_isotropic_of_two_ne_zero
    (K := R ⧸ p) (V := ι → R ⧸ p) Qbar htwo'
    (by simpa only [Module.finrank_pi] using hdim)
  exact exists_nondivisible_isotropic_mod_prime_of_residue_vector
    Q L b hb c hdiag t htL p ht x hx hQx

end NormEuclidean
