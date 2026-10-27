import NormEuclidean.LatticeOperations
import NormEuclidean.IdealQuadratic

/-!
# Algebraic realization of an ideal as isotropic content

This is the algebraic part of Step 1 of Theorem 1.2 (reference manuscript). The prime and the
nonzero isotropic residue vector are explicit hypotheses. No theorem about
the existence of a prime in a prescribed ideal class is assumed or proved.
-/

namespace NormEuclidean

open scoped nonZeroDivisors

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K} [IsFractionRing R K] [IsDedekindDomain R]

namespace IdealRealization

/-- Recover membership by testing against the inverse fractional ideal. -/
theorem mem_iff_inv_mul_mem (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) (a : K) :
    a ∈ I ↔ ∀ s ∈ I⁻¹, s * a ∈ R := by
  have h := FractionalIdeal.mem_inv_iff (inv_ne_zero hI) (x := a)
  simpa only [inv_inv, Hyperbolic.mem_one_fractionalIdeal, mul_comm] using h

/-- Ideal multiplication on a hyperbolic lattice is coordinatewise. -/
theorem mem_hyperbolic_ideal_smul_iff (L : Submodule R V)
    (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) (z : Hyperbolic K V) :
    z ∈ (I : Submodule R K) • Hyperbolic.submodule L ↔
      z.1 ∈ (I : Submodule R K) • L ∧ z.2.1 ∈ I ∧ z.2.2 ∈ I := by
  rw [GeneralContent.mem_ideal_smul_iff _ I hI,
    GeneralContent.mem_ideal_smul_iff _ I hI,
    mem_iff_inv_mul_mem I hI, mem_iff_inv_mul_mem I hI]
  constructor
  · intro h
    exact ⟨fun s hs => (h s hs).1, fun s hs => (h s hs).2.1,
      fun s hs => (h s hs).2.2⟩
  · rintro ⟨hv, ha, hb⟩ s hs
    exact ⟨hv s hs, ha s hs, hb s hs⟩

/-- Maximality replaces the valuation calculation in the manuscript. -/
theorem eq_of_prime_sandwich (I C : FractionalIdeal R⁰ K) (hI : I ≠ 0)
    (hIone : I ≤ 1) (p : Ideal R) (hp : p.IsMaximal)
    (hlow : I * (p : FractionalIdeal R⁰ K) ≤ C) (hupp : C ≤ I)
    (hnot : ¬ C ≤ (p : FractionalIdeal R⁰ K)) : C = I := by
  have hD : I⁻¹ * C ≤ 1 := by
    simpa only [inv_mul_cancel₀ hI] using mul_le_mul_right hupp I⁻¹
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hD
  have hpJ : p ≤ J := by
    apply (FractionalIdeal.coeIdeal_le_coeIdeal K).mp
    rw [hJ]
    simpa only [← mul_assoc, inv_mul_cancel₀ hI, one_mul] using
      mul_le_mul_right hlow I⁻¹
  have hC : C = I * (J : FractionalIdeal R⁰ K) := by
    rw [hJ, ← mul_assoc, mul_inv_cancel₀ hI, one_mul]
  by_cases hJtop : J = ⊤
  · simpa only [hJtop, FractionalIdeal.coeIdeal_top, mul_one] using hC
  · have hp_eq : p = J := hp.eq_of_le hJtop hpJ
    apply False.elim
    apply hnot
    rw [hC, ← hp_eq]
    simpa only [one_mul] using
      mul_le_mul_left hIone (p : FractionalIdeal R⁰ K)

/-- Coprimality turns the two quadratic congruences into the required
principal-ideal divisibility. -/
theorem quadratic_mem_principal_mul {Q : QuadraticForm K V} (L : Lattice R Q)
    (i p : Ideal R) (hicop : IsCoprime i p) (a : K)
    (ha : (i : FractionalIdeal R⁰ K) * (p : FractionalIdeal R⁰ K) =
      FractionalIdeal.spanSingleton R⁰ a)
    {v : V} (hv : v ∈ (i : FractionalIdeal R⁰ K).1 • L.carrier)
    (hQp : Q v ∈ (p : FractionalIdeal R⁰ K)) :
    Q v ∈ FractionalIdeal.spanSingleton R⁰ a * (i : FractionalIdeal R⁰ K) := by
  have hQi := quadratic_mem_ideal_square Q L.carrier L.integral
    (i : FractionalIdeal R⁰ K) hv
  have hboth : Q v ∈ ((i ^ 2 ⊓ p : Ideal R) : FractionalIdeal R⁰ K) := by
    rw [FractionalIdeal.coeIdeal_inf, FractionalIdeal.coeIdeal_pow]
    exact ⟨hQi, hQp⟩
  rw [← Ideal.mul_eq_inf_of_isCoprime hicop.pow_left,
    FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow] at hboth
  convert hboth using 1
  rw [← ha, pow_two]
  ac_rfl

omit [IsDedekindDomain R] in
/-- Dividing a member of `a i` by its nonzero generator lies in `i`. -/
theorem neg_div_mem_of_mem_principal_mul (I : FractionalIdeal R⁰ K) {a q : K}
    (ha : a ≠ 0) (hq : q ∈ FractionalIdeal.spanSingleton R⁰ a * I) :
    -q / a ∈ I := by
  obtain ⟨b, hb, hqb⟩ := FractionalIdeal.mem_singleton_mul.mp hq
  have heq : -q / a = -b := by rw [hqb]; field_simp
  rw [heq]
  exact (I : Submodule R K).neg_mem hb

/-- Given an inverse-class prime and a nonzero isotropic residue lift,
`(v,a,-Q(v)/a)` is a nonzero integral isotropic vector with content exactly `i`.
The good-prime and residue-lift data remain explicit hypotheses. -/
theorem good_prime_isotropic_content {Q : QuadraticForm K V} (L : Lattice R Q)
    (i p : Ideal R) (hi : i ≠ ⊥) (hp : p.IsMaximal) (hp0 : p ≠ ⊥)
    (hicop : IsCoprime i p) (a : K) (ha0 : a ≠ 0)
    (hgen : (i : FractionalIdeal R⁰ K) * (p : FractionalIdeal R⁰ K) =
      FractionalIdeal.spanSingleton R⁰ a)
    (v : V) (hv : v ∈ (i : FractionalIdeal R⁰ K).1 • L.carrier)
    (hvp : v ∉ (p : FractionalIdeal R⁰ K).1 • L.carrier)
    (hQp : Q v ∈ (p : FractionalIdeal R⁰ K)) :
    let z : Hyperbolic K V := (v, a, -Q v / a);
    -Q v / a ∈ (i : FractionalIdeal R⁰ K) ∧
      Hyperbolic.Mem L.carrier z ∧ z ≠ 0 ∧ Hyperbolic.q Q z = 0 ∧
      L.hyperbolic.content z = (i : FractionalIdeal R⁰ K) := by
  let I : FractionalIdeal R⁰ K := i
  let P : FractionalIdeal R⁰ K := p
  let z : Hyperbolic K V := (v, a, -Q v / a)
  have hI : I ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hi
  have hP : P ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hp0
  have hIone : I ≤ 1 := FractionalIdeal.coeIdeal_le_one
  have hIP : I * P ≤ I := by
    simpa only [mul_one] using mul_le_mul_right
      (show P ≤ 1 from FractionalIdeal.coeIdeal_le_one) I
  have haI : a ∈ I := hIP (hgen.symm ▸ FractionalIdeal.mem_spanSingleton_self R⁰ a)
  have hbI : -Q v / a ∈ I := neg_div_mem_of_mem_principal_mul I ha0
    (quadratic_mem_principal_mul L i p hicop a hgen hv hQp)
  have hzI : z ∈ (I : Submodule R K) • L.hyperbolic.carrier :=
    (mem_hyperbolic_ideal_smul_iff L.carrier I hI z).mpr ⟨hv, haI, hbI⟩
  have hzmem : Hyperbolic.Mem L.carrier z := by
    have hz1 := (Submodule.smul_mono
      (show (I : Submodule R K) ≤ (1 : FractionalIdeal R⁰ K).1 from hIone)
      (le_refl L.hyperbolic.carrier)) hzI
    change z ∈ ((1 : FractionalIdeal R⁰ K) : Submodule R K) •
      L.hyperbolic.carrier at hz1
    rw [FractionalIdeal.coe_one, Submodule.one_smul] at hz1
    exact hz1
  have hz0 : z ≠ 0 := by
    intro hz
    have ha := congrArg (fun w : Hyperbolic K V => w.2.1) hz
    exact ha0 ha
  have hziso : Hyperbolic.q Q z = 0 := by
    change Q v + a * (-Q v / a) = 0
    field_simp
    ring
  have hC : L.hyperbolic.content z ≠ 0 := by
    intro h
    exact hz0 ((L.hyperbolic.content_eq_zero_iff z).mp h)
  have hupper : L.hyperbolic.content z ≤ I :=
    (L.hyperbolic.mem_ideal_smul_iff_content_le I hI z).mp hzI
  have hzC : z ∈ (L.hyperbolic.content z : Submodule R K) • L.hyperbolic.carrier :=
    (L.hyperbolic.mem_ideal_smul_iff_content_le _ hC z).mpr le_rfl
  have halower : a ∈ L.hyperbolic.content z :=
    ((mem_hyperbolic_ideal_smul_iff L.carrier _ hC z).mp hzC).2.1
  have hlower : I * P ≤ L.hyperbolic.content z := by
    rw [hgen]
    exact FractionalIdeal.spanSingleton_le_iff_mem.mpr halower
  have hnot : ¬ L.hyperbolic.content z ≤ P := by
    intro h
    have hzP := (L.hyperbolic.mem_ideal_smul_iff_content_le P hP z).mpr h
    exact hvp ((mem_hyperbolic_ideal_smul_iff L.carrier P hP z).mp hzP).1
  exact ⟨hbI, hzmem, hz0, hziso,
    eq_of_prime_sandwich I _ hI hIone p hp hlower hupper hnot⟩

omit [IsFractionRing R K] [IsDedekindDomain R] in
/-- Coprimality lifts a nonzero isotropic residue vector to the ideal multiple.
This is the multiplication-by-`c ≡ 1 mod p` step of the manuscript. -/
theorem exists_isotropic_residue_lift {Q : QuadraticForm K V} (L : Lattice R Q)
    (i p : Ideal R) (hicop : IsCoprime i p) (w : V) (hw : w ∈ L.carrier)
    (hwp : w ∉ (p : FractionalIdeal R⁰ K).1 • L.carrier)
    (hQw : Q w ∈ (p : FractionalIdeal R⁰ K)) :
    ∃ v : V, v ∈ (i : FractionalIdeal R⁰ K).1 • L.carrier ∧
      v ∉ (p : FractionalIdeal R⁰ K).1 • L.carrier ∧
      Q v ∈ (p : FractionalIdeal R⁰ K) := by
  obtain ⟨c, hc, d, hd, hcd⟩ := hicop.exists
  have hcI : (c : K) ∈ (i : FractionalIdeal R⁰ K) :=
    FractionalIdeal.mem_coeIdeal_of_mem R⁰ hc
  have hdP : (d : K) ∈ (p : FractionalIdeal R⁰ K) :=
    FractionalIdeal.mem_coeIdeal_of_mem R⁰ hd
  refine ⟨(c : K) • w, Submodule.smul_mem_smul hcI hw, ?_, ?_⟩
  · intro hvp
    apply hwp
    have hdw := Submodule.smul_mem_smul hdP hw
    have hadd := ((p : FractionalIdeal R⁰ K).1 • L.carrier).add_mem hvp hdw
    have hcdK : (c : K) + (d : K) = 1 := congrArg Subtype.val hcd
    simpa only [← add_smul, hcdK, one_smul] using hadd
  · have h := ((p : FractionalIdeal R⁰ K) : Submodule R K).smul_mem (c * c) hQw
    simpa only [Q.map_smul, smul_eq_mul, Subring.smul_def, Subring.coe_mul,
      mul_assoc, FractionalIdeal.mem_coe] using h

end IdealRealization

/-- The algebraic Step 1 construction followed by Lemma 2.4 makes the
specified ideal principal. Good-prime data are still hypotheses; this does
not assert their global class-field-theoretic existence. -/
theorem numberField_ideal_principal_of_good_prime [NumberField K]
    {Q : QuadraticForm K V} (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (i p : Ideal (integerSubring K)) (hi : i ≠ ⊥)
    (hp : p.IsMaximal) (hp0 : p ≠ ⊥) (hicop : IsCoprime i p)
    (a : K) (ha0 : a ≠ 0)
    (hgen : (i : FractionalIdeal (integerSubring K)⁰ K) *
      (p : FractionalIdeal (integerSubring K)⁰ K) =
      FractionalIdeal.spanSingleton (integerSubring K)⁰ a)
    (w : V) (hw : w ∈ L.carrier)
    (hwp : w ∉ (p : FractionalIdeal (integerSubring K)⁰ K).1 • L.carrier)
    (hQw : Q w ∈ (p : FractionalIdeal (integerSubring K)⁰ K)) :
    ∃ c : integerSubring K, c ≠ 0 ∧ i = Ideal.span {c} := by
  obtain ⟨v, hv, hvp, hQv⟩ :=
    IdealRealization.exists_isotropic_residue_lift L i p hicop w hw hwp hQw
  obtain ⟨_, hz, hz0, hiso, hcontent⟩ :=
    IdealRealization.good_prime_isotropic_content L i p hi hp hp0 hicop a ha0 hgen
      v hv hvp hQv
  obtain ⟨_, c, hc, hc0, _, hprincipal⟩ :=
    numberField_norm_descent_total_content Q L hA hE hz hz0 hiso
  refine ⟨⟨c, hc⟩, ?_, ?_⟩
  · intro h
    exact hc0 (congrArg Subtype.val h)
  · apply FractionalIdeal.coeIdeal_injective (K := K)
    dsimp only
    rw [FractionalIdeal.coeIdeal_span_singleton]
    exact hcontent.symm.trans hprincipal

end NormEuclidean
