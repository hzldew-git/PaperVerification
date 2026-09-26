import TraceEuclidean.V15HunterGeneralCoefficientBridge
import Mathlib.NumberTheory.MahlerMeasure
import Mathlib.Topology.Algebra.Polynomial

/-!
# Finite coefficient boxes for the general Hunter polynomial

This module turns the first-two-coefficient Hunter spread bound into a
uniform bound for every root and every coefficient.  Consequently the set of
integral Hunter candidate polynomials of fixed degree and fixed spread bound
is finite.
-/

namespace TraceEuclidean

noncomputable section

open Algebra NumberField Polynomial

/-- A uniform root bound obtained from the normalized Hunter spread. -/
noncomputable def v15HunterRootBound (d : ℕ) (B : ℝ) : ℝ :=
  Real.sqrt (max B 0 + (d : ℝ) ^ 2)

/-- The uniform coefficient bound obtained by combining the root bound with
Vieta's formulas. -/
noncomputable def v15HunterCoefficientBound (d : ℕ) (B : ℝ) : ℝ :=
  max (v15HunterRootBound d B) 1 ^ d * d.choose (d / 2)

open scoped Classical in
/-- The sum of the squares of the real roots is the second Newton power sum
written in terms of the first two signed coefficients. -/
theorem v15_hunter_roots_sum_sq_eq_coefficients
    (d : ℕ) (hd : 2 ≤ d) (f : ℤ[X])
    (hmonic : f.Monic) (hdeg : f.natDegree = d)
    (hsplit : (f.map (algebraMap ℤ ℝ)).Splits) :
    ((((f.map (algebraMap ℤ ℝ)).roots).map fun x => x ^ 2).sum) =
      (((-f.coeff (d - 1) : ℤ) : ℝ) ^ 2 -
        2 * (f.coeff (d - 2) : ℝ)) := by
  let p : ℝ[X] := f.map (algebraMap ℤ ℝ)
  change p.Splits at hsplit
  have hpmonic : p.Monic := hmonic.map _
  have hpdeg : p.natDegree = d := by
    exact (hmonic.natDegree_map (algebraMap ℤ ℝ)).trans hdeg
  have hdim1 : d - 1 ≤ p.natDegree := by omega
  have hdim2 : d - 2 ≤ p.natDegree := by omega
  have hcoeff1 :=
    Polynomial.coeff_eq_esymm_roots_of_splits hsplit hdim1
  have hcoeff2 :=
    Polynomial.coeff_eq_esymm_roots_of_splits hsplit hdim2
  rw [hpdeg] at hcoeff1 hcoeff2
  have hcoeff1' : p.coeff (d - 1) = -p.roots.esymm 1 := by
    rw [hpmonic.leadingCoeff] at hcoeff1
    simpa [show d - (d - 1) = 1 by omega] using hcoeff1
  have hcoeff2' : p.coeff (d - 2) = p.roots.esymm 2 := by
    rw [hpmonic.leadingCoeff] at hcoeff2
    simpa [show d - (d - 2) = 2 by omega] using hcoeff2
  have hsum :
      p.roots.sum = ((-f.coeff (d - 1) : ℤ) : ℝ) := by
    calc
      p.roots.sum = p.roots.esymm 1 := by
        rw [Multiset.esymm, Multiset.powersetCard_one,
          Multiset.map_map]
        simp
      _ = -p.coeff (d - 1) := by linarith
      _ = ((-f.coeff (d - 1) : ℤ) : ℝ) := by simp [p]
  have hesymm :
      p.roots.esymm 2 = (f.coeff (d - 2) : ℝ) := by
    rw [← hcoeff2']
    simp [p]
  change ((p.roots.map fun x => x ^ 2).sum) = _
  rw [v15_multiset_sum_sq_eq_sum_sq_sub_two_esymm, hsum, hesymm]

/-- Every real root of a Hunter candidate lies in one explicit compact
interval depending only on the degree and spread bound. -/
theorem v15_hunterPolynomialCandidate_root_bound
    {d : ℕ} (hd : 2 ≤ d) {B : ℝ} {f : ℤ[X]}
    (h : V15HunterPolynomialCandidate d B f) :
    ∀ z ∈ (f.map (algebraMap ℤ ℝ)).roots,
      ‖z‖ ≤ v15HunterRootBound d B := by
  classical
  rcases h with ⟨hmonic, _, hdeg, hsplit,
    hs1nonneg, hs1half, hspread⟩
  let p : ℝ[X] := f.map (algebraMap ℤ ℝ)
  let s1 : ℤ := -f.coeff (d - 1)
  let s2 : ℤ := f.coeff (d - 2)
  have hsum := v15_hunter_roots_sum_sq_eq_coefficients
    d hd f hmonic hdeg hsplit
  change ((p.roots.map fun x => x ^ 2).sum) =
      ((s1 : ℝ) ^ 2 - 2 * (s2 : ℝ)) at hsum
  have hsumsqNonneg :
      0 ≤ (p.roots.map fun x => x ^ 2).sum := by
    apply Multiset.sum_nonneg
    intro y hy
    obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp hy
    exact sq_nonneg x
  have hdreal : (1 : ℝ) ≤ d := by
    exact_mod_cast (show 1 ≤ d by omega)
  have hs1le : s1 ≤ (d : ℤ) := by
    change 0 ≤ s1 at hs1nonneg
    change 2 * s1 ≤ (d : ℤ) at hs1half
    omega
  have hs1nonnegReal : (0 : ℝ) ≤ s1 := by
    exact_mod_cast hs1nonneg
  have hs1leReal : (s1 : ℝ) ≤ d := by
    exact_mod_cast hs1le
  have hs1sq : (s1 : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 := by
    nlinarith
  have hspreadReal := hspread
  change (((v15GeneralSpread d s1 s2 : ℤ) : ℝ)) < B at hspreadReal
  push_cast [v15GeneralSpread] at hspreadReal
  have hsumLt :
      (p.roots.map fun x => x ^ 2).sum <
        max B 0 + (d : ℝ) ^ 2 := by
    rw [hsum]
    have hB : B ≤ max B 0 := le_max_left _ _
    nlinarith
  intro z hz
  have hzmem : z ^ 2 ∈ p.roots.map (fun x => x ^ 2) :=
    Multiset.mem_map.mpr ⟨z, hz, rfl⟩
  have hzsq : z ^ 2 ≤ (p.roots.map fun x => x ^ 2).sum := by
    apply Multiset.single_le_sum
    · intro y hy
      obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp hy
      exact sq_nonneg x
    · exact hzmem
  have hzsqLt : z ^ 2 < max B 0 + (d : ℝ) ^ 2 :=
    lt_of_le_of_lt hzsq hsumLt
  have hT : 0 ≤ max B 0 + (d : ℝ) ^ 2 := by positivity
  have hsqrt := Real.sq_sqrt hT
  have hsqrtNonneg :=
    Real.sqrt_nonneg (max B 0 + (d : ℝ) ^ 2)
  have hzabs :
      |z| ≤ Real.sqrt (max B 0 + (d : ℝ) ^ 2) := by
    nlinarith [sq_abs z]
  simpa [v15HunterRootBound, Real.norm_eq_abs] using hzabs

/-- Every coefficient of a Hunter candidate lies in one explicit interval. -/
theorem v15_hunterPolynomialCandidate_coeff_bound
    {d : ℕ} (hd : 2 ≤ d) {B : ℝ} {f : ℤ[X]}
    (h : V15HunterPolynomialCandidate d B f) (i : ℕ) :
    ‖(f.coeff i : ℝ)‖ ≤ v15HunterCoefficientBound d B := by
  rcases h with ⟨hmonic, hirr, hdeg, hsplit,
    hs1nonneg, hs1half, hspread⟩
  have hroot := v15_hunterPolynomialCandidate_root_bound hd
    ⟨hmonic, hirr, hdeg, hsplit, hs1nonneg, hs1half, hspread⟩
  have hb := Polynomial.coeff_bdd_of_roots_le
    (algebraMap ℤ ℝ) hmonic hsplit hdeg.le hroot i
  simpa [v15HunterCoefficientBound] using hb

/-- A directly enumerable box of integral polynomials of degree at most `d`
whose coefficients lie between `-M` and `M`. -/
def v15IntegralPolynomialBox (d M : ℕ) : Finset ℤ[X] :=
  (Fintype.piFinset fun _ : Fin (d + 1) =>
    Finset.Icc (-(M : ℤ)) (M : ℤ)).image (Polynomial.ofFn (d + 1))

open scoped Classical in
/-- Membership in the executable coefficient box is exactly the degree and
coordinatewise integer bound. -/
theorem v15_mem_integralPolynomialBox_iff
    (d M : ℕ) (f : ℤ[X]) :
    f ∈ v15IntegralPolynomialBox d M ↔
      f.natDegree ≤ d ∧ ∀ i : Fin (d + 1),
        -(M : ℤ) ≤ f.coeff i ∧ f.coeff i ≤ (M : ℤ) := by
  constructor
  · intro hf
    rw [v15IntegralPolynomialBox, Finset.mem_image] at hf
    obtain ⟨v, hv, rfl⟩ := hf
    have hv' :
        ∀ i, v i ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) :=
      Fintype.mem_piFinset.mp hv
    constructor
    · exact Nat.le_of_lt_succ
        (Polynomial.ofFn_natDegree_lt (by omega) v)
    · intro i
      simpa [Polynomial.ofFn_coeff_eq_val_of_lt v i.2] using
        (Finset.mem_Icc.mp (hv' i))
  · rintro ⟨hdeg, hcoeff⟩
    rw [v15IntegralPolynomialBox, Finset.mem_image]
    let v : Fin (d + 1) → ℤ := Polynomial.toFn (d + 1) f
    refine ⟨v, ?_, ?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      exact Finset.mem_Icc.mpr (hcoeff i)
    · exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
        (by omega)

/-- The executable degree-`d`, coefficient-`M` box has exactly
`(2M+1)^(d+1)` elements. -/
theorem v15_card_integralPolynomialBox (d M : ℕ) :
    (v15IntegralPolynomialBox d M).card =
      (2 * M + 1) ^ (d + 1) := by
  rw [v15IntegralPolynomialBox]
  rw [Finset.card_image_of_injective]
  · rw [Fintype.card_piFinset]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    congr 1
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg (by omega)]
    push_cast
    ring
  · intro a b hab
    have h := congrArg (Polynomial.toFn (d + 1)) hab
    simpa [Polynomial.toFn_comp_ofFn_eq_id] using h

/-- Any natural-number upper bound for the analytic coefficient bound places
the Hunter candidate in a concrete executable polynomial box. -/
theorem v15_hunterPolynomialCandidate_mem_integralPolynomialBox
    {d M : ℕ} (hd : 2 ≤ d) {B : ℝ} {f : ℤ[X]}
    (hM : v15HunterCoefficientBound d B ≤ M)
    (h : V15HunterPolynomialCandidate d B f) :
    f ∈ v15IntegralPolynomialBox d M := by
  rw [v15_mem_integralPolynomialBox_iff]
  refine ⟨h.2.2.1.le, ?_⟩
  intro i
  have hb := v15_hunterPolynomialCandidate_coeff_bound hd h i
  have hb' : |(f.coeff i : ℝ)| ≤ (M : ℝ) := by
    simpa [Real.norm_eq_abs] using hb.trans hM
  constructor
  · exact_mod_cast (abs_le.mp hb').1
  · exact_mod_cast (abs_le.mp hb').2

/-- A symmetric constant-coefficient polynomial box over the integers is
finite. -/
theorem v15_boxPoly_const_finite (d : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    (Polynomial.boxPoly d (fun _ => -C) (fun _ => C)).Finite := by
  apply Set.finite_of_ncard_ne_zero
  rw [Polynomial.ncard_boxPoly]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  rw [Int.ceil_neg]
  have hfloor : (0 : ℤ) ≤ ⌊C⌋ := Int.floor_nonneg.mpr hC
  rw [ne_eq, Int.toNat_eq_zero]
  omega

/-- Each Hunter candidate belongs to the explicit coefficient box determined
by `v15HunterCoefficientBound`. -/
theorem v15_hunterPolynomialCandidate_mem_box
    {d : ℕ} (hd : 2 ≤ d) {B : ℝ} {f : ℤ[X]}
    (h : V15HunterPolynomialCandidate d B f) :
    f ∈ Polynomial.boxPoly d
      (fun _ => -v15HunterCoefficientBound d B)
      (fun _ => v15HunterCoefficientBound d B) := by
  change f.natDegree ≤ d ∧ ∀ i : Fin (d + 1),
    -v15HunterCoefficientBound d B ≤ f.coeff i ∧
      f.coeff i ≤ v15HunterCoefficientBound d B
  refine ⟨h.2.2.1.le, ?_⟩
  intro i
  have hb := v15_hunterPolynomialCandidate_coeff_bound hd h i
  simpa [Real.norm_eq_abs, abs_le] using hb

/-- For every fixed degree and fixed Hunter spread bound, only finitely many
integral candidate polynomials can occur. -/
theorem v15_hunterPolynomialCandidates_finite
    {d : ℕ} (hd : 2 ≤ d) (B : ℝ) :
    Set.Finite {f : ℤ[X] |
      V15HunterPolynomialCandidate d B f} := by
  have hC : 0 ≤ v15HunterCoefficientBound d B := by
    simp only [v15HunterCoefficientBound]
    positivity
  exact (v15_boxPoly_const_finite d
    (v15HunterCoefficientBound d B) hC).subset
      (fun _ hf => v15_hunterPolynomialCandidate_mem_box hd hf)

/-- The explicit box also gives a computable upper bound on the number of
Hunter candidates. -/
theorem v15_hunterPolynomialCandidates_ncard_le
    {d : ℕ} (hd : 2 ≤ d) (B : ℝ) :
    Set.ncard {f : ℤ[X] | V15HunterPolynomialCandidate d B f} ≤
      ∏ _i : Fin (d + 1),
        (⌊v15HunterCoefficientBound d B⌋ -
          ⌈-v15HunterCoefficientBound d B⌉ + 1).toNat := by
  have hC : 0 ≤ v15HunterCoefficientBound d B := by
    simp only [v15HunterCoefficientBound]
    positivity
  have hbox := v15_boxPoly_const_finite d
    (v15HunterCoefficientBound d B) hC
  calc
    Set.ncard {f : ℤ[X] | V15HunterPolynomialCandidate d B f} ≤
        Set.ncard (Polynomial.boxPoly d
          (fun _ => -v15HunterCoefficientBound d B)
          (fun _ => v15HunterCoefficientBound d B)) :=
      Set.ncard_le_ncard
        (fun _ hf => v15_hunterPolynomialCandidate_mem_box hd hf) hbox
    _ = _ := Polynomial.ncard_boxPoly d _ _

/-- The finite search space of all integral Hunter candidates for fixed
degree and spread bound. -/
noncomputable def v15HunterPolynomialCandidates
    (d : ℕ) (hd : 2 ≤ d) (B : ℝ) : Finset ℤ[X] :=
  (v15_hunterPolynomialCandidates_finite hd B).toFinset

@[simp]
theorem v15_mem_hunterPolynomialCandidates_iff
    (d : ℕ) (hd : 2 ≤ d) (B : ℝ) (f : ℤ[X]) :
    f ∈ v15HunterPolynomialCandidates d hd B ↔
      V15HunterPolynomialCandidate d B f := by
  simp [v15HunterPolynomialCandidates]

/-- The Hunter ball construction now lands in an actual finite polynomial
search space. -/
theorem v15_exists_mem_hunterPolynomialCandidates_of_hunterBall
    (K : Type*) [Field K] [NumberField K] {n : ℕ}
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = n + 1)
    (hprime : Nat.Prime (n + 1))
    (hn : 0 < n) (r : ℝ) (hr : 0 < r)
    (hball :
      ((|NumberField.discr K| : ℤ) : ℝ) *
          (((2 : ℝ) ^ n) ^ 2) <
        (n + 1 : ℝ) *
          (euclideanUnitBallVolume n * r ^ n) ^ 2) :
    ∃ f ∈ v15HunterPolynomialCandidates (n + 1) (by omega)
        ((n + 1 : ℝ) * r ^ 2),
      V15HunterPolynomialCandidate (n + 1)
        ((n + 1 : ℝ) * r ^ 2) f := by
  obtain ⟨f, hf⟩ :=
    v15_exists_hunterPolynomialCandidate_of_hunterBall
      K hreal hdegree hprime hn r hr hball
  exact ⟨f,
    (v15_mem_hunterPolynomialCandidates_iff
      (n + 1) (by omega) ((n + 1 : ℝ) * r ^ 2) f).2 hf,
    hf⟩

end

end TraceEuclidean
