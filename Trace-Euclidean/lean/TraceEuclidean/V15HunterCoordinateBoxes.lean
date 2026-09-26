import TraceEuclidean.V15HunterCoefficientFiniteness

/-!
# Coordinatewise Hunter coefficient boxes

The first finite Hunter box uses one uniform bound for every coefficient.
This module proves the sharper Vieta estimate in each coordinate.  It then
constructs an executable integer polynomial box whose `i`th interval has
radius `choose d (d-i) * R^(d-i)`.
-/

namespace TraceEuclidean

open Polynomial

noncomputable section

/-- If every entry of a real multiset has norm at most `R`, its `k`th
elementary symmetric function has norm at most `choose(card s,k) * R^k`. -/
theorem v15_norm_esymm_le_choose_mul_pow
    {s : Multiset ℝ} {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ z ∈ s, ‖z‖ ≤ R) (k : ℕ) :
    ‖s.esymm k‖ ≤ (s.card.choose k : ℝ) * R ^ k := by
  rw [Multiset.esymm]
  have hprod : ∀ t : Multiset ℝ, t ≤ s →
      ‖t.prod‖ ≤ R ^ t.card := by
    intro t ht
    induction t using Multiset.induction_on with
    | empty => simp
    | @cons z t ih =>
        have hz : ‖z‖ ≤ R := h z (Multiset.mem_of_le ht (by simp))
        have ht' : t ≤ s :=
          le_trans (Multiset.le_cons_self t z) ht
        have hit := ih ht'
        rw [Multiset.prod_cons, Multiset.card_cons, norm_mul]
        calc
          ‖z‖ * ‖t.prod‖ ≤ R * R ^ t.card :=
            mul_le_mul hz hit (norm_nonneg _) hR
          _ = R ^ (t.card + 1) := by rw [pow_succ]; ring
  calc
    ‖((s.powersetCard k).map Multiset.prod).sum‖ ≤
        (((s.powersetCard k).map Multiset.prod).map
          fun x => ‖x‖).sum :=
      norm_multiset_sum_le _
    _ = ((s.powersetCard k).map fun t => ‖t.prod‖).sum := by
      rw [Multiset.map_map]
      rfl
    _ ≤ (s.powersetCard k).card • R ^ k := by
      rw [← Multiset.card_map]
      apply Multiset.sum_le_card_nsmul
      intro x hx
      obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hx
      exact (hprod t (Multiset.mem_powersetCard.mp ht).1).trans_eq
        (congrArg (R ^ ·) (Multiset.mem_powersetCard.mp ht).2)
    _ = (s.card.choose k : ℝ) * R ^ k := by
      rw [Multiset.card_powersetCard]
      simp [nsmul_eq_mul]

/-- The coordinatewise Vieta bound for a Hunter candidate.  Unlike the
uniform bound, this keeps the actual elementary-symmetric degree `d-i`. -/
theorem v15_hunterPolynomialCandidate_coeff_bound_at
    {d : ℕ} (hd : 2 ≤ d) {B : ℝ} {f : ℤ[X]}
    (h : V15HunterPolynomialCandidate d B f)
    (i : ℕ) (hi : i ≤ d) :
    ‖(f.coeff i : ℝ)‖ ≤
      (d.choose (d - i) : ℝ) *
        v15HunterRootBound d B ^ (d - i) := by
  let p : ℝ[X] := f.map (algebraMap ℤ ℝ)
  have hpmonic : p.Monic := h.1.map _
  have hpdeg : p.natDegree = d := by
    exact (h.1.natDegree_map (algebraMap ℤ ℝ)).trans h.2.2.1
  have hcoeff := Polynomial.coeff_eq_esymm_roots_of_splits
    h.2.2.2.1 (show i ≤ p.natDegree by simpa [hpdeg])
  have hroot := v15_hunterPolynomialCandidate_root_bound hd h
  have hR : 0 ≤ v15HunterRootBound d B := by
    exact Real.sqrt_nonneg _
  have hesymm := v15_norm_esymm_le_choose_mul_pow hR hroot (d - i)
  rw [hpdeg] at hcoeff
  change p.coeff i = p.leadingCoeff * (-1) ^ (d - i) *
    p.roots.esymm (d - i) at hcoeff
  have hcard : p.roots.card = d := by
    rw [← hpdeg]
    exact h.2.2.2.1.natDegree_eq_card_roots.symm
  rw [hcard] at hesymm
  calc
    ‖(f.coeff i : ℝ)‖ = ‖p.coeff i‖ := by simp [p]
    _ = ‖p.roots.esymm (d - i)‖ := by
      rw [hcoeff, hpmonic.leadingCoeff]
      simp
    _ ≤ (d.choose (d - i) : ℝ) *
        v15HunterRootBound d B ^ (d - i) := hesymm

/-- The natural coordinate radius obtained from a natural root bound `R`. -/
def v15HunterCoordinateBound
    (d R : ℕ) (i : Fin (d + 1)) : ℕ :=
  d.choose (d - (i : ℕ)) * R ^ (d - (i : ℕ))

/-- An executable integer polynomial box with a separate symmetric interval
for every coefficient. -/
def v15IntegralPolynomialCoordinateBox
    (d : ℕ) (M : Fin (d + 1) → ℕ) : Finset ℤ[X] :=
  (Fintype.piFinset fun i : Fin (d + 1) =>
    Finset.Icc (-(M i : ℤ)) (M i : ℤ)).image
      (Polynomial.ofFn (d + 1))

open scoped Classical in
/-- Membership in the coordinate box is exactly the degree condition and
the displayed coordinatewise integer bounds. -/
theorem v15_mem_integralPolynomialCoordinateBox_iff
    (d : ℕ) (M : Fin (d + 1) → ℕ) (f : ℤ[X]) :
    f ∈ v15IntegralPolynomialCoordinateBox d M ↔
      f.natDegree ≤ d ∧ ∀ i : Fin (d + 1),
        -(M i : ℤ) ≤ f.coeff i ∧ f.coeff i ≤ (M i : ℤ) := by
  constructor
  · intro hf
    rw [v15IntegralPolynomialCoordinateBox, Finset.mem_image] at hf
    obtain ⟨v, hv, rfl⟩ := hf
    have hv' :
        ∀ i, v i ∈ Finset.Icc (-(M i : ℤ)) (M i : ℤ) :=
      Fintype.mem_piFinset.mp hv
    constructor
    · exact Nat.le_of_lt_succ
        (Polynomial.ofFn_natDegree_lt (by omega) v)
    · intro i
      simpa [Polynomial.ofFn_coeff_eq_val_of_lt v i.2] using
        (Finset.mem_Icc.mp (hv' i))
  · rintro ⟨hdeg, hcoeff⟩
    rw [v15IntegralPolynomialCoordinateBox, Finset.mem_image]
    let v : Fin (d + 1) → ℤ := Polynomial.toFn (d + 1) f
    refine ⟨v, ?_, ?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      exact Finset.mem_Icc.mpr (hcoeff i)
    · exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
        (by omega)

/-- The exact cardinality of the coordinate box. -/
theorem v15_card_integralPolynomialCoordinateBox
    (d : ℕ) (M : Fin (d + 1) → ℕ) :
    (v15IntegralPolynomialCoordinateBox d M).card =
      ∏ i : Fin (d + 1), (2 * M i + 1) := by
  rw [v15IntegralPolynomialCoordinateBox]
  rw [Finset.card_image_of_injective]
  · rw [Fintype.card_piFinset]
    apply Finset.prod_congr rfl
    intro i _
    rw [Int.card_Icc]
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg (by omega)]
    push_cast
    ring
  · intro a b hab
    have h := congrArg (Polynomial.toFn (d + 1)) hab
    simpa [Polynomial.toFn_comp_ofFn_eq_id] using h

/-- An executable integer polynomial box with independent lower and upper
endpoints in every coordinate. -/
def v15IntegralPolynomialIntervalBox
    (d : ℕ) (L U : Fin (d + 1) → ℤ) : Finset ℤ[X] :=
  (Fintype.piFinset fun i : Fin (d + 1) =>
    Finset.Icc (L i) (U i)).image (Polynomial.ofFn (d + 1))

open scoped Classical in
/-- Membership in the interval box is exactly the degree condition and its
coordinatewise endpoint inequalities. -/
theorem v15_mem_integralPolynomialIntervalBox_iff
    (d : ℕ) (L U : Fin (d + 1) → ℤ) (f : ℤ[X]) :
    f ∈ v15IntegralPolynomialIntervalBox d L U ↔
      f.natDegree ≤ d ∧ ∀ i : Fin (d + 1),
        L i ≤ f.coeff i ∧ f.coeff i ≤ U i := by
  constructor
  · intro hf
    rw [v15IntegralPolynomialIntervalBox, Finset.mem_image] at hf
    obtain ⟨v, hv, rfl⟩ := hf
    have hv' : ∀ i, v i ∈ Finset.Icc (L i) (U i) :=
      Fintype.mem_piFinset.mp hv
    constructor
    · exact Nat.le_of_lt_succ
        (Polynomial.ofFn_natDegree_lt (by omega) v)
    · intro i
      simpa [Polynomial.ofFn_coeff_eq_val_of_lt v i.2] using
        (Finset.mem_Icc.mp (hv' i))
  · rintro ⟨hdeg, hcoeff⟩
    rw [v15IntegralPolynomialIntervalBox, Finset.mem_image]
    let v : Fin (d + 1) → ℤ := Polynomial.toFn (d + 1) f
    refine ⟨v, ?_, ?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      exact Finset.mem_Icc.mpr (hcoeff i)
    · exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
        (by omega)

/-- Exact cardinality of an interval box. -/
theorem v15_card_integralPolynomialIntervalBox
    (d : ℕ) (L U : Fin (d + 1) → ℤ) :
    (v15IntegralPolynomialIntervalBox d L U).card =
      ∏ i : Fin (d + 1), (U i + 1 - L i).toNat := by
  rw [v15IntegralPolynomialIntervalBox]
  rw [Finset.card_image_of_injective]
  · rw [Fintype.card_piFinset]
    apply Finset.prod_congr rfl
    intro i _
    exact Int.card_Icc (L i) (U i)
  · intro a b hab
    have h := congrArg (Polynomial.toFn (d + 1)) hab
    simpa [Polynomial.toFn_comp_ofFn_eq_id] using h

/-- A natural upper bound for the Hunter root radius places the candidate in
the sharper executable coordinate box. -/
theorem v15_hunterPolynomialCandidate_mem_coordinateBox
    {d R : ℕ} (hd : 2 ≤ d) {B : ℝ} {f : ℤ[X]}
    (hR : v15HunterRootBound d B ≤ R)
    (h : V15HunterPolynomialCandidate d B f) :
    f ∈ v15IntegralPolynomialCoordinateBox d
      (v15HunterCoordinateBound d R) := by
  rw [v15_mem_integralPolynomialCoordinateBox_iff]
  refine ⟨h.2.2.1.le, ?_⟩
  intro i
  have hb := v15_hunterPolynomialCandidate_coeff_bound_at
    hd h i (by omega)
  have hrootNonneg : 0 ≤ v15HunterRootBound d B :=
    Real.sqrt_nonneg _
  have hpow :
      v15HunterRootBound d B ^ (d - (i : ℕ)) ≤
        (R : ℝ) ^ (d - (i : ℕ)) := by
    gcongr
  have hb' :
      |(f.coeff i : ℝ)| ≤
        (v15HunterCoordinateBound d R i : ℝ) := by
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (by
      rw [v15HunterCoordinateBound]
      push_cast
      gcongr)
  constructor
  · exact_mod_cast (abs_le.mp hb').1
  · exact_mod_cast (abs_le.mp hb').2

end

end TraceEuclidean
