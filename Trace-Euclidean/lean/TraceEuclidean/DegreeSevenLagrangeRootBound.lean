import TraceEuclidean.DegreeSevenMinimumReduction

/-!
# Lagrange root bounds for the degree-seven Hunter search

Voight's coefficient enumeration combines Rolle interlacing with an outer
root bound obtained from the first two Newton sums.  This file proves that
outer bound in the exact rational form needed by the later generated
certificates.
-/

namespace TraceEuclidean

noncomputable section

open Polynomial

/-- Cauchy's inequality for a multiset, retaining multiplicities. -/
theorem multiset_sum_sq_le_card_mul_sum_sq (s : Multiset ℝ) :
    s.sum ^ 2 ≤ (s.card : ℝ) * (s.map fun x => x ^ 2).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      by_cases hs : s = 0
      · subst s
        simp
      · let n : ℝ := s.card
        let S : ℝ := s.sum
        let Q : ℝ := (s.map fun x => x ^ 2).sum
        have hnNat : 0 < s.card := Multiset.card_pos.mpr hs
        have hn : 0 < n := by
          dsimp [n]
          exact_mod_cast hnNat
        have hdefect : 0 ≤ n * Q - S ^ 2 := by
          dsimp [n, S, Q]
          linarith
        have hweighted : 0 ≤ (n + 1) * (n * Q - S ^ 2) :=
          mul_nonneg (by linarith) hdefect
        have hsquare : 0 ≤ (n * a - S) ^ 2 := sq_nonneg _
        have hscaled :
            0 ≤ n * ((n + 1) * (a ^ 2 + Q) - (a + S) ^ 2) := by
          nlinarith
        have hgoal : (a + S) ^ 2 ≤ (n + 1) * (a ^ 2 + Q) := by
          nlinarith
        simpa [n, S, Q, Nat.cast_add, Nat.cast_one] using hgoal

/-- Every root of a degree-seven minimum Hunter candidate satisfies the
Lagrange mean-variance bound determined by the two top nonleading
coefficients.  The square-free form avoids any analytic square-root
normalization in generated certificates. -/
theorem degreeSeven_minimumHunterCandidate_root_centered_sq_le
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    {z : ℝ} (hz : z ∈ (f.map (algebraMap ℤ ℝ)).roots) :
    (7 * z + (f.coeff 6 : ℝ)) ^ 2 ≤
      12 * (3 * (f.coeff 6 : ℝ) ^ 2 - 7 * (f.coeff 5 : ℝ)) := by
  let p : ℝ[X] := f.map (algebraMap ℤ ℝ)
  let rest : Multiset ℝ := p.roots.erase z
  have hpmonic : p.Monic := h.1.map _
  have hpdegree : p.natDegree = 7 := by
    exact (h.1.natDegree_map (algebraMap ℤ ℝ)).trans h.2.2.1
  have hcard : p.roots.card = 7 := by
    rw [← hpdegree]
    exact h.2.2.2.1.natDegree_eq_card_roots.symm
  have hrestCard : rest.card = 6 := by
    dsimp [rest]
    rw [Multiset.card_erase_of_mem hz, hcard]
    norm_num
  have hcons : z ::ₘ rest = p.roots := by
    exact Multiset.cons_erase hz
  have hsumRoots : p.roots.sum = (-(f.coeff 6 : ℝ)) := by
    have hnext :=
      h.2.2.2.1.nextCoeff_eq_neg_sum_roots_of_monic hpmonic
    have hnextCoeff : p.nextCoeff = (f.coeff 6 : ℝ) := by
      rw [Polynomial.nextCoeff, hpdegree]
      norm_num [p]
    rw [hnextCoeff] at hnext
    linarith
  have hsumSq := hunter_roots_sum_sq_eq_coefficients
    7 (by norm_num) f h.1 h.2.2.1 h.2.2.2.1
  have hsumSq' : (p.roots.map fun x => x ^ 2).sum =
      (f.coeff 6 : ℝ) ^ 2 - 2 * (f.coeff 5 : ℝ) := by
    simpa [p] using hsumSq
  have hsumRest : rest.sum = -(f.coeff 6 : ℝ) - z := by
    have hsumCons := congrArg Multiset.sum hcons
    simp only [Multiset.sum_cons] at hsumCons
    linarith
  have hsumSqRest :
      (rest.map fun x => x ^ 2).sum =
        (f.coeff 6 : ℝ) ^ 2 - 2 * (f.coeff 5 : ℝ) - z ^ 2 := by
    have hsumCons := congrArg
      (fun t : Multiset ℝ => (t.map fun x => x ^ 2).sum) hcons
    simp only [Multiset.map_cons, Multiset.sum_cons] at hsumCons
    linarith [hsumSq']
  have hcauchy := multiset_sum_sq_le_card_mul_sum_sq rest
  rw [hrestCard] at hcauchy
  norm_num at hcauchy
  rw [hsumRest, hsumSqRest] at hcauchy
  nlinarith

/-- A rational square majorant converts the centered Lagrange inequality
into explicit rational endpoints for every root. -/
theorem degreeSeven_minimumHunterCandidate_root_mem_lagrange_interval
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f)
    {z : ℝ} (hz : z ∈ (f.map (algebraMap ℤ ℝ)).roots)
    (R : ℚ) (hRnonneg : 0 ≤ R)
    (hR :
      (12 : ℝ) *
          (3 * (f.coeff 6 : ℝ) ^ 2 - 7 * (f.coeff 5 : ℝ)) ≤
        (R : ℝ) ^ 2) :
    ((-(f.coeff 6 : ℝ) - (R : ℝ)) / 7 ≤ z ∧
      z ≤ (-(f.coeff 6 : ℝ) + (R : ℝ)) / 7) := by
  have hcenter :=
    degreeSeven_minimumHunterCandidate_root_centered_sq_le h hz
  have hsq :
      (7 * z + (f.coeff 6 : ℝ)) ^ 2 ≤ (R : ℝ) ^ 2 :=
    hcenter.trans hR
  have hRnonnegReal : (0 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast hRnonneg
  have habs : |7 * z + (f.coeff 6 : ℝ)| ≤ (R : ℝ) := by
    apply (sq_le_sq₀ (abs_nonneg _) hRnonnegReal).mp
    simpa [sq_abs] using hsq
  rw [abs_le] at habs
  constructor <;> linarith

/-- The closed Hunter coefficient ranges make `38` a strict rational
majorant for every centered root.  These are the outer endpoints used by the
fifth Rolle stage. -/
theorem degreeSeven_minimumHunterCandidate_root_lagrange_strict_bounds
    {f : ℤ[X]} (h : HunterPolynomialCandidate 7 194 f) :
    ∀ z ∈ (f.map (algebraMap ℤ ℝ)).roots,
      ((-(f.coeff 6 : ℝ) - 38) / 7 < z ∧
        z < (-(f.coeff 6 : ℝ) + 38) / 7) := by
  intro z hz
  have ha6 := degreeSevenMinimum_traceCoefficient_bounds h
  have ha5 := degreeSevenMinimum_secondCoefficient_bounds h
  have ha6Lower : (-3 : ℝ) ≤ (f.coeff 6 : ℝ) := by
    exact_mod_cast ha6.1
  have ha6Upper : (f.coeff 6 : ℝ) ≤ 0 := by
    exact_mod_cast ha6.2
  have ha5Lower : (-13 : ℝ) ≤ (f.coeff 5 : ℝ) := by
    exact_mod_cast ha5.1
  have hmajorant :
      (12 : ℝ) *
          (3 * (f.coeff 6 : ℝ) ^ 2 - 7 * (f.coeff 5 : ℝ)) <
        (38 : ℝ) ^ 2 := by
    nlinarith
  have hcenter :=
    degreeSeven_minimumHunterCandidate_root_centered_sq_le h hz
  have hsquare :
      (7 * z + (f.coeff 6 : ℝ)) ^ 2 < (38 : ℝ) ^ 2 :=
    hcenter.trans_lt hmajorant
  have habs := abs_lt_of_sq_lt_sq' hsquare (by norm_num : (0 : ℝ) ≤ 38)
  constructor <;> linarith

end

end TraceEuclidean
