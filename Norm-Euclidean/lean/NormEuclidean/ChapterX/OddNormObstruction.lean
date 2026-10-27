import NormEuclidean.ChapterX.GoodPlaceNorms
import Mathlib.Algebra.Order.GroupWithZero.Canonical

/-!
# The uniformizer obstruction at odd unramified quadratic places

In x squared minus pi times y squared, the two nonzero terms have distinct
valuation parity. A unit value forces both coordinates to be integral and
its residue to be a square. Hensel lifting then shows that a nonsquare unit
parameter cannot have the uniformizer as a quadratic norm.
-/

noncomputable section

namespace NormEuclidean.OddNormObstruction

open Polynomial IsDedekindDomain CompletedIntegralLattice
open scoped NumberField WithZero

/-- A unit with a square residue has a unit square root in the odd Henselian case. -/
theorem henselian_square_of_residue_square {S : Type*} [CommRing S] [IsLocalRing S]
    [HenselianRing S (IsLocalRing.maximalIdeal S)] (htwo : IsUnit (2 : S))
    (a : Sˣ) (x : S) (h : IsLocalRing.residue S (x ^ 2 - (a : S)) = 0) :
    ∃ r : Sˣ, (r : S) ^ 2 = (a : S) := by
  let f : S[X] := X ^ 2 - C (a : S)
  have hx : IsUnit x := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit x).mp
    intro hx0
    have ha := (a.isUnit.map (IsLocalRing.residue S)).ne_zero
    apply ha
    simpa only [map_sub, map_pow, hx0, zero_pow (by decide : 2 ≠ 0),
      zero_sub, neg_eq_zero] using h
  have hf : f.Monic := monic_X_pow_sub_C _ (by decide)
  have hfx : f.eval x ∈ IsLocalRing.maximalIdeal S := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simpa only [f, eval_sub, eval_pow, eval_X, eval_C] using h
  have hder : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S)
      (f.derivative.eval x)) := by
    have heq : f.derivative.eval x = 2 * x := by simp [f]; ring
    rw [heq]
    exact (htwo.mul hx).map _
  obtain ⟨r, hr, _⟩ := HenselianRing.is_henselian f hf x hfx hder
  have hr2 : r ^ 2 = (a : S) := by simpa [f, Polynomial.IsRoot, sub_eq_zero] using hr
  have hru : IsUnit r := (isUnit_pow_iff (by decide : 2 ≠ 0)).mp (hr2 ▸ a.isUnit)
  exact ⟨hru.unit, by simpa only [hru.unit_spec] using hr2⟩

/-- Distinct even and odd valuation parities force integrality of both
coordinates when the ramified binary norm takes a unit value. -/
theorem integral_coordinates {F : Type*} [Field F] [Valued F ℤᵐ⁰]
    (pi a x y : F) (hpi : Valued.v pi = WithZero.exp (-1 : ℤ))
    (ha : Valued.v a = 1) (h : x ^ 2 - pi * y ^ 2 = a) :
    Valued.v x ≤ 1 ∧ Valued.v y ≤ 1 ∧ Valued.v (x ^ 2 - a) < 1 := by
  have hpi0 : Valued.v pi ≠ 0 := by rw [hpi]; exact WithZero.exp_ne_zero
  have hne : Valued.v (x ^ 2) ≠ Valued.v (pi * y ^ 2) := by
    by_cases hx : x = 0
    · intro heq
      have hy : Valued.v (pi * y ^ 2) = 0 := by simpa [hx] using heq.symm
      have hv : Valued.v (x ^ 2 - pi * y ^ 2) = 0 := by
        simpa [hx, Valuation.map_neg] using hy
      rw [h, ha] at hv
      exact one_ne_zero hv
    · by_cases hy : y = 0
      · simpa [hy] using (Valuation.ne_zero_iff Valued.v).mpr (pow_ne_zero 2 hx)
      · have hxv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr hx
        have hyv : Valued.v y ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr hy
        intro heq
        have hl := congrArg WithZero.log heq
        simp only [map_pow, map_mul, hpi, WithZero.log_mul (WithZero.exp_ne_zero)
          (pow_ne_zero 2 hyv), WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul] at hl
        omega
  have hmax : max (Valued.v (x ^ 2)) (Valued.v (pi * y ^ 2)) = 1 := by
    have hh := (Valued.v : Valuation F ℤᵐ⁰).map_add_of_distinct_val
      (x := x ^ 2) (y := -(pi * y ^ 2)) (by simpa only [Valuation.map_neg] using hne)
    simpa only [← sub_eq_add_neg, h, ha, Valuation.map_neg] using hh.symm
  have hx2 : Valued.v x ^ 2 ≤ 1 := by
    rw [← map_pow]
    exact (le_max_left _ _).trans hmax.le
  have hx1 : Valued.v x ≤ 1 := by
    by_contra! hx
    exact not_le_of_gt (one_lt_pow₀ hx (by decide : 2 ≠ 0)) hx2
  have hy2 : WithZero.exp (-1 : ℤ) * Valued.v y ^ 2 ≤ 1 := by
    rw [← hpi, ← map_pow, ← map_mul]
    exact (le_max_right _ _).trans hmax.le
  have hy1 : Valued.v y ≤ 1 := by
    by_cases hy : y = 0
    · simp [hy]
    · have hyv : Valued.v y ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr hy
      have hl := (WithZero.log_le_log
        (mul_ne_zero (WithZero.exp_ne_zero) (pow_ne_zero 2 hyv)) one_ne_zero).mpr hy2
      simp only [WithZero.log_mul (WithZero.exp_ne_zero) (pow_ne_zero 2 hyv),
        WithZero.log_exp, WithZero.log_pow, WithZero.log_one, nsmul_eq_mul] at hl
      apply (WithZero.log_le_log hyv one_ne_zero).mp
      simp only [WithZero.log_one]
      omega
  refine ⟨hx1, hy1, ?_⟩
  have heq : x ^ 2 - a = pi * y ^ 2 := by linear_combination h
  rw [heq, map_mul, map_pow, hpi]
  have hlt : WithZero.exp (-1 : ℤ) < (1 : ℤᵐ⁰) := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  exact mul_lt_one_of_nonneg_of_lt_one_left bot_le hlt (pow_le_one₀ bot_le hy1)

variable {K : Type*} [Field K] [NumberField K]

/-- At an odd actual finite completion, a unit parameter admitting a
uniformizer as a quadratic norm is a square. -/
theorem square_of_uniformizer_norm (p : HeightOneSpectrum (𝓞 K))
    (htwo : (2 : 𝓞 K) ∉ p.asIdeal) (theta pi : (p.adicCompletion K)ˣ)
    (htheta : Valued.v (theta : p.adicCompletion K) = 1)
    (hpi : Valued.v (pi : p.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (hnorm : Bong.Dyadic.IsQuadraticNorm (p.adicCompletion K) theta pi) :
    IsSquare theta := by
  obtain ⟨x, y, h⟩ := hnorm.symm
  obtain ⟨hx, hy, hclose⟩ := integral_coordinates pi.val theta.val x y hpi htheta h
  let S := LocalRing (integerSubring K) p
  letI : HenselianRing S (IsLocalRing.maximalIdeal S) :=
    CompletionHensel.henselian_completed_integers p
  let t : S := ⟨theta.val, htheta.le⟩
  let z : S := ⟨x, hx⟩
  have ht : IsUnit t :=
    (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mpr htheta
  have htwoS : IsUnit (2 : S) := by
    have h := isUnit_algebraMap_localRing (integerSubring K) p htwo
    convert h using 1
    apply Subtype.ext
    exact (map_ofNat (algebraMap K (p.adicCompletion K)) 2).symm
  have hmem : z ^ 2 - t ∈ IsLocalRing.maximalIdeal S := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hv := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp hu
    exact hclose.ne hv
  have hres : IsLocalRing.residue S (z ^ 2 - ht.unit.val) = 0 := by
    rw [ht.unit_spec, IsLocalRing.residue_eq_zero_iff]
    exact hmem
  obtain ⟨r, hr⟩ := henselian_square_of_residue_square htwoS ht.unit z hres
  have hrF := congrArg S.subtype hr
  rw [map_pow, ht.unit_spec] at hrF
  change S.subtype r.val ^ 2 = theta.val at hrF
  have hr0 : S.subtype r.val ≠ 0 := by
    intro hz
    apply r.ne_zero
    apply Subtype.ext
    exact hz
  refine ⟨Units.mk0 (S.subtype r.val) hr0, ?_⟩
  apply Units.ext
  change theta.val = S.subtype r.val * S.subtype r.val
  exact hrF.symm.trans (pow_two _)

end NormEuclidean.OddNormObstruction
