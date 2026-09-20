import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import TraceEuclidean.DiscriminantBounds
import TraceEuclidean.AnalyticFiniteness

open Set

noncomputable section

namespace TraceEuclidean

/-!
Effective Stirling and half-integral Gamma estimates, together with a coarse
volume bound sufficient for every finiteness range in Theorems 1.2 and 1.3.
The constants are deliberately less sharp than the manuscript's Batir bounds;
the weaker estimate has the same rank thresholds and can be proved entirely
from mathlib.
-/

theorem factorial_upper_stirling (n : ℕ) (hn : 0 < n) :
    (n.factorial : ℝ) < Real.exp 1 * Real.sqrt (2 * n) *
      (((n : ℝ) / Real.exp 1) ^ n : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hanti := Stirling.stirlingSeq'_antitone (Nat.zero_le k)
  change Stirling.stirlingSeq (k + 1) ≤
    Stirling.stirlingSeq (0 + 1) at hanti
  rw [Stirling.stirlingSeq_one] at hanti
  have hsqrt : (1 : ℝ) < Real.sqrt 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hseq : Stirling.stirlingSeq (k + 1) < Real.exp 1 :=
    hanti.trans_lt ((div_lt_iff₀ (Real.sqrt_pos.2 (by norm_num))).2
      (by nlinarith [Real.exp_pos (1 : ℝ)]))
  rw [Stirling.stirlingSeq] at hseq
  have hden :
      0 < Real.sqrt (2 * ((k + 1 : ℕ) : ℝ)) *
        ((((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) : ℝ) := by
    positivity
  have := (div_lt_iff₀ hden).mp hseq
  simpa only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one,
    mul_assoc] using this

theorem gamma_half_nat_lower_strict (m : ℕ) (hm : 0 < m) :
    (((m : ℝ) / (2 * Real.exp 1)) ^ ((m : ℝ) / 2) : ℝ) <
      Real.Gamma ((m : ℝ) / 2 + 1) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · have hk : 0 < k := by omega
    have hbase :
        (((((2 * k : ℕ) : ℝ) / (2 * Real.exp 1)) ^
            (((2 * k : ℕ) : ℝ) / 2)) : ℝ) =
          (((k : ℝ) / Real.exp 1) ^ k : ℝ) := by
      rw [show (((2 * k : ℕ) : ℝ) / (2 * Real.exp 1)) =
          (k : ℝ) / Real.exp 1 by push_cast; field_simp]
      rw [show (((2 * k : ℕ) : ℝ) / 2) = (k : ℝ) by push_cast; ring]
      exact Real.rpow_natCast _ k
    rw [hbase]
    rw [show (((2 * k : ℕ) : ℝ) / 2 + 1) = (k : ℝ) + 1 by
      push_cast; ring]
    rw [Real.Gamma_nat_eq_factorial]
    have hs := Stirling.le_factorial_stirling k
    have hsqrt : (1 : ℝ) < Real.sqrt (2 * Real.pi * k) := by
      have hA : 0 ≤ 2 * Real.pi * (k : ℝ) := by positivity
      have hAsq := Real.sq_sqrt hA
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hpiMul : 3 * (k : ℝ) < Real.pi * k :=
        mul_lt_mul_of_pos_right Real.pi_gt_three (by positivity)
      nlinarith [Real.sqrt_nonneg (2 * Real.pi * k)]
    have hpow : 0 < ((k : ℝ) / Real.exp 1) ^ k := by positivity
    have hstrict :
        ((k : ℝ) / Real.exp 1) ^ k <
          Real.sqrt (2 * Real.pi * k) * ((k : ℝ) / Real.exp 1) ^ k := by
      nlinarith [mul_pos (sub_pos.mpr hsqrt) hpow]
    exact hstrict.trans_le hs
  · have hk0 : 0 ≤ k := Nat.zero_le k
    by_cases hk : k = 0
    · subst k
      norm_num only [Nat.cast_one]
      have hleft :
          ((1 / (2 * Real.exp 1)) ^ (1 / 2 : ℝ) : ℝ) <
            Real.sqrt Real.pi / 2 := by
        rw [← Real.sqrt_eq_rpow]
        have he : (2 : ℝ) < Real.exp 1 := by
          linarith [Real.exp_one_gt_d9]
        have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
        have hfrac : (1 : ℝ) / (2 * Real.exp 1) < 1 / 4 := by
          apply (div_lt_iff₀ (by positivity)).2
          nlinarith
        have hsqrt : Real.sqrt (1 / (2 * Real.exp 1)) < 1 / 2 := by
          have h := Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 / (2 * Real.exp 1) by
            positivity) hfrac
          norm_num at h ⊢
          exact h
        have hright : (1 / 2 : ℝ) < Real.sqrt Real.pi / 2 := by
          have hs := Real.sq_sqrt Real.pi_pos.le
          nlinarith [Real.sqrt_nonneg Real.pi]
        exact hsqrt.trans hright
      have hGamma :
          Real.Gamma ((1 : ℝ) / 2 + 1) = Real.sqrt Real.pi / 2 := by
        rw [Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0),
          Real.Gamma_one_half_eq]
        ring
      have hGamma' :
          Real.Gamma (3 / 2 : ℝ) = Real.sqrt Real.pi / 2 := by
        convert hGamma using 1
        ring
      rw [hGamma']
      exact hleft
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have htargetNonneg :
          0 ≤ ((((2 * k + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) ^
            (((2 * k + 1 : ℕ) : ℝ) / 2) : ℝ) := by positivity
      have hfactorialNonneg : (0 : ℝ) ≤ k.factorial := by positivity
      have hsq :
          ((((2 * k + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) ^
              (((2 * k + 1 : ℕ) : ℝ) / 2) : ℝ) ^ 2 ≤
            (k.factorial : ℝ) ^ 2 := by
        have hs := Stirling.le_factorial_stirling k
        have hs' :
            Real.sqrt (2 * Real.pi * k) *
                (((k : ℝ) / Real.exp 1) ^ k : ℝ) ≤
              (k.factorial : ℝ) := by simpa using hs
        have hsquare := pow_le_pow_left₀ (by positivity :
            0 ≤ Real.sqrt (2 * Real.pi * k) *
              (((k : ℝ) / Real.exp 1) ^ k : ℝ)) hs' 2
        refine ?_
        calc
          ((((2 * k + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) ^
              (((2 * k + 1 : ℕ) : ℝ) / 2) : ℝ) ^ 2 =
              (((2 * k + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) ^
                ((2 * k + 1 : ℕ) : ℝ) := by
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_mul (by positivity)]
            congr 1
            push_cast
            ring
          _ ≤ (2 * Real.pi * k) *
                (((k : ℝ) / Real.exp 1) ^ (2 * k) : ℝ) := by
            have hbase :
                Real.exp 1 *
                    (((2 * k + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) ≤
                  2 * Real.pi * k := by
              have heq :
                  Real.exp 1 *
                      (((2 * k + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) =
                    ((2 * k + 1 : ℕ) : ℝ) / 2 := by
                field_simp
              rw [heq]
              have hkone : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
              have hcast :
                  ((2 * k + 1 : ℕ) : ℝ) / 2 = (k : ℝ) + 1 / 2 := by
                push_cast
                ring
              rw [hcast]
              have hpiMul : 3 * (k : ℝ) < Real.pi * k :=
                mul_lt_mul_of_pos_right Real.pi_gt_three (by positivity)
              nlinarith
            have hratio :
                (((2 * k + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) /
                    ((k : ℝ) / Real.exp 1) =
                  1 + (((2 * k : ℕ) : ℝ))⁻¹ := by
              have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hkpos.ne'
              push_cast
              field_simp
            have hexp := Real.one_add_inv_pow_le_exp (n := 2 * k)
            have hratioNonneg :
                0 ≤ (((2 * k + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) /
                    ((k : ℝ) / Real.exp 1) := by positivity
            have hratioexp :
                ((((2 * k + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) /
                    ((k : ℝ) / Real.exp 1)) ^ (2 * k) ≤ Real.exp 1 :=
              hratio ▸ hexp
            have hkbasepos : 0 < (k : ℝ) / Real.exp 1 := by positivity
            rw [div_pow] at hratioexp
            have hpowa :=
              (div_le_iff₀ (pow_pos hkbasepos (2 * k))).mp hratioexp
            calc
              (((2 * k + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) ^
                  ((2 * k + 1 : ℕ) : ℝ) =
                  (((2 * k + 1 : ℕ) : ℝ) /
                      (2 * Real.exp 1)) ^ (2 * k + 1) := by
                exact Real.rpow_natCast _ (2 * k + 1)
              _ = (((2 * k + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) *
                    (((2 * k + 1 : ℕ) : ℝ) /
                      (2 * Real.exp 1)) ^ (2 * k) := by
                rw [pow_succ']
              _ ≤ (((2 * k + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) *
                    (Real.exp 1 *
                      (((k : ℝ) / Real.exp 1) ^ (2 * k))) := by
                exact mul_le_mul_of_nonneg_left hpowa (by positivity)
              _ = (Real.exp 1 *
                    (((2 * k + 1 : ℕ) : ℝ) / (2 * Real.exp 1))) *
                    (((k : ℝ) / Real.exp 1) ^ (2 * k)) := by ring
              _ ≤ (2 * Real.pi * k) *
                    (((k : ℝ) / Real.exp 1) ^ (2 * k)) := by
                exact mul_le_mul_of_nonneg_right hbase (by positivity)
          _ = (Real.sqrt (2 * Real.pi * k) *
                (((k : ℝ) / Real.exp 1) ^ k : ℝ)) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (by positivity)]
            rw [← pow_mul]
            congr 2
            omega
          _ ≤ (k.factorial : ℝ) ^ 2 := hsquare
      have htofact :
          ((((2 * k + 1 : ℕ) : ℝ) / (2 * Real.exp 1)) ^
              (((2 * k + 1 : ℕ) : ℝ) / 2) : ℝ) ≤
            (k.factorial : ℝ) := by
        nlinarith
      refine htofact.trans_lt ?_
      rw [← Real.Gamma_nat_eq_factorial k]
      have harg :
          (((2 * k + 1 : ℕ) : ℝ) / 2 + 1) =
            (k : ℝ) + 3 / 2 := by
        push_cast
        ring
      rw [harg]
      apply Real.Gamma_strictMonoOn_Ici
      · simp only [Set.mem_Ici]
        have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
        linarith
      · simp only [Set.mem_Ici]
        have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
        linarith
      · linarith

theorem gamma_half_nat_lower (m : ℕ) (hm : 0 < m) :
    (((m : ℝ) / (2 * Real.exp 1)) ^ ((m : ℝ) / 2) : ℝ) ≤
      Real.Gamma ((m : ℝ) / 2 + 1) :=
  (gamma_half_nat_lower_strict m hm).le

theorem euclideanUnitBallVolume_sq_le (m : ℕ) (hm : 0 < m) :
    euclideanUnitBallVolume m ^ (2 : ℕ) ≤
      ((2 * Real.pi * Real.exp 1) / (m : ℝ)) ^ m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let a : ℝ := (m : ℝ) / (2 * Real.exp 1)
  have ha : 0 < a := by dsimp [a]; positivity
  let g : ℝ := a ^ ((m : ℝ) / 2)
  have hg : 0 < g := by dsimp [g]; positivity
  have hGamma : g ≤ Real.Gamma ((m : ℝ) / 2 + 1) := by
    dsimp [g, a]
    exact gamma_half_nat_lower m hm
  have hdiv :
      Real.pi ^ ((m : ℝ) / 2) /
          Real.Gamma ((m : ℝ) / 2 + 1) ≤
        Real.pi ^ ((m : ℝ) / 2) / g :=
    div_le_div_of_nonneg_left (Real.rpow_nonneg Real.pi_pos.le _)
      hg hGamma
  have hsq := pow_le_pow_left₀
    (div_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
      (Real.Gamma_pos_of_pos (by positivity)).le)
    hdiv 2
  unfold euclideanUnitBallVolume
  refine hsq.trans_eq ?_
  dsimp [g, a]
  rw [← Real.div_rpow Real.pi_pos.le (by positivity)
    ((m : ℝ) / 2)]
  have hbase :
      Real.pi / ((m : ℝ) / (2 * Real.exp 1)) =
        (2 * Real.pi * Real.exp 1) / (m : ℝ) := by
    field_simp
  rw [hbase]
  let b : ℝ := (2 * Real.pi * Real.exp 1) / (m : ℝ)
  change (b ^ ((m : ℝ) / 2)) ^ (2 : ℕ) = b ^ m
  calc
    (b ^ ((m : ℝ) / 2)) ^ (2 : ℕ) =
        (b ^ ((m : ℝ) / 2)) ^ (2 : ℝ) := by
      exact (Real.rpow_two _).symm
    _ = b ^ (((m : ℝ) / 2) * 2) := by
      rw [Real.rpow_mul (by dsimp [b]; positivity)]
    _ = b ^ (m : ℝ) := by
      congr 1
      ring
    _ = b ^ m := Real.rpow_natCast b m

/-- The strict version needed for the root-discriminant bounds in v15. -/
theorem euclideanUnitBallVolume_sq_lt (m : ℕ) (hm : 0 < m) :
    euclideanUnitBallVolume m ^ (2 : ℕ) <
      ((2 * Real.pi * Real.exp 1) / (m : ℝ)) ^ m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let a : ℝ := (m : ℝ) / (2 * Real.exp 1)
  have ha : 0 < a := by dsimp [a]; positivity
  let g : ℝ := a ^ ((m : ℝ) / 2)
  have hg : 0 < g := by dsimp [g]; positivity
  have hGamma : g < Real.Gamma ((m : ℝ) / 2 + 1) := by
    dsimp [g, a]
    exact gamma_half_nat_lower_strict m hm
  have hdiv :
      Real.pi ^ ((m : ℝ) / 2) /
          Real.Gamma ((m : ℝ) / 2 + 1) <
        Real.pi ^ ((m : ℝ) / 2) / g :=
    div_lt_div_of_pos_left (Real.rpow_pos_of_pos Real.pi_pos _)
      hg hGamma
  have hsq := pow_lt_pow_left₀ hdiv
    (div_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
      (Real.Gamma_pos_of_pos (by positivity)).le)
    (by norm_num : (2 : ℕ) ≠ 0)
  unfold euclideanUnitBallVolume
  refine hsq.trans_eq ?_
  dsimp [g, a]
  rw [← Real.div_rpow Real.pi_pos.le (by positivity)
    ((m : ℝ) / 2)]
  have hbase :
      Real.pi / ((m : ℝ) / (2 * Real.exp 1)) =
        (2 * Real.pi * Real.exp 1) / (m : ℝ) := by
    field_simp
  rw [hbase]
  let b : ℝ := (2 * Real.pi * Real.exp 1) / (m : ℝ)
  change (b ^ ((m : ℝ) / 2)) ^ (2 : ℕ) = b ^ m
  calc
    (b ^ ((m : ℝ) / 2)) ^ (2 : ℕ) =
        (b ^ ((m : ℝ) / 2)) ^ (2 : ℝ) := by
      exact (Real.rpow_two _).symm
    _ = b ^ (((m : ℝ) / 2) * 2) := by
      rw [Real.rpow_mul (by dsimp [b]; positivity)]
    _ = b ^ (m : ℝ) := by
      congr 1
      ring
    _ = b ^ m := Real.rpow_natCast b m

theorem factorial_ratio_sq_lt (d : ℕ) (hd : 0 < d) :
    (d.factorial : ℝ) ^ (2 : ℕ) / (d : ℝ) ^ (2 * d) <
      (2 * Real.exp 1 ^ (2 : ℕ) * d) /
        Real.exp 1 ^ (2 * d) := by
  have hfac := factorial_upper_stirling d hd
  have hfacNonneg :
      0 ≤ Real.exp 1 * Real.sqrt (2 * d) *
        (((d : ℝ) / Real.exp 1) ^ d : ℝ) := by positivity
  have hsq := pow_lt_pow_left₀ hfac
    (by positivity : (0 : ℝ) ≤ d.factorial) (by norm_num : (2 : ℕ) ≠ 0)
  have hden : 0 < (d : ℝ) ^ (2 * d) := by positivity
  apply (div_lt_iff₀ hden).2
  calc
    (d.factorial : ℝ) ^ (2 : ℕ) <
        (Real.exp 1 * Real.sqrt (2 * d) *
          (((d : ℝ) / Real.exp 1) ^ d : ℝ)) ^ (2 : ℕ) := hsq
    _ = ((2 * Real.exp 1 ^ (2 : ℕ) * d) /
          Real.exp 1 ^ (2 * d)) * (d : ℝ) ^ (2 * d) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      simp only [div_pow, pow_mul]
      field_simp
      ring

def coarseTraceVolumeBound (t : ℝ) (n d : ℕ) : ℝ :=
  ((2 * Real.pi * Real.exp 1) / ((n : ℝ) * d)) ^ (n * d) *
    t ^ (n * d) *
      (((2 * Real.exp 1 ^ (2 : ℕ) * d) /
        Real.exp 1 ^ (2 * d)) ^ n)

theorem minkowskiTraceVolumeBound_lt_coarse
    (t : ℝ) (n d : ℕ) (ht : 0 < t) (hn : 0 < n) (hd : 0 < d) :
    minkowskiTraceVolumeBound t n d < coarseTraceVolumeBound t n d := by
  have hm : 0 < n * d := Nat.mul_pos hn hd
  have hU :
      euclideanUnitBallVolume (n * d) ^ (2 : ℕ) ≤
        ((2 * Real.pi * Real.exp 1) / ((n : ℝ) * d)) ^ (n * d) := by
    simpa only [Nat.cast_mul] using
      euclideanUnitBallVolume_sq_le (n * d) hm
  have hR := factorial_ratio_sq_lt d hd
  have hRpow := pow_lt_pow_left₀ hR (by positivity :
      0 ≤ (d.factorial : ℝ) ^ (2 : ℕ) / (d : ℝ) ^ (2 * d)) hn.ne'
  have hinv :
      (((d : ℝ) ^ (2 * d) / (d.factorial : ℝ) ^ (2 : ℕ)) ^ n)⁻¹ =
        (((d.factorial : ℝ) ^ (2 : ℕ) / (d : ℝ) ^ (2 * d)) ^ n) := by
    rw [div_pow, inv_div, ← div_pow]
  have hexact :
      minkowskiTraceVolumeBound t n d =
        euclideanUnitBallVolume (n * d) ^ (2 : ℕ) * t ^ (n * d) *
          (((d.factorial : ℝ) ^ (2 : ℕ) /
            (d : ℝ) ^ (2 * d)) ^ n) := by
    unfold minkowskiTraceVolumeBound
      totallyRealMinkowskiDiscriminantLowerBound euclideanUnitBallVolume
    conv_lhs => rw [div_eq_mul_inv]
    rw [hinv]
  rw [hexact]
  unfold coarseTraceVolumeBound
  calc
    euclideanUnitBallVolume (n * d) ^ (2 : ℕ) * t ^ (n * d) *
        ((d.factorial : ℝ) ^ (2 : ℕ) / (d : ℝ) ^ (2 * d)) ^ n ≤
      ((2 * Real.pi * Real.exp 1) / ((n : ℝ) * d)) ^ (n * d) *
        t ^ (n * d) *
          ((d.factorial : ℝ) ^ (2 : ℕ) /
            (d : ℝ) ^ (2 * d)) ^ n := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hU (pow_nonneg ht.le (n * d)))
        (by positivity)
    _ < ((2 * Real.pi * Real.exp 1) / ((n : ℝ) * d)) ^ (n * d) *
        t ^ (n * d) *
          ((2 * Real.exp 1 ^ (2 : ℕ) * d) /
            Real.exp 1 ^ (2 * d)) ^ n := by
      exact mul_lt_mul_of_pos_left hRpow
        (mul_pos (pow_pos (by positivity) (n * d))
          (pow_pos ht (n * d)))

def gCoarseClassicReal (x y : ℝ) : ℝ :=
  Real.log (2 * Real.exp 1 ^ (2 : ℕ) * y) +
    y * Real.log (2 * Real.pi / (Real.exp 1 * x))

def gCoarseIntegralReal (x y : ℝ) : ℝ :=
  y * Real.log 2 + gCoarseClassicReal x y

def gCoarseClassicNat (n d : ℕ) : ℝ :=
  gCoarseClassicReal n d

def gCoarseIntegralNat (n d : ℕ) : ℝ :=
  gCoarseIntegralReal n d

def coarseTraceVolumeExponent (t : ℝ) (n d : ℕ) : ℝ :=
  (n : ℝ) * gCoarseClassicNat n d +
    (n : ℝ) * (d : ℝ) * Real.log (t / d)

theorem coarseTraceVolumeExponent_eq_log_product
    (t : ℝ) (n d : ℕ) (ht : 0 < t) (hn : 0 < n) (hd : 0 < d) :
    coarseTraceVolumeExponent t n d =
      (n * d : ℕ) * Real.log
        ((2 * Real.pi * Real.exp 1) / ((n : ℝ) * d)) +
      (n * d : ℕ) * Real.log t +
      (n : ℕ) * Real.log
        ((2 * Real.exp 1 ^ (2 : ℕ) * d) /
          Real.exp 1 ^ (2 * d)) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hA :
      Real.log ((2 * Real.pi * Real.exp 1) / ((n : ℝ) * d)) =
        Real.log (2 * Real.pi) + 1 - Real.log n - Real.log d := by
    rw [Real.log_div (mul_ne_zero h2pi (Real.exp_ne_zero 1))
      (mul_ne_zero hnR hdR),
      Real.log_mul h2pi (Real.exp_ne_zero 1),
      Real.log_mul hnR hdR, Real.log_exp]
    ring
  have hB :
      Real.log (2 * Real.pi / (Real.exp 1 * (n : ℝ))) =
        Real.log (2 * Real.pi) - 1 - Real.log n := by
    rw [Real.log_div h2pi (mul_ne_zero (Real.exp_ne_zero 1) hnR),
      Real.log_mul (Real.exp_ne_zero 1) hnR, Real.log_exp]
    ring
  have hTD : Real.log (t / (d : ℝ)) = Real.log t - Real.log d := by
    exact Real.log_div ht.ne' hdR
  have hC :
      Real.log ((2 * Real.exp 1 ^ (2 : ℕ) * d) /
          Real.exp 1 ^ (2 * d)) =
        Real.log (2 * Real.exp 1 ^ (2 : ℕ) * d) -
          (2 * d : ℕ) := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_pow, Real.log_exp]
    norm_num
  unfold coarseTraceVolumeExponent gCoarseClassicNat gCoarseClassicReal
  simp only [Nat.cast_mul]
  rw [hA, hB, hTD, hC]
  push_cast
  ring

theorem exp_coarseTraceVolumeExponent_eq
    (t : ℝ) (n d : ℕ) (ht : 0 < t) (hn : 0 < n) (hd : 0 < d) :
    Real.exp (coarseTraceVolumeExponent t n d) =
      coarseTraceVolumeBound t n d := by
  rw [coarseTraceVolumeExponent_eq_log_product t n d ht hn hd]
  have hA : 0 <
      (2 * Real.pi * Real.exp 1) / ((n : ℝ) * d) := by positivity
  have hC : 0 <
      (2 * Real.exp 1 ^ (2 : ℕ) * d) /
        Real.exp 1 ^ (2 * d) := by positivity
  rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul,
    Real.exp_log hA, Real.exp_nat_mul, Real.exp_log ht,
    Real.exp_nat_mul, Real.exp_log hC]
  rfl

/-- The exponent for the form scaled by two in the merely integral branch. -/
def coarseIntegralTraceVolumeExponent (t : ℝ) (n d : ℕ) : ℝ :=
  coarseTraceVolumeExponent t n d +
    (n * d : ℕ) * Real.log 2

/-- Scaling the radius parameter by two adds the expected determinant term. -/
theorem coarseTraceVolumeExponent_two_mul
    (t : ℝ) (n d : ℕ) (ht : 0 < t) (hd : 0 < d) :
    coarseTraceVolumeExponent (2 * t) n d =
      coarseIntegralTraceVolumeExponent t n d := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hratio : 0 < t / (d : ℝ) := by positivity
  have hlog :
      Real.log ((2 * t) / (d : ℝ)) =
        Real.log 2 + Real.log (t / (d : ℝ)) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hratio.ne']
    congr 1
    field_simp
  unfold coarseIntegralTraceVolumeExponent coarseTraceVolumeExponent
  rw [hlog]
  simp only [Nat.cast_mul]
  ring

/-- The coarse exponent increases when `t` is replaced by the degree. -/
theorem coarseTraceVolumeExponent_le_degree
    (t : ℝ) (n d : ℕ) (ht : 0 < t) (htd : t ≤ d) :
    coarseTraceVolumeExponent t n d ≤
      (n : ℝ) * gCoarseClassicNat n d := by
  have hdpos : (0 : ℝ) < d := ht.trans_le htd
  unfold coarseTraceVolumeExponent
  exact add_le_of_nonpos_right
    (mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg d))
      (Real.log_nonpos (by positivity)
        ((div_le_one hdpos).2 htd)))

/-- The same comparison after the factor-two scaling. -/
theorem coarseIntegralTraceVolumeExponent_le_degree
    (t : ℝ) (n d : ℕ) (ht : 0 < t) (htd : t ≤ d) :
    coarseIntegralTraceVolumeExponent t n d ≤
      (n : ℝ) * gCoarseIntegralNat n d := by
  calc
    coarseIntegralTraceVolumeExponent t n d =
        coarseTraceVolumeExponent t n d +
          (n * d : ℕ) * Real.log 2 := rfl
    _ ≤ (n : ℝ) * gCoarseClassicNat n d +
          (n * d : ℕ) * Real.log 2 :=
      add_le_add (coarseTraceVolumeExponent_le_degree t n d ht htd)
        (le_refl _)
    _ = (n : ℝ) * gCoarseIntegralNat n d := by
      unfold gCoarseIntegralNat gCoarseIntegralReal gCoarseClassicNat
      simp only [Nat.cast_mul]
      ring

theorem tendsto_gCoarseClassicReal_div_degree (x : ℝ) (_hx : 0 < x) :
    Filter.Tendsto (fun y : ℝ ↦ gCoarseClassicReal x y / y)
      Filter.atTop
      (nhds (Real.log (2 * Real.pi / (Real.exp 1 * x)))) := by
  have hC : 0 < 2 * Real.exp 1 ^ (2 : ℕ) := by positivity
  have hfirst := tendsto_log_affine_div_atTop
    (2 * Real.exp 1 ^ (2 : ℕ)) 0 hC
  let k : ℝ := Real.log (2 * Real.pi / (Real.exp 1 * x))
  have hk : Filter.Tendsto (fun _ : ℝ ↦ k) Filter.atTop (nhds k) :=
    tendsto_const_nhds
  have hsum : Filter.Tendsto
      (fun y : ℝ ↦
        Real.log (2 * Real.exp 1 ^ (2 : ℕ) * (y + 0)) / y + k)
      Filter.atTop (nhds k) := by
    simpa using hfirst.add hk
  apply hsum.congr'
  filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with y hy
  dsimp only [gCoarseClassicReal, k]
  field_simp [hy]
  ring

theorem gCoarseClassicNat_degree_tail (n : ℕ) (hn : 3 ≤ n) :
    Filter.Tendsto (gCoarseClassicNat n) Filter.atTop Filter.atBot := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hreal : Filter.Tendsto
      (fun y : ℝ ↦ gCoarseClassicReal n y)
      Filter.atTop Filter.atBot :=
    tendsto_atBot_of_div_tendsto_neg
      (classic_degree_coefficient_neg (by exact_mod_cast hn))
      (tendsto_gCoarseClassicReal_div_degree n hnpos)
  change Filter.Tendsto
    (fun d : ℕ ↦ gCoarseClassicReal (n : ℝ) (d : ℝ))
    Filter.atTop Filter.atBot
  exact hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem tendsto_gCoarseIntegralReal_div_degree (x : ℝ) (hx : 0 < x) :
    Filter.Tendsto (fun y : ℝ ↦ gCoarseIntegralReal x y / y)
      Filter.atTop
      (nhds (Real.log 2 +
        Real.log (2 * Real.pi / (Real.exp 1 * x)))) := by
  have hclassic := tendsto_gCoarseClassicReal_div_degree x hx
  have htwo : Filter.Tendsto (fun _ : ℝ ↦ Real.log 2)
      Filter.atTop (nhds (Real.log 2)) := tendsto_const_nhds
  have hsum := htwo.add hclassic
  apply hsum.congr'
  filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with y hy
  dsimp only [gCoarseIntegralReal]
  field_simp [hy]

theorem gCoarseIntegralNat_degree_tail (n : ℕ) (hn : 5 ≤ n) :
    Filter.Tendsto (gCoarseIntegralNat n) Filter.atTop Filter.atBot := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hreal : Filter.Tendsto
      (fun y : ℝ ↦ gCoarseIntegralReal n y)
      Filter.atTop Filter.atBot :=
    tendsto_atBot_of_div_tendsto_neg
      (integral_degree_coefficient_neg (by exact_mod_cast hn))
      (tendsto_gCoarseIntegralReal_div_degree n hnpos)
  change Filter.Tendsto
    (fun d : ℕ ↦ gCoarseIntegralReal (n : ℝ) (d : ℝ))
    Filter.atTop Filter.atBot
  exact hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem tendsto_gCoarseClassicReal_rank_atBot (d : ℝ) (hd : 0 < d) :
    Filter.Tendsto (fun x : ℝ ↦ gCoarseClassicReal x d)
      Filter.atTop Filter.atBot := by
  have hneglog : Filter.Tendsto (fun x : ℝ ↦ (-d) * Real.log x)
      Filter.atTop Filter.atBot :=
    Real.tendsto_log_atTop.const_mul_atTop_of_neg (by linarith)
  let c : ℝ := Real.log (2 * Real.exp 1 ^ (2 : ℕ) * d) +
    d * Real.log (2 * Real.pi / Real.exp 1)
  have hc : Filter.Tendsto (fun _ : ℝ ↦ c) Filter.atTop (nhds c) :=
    tendsto_const_nhds
  have hsum : Filter.Tendsto
      (fun x : ℝ ↦ c + (-d) * Real.log x)
      Filter.atTop Filter.atBot := hc.add_atBot hneglog
  apply hsum.congr'
  filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with x hx
  dsimp only [gCoarseClassicReal, c]
  rw [Real.log_div (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (mul_ne_zero (Real.exp_ne_zero 1) hx),
    Real.log_mul (Real.exp_ne_zero 1) hx,
    Real.log_div (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (Real.exp_ne_zero 1)]
  ring

theorem gCoarseClassicNat_rank_tail (d : ℕ) (hd : 1 ≤ d) :
    Filter.Tendsto (fun n ↦ gCoarseClassicNat n d)
      Filter.atTop Filter.atBot := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hreal := tendsto_gCoarseClassicReal_rank_atBot (d : ℝ) hdpos
  change Filter.Tendsto
    (fun n : ℕ ↦ gCoarseClassicReal (n : ℝ) (d : ℝ))
    Filter.atTop Filter.atBot
  exact hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem gCoarseIntegralNat_rank_tail (d : ℕ) (hd : 1 ≤ d) :
    Filter.Tendsto (fun n ↦ gCoarseIntegralNat n d)
      Filter.atTop Filter.atBot := by
  have hclassic := gCoarseClassicNat_rank_tail d hd
  have hconst : Filter.Tendsto (fun _ : ℕ ↦ (d : ℝ) * Real.log 2)
      Filter.atTop (nhds ((d : ℝ) * Real.log 2)) := tendsto_const_nhds
  have hsum := hconst.add_atBot hclassic
  apply hsum.congr'
  filter_upwards with n
  rfl

def gCoarseClassicEnvelopeNat (d : ℕ) : ℝ :=
  gCoarseClassicNat 3 d

def gCoarseIntegralEnvelopeNat (d : ℕ) : ℝ :=
  gCoarseIntegralNat 5 d

theorem gCoarseClassicNat_le_envelope {n d : ℕ}
    (hn : 3 ≤ n) :
    gCoarseClassicNat n d ≤ gCoarseClassicEnvelopeNat d := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : Real.exp 1 * 3 ≤ Real.exp 1 * (n : ℝ) :=
    mul_le_mul_of_nonneg_left hnR (Real.exp_pos 1).le
  have hfrac :
      2 * Real.pi / (Real.exp 1 * (n : ℝ)) ≤
        2 * Real.pi / (Real.exp 1 * 3) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have hlog := Real.log_le_log (by positivity) hfrac
  change Real.log (2 * Real.exp 1 ^ (2 : ℕ) * (d : ℝ)) +
      (d : ℝ) * Real.log (2 * Real.pi / (Real.exp 1 * (n : ℝ))) ≤
    Real.log (2 * Real.exp 1 ^ (2 : ℕ) * (d : ℝ)) +
      (d : ℝ) * Real.log (2 * Real.pi / (Real.exp 1 * 3))
  gcongr

theorem gCoarseIntegralNat_le_envelope {n d : ℕ}
    (hn : 5 ≤ n) :
    gCoarseIntegralNat n d ≤ gCoarseIntegralEnvelopeNat d := by
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : Real.exp 1 * 5 ≤ Real.exp 1 * (n : ℝ) :=
    mul_le_mul_of_nonneg_left hnR (Real.exp_pos 1).le
  have hfrac :
      2 * Real.pi / (Real.exp 1 * (n : ℝ)) ≤
        2 * Real.pi / (Real.exp 1 * 5) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have hlog := Real.log_le_log (by positivity) hfrac
  change (d : ℝ) * Real.log 2 +
      (Real.log (2 * Real.exp 1 ^ (2 : ℕ) * (d : ℝ)) +
        (d : ℝ) * Real.log (2 * Real.pi / (Real.exp 1 * (n : ℝ)))) ≤
    (d : ℝ) * Real.log 2 +
      (Real.log (2 * Real.exp 1 ^ (2 : ℕ) * (d : ℝ)) +
        (d : ℝ) * Real.log (2 * Real.pi / (Real.exp 1 * 5)))
  gcongr

theorem gCoarseClassicEnvelopeNat_tail :
    Filter.Tendsto gCoarseClassicEnvelopeNat Filter.atTop Filter.atBot := by
  exact gCoarseClassicNat_degree_tail 3 (by norm_num)

theorem gCoarseIntegralEnvelopeNat_tail :
    Filter.Tendsto gCoarseIntegralEnvelopeNat Filter.atTop Filter.atBot := by
  exact gCoarseIntegralNat_degree_tail 5 (by norm_num)

end TraceEuclidean
