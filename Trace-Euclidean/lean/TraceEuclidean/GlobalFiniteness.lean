import TraceEuclidean.FinitenessEndpoints
import TraceEuclidean.VolumeIdeals
import TraceEuclidean.CoveringVolume
import TraceEuclidean.GeometricBounds
import TraceEuclidean.DiscriminantBounds
import TraceEuclidean.DirectFixedFieldFiniteness
import TraceEuclidean.PseudoBasisDeterminant
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
The eight finiteness conclusions specialized to the actual quotient of
field--lattice presentations.  The projective pseudobasis determinant gives
the unconditional discriminant bounds, and direct finite reduction codes
give fixed-field, fixed-rank finiteness.
-/

namespace TraceEuclidean

open scoped NumberField

noncomputable section

namespace GlobalLatticeClass

/-- The paper's classic-integral strict trace-Euclidean predicate on classes. -/
def IsClassicTraceEuclidean (t : ℝ) (c : GlobalLatticeClass) : Prop :=
  c.IsClassicIntegral ∧ c.IsTraceEuclidean t

/--
The paper's integral strict trace-Euclidean predicate on classes.  Integrality,
positive definiteness, and fullness are fields of every presentation.
-/
def IsIntegralTraceEuclidean (t : ℝ) (c : GlobalLatticeClass) : Prop :=
  c.IsTraceEuclidean t

end GlobalLatticeClass

/-- The exact discriminant bound in the classic-integral branch. -/
def classicDiscriminantRealBound (n d : ℕ) : ℝ :=
  euclideanUnitBallVolume (n * d) ^ ((2 : ℝ) / n) * (d : ℝ) ^ d

/-- The exact discriminant bound in the integral branch. -/
def integralDiscriminantRealBound (n d : ℕ) : ℝ :=
  euclideanUnitBallVolume (n * d) ^ ((2 : ℝ) / n) * (2 * d : ℝ) ^ d

/-- The discriminant bound before replacing `t` by the field degree. -/
def classicTraceDiscriminantRealBound (t : ℝ) (n d : ℕ) : ℝ :=
  euclideanUnitBallVolume (n * d) ^ ((2 : ℝ) / n) * t ^ d

/-- The integral discriminant bound before replacing `t` by the degree. -/
def integralTraceDiscriminantRealBound (t : ℝ) (n d : ℕ) : ℝ :=
  euclideanUnitBallVolume (n * d) ^ ((2 : ℝ) / n) * (2 * t) ^ d

/-- The logarithmic correction that changes the `d`-bound to the `t`-bound. -/
def traceScaleCorrection (t : ℝ) (n d : ℕ) : ℝ :=
  (n : ℝ) * (d : ℝ) * Real.log (t / d)

/-- The exact logarithm of the classic volume bound `G_t(n,d)`. -/
def classicTraceVolumeExponent (t : ℝ) (n d : ℕ) : ℝ :=
  (n : ℝ) * gClassicNat n d + traceScaleCorrection t n d

/-- The exact logarithm of the scale-two integral volume bound. -/
def integralTraceVolumeExponent (t : ℝ) (n d : ℕ) : ℝ :=
  (n : ℝ) * gIntegralNat n d + traceScaleCorrection t n d

/-- The manuscript's explicit quantity `G_t(n,d)` from equation (3.8). -/
def paperTraceVolumeBound (t : ℝ) (n d : ℕ) : ℝ :=
  (2 * Real.pi * ((d : ℝ) + traceAnalyticB)) ^ n /
      (Real.pi * ((n : ℝ) * d + 1 / 3)) *
    ((2 * Real.pi * t) /
      (Real.exp 1 * (n : ℝ) * d)) ^ (n * d)

/-- Expand the logarithmic classic exponent into the paper's three factors. -/
theorem classicTraceVolumeExponent_eq_log_form
    (t : ℝ) (n d : ℕ) (ht : 0 < t) (hn : 0 < n) (hd : 0 < d) :
    classicTraceVolumeExponent t n d =
      (n : ℝ) * Real.log (2 * Real.pi * ((d : ℝ) + traceAnalyticB)) -
        Real.log (Real.pi * ((n : ℝ) * d + 1 / 3)) +
          (n * d : ℕ) * Real.log
            ((2 * Real.pi * t) / (Real.exp 1 * (n : ℝ) * d)) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hbase : 0 < 2 * Real.pi / (Real.exp 1 * (n : ℝ)) := by positivity
  have hratio : 0 < t / (d : ℝ) := div_pos ht (by exact_mod_cast hd)
  have hlog :
      Real.log ((2 * Real.pi * t) / (Real.exp 1 * (n : ℝ) * d)) =
        Real.log (2 * Real.pi / (Real.exp 1 * (n : ℝ))) +
          Real.log (t / (d : ℝ)) := by
    rw [← Real.log_mul hbase.ne' hratio.ne']
    congr 1
    field_simp [hnR, hdR, Real.exp_ne_zero, Real.pi_ne_zero]
  rw [hlog]
  unfold classicTraceVolumeExponent traceScaleCorrection gClassicNat gClassicReal
  simp only [Nat.cast_mul]
  field_simp [hnR]
  ring

/-- The formal logarithmic bound is exactly the paper's `G_t(n,d)`. -/
theorem exp_classicTraceVolumeExponent_eq_paperTraceVolumeBound
    (t : ℝ) (n d : ℕ) (ht : 0 < t) (hn : 0 < n) (hd : 0 < d) :
    Real.exp (classicTraceVolumeExponent t n d) =
      paperTraceVolumeBound t n d := by
  rw [classicTraceVolumeExponent_eq_log_form t n d ht hn hd]
  have hA : 0 < 2 * Real.pi * ((d : ℝ) + traceAnalyticB) := by
    unfold traceAnalyticB
    have he : 0 < Real.exp 1 ^ 2 := sq_pos_of_pos (Real.exp_pos 1)
    have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    have hfrac : 0 < Real.exp 1 ^ 2 / (2 * Real.pi) := div_pos he hpi
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    exact mul_pos hpi (by linarith)
  have hB : 0 < Real.pi * ((n : ℝ) * d + 1 / 3) := by positivity
  have hD : 0 < (2 * Real.pi * t) / (Real.exp 1 * (n : ℝ) * d) := by
    positivity
  unfold paperTraceVolumeBound
  rw [Real.exp_add, Real.exp_sub, Real.exp_nat_mul,
    Real.exp_log hA, Real.exp_log hB, Real.exp_nat_mul,
    Real.exp_log hD]

/-- The integral exponent differs by the determinant scaling factor. -/
theorem integralTraceVolumeExponent_eq (t : ℝ) (n d : ℕ) :
    integralTraceVolumeExponent t n d =
      classicTraceVolumeExponent t n d +
        (n * d : ℕ) * Real.log 2 := by
  unfold integralTraceVolumeExponent classicTraceVolumeExponent
  unfold gIntegralNat gIntegralReal gClassicNat traceScaleCorrection
  simp only [Nat.cast_mul]
  ring

/-- The scale-two integral bound is exactly `2^(nd) G_t(n,d)`. -/
theorem exp_integralTraceVolumeExponent_eq
    (t : ℝ) (n d : ℕ) (ht : 0 < t) (hn : 0 < n) (hd : 0 < d) :
    Real.exp (integralTraceVolumeExponent t n d) =
      2 ^ (n * d) * paperTraceVolumeBound t n d := by
  rw [integralTraceVolumeExponent_eq, Real.exp_add,
    Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2),
    exp_classicTraceVolumeExponent_eq_paperTraceVolumeBound t n d ht hn hd]
  ring

namespace GlobalFiniteness

/-- The selected representative has the class-level trace-Euclidean
property. -/
theorem representative_isTraceEuclidean
    {c : GlobalLatticeClass} {t : ℝ}
    (hc : c.IsTraceEuclidean t) :
    c.representative.IsTraceEuclidean t := by
  rw [← GlobalLatticeClass.isTraceEuclidean_mk c.representative,
    c.mk_representative]
  exact hc

/-- The projective pseudobasis determinant lower bound and the covering
bound give the classic Gram inequality without an auxiliary input. -/
theorem classic_discriminant_pow_le_trace
    (t : ℝ) (n d : ℕ) (c : GlobalLatticeClass)
    (ht : 0 < t)
    (hc : c.IsClassicTraceEuclidean t ∧ c.rank = n ∧ c.degree = d) :
    ((|c.fieldCode.discriminant| : ℤ) : ℝ) ^ n ≤
      euclideanUnitBallVolume (n * d) ^ (2 : ℕ) * t ^ (n * d) := by
  have hclassic : c.representative.IsClassicIntegral := by
    rw [← GlobalLatticeClass.isClassicIntegral_mk c.representative,
      c.mk_representative]
    exact hc.1.1
  have hE : c.representative.IsTraceEuclidean t :=
    representative_isTraceEuclidean hc.1.2
  have h :=
    (c.representative.discriminant_pow_le_euclideanCovolume_sq_of_classic
      hclassic).trans
      (c.representative.euclideanCovolume_sq_le_of_traceEuclidean ht hE)
  simpa only [GlobalLatticeClass.fieldCode, NumberFieldCode.discriminant,
    GlobalLatticeClass.representative_rank,
    GlobalLatticeClass.representative_degree, hc.2.1, hc.2.2] using h

/-- The scale-two pseudobasis determinant lower bound and covering bound give
the integral Gram inequality. -/
theorem integral_discriminant_pow_le_trace
    (t : ℝ) (n d : ℕ) (c : GlobalLatticeClass)
    (ht : 0 < t)
    (hc : c.IsIntegralTraceEuclidean t ∧ c.rank = n ∧ c.degree = d) :
    ((|c.fieldCode.discriminant| : ℤ) : ℝ) ^ n ≤
      euclideanUnitBallVolume (n * d) ^ (2 : ℕ) *
        (2 * t) ^ (n * d) := by
  have hE : c.representative.IsTraceEuclidean t :=
    representative_isTraceEuclidean hc.1
  have hlower :=
    c.representative.discriminant_pow_le_two_pow_mul_euclideanCovolume_sq
  have hupper :=
    c.representative.euclideanCovolume_sq_le_of_traceEuclidean ht hE
  have h :
      ((|NumberField.discr c.representative.field.1| : ℤ) : ℝ) ^
          c.representative.rank ≤
        euclideanUnitBallVolume
              (c.representative.rank * c.representative.degree) ^ (2 : ℕ) *
          (2 * t) ^
            (c.representative.rank * c.representative.degree) := by
    calc
      ((|NumberField.discr c.representative.field.1| : ℤ) : ℝ) ^
          c.representative.rank ≤
          (2 : ℝ) ^
              (c.representative.rank * c.representative.degree) *
            ZLattice.covolume
              c.representative.euclideanIntegralLattice ^ (2 : ℕ) :=
        hlower
      _ ≤ (2 : ℝ) ^
              (c.representative.rank * c.representative.degree) *
            (euclideanUnitBallVolume
                (c.representative.rank * c.representative.degree) ^ (2 : ℕ) *
              t ^ (c.representative.rank * c.representative.degree)) :=
        mul_le_mul_of_nonneg_left hupper (by positivity)
      _ = euclideanUnitBallVolume
              (c.representative.rank * c.representative.degree) ^ (2 : ℕ) *
            (2 * t) ^
              (c.representative.rank * c.representative.degree) := by
        rw [mul_pow]
        ring
  simpa only [GlobalLatticeClass.fieldCode, NumberFieldCode.discriminant,
    GlobalLatticeClass.representative_rank,
    GlobalLatticeClass.representative_degree, hc.2.1, hc.2.2] using h

/-- The exact classic discriminant estimate. -/
theorem classic_discriminant_le_trace
    (t : ℝ) (n d : ℕ) (c : GlobalLatticeClass)
    (ht : 0 < t) (_htd : t ≤ d)
    (hc : c.IsClassicTraceEuclidean t ∧ c.rank = n ∧ c.degree = d) :
    ((|c.fieldCode.discriminant| : ℤ) : ℝ) ≤
      classicTraceDiscriminantRealBound t n d := by
  have hn : 0 < n := by
    rw [← hc.2.1]
    exact c.rank_pos
  unfold classicTraceDiscriminantRealBound
  apply discriminant_le_of_gram_volume_bound
    ((|c.fieldCode.discriminant| : ℤ) : ℝ)
    (euclideanUnitBallVolume (n * d)) t 1 n d
    (by positivity) (euclideanUnitBallVolume_pos _) ht hn (le_refl 1)
  simpa using classic_discriminant_pow_le_trace t n d c ht hc

/-- The exact integral discriminant estimate. -/
theorem integral_discriminant_le_trace
    (t : ℝ) (n d : ℕ) (c : GlobalLatticeClass)
    (ht : 0 < t) (_htd : t ≤ d)
    (hc : c.IsIntegralTraceEuclidean t ∧ c.rank = n ∧ c.degree = d) :
    ((|c.fieldCode.discriminant| : ℤ) : ℝ) ≤
      integralTraceDiscriminantRealBound t n d := by
  have hn : 0 < n := by
    rw [← hc.2.1]
    exact c.rank_pos
  unfold integralTraceDiscriminantRealBound
  apply discriminant_le_of_gram_volume_bound
    ((|c.fieldCode.discriminant| : ℤ) : ℝ)
    (euclideanUnitBallVolume (n * d)) (2 * t) 1 n d
    (by positivity) (euclideanUnitBallVolume_pos _) (by positivity) hn
    (le_refl 1)
  simpa using integral_discriminant_pow_le_trace t n d c ht hc

/-- A natural-number ceiling of the paper's classic discriminant bound. -/
def classicDiscriminantBound (_t : ℝ) (n d : ℕ) : ℕ :=
  Nat.ceil (classicDiscriminantRealBound n d)

/-- A natural-number ceiling of the paper's integral discriminant bound. -/
def integralDiscriminantBound (_t : ℝ) (n d : ℕ) : ℕ :=
  Nat.ceil (integralDiscriminantRealBound n d)

/-- Replacing `t` by `d` enlarges the classic discriminant bound. -/
theorem classicTraceDiscriminantRealBound_le (t : ℝ) (n d : ℕ)
    (ht : 0 < t) (htd : t ≤ d) :
    classicTraceDiscriminantRealBound t n d ≤
      classicDiscriminantRealBound n d := by
  unfold classicTraceDiscriminantRealBound classicDiscriminantRealBound
  apply mul_le_mul_of_nonneg_left
  · exact pow_le_pow_left₀ ht.le htd d
  · exact Real.rpow_nonneg (euclideanUnitBallVolume_pos _).le _

/-- Replacing `t` by `d` enlarges the integral discriminant bound. -/
theorem integralTraceDiscriminantRealBound_le (t : ℝ) (n d : ℕ)
    (ht : 0 < t) (htd : t ≤ d) :
    integralTraceDiscriminantRealBound t n d ≤
      integralDiscriminantRealBound n d := by
  unfold integralTraceDiscriminantRealBound integralDiscriminantRealBound
  apply mul_le_mul_of_nonneg_left
  · apply pow_le_pow_left₀
    · positivity
    · exact mul_le_mul_of_nonneg_left htd (by norm_num)
  · exact Real.rpow_nonneg (euclideanUnitBallVolume_pos _).le _

/-- The classic real estimate gives the integer bound used by Hermite. -/
theorem classic_discriminant_le (t : ℝ) (n d : ℕ)
    (c : GlobalLatticeClass) (ht : 0 < t) (htd : t ≤ d)
    (hc : c.IsClassicTraceEuclidean t ∧ c.rank = n ∧ c.degree = d) :
    |c.fieldCode.discriminant| ≤ classicDiscriminantBound t n d := by
  have hreal :
      ((|c.fieldCode.discriminant| : ℤ) : ℝ) ≤
        (classicDiscriminantBound t n d : ℝ) :=
    ((classic_discriminant_le_trace t n d c ht htd hc).trans
      (classicTraceDiscriminantRealBound_le t n d ht htd)).trans
      (Nat.le_ceil _)
  exact_mod_cast hreal

/-- The integral real estimate gives the integer bound used by Hermite. -/
theorem integral_discriminant_le (t : ℝ) (n d : ℕ)
    (c : GlobalLatticeClass) (ht : 0 < t) (htd : t ≤ d)
    (hc : c.IsIntegralTraceEuclidean t ∧ c.rank = n ∧ c.degree = d) :
    |c.fieldCode.discriminant| ≤ integralDiscriminantBound t n d := by
  have hreal :
      ((|c.fieldCode.discriminant| : ℤ) : ℝ) ≤
        (integralDiscriminantBound t n d : ℝ) :=
    ((integral_discriminant_le_trace t n d c ht htd hc).trans
      (integralTraceDiscriminantRealBound_le t n d ht htd)).trans
      (Nat.le_ceil _)
  exact_mod_cast hreal

/-- The classic Gram inequality and Minkowski lower bound force the
intermediate volume bound to be at least one. -/
theorem one_le_minkowskiTraceVolumeBound_classic
    (t : ℝ) (n d : ℕ) (c : GlobalLatticeClass)
    (ht : 0 < t) (htd : t ≤ d)
    (hc : c.IsClassicTraceEuclidean t ∧ c.rank = n ∧ c.degree = d) :
    (1 : ℝ) ≤ minkowskiTraceVolumeBound t n d := by
  have hd : 0 < d := by
    have : (0 : ℝ) < d := ht.trans_le htd
    exact_mod_cast this
  have hApos := totallyRealMinkowskiDiscriminantLowerBound_pos hd
  have hdisc :
      totallyRealMinkowskiDiscriminantLowerBound d ≤
        ((|c.fieldCode.discriminant| : ℤ) : ℝ) := by
    simpa only [hc.2.2] using c.minkowski_discriminant_lower_bound
  have hraw := volume_le_div_of_gram_volume_bound
    ((|c.fieldCode.discriminant| : ℤ) : ℝ)
    (euclideanUnitBallVolume (n * d)) t 1 n d
    (hApos.trans_le hdisc)
    (by simpa using classic_discriminant_pow_le_trace t n d c ht hc)
  refine hraw.trans ?_
  unfold minkowskiTraceVolumeBound
  exact div_le_div_of_nonneg_left (by positivity)
    (pow_pos hApos n) (pow_le_pow_left₀ hApos.le hdisc n)

/-- The same lower bound after the scale-two reduction. -/
theorem one_le_minkowskiTraceVolumeBound_integral
    (t : ℝ) (n d : ℕ) (c : GlobalLatticeClass)
    (ht : 0 < t) (htd : t ≤ d)
    (hc : c.IsIntegralTraceEuclidean t ∧ c.rank = n ∧ c.degree = d) :
    (1 : ℝ) ≤ minkowskiTraceVolumeBound (2 * t) n d := by
  have hd : 0 < d := by
    have : (0 : ℝ) < d := ht.trans_le htd
    exact_mod_cast this
  have hApos := totallyRealMinkowskiDiscriminantLowerBound_pos hd
  have hdisc :
      totallyRealMinkowskiDiscriminantLowerBound d ≤
        ((|c.fieldCode.discriminant| : ℤ) : ℝ) := by
    simpa only [hc.2.2] using c.minkowski_discriminant_lower_bound
  have hraw := volume_le_div_of_gram_volume_bound
    ((|c.fieldCode.discriminant| : ℤ) : ℝ)
    (euclideanUnitBallVolume (n * d)) (2 * t) 1 n d
    (hApos.trans_le hdisc)
    (by simpa using integral_discriminant_pow_le_trace t n d c ht hc)
  refine hraw.trans ?_
  unfold minkowskiTraceVolumeBound
  exact div_le_div_of_nonneg_left (by positivity)
    (pow_pos hApos n) (pow_le_pow_left₀ hApos.le hdisc n)

/-- The classic analytic envelope is positive for every realized class. -/
theorem classic_positive (t : ℝ) (c : GlobalLatticeClass)
    (ht : 0 < t) (htd : t ≤ c.degree)
    (hc : c.IsClassicTraceEuclidean t) :
    0 < gCoarseClassicNat c.rank c.degree := by
  have hn : 0 < c.rank := c.rank_pos
  have hd : 0 < c.degree := by
    have : (0 : ℝ) < c.degree := ht.trans_le htd
    exact_mod_cast this
  have hone := one_le_minkowskiTraceVolumeBound_classic
    t c.rank c.degree c ht htd ⟨hc, rfl, rfl⟩
  have hlt : minkowskiTraceVolumeBound t c.rank c.degree <
      Real.exp (coarseTraceVolumeExponent t c.rank c.degree) := by
    rw [exp_coarseTraceVolumeExponent_eq t c.rank c.degree ht hn hd]
    exact minkowskiTraceVolumeBound_lt_coarse t c.rank c.degree ht hn hd
  have hexp : (1 : ℝ) <
      Real.exp ((c.rank : ℝ) * gCoarseClassicNat c.rank c.degree) :=
    (hone.trans_lt hlt).trans_le
      (Real.exp_le_exp.mpr
        (coarseTraceVolumeExponent_le_degree
          t c.rank c.degree ht htd))
  have hmul : 0 < (c.rank : ℝ) *
      gCoarseClassicNat c.rank c.degree := Real.one_lt_exp_iff.mp hexp
  exact ((mul_pos_iff.mp hmul).resolve_right (by
    intro h
    have hr : (0 : ℝ) < c.rank := by exact_mod_cast hn
    exact (not_lt_of_ge hr.le h.1).elim)).2

/-- The integral analytic envelope is positive for every realized class. -/
theorem integral_positive (t : ℝ) (c : GlobalLatticeClass)
    (ht : 0 < t) (htd : t ≤ c.degree)
    (hc : c.IsIntegralTraceEuclidean t) :
    0 < gCoarseIntegralNat c.rank c.degree := by
  have hn : 0 < c.rank := c.rank_pos
  have hd : 0 < c.degree := by
    have : (0 : ℝ) < c.degree := ht.trans_le htd
    exact_mod_cast this
  have hone := one_le_minkowskiTraceVolumeBound_integral
    t c.rank c.degree c ht htd ⟨hc, rfl, rfl⟩
  have hlt : minkowskiTraceVolumeBound (2 * t) c.rank c.degree <
      Real.exp (coarseIntegralTraceVolumeExponent
        t c.rank c.degree) := by
    rw [← coarseTraceVolumeExponent_two_mul
      t c.rank c.degree ht hd,
      exp_coarseTraceVolumeExponent_eq
        (2 * t) c.rank c.degree (by positivity) hn hd]
    exact minkowskiTraceVolumeBound_lt_coarse
      (2 * t) c.rank c.degree (by positivity) hn hd
  have hexp : (1 : ℝ) <
      Real.exp ((c.rank : ℝ) * gCoarseIntegralNat c.rank c.degree) :=
    (hone.trans_lt hlt).trans_le
      (Real.exp_le_exp.mpr
        (coarseIntegralTraceVolumeExponent_le_degree
          t c.rank c.degree ht htd))
  have hmul : 0 < (c.rank : ℝ) *
      gCoarseIntegralNat c.rank c.degree := Real.one_lt_exp_iff.mp hexp
  exact ((mul_pos_iff.mp hmul).resolve_right (by
    intro h
    have hr : (0 : ℝ) < c.rank := by exact_mod_cast hn
    exact (not_lt_of_ge hr.le h.1).elim)).2

/-- Direct finite reduction codes give the classic fixed-field, fixed-rank
fiber required by the global assembly. -/
theorem classic_fixed_field_rank (t : ℝ) (n : ℕ)
    (K : CodedNumberField) (ht : 0 < t) :
    {c : FieldFiber GlobalLatticeClass.fieldCode K |
      c.1.IsClassicTraceEuclidean t ∧ c.1.rank = n}.Finite := by
  apply (GlobalLatticeClass.finite_fixedField_rank_classic_traceEuclidean
    K n ht (lt_add_one t)).subset
  intro c hc
  exact ⟨hc.2, hc.1.2, hc.1.1⟩

/-- Direct scale-two reduction codes give the integral fixed-field,
fixed-rank fiber. -/
theorem integral_fixed_field_rank (t : ℝ) (n : ℕ)
    (K : CodedNumberField) (ht : 0 < t) :
    {c : FieldFiber GlobalLatticeClass.fieldCode K |
      c.1.IsIntegralTraceEuclidean t ∧ c.1.rank = n}.Finite := by
  apply (GlobalLatticeClass.finite_fixedField_rank_integral_traceEuclidean
    K n ht (lt_add_one t)).subset
  intro c hc
  exact ⟨hc.2, hc.1⟩

/-- The concrete, unconditional finiteness framework. -/
def toMainFinitenessFramework :
    MainFinitenessFramework UniversalNumberFieldAmbient GlobalLatticeClass where
  rank := GlobalLatticeClass.rank
  degree := GlobalLatticeClass.degree
  classic := GlobalLatticeClass.IsClassicTraceEuclidean
  integral := GlobalLatticeClass.IsIntegralTraceEuclidean
  fieldCode := GlobalLatticeClass.fieldCode
  classicDiscriminantBound := classicDiscriminantBound
  integralDiscriminantBound := integralDiscriminantBound
  classic_positive := classic_positive
  integral_positive := integral_positive
  classic_discriminant_le := classic_discriminant_le
  integral_discriminant_le := integral_discriminant_le
  classic_fixed_field_rank := classic_fixed_field_rank
  integral_fixed_field_rank := integral_fixed_field_rank

/-- Lemma 5.1 for a fixed classic-integral rank--degree fiber. -/
theorem classic_fixed_pair (t : ℝ) (ht : 0 < t)
    (n d : ℕ) (htd : t ≤ d) :
    {c : GlobalLatticeClass |
      c.IsClassicTraceEuclidean t ∧ c.rank = n ∧ c.degree = d}.Finite :=
  MainFinitenessFramework.classic_fixed_pair
    toMainFinitenessFramework t ht n d htd

/-- Lemma 5.1 for a fixed integral rank--degree fiber. -/
theorem integral_fixed_pair (t : ℝ) (ht : 0 < t)
    (n d : ℕ) (htd : t ≤ d) :
    {c : GlobalLatticeClass |
      c.IsIntegralTraceEuclidean t ∧ c.rank = n ∧ c.degree = d}.Finite :=
  MainFinitenessFramework.integral_fixed_pair
    toMainFinitenessFramework t ht n d htd

/-- Theorem 1.2(i). -/
theorem finiteness_classic_fixed_degree_low_rank
    (t : ℝ) (ht : 0 < t) (n d : ℕ) (htd : t ≤ d)
    (hn : n = 1 ∨ n = 2) :
    {c : GlobalLatticeClass |
      c.IsClassicTraceEuclidean t ∧ c.rank = n ∧ c.degree = d}.Finite :=
  MainFinitenessFramework.finiteness_classic_fixed_degree_low_rank
    toMainFinitenessFramework t ht n d htd hn

/-- Theorem 1.2(ii). -/
theorem finiteness_classic_fixed_high_rank
    (t : ℝ) (ht : 0 < t) (n : ℕ) (hn : 3 ≤ n) :
    {c : GlobalLatticeClass |
      c.IsClassicTraceEuclidean t ∧ c.rank = n ∧ t ≤ c.degree}.Finite :=
  MainFinitenessFramework.finiteness_classic_fixed_high_rank
    toMainFinitenessFramework t ht n hn

/-- Theorem 1.2(iii). -/
theorem finiteness_classic_fixed_degree
    (t : ℝ) (ht : 0 < t) (d : ℕ) (htd : t ≤ d) :
    {c : GlobalLatticeClass |
      c.IsClassicTraceEuclidean t ∧ c.degree = d}.Finite :=
  MainFinitenessFramework.finiteness_classic_fixed_degree
    toMainFinitenessFramework t ht d htd

/-- Theorem 1.2(iv). -/
theorem finiteness_classic_global (t : ℝ) (ht : 0 < t) :
    {c : GlobalLatticeClass |
      c.IsClassicTraceEuclidean t ∧ t ≤ c.degree ∧ 3 ≤ c.rank}.Finite :=
  MainFinitenessFramework.finiteness_classic_global
    toMainFinitenessFramework t ht

/-- Theorem 1.3(i). -/
theorem finiteness_integral_fixed_degree_low_rank
    (t : ℝ) (ht : 0 < t) (n d : ℕ) (htd : t ≤ d)
    (hn : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4) :
    {c : GlobalLatticeClass |
      c.IsIntegralTraceEuclidean t ∧ c.rank = n ∧ c.degree = d}.Finite :=
  MainFinitenessFramework.finiteness_integral_fixed_degree_low_rank
    toMainFinitenessFramework t ht n d htd hn

/-- Theorem 1.3(ii). -/
theorem finiteness_integral_fixed_high_rank
    (t : ℝ) (ht : 0 < t) (n : ℕ) (hn : 5 ≤ n) :
    {c : GlobalLatticeClass |
      c.IsIntegralTraceEuclidean t ∧ c.rank = n ∧ t ≤ c.degree}.Finite :=
  MainFinitenessFramework.finiteness_integral_fixed_high_rank
    toMainFinitenessFramework t ht n hn

/-- Theorem 1.3(iii). -/
theorem finiteness_integral_fixed_degree
    (t : ℝ) (ht : 0 < t) (d : ℕ) (htd : t ≤ d) :
    {c : GlobalLatticeClass |
      c.IsIntegralTraceEuclidean t ∧ c.degree = d}.Finite :=
  MainFinitenessFramework.finiteness_integral_fixed_degree
    toMainFinitenessFramework t ht d htd

/-- Theorem 1.3(iv). -/
theorem finiteness_integral_global (t : ℝ) (ht : 0 < t) :
    {c : GlobalLatticeClass |
      c.IsIntegralTraceEuclidean t ∧ t ≤ c.degree ∧ 5 ≤ c.rank}.Finite :=
  MainFinitenessFramework.finiteness_integral_global
    toMainFinitenessFramework t ht

end GlobalFiniteness

end

end TraceEuclidean
