import TraceEuclidean.V15DedekindZetaZeroHeight
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Unordered zero sums from finite height counts

The first theorem removes the need to sort zeros by height. A quadratic
count on each unit-height shell and fourth-power decay suffice for absolute
summability over the occurrence type itself.
-/

namespace TraceEuclidean

noncomputable section

private theorem summable_of_shell_quadratic_fourth
    {ι : Type*} (level : ι → ℕ) (f : ι → ℂ) (C D : ℝ)
    (hD : 0 ≤ D)
    (hFinite : ∀ n, {i : ι | level i = n}.Finite)
    (hCard : ∀ n, (({i : ι | level i = n}.ncard : ℝ) ≤ C * (n + 1 : ℝ) ^ 2))
    (hDecay : ∀ i, ‖f i‖ ≤ D / (level i + 1 : ℝ) ^ 4) :
    Summable f := by
  let shell : ℕ → Set ι := fun n ↦ {i | level i = n}
  have hPartition : ∀ i : ι, ∃! n : ℕ, i ∈ shell n := by
    intro i
    refine ⟨level i, rfl, ?_⟩
    intro n hn
    exact hn.symm
  have hBase : Summable (fun n : ℕ ↦ C * D / (n + 1 : ℝ) ^ 2) := by
    have hp : Summable (fun n : ℕ ↦ 1 / (n + 1 : ℝ) ^ 2) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        ((summable_nat_add_iff 1).2
          ((Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)))
    simpa [div_eq_mul_inv] using hp.mul_left (C * D)
  have hNorm : Summable (fun i : ι ↦ ‖f i‖) := by
    apply (summable_partition (f := fun i : ι ↦ ‖f i‖)
      (s := shell) (fun i ↦ norm_nonneg _) hPartition).2
    constructor
    · intro n
      letI : Fintype (shell n) := (hFinite n).fintype
      exact summable_of_hasFiniteSupport
        (Set.finite_univ.subset (Set.subset_univ _))
    · apply hBase.of_nonneg_of_le (fun n ↦ by positivity)
      intro n
      letI : Fintype (shell n) := (hFinite n).fintype
      have hTerm : ∀ i : shell n, ‖f i‖ ≤ D / (n + 1 : ℝ) ^ 4 := by
        intro i
        simpa only [show level i = n from i.property] using hDecay i
      have hSum : (∑' i : shell n, ‖f i‖) ≤
          ((shell n).ncard : ℝ) * (D / (n + 1 : ℝ) ^ 4) := by
        rw [tsum_fintype]
        have h := Finset.sum_le_card_nsmul (Finset.univ : Finset (shell n))
          (fun i : shell n ↦ ‖f i‖) (D / (n + 1 : ℝ) ^ 4)
          (fun i _ ↦ hTerm i)
        simpa [Set.fintypeCard_eq_ncard, nsmul_eq_mul] using h
      have hNonneg : 0 ≤ D / (n + 1 : ℝ) ^ 4 := by positivity
      have hCount := mul_le_mul_of_nonneg_right (hCard n) hNonneg
      have hEq : C * (n + 1 : ℝ) ^ 2 * (D / (n + 1 : ℝ) ^ 4) =
          C * D / (n + 1 : ℝ) ^ 2 := by
        have hn : (n + 1 : ℝ) ≠ 0 := by positivity
        field_simp
      exact hSum.trans (by simpa [shell, hEq] using hCount)
  exact hNorm.of_norm

private theorem summable_of_sublevel_quadratic_fourth
    {ι : Type*} (height : ι → ℝ) (f : ι → ℂ) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hHeight : ∀ i, 0 ≤ height i)
    (hFinite : ∀ T : ℝ, {i : ι | height i ≤ T}.Finite)
    (hCount : ∀ T : ℝ, 0 ≤ T →
      (({i : ι | height i ≤ T}.ncard : ℝ) ≤ C * (1 + T) ^ 2))
    (hDecay : ∀ i, ‖f i‖ ≤ D / (1 + height i) ^ 4) :
    Summable f := by
  let level : ι → ℕ := fun i ↦ ⌊height i⌋₊
  have hShellFinite (n : ℕ) : {i : ι | level i = n}.Finite := by
    apply (hFinite (n + 1)).subset
    intro i hi
    have hFloor : height i < (level i : ℝ) + 1 := by
      simpa [level] using Nat.lt_floor_add_one (height i)
    change level i = n at hi
    rw [hi] at hFloor
    exact hFloor.le
  have hShellCard (n : ℕ) :
      (({i : ι | level i = n}.ncard : ℝ) ≤ (4 * C) * (n + 1 : ℝ) ^ 2) := by
    have hSub : {i : ι | level i = n} ⊆ {i : ι | height i ≤ (n + 1 : ℝ)} := by
      intro i hi
      have hFloor : height i < (level i : ℝ) + 1 := by
        simpa [level] using Nat.lt_floor_add_one (height i)
      change level i = n at hi
      rw [hi] at hFloor
      exact hFloor.le
    have hNat := Set.ncard_le_ncard hSub (hFinite (n + 1))
    have hReal : (({i : ι | level i = n}.ncard : ℝ) ≤
        ({i : ι | height i ≤ (n + 1 : ℝ)}.ncard : ℝ)) := by
      exact_mod_cast hNat
    have hSquare : (1 + (n + 1 : ℝ)) ^ 2 ≤ 4 * (n + 1 : ℝ) ^ 2 := by
      have hn : (0 : ℝ) ≤ n := by positivity
      nlinarith
    calc
      _ ≤ ({i : ι | height i ≤ (n + 1 : ℝ)}.ncard : ℝ) := hReal
      _ ≤ C * (1 + (n + 1 : ℝ)) ^ 2 := hCount _ (by positivity)
      _ ≤ (4 * C) * (n + 1 : ℝ) ^ 2 := by
        nlinarith [mul_nonneg hC (sub_nonneg.mpr hSquare)]
  have hLevelDecay (i : ι) :
      ‖f i‖ ≤ D / (level i + 1 : ℝ) ^ 4 := by
    have hFloor : (level i : ℝ) ≤ height i := Nat.floor_le (hHeight i)
    have hBase : (level i + 1 : ℝ) ≤ 1 + height i := by
      simpa [Nat.cast_add, add_comm] using add_le_add_right hFloor 1
    have hPow : (level i + 1 : ℝ) ^ 4 ≤ (1 + height i) ^ 4 := by
      gcongr
    calc
      ‖f i‖ ≤ D / (1 + height i) ^ 4 := hDecay i
      _ ≤ D / (level i + 1 : ℝ) ^ 4 :=
        div_le_div_of_nonneg_left hD (by positivity) hPow
  exact summable_of_shell_quadratic_fourth level f (4 * C) D hD
    hShellFinite hShellCard hLevelDecay

variable {K : Type*} [Field K] [NumberField K]

/-- A deliberately coarse count on actual multiplicity-aware zero
occurrences. Its proof from global zeta theory remains a separate task. -/
def V15DedekindZetaZeroOccurrence.QuadraticCountInput
    (Z : V15DedekindZetaRegularization K) (C : ℝ) : Prop :=
  ∀ T : ℝ, 0 ≤ T →
    ((V15DedekindZetaZeroOccurrence.boundedSet Z T).ncard : ℝ) ≤
      C * (1 + T) ^ 2

/-- The published HSW estimate implies a coarse all-height count on the
actual occurrence type. The factor four also handles heights below one. -/
theorem V15DedekindZetaZeroOccurrence.quadraticCount_of_HSWNumeric
    (Z : V15DedekindZetaRegularization K) (d : ℝ) (n : ℕ)
    (hd : 1 ≤ d)
    (hNumeric : V15DedekindZetaZeroOccurrence.HSWNumericInput Z d n) :
    V15DedekindZetaZeroOccurrence.QuadraticCountInput Z
      (4 * (Real.log d + 25 * (n : ℝ) + 5)) := by
  let C₀ : ℝ := Real.log d + 25 * (n : ℝ) + 5
  have hLogD : 0 ≤ Real.log d := Real.log_nonneg hd
  have hN : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hLarge (T : ℝ) (hT : 1 ≤ T) :
      ((V15DedekindZetaZeroOccurrence.boundedSet Z T).ncard : ℝ) ≤
        C₀ * (1 + T) ^ 2 := by
    have hMainLog := v15HasanalizadeShenWong_log_main_term d T n
      (by linarith) (by linarith)
    have hBound := (abs_le.mp (hNumeric T hT)).2
    rw [hMainLog] at hBound
    have hPi : 1 ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
    have hPiPos : 0 < Real.pi := Real.pi_pos
    have hExp : 1 ≤ Real.exp 1 := by
      simpa only [Real.exp_zero] using
        Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num)
    have hDen : 1 ≤ 2 * Real.pi * Real.exp 1 := by
      have hTwoPi : 1 ≤ 2 * Real.pi := by linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hTwoPi) (sub_nonneg.mpr hExp)]
    have hLogDen : 0 ≤ Real.log (2 * Real.pi * Real.exp 1) :=
      Real.log_nonneg hDen
    have hLogT : 0 ≤ Real.log T := Real.log_nonneg hT
    have hLogTle : Real.log T ≤ T := by
      linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < T)]
    let q : ℝ := Real.log d + (n : ℝ) * Real.log T
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hMain :
        T / Real.pi * (q - (n : ℝ) * Real.log (2 * Real.pi * Real.exp 1)) ≤
          T * q := by
      have hDiv : T / Real.pi ≤ T := by
        apply (div_le_iff₀ hPiPos).2
        nlinarith [mul_nonneg (sub_nonneg.mpr hPi) (by linarith : 0 ≤ T)]
      calc
        _ ≤ T / Real.pi * q :=
          mul_le_mul_of_nonneg_left (sub_le_self _ (mul_nonneg hN hLogDen))
            (div_nonneg (by linarith) hPiPos.le)
        _ ≤ T * q := mul_le_mul_of_nonneg_right hDiv hq
    have hError :
        (228 / 1000 : ℝ) * q + (23108 / 1000 : ℝ) * n + 4520 / 1000 ≤
          q + 24 * n + 5 := by
      nlinarith
    have hFirst :
        ((V15DedekindZetaZeroOccurrence.boundedSet Z T).ncard : ℝ) ≤
          (T + 1) * q + 24 * n + 5 := by
      dsimp [q] at hBound ⊢
      nlinarith [hMain, hError]
    have hqUpper : q ≤ (Real.log d + n) * (1 + T) := by
      dsimp [q]
      have hA : 0 ≤ (n : ℝ) * (1 + T - Real.log T) :=
        mul_nonneg hN (by linarith)
      have hB : 0 ≤ T * Real.log d := mul_nonneg (by linarith) hLogD
      nlinarith
    have hSecond : (T + 1) * q ≤ (Real.log d + n) * (1 + T) ^ 2 := by
      calc
        _ ≤ (T + 1) * ((Real.log d + n) * (1 + T)) :=
          mul_le_mul_of_nonneg_left hqUpper (by linarith)
        _ = _ := by ring
    have hSquare : (1 : ℝ) ≤ (1 + T) ^ 2 := by nlinarith
    have hConstant : 24 * (n : ℝ) + 5 ≤
        (24 * (n : ℝ) + 5) * (1 + T) ^ 2 := by
      nlinarith [mul_nonneg (by positivity : 0 ≤ 24 * (n : ℝ) + 5)
        (sub_nonneg.mpr hSquare)]
    dsimp [C₀]
    nlinarith [hFirst, hSecond, hConstant]
  intro T hT
  by_cases hOne : 1 ≤ T
  · have h := hLarge T hOne
    have hFactor : C₀ * (1 + T) ^ 2 ≤ (4 * C₀) * (1 + T) ^ 2 := by
      nlinarith [mul_nonneg hC₀ (sq_nonneg (1 + T))]
    simpa [C₀] using h.trans hFactor
  · have hSub : V15DedekindZetaZeroOccurrence.boundedSet Z T ⊆
        V15DedekindZetaZeroOccurrence.boundedSet Z 1 := by
      intro o ho
      change |o.value.im| ≤ T at ho
      change |o.value.im| ≤ (1 : ℝ)
      exact ho.trans (by linarith)
    have hNat := Set.ncard_le_ncard hSub
      (V15DedekindZetaZeroOccurrence.boundedSet_finite Z 1)
    have hCard :
        ((V15DedekindZetaZeroOccurrence.boundedSet Z T).ncard : ℝ) ≤
          (V15DedekindZetaZeroOccurrence.boundedSet Z 1).ncard := by
      exact_mod_cast hNat
    have hAtOne := hLarge 1 le_rfl
    have hSquare : (1 : ℝ) ≤ (1 + T) ^ 2 := by nlinarith
    have hLast : (4 * C₀) ≤ (4 * C₀) * (1 + T) ^ 2 := by
      nlinarith [mul_nonneg (by positivity : 0 ≤ 4 * C₀)
        (sub_nonneg.mpr hSquare)]
    have hFinal := hCard.trans hAtOne
    dsimp [C₀] at *
    nlinarith

/-- Fixes the coarse count's parameters to the actual number-field
discriminant and degree. -/
theorem V15DedekindZetaZeroOccurrence.quadraticCount_of_HSWField
    (Z : V15DedekindZetaRegularization K)
    (hField : V15DedekindZetaZeroOccurrence.HSWFieldInput Z) :
    V15DedekindZetaZeroOccurrence.QuadraticCountInput Z
      (4 * (Real.log |(NumberField.discr K : ℝ)| +
        25 * (Module.finrank ℚ K : ℝ) + 5)) := by
  exact V15DedekindZetaZeroOccurrence.quadraticCount_of_HSWNumeric Z
    |(NumberField.discr K : ℝ)| (Module.finrank ℚ K)
    (v15_abs_discr_ge_one K) hField

/-- The exact Odlyzko transform is absolutely summable over every actual
zero occurrence, with no ordered enumeration, if a quadratic height count
is available. The fourth-power decay is already proved for this kernel. -/
theorem V15DedekindZetaZeroOccurrence.phi_summable_of_quadratic_count
    (Z : V15DedekindZetaRegularization K) (C : ℝ) (hC : 0 ≤ C)
    (hCount : V15DedekindZetaZeroOccurrence.QuadraticCountInput Z C) :
    Summable (fun o : V15DedekindZetaZeroOccurrence Z ↦ v15OdlyzkoPhi o.value) := by
  obtain ⟨D, hD, hDecay⟩ := v15OdlyzkoPhi_exists_fourthPowerBound
  exact summable_of_sublevel_quadratic_fourth
    (fun o : V15DedekindZetaZeroOccurrence Z ↦ |o.value.im|)
    (fun o ↦ v15OdlyzkoPhi o.value) C D hC hD
    (fun o ↦ abs_nonneg _) (fun T ↦ V15DedekindZetaZeroOccurrence.boundedSet_finite Z T)
    (fun T hT ↦ hCount T hT)
    (fun o ↦ hDecay o.value (le_of_lt o.in_strip.1) (le_of_lt o.in_strip.2))

/-- The unordered, absolutely convergent zero contribution has a
nonnegative real part throughout the actual critical strip. -/
theorem V15DedekindZetaZeroOccurrence.phi_tsum_re_nonneg_of_quadratic_count
    (Z : V15DedekindZetaRegularization K) (C : ℝ) (hC : 0 ≤ C)
    (hCount : V15DedekindZetaZeroOccurrence.QuadraticCountInput Z C) :
    0 ≤ (∑' o : V15DedekindZetaZeroOccurrence Z, v15OdlyzkoPhi o.value).re := by
  exact v15OdlyzkoPhi_zero_tsum_re_nonneg
    (fun o : V15DedekindZetaZeroOccurrence Z ↦ o.value)
    (fun o ↦ ⟨le_of_lt o.in_strip.1, le_of_lt o.in_strip.2⟩)
    (V15DedekindZetaZeroOccurrence.phi_summable_of_quadratic_count Z C hC hCount)

/-- The HSW source count at regular heights suffices to sum actual zeros
without choosing any ordered sequence. Both the count and the entire
regularization remain explicit external analytic inputs. -/
theorem V15DedekindZetaZeroOccurrence.phi_summable_of_HSWRegular
    (Z : V15DedekindZetaRegularization K)
    (hRegular : V15DedekindZetaZeroOccurrence.HSWRegularHeightInput Z
      |(NumberField.discr K : ℝ)| (Module.finrank ℚ K)) :
    Summable (fun o : V15DedekindZetaZeroOccurrence Z ↦ v15OdlyzkoPhi o.value) := by
  let C : ℝ := 4 * (Real.log |(NumberField.discr K : ℝ)| +
    25 * (Module.finrank ℚ K : ℝ) + 5)
  have hC : 0 ≤ C := by
    have hd := v15_abs_discr_ge_one K
    have hLogD : 0 ≤ Real.log |(NumberField.discr K : ℝ)| :=
      Real.log_nonneg hd
    dsimp [C]
    positivity
  exact V15DedekindZetaZeroOccurrence.phi_summable_of_quadratic_count Z C hC
    (V15DedekindZetaZeroOccurrence.quadraticCount_of_HSWField Z
      (V15DedekindZetaZeroOccurrence.HSWFieldInput_of_regular_heights Z hRegular))

/-- A source-normalized explicit formula over actual zero occurrences yields
the Table 4 inequality with no height-ordered enumeration premise. The
entire regularization, quadratic count and explicit formula are named
inputs; kernel decay, positivity and archimedean bounds are internal. -/
theorem v15_odlyzkoTable4ExplicitCorrectionInput_of_unorderedZeros
    (regularization : ∀ K : CodedNumberField,
      V15DedekindZetaRegularization K.1)
    (C : CodedNumberField → ℝ) (hC : ∀ K, 0 ≤ C K)
    (hCount : ∀ K,
      V15DedekindZetaZeroOccurrence.QuadraticCountInput
        (regularization K) (C K))
    (hFormula : V15OdlyzkoExplicitFormulaInput
      (fun K ↦ (∑' o : V15DedekindZetaZeroOccurrence (regularization K),
        v15OdlyzkoPhi o.value).re))
    (hAB : V15OdlyzkoABIntegralCertificate) :
    V15OdlyzkoTable4ExplicitCorrectionInput := by
  apply v15_odlyzkoTable4ExplicitCorrectionInput_of_sourceFormula _ hFormula
  · intro K
    exact V15DedekindZetaZeroOccurrence.phi_tsum_re_nonneg_of_quadratic_count
      (regularization K) (C K) (hC K) (hCount K)
  · exact hAB

end
end TraceEuclidean
