import TraceEuclidean.OdlyzkoPairedFormula
import Mathlib.Analysis.PSeries

/-!
# A quantitative criterion for convergence of the paired zero sum

This separates the two estimates needed to sum the actual zero terms: a
fourth-power bound for the exact source transform and a quadratic ordinal
bound for an enumeration ordered by zero height. Neither estimate is asserted
here for Dedekind-zeta zeros. The criterion removes summability as a separate
assumption once both estimates have been established.
-/

namespace TraceEuclidean

noncomputable section
open scoped ComplexConjugate

/-- The ordinal bound is a deliberately coarse consequence expected from a
zero-counting estimate for a height-ordered enumeration. -/
def OdlyzkoZeroOrdinalBound (C : ℝ) (zeros : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, (n + 1 : ℝ) ≤ C * (1 + |(zeros n).im|) ^ 2

/-- A quadratic upper bound on the number of indexed zeros up to height `T`.
The finite set records multiplicity through the enumeration indices. -/
def OdlyzkoZeroCountBound (C : ℝ) (zeros : ℕ → ℂ) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∃ s : Finset ℕ,
    (∀ n, n ∈ s ↔ |(zeros n).im| ≤ T) ∧
      (s.card : ℝ) ≤ C * (1 + T) ^ 2

/-- A count in the customary `T log T` scale, with explicit finite-index
completeness and constants independent of the height. -/
def OdlyzkoZeroCountLogBound (A B : ℝ) (zeros : ℕ → ℂ) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∃ s : Finset ℕ,
    (∀ n, n ∈ s ↔ |(zeros n).im| ≤ T) ∧
      (s.card : ℝ) ≤ A + B * T * Real.log (2 + T)

/-- The large-height version matches the range `T ≥ 1` in the explicit
Dedekind-zeta zero count of Hasanalizade--Shen--Wong, Corollary 1.2. -/
def OdlyzkoZeroCountLargeHeightLogBound (A B : ℝ) (zeros : ℕ → ℂ) : Prop :=
  ∀ T : ℝ, 1 ≤ T → ∃ s : Finset ℕ,
    (∀ n, n ∈ s ↔ |(zeros n).im| ≤ T) ∧
      (s.card : ℝ) ≤ A + B * T * Real.log (2 + T)

/-- The count at height one controls every smaller height by restricting its
finite index set. Thus a published `T ≥ 1` estimate suffices for the `T ≥ 0`
interface, after increasing the constant term by `B * log 3`. -/
theorem odlyzkoZeroCountLogBound_of_largeHeight
    (zeros : ℕ → ℂ) (A B : ℝ) (hB : 0 ≤ B)
    (hLarge : OdlyzkoZeroCountLargeHeightLogBound A B zeros) :
    OdlyzkoZeroCountLogBound (A + B * Real.log 3) B zeros := by
  classical
  intro T hT
  by_cases hOne : 1 ≤ T
  · obtain ⟨s, hs, hCard⟩ := hLarge T hOne
    refine ⟨s, hs, ?_⟩
    have hLogThree : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    nlinarith [mul_nonneg hB hLogThree]
  · obtain ⟨s, hs, hCard⟩ := hLarge 1 le_rfl
    let s' := s.filter (fun n ↦ |(zeros n).im| ≤ T)
    refine ⟨s', ?_, ?_⟩
    · intro n
      simp only [s', Finset.mem_filter, hs n]
      constructor
      · exact And.right
      · intro hn
        exact ⟨hn.trans (by linarith), hn⟩
    · have hSub : s' ⊆ s := Finset.filter_subset _ _
      have hCard' : (s'.card : ℝ) ≤ (s.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hSub
      have hLog : 0 ≤ Real.log (2 + T) :=
        Real.log_nonneg (by linarith)
      have hExtra : 0 ≤ B * T * Real.log (2 + T) := by positivity
      norm_num at hCard
      nlinarith

/-- The standard logarithmic counting scale yields the coarser quadratic
count used by the summability criterion. -/
theorem odlyzkoZeroCountBound_of_logBound
    (zeros : ℕ → ℂ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hLogCount : OdlyzkoZeroCountLogBound A B zeros) :
    OdlyzkoZeroCountBound (A + B) zeros := by
  intro T hT
  obtain ⟨s, hs, hCard⟩ := hLogCount T hT
  refine ⟨s, hs, ?_⟩
  have hLog : Real.log (2 + T) ≤ 1 + T := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 2 + T)]
  have hLogTerm : B * T * Real.log (2 + T) ≤ B * T * (1 + T) :=
    mul_le_mul_of_nonneg_left hLog (mul_nonneg hB hT)
  have hAterm : A ≤ A * (1 + T) ^ 2 := by
    nlinarith [mul_nonneg hA hT, mul_nonneg hA (sq_nonneg T)]
  have hBterm : B * T * (1 + T) ≤ B * (1 + T) ^ 2 := by
    nlinarith [mul_nonneg hB (by linarith : 0 ≤ 1 + T)]
  nlinarith

/-- A height-ordered enumeration converts the counting estimate into the
ordinal estimate used for comparison with the square series. -/
theorem odlyzkoZeroOrdinalBound_of_countBound
    (zeros : ℕ → ℂ) (C : ℝ)
    (hOrdered : ∀ i j : ℕ, i ≤ j → |(zeros i).im| ≤ |(zeros j).im|)
    (hCount : OdlyzkoZeroCountBound C zeros) :
    OdlyzkoZeroOrdinalBound C zeros := by
  intro n
  obtain ⟨s, hs, hCard⟩ := hCount |(zeros n).im| (abs_nonneg _)
  have hSubset : Finset.range (n + 1) ⊆ s := by
    intro i hi
    exact (hs i).2 (hOrdered i n (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
  have hCardNat : n + 1 ≤ s.card := by
    simpa only [Finset.card_range] using Finset.card_le_card hSubset
  exact (by exact_mod_cast hCardNat : (n + 1 : ℝ) ≤ (s.card : ℝ)).trans hCard

/-- A uniform fourth-power vertical bound for the exact test-function
transform throughout the closed critical strip. -/
def OdlyzkoPhiFourthPowerBound (D : ℝ) : Prop :=
  ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 →
    ‖odlyzkoPhi s‖ ≤ D / (1 + |s.im|) ^ 4

/-- A fourth-power transform bound and a quadratic ordinal bound give a
summable square-series majorant for the real contributions. -/
theorem odlyzkoPhi_zero_re_summable_of_bounds
    (zeros : ℕ → ℂ) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hStrip : ∀ n, 0 ≤ (zeros n).re ∧ (zeros n).re ≤ 1)
    (hGrowth : OdlyzkoZeroOrdinalBound C zeros)
    (hDecay : OdlyzkoPhiFourthPowerBound D) :
    Summable (fun n ↦ (odlyzkoPhi (zeros n)).re) := by
  have hPSeries : Summable (fun n : ℕ ↦ D * C ^ 2 / (n + 1 : ℝ) ^ 2) := by
    have hBase : Summable (fun n : ℕ ↦ 1 / (n + 1 : ℝ) ^ 2) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        ((summable_nat_add_iff 1).2
          ((Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)))
    simpa [div_eq_mul_inv] using hBase.mul_left (D * C ^ 2)
  apply hPSeries.of_norm_bounded
  intro n
  let u : ℝ := 1 + |(zeros n).im|
  let m : ℝ := (n + 1 : ℝ)
  have hu : 0 < u := by dsimp [u]; positivity
  have hm : 0 < m := by dsimp [m]; positivity
  have hOrd : m ≤ C * u ^ 2 := hGrowth n
  have hPow : m ^ 2 ≤ C ^ 2 * u ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hOrd)
      (add_nonneg (mul_nonneg hC (sq_nonneg u)) hm.le)]
  have hCompare : D / u ^ 4 ≤ D * C ^ 2 / m ^ 2 := by
    rw [div_le_div_iff₀ (pow_pos hu 4) (pow_pos hm 2)]
    nlinarith [mul_nonneg hD (sub_nonneg.mpr hPow)]
  calc
    ‖(odlyzkoPhi (zeros n)).re‖ = |(odlyzkoPhi (zeros n)).re| := Real.norm_eq_abs _
    _ ≤ ‖odlyzkoPhi (zeros n)‖ := Complex.abs_re_le_norm _
    _ ≤ D / u ^ 4 := hDecay (zeros n) (hStrip n).1 (hStrip n).2
    _ ≤ D * C ^ 2 / m ^ 2 := hCompare

/-- The same two independent quantitative bounds imply absolute convergence
of the complex conjugate-paired series. -/
theorem odlyzkoPhi_conj_pair_summable_of_bounds
    (zeros : ℕ → ℂ) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hStrip : ∀ n, 0 ≤ (zeros n).re ∧ (zeros n).re ≤ 1)
    (hGrowth : OdlyzkoZeroOrdinalBound C zeros)
    (hDecay : OdlyzkoPhiFourthPowerBound D) :
    Summable (fun n ↦ odlyzkoPhi (zeros n) +
      odlyzkoPhi (conj (zeros n))) := by
  exact (odlyzkoPhi_conj_pair_summable_iff zeros).2
    (odlyzkoPhi_zero_re_summable_of_bounds zeros C D hC hD hStrip hGrowth hDecay)

/-- A height-ordered zero list, a quadratic zero count, and fourth-power
decay replace the independent paired-summability premise in the Table 4
reduction. The source explicit formula and the two estimates remain explicit
inputs. -/
theorem odlyzkoTable4ExplicitCorrectionInput_of_countAndDecay
    (realIndices : CodedNumberField → Finset ℕ)
    (realZeros pairReps : CodedNumberField → ℕ → ℂ)
    (hReal : ∀ K i, i ∈ realIndices K → (realZeros K i).im = 0)
    (hNonreal : ∀ K i, (pairReps K i).im ≠ 0)
    (hRealStrip : ∀ K i, i ∈ realIndices K →
      0 ≤ (realZeros K i).re ∧ (realZeros K i).re ≤ 1)
    (hPairStrip : ∀ K i, 0 ≤ (pairReps K i).re ∧ (pairReps K i).re ≤ 1)
    (C : CodedNumberField → ℝ) (D : ℝ)
    (hC : ∀ K, 0 ≤ C K) (hD : 0 ≤ D)
    (hOrdered : ∀ K i j, i ≤ j →
      |(pairReps K i).im| ≤ |(pairReps K j).im|)
    (hCount : ∀ K, OdlyzkoZeroCountBound (C K) (pairReps K))
    (hDecay : OdlyzkoPhiFourthPowerBound D)
    (hFormula : OdlyzkoExplicitFormulaInput
      (fun K ↦ (∑ i ∈ realIndices K, (odlyzkoPhi (realZeros K i)).re) +
        (∑' i, (odlyzkoPhi (pairReps K i) +
          odlyzkoPhi (conj (pairReps K i)))).re))
    (hAB : OdlyzkoABIntegralCertificate) :
    OdlyzkoTable4ExplicitCorrectionInput := by
  apply odlyzkoTable4ExplicitCorrectionInput_of_realAndPairedZeros
    realIndices realZeros pairReps hReal hNonreal hRealStrip hPairStrip
  · intro K
    exact odlyzkoPhi_conj_pair_summable_of_bounds
      (pairReps K) (C K) D (hC K) hD (hPairStrip K)
      (odlyzkoZeroOrdinalBound_of_countBound (pairReps K) (C K)
        (hOrdered K) (hCount K)) hDecay
  · exact hFormula
  · exact hAB

end
end TraceEuclidean
