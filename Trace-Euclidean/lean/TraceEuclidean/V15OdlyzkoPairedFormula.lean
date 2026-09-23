import TraceEuclidean.V15OdlyzkoZeroPairing
import TraceEuclidean.V15OdlyzkoExplicitFormulaReduction

/-!
# Real zeros and conjugate pairs in the source explicit formula

Real zeros are finitely indexed single terms. Nonreal zeros are represented
once per distinct conjugate pair. Multiplicity and completeness of these lists, and the source
explicit formula, remain explicit external inputs.
-/

namespace TraceEuclidean

noncomputable section
open scoped ComplexConjugate

/-- With real zeros counted once and nonreal zeros counted by conjugate pairs,
the source formula implies the exact-error Table 4 inequality. -/
theorem v15_odlyzkoTable4ExplicitCorrectionInput_of_realAndPairedZeros
    (realIndices : CodedNumberField → Finset ℕ)
    (realZeros pairReps : CodedNumberField → ℕ → ℂ)
    (_hReal : ∀ K i, i ∈ realIndices K → (realZeros K i).im = 0)
    (_hNonreal : ∀ K i, (pairReps K i).im ≠ 0)
    (hRealStrip : ∀ K i, i ∈ realIndices K →
      0 ≤ (realZeros K i).re ∧ (realZeros K i).re ≤ 1)
    (hPairStrip : ∀ K i, 0 ≤ (pairReps K i).re ∧ (pairReps K i).re ≤ 1)
    (hPairSummable : ∀ K, Summable (fun i ↦
      v15OdlyzkoPhi (pairReps K i) +
        v15OdlyzkoPhi (conj (pairReps K i))))
    (hFormula : V15OdlyzkoExplicitFormulaInput
      (fun K ↦ (∑ i ∈ realIndices K, (v15OdlyzkoPhi (realZeros K i)).re) +
        (∑' i, (v15OdlyzkoPhi (pairReps K i) +
          v15OdlyzkoPhi (conj (pairReps K i)))).re))
    (hAB : V15OdlyzkoABIntegralCertificate) :
    V15OdlyzkoTable4ExplicitCorrectionInput := by
  apply v15_odlyzkoTable4ExplicitCorrectionInput_of_sourceFormula
    (fun K ↦ (∑ i ∈ realIndices K, (v15OdlyzkoPhi (realZeros K i)).re) +
      (∑' i, (v15OdlyzkoPhi (pairReps K i) +
        v15OdlyzkoPhi (conj (pairReps K i)))).re) hFormula _ hAB
  intro K
  have hRealNonneg :
      0 ≤ ∑ i ∈ realIndices K, (v15OdlyzkoPhi (realZeros K i)).re := by
    apply Finset.sum_nonneg
    intro i hi
    exact v15OdlyzkoPhi_re_nonneg_of_mem_closed_strip (realZeros K i)
      (hRealStrip K i hi).1 (hRealStrip K i hi).2
  have hPairNonneg : 0 ≤
      (∑' i, (v15OdlyzkoPhi (pairReps K i) +
        v15OdlyzkoPhi (conj (pairReps K i)))).re := by
    rw [Complex.re_tsum (hPairSummable K)]
    exact tsum_nonneg fun i ↦
      v15OdlyzkoPhi_conj_pair_nonneg (pairReps K i)
        (hPairStrip K i).1 (hPairStrip K i).2
  exact add_nonneg hRealNonneg hPairNonneg

end
end TraceEuclidean
