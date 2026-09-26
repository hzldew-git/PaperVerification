import TraceEuclidean.V15VoightDiscriminantData
import TraceEuclidean.V15AnalyticTableBridge

/-!
# Certified finite-data bridge for Voight's enumeration

The archived data columns are checked in `V15VoightDiscriminantData`.  This
module isolates one source-facing completeness statement matching Voight's
enumeration through root discriminant fourteen, then derives the degree-five
through degree-nine minima and the empty degree-ten range used in Section 4.
-/

namespace TraceEuclidean

noncomputable section

/-- Source-facing completeness statement for the portion of Voight's
root-discriminant-fourteen enumeration used in Section 4.  The finite lists
themselves are imported and checked separately. -/
def V15VoightEnumerationUpToFourteenInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    let d := Module.finrank ℚ K.1
    5 ≤ d → d ≤ 10 → K.discriminant.natAbs ≤ 14 ^ d →
      K.discriminant.natAbs ∈ v15VoightDiscriminants d

theorem v15_voightDiscriminantsFive_minimum {D : ℕ}
    (hD : D ∈ v15VoightDiscriminantsFive) : 14641 ≤ D := by
  have h := v15_voightDiscriminantsFive_pairwise.rel_head hD
  change 14641 ≤ D at h
  exact h

theorem v15_voightDiscriminantsSix_minimum {D : ℕ}
    (hD : D ∈ v15VoightDiscriminantsSix) : 300125 ≤ D := by
  have h := v15_voightDiscriminantsSix_pairwise.rel_head hD
  change 300125 ≤ D at h
  exact h

theorem v15_voightDiscriminantsSeven_minimum {D : ℕ}
    (hD : D ∈ v15VoightDiscriminantsSeven) : 20134393 ≤ D := by
  have h := v15_voightDiscriminantsSeven_pairwise.rel_head hD
  change 20134393 ≤ D at h
  exact h

theorem v15_voightDiscriminantsEight_minimum {D : ℕ}
    (hD : D ∈ v15VoightDiscriminantsEight) : 282300416 ≤ D := by
  have h := v15_voightDiscriminantsEight_pairwise.rel_head hD
  change 282300416 ≤ D at h
  exact h

theorem v15_voightDiscriminantsNine_minimum {D : ℕ}
    (hD : D ∈ v15VoightDiscriminantsNine) : 9685993193 ≤ D := by
  have h := v15_voightDiscriminantsNine_pairwise.rel_head hD
  change 9685993193 ≤ D at h
  exact h

/-- Every imported row in degrees five through nine is bounded below by the
minimum used in the manuscript. -/
theorem v15_voightDiscriminants_minimum {d D : ℕ}
    (hd5 : 5 ≤ d) (hd9 : d ≤ 9)
    (hD : D ∈ v15VoightDiscriminants d) :
    v15MinimumDiscriminant d ≤ D := by
  interval_cases d
  all_goals simp only [v15VoightDiscriminants] at hD
  · simpa [v15MinimumDiscriminant] using
      v15_voightDiscriminantsFive_minimum hD
  · simpa [v15MinimumDiscriminant] using
      v15_voightDiscriminantsSix_minimum hD
  · simpa [v15MinimumDiscriminant] using
      v15_voightDiscriminantsSeven_minimum hD
  · simpa [v15MinimumDiscriminant] using
      v15_voightDiscriminantsEight_minimum hD
  · simpa [v15MinimumDiscriminant] using
      v15_voightDiscriminantsNine_minimum hD

/-- Voight completeness plus the checked table columns gives all exact minima
used in degrees five through nine. -/
theorem v15_degreeFiveToNineMinimumInput_of_voightEnumeration
    (hEnum : V15VoightEnumerationUpToFourteenInput) :
    V15DegreeFiveToNineMinimumInput := by
  intro K hreal
  dsimp only
  intro hd5 hd9
  let d := Module.finrank ℚ K.1
  let D := K.discriminant.natAbs
  have hd5d : 5 ≤ d := by simpa [d] using hd5
  have hd9d : d ≤ 9 := by simpa [d] using hd9
  have hdiscReal : ((|K.discriminant| : ℤ) : ℝ) = (D : ℝ) := by
    dsimp only [D]
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hdiscReal]
  change (v15MinimumDiscriminant d : ℝ) ≤ (D : ℝ)
  have hNat : v15MinimumDiscriminant d ≤ D := by
    by_contra hnot
    have hDlt : D < v15MinimumDiscriminant d := by omega
    have hD14 : D ≤ 14 ^ d := by
      interval_cases d <;>
        norm_num [v15MinimumDiscriminant] at hDlt ⊢ <;> omega
    have hmem := hEnum K hreal hd5d (by omega) hD14
    exact hnot (v15_voightDiscriminants_minimum hd5d hd9d hmem)
  exact_mod_cast hNat

/-- Voight completeness and the empty degree-ten data row prove the exact
degree-ten root-discriminant input used in Section 4. -/
theorem v15_degreeTenRootDiscriminantInput_of_voightEnumeration
    (hEnum : V15VoightEnumerationUpToFourteenInput) :
    V15DegreeTenRootDiscriminantInput := by
  intro K hreal hdegree
  by_contra hnot
  have hleReal :
      ((|K.discriminant| : ℤ) : ℝ) ≤ (14 : ℝ) ^ (10 : ℕ) :=
    le_of_not_gt hnot
  have hdiscReal :
      ((|K.discriminant| : ℤ) : ℝ) =
        (K.discriminant.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hdiscReal] at hleReal
  have hleNat : K.discriminant.natAbs ≤ 14 ^ (10 : ℕ) := by
    exact_mod_cast hleReal
  have hmem := hEnum K hreal (by omega) (by omega)
    (by simpa [hdegree] using hleNat)
  simp [hdegree, v15VoightDiscriminants] at hmem

end

end TraceEuclidean
