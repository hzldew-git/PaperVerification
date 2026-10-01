import TraceEuclidean.VoightDiscriminantData
import TraceEuclidean.AnalyticTableBridge

/-!
# Certified finite-data bridge for Voight's enumeration

The archived data columns are checked in `VoightDiscriminantData`.  This
module isolates one source-facing completeness statement matching Voight's
enumeration through root discriminant fourteen, then derives the degree-five
through degree-nine minima and the empty degree-ten range used in Section 4.
-/

namespace TraceEuclidean

noncomputable section

/-- Source-facing completeness statement for the portion of Voight's
root-discriminant-fourteen enumeration used in Section 4.  The finite lists
themselves are imported and checked separately. -/
def VoightEnumerationUpToFourteenInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    let d := Module.finrank ℚ K.1
    5 ≤ d → d ≤ 10 → K.discriminant.natAbs ≤ 14 ^ d →
      K.discriminant.natAbs ∈ voightDiscriminants d

/-- The remaining source-facing completeness statement after the degree-five
minimum has been proved internally. -/
def VoightEnumerationSixToTenInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    let d := Module.finrank ℚ K.1
    6 ≤ d → d ≤ 10 → K.discriminant.natAbs ≤ 14 ^ d →
      K.discriminant.natAbs ∈ voightDiscriminants d

/-- Compatibility projection from the former degree-five through degree-ten
source statement. -/
theorem voightEnumerationSixToTenInput_of_fiveToTen
    (hEnum : VoightEnumerationUpToFourteenInput) :
    VoightEnumerationSixToTenInput := by
  intro K hreal
  dsimp only
  intro hd6 hd10 hdisc
  exact hEnum K hreal (by omega) hd10 hdisc

theorem voightDiscriminantsFive_minimum {D : ℕ}
    (hD : D ∈ voightDiscriminantsFive) : 14641 ≤ D := by
  have h := voightDiscriminantsFive_pairwise.rel_head hD
  change 14641 ≤ D at h
  exact h

theorem voightDiscriminantsSix_minimum {D : ℕ}
    (hD : D ∈ voightDiscriminantsSix) : 300125 ≤ D := by
  have h := voightDiscriminantsSix_pairwise.rel_head hD
  change 300125 ≤ D at h
  exact h

theorem voightDiscriminantsSeven_minimum {D : ℕ}
    (hD : D ∈ voightDiscriminantsSeven) : 20134393 ≤ D := by
  have h := voightDiscriminantsSeven_pairwise.rel_head hD
  change 20134393 ≤ D at h
  exact h

theorem voightDiscriminantsEight_minimum {D : ℕ}
    (hD : D ∈ voightDiscriminantsEight) : 282300416 ≤ D := by
  have h := voightDiscriminantsEight_pairwise.rel_head hD
  change 282300416 ≤ D at h
  exact h

theorem voightDiscriminantsNine_minimum {D : ℕ}
    (hD : D ∈ voightDiscriminantsNine) : 9685993193 ≤ D := by
  have h := voightDiscriminantsNine_pairwise.rel_head hD
  change 9685993193 ≤ D at h
  exact h

/-- Every imported row in degrees five through nine is bounded below by the
minimum used in the manuscript. -/
theorem voightDiscriminants_minimum {d D : ℕ}
    (hd5 : 5 ≤ d) (hd9 : d ≤ 9)
    (hD : D ∈ voightDiscriminants d) :
    minimumDiscriminant d ≤ D := by
  interval_cases d
  all_goals simp only [voightDiscriminants] at hD
  · simpa [minimumDiscriminant] using
      voightDiscriminantsFive_minimum hD
  · simpa [minimumDiscriminant] using
      voightDiscriminantsSix_minimum hD
  · simpa [minimumDiscriminant] using
      voightDiscriminantsSeven_minimum hD
  · simpa [minimumDiscriminant] using
      voightDiscriminantsEight_minimum hD
  · simpa [minimumDiscriminant] using
      voightDiscriminantsNine_minimum hD

/-- Voight completeness plus the checked table columns gives all exact minima
used in degrees five through nine. -/
theorem degreeFiveToNineMinimumInput_of_voightEnumeration
    (hEnum : VoightEnumerationUpToFourteenInput) :
    DegreeFiveToNineMinimumInput := by
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
  change (minimumDiscriminant d : ℝ) ≤ (D : ℝ)
  have hNat : minimumDiscriminant d ≤ D := by
    by_contra hnot
    have hDlt : D < minimumDiscriminant d := by omega
    have hD14 : D ≤ 14 ^ d := by
      interval_cases d <;>
        norm_num [minimumDiscriminant] at hDlt ⊢ <;> omega
    have hmem := hEnum K hreal hd5d (by omega) hD14
    exact hnot (voightDiscriminants_minimum hd5d hd9d hmem)
  exact_mod_cast hNat

/-- Voight completeness in degrees six through ten gives the residual exact
minima in degrees six through nine. -/
theorem degreeSixToNineMinimumInput_of_voightEnumeration
    (hEnum : VoightEnumerationSixToTenInput) :
    DegreeSixToNineMinimumInput := by
  intro K hreal
  dsimp only
  intro hd6 hd9
  let d := Module.finrank ℚ K.1
  let D := K.discriminant.natAbs
  have hd6d : 6 ≤ d := by simpa [d] using hd6
  have hd9d : d ≤ 9 := by simpa [d] using hd9
  have hdiscReal : ((|K.discriminant| : ℤ) : ℝ) = (D : ℝ) := by
    dsimp only [D]
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hdiscReal]
  change (minimumDiscriminant d : ℝ) ≤ (D : ℝ)
  have hNat : minimumDiscriminant d ≤ D := by
    by_contra hnot
    have hDlt : D < minimumDiscriminant d := by omega
    have hD14 : D ≤ 14 ^ d := by
      interval_cases d <;>
        norm_num [minimumDiscriminant] at hDlt ⊢ <;> omega
    have hmem := hEnum K hreal hd6d (by omega) hD14
    exact hnot (voightDiscriminants_minimum (by omega) hd9d hmem)
  exact_mod_cast hNat

/-- Voight completeness and the empty degree-ten data row prove the exact
degree-ten root-discriminant input used in Section 4. -/
theorem degreeTenRootDiscriminantInput_of_voightEnumeration
    (hEnum : VoightEnumerationUpToFourteenInput) :
    DegreeTenRootDiscriminantInput := by
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
  simp [hdegree, voightDiscriminants] at hmem

/-- The restricted degree-six through degree-ten completeness statement still
contains exactly the empty degree-ten row needed by Section 4. -/
theorem degreeTenRootDiscriminantInput_of_voightEnumerationSixToTen
    (hEnum : VoightEnumerationSixToTenInput) :
    DegreeTenRootDiscriminantInput := by
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
  simp [hdegree, voightDiscriminants] at hmem

end

end TraceEuclidean
