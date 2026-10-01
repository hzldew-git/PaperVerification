import TraceEuclidean.AnalyticTableBridge

/-!
# Sensitivity of the degree-eleven integral-table cell

The online November 1976 Table 2 gives root-discriminant lower bound `14.034`
in degree eleven, while the frozen manuscript uses the later bound `14.083`.
This file checks inside Lean that the distinction is necessary for the
rank-two integral-table cell `(2, 11)`.
-/

namespace TraceEuclidean

noncomputable section

/-- Source-facing formulation of the optimized unconditional bound quoted by
Voight: every totally real field of degree at least eleven has root
discriminant strictly greater than `14.083`. -/
def OdlyzkoMartinetAtLeastElevenInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    11 ≤ Module.finrank ℚ K.1 →
      (14083 / 1000 : ℝ) ^ Module.finrank ℚ K.1 <
        ((|K.discriminant| : ℤ) : ℝ)

/-- The source-facing all-degrees bound specializes to the exact degree-eleven
interface used by Section 4. -/
theorem degreeElevenRootDiscriminantInput_of_odlyzkoMartinet
    (hBound : OdlyzkoMartinetAtLeastElevenInput) :
    DegreeElevenRootDiscriminantInput := by
  intro K hreal hdegree
  simpa [hdegree] using hBound K hreal (by omega)

/-- The Section 4 analytic quantity in degree eleven after replacing the
manuscript's `14.083` by the weaker online Table 2 value `14.034`. -/
def degreeElevenTableTwoAnalyticH (n : ℕ) : ℝ :=
  euclideanUnitBallVolume (n * 11) ^ (2 : ℕ) *
    (11 : ℝ) ^ (n * 11) / (14034 / 1000 : ℝ) ^ (n * 11)

/-- The weaker online Table 2 value admits the extra rank-two, degree-eleven
cell under the manuscript's necessary integral condition. -/
theorem degreeEleven_tableTwo_bound_admits_integral_pair :
    integralThreshold 2 11 ≤ degreeElevenTableTwoAnalyticH 2 := by
  have hpi : (333 / 106 : ℝ) ≤ Real.pi := by
    linarith [Real.pi_gt_d20]
  have hpow : (333 / 106 : ℝ) ^ (22 : ℕ) ≤ Real.pi ^ (22 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) hpi 22
  have hclosed :
      degreeElevenTableTwoAnalyticH 2 =
        (Real.pi ^ (22 : ℕ) * 11 ^ (22 : ℕ)) /
          (39916800 ^ (2 : ℕ) * (7017 / 500 : ℝ) ^ (22 : ℕ)) := by
    rw [degreeElevenTableTwoAnalyticH,
      unitBallVolume_sq_closed]
    norm_num [unitBallSquareCoefficient,
      piExponent, Nat.factorial]
    ring
  rw [hclosed]
  have hthreshold : integralThreshold 2 11 = (1 : ℝ) / 4194304 := by
    norm_num [integralThreshold]
  rw [hthreshold]
  calc
    (1 : ℝ) / 4194304 ≤
        ((333 / 106 : ℝ) ^ (22 : ℕ) * 11 ^ (22 : ℕ)) /
          (39916800 ^ (2 : ℕ) * (7017 / 500 : ℝ) ^ (22 : ℕ)) := by
      norm_num
    _ ≤
        (Real.pi ^ (22 : ℕ) * 11 ^ (22 : ℕ)) /
          (39916800 ^ (2 : ℕ) * (7017 / 500 : ℝ) ^ (22 : ℕ)) := by
      gcongr

/-- The optimized `14.083` value used in the manuscript excludes the
rank-two, degree-eleven cell. -/
theorem degreeEleven_optimized_bound_excludes_integral_pair :
    analyticH 2 11 < integralThreshold 2 11 := by
  have hiff := integral_analytic_grid_iff_mem 2 11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnot : (2, 11) ∉ integralAdmissiblePairs := by
    simp [integralAdmissiblePairs]
  exact lt_of_not_ge (fun h ↦ hnot (hiff.mp h))

end

end TraceEuclidean
