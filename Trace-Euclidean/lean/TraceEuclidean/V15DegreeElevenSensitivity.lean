import TraceEuclidean.V15AnalyticTableBridge

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
def V15OdlyzkoMartinetAtLeastElevenInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    11 ≤ Module.finrank ℚ K.1 →
      (14083 / 1000 : ℝ) ^ Module.finrank ℚ K.1 <
        ((|K.discriminant| : ℤ) : ℝ)

/-- The source-facing all-degrees bound specializes to the exact degree-eleven
interface used by Section 4. -/
theorem v15_degreeElevenRootDiscriminantInput_of_odlyzkoMartinet
    (hBound : V15OdlyzkoMartinetAtLeastElevenInput) :
    V15DegreeElevenRootDiscriminantInput := by
  intro K hreal hdegree
  simpa [hdegree] using hBound K hreal (by omega)

/-- The Section 4 analytic quantity in degree eleven after replacing the
manuscript's `14.083` by the weaker online Table 2 value `14.034`. -/
def v15DegreeElevenTableTwoAnalyticH (n : ℕ) : ℝ :=
  euclideanUnitBallVolume (n * 11) ^ (2 : ℕ) *
    (11 : ℝ) ^ (n * 11) / (14034 / 1000 : ℝ) ^ (n * 11)

/-- The weaker online Table 2 value admits the extra rank-two, degree-eleven
cell under the manuscript's necessary integral condition. -/
theorem v15_degreeEleven_tableTwo_bound_admits_integral_pair :
    v15IntegralThreshold 2 11 ≤ v15DegreeElevenTableTwoAnalyticH 2 := by
  have hpi : (333 / 106 : ℝ) ≤ Real.pi := by
    linarith [Real.pi_gt_d20]
  have hpow : (333 / 106 : ℝ) ^ (22 : ℕ) ≤ Real.pi ^ (22 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) hpi 22
  have hclosed :
      v15DegreeElevenTableTwoAnalyticH 2 =
        (Real.pi ^ (22 : ℕ) * 11 ^ (22 : ℕ)) /
          (39916800 ^ (2 : ℕ) * (7017 / 500 : ℝ) ^ (22 : ℕ)) := by
    rw [v15DegreeElevenTableTwoAnalyticH,
      v15_unitBallVolume_sq_closed]
    norm_num [v15UnitBallSquareCoefficient,
      v15PiExponent, Nat.factorial]
    ring
  rw [hclosed]
  have hthreshold : v15IntegralThreshold 2 11 = (1 : ℝ) / 4194304 := by
    norm_num [v15IntegralThreshold]
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
theorem v15_degreeEleven_optimized_bound_excludes_integral_pair :
    v15AnalyticH 2 11 < v15IntegralThreshold 2 11 := by
  have hiff := v15_integral_analytic_grid_iff_mem 2 11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnot : (2, 11) ∉ v15IntegralAdmissiblePairs := by
    simp [v15IntegralAdmissiblePairs]
  exact lt_of_not_ge (fun h ↦ hnot (hiff.mp h))

end

end TraceEuclidean
