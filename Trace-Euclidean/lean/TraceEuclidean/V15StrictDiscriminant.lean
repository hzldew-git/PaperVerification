import TraceEuclidean.V15FinitenessAssembly

/-! Strict root-discriminant inequalities for the varying trace threshold `t = d`. -/

namespace TraceEuclidean

noncomputable section

theorem v15_ball_degree_bound_strict (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (c : ℝ) (hc : 0 < c) :
    euclideanUnitBallVolume (n * d) ^ (2 : ℕ) *
      (c * (d : ℝ)) ^ (n * d) <
        ((2 * c * Real.pi * Real.exp 1) / (n : ℝ)) ^ (n * d) := by
  have hU := euclideanUnitBallVolume_sq_lt (n * d) (Nat.mul_pos hn hd)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  calc
    euclideanUnitBallVolume (n * d) ^ (2 : ℕ) *
        (c * (d : ℝ)) ^ (n * d) <
        ((2 * Real.pi * Real.exp 1) / ((n : ℝ) * d)) ^ (n * d) *
          (c * (d : ℝ)) ^ (n * d) := by
            exact mul_lt_mul_of_pos_right
              (by simpa only [Nat.cast_mul] using hU) (pow_pos (by positivity) _)
    _ = ((2 * c * Real.pi * Real.exp 1) / (n : ℝ)) ^ (n * d) := by
      rw [← mul_pow]
      congr 1
      field_simp

private theorem root_bound_of_power_bound
    (D K : ℝ) (n d : ℕ)
    (hD : 0 < D) (hK : 0 < K) (hn : 0 < n) (hd : 0 < d)
    (hbound : D ^ n < (K / (n : ℝ)) ^ (n * d)) :
    (n : ℝ) * D ^ (1 / (d : ℝ)) < K := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hrootpow :
      (D ^ (1 / (d : ℝ))) ^ (n * d) = D ^ n := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hD.le]
    have hexp : (1 / (d : ℝ)) * (↑(n * d) : ℝ) = n := by
      push_cast
      field_simp
    rw [hexp, Real.rpow_natCast]
  have hmul :
      ((n : ℝ) * D ^ (1 / (d : ℝ))) ^ (n * d) =
        (n : ℝ) ^ (n * d) * D ^ n := by
    rw [mul_pow, hrootpow]
  have hright :
      (n : ℝ) ^ (n * d) * (K / (n : ℝ)) ^ (n * d) = K ^ (n * d) := by
    rw [← mul_pow]
    congr 1
    field_simp
  apply lt_of_pow_lt_pow_left₀ (n * d) hK.le
  rw [hmul, ← hright]
  exact mul_lt_mul_of_pos_left hbound (pow_pos hnR _)

theorem v15_classic_root_discriminant_lt
    (c : GlobalLatticeClass)
    (hE : c.IsClassicTraceEuclidean (c.degree : ℝ)) :
    (c.rank : ℝ) *
      (((|c.fieldCode.discriminant| : ℤ) : ℝ) ^ (1 / (c.degree : ℝ))) <
        2 * Real.pi * Real.exp 1 := by
  have hn := c.rank_pos
  have hd := c.degree_pos_v15
  have hdisc := GlobalFiniteness.classic_discriminant_pow_le_trace
    (c.degree : ℝ) c.rank c.degree c (by exact_mod_cast hd)
    ⟨hE, rfl, rfl⟩
  have hvol := v15_ball_degree_bound_strict c.rank c.degree hn hd 1 (by norm_num)
  have hD : 0 < ((|c.fieldCode.discriminant| : ℤ) : ℝ) :=
    (totallyRealMinkowskiDiscriminantLowerBound_pos hd).trans_le
      c.minkowski_discriminant_lower_bound
  apply root_bound_of_power_bound _ _ c.rank c.degree hD (by positivity) hn hd
  exact hdisc.trans_lt (by simpa using hvol)

theorem v15_integral_root_discriminant_lt
    (c : GlobalLatticeClass)
    (hE : c.IsIntegralTraceEuclidean (c.degree : ℝ)) :
    (c.rank : ℝ) *
      (((|c.fieldCode.discriminant| : ℤ) : ℝ) ^ (1 / (c.degree : ℝ))) <
        4 * Real.pi * Real.exp 1 := by
  have hn := c.rank_pos
  have hd := c.degree_pos_v15
  have hdisc := GlobalFiniteness.integral_discriminant_pow_le_trace
    (c.degree : ℝ) c.rank c.degree c (by exact_mod_cast hd)
    ⟨hE, rfl, rfl⟩
  have hvol := v15_ball_degree_bound_strict c.rank c.degree hn hd 2 (by norm_num)
  have hD : 0 < ((|c.fieldCode.discriminant| : ℤ) : ℝ) :=
    (totallyRealMinkowskiDiscriminantLowerBound_pos hd).trans_le
      c.minkowski_discriminant_lower_bound
  apply root_bound_of_power_bound _ _ c.rank c.degree hD (by positivity) hn hd
  have hbase : 2 * 2 * Real.pi * Real.exp 1 = (4 : ℝ) * Real.pi * Real.exp 1 := by
    ring
  exact hdisc.trans_lt (by simpa only [hbase] using hvol)

end

end TraceEuclidean
