import TraceEuclidean.CoveringVolume

/-!
Algebraic consequences of the Gram/covolume covering inequality.  These
lemmas isolate the order and exponent manipulations used in Section 3 of the
manuscript from the later number-field realization.
-/

namespace TraceEuclidean

noncomputable section

/--
If `D^n * V` is bounded by the square of the covering-ball volume and
`V ≥ 1`, then `D` satisfies the manuscript's discriminant bound.
-/
theorem discriminant_le_of_gram_volume_bound
    (D U t V : ℝ) (n d : ℕ) (hD : 0 ≤ D)
    (hU : 0 < U) (ht : 0 < t)
    (hn : 0 < n) (hV : 1 ≤ V)
    (hgram : D ^ n * V ≤ U ^ (2 : ℕ) * t ^ (n * d)) :
    D ≤ U ^ ((2 : ℝ) / n) * t ^ d := by
  apply le_of_pow_le_pow_left₀ hn.ne'
    (mul_nonneg (Real.rpow_nonneg hU.le _) (pow_nonneg ht.le d))
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hUeq : (U ^ ((2 : ℝ) / n)) ^ n = U ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU.le]
    rw [div_mul_cancel₀ _ hnR]
    exact Real.rpow_natCast U 2
  have hteq : (t ^ n) ^ d = (t ^ d) ^ n := by
    calc
      (t ^ n) ^ d = t ^ (n * d) := (pow_mul t n d).symm
      _ = t ^ (d * n) := by rw [Nat.mul_comm]
      _ = (t ^ d) ^ n := pow_mul t d n
  calc
    D ^ n ≤ D ^ n * V :=
      le_mul_of_one_le_right (pow_nonneg hD n) hV
    _ ≤ U ^ (2 : ℕ) * t ^ (n * d) := hgram
    _ = (U ^ ((2 : ℝ) / n) * t ^ d) ^ n := by
      rw [mul_pow, hUeq, pow_mul, hteq]

/-- Solve the same Gram/covolume inequality for the volume norm. -/
theorem volume_le_div_of_gram_volume_bound
    (D U t V : ℝ) (n d : ℕ) (hD : 0 < D)
    (hgram : D ^ n * V ≤ U ^ (2 : ℕ) * t ^ (n * d)) :
    V ≤ U ^ (2 : ℕ) * t ^ (n * d) / D ^ n := by
  apply (le_div_iff₀ (pow_pos hD n)).2
  simpa [mul_comm] using hgram

end

end TraceEuclidean
