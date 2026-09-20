import TraceEuclidean.V15QuadraticSieve

/-!
Exact rational values of the binary covering expression for the six surviving
reduced Gram matrices. This checks the formula's arithmetic; the assertion
that it is the full covering radius is a separate geometric obligation.
-/

namespace TraceEuclidean

def v15GramRadius (a b c : ℕ) : ℚ :=
  (a : ℚ) * c * ((a : ℚ) + c - 2 * b) /
    (4 * ((a : ℚ) * c - (b : ℚ) ^ 2))

theorem v15_six_radius_values :
    v15GramRadius 2 0 4 = 3 / 2 ∧
    v15GramRadius 4 2 4 = 4 / 3 ∧
    v15GramRadius 2 1 3 = 9 / 10 ∧
    v15GramRadius 4 2 6 = 9 / 5 ∧
    v15GramRadius 2 1 7 = 49 / 26 ∧
    v15GramRadius 5 2 5 = 25 / 14 := by
  norm_num [v15GramRadius]

theorem v15_six_radius_values_lt_two :
    v15GramRadius 2 0 4 < 2 ∧
    v15GramRadius 4 2 4 < 2 ∧
    v15GramRadius 2 1 3 < 2 ∧
    v15GramRadius 4 2 6 < 2 ∧
    v15GramRadius 2 1 7 < 2 ∧
    v15GramRadius 5 2 5 < 2 := by
  norm_num [v15GramRadius]

end TraceEuclidean
