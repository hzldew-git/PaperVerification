import TraceEuclidean.QuadraticSieve

/-!
Exact rational values of the binary covering expression for the six surviving
reduced Gram matrices. This checks the formula's arithmetic; the assertion
that it is the full covering radius is a separate geometric obligation.
-/

namespace TraceEuclidean

def gramRadius (a b c : ℕ) : ℚ :=
  (a : ℚ) * c * ((a : ℚ) + c - 2 * b) /
    (4 * ((a : ℚ) * c - (b : ℚ) ^ 2))

theorem six_radius_values :
    gramRadius 2 0 4 = 3 / 2 ∧
    gramRadius 4 2 4 = 4 / 3 ∧
    gramRadius 2 1 3 = 9 / 10 ∧
    gramRadius 4 2 6 = 9 / 5 ∧
    gramRadius 2 1 7 = 49 / 26 ∧
    gramRadius 5 2 5 = 25 / 14 := by
  norm_num [gramRadius]

theorem six_radius_values_lt_two :
    gramRadius 2 0 4 < 2 ∧
    gramRadius 4 2 4 < 2 ∧
    gramRadius 2 1 3 < 2 ∧
    gramRadius 4 2 6 < 2 ∧
    gramRadius 2 1 7 < 2 ∧
    gramRadius 5 2 5 < 2 := by
  norm_num [gramRadius]

end TraceEuclidean
