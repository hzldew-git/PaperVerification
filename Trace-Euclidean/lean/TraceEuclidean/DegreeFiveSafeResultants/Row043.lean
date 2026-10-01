import TraceEuclidean.DegreeFiveFrontierArithmetic

/-! Pure-kernel Euclidean-resultant certificate for safe quintic 043. -/

namespace TraceEuclidean
namespace DegreeFiveSafeRow043

open Polynomial
noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨70601, [-1, 7, 7, -5, -2, 1], 1⟩

def p0 : ℚ[X] :=
  C (-1) + C (7) * X ^ 1 + C (7) * X ^ 2 + C (-5) * X ^ 3 + C (-2) * X ^ 4 + C (1) * X ^ 5

def p1 : ℚ[X] :=
  C (7) + C (14) * X ^ 1 + C (-15) * X ^ 2 + C (-8) * X ^ 3 + C (5) * X ^ 4

def p2 : ℚ[X] :=
  C ((-11 : ℚ) / 25) + C ((168 : ℚ) / 25) * X ^ 1 + C (3) * X ^ 2 + C ((-66 : ℚ) / 25) * X ^ 3

def p3 : ℚ[X] :=
  C ((325 : ℚ) / 44) + C ((5275 : ℚ) / 726) * X ^ 1 + C ((-2375 : ℚ) / 484) * X ^ 2

def p4 : ℚ[X] :=
  C ((-408012 : ℚ) / 225625) + C ((947672 : ℚ) / 676875) * X ^ 1

def p5 : ℚ[X] :=
  C ((15929350625 : ℚ) / 1855541776)

def q0 : ℚ[X] :=
  C ((-2 : ℚ) / 25) + C ((1 : ℚ) / 5) * X ^ 1

def q1 : ℚ[X] :=
  C ((425 : ℚ) / 484) + C ((-125 : ℚ) / 66) * X ^ 1

def q2 : ℚ[X] :=
  C ((1044956 : ℚ) / 5640625) + C ((31944 : ℚ) / 59375) * X ^ 1

def q3 : ℚ[X] :=
  C ((595147984375 : ℚ) / 898082219584) + C ((-1607578125 : ℚ) / 458673248) * X ^ 1

lemma p0_degree : p0.natDegree = 5 := by
  unfold p0
  compute_degree <;> norm_num

lemma p1_degree : p1.natDegree = 4 := by
  unfold p1
  compute_degree <;> norm_num

lemma p2_degree : p2.natDegree = 3 := by
  unfold p2
  compute_degree <;> norm_num

lemma p3_degree : p3.natDegree = 2 := by
  unfold p3
  compute_degree <;> norm_num

lemma p4_degree : p4.natDegree = 1 := by
  unfold p4
  compute_degree <;> norm_num

lemma p5_degree : p5.natDegree = 0 := by
  unfold p5
  compute_degree <;> norm_num

lemma q0_degree : q0.natDegree = 1 := by
  unfold q0
  compute_degree <;> norm_num

lemma q1_degree : q1.natDegree = 1 := by
  unfold q1
  compute_degree <;> norm_num

lemma q2_degree : q2.natDegree = 1 := by
  unfold q2
  compute_degree <;> norm_num

lemma q3_degree : q3.natDegree = 1 := by
  unfold q3
  compute_degree <;> norm_num

lemma division0 : p0 = p2 + p1 * q0 := by
  apply Polynomial.funext
  intro x
  simp [p0, p1, p2, q0]
  ring

lemma division1 : p1 = p3 + p2 * q1 := by
  apply Polynomial.funext
  intro x
  simp [p1, p2, p3, q1]
  ring

lemma division2 : p2 = p4 + p3 * q2 := by
  apply Polynomial.funext
  intro x
  simp [p2, p3, p4, q2]
  ring

lemma division3 : p3 = p5 + p4 * q3 := by
  apply Polynomial.funext
  intro x
  simp [p3, p4, p5, q3]
  ring

lemma resultantStep0 :
    p0.resultant p1 5 4 = (25) *
      p1.resultant p2 4 3 := by
  calc
    p0.resultant p1 5 4 =
        (p2 + p1 * q0).resultant p1 5 4 := by
      rw [division0]
    _ = p2.resultant p1 5 4 :=
      Polynomial.resultant_add_mul_left p2 p1 q0 5 4
        (by rw [q0_degree])
        (by rw [p1_degree])
    _ = (-1 : ℚ) ^ (4 * 2) * p1.coeff 4 ^ 2 *
        p2.resultant p1 3 4 := by
      simpa using Polynomial.resultant_add_left_deg
        p2 p1 3 4 2
          (by rw [p2_degree])
    _ = (-1 : ℚ) ^ (4 * 2) * p1.coeff 4 ^ 2 *
        ((-1 : ℚ) ^ (3 * 4) *
          p1.resultant p2 4 3) := by
      rw [Polynomial.resultant_comm p2 p1 3 4]
    _ = (25) * p1.resultant p2 4 3 := by
      norm_num [p1, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep1 :
    p1.resultant p2 4 3 = ((4356 : ℚ) / 625) *
      p2.resultant p3 3 2 := by
  calc
    p1.resultant p2 4 3 =
        (p3 + p2 * q1).resultant p2 4 3 := by
      rw [division1]
    _ = p3.resultant p2 4 3 :=
      Polynomial.resultant_add_mul_left p3 p2 q1 4 3
        (by rw [q1_degree])
        (by rw [p2_degree])
    _ = (-1 : ℚ) ^ (3 * 2) * p2.coeff 3 ^ 2 *
        p3.resultant p2 2 3 := by
      simpa using Polynomial.resultant_add_left_deg
        p3 p2 2 3 2
          (by rw [p3_degree])
    _ = (-1 : ℚ) ^ (3 * 2) * p2.coeff 3 ^ 2 *
        ((-1 : ℚ) ^ (2 * 3) *
          p2.resultant p3 3 2) := by
      rw [Polynomial.resultant_comm p3 p2 2 3]
    _ = ((4356 : ℚ) / 625) * p2.resultant p3 3 2 := by
      norm_num [p2, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep2 :
    p2.resultant p3 3 2 = ((5640625 : ℚ) / 234256) *
      p3.resultant p4 2 1 := by
  calc
    p2.resultant p3 3 2 =
        (p4 + p3 * q2).resultant p3 3 2 := by
      rw [division2]
    _ = p4.resultant p3 3 2 :=
      Polynomial.resultant_add_mul_left p4 p3 q2 3 2
        (by rw [q2_degree])
        (by rw [p3_degree])
    _ = (-1 : ℚ) ^ (2 * 2) * p3.coeff 2 ^ 2 *
        p4.resultant p3 1 2 := by
      simpa using Polynomial.resultant_add_left_deg
        p4 p3 1 2 2
          (by rw [p4_degree])
    _ = (-1 : ℚ) ^ (2 * 2) * p3.coeff 2 ^ 2 *
        ((-1 : ℚ) ^ (1 * 2) *
          p3.resultant p4 2 1) := by
      rw [Polynomial.resultant_comm p4 p3 1 2]
    _ = ((5640625 : ℚ) / 234256) * p3.resultant p4 2 1 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 2 1 = ((898082219584 : ℚ) / 458159765625) *
      p4.resultant p5 1 0 := by
  calc
    p3.resultant p4 2 1 =
        (p5 + p4 * q3).resultant p4 2 1 := by
      rw [division3]
    _ = p5.resultant p4 2 1 :=
      Polynomial.resultant_add_mul_left p5 p4 q3 2 1
        (by rw [q3_degree])
        (by rw [p4_degree])
    _ = (-1 : ℚ) ^ (1 * 2) * p4.coeff 1 ^ 2 *
        p5.resultant p4 0 1 := by
      simpa using Polynomial.resultant_add_left_deg
        p5 p4 0 1 2
          (by rw [p5_degree])
    _ = (-1 : ℚ) ^ (1 * 2) * p4.coeff 1 ^ 2 *
        ((-1 : ℚ) ^ (0 * 1) *
          p4.resultant p5 1 0) := by
      rw [Polynomial.resultant_comm p5 p4 0 1]
    _ = ((898082219584 : ℚ) / 458159765625) * p4.resultant p5 1 0 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p4.resultant p5 1 0 = ((15929350625 : ℚ) / 1855541776) := by
  rw [show p5 = C ((15929350625 : ℚ) / 1855541776) by rfl]
  simpa [p4] using
    (Polynomial.resultant_C_right p4 1 0 ((15929350625 : ℚ) / 1855541776))

theorem resultant_eq : p0.resultant p1 5 4 = (70601 : ℚ) := by
  calc
    p0.resultant p1 5 4 = (25) * p1.resultant p2 4 3 := resultantStep0
    _ = (25) * (((4356 : ℚ) / 625) * p2.resultant p3 3 2) := by
      rw [resultantStep1]
    _ = (25) * ((4356 : ℚ) / 625) * p2.resultant p3 3 2 := by ring
    _ = (25) * ((4356 : ℚ) / 625) * (((5640625 : ℚ) / 234256) * p3.resultant p4 2 1) := by
      rw [resultantStep2]
    _ = (25) * ((4356 : ℚ) / 625) * ((5640625 : ℚ) / 234256) * p3.resultant p4 2 1 := by ring
    _ = (25) * ((4356 : ℚ) / 625) * ((5640625 : ℚ) / 234256) * (((898082219584 : ℚ) / 458159765625) * p4.resultant p5 1 0) := by
      rw [resultantStep3]
    _ = (25) * ((4356 : ℚ) / 625) * ((5640625 : ℚ) / 234256) * ((898082219584 : ℚ) / 458159765625) * p4.resultant p5 1 0 := by ring
    _ = 70601 := by
      rw [resultantLast]
      norm_num

lemma polynomial_map_eq :
    row.polynomial.map (Int.castRingHom ℚ) = p0 := by
  ext n
  rw [voightPolynomial_map_coeff]
  by_cases hn : n ≤ 5
  · interval_cases n <;>
      norm_num [row, p0, voightCoefficient, Polynomial.coeff_one,
        Polynomial.coeff_X]
  · have hn6 : 6 ≤ n := by omega
    have hget : ([-1, 7, 7, -5, -2, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([-1, 7, 7, -5, -2, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
      rw [hget]
      norm_num
    · rw [p0_degree]
      omega

lemma derivative_eq : p0.derivative = p1 := by
  apply Polynomial.funext
  intro x
  simp [p0, p1]
  ring

lemma row_resultant :
    let polynomial := row.polynomial.map (Int.castRingHom ℚ)
    polynomial.resultant polynomial.derivative 5 4 =
      voightExpectedResultant 5 row := by
  simp only
  rw [polynomial_map_eq, derivative_eq]
  norm_num [voightExpectedResultant, row]
  exact resultant_eq

theorem polynomial_discr :
    row.polynomial.discr = (row.fieldDiscriminant : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 5 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h

theorem quotient_safe :
    discriminantQuotientSafe 14641 row.fieldDiscriminant = true := by
  norm_num [row, discriminantQuotientSafe]
  intro index hindex
  interval_cases index <;> norm_num

theorem properties :
    row.polynomial.discr = (row.fieldDiscriminant : ℤ) ∧
      discriminantQuotientSafe 14641 row.fieldDiscriminant = true :=
  ⟨polynomial_discr, quotient_safe⟩

end
end DegreeFiveSafeRow043
end TraceEuclidean
