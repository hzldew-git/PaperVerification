import TraceEuclidean.DegreeFiveFrontierArithmetic

/-! Pure-kernel Euclidean-resultant certificate for safe quintic 148. -/

namespace TraceEuclidean
namespace DegreeFiveSafeRow148

open Polynomial
noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨288633, [-5, 7, 5, -6, -1, 1], 1⟩

def p0 : ℚ[X] :=
  C (-5) + C (7) * X ^ 1 + C (5) * X ^ 2 + C (-6) * X ^ 3 + C (-1) * X ^ 4 + C (1) * X ^ 5

def p1 : ℚ[X] :=
  C (7) + C (10) * X ^ 1 + C (-18) * X ^ 2 + C (-4) * X ^ 3 + C (5) * X ^ 4

def p2 : ℚ[X] :=
  C ((-118 : ℚ) / 25) + C (6) * X ^ 1 + C ((57 : ℚ) / 25) * X ^ 2 + C ((-64 : ℚ) / 25) * X ^ 3

def p3 : ℚ[X] :=
  C ((12625 : ℚ) / 2048) + C ((3775 : ℚ) / 2048) * X ^ 1 + C ((-24075 : ℚ) / 4096) * X ^ 2

def p4 : ℚ[X] :=
  C ((-73510912 : ℚ) / 23184225) + C ((87597056 : ℚ) / 23184225) * X ^ 1

def p5 : ℚ[X] :=
  C ((6691732414425 : ℚ) / 1873350639616)

def q0 : ℚ[X] :=
  C ((-1 : ℚ) / 25) + C ((1 : ℚ) / 5) * X ^ 1

def q1 : ℚ[X] :=
  C ((-725 : ℚ) / 4096) + C ((-125 : ℚ) / 64) * X ^ 1

def q2 : ℚ[X] :=
  C ((-145666048 : ℚ) / 579605625) + C ((262144 : ℚ) / 601875) * X ^ 1

def q3 : ℚ[X] :=
  C ((-6273876751588125 : ℚ) / 7673244219867136) + C ((-558160216875 : ℚ) / 358797541376) * X ^ 1

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
    p1.resultant p2 4 3 = ((4096 : ℚ) / 625) *
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
    _ = ((4096 : ℚ) / 625) * p2.resultant p3 3 2 := by
      norm_num [p2, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep2 :
    p2.resultant p3 3 2 = ((579605625 : ℚ) / 16777216) *
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
    _ = ((579605625 : ℚ) / 16777216) * p3.resultant p4 2 1 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 2 1 = ((7673244219867136 : ℚ) / 537508288850625) *
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
    _ = ((7673244219867136 : ℚ) / 537508288850625) * p4.resultant p5 1 0 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p4.resultant p5 1 0 = ((6691732414425 : ℚ) / 1873350639616) := by
  rw [show p5 = C ((6691732414425 : ℚ) / 1873350639616) by rfl]
  simpa [p4] using
    (Polynomial.resultant_C_right p4 1 0 ((6691732414425 : ℚ) / 1873350639616))

theorem resultant_eq : p0.resultant p1 5 4 = (288633 : ℚ) := by
  calc
    p0.resultant p1 5 4 = (25) * p1.resultant p2 4 3 := resultantStep0
    _ = (25) * (((4096 : ℚ) / 625) * p2.resultant p3 3 2) := by
      rw [resultantStep1]
    _ = (25) * ((4096 : ℚ) / 625) * p2.resultant p3 3 2 := by ring
    _ = (25) * ((4096 : ℚ) / 625) * (((579605625 : ℚ) / 16777216) * p3.resultant p4 2 1) := by
      rw [resultantStep2]
    _ = (25) * ((4096 : ℚ) / 625) * ((579605625 : ℚ) / 16777216) * p3.resultant p4 2 1 := by ring
    _ = (25) * ((4096 : ℚ) / 625) * ((579605625 : ℚ) / 16777216) * (((7673244219867136 : ℚ) / 537508288850625) * p4.resultant p5 1 0) := by
      rw [resultantStep3]
    _ = (25) * ((4096 : ℚ) / 625) * ((579605625 : ℚ) / 16777216) * ((7673244219867136 : ℚ) / 537508288850625) * p4.resultant p5 1 0 := by ring
    _ = 288633 := by
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
    have hget : ([-5, 7, 5, -6, -1, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([-5, 7, 5, -6, -1, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
end DegreeFiveSafeRow148
end TraceEuclidean
