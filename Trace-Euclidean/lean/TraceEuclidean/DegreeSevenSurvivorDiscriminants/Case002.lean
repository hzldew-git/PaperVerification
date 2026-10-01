import TraceEuclidean.DegreeSevenSurvivorDiscriminant

/-! Pure-kernel resultant certificate for retained septic 002. -/

namespace TraceEuclidean
namespace DegreeSevenSurvivorDiscriminantCase002

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨374305189, [1, -3, -4, 12, 6, -9, -3, 1], 1⟩

def p0 : ℚ[X] :=
  C (1 : ℚ) + C (-3 : ℚ) * X ^ 1 + C (-4 : ℚ) * X ^ 2 + C (12 : ℚ) * X ^ 3 + C (6 : ℚ) * X ^ 4 + C (-9 : ℚ) * X ^ 5 + C (-3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7

def p1 : ℚ[X] :=
  C (-3 : ℚ) + C (-8 : ℚ) * X ^ 1 + C (36 : ℚ) * X ^ 2 + C (24 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6

def p2 : ℚ[X] :=
  C ((40 : ℚ) / 49) + C ((-150 : ℚ) / 49) * X ^ 1 + C ((-32 : ℚ) / 49) * X ^ 2 + C ((408 : ℚ) / 49) * X ^ 3 + C ((-9 : ℚ) / 49) * X ^ 4 + C ((-180 : ℚ) / 49) * X ^ 5

def p3 : ℚ[X] :=
  C ((-637 : ℚ) / 90) + C ((637 : ℚ) / 72) * X ^ 1 + C ((15043 : ℚ) / 450) * X ^ 2 + C ((-8477 : ℚ) / 450) * X ^ 3 + C ((-33859 : ℚ) / 1200) * X ^ 4

def p4 : ℚ[X] :=
  C ((5783600 : ℚ) / 23396569) + C ((-33418400 : ℚ) / 23396569) * X ^ 1 + C ((20662400 : ℚ) / 23396569) * X ^ 2 + C ((57546400 : ℚ) / 23396569) * X ^ 3

def p5 : ℚ[X] :=
  C ((-57771205916473 : ℚ) / 9313841680200) + C ((27431705065723 : ℚ) / 4139485191200) * X ^ 1 + C ((375712188923239 : ℚ) / 18627683360400) * X ^ 2

def p6 : ℚ[X] :=
  C ((1630625619475638622800 : ℚ) / 6033348261682797778009) + C ((-600398036523107397000 : ℚ) / 861906894526113968287) * X ^ 1

def p7 : ℚ[X] :=
  C ((-46088031865142879190743648749 : ℚ) / 77406899244837048572400090000)

def q0 : ℚ[X] :=
  C ((-3 : ℚ) / 49) + C ((1 : ℚ) / 7) * X ^ 1

def q1 : ℚ[X] :=
  C ((17983 : ℚ) / 3600) + C ((-343 : ℚ) / 180) * X ^ 1

def q2 : ℚ[X] :=
  C ((-92185200 : ℚ) / 1146431881) + C ((216000 : ℚ) / 1659091) * X ^ 1

def q3 : ℚ[X] :=
  C ((-13187929846512617 : ℚ) / 3725536672080000) + C ((-792184429771 : ℚ) / 69055680000) * X ^ 1

def q4 : ℚ[X] :=
  C ((525022696081041139861920000 : ℚ) / 141159648905491634326234251121) + C ((1071956117730922560000 : ℚ) / 8790376152283596966991) * X ^ 1

def q5 : ℚ[X] :=
  C ((-29915652253004334600837943502394597939524737 : ℚ) / 1441911209043210415301543731184462436000000) + C ((-323828925990437561557866315923321593 : ℚ) / 11184024514558319129199056878800000) * X ^ 1

lemma p0_degree : p0.natDegree = 7 := by
  unfold p0
  compute_degree <;> norm_num

lemma p1_degree : p1.natDegree = 6 := by
  unfold p1
  compute_degree <;> norm_num

lemma p2_degree : p2.natDegree = 5 := by
  unfold p2
  compute_degree <;> norm_num

lemma p3_degree : p3.natDegree = 4 := by
  unfold p3
  compute_degree <;> norm_num

lemma p4_degree : p4.natDegree = 3 := by
  unfold p4
  compute_degree <;> norm_num

lemma p5_degree : p5.natDegree = 2 := by
  unfold p5
  compute_degree <;> norm_num

lemma p6_degree : p6.natDegree = 1 := by
  unfold p6
  compute_degree <;> norm_num

lemma p7_degree : p7.natDegree = 0 := by
  unfold p7
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

lemma q4_degree : q4.natDegree = 1 := by
  unfold q4
  compute_degree <;> norm_num

lemma q5_degree : q5.natDegree = 1 := by
  unfold q5
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

lemma division4 : p4 = p6 + p5 * q4 := by
  apply Polynomial.funext
  intro x
  simp [p4, p5, p6, q4]
  ring

lemma division5 : p5 = p7 + p6 * q5 := by
  apply Polynomial.funext
  intro x
  simp [p5, p6, p7, q5]
  ring

lemma resultantStep0 :
    p0.resultant p1 7 6 = (49 : ℚ) *
      p1.resultant p2 6 5 := by
  calc
    p0.resultant p1 7 6 =
        (p2 + p1 * q0).resultant p1 7 6 := by
      rw [division0]
    _ = p2.resultant p1 7 6 :=
      Polynomial.resultant_add_mul_left p2 p1 q0 7 6
        (by rw [q0_degree])
        (by rw [p1_degree])
    _ = (-1 : ℚ) ^ (6 * 2) * p1.coeff 6 ^ 2 *
        p2.resultant p1 5 6 := by
      simpa using Polynomial.resultant_add_left_deg
        p2 p1 5 6 2
          (by rw [p2_degree])
    _ = (-1 : ℚ) ^ (6 * 2) * p1.coeff 6 ^ 2 *
        ((-1 : ℚ) ^ (5 * 6) *
          p1.resultant p2 6 5) := by
      rw [Polynomial.resultant_comm p2 p1 5 6]
    _ = (49 : ℚ) *
        p1.resultant p2 6 5 := by
      norm_num [p1, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep1 :
    p1.resultant p2 6 5 = ((32400 : ℚ) / 2401) *
      p2.resultant p3 5 4 := by
  calc
    p1.resultant p2 6 5 =
        (p3 + p2 * q1).resultant p2 6 5 := by
      rw [division1]
    _ = p3.resultant p2 6 5 :=
      Polynomial.resultant_add_mul_left p3 p2 q1 6 5
        (by rw [q1_degree])
        (by rw [p2_degree])
    _ = (-1 : ℚ) ^ (5 * 2) * p2.coeff 5 ^ 2 *
        p3.resultant p2 4 5 := by
      simpa using Polynomial.resultant_add_left_deg
        p3 p2 4 5 2
          (by rw [p3_degree])
    _ = (-1 : ℚ) ^ (5 * 2) * p2.coeff 5 ^ 2 *
        ((-1 : ℚ) ^ (4 * 5) *
          p2.resultant p3 5 4) := by
      rw [Polynomial.resultant_comm p3 p2 4 5]
    _ = ((32400 : ℚ) / 2401) *
        p2.resultant p3 5 4 := by
      norm_num [p2, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep2 :
    p2.resultant p3 5 4 = ((1146431881 : ℚ) / 1440000) *
      p3.resultant p4 4 3 := by
  calc
    p2.resultant p3 5 4 =
        (p4 + p3 * q2).resultant p3 5 4 := by
      rw [division2]
    _ = p4.resultant p3 5 4 :=
      Polynomial.resultant_add_mul_left p4 p3 q2 5 4
        (by rw [q2_degree])
        (by rw [p3_degree])
    _ = (-1 : ℚ) ^ (4 * 2) * p3.coeff 4 ^ 2 *
        p4.resultant p3 3 4 := by
      simpa using Polynomial.resultant_add_left_deg
        p4 p3 3 4 2
          (by rw [p4_degree])
    _ = (-1 : ℚ) ^ (4 * 2) * p3.coeff 4 ^ 2 *
        ((-1 : ℚ) ^ (3 * 4) *
          p3.resultant p4 4 3) := by
      rw [Polynomial.resultant_comm p4 p3 3 4]
    _ = ((1146431881 : ℚ) / 1440000) *
        p3.resultant p4 4 3 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 4 3 = ((3311588152960000 : ℚ) / 547399440971761) *
      p4.resultant p5 3 2 := by
  calc
    p3.resultant p4 4 3 =
        (p5 + p4 * q3).resultant p4 4 3 := by
      rw [division3]
    _ = p5.resultant p4 4 3 :=
      Polynomial.resultant_add_mul_left p5 p4 q3 4 3
        (by rw [q3_degree])
        (by rw [p4_degree])
    _ = (-1 : ℚ) ^ (3 * 2) * p4.coeff 3 ^ 2 *
        p5.resultant p4 2 3 := by
      simpa using Polynomial.resultant_add_left_deg
        p5 p4 2 3 2
          (by rw [p5_degree])
    _ = (-1 : ℚ) ^ (3 * 2) * p4.coeff 3 ^ 2 *
        ((-1 : ℚ) ^ (2 * 3) *
          p4.resultant p5 3 2) := by
      rw [Polynomial.resultant_comm p5 p4 2 3]
    _ = ((3311588152960000 : ℚ) / 547399440971761) *
        p4.resultant p5 3 2 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep4 :
    p4.resultant p5 3 2 = ((141159648905491634326234251121 : ℚ) / 346990587375323036288160000) *
      p5.resultant p6 2 1 := by
  calc
    p4.resultant p5 3 2 =
        (p6 + p5 * q4).resultant p5 3 2 := by
      rw [division4]
    _ = p6.resultant p5 3 2 :=
      Polynomial.resultant_add_mul_left p6 p5 q4 3 2
        (by rw [q4_degree])
        (by rw [p5_degree])
    _ = (-1 : ℚ) ^ (2 * 2) * p5.coeff 2 ^ 2 *
        p6.resultant p5 1 2 := by
      simpa using Polynomial.resultant_add_left_deg
        p6 p5 1 2 2
          (by rw [p6_degree])
    _ = (-1 : ℚ) ^ (2 * 2) * p5.coeff 2 ^ 2 *
        ((-1 : ℚ) ^ (1 * 2) *
          p5.resultant p6 2 1) := by
      rw [Polynomial.resultant_comm p6 p5 1 2]
    _ = ((141159648905491634326234251121 : ℚ) / 346990587375323036288160000) *
        p5.resultant p6 2 1 := by
      norm_num [p5, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep5 :
    p5.resultant p6 2 1 = ((360477802260802603825385932796115609000000 : ℚ) / 742883494831649748869321248782694441714369) *
      p6.resultant p7 1 0 := by
  calc
    p5.resultant p6 2 1 =
        (p7 + p6 * q5).resultant p6 2 1 := by
      rw [division5]
    _ = p7.resultant p6 2 1 :=
      Polynomial.resultant_add_mul_left p7 p6 q5 2 1
        (by rw [q5_degree])
        (by rw [p6_degree])
    _ = (-1 : ℚ) ^ (1 * 2) * p6.coeff 1 ^ 2 *
        p7.resultant p6 0 1 := by
      simpa using Polynomial.resultant_add_left_deg
        p7 p6 0 1 2
          (by rw [p7_degree])
    _ = (-1 : ℚ) ^ (1 * 2) * p6.coeff 1 ^ 2 *
        ((-1 : ℚ) ^ (0 * 1) *
          p6.resultant p7 1 0) := by
      rw [Polynomial.resultant_comm p7 p6 0 1]
    _ = ((360477802260802603825385932796115609000000 : ℚ) / 742883494831649748869321248782694441714369) *
        p6.resultant p7 1 0 := by
      norm_num [p6, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p6.resultant p7 1 0 = ((-46088031865142879190743648749 : ℚ) / 77406899244837048572400090000) := by
  rw [show p7 = C ((-46088031865142879190743648749 : ℚ) / 77406899244837048572400090000) by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 ((-46088031865142879190743648749 : ℚ) / 77406899244837048572400090000))

theorem resultant_eq : p0.resultant p1 7 6 = (-374305189 : ℚ) := by
  rw [resultantStep0, resultantStep1, resultantStep2, resultantStep3, resultantStep4, resultantStep5, resultantLast]
  norm_num

lemma polynomial_map_eq :
    row.polynomial.map (Int.castRingHom ℚ) = p0 := by
  ext n
  rw [voightPolynomial_map_coeff]
  by_cases hn : n ≤ 7
  · interval_cases n <;>
      norm_num [row, p0, voightCoefficient, Polynomial.coeff_one,
        Polynomial.coeff_X]
  · have hn8 : 8 ≤ n := by omega
    have hget : ([1, -3, -4, 12, 6, -9, -3, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([1, -3, -4, 12, 6, -9, -3, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
    polynomial.resultant polynomial.derivative 7 6 =
      voightExpectedResultant 7 row := by
  simp only
  rw [polynomial_map_eq, derivative_eq]
  norm_num [voightExpectedResultant, row]
  exact resultant_eq

theorem polynomial_discr :
    row.polynomial.discr = (374305189 : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h


theorem kernel_squarefree : Squarefree 374305189 := by
  have hp0 : Prime (1087 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp1 : Prime (344347 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  rw [show 374305189 = 1087 * (344347) by norm_num]
  exact (Nat.squarefree_mul (m := 1087) (n := 344347) (by norm_num)).mpr ⟨hp0.squarefree, hp1.squarefree⟩

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  { coefficients := [1, -3, -4, 12, 6, -9, -3, 1]
    discriminant := 374305189
    squarePart := 1
    kernel := 374305189
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = (374305189 : ℤ)
      exact polynomial_discr }


end

end DegreeSevenSurvivorDiscriminantCase002
end TraceEuclidean
