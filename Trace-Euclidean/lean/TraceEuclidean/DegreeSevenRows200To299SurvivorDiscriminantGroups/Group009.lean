import TraceEuclidean.DegreeSevenSurvivorDiscriminant

/-! Pure-kernel resultant certificate for retained septic 046. -/

namespace TraceEuclidean
namespace DegreeSevenRows200To299SurvivorDiscriminantCase046

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨25007664373, [1, -4, -5, 15, 8, -9, -3, 1], 1⟩

def p0 : ℚ[X] :=
  C (1 : ℚ) + C (-4 : ℚ) * X ^ 1 + C (-5 : ℚ) * X ^ 2 + C (15 : ℚ) * X ^ 3 + C (8 : ℚ) * X ^ 4 + C (-9 : ℚ) * X ^ 5 + C (-3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7

def p1 : ℚ[X] :=
  C (-4 : ℚ) + C (-10 : ℚ) * X ^ 1 + C (45 : ℚ) * X ^ 2 + C (32 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6

def p2 : ℚ[X] :=
  C ((37 : ℚ) / 49) + C ((-198 : ℚ) / 49) * X ^ 1 + C ((-40 : ℚ) / 49) * X ^ 2 + C ((516 : ℚ) / 49) * X ^ 3 + C ((33 : ℚ) / 49) * X ^ 4 + C ((-180 : ℚ) / 49) * X ^ 5

def p3 : ℚ[X] :=
  C ((-80311 : ℚ) / 10800) + C ((17689 : ℚ) / 1800) * X ^ 1 + C ((5537 : ℚ) / 135) * X ^ 2 + C ((-5243 : ℚ) / 300) * X ^ 3 + C ((-100793 : ℚ) / 3600) * X ^ 4

def p4 : ℚ[X] :=
  C ((-618000 : ℚ) / 18848291) + C ((-419623200 : ℚ) / 207331201) * X ^ 1 + C ((464412000 : ℚ) / 207331201) * X ^ 2 + C ((683690400 : ℚ) / 207331201) * X ^ 3

def p5 : ℚ[X] :=
  C ((-4335948298861949 : ℚ) / 584290703815200) + C ((408810064189373 : ℚ) / 38952713587680) * X ^ 1 + C ((3328043740829423 : ℚ) / 146072675953800) * X ^ 2

def p6 : ℚ[X] :=
  C ((10792915082228671913250 : ℚ) / 53421169064051771188129) + C ((-68483978758174051351350 : ℚ) / 53421169064051771188129) * X ^ 1

def p7 : ℚ[X] :=
  C ((-1335938666367097233368921473828117 : ℚ) / 256861473423457221509753401784100)

def q0 : ℚ[X] :=
  C ((-3 : ℚ) / 49) + C ((1 : ℚ) / 7) * X ^ 1

def q1 : ℚ[X] :=
  C ((49147 : ℚ) / 10800) + C ((-343 : ℚ) / 180) * X ^ 1

def q2 : ℚ[X] :=
  C ((-1076403600 : ℚ) / 10159228849) + C ((648000 : ℚ) / 4938857) * X ^ 1

def q3 : ℚ[X] :=
  C ((327791795848330429 : ℚ) / 701148844578240000) + C ((-20897533742393 : ℚ) / 2461285440000) * X ^ 1

def q4 : ℚ[X] :=
  C ((50068511179190242708908600000 : ℚ) / 1582267877267699949515997501847) + C ((99868486251923903520000 : ℚ) / 690007305766697006727023) * X ^ 1

def q5 : ℚ[X] :=
  C ((-6107531352859283208129020060361969994872811787 : ℚ) / 555858411442967073263566160962311912432216000) + C ((-177787987331407902447178092976631519567 : ℚ) / 10003638037169680736025469540167630000) * X ^ 1

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
    p2.resultant p3 5 4 = ((10159228849 : ℚ) / 12960000) *
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
    _ = ((10159228849 : ℚ) / 12960000) *
        p3.resultant p4 4 3 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 4 3 = ((467432563052160000 : ℚ) / 42986226908102401) *
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
    _ = ((467432563052160000 : ℚ) / 42986226908102401) *
        p4.resultant p5 3 2 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep4 :
    p4.resultant p5 3 2 = ((11075875140873899646611982512929 : ℚ) / 21337226660303860739734440000) *
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
    _ = ((11075875140873899646611982512929 : ℚ) / 21337226660303860739734440000) *
        p5.resultant p6 2 1 := by
      norm_num [p5, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep5 :
    p5.resultant p6 2 1 = ((4690055346550034680661339483119506761146822500 : ℚ) / 2853821304170001990883369597938432288310520641) *
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
    _ = ((4690055346550034680661339483119506761146822500 : ℚ) / 2853821304170001990883369597938432288310520641) *
        p6.resultant p7 1 0 := by
      norm_num [p6, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p6.resultant p7 1 0 = ((-1335938666367097233368921473828117 : ℚ) / 256861473423457221509753401784100) := by
  rw [show p7 = C ((-1335938666367097233368921473828117 : ℚ) / 256861473423457221509753401784100) by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 ((-1335938666367097233368921473828117 : ℚ) / 256861473423457221509753401784100))

theorem resultant_eq : p0.resultant p1 7 6 = (-25007664373 : ℚ) := by
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
    have hget : ([1, -4, -5, 15, 8, -9, -3, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([1, -4, -5, 15, 8, -9, -3, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
    row.polynomial.discr = (25007664373 : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h


theorem kernel_squarefree : Squarefree 25007664373 := by
  have hp0 : Prime (25007664373 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  rw [show 25007664373 = 25007664373 by norm_num]
  exact hp0.squarefree

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  { coefficients := [1, -4, -5, 15, 8, -9, -3, 1]
    discriminant := 25007664373
    squarePart := 1
    kernel := 25007664373
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = (25007664373 : ℤ)
      exact polynomial_discr }


end

end DegreeSevenRows200To299SurvivorDiscriminantCase046
end TraceEuclidean

/-! Pure-kernel resultant certificate for retained septic 047. -/

namespace TraceEuclidean
namespace DegreeSevenRows200To299SurvivorDiscriminantCase047

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨18390439888, [1, -4, -4, 15, 8, -9, -3, 1], 1⟩

def p0 : ℚ[X] :=
  C (1 : ℚ) + C (-4 : ℚ) * X ^ 1 + C (-4 : ℚ) * X ^ 2 + C (15 : ℚ) * X ^ 3 + C (8 : ℚ) * X ^ 4 + C (-9 : ℚ) * X ^ 5 + C (-3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7

def p1 : ℚ[X] :=
  C (-4 : ℚ) + C (-8 : ℚ) * X ^ 1 + C (45 : ℚ) * X ^ 2 + C (32 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6

def p2 : ℚ[X] :=
  C ((37 : ℚ) / 49) + C ((-192 : ℚ) / 49) * X ^ 1 + C ((-5 : ℚ) / 49) * X ^ 2 + C ((516 : ℚ) / 49) * X ^ 3 + C ((33 : ℚ) / 49) * X ^ 4 + C ((-180 : ℚ) / 49) * X ^ 5

def p3 : ℚ[X] :=
  C ((-80311 : ℚ) / 10800) + C ((1127 : ℚ) / 100) * X ^ 1 + C ((16415 : ℚ) / 432) * X ^ 2 + C ((-3626 : ℚ) / 225) * X ^ 3 + C ((-100793 : ℚ) / 3600) * X ^ 4

def p4 : ℚ[X] :=
  C ((276000 : ℚ) / 18848291) + C ((-53920800 : ℚ) / 29618743) * X ^ 1 + C ((456729600 : ℚ) / 207331201) * X ^ 2 + C ((816976800 : ℚ) / 207331201) * X ^ 3

def p5 : ℚ[X] :=
  C ((-3101345732344013 : ℚ) / 417156932336400) + C ((1551824487327961 : ℚ) / 139052310778800) * X ^ 1 + C ((5281520389963433 : ℚ) / 208578466168200) * X ^ 2

def p6 : ℚ[X] :=
  C ((20386454485975146131400 : ℚ) / 134540568400023368348689) + C ((-116921850669695349628200 : ℚ) / 134540568400023368348689) * X ^ 1

def p7 : ℚ[X] :=
  C ((-1418727199345173218699453485153 : ℚ) / 300652900982269840562532894900)

def q0 : ℚ[X] :=
  C ((-3 : ℚ) / 49) + C ((1 : ℚ) / 7) * X ^ 1

def q1 : ℚ[X] :=
  C ((49147 : ℚ) / 10800) + C ((-343 : ℚ) / 180) * X ^ 1

def q2 : ℚ[X] :=
  C ((-144514800 : ℚ) / 1451318407) + C ((648000 : ℚ) / 4938857) * X ^ 1

def q3 : ℚ[X] :=
  C ((-45980669770574 : ℚ) / 391084624065375) + C ((-20897533742393 : ℚ) / 2941116480000) * X ^ 1

def q4 : ℚ[X] :=
  C ((513590979563359844022000720000 : ℚ) / 27894457629599493387799077145489) + C ((170403767839004297760000 : ℚ) / 1095023965557106909973033) * X ^ 1

def q5 : ℚ[X] :=
  C ((-98002800864234430538845957201675071191601180197 : ℚ) / 5468287665610615551337509461454815151294096000) + C ((-710578755281993351445397928758303489337 : ℚ) / 24387380274232383995426384148663240000) * X ^ 1

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
    p2.resultant p3 5 4 = ((10159228849 : ℚ) / 12960000) *
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
    _ = ((10159228849 : ℚ) / 12960000) *
        p3.resultant p4 4 3 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 4 3 = ((667451091738240000 : ℚ) / 42986226908102401) *
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
    _ = ((667451091738240000 : ℚ) / 42986226908102401) *
        p4.resultant p5 3 2 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep4 :
    p4.resultant p5 3 2 = ((27894457629599493387799077145489 : ℚ) / 43504976549078951990691240000) *
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
    _ = ((27894457629599493387799077145489 : ℚ) / 43504976549078951990691240000) *
        p5.resultant p6 2 1 := by
      norm_num [p5, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep5 :
    p5.resultant p6 2 1 = ((13670719164026538878343773653637037878235240000 : ℚ) / 18101164545401366541830375455734920450688018721) *
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
    _ = ((13670719164026538878343773653637037878235240000 : ℚ) / 18101164545401366541830375455734920450688018721) *
        p6.resultant p7 1 0 := by
      norm_num [p6, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p6.resultant p7 1 0 = ((-1418727199345173218699453485153 : ℚ) / 300652900982269840562532894900) := by
  rw [show p7 = C ((-1418727199345173218699453485153 : ℚ) / 300652900982269840562532894900) by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 ((-1418727199345173218699453485153 : ℚ) / 300652900982269840562532894900))

theorem resultant_eq : p0.resultant p1 7 6 = (-18390439888 : ℚ) := by
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
    have hget : ([1, -4, -4, 15, 8, -9, -3, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([1, -4, -4, 15, 8, -9, -3, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
    row.polynomial.discr = (18390439888 : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h


theorem kernel_squarefree : Squarefree 1149402493 := by
  have hp0 : Prime (109 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp1 : Prime (1283 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp2 : Prime (8219 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  rw [show 1149402493 = 109 * (1283 * (8219)) by norm_num]
  exact (Nat.squarefree_mul (m := 109) (n := 1283 * (8219)) (by norm_num)).mpr ⟨hp0.squarefree, (Nat.squarefree_mul (m := 1283) (n := 8219) (by norm_num)).mpr ⟨hp1.squarefree, hp2.squarefree⟩⟩

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  { coefficients := [1, -4, -4, 15, 8, -9, -3, 1]
    discriminant := 18390439888
    squarePart := 4
    kernel := 1149402493
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = (18390439888 : ℤ)
      exact polynomial_discr }


end

end DegreeSevenRows200To299SurvivorDiscriminantCase047
end TraceEuclidean

/-! Pure-kernel resultant certificate for retained septic 048. -/

namespace TraceEuclidean
namespace DegreeSevenRows200To299SurvivorDiscriminantCase048

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨7747584497, [-1, -5, -1, 15, 8, -9, -3, 1], 1⟩

def p0 : ℚ[X] :=
  C (-1 : ℚ) + C (-5 : ℚ) * X ^ 1 + C (-1 : ℚ) * X ^ 2 + C (15 : ℚ) * X ^ 3 + C (8 : ℚ) * X ^ 4 + C (-9 : ℚ) * X ^ 5 + C (-3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7

def p1 : ℚ[X] :=
  C (-5 : ℚ) + C (-2 : ℚ) * X ^ 1 + C (45 : ℚ) * X ^ 2 + C (32 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6

def p2 : ℚ[X] :=
  C ((-64 : ℚ) / 49) + C ((-216 : ℚ) / 49) * X ^ 1 + C ((100 : ℚ) / 49) * X ^ 2 + C ((516 : ℚ) / 49) * X ^ 3 + C ((33 : ℚ) / 49) * X ^ 4 + C ((-180 : ℚ) / 49) * X ^ 5

def p3 : ℚ[X] :=
  C ((637 : ℚ) / 675) + C ((7007 : ℚ) / 450) * X ^ 1 + C ((14749 : ℚ) / 540) * X ^ 2 + C ((-10829 : ℚ) / 900) * X ^ 3 + C ((-100793 : ℚ) / 3600) * X ^ 4

def p4 : ℚ[X] :=
  C ((-15003600 : ℚ) / 12195953) + C ((-3636000 : ℚ) / 1108723) * X ^ 1 + C ((26768400 : ℚ) / 12195953) * X ^ 2 + C ((72921600 : ℚ) / 12195953) * X ^ 3

def p5 : ℚ[X] :=
  C ((309855403781 : ℚ) / 531755974656) + C ((19604458542977 : ℚ) / 2215649894400) * X ^ 1 + C ((167512154103679 : ℚ) / 13293899366400) * X ^ 2

def p6 : ℚ[X] :=
  C ((-44493585988029297868800 : ℚ) / 39113423127469408998049) + C ((-84052905419032274534400 : ℚ) / 39113423127469408998049) * X ^ 1

def p7 : ℚ[X] :=
  C ((-303034550646983247995036735646353 : ℚ) / 531438573037277621973599413862400)

def q0 : ℚ[X] :=
  C ((-3 : ℚ) / 49) + C ((1 : ℚ) / 7) * X ^ 1

def q1 : ℚ[X] :=
  C ((49147 : ℚ) / 10800) + C ((-343 : ℚ) / 180) * X ^ 1

def q2 : ℚ[X] :=
  C ((-48070800 : ℚ) / 597601697) + C ((648000 : ℚ) / 4938857) * X ^ 1

def q3 : ℚ[X] :=
  C ((-4681260902101861 : ℚ) / 15952679239680000) + C ((-1229266690729 : ℚ) / 262517760000) * X ^ 1

def q4 : ℚ[X] :=
  C ((-75854300538116642912501760000 : ℚ) / 477025470131729921077982695697) + C ((969412412036874240000 : ℚ) / 2042970358377226211087) * X ^ 1

def q5 : ℚ[X] :=
  C ((-7160316687758652888169113674503176861119571841 : ℚ) / 7064890909380785102335731965472770736783360000) + C ((-6551973762451057866803070643054722271 : ℚ) / 1117390866094152280934011015004160000) * X ^ 1

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
    p2.resultant p3 5 4 = ((10159228849 : ℚ) / 12960000) *
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
    _ = ((10159228849 : ℚ) / 12960000) *
        p3.resultant p4 4 3 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 4 3 = ((5317559746560000 : ℚ) / 148741269578209) *
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
    _ = ((5317559746560000 : ℚ) / 148741269578209) *
        p4.resultant p5 3 2 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep4 :
    p4.resultant p5 3 2 = ((28060321772454701239881335041 : ℚ) / 176727760363970321448960000) *
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
    _ = ((28060321772454701239881335041 : ℚ) / 176727760363970321448960000) *
        p5.resultant p6 2 1 := by
      norm_num [p5, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep5 :
    p5.resultant p6 2 1 = ((7064890909380785102335731965472770736783360000 : ℚ) / 1529859868748458843649843653765895366085806401) *
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
    _ = ((7064890909380785102335731965472770736783360000 : ℚ) / 1529859868748458843649843653765895366085806401) *
        p6.resultant p7 1 0 := by
      norm_num [p6, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p6.resultant p7 1 0 = ((-303034550646983247995036735646353 : ℚ) / 531438573037277621973599413862400) := by
  rw [show p7 = C ((-303034550646983247995036735646353 : ℚ) / 531438573037277621973599413862400) by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 ((-303034550646983247995036735646353 : ℚ) / 531438573037277621973599413862400))

theorem resultant_eq : p0.resultant p1 7 6 = (-7747584497 : ℚ) := by
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
    have hget : ([-1, -5, -1, 15, 8, -9, -3, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([-1, -5, -1, 15, 8, -9, -3, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
    row.polynomial.discr = (7747584497 : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h


theorem kernel_squarefree : Squarefree 7747584497 := by
  have hp0 : Prime (7747584497 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  rw [show 7747584497 = 7747584497 by norm_num]
  exact hp0.squarefree

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  { coefficients := [-1, -5, -1, 15, 8, -9, -3, 1]
    discriminant := 7747584497
    squarePart := 1
    kernel := 7747584497
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = (7747584497 : ℤ)
      exact polynomial_discr }


end

end DegreeSevenRows200To299SurvivorDiscriminantCase048
end TraceEuclidean

/-! Pure-kernel resultant certificate for retained septic 049. -/

namespace TraceEuclidean
namespace DegreeSevenRows200To299SurvivorDiscriminantCase049

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨2918309309, [2, -7, -7, 16, 8, -9, -3, 1], 1⟩

def p0 : ℚ[X] :=
  C (2 : ℚ) + C (-7 : ℚ) * X ^ 1 + C (-7 : ℚ) * X ^ 2 + C (16 : ℚ) * X ^ 3 + C (8 : ℚ) * X ^ 4 + C (-9 : ℚ) * X ^ 5 + C (-3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7

def p1 : ℚ[X] :=
  C (-7 : ℚ) + C (-14 : ℚ) * X ^ 1 + C (48 : ℚ) * X ^ 2 + C (32 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6

def p2 : ℚ[X] :=
  C ((11 : ℚ) / 7) + C ((-48 : ℚ) / 7) * X ^ 1 + C ((-101 : ℚ) / 49) * X ^ 2 + C ((544 : ℚ) / 49) * X ^ 3 + C ((33 : ℚ) / 49) * X ^ 4 + C ((-180 : ℚ) / 49) * X ^ 5

def p3 : ℚ[X] :=
  C ((-152831 : ℚ) / 10800) + C ((18179 : ℚ) / 900) * X ^ 1 + C ((478583 : ℚ) / 10800) * X ^ 2 + C ((-60613 : ℚ) / 2700) * X ^ 3 + C ((-32291 : ℚ) / 1200) * X ^ 4

def p4 : ℚ[X] :=
  C ((-75528400 : ℚ) / 191517921) + C ((-135300800 : ℚ) / 63839307) * X ^ 1 + C ((256087600 : ℚ) / 191517921) * X ^ 2 + C ((370420000 : ℚ) / 191517921) * X ^ 3

def p5 : ℚ[X] :=
  C ((-5123172758647797 : ℚ) / 343027441000000) + C ((1800545966867529 : ℚ) / 171513720500000) * X ^ 1 + C ((5997905199413883 : ℚ) / 343027441000000) * X ^ 2

def p6 : ℚ[X] :=
  C ((-45853640558467549000000 : ℚ) / 187840733615503750148409) + C ((-107624968010421356000000 : ℚ) / 187840733615503750148409) * X ^ 1

def p7 : ℚ[X] :=
  C ((-548177361519513820782512116239381 : ℚ) / 33767367722759591738148496000000)

def q0 : ℚ[X] :=
  C ((-3 : ℚ) / 49) + C ((1 : ℚ) / 7) * X ^ 1

def q1 : ℚ[X] :=
  C ((49147 : ℚ) / 10800) + C ((-343 : ℚ) / 180) * X ^ 1

def q2 : ℚ[X] :=
  C ((-144848400 : ℚ) / 1042708681) + C ((216000 : ℚ) / 1582259) * X ^ 1

def q3 : ℚ[X] :=
  C ((-818480968227171991 : ℚ) / 411632929200000000) + C ((-2061435062337 : ℚ) / 148168000000) * X ^ 1

def q4 : ℚ[X] :=
  C ((361932041179697647886800000000 : ℚ) / 35974866781156091596126733137689) + C ((127064224695220000000000 : ℚ) / 1148706334146837290697243) * X ^ 1

def q5 : ℚ[X] :=
  C ((-61627429782955307608008596702741325114527673969 : ℚ) / 11583133739244220212141820660878736000000000000) + C ((-1126650912814148096370124901301064962147 : ℚ) / 36918317364321699080429996000000000000) * X ^ 1

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
    p2.resultant p3 5 4 = ((1042708681 : ℚ) / 1440000) *
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
    _ = ((1042708681 : ℚ) / 1440000) *
        p3.resultant p4 4 3 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 4 3 = ((137210976400000000 : ℚ) / 36679114064162241) *
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
    _ = ((137210976400000000 : ℚ) / 36679114064162241) *
        p4.resultant p5 3 2 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep4 :
    p4.resultant p5 3 2 = ((35974866781156091596126733137689 : ℚ) / 117667825279008481000000000000) *
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
    _ = ((35974866781156091596126733137689 : ℚ) / 117667825279008481000000000000) *
        p5.resultant p6 2 1 := by
      norm_num [p5, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep5 :
    p5.resultant p6 2 1 = ((11583133739244220212141820660878736000000000000 : ℚ) / 35284141205210640563096877134349092089525231281) *
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
    _ = ((11583133739244220212141820660878736000000000000 : ℚ) / 35284141205210640563096877134349092089525231281) *
        p6.resultant p7 1 0 := by
      norm_num [p6, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p6.resultant p7 1 0 = ((-548177361519513820782512116239381 : ℚ) / 33767367722759591738148496000000) := by
  rw [show p7 = C ((-548177361519513820782512116239381 : ℚ) / 33767367722759591738148496000000) by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 ((-548177361519513820782512116239381 : ℚ) / 33767367722759591738148496000000))

theorem resultant_eq : p0.resultant p1 7 6 = (-2918309309 : ℚ) := by
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
    have hget : ([2, -7, -7, 16, 8, -9, -3, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([2, -7, -7, 16, 8, -9, -3, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
    row.polynomial.discr = (2918309309 : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h


theorem kernel_squarefree : Squarefree 2918309309 := by
  have hp0 : Prime (139 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp1 : Prime (20995031 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  rw [show 2918309309 = 139 * (20995031) by norm_num]
  exact (Nat.squarefree_mul (m := 139) (n := 20995031) (by norm_num)).mpr ⟨hp0.squarefree, hp1.squarefree⟩

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  { coefficients := [2, -7, -7, 16, 8, -9, -3, 1]
    discriminant := 2918309309
    squarePart := 1
    kernel := 2918309309
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = (2918309309 : ℤ)
      exact polynomial_discr }


end

end DegreeSevenRows200To299SurvivorDiscriminantCase049
end TraceEuclidean

/-! Pure-kernel resultant certificate for retained septic 050. -/

namespace TraceEuclidean
namespace DegreeSevenRows200To299SurvivorDiscriminantCase050

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨14807620757, [1, -7, -6, 16, 8, -9, -3, 1], 1⟩

def p0 : ℚ[X] :=
  C (1 : ℚ) + C (-7 : ℚ) * X ^ 1 + C (-6 : ℚ) * X ^ 2 + C (16 : ℚ) * X ^ 3 + C (8 : ℚ) * X ^ 4 + C (-9 : ℚ) * X ^ 5 + C (-3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7

def p1 : ℚ[X] :=
  C (-7 : ℚ) + C (-12 : ℚ) * X ^ 1 + C (48 : ℚ) * X ^ 2 + C (32 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6

def p2 : ℚ[X] :=
  C ((4 : ℚ) / 7) + C ((-330 : ℚ) / 49) * X ^ 1 + C ((-66 : ℚ) / 49) * X ^ 2 + C ((544 : ℚ) / 49) * X ^ 3 + C ((33 : ℚ) / 49) * X ^ 4 + C ((-180 : ℚ) / 49) * X ^ 5

def p3 : ℚ[X] :=
  C ((-25921 : ℚ) / 2700) + C ((1421 : ℚ) / 72) * X ^ 1 + C ((74333 : ℚ) / 1800) * X ^ 2 + C ((-28469 : ℚ) / 1350) * X ^ 3 + C ((-32291 : ℚ) / 1200) * X ^ 4

def p4 : ℚ[X] :=
  C ((-133281200 : ℚ) / 191517921) + C ((-179946400 : ℚ) / 63839307) * X ^ 1 + C ((90034400 : ℚ) / 63839307) * X ^ 2 + C ((10477600 : ℚ) / 3908529) * X ^ 3

def p5 : ℚ[X] :=
  C ((-76652042221449 : ℚ) / 6724031232800) + C ((36729099737343 : ℚ) / 6724031232800) * X ^ 1 + C ((27985071548529 : ℚ) / 1681007808200) * X ^ 2

def p6 : ℚ[X] :=
  C ((-22206792693728464850 : ℚ) / 66791046757513062843) + C ((-77294260753354373050 : ℚ) / 66791046757513062843) * X ^ 1

def p7 : ℚ[X] :=
  C ((-329672163449435991684217410717 : ℚ) / 28432480640550248375081628100)

def q0 : ℚ[X] :=
  C ((-3 : ℚ) / 49) + C ((1 : ℚ) / 7) * X ^ 1

def q1 : ℚ[X] :=
  C ((49147 : ℚ) / 10800) + C ((-343 : ℚ) / 180) * X ^ 1

def q2 : ℚ[X] :=
  C ((-137648400 : ℚ) / 1042708681) + C ((216000 : ℚ) / 1582259) * X ^ 1

def q3 : ℚ[X] :=
  C ((-85152979883389 : ℚ) / 32934030528000) + C ((-6010014759 : ℚ) / 598720000) * X ^ 1

def q4 : ℚ[X] :=
  C ((8322785834940507891800000 : ℚ) / 261054743192095774000687947) + C ((17612927411196320000 : ℚ) / 109380463714500503841) * X ^ 1

def q5 : ℚ[X] :=
  C ((-56120728858215062813235908665572689064333 : ℚ) / 95590443926520610125923158296937060840000) + C ((-1869152222310148933940699701207947 : ℚ) / 129932255855435515438665649010000) * X ^ 1

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
    p2.resultant p3 5 4 = ((1042708681 : ℚ) / 1440000) *
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
    _ = ((1042708681 : ℚ) / 1440000) *
        p3.resultant p4 4 3 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 4 3 = ((109780101760000 : ℚ) / 15276598943841) *
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
    _ = ((109780101760000 : ℚ) / 15276598943841) *
        p4.resultant p5 3 2 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep4 :
    p4.resultant p5 3 2 = ((783164229576287322002063841 : ℚ) / 2825787251229367987240000) *
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
    _ = ((783164229576287322002063841 : ℚ) / 2825787251229367987240000) *
        p5.resultant p6 2 1 := by
      norm_num [p5, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep5 :
    p5.resultant p6 2 1 = ((5974402745407538132870197393558566302500 : ℚ) / 4461043926964296225721447933782867242649) *
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
    _ = ((5974402745407538132870197393558566302500 : ℚ) / 4461043926964296225721447933782867242649) *
        p6.resultant p7 1 0 := by
      norm_num [p6, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p6.resultant p7 1 0 = ((-329672163449435991684217410717 : ℚ) / 28432480640550248375081628100) := by
  rw [show p7 = C ((-329672163449435991684217410717 : ℚ) / 28432480640550248375081628100) by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 ((-329672163449435991684217410717 : ℚ) / 28432480640550248375081628100))

theorem resultant_eq : p0.resultant p1 7 6 = (-14807620757 : ℚ) := by
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
    have hget : ([1, -7, -6, 16, 8, -9, -3, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([1, -7, -6, 16, 8, -9, -3, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
    row.polynomial.discr = (14807620757 : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h


theorem kernel_squarefree : Squarefree 14807620757 := by
  have hp0 : Prime (59 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp1 : Prime (271 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp2 : Prime (926113 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  rw [show 14807620757 = 59 * (271 * (926113)) by norm_num]
  exact (Nat.squarefree_mul (m := 59) (n := 271 * (926113)) (by norm_num)).mpr ⟨hp0.squarefree, (Nat.squarefree_mul (m := 271) (n := 926113) (by norm_num)).mpr ⟨hp1.squarefree, hp2.squarefree⟩⟩

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  { coefficients := [1, -7, -6, 16, 8, -9, -3, 1]
    discriminant := 14807620757
    squarePart := 1
    kernel := 14807620757
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = (14807620757 : ℤ)
      exact polynomial_discr }


end

end DegreeSevenRows200To299SurvivorDiscriminantCase050
end TraceEuclidean
