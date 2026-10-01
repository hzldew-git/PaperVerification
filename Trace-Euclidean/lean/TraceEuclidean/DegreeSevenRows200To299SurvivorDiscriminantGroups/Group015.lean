import TraceEuclidean.DegreeSevenSurvivorDiscriminant

/-! Pure-kernel resultant certificate for retained septic 076. -/

namespace TraceEuclidean
namespace DegreeSevenRows200To299SurvivorDiscriminantCase076

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨44347199213, [-1, -7, -2, 18, 8, -9, -3, 1], 1⟩

def p0 : ℚ[X] :=
  C (-1 : ℚ) + C (-7 : ℚ) * X ^ 1 + C (-2 : ℚ) * X ^ 2 + C (18 : ℚ) * X ^ 3 + C (8 : ℚ) * X ^ 4 + C (-9 : ℚ) * X ^ 5 + C (-3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7

def p1 : ℚ[X] :=
  C (-7 : ℚ) + C (-4 : ℚ) * X ^ 1 + C (54 : ℚ) * X ^ 2 + C (32 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6

def p2 : ℚ[X] :=
  C ((-10 : ℚ) / 7) + C ((-306 : ℚ) / 49) * X ^ 1 + C ((92 : ℚ) / 49) * X ^ 2 + C ((600 : ℚ) / 49) * X ^ 3 + C ((33 : ℚ) / 49) * X ^ 4 + C ((-180 : ℚ) / 49) * X ^ 5

def p3 : ℚ[X] :=
  C ((-539 : ℚ) / 1080) + C ((39053 : ℚ) / 1800) * X ^ 1 + C ((90601 : ℚ) / 2700) * X ^ 2 + C ((-1813 : ℚ) / 90) * X ^ 3 + C ((-89033 : ℚ) / 3600) * X ^ 4

def p4 : ℚ[X] :=
  C ((-34724400 : ℚ) / 23110423) + C ((-9756000 : ℚ) / 3301489) * X ^ 1 + C ((83856000 : ℚ) / 23110423) * X ^ 2 + C ((691567200 : ℚ) / 161772961) * X ^ 3

def p5 : ℚ[X] :=
  C ((-1504326764339 : ℚ) / 7472893626810) + C ((2708014496182639 : ℚ) / 199277163381600) * X ^ 1 + C ((4705332711515947 : ℚ) / 298915745072400) * X ^ 2

def p6 : ℚ[X] :=
  C ((-205745612323376266405200 : ℚ) / 136859434291136045372569) + C ((-55660091600918367041400 : ℚ) / 19551347755876577910367) * X ^ 1

def p7 : ℚ[X] :=
  C ((-123863930544642727433108658134453 : ℚ) / 41457110882830874503651114851600)

def q0 : ℚ[X] :=
  C ((-3 : ℚ) / 49) + C ((1 : ℚ) / 7) * X ^ 1

def q1 : ℚ[X] :=
  C ((49147 : ℚ) / 10800) + C ((-343 : ℚ) / 180) * X ^ 1

def q2 : ℚ[X] :=
  C ((-167842800 : ℚ) / 1132410727) + C ((648000 : ℚ) / 4362617) * X ^ 1

def q3 : ℚ[X] :=
  C ((7108591700437619 : ℚ) / 35869889408688000) + C ((-14403132036713 : ℚ) / 2489641920000) * X ^ 1

def q4 : ℚ[X] :=
  C ((-87155238495157107930672480000 : ℚ) / 22140155926062014113750835306809) + C ((206720324855633465280000 : ℚ) / 761195605232093544909067) * X ^ 1

def q5 : ℚ[X] :=
  C ((-22969113077390625677105540987714848493542136689 : ℚ) / 12392183188090493389177333530010919157255840000) + C ((-91995596149949963740991123858057122549 : ℚ) / 16637677751686547000270016616797360000) * X ^ 1

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
    p2.resultant p3 5 4 = ((7926875089 : ℚ) / 12960000) *
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
    _ = ((7926875089 : ℚ) / 12960000) *
        p3.resultant p4 4 3 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 4 3 = ((478265192115840000 : ℚ) / 26170490910707521) *
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
    _ = ((478265192115840000 : ℚ) / 26170490910707521) *
        p4.resultant p5 3 2 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep4 :
    p4.resultant p5 3 2 = ((22140155926062014113750835306809 : ℚ) / 89350622652188024881241760000) *
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
    _ = ((22140155926062014113750835306809 : ℚ) / 89350622652188024881241760000) *
        p5.resultant p6 2 1 := by
      norm_num [p5, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep5 :
    p5.resultant p6 2 1 = ((3098045797022623347294333382502729789313960000 : ℚ) / 382255199071220099145641262185113376286074689) *
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
    _ = ((3098045797022623347294333382502729789313960000 : ℚ) / 382255199071220099145641262185113376286074689) *
        p6.resultant p7 1 0 := by
      norm_num [p6, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p6.resultant p7 1 0 = ((-123863930544642727433108658134453 : ℚ) / 41457110882830874503651114851600) := by
  rw [show p7 = C ((-123863930544642727433108658134453 : ℚ) / 41457110882830874503651114851600) by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 ((-123863930544642727433108658134453 : ℚ) / 41457110882830874503651114851600))

theorem resultant_eq : p0.resultant p1 7 6 = (-44347199213 : ℚ) := by
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
    have hget : ([-1, -7, -2, 18, 8, -9, -3, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([-1, -7, -2, 18, 8, -9, -3, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
    row.polynomial.discr = (44347199213 : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h


theorem kernel_squarefree : Squarefree 44347199213 := by
  have hp0 : Prime (44347199213 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  rw [show 44347199213 = 44347199213 by norm_num]
  exact hp0.squarefree

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  { coefficients := [-1, -7, -2, 18, 8, -9, -3, 1]
    discriminant := 44347199213
    squarePart := 1
    kernel := 44347199213
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = (44347199213 : ℤ)
      exact polynomial_discr }


end

end DegreeSevenRows200To299SurvivorDiscriminantCase076
end TraceEuclidean

/-! Pure-kernel resultant certificate for retained septic 077. -/

namespace TraceEuclidean
namespace DegreeSevenRows200To299SurvivorDiscriminantCase077

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨6802888868, [-1, -6, -2, 18, 8, -9, -3, 1], 1⟩

def p0 : ℚ[X] :=
  C (-1 : ℚ) + C (-6 : ℚ) * X ^ 1 + C (-2 : ℚ) * X ^ 2 + C (18 : ℚ) * X ^ 3 + C (8 : ℚ) * X ^ 4 + C (-9 : ℚ) * X ^ 5 + C (-3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7

def p1 : ℚ[X] :=
  C (-6 : ℚ) + C (-4 : ℚ) * X ^ 1 + C (54 : ℚ) * X ^ 2 + C (32 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6

def p2 : ℚ[X] :=
  C ((-67 : ℚ) / 49) + C ((-264 : ℚ) / 49) * X ^ 1 + C ((92 : ℚ) / 49) * X ^ 2 + C ((600 : ℚ) / 49) * X ^ 3 + C ((33 : ℚ) / 49) * X ^ 4 + C ((-180 : ℚ) / 49) * X ^ 5

def p3 : ℚ[X] :=
  C ((2401 : ℚ) / 10800) + C ((16121 : ℚ) / 900) * X ^ 1 + C ((95011 : ℚ) / 2700) * X ^ 2 + C ((-1813 : ℚ) / 90) * X ^ 3 + C ((-89033 : ℚ) / 3600) * X ^ 4

def p4 : ℚ[X] :=
  C ((-215869200 : ℚ) / 161772961) + C ((-447444000 : ℚ) / 161772961) * X ^ 1 + C ((717078000 : ℚ) / 161772961) * X ^ 2 + C ((652320000 : ℚ) / 161772961) * X ^ 3

def p5 : ℚ[X] :=
  C ((543120200192339 : ℚ) / 212760691200000) + C ((34416065042023 : ℚ) / 2364007680000) * X ^ 1 + C ((446121779868583 : ℚ) / 42552138240000) * X ^ 2

def p6 : ℚ[X] :=
  C ((-1292181752122831872000 : ℚ) / 1230271370708930944849) + C ((-2617523296241356800000 : ℚ) / 1230271370708930944849) * X ^ 1

def p7 : ℚ[X] :=
  C ((-2092349853103721898223496010233 : ℚ) / 1006328425807183612953600000000)

def q0 : ℚ[X] :=
  C ((-3 : ℚ) / 49) + C ((1 : ℚ) / 7) * X ^ 1

def q1 : ℚ[X] :=
  C ((49147 : ℚ) / 10800) + C ((-343 : ℚ) / 180) * X ^ 1

def q2 : ℚ[X] :=
  C ((-167842800 : ℚ) / 1132410727) + C ((648000 : ℚ) / 4362617) * X ^ 1

def q3 : ℚ[X] :=
  C ((445882926783082369 : ℚ) / 255312829440000000) + C ((-14403132036713 : ℚ) / 2348352000000) * X ^ 1

def q4 : ℚ[X] :=
  C ((-22147923958851601751040000000 : ℚ) / 199024642473112428092750427889) + C ((27757610816716800000000 : ℚ) / 72170441295930862784263) * X ^ 1

def q5 : ℚ[X] :=
  C ((-75536956194746136768569301652895249503360181 : ℚ) / 17128570515915544273385696762265600000000000) + C ((-548850853622029562288662133240778967 : ℚ) / 111381213148082686958764032000000000) * X ^ 1

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
    p2.resultant p3 5 4 = ((7926875089 : ℚ) / 12960000) *
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
    _ = ((7926875089 : ℚ) / 12960000) *
        p3.resultant p4 4 3 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 4 3 = ((425521382400000000 : ℚ) / 26170490910707521) *
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
    _ = ((425521382400000000 : ℚ) / 26170490910707521) *
        p4.resultant p5 3 2 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep4 :
    p4.resultant p5 3 2 = ((199024642473112428092750427889 : ℚ) / 1810684468796070297600000000) *
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
    _ = ((199024642473112428092750427889 : ℚ) / 1810684468796070297600000000) *
        p5.resultant p6 2 1 := by
      norm_num [p5, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep5 :
    p5.resultant p6 2 1 = ((6851428206366217709354278704906240000000000 : ℚ) / 1513567645586031790012130430824495879632801) *
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
    _ = ((6851428206366217709354278704906240000000000 : ℚ) / 1513567645586031790012130430824495879632801) *
        p6.resultant p7 1 0 := by
      norm_num [p6, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p6.resultant p7 1 0 = ((-2092349853103721898223496010233 : ℚ) / 1006328425807183612953600000000) := by
  rw [show p7 = C ((-2092349853103721898223496010233 : ℚ) / 1006328425807183612953600000000) by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 ((-2092349853103721898223496010233 : ℚ) / 1006328425807183612953600000000))

theorem resultant_eq : p0.resultant p1 7 6 = (-6802888868 : ℚ) := by
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
    have hget : ([-1, -6, -2, 18, 8, -9, -3, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([-1, -6, -2, 18, 8, -9, -3, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
    row.polynomial.discr = (6802888868 : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h


theorem kernel_squarefree : Squarefree 1700722217 := by
  have hp0 : Prime (31 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp1 : Prime (54862007 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  rw [show 1700722217 = 31 * (54862007) by norm_num]
  exact (Nat.squarefree_mul (m := 31) (n := 54862007) (by norm_num)).mpr ⟨hp0.squarefree, hp1.squarefree⟩

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  { coefficients := [-1, -6, -2, 18, 8, -9, -3, 1]
    discriminant := 6802888868
    squarePart := 2
    kernel := 1700722217
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = (6802888868 : ℤ)
      exact polynomial_discr }


end

end DegreeSevenRows200To299SurvivorDiscriminantCase077
end TraceEuclidean

/-! Pure-kernel resultant certificate for retained septic 078. -/

namespace TraceEuclidean
namespace DegreeSevenRows200To299SurvivorDiscriminantCase078

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨5995033749, [1, -5, -2, 18, 8, -9, -3, 1], 1⟩

def p0 : ℚ[X] :=
  C (1 : ℚ) + C (-5 : ℚ) * X ^ 1 + C (-2 : ℚ) * X ^ 2 + C (18 : ℚ) * X ^ 3 + C (8 : ℚ) * X ^ 4 + C (-9 : ℚ) * X ^ 5 + C (-3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7

def p1 : ℚ[X] :=
  C (-5 : ℚ) + C (-4 : ℚ) * X ^ 1 + C (54 : ℚ) * X ^ 2 + C (32 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6

def p2 : ℚ[X] :=
  C ((34 : ℚ) / 49) + C ((-222 : ℚ) / 49) * X ^ 1 + C ((92 : ℚ) / 49) * X ^ 2 + C ((600 : ℚ) / 49) * X ^ 3 + C ((33 : ℚ) / 49) * X ^ 4 + C ((-180 : ℚ) / 49) * X ^ 5

def p3 : ℚ[X] :=
  C ((-44051 : ℚ) / 5400) + C ((32291 : ℚ) / 1800) * X ^ 1 + C ((99421 : ℚ) / 2700) * X ^ 2 + C ((-1813 : ℚ) / 90) * X ^ 3 + C ((-89033 : ℚ) / 3600) * X ^ 4

def p4 : ℚ[X] :=
  C ((-83348400 : ℚ) / 161772961) + C ((-106768800 : ℚ) / 161772961) * X ^ 1 + C ((755587200 : ℚ) / 161772961) * X ^ 2 + C ((613072800 : ℚ) / 161772961) * X ^ 3

def p5 : ℚ[X] :=
  C ((-198276867876689 : ℚ) / 29363926414050) + C ((170986416447833 : ℚ) / 10440507169440) * X ^ 1 + C ((4645809321153763 : ℚ) / 234911411312400) * X ^ 2

def p6 : ℚ[X] :=
  C ((526906295573713200 : ℚ) / 65950933112737232623) + C ((-84728619163775476265400 : ℚ) / 133418737687067421596329) * X ^ 1

def p7 : ℚ[X] :=
  C ((-29624067969738792344755696648423 : ℚ) / 4527436528357268597952709546800)

def q0 : ℚ[X] :=
  C ((-3 : ℚ) / 49) + C ((1 : ℚ) / 7) * X ^ 1

def q1 : ℚ[X] :=
  C ((49147 : ℚ) / 10800) + C ((-343 : ℚ) / 180) * X ^ 1

def q2 : ℚ[X] :=
  C ((-167842800 : ℚ) / 1132410727) + C ((648000 : ℚ) / 4362617) * X ^ 1

def q3 : ℚ[X] :=
  C ((384415622695450381 : ℚ) / 140946846787440000) + C ((-14403132036713 : ℚ) / 2207062080000) * X ^ 1

def q4 : ℚ[X] :=
  C ((1672395503794637572381292640000 : ℚ) / 21583544248519188198273489060169) + C ((144017796685244742720000 : ℚ) / 751566330124444176802243) * X ^ 1

def q5 : ℚ[X] :=
  C ((-751787620769590842510326191936438499199284494967 : ℚ) / 28715755621600403547566582364634394924948640000) + C ((-619838015163146673770638515529525336027 : ℚ) / 19903719506313357843465583264710960000) * X ^ 1

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
    p2.resultant p3 5 4 = ((7926875089 : ℚ) / 12960000) *
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
    _ = ((7926875089 : ℚ) / 12960000) *
        p3.resultant p4 4 3 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 4 3 = ((375858258099840000 : ℚ) / 26170490910707521) *
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
    _ = ((375858258099840000 : ℚ) / 26170490910707521) *
        p4.resultant p5 3 2 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep4 :
    p4.resultant p5 3 2 = ((21583544248519188198273489060169 : ℚ) / 55183371164783570690393760000) *
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
    _ = ((21583544248519188198273489060169 : ℚ) / 55183371164783570690393760000) *
        p5.resultant p6 2 1 := by
      norm_num [p5, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep5 :
    p5.resultant p6 2 1 = ((7178938905400100886891645591158598731237160000 : ℚ) / 17800559566010504718519119851973697550626276241) *
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
    _ = ((7178938905400100886891645591158598731237160000 : ℚ) / 17800559566010504718519119851973697550626276241) *
        p6.resultant p7 1 0 := by
      norm_num [p6, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p6.resultant p7 1 0 = ((-29624067969738792344755696648423 : ℚ) / 4527436528357268597952709546800) := by
  rw [show p7 = C ((-29624067969738792344755696648423 : ℚ) / 4527436528357268597952709546800) by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 ((-29624067969738792344755696648423 : ℚ) / 4527436528357268597952709546800))

theorem resultant_eq : p0.resultant p1 7 6 = (-5995033749 : ℚ) := by
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
    have hget : ([1, -5, -2, 18, 8, -9, -3, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([1, -5, -2, 18, 8, -9, -3, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
    row.polynomial.discr = (5995033749 : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h


theorem kernel_squarefree : Squarefree 666114861 := by
  have hp0 : Prime (3 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp1 : Prime (379 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp2 : Prime (585853 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  rw [show 666114861 = 3 * (379 * (585853)) by norm_num]
  exact (Nat.squarefree_mul (m := 3) (n := 379 * (585853)) (by norm_num)).mpr ⟨hp0.squarefree, (Nat.squarefree_mul (m := 379) (n := 585853) (by norm_num)).mpr ⟨hp1.squarefree, hp2.squarefree⟩⟩

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  { coefficients := [1, -5, -2, 18, 8, -9, -3, 1]
    discriminant := 5995033749
    squarePart := 3
    kernel := 666114861
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = (5995033749 : ℤ)
      exact polynomial_discr }


end

end DegreeSevenRows200To299SurvivorDiscriminantCase078
end TraceEuclidean

/-! Pure-kernel resultant certificate for retained septic 079. -/

namespace TraceEuclidean
namespace DegreeSevenRows200To299SurvivorDiscriminantCase079

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨44794811417, [-1, -6, -1, 18, 8, -9, -3, 1], 1⟩

def p0 : ℚ[X] :=
  C (-1 : ℚ) + C (-6 : ℚ) * X ^ 1 + C (-1 : ℚ) * X ^ 2 + C (18 : ℚ) * X ^ 3 + C (8 : ℚ) * X ^ 4 + C (-9 : ℚ) * X ^ 5 + C (-3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7

def p1 : ℚ[X] :=
  C (-6 : ℚ) + C (-2 : ℚ) * X ^ 1 + C (54 : ℚ) * X ^ 2 + C (32 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6

def p2 : ℚ[X] :=
  C ((-67 : ℚ) / 49) + C ((-258 : ℚ) / 49) * X ^ 1 + C ((127 : ℚ) / 49) * X ^ 2 + C ((600 : ℚ) / 49) * X ^ 3 + C ((33 : ℚ) / 49) * X ^ 4 + C ((-180 : ℚ) / 49) * X ^ 5

def p3 : ℚ[X] :=
  C ((2401 : ℚ) / 10800) + C ((3871 : ℚ) / 200) * X ^ 1 + C ((347459 : ℚ) / 10800) * X ^ 2 + C ((-1127 : ℚ) / 60) * X ^ 3 + C ((-89033 : ℚ) / 3600) * X ^ 4

def p4 : ℚ[X] :=
  C ((-9398400 : ℚ) / 7033607) + C ((-230400 : ℚ) / 89033) * X ^ 1 + C ((29698800 : ℚ) / 7033607) * X ^ 2 + C ((34012800 : ℚ) / 7033607) * X ^ 3

def p5 : ℚ[X] :=
  C ((361204159687 : ℚ) / 361522051200) + C ((7042475461 : ℚ) / 502113960) * X ^ 1 + C ((47670837494959 : ℚ) / 2892176409600) * X ^ 2

def p6 : ℚ[X] :=
  C ((-9978014967231571891200 : ℚ) / 7431137564528149486609) + C ((-22088440717401266841600 : ℚ) / 7431137564528149486609) * X ^ 1

def p7 : ℚ[X] :=
  C ((-332876405816823124840635521814953 : ℚ) / 168696214970382348759311266713600)

def q0 : ℚ[X] :=
  C ((-3 : ℚ) / 49) + C ((1 : ℚ) / 7) * X ^ 1

def q1 : ℚ[X] :=
  C ((49147 : ℚ) / 10800) + C ((-343 : ℚ) / 180) * X ^ 1

def q2 : ℚ[X] :=
  C ((-48265200 : ℚ) / 344646743) + C ((648000 : ℚ) / 4362617) * X ^ 1

def q3 : ℚ[X] :=
  C ((2017635443278259 : ℚ) / 3470611691520000) + C ((-626223132031 : ℚ) / 122446080000) * X ^ 1

def q4 : ℚ[X] :=
  C ((340932419918971548641280000 : ℚ) / 52267701191828143926059468663) + C ((98371017784442880000 : ℚ) / 335297936300406087113) * X ^ 1

def q5 : ℚ[X] :=
  C ((-1080043611070328361579583915139495990315858933 : ℚ) / 487899213326150191773919873932567639490560000) + C ((-354248551241306813889059663475504031 : ℚ) / 63883667167716044176430219919360000) * X ^ 1

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
    p2.resultant p3 5 4 = ((7926875089 : ℚ) / 12960000) *
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
    _ = ((7926875089 : ℚ) / 12960000) *
        p3.resultant p4 4 3 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 4 3 = ((1156870563840000 : ℚ) / 49471627430449) *
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
    _ = ((1156870563840000 : ℚ) / 49471627430449) *
        p4.resultant p5 3 2 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep4 :
    p4.resultant p5 3 2 = ((2272508747470788866350411681 : ℚ) / 8364684384246746972160000) *
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
    _ = ((2272508747470788866350411681 : ℚ) / 8364684384246746972160000) *
        p5.resultant p6 2 1 := by
      norm_num [p5, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep5 :
    p5.resultant p6 2 1 = ((487899213326150191773919873932567639490560000 : ℚ) / 55221805502941357074973851641157350270318881) *
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
    _ = ((487899213326150191773919873932567639490560000 : ℚ) / 55221805502941357074973851641157350270318881) *
        p6.resultant p7 1 0 := by
      norm_num [p6, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p6.resultant p7 1 0 = ((-332876405816823124840635521814953 : ℚ) / 168696214970382348759311266713600) := by
  rw [show p7 = C ((-332876405816823124840635521814953 : ℚ) / 168696214970382348759311266713600) by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 ((-332876405816823124840635521814953 : ℚ) / 168696214970382348759311266713600))

theorem resultant_eq : p0.resultant p1 7 6 = (-44794811417 : ℚ) := by
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
    have hget : ([-1, -6, -1, 18, 8, -9, -3, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([-1, -6, -1, 18, 8, -9, -3, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
    row.polynomial.discr = (44794811417 : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h


theorem kernel_squarefree : Squarefree 44794811417 := by
  have hp0 : Prime (227 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp1 : Prime (457 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp2 : Prime (431803 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  rw [show 44794811417 = 227 * (457 * (431803)) by norm_num]
  exact (Nat.squarefree_mul (m := 227) (n := 457 * (431803)) (by norm_num)).mpr ⟨hp0.squarefree, (Nat.squarefree_mul (m := 457) (n := 431803) (by norm_num)).mpr ⟨hp1.squarefree, hp2.squarefree⟩⟩

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  { coefficients := [-1, -6, -1, 18, 8, -9, -3, 1]
    discriminant := 44794811417
    squarePart := 1
    kernel := 44794811417
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = (44794811417 : ℤ)
      exact polynomial_discr }


end

end DegreeSevenRows200To299SurvivorDiscriminantCase079
end TraceEuclidean

/-! Pure-kernel resultant certificate for retained septic 080. -/

namespace TraceEuclidean
namespace DegreeSevenRows200To299SurvivorDiscriminantCase080

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨24545885213, [-1, -5, 0, 18, 8, -9, -3, 1], 1⟩

def p0 : ℚ[X] :=
  C (-1 : ℚ) + C (-5 : ℚ) * X ^ 1 + C (18 : ℚ) * X ^ 3 + C (8 : ℚ) * X ^ 4 + C (-9 : ℚ) * X ^ 5 + C (-3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7

def p1 : ℚ[X] :=
  C (-5 : ℚ) + C (54 : ℚ) * X ^ 2 + C (32 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6

def p2 : ℚ[X] :=
  C ((-64 : ℚ) / 49) + C ((-30 : ℚ) / 7) * X ^ 1 + C ((162 : ℚ) / 49) * X ^ 2 + C ((600 : ℚ) / 49) * X ^ 3 + C ((33 : ℚ) / 49) * X ^ 4 + C ((-180 : ℚ) / 49) * X ^ 5

def p3 : ℚ[X] :=
  C ((637 : ℚ) / 675) + C ((1225 : ℚ) / 72) * X ^ 1 + C ((18473 : ℚ) / 600) * X ^ 2 + C ((-784 : ℚ) / 45) * X ^ 3 + C ((-89033 : ℚ) / 3600) * X ^ 4

def p4 : ℚ[X] :=
  C ((-191163600 : ℚ) / 161772961) + C ((-353037600 : ℚ) / 161772961) * X ^ 1 + C ((111830400 : ℚ) / 23110423) * X ^ 2 + C ((869421600 : ℚ) / 161772961) * X ^ 3

def p5 : ℚ[X] :=
  C ((52731676140521 : ℚ) / 26246316616200) + C ((1421884513273063 : ℚ) / 104985266464800) * X ^ 1 + C ((859991046275557 : ℚ) / 52492633232400) * X ^ 2

def p6 : ℚ[X] :=
  C ((-5624390045802691666800 : ℚ) / 4571744221669573207609) + C ((-14486963191733946360600 : ℚ) / 4571744221669573207609) * X ^ 1

def p7 : ℚ[X] :=
  C ((-112217508888297371168670732185717 : ℚ) / 143932495388860369082595775280400)

def q0 : ℚ[X] :=
  C ((-3 : ℚ) / 49) + C ((1 : ℚ) / 7) * X ^ 1

def q1 : ℚ[X] :=
  C ((49147 : ℚ) / 10800) + C ((-343 : ℚ) / 180) * X ^ 1

def q2 : ℚ[X] :=
  C ((-1045299600 : ℚ) / 7926875089) + C ((648000 : ℚ) / 4362617) * X ^ 1

def q3 : ℚ[X] :=
  C ((85189468650850613 : ℚ) / 94486739818320000) + C ((-14403132036713 : ℚ) / 3129917760000) * X ^ 1

def q4 : ℚ[X] :=
  C ((777397853115270550539360000 : ℚ) / 32155852159744661800051115663) + C ((45638229173126379840000 : ℚ) / 139123297989484877814277) * X ^ 1

def q5 : ℚ[X] :=
  C ((-5708918124934778630025925604220148656716037571 : ℚ) / 2518465230223850523622798831313255822788320000) + C ((-3931659096497848251675841653383113213 : ℚ) / 760458845474968925707630594003440000) * X ^ 1

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
    p2.resultant p3 5 4 = ((7926875089 : ℚ) / 12960000) *
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
    _ = ((7926875089 : ℚ) / 12960000) *
        p3.resultant p4 4 3 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 4 3 = ((755893918546560000 : ℚ) / 26170490910707521) *
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
    _ = ((755893918546560000 : ℚ) / 26170490910707521) *
        p4.resultant p5 3 2 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep4 :
    p4.resultant p5 3 2 = ((739584599674127221401175660249 : ℚ) / 2755476543671264872409760000) *
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
    _ = ((739584599674127221401175660249 : ℚ) / 2755476543671264872409760000) *
        p5.resultant p6 2 1 := by
      norm_num [p5, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep5 :
    p5.resultant p6 2 1 = ((209872102518654210301899902609437985232360000 : ℚ) / 20900845228369131726294086235525805015496881) *
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
    _ = ((209872102518654210301899902609437985232360000 : ℚ) / 20900845228369131726294086235525805015496881) *
        p6.resultant p7 1 0 := by
      norm_num [p6, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p6.resultant p7 1 0 = ((-112217508888297371168670732185717 : ℚ) / 143932495388860369082595775280400) := by
  rw [show p7 = C ((-112217508888297371168670732185717 : ℚ) / 143932495388860369082595775280400) by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 ((-112217508888297371168670732185717 : ℚ) / 143932495388860369082595775280400))

theorem resultant_eq : p0.resultant p1 7 6 = (-24545885213 : ℚ) := by
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
    have hget : ([-1, -5, 0, 18, 8, -9, -3, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([-1, -5, 0, 18, 8, -9, -3, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
    row.polynomial.discr = (24545885213 : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h


theorem kernel_squarefree : Squarefree 24545885213 := by
  have hp0 : Prime (24545885213 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  rw [show 24545885213 = 24545885213 by norm_num]
  exact hp0.squarefree

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  { coefficients := [-1, -5, 0, 18, 8, -9, -3, 1]
    discriminant := 24545885213
    squarePart := 1
    kernel := 24545885213
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = (24545885213 : ℤ)
      exact polynomial_discr }


end

end DegreeSevenRows200To299SurvivorDiscriminantCase080
end TraceEuclidean
