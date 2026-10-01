import TraceEuclidean.DegreeSevenSurvivorDiscriminant

/-! Pure-kernel resultant certificate for retained septic 011. -/

namespace TraceEuclidean
namespace DegreeSevenRows200To299SurvivorDiscriminantCase011

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨5884241393, [-1, -6, -3, 15, 7, -9, -3, 1], 1⟩

def p0 : ℚ[X] :=
  C (-1 : ℚ) + C (-6 : ℚ) * X ^ 1 + C (-3 : ℚ) * X ^ 2 + C (15 : ℚ) * X ^ 3 + C (7 : ℚ) * X ^ 4 + C (-9 : ℚ) * X ^ 5 + C (-3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7

def p1 : ℚ[X] :=
  C (-6 : ℚ) + C (-6 : ℚ) * X ^ 1 + C (45 : ℚ) * X ^ 2 + C (28 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6

def p2 : ℚ[X] :=
  C ((-67 : ℚ) / 49) + C ((-270 : ℚ) / 49) * X ^ 1 + C ((30 : ℚ) / 49) * X ^ 2 + C ((72 : ℚ) / 7) * X ^ 3 + C ((12 : ℚ) / 49) * X ^ 4 + C ((-180 : ℚ) / 49) * X ^ 5

def p3 : ℚ[X] :=
  C ((1421 : ℚ) / 2700) + C ((637 : ℚ) / 36) * X ^ 1 + C ((1421 : ℚ) / 45) * X ^ 2 + C ((-2989 : ℚ) / 150) * X ^ 3 + C ((-5978 : ℚ) / 225) * X ^ 4

def p4 : ℚ[X] :=
  C ((-31275 : ℚ) / 23912) + C ((-85725 : ℚ) / 23912) * X ^ 1 + C ((5175 : ℚ) / 2989) * X ^ 2 + C ((43875 : ℚ) / 11956) * X ^ 3

def p5 : ℚ[X] :=
  C ((-18036508 : ℚ) / 8555625) + C ((954422 : ℚ) / 950625) * X ^ 1 + C ((77936068 : ℚ) / 8555625) * X ^ 2

def p6 : ℚ[X] :=
  C ((-31016077048125 : ℚ) / 30989952527044) + C ((-357251612079375 : ℚ) / 123959810108176) * X ^ 1

def p7 : ℚ[X] :=
  C ((-182352361426737256732292 : ℚ) / 134257687661603931530625)

def q0 : ℚ[X] :=
  C ((-3 : ℚ) / 49) + C ((1 : ℚ) / 7) * X ^ 1

def q1 : ℚ[X] :=
  C ((12887 : ℚ) / 2700) + C ((-343 : ℚ) / 180) * X ^ 1

def q2 : ℚ[X] :=
  C ((-675 : ℚ) / 5978) + C ((20250 : ℚ) / 146461) * X ^ 1

def q3 : ℚ[X] :=
  C ((-3877408514 : ℚ) / 1925015625) + C ((-71472968 : ℚ) / 9871875) * X ^ 1

def q4 : ℚ[X] :=
  C ((15420070086890625 : ℚ) / 105861677832382304) + C ((375378046875 : ℚ) / 931803629008) * X ^ 1

def q5 : ℚ[X] :=
  C ((286891961937936170292527608096 : ℚ) / 382886142999936712233901171875) + C ((-9660940189857892091968 : ℚ) / 3056510823596602734375) * X ^ 1

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
    p2.resultant p3 5 4 = ((35736484 : ℚ) / 50625) *
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
    _ = ((35736484 : ℚ) / 50625) *
        p3.resultant p4 4 3 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 4 3 = ((1925015625 : ℚ) / 142945936) *
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
    _ = ((1925015625 : ℚ) / 142945936) *
        p4.resultant p5 3 2 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep4 :
    p4.resultant p5 3 2 = ((6074030695300624 : ℚ) / 73198719140625) *
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
    _ = ((6074030695300624 : ℚ) / 73198719140625) *
        p5.resultant p6 2 1 := by
      norm_num [p5, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep5 :
    p5.resultant p6 2 1 = ((127628714333312237411300390625 : ℚ) / 15366034522055052824822046976) *
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
    _ = ((127628714333312237411300390625 : ℚ) / 15366034522055052824822046976) *
        p6.resultant p7 1 0 := by
      norm_num [p6, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p6.resultant p7 1 0 = ((-182352361426737256732292 : ℚ) / 134257687661603931530625) := by
  rw [show p7 = C ((-182352361426737256732292 : ℚ) / 134257687661603931530625) by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 ((-182352361426737256732292 : ℚ) / 134257687661603931530625))

theorem resultant_eq : p0.resultant p1 7 6 = (-5884241393 : ℚ) := by
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
    have hget : ([-1, -6, -3, 15, 7, -9, -3, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([-1, -6, -3, 15, 7, -9, -3, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
    row.polynomial.discr = (5884241393 : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h


theorem kernel_squarefree : Squarefree 5884241393 := by
  have hp0 : Prime (5884241393 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  rw [show 5884241393 = 5884241393 by norm_num]
  exact hp0.squarefree

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  { coefficients := [-1, -6, -3, 15, 7, -9, -3, 1]
    discriminant := 5884241393
    squarePart := 1
    kernel := 5884241393
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = (5884241393 : ℤ)
      exact polynomial_discr }


end

end DegreeSevenRows200To299SurvivorDiscriminantCase011
end TraceEuclidean

/-! Pure-kernel resultant certificate for retained septic 012. -/

namespace TraceEuclidean
namespace DegreeSevenRows200To299SurvivorDiscriminantCase012

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨2787888809, [1, -4, -3, 15, 7, -9, -3, 1], 1⟩

def p0 : ℚ[X] :=
  C (1 : ℚ) + C (-4 : ℚ) * X ^ 1 + C (-3 : ℚ) * X ^ 2 + C (15 : ℚ) * X ^ 3 + C (7 : ℚ) * X ^ 4 + C (-9 : ℚ) * X ^ 5 + C (-3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7

def p1 : ℚ[X] :=
  C (-4 : ℚ) + C (-6 : ℚ) * X ^ 1 + C (45 : ℚ) * X ^ 2 + C (28 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6

def p2 : ℚ[X] :=
  C ((37 : ℚ) / 49) + C ((-186 : ℚ) / 49) * X ^ 1 + C ((30 : ℚ) / 49) * X ^ 2 + C ((72 : ℚ) / 7) * X ^ 3 + C ((12 : ℚ) / 49) * X ^ 4 + C ((-180 : ℚ) / 49) * X ^ 5

def p3 : ℚ[X] :=
  C ((-20531 : ℚ) / 2700) + C ((4067 : ℚ) / 300) * X ^ 1 + C ((1568 : ℚ) / 45) * X ^ 2 + C ((-2989 : ℚ) / 150) * X ^ 3 + C ((-5978 : ℚ) / 225) * X ^ 4

def p4 : ℚ[X] :=
  C ((-2475 : ℚ) / 23912) + C ((-29025 : ℚ) / 23912) * X ^ 1 + C ((15975 : ℚ) / 5978) * X ^ 2 + C ((38475 : ℚ) / 11956) * X ^ 3

def p5 : ℚ[X] :=
  C ((-49576828 : ℚ) / 6579225) + C ((5924786 : ℚ) / 438615) * X ^ 1 + C ((151643044 : ℚ) / 6579225) * X ^ 2

def p6 : ℚ[X] :=
  C ((18017718648975 : ℚ) / 117324555069316) + C ((-292176506959875 : ℚ) / 469298220277264) * X ^ 1

def p7 : ℚ[X] :=
  C ((-327087814098650295684644 : ℚ) / 116777280146744481125625)

def q0 : ℚ[X] :=
  C ((-3 : ℚ) / 49) + C ((1 : ℚ) / 7) * X ^ 1

def q1 : ℚ[X] :=
  C ((12887 : ℚ) / 2700) + C ((-343 : ℚ) / 180) * X ^ 1

def q2 : ℚ[X] :=
  C ((-675 : ℚ) / 5978) + C ((20250 : ℚ) / 146461) * X ^ 1

def q3 : ℚ[X] :=
  C ((196550662 : ℚ) / 296065125) + C ((-71472968 : ℚ) / 8656875) * X ^ 1

def q4 : ℚ[X] :=
  C ((95711150517744375 : ℚ) / 2805464760817484192) + C ((253135681875 : ℚ) / 1813044234064) * X ^ 1

def q5 : ℚ[X] :=
  C ((-7895259732831302141197587372512 : ℚ) / 256101333657821652944580046875) + C ((-71165810666626836951616 : ℚ) / 1922294979003083596875) * X ^ 1

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
    p2.resultant p3 5 4 = ((35736484 : ℚ) / 50625) *
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
    _ = ((35736484 : ℚ) / 50625) *
        p3.resultant p4 4 3 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 4 3 = ((1480325625 : ℚ) / 142945936) *
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
    _ = ((1480325625 : ℚ) / 142945936) *
        p4.resultant p5 3 2 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep4 :
    p4.resultant p5 3 2 = ((22995612793585936 : ℚ) / 43286201600625) *
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
    _ = ((22995612793585936 : ℚ) / 43286201600625) *
        p5.resultant p6 2 1 := by
      norm_num [p5, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep5 :
    p5.resultant p6 2 1 = ((85367111219273884314860015625 : ℚ) / 220240819555407403417035325696) *
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
    _ = ((85367111219273884314860015625 : ℚ) / 220240819555407403417035325696) *
        p6.resultant p7 1 0 := by
      norm_num [p6, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p6.resultant p7 1 0 = ((-327087814098650295684644 : ℚ) / 116777280146744481125625) := by
  rw [show p7 = C ((-327087814098650295684644 : ℚ) / 116777280146744481125625) by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 ((-327087814098650295684644 : ℚ) / 116777280146744481125625))

theorem resultant_eq : p0.resultant p1 7 6 = (-2787888809 : ℚ) := by
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
    have hget : ([1, -4, -3, 15, 7, -9, -3, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([1, -4, -3, 15, 7, -9, -3, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
    row.polynomial.discr = (2787888809 : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h


theorem kernel_squarefree : Squarefree 2787888809 := by
  have hp0 : Prime (313 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp1 : Prime (1753 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp2 : Prime (5081 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  rw [show 2787888809 = 313 * (1753 * (5081)) by norm_num]
  exact (Nat.squarefree_mul (m := 313) (n := 1753 * (5081)) (by norm_num)).mpr ⟨hp0.squarefree, (Nat.squarefree_mul (m := 1753) (n := 5081) (by norm_num)).mpr ⟨hp1.squarefree, hp2.squarefree⟩⟩

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  { coefficients := [1, -4, -3, 15, 7, -9, -3, 1]
    discriminant := 2787888809
    squarePart := 1
    kernel := 2787888809
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = (2787888809 : ℤ)
      exact polynomial_discr }


end

end DegreeSevenRows200To299SurvivorDiscriminantCase012
end TraceEuclidean

/-! Pure-kernel resultant certificate for retained septic 013. -/

namespace TraceEuclidean
namespace DegreeSevenRows200To299SurvivorDiscriminantCase013

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨675836981, [-1, -5, -2, 15, 7, -9, -3, 1], 1⟩

def p0 : ℚ[X] :=
  C (-1 : ℚ) + C (-5 : ℚ) * X ^ 1 + C (-2 : ℚ) * X ^ 2 + C (15 : ℚ) * X ^ 3 + C (7 : ℚ) * X ^ 4 + C (-9 : ℚ) * X ^ 5 + C (-3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7

def p1 : ℚ[X] :=
  C (-5 : ℚ) + C (-4 : ℚ) * X ^ 1 + C (45 : ℚ) * X ^ 2 + C (28 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6

def p2 : ℚ[X] :=
  C ((-64 : ℚ) / 49) + C ((-222 : ℚ) / 49) * X ^ 1 + C ((65 : ℚ) / 49) * X ^ 2 + C ((72 : ℚ) / 7) * X ^ 3 + C ((12 : ℚ) / 49) * X ^ 4 + C ((-180 : ℚ) / 49) * X ^ 5

def p3 : ℚ[X] :=
  C ((833 : ℚ) / 675) + C ((6811 : ℚ) / 450) * X ^ 1 + C ((16219 : ℚ) / 540) * X ^ 2 + C ((-16709 : ℚ) / 900) * X ^ 3 + C ((-5978 : ℚ) / 225) * X ^ 4

def p4 : ℚ[X] :=
  C ((-122475 : ℚ) / 104188) + C ((-4520925 : ℚ) / 1458632) * X ^ 1 + C ((7037925 : ℚ) / 2917264) * X ^ 2 + C ((12159675 : ℚ) / 2917264) * X ^ 3

def p5 : ℚ[X] :=
  C ((1981732442368 : ℚ) / 5914307844225) + C ((10393787170088 : ℚ) / 1971435948075) * X ^ 1 + C ((71703611997052 : ℚ) / 5914307844225) * X ^ 2

def p6 : ℚ[X] :=
  C ((-8403861335173141243725 : ℚ) / 7049630027894327703844) + C ((-12250528635634042299975 : ℚ) / 3524815013947163851922) * X ^ 1

def p7 : ℚ[X] :=
  C ((-1191100168804762055597647763741 : ℚ) / 25374981452653024785945699858225)

def q0 : ℚ[X] :=
  C ((-3 : ℚ) / 49) + C ((1 : ℚ) / 7) * X ^ 1

def q1 : ℚ[X] :=
  C ((12887 : ℚ) / 2700) + C ((-343 : ℚ) / 180) * X ^ 1

def q2 : ℚ[X] :=
  C ((-3782025 : ℚ) / 35736484) + C ((20250 : ℚ) / 146461) * X ^ 1

def q3 : ℚ[X] :=
  C ((-339230611349588 : ℚ) / 443573088316875) + C ((-17439404192 : ℚ) / 2735926875) * X ^ 1

def q4 : ℚ[X] :=
  C ((1017642653667095550047105625 : ℚ) / 20565631893695118014626762816) + C ((71916061235726626875 : ℚ) / 209178365948967905728) * X ^ 1

def q5 : ℚ[X] :=
  C ((-16030806957407497372943588821703809833275852 : ℚ) / 50025150617496556642897334735469195961666875) + C ((-252741968121450870677524303228533944 : ℚ) / 72453397605633403231187603021394375) * X ^ 1

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
    p2.resultant p3 5 4 = ((35736484 : ℚ) / 50625) *
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
    _ = ((35736484 : ℚ) / 50625) *
        p3.resultant p4 4 3 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 4 3 = ((147857696105625 : ℚ) / 8510429245696) *
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
    _ = ((147857696105625 : ℚ) / 8510429245696) *
        p4.resultant p5 3 2 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep4 :
    p4.resultant p5 3 2 = ((5141407973423779503656690704 : ℚ) / 34979037276261366865850625) *
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
    _ = ((5141407973423779503656690704 : ℚ) / 34979037276261366865850625) *
        p5.resultant p6 2 1 := by
      norm_num [p5, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep5 :
    p5.resultant p6 2 1 = ((150075451852489669928692004206407587885000625 : ℚ) / 12424320882547344899948268372359720343094084) *
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
    _ = ((150075451852489669928692004206407587885000625 : ℚ) / 12424320882547344899948268372359720343094084) *
        p6.resultant p7 1 0 := by
      norm_num [p6, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p6.resultant p7 1 0 = ((-1191100168804762055597647763741 : ℚ) / 25374981452653024785945699858225) := by
  rw [show p7 = C ((-1191100168804762055597647763741 : ℚ) / 25374981452653024785945699858225) by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 ((-1191100168804762055597647763741 : ℚ) / 25374981452653024785945699858225))

theorem resultant_eq : p0.resultant p1 7 6 = (-675836981 : ℚ) := by
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
    have hget : ([-1, -5, -2, 15, 7, -9, -3, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([-1, -5, -2, 15, 7, -9, -3, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
    row.polynomial.discr = (675836981 : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h


theorem kernel_squarefree : Squarefree 675836981 := by
  have hp0 : Prime (675836981 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  rw [show 675836981 = 675836981 by norm_num]
  exact hp0.squarefree

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  { coefficients := [-1, -5, -2, 15, 7, -9, -3, 1]
    discriminant := 675836981
    squarePart := 1
    kernel := 675836981
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = (675836981 : ℤ)
      exact polynomial_discr }


end

end DegreeSevenRows200To299SurvivorDiscriminantCase013
end TraceEuclidean

/-! Pure-kernel resultant certificate for retained septic 014. -/

namespace TraceEuclidean
namespace DegreeSevenRows200To299SurvivorDiscriminantCase014

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨1674073729, [-1, -4, 1, 15, 7, -9, -3, 1], 1⟩

def p0 : ℚ[X] :=
  C (-1 : ℚ) + C (-4 : ℚ) * X ^ 1 + C (1 : ℚ) * X ^ 2 + C (15 : ℚ) * X ^ 3 + C (7 : ℚ) * X ^ 4 + C (-9 : ℚ) * X ^ 5 + C (-3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7

def p1 : ℚ[X] :=
  C (-4 : ℚ) + C (2 : ℚ) * X ^ 1 + C (45 : ℚ) * X ^ 2 + C (28 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6

def p2 : ℚ[X] :=
  C ((-61 : ℚ) / 49) + C ((-162 : ℚ) / 49) * X ^ 1 + C ((170 : ℚ) / 49) * X ^ 2 + C ((72 : ℚ) / 7) * X ^ 3 + C ((12 : ℚ) / 49) * X ^ 4 + C ((-180 : ℚ) / 49) * X ^ 5

def p3 : ℚ[X] :=
  C ((5243 : ℚ) / 2700) + C ((13867 : ℚ) / 900) * X ^ 1 + C ((2989 : ℚ) / 135) * X ^ 2 + C ((-6517 : ℚ) / 450) * X ^ 3 + C ((-5978 : ℚ) / 225) * X ^ 4

def p4 : ℚ[X] :=
  C ((-1576275 : ℚ) / 1458632) + C ((-3313125 : ℚ) / 1458632) * X ^ 1 + C ((9600 : ℚ) / 2989) * X ^ 2 + C ((4375575 : ℚ) / 729316) * X ^ 3

def p5 : ℚ[X] :=
  C ((1451400102544 : ℚ) / 765826263225) + C ((179102870674 : ℚ) / 17018361405) * X ^ 1 + C ((1871766905204 : ℚ) / 153165252645) * X ^ 2

def p6 : ℚ[X] :=
  C ((-7469744848146249615 : ℚ) / 9607663474864009352) + C ((-595397295458624115 : ℚ) / 392149529586286096) * X ^ 1

def p7 : ℚ[X] :=
  C ((-164121806330027447997892996 : ℚ) / 567047640785509797230871225)

def q0 : ℚ[X] :=
  C ((-3 : ℚ) / 49) + C ((1 : ℚ) / 7) * X ^ 1

def q1 : ℚ[X] :=
  C ((12887 : ℚ) / 2700) + C ((-343 : ℚ) / 180) * X ^ 1

def q2 : ℚ[X] :=
  C ((-1511325 : ℚ) / 17868242) + C ((20250 : ℚ) / 146461) * X ^ 1

def q3 : ℚ[X] :=
  C ((-495825847258 : ℚ) / 11487393948375) + C ((-4359851048 : ℚ) / 984504375) * X ^ 1

def q4 : ℚ[X] :=
  C ((-160129832486292271810125 : ℚ) / 1001003242119131406366176) + C ((670186050342145875 : ℚ) / 1365109552235760464) * X ^ 1

def q5 : ℚ[X] :=
  C ((-996106211540762188974498250933687648 : ℚ) / 354497939439444140195873928859533225) + C ((-734012511370927160390055243584 : ℚ) / 91194177183069873718064534175) * X ^ 1

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
    p2.resultant p3 5 4 = ((35736484 : ℚ) / 50625) *
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
    _ = ((35736484 : ℚ) / 50625) *
        p3.resultant p4 4 3 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 4 3 = ((19145656580625 : ℚ) / 531901827856) *
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
    _ = ((19145656580625 : ℚ) / 531901827856) *
        p4.resultant p5 3 2 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep4 :
    p4.resultant p5 3 2 = ((3503511347416959922281616 : ℚ) / 23459594617806679496025) *
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
    _ = ((3503511347416959922281616 : ℚ) / 23459594617806679496025) *
        p5.resultant p6 2 1 := by
      norm_num [p5, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep5 :
    p5.resultant p6 2 1 = ((354497939439444140195873928859533225 : ℚ) / 153781253554745474155028954362921216) *
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
    _ = ((354497939439444140195873928859533225 : ℚ) / 153781253554745474155028954362921216) *
        p6.resultant p7 1 0 := by
      norm_num [p6, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p6.resultant p7 1 0 = ((-164121806330027447997892996 : ℚ) / 567047640785509797230871225) := by
  rw [show p7 = C ((-164121806330027447997892996 : ℚ) / 567047640785509797230871225) by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 ((-164121806330027447997892996 : ℚ) / 567047640785509797230871225))

theorem resultant_eq : p0.resultant p1 7 6 = (-1674073729 : ℚ) := by
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
    have hget : ([-1, -4, 1, 15, 7, -9, -3, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([-1, -4, 1, 15, 7, -9, -3, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
    row.polynomial.discr = (1674073729 : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h


theorem kernel_squarefree : Squarefree 1674073729 := by
  have hp0 : Prime (59 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp1 : Prime (83 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp2 : Prime (103 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp3 : Prime (3319 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  rw [show 1674073729 = 59 * (83 * (103 * (3319))) by norm_num]
  exact (Nat.squarefree_mul (m := 59) (n := 83 * (103 * (3319))) (by norm_num)).mpr ⟨hp0.squarefree, (Nat.squarefree_mul (m := 83) (n := 103 * (3319)) (by norm_num)).mpr ⟨hp1.squarefree, (Nat.squarefree_mul (m := 103) (n := 3319) (by norm_num)).mpr ⟨hp2.squarefree, hp3.squarefree⟩⟩⟩

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  { coefficients := [-1, -4, 1, 15, 7, -9, -3, 1]
    discriminant := 1674073729
    squarePart := 1
    kernel := 1674073729
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = (1674073729 : ℤ)
      exact polynomial_discr }


end

end DegreeSevenRows200To299SurvivorDiscriminantCase014
end TraceEuclidean

/-! Pure-kernel resultant certificate for retained septic 015. -/

namespace TraceEuclidean
namespace DegreeSevenRows200To299SurvivorDiscriminantCase015

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨6714752321, [-1, -7, -3, 16, 7, -9, -3, 1], 1⟩

def p0 : ℚ[X] :=
  C (-1 : ℚ) + C (-7 : ℚ) * X ^ 1 + C (-3 : ℚ) * X ^ 2 + C (16 : ℚ) * X ^ 3 + C (7 : ℚ) * X ^ 4 + C (-9 : ℚ) * X ^ 5 + C (-3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7

def p1 : ℚ[X] :=
  C (-7 : ℚ) + C (-6 : ℚ) * X ^ 1 + C (48 : ℚ) * X ^ 2 + C (28 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6

def p2 : ℚ[X] :=
  C ((-10 : ℚ) / 7) + C ((-312 : ℚ) / 49) * X ^ 1 + C ((39 : ℚ) / 49) * X ^ 2 + C ((76 : ℚ) / 7) * X ^ 3 + C ((12 : ℚ) / 49) * X ^ 4 + C ((-180 : ℚ) / 49) * X ^ 5

def p3 : ℚ[X] :=
  C ((-49 : ℚ) / 270) + C ((9751 : ℚ) / 450) * X ^ 1 + C ((28861 : ℚ) / 900) * X ^ 2 + C ((-60221 : ℚ) / 2700) * X ^ 3 + C ((-637 : ℚ) / 25) * X ^ 4

def p4 : ℚ[X] :=
  C ((-1949525 : ℚ) / 1341522) + C ((-1519625 : ℚ) / 447174) * X ^ 1 + C ((1812925 : ℚ) / 894348) * X ^ 2 + C ((8598475 : ℚ) / 2683044) * X ^ 3

def p5 : ℚ[X] :=
  C ((-8834044448502 : ℚ) / 2957350893025) + C ((10509977028096 : ℚ) / 2957350893025) * X ^ 1 + C ((26505608558247 : ℚ) / 2957350893025) * X ^ 2

def p6 : ℚ[X] :=
  C ((-419351856838644078775 : ℚ) / 349129463918850683523) + C ((-918239666775991847650 : ℚ) / 349129463918850683523) * X ^ 1

def p7 : ℚ[X] :=
  C ((-781439292726196127612833568961 : ℚ) / 285107894240589477880353232900)

def q0 : ℚ[X] :=
  C ((-3 : ℚ) / 49) + C ((1 : ℚ) / 7) * X ^ 1

def q1 : ℚ[X] :=
  C ((12887 : ℚ) / 2700) + C ((-343 : ℚ) / 180) * X ^ 1

def q2 : ℚ[X] :=
  C ((-165325 : ℚ) / 1217307) + C ((4500 : ℚ) / 31213) * X ^ 1

def q3 : ℚ[X] :=
  C ((-142740721303089 : ℚ) / 73933772325625) + C ((-1709099028 : ℚ) / 214961875) * X ^ 1

def q4 : ℚ[X] :=
  C ((79049903939418923789381875 : ℚ) / 936729713390688813322284012) + C ((25428707719903136875 : ℚ) / 71115714008553263868) * X ^ 1

def q5 : ℚ[X] :=
  C ((172891059036797936235897695099313744472323 : ℚ) / 843164085640884546611881117419260810522500) + C ((-9253888906783675872299334508664181 : ℚ) / 2715556898550957913277847247641250) * X ^ 1

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
    p2.resultant p3 5 4 = ((405769 : ℚ) / 625) *
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
    _ = ((405769 : ℚ) / 625) *
        p3.resultant p4 4 3 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 4 3 = ((73933772325625 : ℚ) / 7198725105936) *
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
    _ = ((73933772325625 : ℚ) / 7198725105936) *
        p4.resultant p5 3 2 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep4 :
    p4.resultant p5 3 2 = ((702547285043016609991713009 : ℚ) / 8745924304475764993650625) *
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
    _ = ((702547285043016609991713009 : ℚ) / 8745924304475764993650625) *
        p5.resultant p6 2 1 := by
      norm_num [p5, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep5 :
    p5.resultant p6 2 1 = ((843164085640884546611881117419260810522500 : ℚ) / 121891382576264061275422454908684303691529) *
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
    _ = ((843164085640884546611881117419260810522500 : ℚ) / 121891382576264061275422454908684303691529) *
        p6.resultant p7 1 0 := by
      norm_num [p6, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p6.resultant p7 1 0 = ((-781439292726196127612833568961 : ℚ) / 285107894240589477880353232900) := by
  rw [show p7 = C ((-781439292726196127612833568961 : ℚ) / 285107894240589477880353232900) by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 ((-781439292726196127612833568961 : ℚ) / 285107894240589477880353232900))

theorem resultant_eq : p0.resultant p1 7 6 = (-6714752321 : ℚ) := by
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
    have hget : ([-1, -7, -3, 16, 7, -9, -3, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([-1, -7, -3, 16, 7, -9, -3, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
    row.polynomial.discr = (6714752321 : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h


theorem kernel_squarefree : Squarefree 6714752321 := by
  have hp0 : Prime (887 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp1 : Prime (7570183 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  rw [show 6714752321 = 887 * (7570183) by norm_num]
  exact (Nat.squarefree_mul (m := 887) (n := 7570183) (by norm_num)).mpr ⟨hp0.squarefree, hp1.squarefree⟩

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  { coefficients := [-1, -7, -3, 16, 7, -9, -3, 1]
    discriminant := 6714752321
    squarePart := 1
    kernel := 6714752321
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = (6714752321 : ℤ)
      exact polynomial_discr }


end

end DegreeSevenRows200To299SurvivorDiscriminantCase015
end TraceEuclidean
