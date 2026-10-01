import TraceEuclidean.DegreeSevenSurvivorDiscriminant

/-! Pure-kernel resultant certificate for retained septic 000. -/

namespace TraceEuclidean
namespace DegreeSevenRows200To299SurvivorDiscriminantCase000

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨500782544, [-1, -4, 2, 17, 6, -9, -3, 1], 1⟩

def p0 : ℚ[X] :=
  C (-1 : ℚ) + C (-4 : ℚ) * X ^ 1 + C (2 : ℚ) * X ^ 2 + C (17 : ℚ) * X ^ 3 + C (6 : ℚ) * X ^ 4 + C (-9 : ℚ) * X ^ 5 + C (-3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7

def p1 : ℚ[X] :=
  C (-4 : ℚ) + C (4 : ℚ) * X ^ 1 + C (51 : ℚ) * X ^ 2 + C (24 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6

def p2 : ℚ[X] :=
  C ((-61 : ℚ) / 49) + C ((-156 : ℚ) / 49) * X ^ 1 + C ((223 : ℚ) / 49) * X ^ 2 + C ((548 : ℚ) / 49) * X ^ 3 + C ((-9 : ℚ) / 49) * X ^ 4 + C ((-180 : ℚ) / 49) * X ^ 5

def p3 : ℚ[X] :=
  C ((7987 : ℚ) / 3600) + C ((7889 : ℚ) / 450) * X ^ 1 + C ((79919 : ℚ) / 3600) * X ^ 2 + C ((-3479 : ℚ) / 150) * X ^ 3 + C ((-81977 : ℚ) / 3600) * X ^ 4

def p4 : ℚ[X] :=
  C ((-123193600 : ℚ) / 137147521) + C ((-15722400 : ℚ) / 19592503) * X ^ 1 + C ((101713600 : ℚ) / 19592503) * X ^ 2 + C ((545660000 : ℚ) / 137147521) * X ^ 3

def p5 : ℚ[X] :=
  C ((686771560160819 : ℚ) / 186090522250000) + C ((1275182701178211 : ℚ) / 93045261125000) * X ^ 1 + C ((846707787545221 : ℚ) / 93045261125000) * X ^ 2

def p6 : ℚ[X] :=
  C ((-2998313383626236750000 : ℚ) / 5227320714675718432921) + C ((-6326823370756084250000 : ℚ) / 5227320714675718432921) * X ^ 1

def p7 : ℚ[X] :=
  C ((-163609435362450275741616983189 : ℚ) / 215103345838159040932830250000)

def q0 : ℚ[X] :=
  C ((-3 : ℚ) / 49) + C ((1 : ℚ) / 7) * X ^ 1

def q1 : ℚ[X] :=
  C ((17983 : ℚ) / 3600) + C ((-343 : ℚ) / 180) * X ^ 1

def q2 : ℚ[X] :=
  C ((-1049986800 : ℚ) / 6720228529) + C ((648000 : ℚ) / 4016873) * X ^ 1

def q3 : ℚ[X] :=
  C ((1097763315007718849 : ℚ) / 669925880100000000) + C ((-11242942329017 : ℚ) / 1964376000000) * X ^ 1

def q4 : ℚ[X] :=
  C ((-63069960287743910875900000000 : ℚ) / 716914077489723101969119938841) + C ((50771077185467500000000 : ℚ) / 116123874073221735547141) * X ^ 1

def q5 : ℚ[X] :=
  C ((-7765762187045193036963700630360485243820049 : ℚ) / 1000717349118634497643737709827451562500000) + C ((-4426013157112381004349857735542620541 : ℚ) / 588680932623752547723749781250000000) * X ^ 1

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
    p2.resultant p3 5 4 = ((6720228529 : ℚ) / 12960000) *
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
    _ = ((6720228529 : ℚ) / 12960000) *
        p3.resultant p4 4 3 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 4 3 = ((297744835600000000 : ℚ) / 18809442516445441) *
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
    _ = ((297744835600000000 : ℚ) / 18809442516445441) *
        p4.resultant p5 3 2 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep4 :
    p4.resultant p5 3 2 = ((716914077489723101969119938841 : ℚ) / 8657420617819436265625000000) *
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
    _ = ((716914077489723101969119938841 : ℚ) / 8657420617819436265625000000) *
        p5.resultant p6 2 1 := by
      norm_num [p5, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep5 :
    p5.resultant p6 2 1 = ((40028693964745379905749508393098062500000000 : ℚ) / 27324881854077863718935721051777211976592241) *
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
    _ = ((40028693964745379905749508393098062500000000 : ℚ) / 27324881854077863718935721051777211976592241) *
        p6.resultant p7 1 0 := by
      norm_num [p6, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p6.resultant p7 1 0 = ((-163609435362450275741616983189 : ℚ) / 215103345838159040932830250000) := by
  rw [show p7 = C ((-163609435362450275741616983189 : ℚ) / 215103345838159040932830250000) by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 ((-163609435362450275741616983189 : ℚ) / 215103345838159040932830250000))

theorem resultant_eq : p0.resultant p1 7 6 = (-500782544 : ℚ) := by
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
    have hget : ([-1, -4, 2, 17, 6, -9, -3, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([-1, -4, 2, 17, 6, -9, -3, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
    row.polynomial.discr = (500782544 : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h


theorem kernel_squarefree : Squarefree 31298909 := by
  have hp0 : Prime (19 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp1 : Prime (1647311 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  rw [show 31298909 = 19 * (1647311) by norm_num]
  exact (Nat.squarefree_mul (m := 19) (n := 1647311) (by norm_num)).mpr ⟨hp0.squarefree, hp1.squarefree⟩

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  { coefficients := [-1, -4, 2, 17, 6, -9, -3, 1]
    discriminant := 500782544
    squarePart := 4
    kernel := 31298909
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = (500782544 : ℤ)
      exact polynomial_discr }


end

end DegreeSevenRows200To299SurvivorDiscriminantCase000
end TraceEuclidean

/-! Pure-kernel resultant certificate for retained septic 001. -/

namespace TraceEuclidean
namespace DegreeSevenRows200To299SurvivorDiscriminantCase001

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨28118369, [1, -2, -5, 9, 7, -9, -3, 1], 1⟩

def p0 : ℚ[X] :=
  C (1 : ℚ) + C (-2 : ℚ) * X ^ 1 + C (-5 : ℚ) * X ^ 2 + C (9 : ℚ) * X ^ 3 + C (7 : ℚ) * X ^ 4 + C (-9 : ℚ) * X ^ 5 + C (-3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7

def p1 : ℚ[X] :=
  C (-2 : ℚ) + C (-10 : ℚ) * X ^ 1 + C (27 : ℚ) * X ^ 2 + C (28 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6

def p2 : ℚ[X] :=
  C ((43 : ℚ) / 49) + C ((-114 : ℚ) / 49) * X ^ 1 + C ((-94 : ℚ) / 49) * X ^ 2 + C ((48 : ℚ) / 7) * X ^ 3 + C ((12 : ℚ) / 49) * X ^ 4 + C ((-180 : ℚ) / 49) * X ^ 5

def p3 : ℚ[X] :=
  C ((-16709 : ℚ) / 2700) + C ((833 : ℚ) / 300) * X ^ 1 + C ((21413 : ℚ) / 675) * X ^ 2 + C ((-3773 : ℚ) / 450) * X ^ 3 + C ((-7448 : ℚ) / 225) * X ^ 4

def p4 : ℚ[X] :=
  C ((212775 : ℚ) / 323456) + C ((-3489525 : ℚ) / 2264192) * X ^ 1 + C ((-1725 : ℚ) / 1568) * X ^ 2 + C ((3440475 : ℚ) / 1132096) * X ^ 3

def p5 : ℚ[X] :=
  C ((-842718677248 : ℚ) / 473474729025) + C ((-61086202016 : ℚ) / 157824909675) * X ^ 1 + C ((716167325888 : ℚ) / 94694945805) * X ^ 2

def p6 : ℚ[X] :=
  C ((394619539377726477 : ℚ) / 906099197717452928) + C ((-1584426193263777051 : ℚ) / 1812198395434905856) * X ^ 1

def p7 : ℚ[X] :=
  C ((-12739015796011649584817216 : ℚ) / 132552288855515216824141041)

def q0 : ℚ[X] :=
  C ((-3 : ℚ) / 49) + C ((1 : ℚ) / 7) * X ^ 1

def q1 : ℚ[X] :=
  C ((12887 : ℚ) / 2700) + C ((-343 : ℚ) / 180) * X ^ 1

def q2 : ℚ[X] :=
  C ((-984825 : ℚ) / 27736352) + C ((10125 : ℚ) / 91238) * X ^ 1

def q3 : ℚ[X] :=
  C ((-47598048567328 : ℚ) / 7102120935375) + C ((-8431851008 : ℚ) / 774106875) * X ^ 1

def q4 : ℚ[X] :=
  C ((-128120307961659857000775 : ℚ) / 1025791277339137589977088) + C ((325795593668457375 : ℚ) / 810770164968501248) * X ^ 1

def q5 : ℚ[X] :=
  C ((-242638612106893607362721947540458954752 : ℚ) / 62760159047508594662574300465856415025) + C ((-1297837278837140913664551600128 : ℚ) / 150037152503135823914047721055) * X ^ 1

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
    p2.resultant p3 5 4 = ((55472704 : ℚ) / 50625) *
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
    _ = ((55472704 : ℚ) / 50625) *
        p3.resultant p4 4 3 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 4 3 = ((11836868225625 : ℚ) / 1281641353216) *
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
    _ = ((11836868225625 : ℚ) / 1281641353216) *
        p4.resultant p5 3 2 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep4 :
    p4.resultant p5 3 2 = ((512895638669568794988544 : ℚ) / 8967132761011887098025) *
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
    _ = ((512895638669568794988544 : ℚ) / 8967132761011887098025) *
        p5.resultant p6 2 1 := by
      norm_num [p5, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep5 :
    p5.resultant p6 2 1 = ((2510406361900343786502972018634256601 : ℚ) / 3284063024416847413627745343583092736) *
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
    _ = ((2510406361900343786502972018634256601 : ℚ) / 3284063024416847413627745343583092736) *
        p6.resultant p7 1 0 := by
      norm_num [p6, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p6.resultant p7 1 0 = ((-12739015796011649584817216 : ℚ) / 132552288855515216824141041) := by
  rw [show p7 = C ((-12739015796011649584817216 : ℚ) / 132552288855515216824141041) by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 ((-12739015796011649584817216 : ℚ) / 132552288855515216824141041))

theorem resultant_eq : p0.resultant p1 7 6 = (-28118369 : ℚ) := by
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
    have hget : ([1, -2, -5, 9, 7, -9, -3, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([1, -2, -5, 9, 7, -9, -3, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
    row.polynomial.discr = (28118369 : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h


theorem kernel_squarefree : Squarefree 28118369 := by
  have hp0 : Prime (28118369 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  rw [show 28118369 = 28118369 by norm_num]
  exact hp0.squarefree

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  { coefficients := [1, -2, -5, 9, 7, -9, -3, 1]
    discriminant := 28118369
    squarePart := 1
    kernel := 28118369
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = (28118369 : ℤ)
      exact polynomial_discr }


end

end DegreeSevenRows200To299SurvivorDiscriminantCase001
end TraceEuclidean

/-! Pure-kernel resultant certificate for retained septic 002. -/

namespace TraceEuclidean
namespace DegreeSevenRows200To299SurvivorDiscriminantCase002

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨178799897, [1, -2, -6, 10, 7, -9, -3, 1], 1⟩

def p0 : ℚ[X] :=
  C (1 : ℚ) + C (-2 : ℚ) * X ^ 1 + C (-6 : ℚ) * X ^ 2 + C (10 : ℚ) * X ^ 3 + C (7 : ℚ) * X ^ 4 + C (-9 : ℚ) * X ^ 5 + C (-3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7

def p1 : ℚ[X] :=
  C (-2 : ℚ) + C (-12 : ℚ) * X ^ 1 + C (30 : ℚ) * X ^ 2 + C (28 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6

def p2 : ℚ[X] :=
  C ((43 : ℚ) / 49) + C ((-120 : ℚ) / 49) * X ^ 1 + C ((-120 : ℚ) / 49) * X ^ 2 + C ((52 : ℚ) / 7) * X ^ 3 + C ((12 : ℚ) / 49) * X ^ 4 + C ((-180 : ℚ) / 49) * X ^ 5

def p3 : ℚ[X] :=
  C ((-16709 : ℚ) / 2700) + C ((49 : ℚ) / 36) * X ^ 1 + C ((1666 : ℚ) / 45) * X ^ 2 + C ((-8183 : ℚ) / 675) * X ^ 3 + C ((-2401 : ℚ) / 75) * X ^ 4

def p4 : ℚ[X] :=
  C ((594325 : ℚ) / 1058841) + C ((-589175 : ℚ) / 352947) * X ^ 1 + C ((-251725 : ℚ) / 352947) * X ^ 2 + C ((2711500 : ℚ) / 1058841) * X ^ 3

def p5 : ℚ[X] :=
  C ((-463796711343 : ℚ) / 294089290000) + C ((-1569402482949 : ℚ) / 294089290000) * X ^ 1 + C ((3027477364317 : ℚ) / 294089290000) * X ^ 2

def p6 : ℚ[X] :=
  C ((1891117431634832500 : ℚ) / 2885425098905882043) + C ((-921949705511312500 : ℚ) / 961808366301960681) * X ^ 1

def p7 : ℚ[X] :=
  C ((-1123995011951168893208169 : ℚ) / 2720234299045374856250000)

def q0 : ℚ[X] :=
  C ((-3 : ℚ) / 49) + C ((1 : ℚ) / 7) * X ^ 1

def q1 : ℚ[X] :=
  C ((12887 : ℚ) / 2700) + C ((-343 : ℚ) / 180) * X ^ 1

def q2 : ℚ[X] :=
  C ((-294600 : ℚ) / 5764801) + C ((13500 : ℚ) / 117649) * X ^ 1

def q3 : ℚ[X] :=
  C ((-181211371467707 : ℚ) / 22056696750000) + C ((-847425747 : ℚ) / 67787500) * X ^ 1

def q4 : ℚ[X] :=
  C ((182309006657233370750000 : ℚ) / 3055206397150603048292163) + C ((797423109835000000 : ℚ) / 3205617159910776597) * X ^ 1

def q5 : ℚ[X] :=
  C ((-3018822827864000447621929128003102609 : ℚ) / 1699982518984791684674130945312500000) + C ((-2911853057789899602663246419877 : ℚ) / 271135534309530980093125000000) * X ^ 1

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
    p2.resultant p3 5 4 = ((5764801 : ℚ) / 5625) *
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
    _ = ((5764801 : ℚ) / 5625) *
        p3.resultant p4 4 3 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 4 3 = ((7352232250000 : ℚ) / 1121144263281) *
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
    _ = ((7352232250000 : ℚ) / 1121144263281) *
        p4.resultant p5 3 2 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep4 :
    p4.resultant p5 3 2 = ((9165619191451809144876489 : ℚ) / 86488510492704100000000) *
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
    _ = ((9165619191451809144876489 : ℚ) / 86488510492704100000000) *
        p5.resultant p6 2 1 := by
      norm_num [p5, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep5 :
    p5.resultant p6 2 1 = ((849991259492395842337065472656250000 : ℚ) / 925075333488446574468894744869983761) *
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
    _ = ((849991259492395842337065472656250000 : ℚ) / 925075333488446574468894744869983761) *
        p6.resultant p7 1 0 := by
      norm_num [p6, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p6.resultant p7 1 0 = ((-1123995011951168893208169 : ℚ) / 2720234299045374856250000) := by
  rw [show p7 = C ((-1123995011951168893208169 : ℚ) / 2720234299045374856250000) by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 ((-1123995011951168893208169 : ℚ) / 2720234299045374856250000))

theorem resultant_eq : p0.resultant p1 7 6 = (-178799897 : ℚ) := by
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
    have hget : ([1, -2, -6, 10, 7, -9, -3, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([1, -2, -6, 10, 7, -9, -3, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
    row.polynomial.discr = (178799897 : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h


theorem kernel_squarefree : Squarefree 178799897 := by
  have hp0 : Prime (17 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp1 : Prime (10517641 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  rw [show 178799897 = 17 * (10517641) by norm_num]
  exact (Nat.squarefree_mul (m := 17) (n := 10517641) (by norm_num)).mpr ⟨hp0.squarefree, hp1.squarefree⟩

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  { coefficients := [1, -2, -6, 10, 7, -9, -3, 1]
    discriminant := 178799897
    squarePart := 1
    kernel := 178799897
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = (178799897 : ℤ)
      exact polynomial_discr }


end

end DegreeSevenRows200To299SurvivorDiscriminantCase002
end TraceEuclidean

/-! Pure-kernel resultant certificate for retained septic 003. -/

namespace TraceEuclidean
namespace DegreeSevenRows200To299SurvivorDiscriminantCase003

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨5165523209, [1, -3, -5, 12, 7, -9, -3, 1], 1⟩

def p0 : ℚ[X] :=
  C (1 : ℚ) + C (-3 : ℚ) * X ^ 1 + C (-5 : ℚ) * X ^ 2 + C (12 : ℚ) * X ^ 3 + C (7 : ℚ) * X ^ 4 + C (-9 : ℚ) * X ^ 5 + C (-3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7

def p1 : ℚ[X] :=
  C (-3 : ℚ) + C (-10 : ℚ) * X ^ 1 + C (36 : ℚ) * X ^ 2 + C (28 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6

def p2 : ℚ[X] :=
  C ((40 : ℚ) / 49) + C ((-156 : ℚ) / 49) * X ^ 1 + C ((-67 : ℚ) / 49) * X ^ 2 + C ((60 : ℚ) / 7) * X ^ 3 + C ((12 : ℚ) / 49) * X ^ 4 + C ((-180 : ℚ) / 49) * X ^ 5

def p3 : ℚ[X] :=
  C ((-931 : ℚ) / 135) + C ((1519 : ℚ) / 225) * X ^ 1 + C ((98441 : ℚ) / 2700) * X ^ 2 + C ((-931 : ℚ) / 60) * X ^ 3 + C ((-6713 : ℚ) / 225) * X ^ 4

def p4 : ℚ[X] :=
  C ((292575 : ℚ) / 919681) + C ((-1698525 : ℚ) / 919681) * X ^ 1 + C ((1601475 : ℚ) / 3678724) * X ^ 2 + C ((1556325 : ℚ) / 525532) * X ^ 3

def p5 : ℚ[X] :=
  C ((-552306654184 : ℚ) / 96885900225) + C ((97355628836 : ℚ) / 32295300075) * X ^ 1 + C ((1888232853583 : ℚ) / 96885900225) * X ^ 2

def p6 : ℚ[X] :=
  C ((59169362617916055225 : ℚ) / 189963413572923390481) + C ((-185619302853045897150 : ℚ) / 189963413572923390481) * X ^ 1

def p7 : ℚ[X] :=
  C ((-20025722891261252806297452521 : ℚ) / 7257542964147825716947608900)

def q0 : ℚ[X] :=
  C ((-3 : ℚ) / 49) + C ((1 : ℚ) / 7) * X ^ 1

def q1 : ℚ[X] :=
  C ((12887 : ℚ) / 2700) + C ((-343 : ℚ) / 180) * X ^ 1

def q2 : ℚ[X] :=
  C ((-465075 : ℚ) / 6437767) + C ((40500 : ℚ) / 328937) * X ^ 1

def q3 : ℚ[X] :=
  C ((-27311583640481 : ℚ) / 7266442516875) + C ((-3527896316 : ℚ) / 350173125) * X ^ 1

def q4 : ℚ[X] :=
  C ((-815078746778044590894375 : ℚ) / 698822968632639026723826244) + C ((150785948667673125 : ℚ) / 992326788009181156) * X ^ 1

def q5 : ℚ[X] :=
  C ((-9295853078677888002163076972659226499269 : ℚ) / 984415016904307792388025178412810803500) + C ((-358695158487168727271386008943423 : ℚ) / 17983893256054262628620511858750) * X ^ 1

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
    p2.resultant p3 5 4 = ((45064369 : ℚ) / 50625) *
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
    _ = ((45064369 : ℚ) / 50625) *
        p3.resultant p4 4 3 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 4 3 = ((2422147505625 : ℚ) / 276183883024) *
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
    _ = ((2422147505625 : ℚ) / 276183883024) *
        p4.resultant p5 3 2 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep4 :
    p4.resultant p5 3 2 = ((3565423309350199115937889 : ℚ) / 9386877662408655050625) *
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
    _ = ((3565423309350199115937889 : ℚ) / 9386877662408655050625) *
        p5.resultant p6 2 1 := by
      norm_num [p5, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep5 :
    p5.resultant p6 2 1 = ((34454525591650772733580881244448378122500 : ℚ) / 36086098496277534614846154666244401411361) *
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
    _ = ((34454525591650772733580881244448378122500 : ℚ) / 36086098496277534614846154666244401411361) *
        p6.resultant p7 1 0 := by
      norm_num [p6, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p6.resultant p7 1 0 = ((-20025722891261252806297452521 : ℚ) / 7257542964147825716947608900) := by
  rw [show p7 = C ((-20025722891261252806297452521 : ℚ) / 7257542964147825716947608900) by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 ((-20025722891261252806297452521 : ℚ) / 7257542964147825716947608900))

theorem resultant_eq : p0.resultant p1 7 6 = (-5165523209 : ℚ) := by
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
    have hget : ([1, -3, -5, 12, 7, -9, -3, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([1, -3, -5, 12, 7, -9, -3, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
    row.polynomial.discr = (5165523209 : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h


theorem kernel_squarefree : Squarefree 105418841 := by
  have hp0 : Prime (11 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp1 : Prime (149 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp2 : Prime (64319 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  rw [show 105418841 = 11 * (149 * (64319)) by norm_num]
  exact (Nat.squarefree_mul (m := 11) (n := 149 * (64319)) (by norm_num)).mpr ⟨hp0.squarefree, (Nat.squarefree_mul (m := 149) (n := 64319) (by norm_num)).mpr ⟨hp1.squarefree, hp2.squarefree⟩⟩

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  { coefficients := [1, -3, -5, 12, 7, -9, -3, 1]
    discriminant := 5165523209
    squarePart := 7
    kernel := 105418841
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = (5165523209 : ℤ)
      exact polynomial_discr }


end

end DegreeSevenRows200To299SurvivorDiscriminantCase003
end TraceEuclidean

/-! Pure-kernel resultant certificate for retained septic 004. -/

namespace TraceEuclidean
namespace DegreeSevenRows200To299SurvivorDiscriminantCase004

open Polynomial

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def row : VoightPolynomialRow :=
  ⟨9551576993, [1, -4, -5, 13, 7, -9, -3, 1], 1⟩

def p0 : ℚ[X] :=
  C (1 : ℚ) + C (-4 : ℚ) * X ^ 1 + C (-5 : ℚ) * X ^ 2 + C (13 : ℚ) * X ^ 3 + C (7 : ℚ) * X ^ 4 + C (-9 : ℚ) * X ^ 5 + C (-3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7

def p1 : ℚ[X] :=
  C (-4 : ℚ) + C (-10 : ℚ) * X ^ 1 + C (39 : ℚ) * X ^ 2 + C (28 : ℚ) * X ^ 3 + C (-45 : ℚ) * X ^ 4 + C (-18 : ℚ) * X ^ 5 + C (7 : ℚ) * X ^ 6

def p2 : ℚ[X] :=
  C ((37 : ℚ) / 49) + C ((-198 : ℚ) / 49) * X ^ 1 + C ((-58 : ℚ) / 49) * X ^ 2 + C ((64 : ℚ) / 7) * X ^ 3 + C ((12 : ℚ) / 49) * X ^ 4 + C ((-180 : ℚ) / 49) * X ^ 5

def p3 : ℚ[X] :=
  C ((-20531 : ℚ) / 2700) + C ((9653 : ℚ) / 900) * X ^ 1 + C ((24941 : ℚ) / 675) * X ^ 2 + C ((-24157 : ℚ) / 1350) * X ^ 3 + C ((-2156 : ℚ) / 75) * X ^ 4

def p4 : ℚ[X] :=
  C ((145925 : ℚ) / 1707552) + C ((-1209275 : ℚ) / 569184) * X ^ 1 + C ((298675 : ℚ) / 426888) * X ^ 2 + C ((2429275 : ℚ) / 853776) * X ^ 3

def p5 : ℚ[X] :=
  C ((-1718230176432 : ℚ) / 236055081025) + C ((33102176184 : ℚ) / 9442203241) * X ^ 1 + C ((171345159216 : ℚ) / 9442203241) * X ^ 2

def p6 : ℚ[X] :=
  C ((5007247589718505 : ℚ) / 34387431348218256) + C ((-139233662022819767 : ℚ) / 137549725392873024) * X ^ 1

def p7 : ℚ[X] :=
  C ((-328454198114008465552184208 : ℚ) / 51328096169617292638708225)

def q0 : ℚ[X] :=
  C ((-3 : ℚ) / 49) + C ((1 : ℚ) / 7) * X ^ 1

def q1 : ℚ[X] :=
  C ((12887 : ℚ) / 2700) + C ((-343 : ℚ) / 180) * X ^ 1

def q2 : ℚ[X] :=
  C ((-204675 : ℚ) / 2324168) + C ((3375 : ℚ) / 26411) * X ^ 1

def q3 : ℚ[X] :=
  C ((-13471461094168 : ℚ) / 3540826215375) + C ((-613580352 : ℚ) / 60731875) * X ^ 1

def q4 : ℚ[X] :=
  C ((485256224128360321375 : ℚ) / 58718327173512779469312) + C ((22937708278280275 : ℚ) / 146290384654799616) * X ^ 1

def q5 : ℚ[X] :=
  C ((-117134832849126863468782003517993472 : ℚ) / 19386012640284803451314249765934289) + C ((-23568479597558906448951389184 : ℚ) / 1314672534808167419926264847) * X ^ 1

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
    p2.resultant p3 5 4 = ((4648336 : ℚ) / 5625) *
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
    _ = ((4648336 : ℚ) / 5625) *
        p3.resultant p4 4 3 := by
      norm_num [p3, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep3 :
    p3.resultant p4 4 3 = ((5901377025625 : ℚ) / 728933458176) *
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
    _ = ((5901377025625 : ℚ) / 728933458176) *
        p4.resultant p5 3 2 := by
      norm_num [p4, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep4 :
    p4.resultant p5 3 2 = ((29359163586756389734656 : ℚ) / 89155202044350904081) *
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
    _ = ((29359163586756389734656 : ℚ) / 89155202044350904081) *
        p5.resultant p6 2 1 := by
      norm_num [p5, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantStep5 :
    p5.resultant p6 2 1 = ((19386012640284803451314249765934289 : ℚ) / 18919926955654777976586012986904576) *
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
    _ = ((19386012640284803451314249765934289 : ℚ) / 18919926955654777976586012986904576) *
        p6.resultant p7 1 0 := by
      norm_num [p6, Polynomial.coeff_one, Polynomial.coeff_X]

lemma resultantLast :
    p6.resultant p7 1 0 = ((-328454198114008465552184208 : ℚ) / 51328096169617292638708225) := by
  rw [show p7 = C ((-328454198114008465552184208 : ℚ) / 51328096169617292638708225) by rfl]
  simpa [p6] using
    (Polynomial.resultant_C_right p6 1 0 ((-328454198114008465552184208 : ℚ) / 51328096169617292638708225))

theorem resultant_eq : p0.resultant p1 7 6 = (-9551576993 : ℚ) := by
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
    have hget : ([1, -4, -5, 13, 7, -9, -3, 1] : List ℤ).getD n 0 = 0 :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
    · change ((([1, -4, -5, 13, 7, -9, -3, 1] : List ℤ).getD n 0 : ℤ) : ℚ) = 0
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
    row.polynomial.discr = (9551576993 : ℤ) := by
  have h := voightPolynomial_discr_eq_of_resultant 7 row
    (by norm_num) (by norm_num [row]) (by norm_num [row]) row_resultant
  simpa [row] using h


theorem kernel_squarefree : Squarefree 9551576993 := by
  have hp0 : Prime (7 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  have hp1 : Prime (1364510999 : ℕ) :=
    Nat.prime_iff.mp (by norm_num)
  rw [show 9551576993 = 7 * (1364510999) by norm_num]
  exact (Nat.squarefree_mul (m := 7) (n := 1364510999) (by norm_num)).mpr ⟨hp0.squarefree, hp1.squarefree⟩

def certificate : DegreeSevenSurvivorDiscriminantCertificate :=
  { coefficients := [1, -4, -5, 13, 7, -9, -3, 1]
    discriminant := 9551576993
    squarePart := 1
    kernel := 9551576993
    squarePartPositive := by norm_num
    kernelPositive := by norm_num
    discriminantFactorization := by norm_num
    kernelSquarefree := kernel_squarefree
    thresholdLowerBound := by norm_num
    polynomialDiscriminant := by
      change row.polynomial.discr = (9551576993 : ℤ)
      exact polynomial_discr }


end

end DegreeSevenRows200To299SurvivorDiscriminantCase004
end TraceEuclidean
