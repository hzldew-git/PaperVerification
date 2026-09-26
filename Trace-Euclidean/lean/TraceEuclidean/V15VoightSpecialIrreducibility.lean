import TraceEuclidean.V15VoightExceptionalIrreducibilityCertificates

/-!
# The exceptional degree-eight Voight polynomial

The polynomial
`X^8 - 14 X^6 + 52 X^4 - 56 X^2 + 16` is the only archived
Voight polynomial not settled by the single-prime or multi-prime degree
exclusion certificates.  Factorizations modulo `3` and `5` force the
constant coefficient of any monic quartic divisor to be `4`.  Comparing
integer coefficients then reduces the remaining possibility to three finite
Diophantine contradictions.
-/

namespace TraceEuclidean

open Polynomial

/-- The two modular factorizations and divisibility of the source constant
force the constant coefficient of a hypothetical quartic factor to be `4`. -/
theorem v15_voightSpecialEight_quartic_constantCoeff
    {divisor : ℤ[X]} (hdivisorMonic : divisor.Monic)
    (hdivisorDegree : divisor.natDegree = 4)
    (hdivides : divisor ∣ v15VoightSpecialEightRow.polynomial) :
    divisor.coeff 0 = 4 := by
  have hthree :
      (divisor.coeff 0 : ZMod 3) = ((1 : ℤ) : ZMod 3) :=
    V15ModularFactorizationCertificate.constantCoeff_mod_eq_of_valid_and_forcesConstantResidue
        v15_voightSpecialEightFactorizationThree_valid
        v15_voightSpecialEight_forces_constant_three
        hdivisorMonic hdivisorDegree hdivides
  have hfive :
      (divisor.coeff 0 : ZMod 5) = ((4 : ℤ) : ZMod 5) :=
    V15ModularFactorizationCertificate.constantCoeff_mod_eq_of_valid_and_forcesConstantResidue
        v15_voightSpecialEightFactorizationFive_valid
        v15_voightSpecialEight_forces_constant_five
        hdivisorMonic hdivisorDegree hdivides
  have hdvd : divisor.coeff 0 ∣ (16 : ℤ) := by
    simpa [V15ModularFactorizationCertificate.sourceConstant,
      v15VoightSpecialEightRow] using
      V15ModularFactorizationCertificate.constantCoeff_dvd_sourceConstant_of_dvd
        hdivides
  have habs : Int.natAbs (divisor.coeff 0) ≤ 16 :=
    Int.natAbs_le_of_dvd_ne_zero hdvd (by norm_num)
  have hsquare : divisor.coeff 0 * divisor.coeff 0 ≤ 16 * 16 := by
    rw [← Int.natAbs_le_iff_mul_self_le]
    simpa using habs
  have hlower : -(16 : ℤ) ≤ divisor.coeff 0 := by nlinarith
  have hupper : divisor.coeff 0 ≤ (16 : ℤ) := by nlinarith
  have hthree' : divisor.coeff 0 % 3 = 1 :=
    (ZMod.intCast_eq_intCast_iff' _ _ _).mp hthree
  have hfive' : divisor.coeff 0 % 5 = 4 :=
    (ZMod.intCast_eq_intCast_iff' _ _ _).mp hfive
  interval_cases hvalue : divisor.coeff 0
  all_goals norm_num at hdvd
  all_goals norm_num at hthree'
  all_goals norm_num at hfive'
  all_goals rfl

/-- The constant, cubic, and linear coefficients of the complementary
quartic factor are forced by the source polynomial. -/
private theorem v15_voightSpecialEight_complementary_coefficients
    {divisor quotient : ℤ[X]}
    (hdivisorDegree : divisor.IsMonicOfDegree 4)
    (hquotientDegree : quotient.IsMonicOfDegree 4)
    (hquotient : v15VoightSpecialEightRow.polynomial =
      divisor * quotient)
    (hconstant : divisor.coeff 0 = 4) :
    quotient.coeff 0 = 4 ∧
      quotient.coeff 3 = -divisor.coeff 3 ∧
      quotient.coeff 1 = -divisor.coeff 1 := by
  have hdivisorAbove : ∀ n, 4 < n → divisor.coeff n = 0 := by
    intro n hn
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (hdivisorDegree.natDegree_eq.symm ▸ hn)
  have hquotientAbove : ∀ n, 4 < n → quotient.coeff n = 0 := by
    intro n hn
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (hquotientDegree.natDegree_eq.symm ▸ hn)
  have hdivisorLead : divisor.coeff 4 = 1 := by
    simpa [hdivisorDegree.natDegree_eq] using
      hdivisorDegree.monic.coeff_natDegree
  have hquotientLead : quotient.coeff 4 = 1 := by
    simpa [hquotientDegree.natDegree_eq] using
      hquotientDegree.monic.coeff_natDegree
  have hcoeff0 := congrArg (fun polynomial : ℤ[X] =>
    polynomial.coeff 0) hquotient
  have hcoeff1 := congrArg (fun polynomial : ℤ[X] =>
    polynomial.coeff 1) hquotient
  have hcoeff7 := congrArg (fun polynomial : ℤ[X] =>
    polynomial.coeff 7) hquotient
  rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hcoeff0 hcoeff1 hcoeff7
  norm_num [v15VoightSpecialEightRow, Finset.sum_range_succ,
    hconstant, hdivisorAbove, hquotientAbove, hdivisorLead,
    hquotientLead] at hcoeff0 hcoeff1 hcoeff7
  have hquotientConstant : quotient.coeff 0 = 4 := by nlinarith
  rw [hquotientConstant] at hcoeff1
  exact ⟨hquotientConstant, by nlinarith, by nlinarith⟩

private theorem v15_no_integer_square_twenty (value : ℤ)
    (hsquare : value * value = 20) : False := by
  have hlower : -(5 : ℤ) ≤ value := by
    nlinarith [sq_nonneg (value + 5)]
  have hupper : value ≤ (5 : ℤ) := by
    nlinarith [sq_nonneg (value - 5)]
  interval_cases hvalue : value
  all_goals norm_num at hsquare

private theorem v15_no_integer_root_quartic_forty_four (value : ℤ)
    (hequation : value ^ 4 - 44 * value ^ 2 + 20 = 0) : False := by
  have hsquareNonnegative : 0 ≤ value * value := mul_self_nonneg value
  have hsquareBound : value * value ≤ 44 := by
    by_contra hbound
    have hgreater : 44 < value * value := lt_of_not_ge hbound
    have hpositive :
        0 < (value * value) * (value * value - 44) :=
      mul_pos (by nlinarith) (by nlinarith)
    nlinarith [hpositive]
  have hlower : -(7 : ℤ) ≤ value := by
    nlinarith [sq_nonneg (value + 7)]
  have hupper : value ≤ (7 : ℤ) := by
    nlinarith [sq_nonneg (value - 7)]
  interval_cases hvalue : value
  all_goals norm_num at hequation

private theorem v15_no_integer_root_quartic_twelve (value : ℤ)
    (hequation : value ^ 4 - 12 * value ^ 2 + 20 = 0) : False := by
  have hsquareNonnegative : 0 ≤ value * value := mul_self_nonneg value
  have hsquareBound : value * value ≤ 12 := by
    by_contra hbound
    have hgreater : 12 < value * value := lt_of_not_ge hbound
    have hpositive :
        0 < (value * value) * (value * value - 12) :=
      mul_pos (by nlinarith) (by nlinarith)
    nlinarith [hpositive]
  have hlower : -(4 : ℤ) ≤ value := by
    nlinarith [sq_nonneg (value + 4)]
  have hupper : value ≤ (4 : ℤ) := by
    nlinarith [sq_nonneg (value - 4)]
  interval_cases hvalue : value
  all_goals norm_num at hequation

set_option maxHeartbeats 1000000 in
-- Normalizing four polynomial coefficients and solving the resulting
-- nonlinear integer equations needs more than the default elaboration limit.
/-- The exceptional polynomial has no monic quartic integral divisor. -/
theorem v15_voightSpecialEight_no_quartic_divisor
    {divisor : ℤ[X]} (hdivisorMonic : divisor.Monic)
    (hdivisorDegree : divisor.natDegree = 4) :
    ¬divisor ∣ v15VoightSpecialEightRow.polynomial := by
  intro hdivides
  have hconstant := v15_voightSpecialEight_quartic_constantCoeff
    hdivisorMonic hdivisorDegree hdivides
  obtain ⟨quotient, hquotient⟩ := hdivides
  have hdivisorIsMonic : divisor.IsMonicOfDegree 4 :=
    ⟨hdivisorDegree, hdivisorMonic⟩
  have hsourceIsMonic :
      v15VoightSpecialEightRow.polynomial.IsMonicOfDegree 8 :=
    v15VoightPolynomial_isMonicOfDegree 8
      v15VoightSpecialEightRow (by norm_num [v15VoightSpecialEightRow])
      (by norm_num [v15VoightSpecialEightRow])
  have hproductIsMonic :
      (divisor * quotient).IsMonicOfDegree (4 + 4) := by
    rw [← hquotient]
    simpa using hsourceIsMonic
  have hquotientIsMonic : quotient.IsMonicOfDegree 4 :=
    hdivisorIsMonic.of_mul_left hproductIsMonic
  obtain ⟨hquotientConstant, hquotientCubic, hquotientLinear⟩ :=
    v15_voightSpecialEight_complementary_coefficients
      hdivisorIsMonic hquotientIsMonic hquotient hconstant
  have hdivisorAbove : ∀ n, 4 < n → divisor.coeff n = 0 := by
    intro n hn
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (hdivisorDegree.symm ▸ hn)
  have hquotientAbove : ∀ n, 4 < n → quotient.coeff n = 0 := by
    intro n hn
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (hquotientIsMonic.natDegree_eq.symm ▸ hn)
  have hdivisorLead : divisor.coeff 4 = 1 := by
    simpa [hdivisorDegree] using hdivisorMonic.coeff_natDegree
  have hquotientLead : quotient.coeff 4 = 1 := by
    simpa [hquotientIsMonic.natDegree_eq] using
      hquotientIsMonic.monic.coeff_natDegree
  have hcoeff2 := congrArg (fun polynomial : ℤ[X] =>
    polynomial.coeff 2) hquotient
  have hcoeff4 := congrArg (fun polynomial : ℤ[X] =>
    polynomial.coeff 4) hquotient
  have hcoeff5 := congrArg (fun polynomial : ℤ[X] =>
    polynomial.coeff 5) hquotient
  have hcoeff6 := congrArg (fun polynomial : ℤ[X] =>
    polynomial.coeff 6) hquotient
  rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hcoeff2 hcoeff4 hcoeff5 hcoeff6
  norm_num [v15VoightSpecialEightRow, Finset.sum_range_succ,
    hconstant, hquotientConstant, hquotientCubic,
    hquotientLinear, hdivisorAbove, hquotientAbove,
    hdivisorLead, hquotientLead] at hcoeff2 hcoeff4 hcoeff5 hcoeff6
  let a : ℤ := divisor.coeff 3
  let b : ℤ := divisor.coeff 2
  let c : ℤ := divisor.coeff 1
  let d : ℤ := quotient.coeff 2
  have heq2 : -56 = 4 * d - c ^ 2 + 4 * b := by
    dsimp [b, c, d]
    nlinarith [hcoeff2]
  have heq4 : 52 = 8 - 2 * a * c + b * d := by
    dsimp [a, b, c, d]
    nlinarith [hcoeff4]
  have heq5 : 0 = a * d - b * a := by
    dsimp [a, b, d]
    nlinarith [hcoeff5]
  have heq6 : -14 = d - a ^ 2 + b := by
    dsimp [a, b, d]
    nlinarith [hcoeff6]
  have hacSquare : c ^ 2 = (2 * a) ^ 2 := by
    nlinarith [heq2, heq6]
  have hfactor : a * (d - b) = 0 := by
    nlinarith [heq5]
  rcases mul_eq_zero.mp hfactor with ha | hdb
  · have hsum : b + d = -14 := by nlinarith [heq6]
    have hproduct : b * d = 44 := by nlinarith [heq4]
    apply v15_no_integer_square_twenty (b - d)
    nlinarith [hsum, hproduct]
  · have hdeq : d = b := by nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hacSquare with hc | hc
    · apply v15_no_integer_root_quartic_forty_four a
      nlinarith [heq4, heq6]
    · apply v15_no_integer_root_quartic_twelve a
      nlinarith [heq4, heq6]

/-- The exceptional degree-eight Voight polynomial is irreducible over the
integers. -/
theorem v15_voightSpecialEight_irreducible :
    Irreducible v15VoightSpecialEightRow.polynomial := by
  have hrowDegree := v15VoightPolynomial_isMonicOfDegree 8
    v15VoightSpecialEightRow (by norm_num [v15VoightSpecialEightRow])
    (by norm_num [v15VoightSpecialEightRow])
  have hrowNotOne : v15VoightSpecialEightRow.polynomial ≠ 1 := by
    intro hrowOne
    have hdegreeZero : 8 = 0 := by
      rw [← hrowDegree.natDegree_eq, hrowOne,
        Polynomial.natDegree_one]
    omega
  rw [hrowDegree.monic.irreducible_iff_lt_natDegree_lt hrowNotOne]
  intro divisor hdivisorMonic hdivisorDegree
  have hdegreeInterval := Finset.mem_Ioc.mp hdivisorDegree
  have hdegreeCases :
      divisor.natDegree = 1 ∨ divisor.natDegree = 2 ∨
        divisor.natDegree = 3 ∨ divisor.natDegree = 4 := by
    rw [hrowDegree.natDegree_eq] at hdegreeInterval
    omega
  rcases hdegreeCases with hdegree | hdegree | hdegree | hdegree
  · exact V15ModularFactorizationCertificate.not_dvd_of_valid_and_excludesDegree
        v15_voightSpecialEightFactorizationThree_valid
        v15_voightSpecialEight_excludes_degree_1
        hdivisorMonic hdegree
  · exact V15ModularFactorizationCertificate.not_dvd_of_valid_and_excludesDegree
        v15_voightSpecialEightFactorizationThree_valid
        v15_voightSpecialEight_excludes_degree_2
        hdivisorMonic hdegree
  · exact V15ModularFactorizationCertificate.not_dvd_of_valid_and_excludesDegree
        v15_voightSpecialEightFactorizationThree_valid
        v15_voightSpecialEight_excludes_degree_3
        hdivisorMonic hdegree
  · exact v15_voightSpecialEight_no_quartic_divisor
      hdivisorMonic hdegree

end TraceEuclidean
