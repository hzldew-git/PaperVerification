import TraceEuclidean.V15DensePolynomialCertificate
import TraceEuclidean.V15DeterminantCertificate

/-!
# Finite-field irreducibility certificates

This module proves the finite-field criterion used to certify the archived
Voight defining polynomials.  The executable certificate records Frobenius
remainders, exact quotient identities, and Bezout identities.  Its checker
uses only the computable dense-polynomial language.
-/

namespace TraceEuclidean

open Polynomial

/-- The converse finite-field divisibility fact needed by Rabin's criterion. -/
theorem irreducible_dvd_X_pow_card_pow_sub_X_of_natDegree_dvd
    {K : Type*} [Field K] [Finite K] {f : K[X]} {n : ℕ}
    (hf : Irreducible f) (hdegree : f.natDegree ∣ n) :
    f ∣ X ^ (Nat.card K) ^ n - X := by
  letI : Fact (Irreducible f) := ⟨hf⟩
  letI : Module.Finite K (AdjoinRoot f) :=
    (AdjoinRoot.powerBasis hf.ne_zero).finite
  letI : Finite (AdjoinRoot f) := Module.finite_of_finite K
  letI := Fintype.ofFinite K
  letI := Fintype.ofFinite (AdjoinRoot f)
  obtain ⟨k, rfl⟩ := hdegree
  have hcard :
      Fintype.card (AdjoinRoot f) =
        Fintype.card K ^ f.natDegree := by
    rw [Module.card_eq_pow_finrank (K := K),
      (AdjoinRoot.powerBasis hf.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim]
  rw [← AdjoinRoot.mk_eq_zero]
  simp only [map_sub, map_pow, AdjoinRoot.mk_X]
  rw [Nat.card_eq_fintype_card]
  change (AdjoinRoot.root f) ^ (Fintype.card K) ^ (f.natDegree * k) -
      AdjoinRoot.root f = 0
  rw [pow_mul, ← hcard, FiniteField.pow_card_pow, sub_self]

/-- Rabin's finite-field criterion, phrased using all proper divisors of the
degree.  For degrees at most ten this gives at most three coprimality checks. -/
theorem irreducible_of_frobenius_coprime
    {K : Type*} [Field K] [Finite K] {f : K[X]} {n : ℕ}
    (hmonic : f.Monic) (hdegree : f.natDegree = n) (hn : 0 < n)
    (hfull : f ∣ X ^ (Nat.card K) ^ n - X)
    (hproper : ∀ d, 0 < d → d < n → d ∣ n →
      IsCoprime f (X ^ (Nat.card K) ^ d - X)) :
    Irreducible f := by
  have hf0 : f ≠ 0 := hmonic.ne_zero
  obtain ⟨g, hgirreducible, hgf⟩ :=
    Polynomial.exists_irreducible_of_natDegree_pos
      (f := f) (hdegree.symm ▸ hn)
  have hgfull : g ∣ X ^ (Nat.card K) ^ n - X := hgf.trans hfull
  have hgdegree_dvd : g.natDegree ∣ n :=
    hgirreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hgfull
  have hgdegree_pos : 0 < g.natDegree := hgirreducible.natDegree_pos
  have hgdegree_le : g.natDegree ≤ n := by
    rw [← hdegree]
    exact Polynomial.natDegree_le_of_dvd hgf hf0
  have hgdegree_eq : g.natDegree = n := by
    apply hgdegree_le.antisymm
    by_contra hnot
    have hgdegree_lt : g.natDegree < n := lt_of_not_ge hnot
    have hcoprime := hproper g.natDegree hgdegree_pos hgdegree_lt hgdegree_dvd
    have hgsmall : g ∣ X ^ (Nat.card K) ^ g.natDegree - X :=
      irreducible_dvd_X_pow_card_pow_sub_X_of_natDegree_dvd
        hgirreducible (dvd_refl g.natDegree)
    exact hgirreducible.not_isUnit
      (hcoprime.isUnit_of_dvd' hgf hgsmall)
  have hassociated : Associated g f :=
    Polynomial.associated_of_dvd_of_natDegree_le hgf hf0 (by
      rw [hgdegree_eq, ← hdegree])
  exact hassociated.irreducible hgirreducible

/-- Data replayed for one integer polynomial.  All coefficient lists use
ascending order and residues in the range `0, ..., prime - 1`. -/
structure V15RabinIrreducibilityCertificate where
  prime : ℕ
  states : List (List ℕ)
  quotients : List (List ℕ)
  bezoutLeft : List (List ℕ)
  bezoutRight : List (List ℕ)
deriving DecidableEq, Repr

/-- Convert nonnegative representatives to coefficients in `ZMod p`. -/
def v15ResidueCoefficients (p : ℕ) (values : List ℕ) : List (ZMod p) :=
  List.map (fun (value : ℕ) => (value : ZMod p)) values

/-- Reduce the archived integer coefficients modulo `p`. -/
def v15IntegerResidueCoefficients (p : ℕ) (values : List ℤ) :
    List (ZMod p) :=
  List.map (fun (value : ℤ) => (value : ZMod p)) values

/-- The dense representative of `X`. -/
def v15DenseX (p : ℕ) : List (ZMod p) := [0, 1]

/-- Check one exact Frobenius division identity. -/
def v15FrobeniusStepValid (p : ℕ)
    (modulus current quotient next : List (ZMod p)) : Bool :=
  V15DensePolynomial.equal
    (V15DensePolynomial.pow current p)
    (V15DensePolynomial.add
      (V15DensePolynomial.mul modulus quotient) next)

/-- Check one exact Bezout identity. -/
def v15BezoutStepValid (p : ℕ)
    (modulus state left right : List (ZMod p)) : Bool :=
  V15DensePolynomial.equal
    (V15DensePolynomial.add
      (V15DensePolynomial.mul left modulus)
      (V15DensePolynomial.mul right
        (V15DensePolynomial.sub state (v15DenseX p))))
    [1]

/-- Dense interpretation of the archived row is its mapped mathlib
polynomial. -/
theorem v15IntegerResidueCoefficients_toPolynomial
    (p : ℕ) (row : V15VoightPolynomialRow) :
    V15DensePolynomial.toPolynomial
        (v15IntegerResidueCoefficients p row.coefficients) =
      row.polynomial.map (Int.castRingHom (ZMod p)) := by
  ext exponent
  rw [V15DensePolynomial.coeff_toPolynomial,
    Polynomial.coeff_map, v15VoightPolynomial_coeff]
  change
    (List.map (fun (value : ℤ) => (value : ZMod p))
      row.coefficients).getD exponent 0 =
      (row.coefficients.getD exponent 0 : ZMod p)
  simpa only [Int.cast_zero] using
    (List.getD_map row.coefficients (0 : ℤ)
      (n := exponent) (fun (value : ℤ) => (value : ZMod p)))

/-- A successful dense Frobenius step has the asserted polynomial meaning. -/
theorem v15FrobeniusStepValid_spec (p : ℕ)
    {modulus current quotient next : List (ZMod p)}
    (h : v15FrobeniusStepValid p modulus current quotient next = true) :
    V15DensePolynomial.toPolynomial current ^ p =
      V15DensePolynomial.toPolynomial modulus *
          V15DensePolynomial.toPolynomial quotient +
        V15DensePolynomial.toPolynomial next := by
  have heq := V15DensePolynomial.toPolynomial_eq_of_equal h
  simpa [v15FrobeniusStepValid] using heq

/-- A successful dense Bezout step proves polynomial coprimality. -/
theorem v15BezoutStepValid_spec (p : ℕ)
    {modulus state left right : List (ZMod p)}
    (h : v15BezoutStepValid p modulus state left right = true) :
    IsCoprime
      (V15DensePolynomial.toPolynomial modulus)
      (V15DensePolynomial.toPolynomial state - X) := by
  refine ⟨V15DensePolynomial.toPolynomial left,
    V15DensePolynomial.toPolynomial right, ?_⟩
  have heq := V15DensePolynomial.toPolynomial_eq_of_equal h
  simpa [v15BezoutStepValid, v15DenseX] using heq

namespace V15RabinIrreducibilityCertificate

/-- The archived modulus reduced modulo the certificate prime. -/
def modulus (certificate : V15RabinIrreducibilityCertificate)
    (row : V15VoightPolynomialRow) : List (ZMod certificate.prime) :=
  v15IntegerResidueCoefficients certificate.prime row.coefficients

/-- A recorded Frobenius state. -/
def state (certificate : V15RabinIrreducibilityCertificate) (index : ℕ) :
    List (ZMod certificate.prime) :=
  v15ResidueCoefficients certificate.prime
    (certificate.states.getD index [])

/-- A recorded quotient for one Frobenius step. -/
def quotient (certificate : V15RabinIrreducibilityCertificate) (index : ℕ) :
    List (ZMod certificate.prime) :=
  v15ResidueCoefficients certificate.prime
    (certificate.quotients.getD index [])

/-- The left Bezout coefficient associated with a possible factor degree. -/
def left (certificate : V15RabinIrreducibilityCertificate) (index : ℕ) :
    List (ZMod certificate.prime) :=
  v15ResidueCoefficients certificate.prime
    (certificate.bezoutLeft.getD index [])

/-- The right Bezout coefficient associated with a possible factor degree. -/
def right (certificate : V15RabinIrreducibilityCertificate) (index : ℕ) :
    List (ZMod certificate.prime) :=
  v15ResidueCoefficients certificate.prime
    (certificate.bezoutRight.getD index [])

/-- Mathematical statement checked by one executable certificate. -/
abbrev Valid (degree : ℕ) (row : V15VoightPolynomialRow)
    (certificate : V15RabinIrreducibilityCertificate) : Prop :=
  certificate.prime.Prime ∧
    0 < degree ∧
    row.coefficients.length = degree + 1 ∧
    row.coefficients.getLast? = some 1 ∧
    certificate.states.length = degree + 1 ∧
    certificate.quotients.length = degree ∧
    certificate.bezoutLeft.length = degree ∧
    certificate.bezoutRight.length = degree ∧
    V15DensePolynomial.equal (certificate.state 0)
      (v15DenseX certificate.prime) = true ∧
    V15DensePolynomial.equal (certificate.state degree)
      (v15DenseX certificate.prime) = true ∧
    (∀ index : Fin degree,
      v15FrobeniusStepValid certificate.prime
        (certificate.modulus row)
        (certificate.state index.val)
        (certificate.quotient index.val)
        (certificate.state (index.val + 1)) = true) ∧
    (∀ factorDegree : Fin degree,
      0 < factorDegree.val → factorDegree.val ∣ degree →
        v15BezoutStepValid certificate.prime
          (certificate.modulus row)
          (certificate.state factorDegree.val)
          (certificate.left factorDegree.val)
          (certificate.right factorDegree.val) = true)

/-- Executable wrapper for `Valid`. -/
def check (degree : ℕ) (row : V15VoightPolynomialRow)
    (certificate : V15RabinIrreducibilityCertificate) : Bool :=
  decide (certificate.Valid degree row)

theorem valid_of_check_eq_true {degree : ℕ}
    {row : V15VoightPolynomialRow}
    {certificate : V15RabinIrreducibilityCertificate}
    (h : certificate.check degree row = true) :
    certificate.Valid degree row := by
  exact of_decide_eq_true h

/-- Every accepted Rabin certificate proves irreducibility after reduction at
the recorded prime.  This form is also used for irreducible factors in later
finite-field factorization certificates. -/
theorem reduced_irreducible_of_valid {degree : ℕ}
    {row : V15VoightPolynomialRow}
    {certificate : V15RabinIrreducibilityCertificate}
    (hvalid : certificate.Valid degree row) :
    Irreducible
      (row.polynomial.map (Int.castRingHom (ZMod certificate.prime))) := by
  rcases hvalid with
    ⟨hprime, hdegreePositive, hcoefficientLength, hlast,
      hstateLength, hquotientLength, hleftLength, hrightLength,
      hstateZero, hstateFinal, hsteps, hbezout⟩
  letI : Fact certificate.prime.Prime := ⟨hprime⟩
  let reducedPolynomial :=
    row.polynomial.map (Int.castRingHom (ZMod certificate.prime))
  have hrowDegree := v15VoightPolynomial_isMonicOfDegree
    degree row hcoefficientLength hlast
  have hrowMonic : row.polynomial.Monic := hrowDegree.monic
  have hreducedMonic : reducedPolynomial.Monic :=
    hrowMonic.map (Int.castRingHom (ZMod certificate.prime))
  have hreducedDegree : reducedPolynomial.natDegree = degree := by
    simpa [reducedPolynomial, hrowDegree.natDegree_eq] using
      hrowMonic.natDegree_map (Int.castRingHom (ZMod certificate.prime))
  have hmodulus :
      V15DensePolynomial.toPolynomial (certificate.modulus row) =
        reducedPolynomial := by
    exact v15IntegerResidueCoefficients_toPolynomial certificate.prime row
  have hstateZeroPolynomial :
      V15DensePolynomial.toPolynomial (certificate.state 0) =
        (X : (ZMod certificate.prime)[X]) := by
    have heq := V15DensePolynomial.toPolynomial_eq_of_equal hstateZero
    simpa [v15DenseX] using heq
  have hstateFinalPolynomial :
      V15DensePolynomial.toPolynomial (certificate.state degree) =
        (X : (ZMod certificate.prime)[X]) := by
    have heq := V15DensePolynomial.toPolynomial_eq_of_equal hstateFinal
    simpa [v15DenseX] using heq
  have hstateDivisibility : ∀ index, index ≤ degree →
      reducedPolynomial ∣
        V15DensePolynomial.toPolynomial (certificate.state index) -
          X ^ certificate.prime ^ index := by
    intro index
    induction index with
    | zero =>
        intro _
        rw [hstateZeroPolynomial]
        simp
    | succ index induction =>
        intro hindex
        have hindexLess : index < degree := Nat.lt_of_succ_le hindex
        have hstepValid := hsteps ⟨index, hindexLess⟩
        have hstep :=
          v15FrobeniusStepValid_spec certificate.prime hstepValid
        rw [hmodulus] at hstep
        have hstepDivisibility :
            reducedPolynomial ∣
              V15DensePolynomial.toPolynomial
                  (certificate.state (index + 1)) -
                V15DensePolynomial.toPolynomial
                    (certificate.state index) ^ certificate.prime := by
          refine ⟨-V15DensePolynomial.toPolynomial
            (certificate.quotient index), ?_⟩
          rw [hstep]
          ring
        have hprevious := induction (Nat.le_of_lt hindexLess)
        have hpowerDivisibility :
            reducedPolynomial ∣
              V15DensePolynomial.toPolynomial
                    (certificate.state index) ^ certificate.prime -
                (X ^ certificate.prime ^ index) ^ certificate.prime :=
          hprevious.trans
            (sub_dvd_pow_sub_pow
              (V15DensePolynomial.toPolynomial
                (certificate.state index))
              (X ^ certificate.prime ^ index) certificate.prime)
        convert dvd_add hstepDivisibility hpowerDivisibility using 1 <;>
          simp [pow_succ, pow_mul]
  have hdegreeState := hstateDivisibility degree le_rfl
  rw [hstateFinalPolynomial] at hdegreeState
  have hfullPrime :
      reducedPolynomial ∣
        X ^ certificate.prime ^ degree - X := by
    simpa only [neg_sub] using (dvd_neg.mpr hdegreeState)
  have hproperPrime : ∀ factorDegree,
      0 < factorDegree → factorDegree < degree →
        factorDegree ∣ degree →
          IsCoprime reducedPolynomial
            (X ^ certificate.prime ^ factorDegree - X) := by
    intro factorDegree hfactorPositive hfactorLess hfactorDivides
    have hbezoutValid := hbezout
      ⟨factorDegree, hfactorLess⟩ hfactorPositive hfactorDivides
    have hcoprime :=
      v15BezoutStepValid_spec certificate.prime hbezoutValid
    rw [hmodulus] at hcoprime
    have hcongruence := hstateDivisibility factorDegree hfactorLess.le
    obtain ⟨quotient, hquotient⟩ := hcongruence
    have hrewrite :
        V15DensePolynomial.toPolynomial
              (certificate.state factorDegree) - X =
          (X ^ certificate.prime ^ factorDegree - X) +
            reducedPolynomial * quotient := by
      calc
        V15DensePolynomial.toPolynomial
              (certificate.state factorDegree) - X =
            (V15DensePolynomial.toPolynomial
                (certificate.state factorDegree) -
              X ^ certificate.prime ^ factorDegree) +
              (X ^ certificate.prime ^ factorDegree - X) := by ring
        _ = reducedPolynomial * quotient +
              (X ^ certificate.prime ^ factorDegree - X) := by
            rw [hquotient]
        _ = (X ^ certificate.prime ^ factorDegree - X) +
              reducedPolynomial * quotient := by ring
    rw [hrewrite, IsCoprime.add_mul_left_right_iff] at hcoprime
    exact hcoprime
  have hreducedIrreducible : Irreducible reducedPolynomial :=
    irreducible_of_frobenius_coprime hreducedMonic hreducedDegree
      hdegreePositive
      (by simpa [ZMod.card] using hfullPrime)
      (by
        intro factorDegree hfactorPositive hfactorLess hfactorDivides
        simpa [ZMod.card] using
          hproperPrime factorDegree hfactorPositive hfactorLess hfactorDivides)
  exact hreducedIrreducible

/-- Every accepted Rabin certificate proves irreducibility of the archived
integer polynomial. -/
theorem irreducible_of_valid {degree : ℕ}
    {row : V15VoightPolynomialRow}
    {certificate : V15RabinIrreducibilityCertificate}
    (hvalid : certificate.Valid degree row) :
    Irreducible row.polynomial := by
  letI : Fact certificate.prime.Prime := ⟨hvalid.1⟩
  have hrowDegree := v15VoightPolynomial_isMonicOfDegree degree row
    hvalid.2.2.1 hvalid.2.2.2.1
  exact Polynomial.Monic.irreducible_of_irreducible_map
    (Int.castRingHom (ZMod certificate.prime)) row.polynomial
    hrowDegree.monic (reduced_irreducible_of_valid hvalid)

/-- Executable certificates expose the same irreducibility conclusion. -/
theorem irreducible_of_check_eq_true {degree : ℕ}
    {row : V15VoightPolynomialRow}
    {certificate : V15RabinIrreducibilityCertificate}
    (h : certificate.check degree row = true) :
    Irreducible row.polynomial :=
  irreducible_of_valid (valid_of_check_eq_true h)

end V15RabinIrreducibilityCertificate

/-- Check a list of certificates against a list of archived rows. -/
def v15RabinCertificateBatchCheck (degree : ℕ)
    (rows : List V15VoightPolynomialRow)
    (certificates : List V15RabinIrreducibilityCertificate) : Bool :=
  decide (rows.length = certificates.length) &&
    (rows.zip certificates).all fun rowAndCertificate =>
      rowAndCertificate.2.check degree rowAndCertificate.1

/-- A successful batch check supplies an irreducibility theorem for every
row in the batch. -/
theorem v15_irreducible_of_batchCheck_eq_true (degree : ℕ) :
    ∀ {rows : List V15VoightPolynomialRow}
      {certificates : List V15RabinIrreducibilityCertificate},
      v15RabinCertificateBatchCheck degree rows certificates = true →
        ∀ row ∈ rows, Irreducible row.polynomial := by
  intro rows
  induction rows with
  | nil =>
      intro certificates h row hrow
      simp at hrow
  | cons first rows induction =>
      intro certificates h row hrow
      cases certificates with
      | nil =>
          simp [v15RabinCertificateBatchCheck] at h
      | cons certificate certificates =>
          have hparts := Bool.and_eq_true_iff.mp h
          have hlength : rows.length = certificates.length := by
            simpa using of_decide_eq_true hparts.1
          have hallParts :
              certificate.check degree first = true ∧
              ((rows.zip certificates).all fun rowAndCertificate =>
                rowAndCertificate.2.check degree rowAndCertificate.1) = true := by
            simpa [List.all_cons, Bool.and_eq_true_iff] using hparts.2
          have htail :
              v15RabinCertificateBatchCheck degree rows certificates = true := by
            exact Bool.and_eq_true_iff.mpr
              ⟨decide_eq_true hlength, hallParts.2⟩
          rcases List.mem_cons.mp hrow with rfl | hrow
          · exact V15RabinIrreducibilityCertificate.irreducible_of_check_eq_true
              (degree := degree) hallParts.1
          · exact induction htail row hrow

/-- Combine two listwise proofs. -/
theorem v15_forall_mem_append {R : Type*} {property : R → Prop}
    {left right : List R}
    (hleft : ∀ value ∈ left, property value)
    (hright : ∀ value ∈ right, property value) :
    ∀ value ∈ left ++ right, property value := by
  intro value hvalue
  rcases List.mem_append.mp hvalue with hvalue | hvalue
  · exact hleft value hvalue
  · exact hright value hvalue

end TraceEuclidean
