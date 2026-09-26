import TraceEuclidean.V15FiniteFieldIrreducibilityCertificate
import Mathlib.NumberTheory.Divisors

/-!
# Modular factorization certificates

This module handles the defining polynomials that have no irreducible
reduction at a single small prime.  A certificate gives a complete product of
irreducible factors modulo a prime.  The degrees and constant coefficients of
all subproducts then exclude an integral monic divisor of a prescribed degree.
-/

namespace TraceEuclidean

open Polynomial UniqueFactorizationMonoid

/-- One complete finite-field factorization.  The first component of each
entry is an integer lift of a monic factor; the second is its Rabin
irreducibility certificate. -/
structure V15ModularFactorizationCertificate where
  prime : ℕ
  factors : List
    (V15VoightPolynomialRow × V15RabinIrreducibilityCertificate)
deriving DecidableEq, Repr

namespace V15ModularFactorizationCertificate

/-- The dense modular coefficient list attached to one lifted factor. -/
def factorCoefficients (certificate : V15ModularFactorizationCertificate)
    (factor : V15VoightPolynomialRow) : List (ZMod certificate.prime) :=
  v15IntegerResidueCoefficients certificate.prime factor.coefficients

/-- The finite-field polynomial attached to one lifted factor. -/
noncomputable def factorPolynomial
    (certificate : V15ModularFactorizationCertificate)
    (factor : V15VoightPolynomialRow) : (ZMod certificate.prime)[X] :=
  factor.polynomial.map (Int.castRingHom (ZMod certificate.prime))

/-- All factor polynomials, with multiplicity. -/
noncomputable def factorPolynomials
    (certificate : V15ModularFactorizationCertificate) :
    List (ZMod certificate.prime)[X] :=
  certificate.factors.map fun entry =>
    certificate.factorPolynomial entry.1

/-- The degree and constant coefficient used by the finite subset check. -/
def factorSignature (certificate : V15ModularFactorizationCertificate)
    (factor : V15VoightPolynomialRow) : ℕ × ZMod certificate.prime :=
  (factor.coefficients.length - 1,
    (factor.coefficients.getD 0 0 : ZMod certificate.prime))

/-- Factor signatures, with multiplicity. -/
def factorSignatures (certificate : V15ModularFactorizationCertificate) :
    Multiset (ℕ × ZMod certificate.prime) :=
  certificate.factors.map (fun entry =>
    certificate.factorSignature entry.1)

/-- The archived source polynomial's constant coefficient. -/
def sourceConstant (row : V15VoightPolynomialRow) : ℤ :=
  row.coefficients.getD 0 0

/-- Exact finite check excluding a monic divisor of the indicated degree. -/
def excludesDegree (certificate : V15ModularFactorizationCertificate)
    (row : V15VoightPolynomialRow) (degree : ℕ) : Bool :=
  (certificate.factorSignatures.powerset.map fun subset =>
    if decide ((subset.map Prod.fst).sum = degree) then
      (((sourceConstant row).divisors.1.map fun divisor =>
        decide ((subset.map Prod.snd).prod ≠
          (divisor : ZMod certificate.prime))).prod)
    else true).prod

/-- Exact finite check that every subproduct of the indicated degree has the
specified constant coefficient.  This is useful when modular factorization
does not by itself exclude the degree, but does force the constant term of a
hypothetical integral factor into one residue class. -/
def forcesConstantResidue
    (certificate : V15ModularFactorizationCertificate)
    (degree : ℕ) (residue : ZMod certificate.prime) : Bool :=
  (certificate.factorSignatures.powerset.map fun subset =>
    if decide ((subset.map Prod.fst).sum = degree) then
      decide ((subset.map Prod.snd).prod = residue)
    else true).prod

/-- Mathematical statement checked by a complete modular factorization. -/
abbrev Valid (degree : ℕ) (row : V15VoightPolynomialRow)
    (certificate : V15ModularFactorizationCertificate) : Prop :=
  certificate.prime.Prime ∧
    row.coefficients.length = degree + 1 ∧
    row.coefficients.getLast? = some 1 ∧
    sourceConstant row ≠ 0 ∧
    (∀ entry ∈ certificate.factors,
      entry.2.prime = certificate.prime ∧
      entry.2.Valid (entry.1.coefficients.length - 1) entry.1) ∧
    V15DensePolynomial.equal
      (V15DensePolynomial.prod
        (certificate.factors.map fun entry =>
          certificate.factorCoefficients entry.1))
      (v15IntegerResidueCoefficients certificate.prime row.coefficients) = true

/-- Executable wrapper for `Valid`. -/
def check (degree : ℕ) (row : V15VoightPolynomialRow)
    (certificate : V15ModularFactorizationCertificate) : Bool :=
  decide (certificate.Valid degree row)

theorem valid_of_check_eq_true {degree : ℕ}
    {row : V15VoightPolynomialRow}
    {certificate : V15ModularFactorizationCertificate}
    (h : certificate.check degree row = true) :
    certificate.Valid degree row := by
  exact of_decide_eq_true h

/-- A Boolean multiset product is true exactly when every entry is true. -/
theorem bool_mul_eq_and (left right : Bool) :
    left * right = (left && right) := by
  cases left <;> cases right <;> rfl

theorem bool_multiset_prod_eq_true {values : Multiset Bool} :
    values.prod = true ↔ ∀ value ∈ values, value = true := by
  induction values using Multiset.induction with
  | empty =>
      constructor
      · intro _ value hvalue
        simp at hvalue
      · intro _
        exact Bool.one_eq_true
  | cons head tail induction =>
      simp only [Multiset.prod_cons, bool_mul_eq_and,
        Bool.and_eq_true, Multiset.mem_cons, forall_eq_or_imp,
        induction]

/-- Semantic form of the finite subproduct exclusion check. -/
theorem excludesDegree_spec
    {certificate : V15ModularFactorizationCertificate}
    {row : V15VoightPolynomialRow} {degree : ℕ}
    (hexcludes : certificate.excludesDegree row degree = true)
    {subset : Multiset (ℕ × ZMod certificate.prime)}
    (hsubset : subset ≤ certificate.factorSignatures)
    (hdegree : (subset.map Prod.fst).sum = degree)
    {divisor : ℤ} (hdivisor : divisor ∣ sourceConstant row)
    (hconstant : sourceConstant row ≠ 0) :
    (subset.map Prod.snd).prod ≠
      (divisor : ZMod certificate.prime) := by
  have hsubsetMem :
      subset ∈ certificate.factorSignatures.powerset :=
    Multiset.mem_powerset.mpr hsubset
  have houter := (bool_multiset_prod_eq_true.mp hexcludes)
    (if decide ((subset.map Prod.fst).sum = degree) then
      (((sourceConstant row).divisors.1.map fun value =>
        decide ((subset.map Prod.snd).prod ≠
          (value : ZMod certificate.prime))).prod)
    else true)
    (Multiset.mem_map.mpr ⟨subset, hsubsetMem, rfl⟩)
  simp only [hdegree, decide_true, if_true] at houter
  have hdivisorMem : divisor ∈ (sourceConstant row).divisors :=
    Int.mem_divisors.mpr ⟨hdivisor, hconstant⟩
  have hdivisorMem' :
      divisor ∈ (sourceConstant row).divisors.1 := hdivisorMem
  let castDivisors : Multiset (ZMod certificate.prime) :=
    (sourceConstant row).divisors.1.map fun value : ℤ =>
      (value : ZMod certificate.prime)
  let predicate : ZMod certificate.prime → Bool := fun value =>
    decide ((subset.map Prod.snd).prod ≠ value)
  have hcastMem : (divisor : ZMod certificate.prime) ∈ castDivisors :=
    Multiset.mem_map.mpr ⟨divisor, hdivisorMem', rfl⟩
  have hpredicateMem : predicate (divisor : ZMod certificate.prime) ∈
      castDivisors.map predicate :=
    Multiset.mem_map.mpr
      ⟨(divisor : ZMod certificate.prime), hcastMem, rfl⟩
  have hentry := (bool_multiset_prod_eq_true.mp houter)
    (predicate (divisor : ZMod certificate.prime)) (by
      simpa [castDivisors, predicate] using hpredicateMem)
  change decide ((subset.map Prod.snd).prod ≠
    (divisor : ZMod certificate.prime)) = true at hentry
  exact of_decide_eq_true hentry

/-- Semantic form of the finite constant-residue check. -/
theorem forcesConstantResidue_spec
    {certificate : V15ModularFactorizationCertificate}
    {degree : ℕ} {residue : ZMod certificate.prime}
    (hforces : certificate.forcesConstantResidue degree residue = true)
    {subset : Multiset (ℕ × ZMod certificate.prime)}
    (hsubset : subset ≤ certificate.factorSignatures)
    (hdegree : (subset.map Prod.fst).sum = degree) :
    (subset.map Prod.snd).prod = residue := by
  have hsubsetMem :
      subset ∈ certificate.factorSignatures.powerset :=
    Multiset.mem_powerset.mpr hsubset
  have hentry := (bool_multiset_prod_eq_true.mp hforces)
    (if decide ((subset.map Prod.fst).sum = degree) then
      decide ((subset.map Prod.snd).prod = residue)
    else true)
    (Multiset.mem_map.mpr ⟨subset, hsubsetMem, rfl⟩)
  simp only [hdegree, decide_true, if_true] at hentry
  exact of_decide_eq_true hentry

@[simp]
theorem factorCoefficients_toPolynomial
    (certificate : V15ModularFactorizationCertificate)
    (factor : V15VoightPolynomialRow) :
    V15DensePolynomial.toPolynomial
        (certificate.factorCoefficients factor) =
      certificate.factorPolynomial factor := by
  exact v15IntegerResidueCoefficients_toPolynomial
    certificate.prime factor

/-- Every displayed factor in a valid certificate is monic and irreducible
over the certificate field. -/
theorem factor_monic_and_irreducible_of_valid
    {degree : ℕ} {row : V15VoightPolynomialRow}
    {certificate : V15ModularFactorizationCertificate}
    (hvalid : certificate.Valid degree row)
    {entry : V15VoightPolynomialRow ×
      V15RabinIrreducibilityCertificate}
    (hentry : entry ∈ certificate.factors) :
    (certificate.factorPolynomial entry.1).Monic ∧
      Irreducible (certificate.factorPolynomial entry.1) := by
  rcases hvalid with
    ⟨hprime, -, -, -, hfactorValid, -⟩
  have hentryValid := hfactorValid entry hentry
  have hfactorDegree := v15VoightPolynomial_isMonicOfDegree
    (entry.1.coefficients.length - 1) entry.1
    hentryValid.2.2.2.1 hentryValid.2.2.2.2.1
  constructor
  · exact hfactorDegree.monic.map
      (Int.castRingHom (ZMod certificate.prime))
  · have hirreducible :=
      V15RabinIrreducibilityCertificate.reduced_irreducible_of_valid
        hentryValid.2
    rw [hentryValid.1] at hirreducible
    exact hirreducible

/-- The displayed irreducible factors multiply to the reduced source
polynomial. -/
theorem factorPolynomials_prod_eq_source_of_valid
    {degree : ℕ} {row : V15VoightPolynomialRow}
    {certificate : V15ModularFactorizationCertificate}
    (hvalid : certificate.Valid degree row) :
    certificate.factorPolynomials.prod =
      row.polynomial.map
        (Int.castRingHom (ZMod certificate.prime)) := by
  rcases hvalid with ⟨-, -, -, -, -, hproduct⟩
  have heq := V15DensePolynomial.toPolynomial_eq_of_equal hproduct
  rw [V15DensePolynomial.toPolynomial_prod] at heq
  rw [List.map_map] at heq
  change
    (certificate.factors.map fun entry =>
      V15DensePolynomial.toPolynomial
        (certificate.factorCoefficients entry.1)).prod =
      V15DensePolynomial.toPolynomial
        (v15IntegerResidueCoefficients certificate.prime
          row.coefficients) at heq
  have hmap :
      (certificate.factors.map fun entry =>
        V15DensePolynomial.toPolynomial
          (certificate.factorCoefficients entry.1)) =
        certificate.factorPolynomials := by
    apply List.map_congr_left
    intro entry hentry
    exact factorCoefficients_toPolynomial certificate entry.1
  rw [hmap,
    v15IntegerResidueCoefficients_toPolynomial certificate.prime row] at heq
  exact heq

/-- Stored factor signatures agree with the mathematical degrees and constant
coefficients. -/
theorem factorPolynomial_signature_of_valid
    {degree : ℕ} {row : V15VoightPolynomialRow}
    {certificate : V15ModularFactorizationCertificate}
    (hvalid : certificate.Valid degree row)
    {entry : V15VoightPolynomialRow ×
      V15RabinIrreducibilityCertificate}
    (hentry : entry ∈ certificate.factors) :
    ((certificate.factorPolynomial entry.1).natDegree,
      (certificate.factorPolynomial entry.1).coeff 0) =
      certificate.factorSignature entry.1 := by
  have hprime := hvalid.1
  letI : Fact certificate.prime.Prime := ⟨hprime⟩
  have hfactorValid := hvalid.2.2.2.2.1
  have hentryValid := hfactorValid entry hentry
  have hfactorDegree := v15VoightPolynomial_isMonicOfDegree
    (entry.1.coefficients.length - 1) entry.1
    hentryValid.2.2.2.1 hentryValid.2.2.2.2.1
  apply Prod.ext
  · change (entry.1.polynomial.map
      (Int.castRingHom (ZMod certificate.prime))).natDegree =
        entry.1.coefficients.length - 1
    rw [hfactorDegree.monic.natDegree_map,
      hfactorDegree.natDegree_eq]
  · change (entry.1.polynomial.map
      (Int.castRingHom (ZMod certificate.prime))).coeff 0 =
        (entry.1.coefficients.getD 0 0 : ZMod certificate.prime)
    rw [Polynomial.coeff_map, v15VoightPolynomial_coeff]
    rfl

/-- The multiset of mathematical factor signatures is the stored executable
multiset. -/
theorem factorPolynomials_signatures_eq_of_valid
    {degree : ℕ} {row : V15VoightPolynomialRow}
    {certificate : V15ModularFactorizationCertificate}
    (hvalid : certificate.Valid degree row) :
    ((certificate.factorPolynomials.map fun factor =>
      (factor.natDegree, factor.coeff 0) :
        List (ℕ × ZMod certificate.prime)) :
      Multiset (ℕ × ZMod certificate.prime)) =
        certificate.factorSignatures := by
  simp only [factorPolynomials, factorSignatures, List.map_map]
  change
    Multiset.map
      (fun entry : V15VoightPolynomialRow ×
        V15RabinIrreducibilityCertificate =>
        ((certificate.factorPolynomial entry.1).natDegree,
          (certificate.factorPolynomial entry.1).coeff 0))
      (certificate.factors : Multiset _) =
    Multiset.map
      (fun entry : V15VoightPolynomialRow ×
        V15RabinIrreducibilityCertificate =>
        certificate.factorSignature entry.1)
      (certificate.factors : Multiset _)
  apply Multiset.map_congr rfl
  intro entry hentry
  exact factorPolynomial_signature_of_valid hvalid (by simpa using hentry)

/-- Auxiliary normalized-factor form used by the executable exclusion
criterion below. -/
theorem exists_factor_submultiset_of_monic_dvd_aux
    {K : Type*} [Field K] {source divisor : K[X]}
    (factors : Multiset K[X])
    (hirreducible : ∀ factor ∈ factors, Irreducible factor)
    (hmonic : ∀ factor ∈ factors, factor.Monic)
    (hproduct : factors.prod = source)
    (hdivisorMonic : divisor.Monic) (hdivides : divisor ∣ source) :
    ∃ subset ≤ factors, subset.prod = divisor := by
  classical
  have hdivisorZero : divisor ≠ 0 := hdivisorMonic.ne_zero
  have hfactorsZero : factors.prod ≠ 0 :=
    Multiset.prod_ne_zero fun hzero =>
      (hirreducible 0 hzero).ne_zero rfl
  have hsourceZero : source ≠ 0 := hproduct ▸ hfactorsZero
  have hnormalizedFactors : normalizedFactors source = factors := by
    rw [← hproduct, normalizedFactors_prod_eq factors hirreducible]
    calc
      factors.map normalize = factors.map id := by
        apply Multiset.map_congr rfl
        intro factor hfactor
        exact (normalize_eq_self_iff_monic
          (hirreducible factor hfactor).ne_zero).2
            (hmonic factor hfactor)
      _ = factors := Multiset.map_id factors
  refine ⟨normalizedFactors divisor, ?_, ?_⟩
  · rw [← hnormalizedFactors]
    exact (dvd_iff_normalizedFactors_le_normalizedFactors
      hdivisorZero hsourceZero).1 hdivides
  · have hfactorization :=
      Polynomial.leadingCoeff_mul_prod_normalizedFactors divisor
    simpa [hdivisorMonic.leadingCoeff] using hfactorization

/-- A monic integral divisor determines a submultiset of the stored modular
factor signatures.  Both its degree and its constant coefficient are
preserved. -/
theorem exists_signature_submultiset_of_valid_and_dvd
    {sourceDegree factorDegree : ℕ}
    {row : V15VoightPolynomialRow}
    {certificate : V15ModularFactorizationCertificate}
    (hvalid : certificate.Valid sourceDegree row)
    {divisor : ℤ[X]} (hdivisorMonic : divisor.Monic)
    (hdivisorDegree : divisor.natDegree = factorDegree)
    (hdivides : divisor ∣ row.polynomial) :
    ∃ signatureSubset ≤ certificate.factorSignatures,
      (signatureSubset.map Prod.fst).sum = factorDegree ∧
      (signatureSubset.map Prod.snd).prod =
        (divisor.coeff 0 : ZMod certificate.prime) := by
  letI : Fact certificate.prime.Prime := ⟨hvalid.1⟩
  let reducedDivisor :=
    divisor.map (Int.castRingHom (ZMod certificate.prime))
  let reducedSource :=
    row.polynomial.map (Int.castRingHom (ZMod certificate.prime))
  have hreducedDivisorMonic : reducedDivisor.Monic :=
    hdivisorMonic.map (Int.castRingHom (ZMod certificate.prime))
  have hreducedDivides : reducedDivisor ∣ reducedSource := by
    obtain ⟨quotient, hquotient⟩ := hdivides
    refine ⟨quotient.map
      (Int.castRingHom (ZMod certificate.prime)), ?_⟩
    simpa [reducedDivisor, reducedSource, Polynomial.map_mul] using
      congrArg (Polynomial.map
        (Int.castRingHom (ZMod certificate.prime))) hquotient
  have hfactorProduct :=
    factorPolynomials_prod_eq_source_of_valid hvalid
  change certificate.factorPolynomials.prod = reducedSource at hfactorProduct
  obtain ⟨factorSubset, hfactorSubset, hfactorSubsetProduct⟩ :=
    exists_factor_submultiset_of_monic_dvd_aux
      (source := reducedSource) (divisor := reducedDivisor)
      (certificate.factorPolynomials :
        Multiset (ZMod certificate.prime)[X])
      (by
        intro factor hfactor
        have hfactorList : factor ∈ certificate.factorPolynomials := by
          simpa using hfactor
        rcases List.mem_map.mp hfactorList with
          ⟨entry, hentry, rfl⟩
        exact (factor_monic_and_irreducible_of_valid
          hvalid hentry).2)
      (by
        intro factor hfactor
        have hfactorList : factor ∈ certificate.factorPolynomials := by
          simpa using hfactor
        rcases List.mem_map.mp hfactorList with
          ⟨entry, hentry, rfl⟩
        exact (factor_monic_and_irreducible_of_valid
          hvalid hentry).1)
      (by simpa using hfactorProduct)
      hreducedDivisorMonic hreducedDivides
  let signatureSubset : Multiset (ℕ × ZMod certificate.prime) :=
    factorSubset.map fun factor => (factor.natDegree, factor.coeff 0)
  have hsignatureSubset :
      signatureSubset ≤ certificate.factorSignatures := by
    have hmapped := Multiset.map_le_map
      (f := fun factor : (ZMod certificate.prime)[X] =>
        (factor.natDegree, factor.coeff 0)) hfactorSubset
    have hfullSignatures :
        Multiset.map
          (fun factor : (ZMod certificate.prime)[X] =>
            (factor.natDegree, factor.coeff 0))
          (certificate.factorPolynomials :
            Multiset (ZMod certificate.prime)[X]) =
          certificate.factorSignatures := by
      simpa using factorPolynomials_signatures_eq_of_valid hvalid
    rw [hfullSignatures] at hmapped
    exact hmapped
  have hfactorSubsetZero : (0 : (ZMod certificate.prime)[X]) ∉
      factorSubset := by
    intro hzero
    have hzeroFull := Multiset.mem_of_le hfactorSubset hzero
    have hzeroList :
        (0 : (ZMod certificate.prime)[X]) ∈
          certificate.factorPolynomials := by
      simpa using hzeroFull
    rcases List.mem_map.mp hzeroList with ⟨entry, hentry, heq⟩
    have hirreducible :=
      (factor_monic_and_irreducible_of_valid hvalid hentry).2
    exact hirreducible.ne_zero heq
  have hsignatureDegree :
      (signatureSubset.map Prod.fst).sum = factorDegree := by
    dsimp [signatureSubset]
    rw [Multiset.map_map]
    change (factorSubset.map Polynomial.natDegree).sum = factorDegree
    rw [← Polynomial.natDegree_multiset_prod factorSubset
      hfactorSubsetZero, hfactorSubsetProduct]
    change reducedDivisor.natDegree = factorDegree
    rw [hdivisorMonic.natDegree_map, hdivisorDegree]
  have hsignatureConstant :
      (signatureSubset.map Prod.snd).prod =
        (divisor.coeff 0 : ZMod certificate.prime) := by
    dsimp [signatureSubset]
    rw [Multiset.map_map]
    change (factorSubset.map fun factor => factor.coeff 0).prod = _
    rw [← Polynomial.coeff_zero_multiset_prod,
      hfactorSubsetProduct]
    change (divisor.map
      (Int.castRingHom (ZMod certificate.prime))).coeff 0 = _
    rw [Polynomial.coeff_map]
    rfl
  exact ⟨signatureSubset, hsignatureSubset, hsignatureDegree,
    hsignatureConstant⟩

/-- The constant coefficient of an integral divisor divides the source
constant coefficient. -/
theorem constantCoeff_dvd_sourceConstant_of_dvd
    {row : V15VoightPolynomialRow} {divisor : ℤ[X]}
    (hdivides : divisor ∣ row.polynomial) :
    divisor.coeff 0 ∣ sourceConstant row := by
  obtain ⟨quotient, hquotient⟩ := hdivides
  refine ⟨quotient.coeff 0, ?_⟩
  rw [← Polynomial.mul_coeff_zero, ← hquotient]
  exact (v15VoightPolynomial_coeff row 0).symm

/-- A successful residue check fixes the constant coefficient of every monic
integral divisor of the indicated degree modulo the certificate prime. -/
theorem constantCoeff_mod_eq_of_valid_and_forcesConstantResidue
    {sourceDegree factorDegree : ℕ}
    {row : V15VoightPolynomialRow}
    {certificate : V15ModularFactorizationCertificate}
    {residue : ZMod certificate.prime}
    (hvalid : certificate.Valid sourceDegree row)
    (hforces :
      certificate.forcesConstantResidue factorDegree residue = true)
    {divisor : ℤ[X]} (hdivisorMonic : divisor.Monic)
    (hdivisorDegree : divisor.natDegree = factorDegree)
    (hdivides : divisor ∣ row.polynomial) :
    (divisor.coeff 0 : ZMod certificate.prime) = residue := by
  obtain ⟨signatureSubset, hsignatureSubset, hsignatureDegree,
      hsignatureConstant⟩ :=
    exists_signature_submultiset_of_valid_and_dvd hvalid
      hdivisorMonic hdivisorDegree hdivides
  rw [← hsignatureConstant]
  exact forcesConstantResidue_spec hforces hsignatureSubset
    hsignatureDegree

/-- A successful degree exclusion rules out an integral monic divisor of that
degree. -/
theorem not_dvd_of_valid_and_excludesDegree
    {sourceDegree factorDegree : ℕ}
    {row : V15VoightPolynomialRow}
    {certificate : V15ModularFactorizationCertificate}
    (hvalid : certificate.Valid sourceDegree row)
    (hexcludes : certificate.excludesDegree row factorDegree = true)
    {divisor : ℤ[X]} (hdivisorMonic : divisor.Monic)
    (hdivisorDegree : divisor.natDegree = factorDegree) :
    ¬divisor ∣ row.polynomial := by
  intro hdivides
  letI : Fact certificate.prime.Prime := ⟨hvalid.1⟩
  let reducedDivisor :=
    divisor.map (Int.castRingHom (ZMod certificate.prime))
  let reducedSource :=
    row.polynomial.map (Int.castRingHom (ZMod certificate.prime))
  have hreducedDivisorMonic : reducedDivisor.Monic :=
    hdivisorMonic.map (Int.castRingHom (ZMod certificate.prime))
  have hreducedDivides : reducedDivisor ∣ reducedSource := by
    obtain ⟨quotient, hquotient⟩ := hdivides
    refine ⟨quotient.map
      (Int.castRingHom (ZMod certificate.prime)), ?_⟩
    simpa [reducedDivisor, reducedSource, Polynomial.map_mul] using
      congrArg (Polynomial.map
        (Int.castRingHom (ZMod certificate.prime))) hquotient
  have hfactorProduct :=
    factorPolynomials_prod_eq_source_of_valid hvalid
  change certificate.factorPolynomials.prod = reducedSource at hfactorProduct
  obtain ⟨factorSubset, hfactorSubset, hfactorSubsetProduct⟩ :=
    exists_factor_submultiset_of_monic_dvd_aux
      (source := reducedSource) (divisor := reducedDivisor)
      (certificate.factorPolynomials :
        Multiset (ZMod certificate.prime)[X])
      (by
        intro factor hfactor
        have hfactorList : factor ∈ certificate.factorPolynomials := by
          simpa using hfactor
        rcases List.mem_map.mp hfactorList with
          ⟨entry, hentry, rfl⟩
        exact (factor_monic_and_irreducible_of_valid
          hvalid hentry).2)
      (by
        intro factor hfactor
        have hfactorList : factor ∈ certificate.factorPolynomials := by
          simpa using hfactor
        rcases List.mem_map.mp hfactorList with
          ⟨entry, hentry, rfl⟩
        exact (factor_monic_and_irreducible_of_valid
          hvalid hentry).1)
      (by simpa using hfactorProduct)
      hreducedDivisorMonic hreducedDivides
  let signatureSubset : Multiset (ℕ × ZMod certificate.prime) :=
    factorSubset.map fun factor => (factor.natDegree, factor.coeff 0)
  have hsignatureSubset :
      signatureSubset ≤ certificate.factorSignatures := by
    have hmapped := Multiset.map_le_map
      (f := fun factor : (ZMod certificate.prime)[X] =>
        (factor.natDegree, factor.coeff 0)) hfactorSubset
    have hfullSignatures :
        Multiset.map
          (fun factor : (ZMod certificate.prime)[X] =>
            (factor.natDegree, factor.coeff 0))
          (certificate.factorPolynomials :
            Multiset (ZMod certificate.prime)[X]) =
          certificate.factorSignatures := by
      simpa using factorPolynomials_signatures_eq_of_valid hvalid
    rw [hfullSignatures] at hmapped
    exact hmapped
  have hfactorSubsetZero : (0 : (ZMod certificate.prime)[X]) ∉
      factorSubset := by
    intro hzero
    have hzeroFull := Multiset.mem_of_le hfactorSubset hzero
    have hzeroList :
        (0 : (ZMod certificate.prime)[X]) ∈
          certificate.factorPolynomials := by
      simpa using hzeroFull
    rcases List.mem_map.mp hzeroList with ⟨entry, hentry, heq⟩
    have hirreducible :=
      (factor_monic_and_irreducible_of_valid hvalid hentry).2
    exact hirreducible.ne_zero heq
  have hsignatureDegree :
      (signatureSubset.map Prod.fst).sum = factorDegree := by
    dsimp [signatureSubset]
    rw [Multiset.map_map]
    change (factorSubset.map Polynomial.natDegree).sum = factorDegree
    rw [← Polynomial.natDegree_multiset_prod factorSubset
      hfactorSubsetZero, hfactorSubsetProduct]
    change reducedDivisor.natDegree = factorDegree
    rw [hdivisorMonic.natDegree_map, hdivisorDegree]
  have hconstantDivides : divisor.coeff 0 ∣ sourceConstant row := by
    obtain ⟨quotient, hquotient⟩ := hdivides
    refine ⟨quotient.coeff 0, ?_⟩
    rw [← Polynomial.mul_coeff_zero, ← hquotient]
    exact (v15VoightPolynomial_coeff row 0).symm
  have hsignatureConstant :
      (signatureSubset.map Prod.snd).prod =
        (divisor.coeff 0 : ZMod certificate.prime) := by
    dsimp [signatureSubset]
    rw [Multiset.map_map]
    change (factorSubset.map fun factor => factor.coeff 0).prod = _
    rw [← Polynomial.coeff_zero_multiset_prod,
      hfactorSubsetProduct]
    change (divisor.map
      (Int.castRingHom (ZMod certificate.prime))).coeff 0 = _
    rw [Polynomial.coeff_map]
    rfl
  exact (excludesDegree_spec hexcludes hsignatureSubset
    hsignatureDegree hconstantDivides hvalid.2.2.2.1)
    hsignatureConstant

/-- A monic divisor of a completely factored polynomial is the product of a
submultiset of the displayed irreducible monic factors. -/
theorem exists_factor_submultiset_of_monic_dvd
    {K : Type*} [Field K] {source divisor : K[X]}
    (factors : Multiset K[X])
    (hirreducible : ∀ factor ∈ factors, Irreducible factor)
    (hmonic : ∀ factor ∈ factors, factor.Monic)
    (hproduct : factors.prod = source)
    (hdivisorMonic : divisor.Monic) (hdivides : divisor ∣ source) :
    ∃ subset ≤ factors, subset.prod = divisor := by
  classical
  have hdivisorZero : divisor ≠ 0 := hdivisorMonic.ne_zero
  have hfactorsZero : factors.prod ≠ 0 :=
    Multiset.prod_ne_zero fun hzero =>
      (hirreducible 0 hzero).ne_zero rfl
  have hsourceZero : source ≠ 0 := hproduct ▸ hfactorsZero
  have hnormalizedFactors : normalizedFactors source = factors := by
    rw [← hproduct, normalizedFactors_prod_eq factors hirreducible]
    have hmap : factors.map normalize = factors := by
      calc
        factors.map normalize = factors.map id := by
          apply Multiset.map_congr rfl
          intro factor hfactor
          exact (normalize_eq_self_iff_monic
            (hirreducible factor hfactor).ne_zero).2
              (hmonic factor hfactor)
        _ = factors := Multiset.map_id factors
    exact hmap
  refine ⟨normalizedFactors divisor, ?_, ?_⟩
  · rw [← hnormalizedFactors]
    exact (dvd_iff_normalizedFactors_le_normalizedFactors
      hdivisorZero hsourceZero).1 hdivides
  · have hfactorization :=
      Polynomial.leadingCoeff_mul_prod_normalizedFactors divisor
    simpa [hdivisorMonic.leadingCoeff] using hfactorization

end V15ModularFactorizationCertificate

/-- A collection of complete modular factorizations together with the index
of the factorization used for each possible proper factor degree. -/
structure V15MultiPrimeIrreducibilityCertificate where
  factorizations : List V15ModularFactorizationCertificate
  assignments : List ℕ
deriving DecidableEq, Repr

namespace V15MultiPrimeIrreducibilityCertificate

/-- Harmless fallback used only outside the range certified by `Valid`. -/
def fallbackFactorization : V15ModularFactorizationCertificate :=
  ⟨2, []⟩

/-- Factorization assigned to the positive degree `index + 1`. -/
def factorizationAt
    (certificate : V15MultiPrimeIrreducibilityCertificate)
    (index : ℕ) : V15ModularFactorizationCertificate :=
  certificate.factorizations.getD
    (certificate.assignments.getD index 0) fallbackFactorization

/-- Mathematical statement replayed by a multi-prime certificate. -/
abbrev Valid (degree : ℕ) (row : V15VoightPolynomialRow)
    (certificate : V15MultiPrimeIrreducibilityCertificate) : Prop :=
  1 < degree ∧
    row.coefficients.length = degree + 1 ∧
    row.coefficients.getLast? = some 1 ∧
    certificate.assignments.length = degree / 2 ∧
    (∀ index : Fin (degree / 2),
      (certificate.factorizationAt index.val).Valid degree row ∧
      (certificate.factorizationAt index.val).excludesDegree row
        (index.val + 1) = true)

/-- Executable wrapper for multi-prime validity. -/
def check (degree : ℕ) (row : V15VoightPolynomialRow)
    (certificate : V15MultiPrimeIrreducibilityCertificate) : Bool :=
  decide (certificate.Valid degree row)

theorem valid_of_check_eq_true {degree : ℕ}
    {row : V15VoightPolynomialRow}
    {certificate : V15MultiPrimeIrreducibilityCertificate}
    (h : certificate.check degree row = true) :
    certificate.Valid degree row := by
  exact of_decide_eq_true h

/-- Every accepted multi-prime certificate proves irreducibility over the
integers. -/
theorem irreducible_of_valid {degree : ℕ}
    {row : V15VoightPolynomialRow}
    {certificate : V15MultiPrimeIrreducibilityCertificate}
    (hvalid : certificate.Valid degree row) :
    Irreducible row.polynomial := by
  have hrowDegree := v15VoightPolynomial_isMonicOfDegree degree row
    hvalid.2.1 hvalid.2.2.1
  have hrowNotOne : row.polynomial ≠ 1 := by
    intro hrowOne
    have hdegreeZero : degree = 0 := by
      rw [← hrowDegree.natDegree_eq, hrowOne,
        Polynomial.natDegree_one]
    omega
  rw [hrowDegree.monic.irreducible_iff_lt_natDegree_lt hrowNotOne]
  intro divisor hdivisorMonic hdivisorDegree
  have hdegreeInterval := Finset.mem_Ioc.mp hdivisorDegree
  have hdegreePositive : 0 < divisor.natDegree := hdegreeInterval.1
  have hdegreeBound : divisor.natDegree ≤ degree / 2 := by
    simpa [hrowDegree.natDegree_eq] using hdegreeInterval.2
  let index : Fin (degree / 2) :=
    ⟨divisor.natDegree - 1, by omega⟩
  have hassigned := hvalid.2.2.2.2 index
  have hindexDegree : index.val + 1 = divisor.natDegree := by
    dsimp [index]
    omega
  apply V15ModularFactorizationCertificate.not_dvd_of_valid_and_excludesDegree
    (factorDegree := index.val + 1)
    hassigned.1 hassigned.2
    hdivisorMonic
  exact hindexDegree.symm

/-- Executable certificates expose the same irreducibility conclusion. -/
theorem irreducible_of_check_eq_true {degree : ℕ}
    {row : V15VoightPolynomialRow}
    {certificate : V15MultiPrimeIrreducibilityCertificate}
    (h : certificate.check degree row = true) :
    Irreducible row.polynomial :=
  irreducible_of_valid (valid_of_check_eq_true h)

end V15MultiPrimeIrreducibilityCertificate

/-- Check a list of multi-prime certificates against a list of rows. -/
def v15MultiPrimeCertificateBatchCheck (degree : ℕ)
    (rows : List V15VoightPolynomialRow)
    (certificates : List V15MultiPrimeIrreducibilityCertificate) : Bool :=
  decide (rows.length = certificates.length) &&
    (rows.zip certificates).all fun rowAndCertificate =>
      rowAndCertificate.2.check degree rowAndCertificate.1

/-- A successful multi-prime batch check supplies an irreducibility theorem
for every row in the batch. -/
theorem v15_irreducible_of_multiPrimeBatchCheck_eq_true (degree : ℕ) :
    ∀ {rows : List V15VoightPolynomialRow}
      {certificates : List V15MultiPrimeIrreducibilityCertificate},
      v15MultiPrimeCertificateBatchCheck degree rows certificates = true →
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
          simp [v15MultiPrimeCertificateBatchCheck] at h
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
              v15MultiPrimeCertificateBatchCheck degree rows certificates =
                true := by
            exact Bool.and_eq_true_iff.mpr
              ⟨decide_eq_true hlength, hallParts.2⟩
          rcases List.mem_cons.mp hrow with rfl | hrow
          · exact
              V15MultiPrimeIrreducibilityCertificate.irreducible_of_check_eq_true
                hallParts.1
          · exact induction htail row hrow

end TraceEuclidean
