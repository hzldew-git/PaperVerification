import TraceEuclidean.V15FiniteFieldIrreducibilityCertificate

/-!
# Rational interval certificates for total reality

This module turns exact rational sign changes on pairwise disjoint intervals
into a proof that an integral polynomial splits over the real numbers.  The
large archived tables use this kernel-checked implication with generated
finite certificates.
-/

namespace TraceEuclidean

open Polynomial

/-- One rational interval intended to isolate a real root. -/
structure V15RationalRootInterval where
  lower : ℚ
  upper : ℚ
deriving DecidableEq, Repr

/-- The defining polynomial evaluated over the reals. -/
noncomputable def V15VoightPolynomialRow.realPolynomial
    (row : V15VoightPolynomialRow) : ℝ[X] :=
  row.polynomial.map (Int.castRingHom ℝ)

/-- Computable exact evaluation of a defining polynomial over the rationals. -/
def V15VoightPolynomialRow.rationalEval
    (row : V15VoightPolynomialRow) (value : ℚ) : ℚ :=
  V15DensePolynomial.eval
    (row.coefficients.map (Int.castRingHom ℚ)) value

/-- Executable root-isolation conditions.  There is one sign-changing
interval per degree, and the intervals are strictly ordered. -/
def V15RationalRootIntervalCertificate.Valid
    (degree : ℕ) (row : V15VoightPolynomialRow)
    (intervals : List V15RationalRootInterval) : Prop :=
  0 < degree ∧
    row.coefficients.length = degree + 1 ∧
    row.coefficients.getLast? = some 1 ∧
    intervals.length = degree ∧
    intervals.Forall (fun interval =>
      interval.lower < interval.upper ∧
        row.rationalEval interval.lower *
          row.rationalEval interval.upper < 0) ∧
    intervals.Pairwise (fun left right => left.upper < right.lower)

instance (degree : ℕ) (row : V15VoightPolynomialRow)
    (intervals : List V15RationalRootInterval) :
    Decidable (V15RationalRootIntervalCertificate.Valid degree row intervals) :=
  by
    unfold V15RationalRootIntervalCertificate.Valid
    infer_instance

/-- Executable wrapper for a rational root-interval certificate. -/
def v15RationalRootIntervalCertificateCheck
    (degree : ℕ) (row : V15VoightPolynomialRow)
    (intervals : List V15RationalRootInterval) : Bool :=
  decide (V15RationalRootIntervalCertificate.Valid degree row intervals)

theorem v15RationalRootIntervalCertificate_valid_of_check_eq_true
    {degree : ℕ} {row : V15VoightPolynomialRow}
    {intervals : List V15RationalRootInterval}
    (hcheck : v15RationalRootIntervalCertificateCheck
      degree row intervals = true) :
    V15RationalRootIntervalCertificate.Valid degree row intervals := by
  exact of_decide_eq_true hcheck

private theorem v15_voightPolynomial_eq_dense
    (row : V15VoightPolynomialRow) :
    row.polynomial =
      V15DensePolynomial.toPolynomial row.coefficients := by
  ext exponent
  simp [v15VoightPolynomial_coeff]

private theorem v15_eval_realPolynomial_ratCast
    (row : V15VoightPolynomialRow) (x : ℚ) :
    row.realPolynomial.eval (x : ℝ) =
      (row.rationalEval x : ℝ) := by
  rw [V15VoightPolynomialRow.realPolynomial,
    v15_voightPolynomial_eq_dense,
    ← V15DensePolynomial.toPolynomial_map]
  rw [V15DensePolynomial.eval_toPolynomial]
  change V15DensePolynomial.eval
    (row.coefficients.map (Int.castRingHom ℝ))
      (x : ℝ) = _
  rw [show row.coefficients.map (Int.castRingHom ℝ) =
      (row.coefficients.map (Int.castRingHom ℚ)).map
        (algebraMap ℚ ℝ) by
    simp]
  change V15DensePolynomial.eval
      ((row.coefficients.map (Int.castRingHom ℚ)).map
        (algebraMap ℚ ℝ)) (algebraMap ℚ ℝ x) =
    algebraMap ℚ ℝ (row.rationalEval x)
  unfold V15VoightPolynomialRow.rationalEval
  exact V15DensePolynomial.eval_map (algebraMap ℚ ℝ)
    (row.coefficients.map (Int.castRingHom ℚ)) x

private theorem v15_exists_real_root_in_rational_interval
    (row : V15VoightPolynomialRow)
    (interval : V15RationalRootInterval)
    (hinterval : interval.lower < interval.upper)
    (hsign : row.rationalEval interval.lower *
      row.rationalEval interval.upper < 0) :
    ∃ root : ℝ,
      root ∈ Set.Icc (interval.lower : ℝ) (interval.upper : ℝ) ∧
        row.realPolynomial.eval root = 0 := by
  have hlowerUpper : (interval.lower : ℝ) ≤ interval.upper := by
    exact_mod_cast hinterval.le
  have hsignReal :
      row.realPolynomial.eval (interval.lower : ℝ) *
        row.realPolynomial.eval (interval.upper : ℝ) < 0 := by
    rw [v15_eval_realPolynomial_ratCast,
      v15_eval_realPolynomial_ratCast]
    exact_mod_cast hsign
  have hzeroBetween :
      (0 : ℝ) ∈ Set.uIcc
        (row.realPolynomial.eval (interval.lower : ℝ))
        (row.realPolynomial.eval (interval.upper : ℝ)) := by
    rw [Set.mem_uIcc]
    rcases (mul_neg_iff.mp hsignReal) with h | h
    · exact Or.inr ⟨h.2.le, h.1.le⟩
    · exact Or.inl ⟨h.1.le, h.2.le⟩
  obtain ⟨root, hrootInterval, hroot⟩ :=
    (intermediate_value_uIcc
      row.realPolynomial.continuous.continuousOn hzeroBetween)
  rw [Set.uIcc_of_le hlowerUpper] at hrootInterval
  exact ⟨root, hrootInterval, hroot⟩

/-- A valid family of rational root intervals proves that the defining
polynomial splits completely over the real numbers. -/
theorem v15_realPolynomial_splits_of_rootIntervalCertificate
    {degree : ℕ} {row : V15VoightPolynomialRow}
    {intervals : List V15RationalRootInterval}
    (hvalid : V15RationalRootIntervalCertificate.Valid
      degree row intervals) :
    row.realPolynomial.Splits := by
  rcases hvalid with
    ⟨hdegreePositive, hcoefficientLength, hlast, hintervalLength,
      hintervals, hpairwise⟩
  have hrowDegree := v15VoightPolynomial_isMonicOfDegree degree row
    hcoefficientLength hlast
  have hrealDegree : row.realPolynomial.natDegree = degree := by
    rw [V15VoightPolynomialRow.realPolynomial,
      hrowDegree.monic.natDegree_map, hrowDegree.natDegree_eq]
  have hrealNonzero : row.realPolynomial ≠ 0 := by
    intro hzero
    have : degree = 0 := by
      rw [← hrealDegree, hzero, Polynomial.natDegree_zero]
    omega
  have hrootExists : ∀ index : Fin intervals.length,
      ∃ root : ℝ,
        root ∈ Set.Icc ((intervals.get index).lower : ℝ)
          ((intervals.get index).upper : ℝ) ∧
          row.realPolynomial.eval root = 0 := by
    intro index
    have hmem : intervals.get index ∈ intervals :=
      List.get_mem intervals index
    have hinterval :=
      (List.forall_iff_forall_mem.mp hintervals) _ hmem
    exact v15_exists_real_root_in_rational_interval row
      (intervals.get index) hinterval.1 hinterval.2
  let root : Fin intervals.length → ℝ := fun index =>
    Classical.choose (hrootExists index)
  have hrootSpec : ∀ index : Fin intervals.length,
      root index ∈ Set.Icc ((intervals.get index).lower : ℝ)
        ((intervals.get index).upper : ℝ) ∧
        row.realPolynomial.eval (root index) = 0 := by
    intro index
    exact Classical.choose_spec (hrootExists index)
  have hrootStrictMono : StrictMono root := by
    intro left right hleftRight
    have hseparated := hpairwise.rel_get_of_lt hleftRight
    have hseparatedReal :
        ((intervals.get left).upper : ℝ) <
          (intervals.get right).lower := by
      exact_mod_cast hseparated
    exact lt_of_le_of_lt (hrootSpec left).1.2
      (lt_of_lt_of_le hseparatedReal (hrootSpec right).1.1)
  let rootSet : Finset ℝ := Finset.univ.image root
  have hrootSetCard : rootSet.card = intervals.length := by
    dsimp [rootSet]
    rw [Finset.card_image_of_injective _ hrootStrictMono.injective,
      Finset.card_univ, Fintype.card_fin]
  have hrootSetSubset : rootSet ⊆ row.realPolynomial.roots.toFinset := by
    intro value hvalue
    obtain ⟨index, -, rfl⟩ := Finset.mem_image.mp hvalue
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hrealNonzero]
    exact (hrootSpec index).2
  have hlower : degree ≤ row.realPolynomial.roots.card := by
    calc
      degree = rootSet.card := by rw [hrootSetCard, hintervalLength]
      _ ≤ row.realPolynomial.roots.toFinset.card :=
        Finset.card_le_card hrootSetSubset
      _ ≤ row.realPolynomial.roots.card :=
        row.realPolynomial.roots.toFinset_card_le
  apply Polynomial.splits_iff_card_roots.mpr
  exact Nat.le_antisymm (Polynomial.card_roots' row.realPolynomial)
    (by simpa [hrealDegree] using hlower)

/-- A successful executable check proves real splitting. -/
theorem v15_realPolynomial_splits_of_rootIntervalCheck_eq_true
    {degree : ℕ} {row : V15VoightPolynomialRow}
    {intervals : List V15RationalRootInterval}
    (hcheck : v15RationalRootIntervalCertificateCheck
      degree row intervals = true) :
    row.realPolynomial.Splits :=
  v15_realPolynomial_splits_of_rootIntervalCertificate
    (v15RationalRootIntervalCertificate_valid_of_check_eq_true hcheck)

/-- Check one interval-certificate list for every row in a finite batch. -/
def v15RootIntervalCertificateBatchCheck (degree : ℕ)
    (rows : List V15VoightPolynomialRow)
    (certificates : List (List V15RationalRootInterval)) : Bool :=
  decide (rows.length = certificates.length) &&
    (rows.zip certificates).all fun rowAndCertificate =>
      v15RationalRootIntervalCertificateCheck degree
        rowAndCertificate.1 rowAndCertificate.2

/-- A successful batch check supplies real splitting for every row in the
batch. -/
theorem v15_splits_of_rootIntervalBatchCheck_eq_true (degree : ℕ) :
    ∀ {rows : List V15VoightPolynomialRow}
      {certificates : List (List V15RationalRootInterval)},
      v15RootIntervalCertificateBatchCheck degree rows certificates = true →
        ∀ row ∈ rows, row.realPolynomial.Splits := by
  intro rows
  induction rows with
  | nil =>
      intro certificates h row hrow
      simp at hrow
  | cons first rows induction =>
      intro certificates h row hrow
      cases certificates with
      | nil =>
          simp [v15RootIntervalCertificateBatchCheck] at h
      | cons certificate certificates =>
          have hparts := Bool.and_eq_true_iff.mp h
          have hlength : rows.length = certificates.length := by
            simpa using of_decide_eq_true hparts.1
          have hallParts :
              v15RationalRootIntervalCertificateCheck degree
                  first certificate = true ∧
                ((rows.zip certificates).all fun rowAndCertificate =>
                  v15RationalRootIntervalCertificateCheck degree
                    rowAndCertificate.1 rowAndCertificate.2) = true := by
            simpa [List.all_cons, Bool.and_eq_true_iff] using hparts.2
          have htail :
              v15RootIntervalCertificateBatchCheck degree
                rows certificates = true := by
            exact Bool.and_eq_true_iff.mpr
              ⟨decide_eq_true hlength, hallParts.2⟩
          rcases List.mem_cons.mp hrow with rfl | hrow
          · exact v15_realPolynomial_splits_of_rootIntervalCheck_eq_true
              hallParts.1
          · exact induction htail row hrow

end TraceEuclidean
