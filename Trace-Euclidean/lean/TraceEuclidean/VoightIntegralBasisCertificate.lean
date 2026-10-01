import TraceEuclidean.VoightSquarefreeIndexOneCore
import TraceEuclidean.DensePolynomialCertificate
import TraceEuclidean.VoightAllRows

/-!
# Integral-basis certificates for archived Voight rows

This module provides a small certificate language for proving that rational
linear combinations of a Voight power basis are algebraic integers.  A
certificate supplies, for every proposed basis vector, a monic integral
annihilating polynomial and an exact polynomial identity modulo the archived
defining polynomial.  A rational change-of-basis determinant then computes
the discriminant of the proposed integral family.
-/

namespace TraceEuclidean

noncomputable section

open Algebra Module NumberField Polynomial
open scoped Matrix NumberField

/-- A dense coefficient list whose final coefficient is one represents a
monic polynomial of the corresponding degree. -/
theorem densePolynomial_isMonicOfDegree
    (values : List ℤ) (degree : ℕ)
    (hlength : values.length = degree + 1)
    (hlast : values.getLast? = some 1) :
    (DensePolynomial.toPolynomial values).IsMonicOfDegree degree := by
  rw [Polynomial.isMonicOfDegree_iff]
  constructor
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro exponent hexponent
    rw [DensePolynomial.coeff_toPolynomial,
      List.getD_eq_default values 0]
    omega
  · rw [DensePolynomial.coeff_toPolynomial,
      List.getD_eq_getElem?_getD]
    have hlast' := hlast
    rw [List.getLast?_eq_getElem?, hlength] at hlast'
    simp only [Nat.add_sub_cancel] at hlast'
    rw [hlast']
    rfl

/-- A nonempty dense integer polynomial ending in one is monic. -/
theorem densePolynomial_monic_of_getLast_eq_one
    (values : List ℤ) (hlast : values.getLast? = some 1) :
    (DensePolynomial.toPolynomial values).Monic := by
  have hnonempty : values ≠ [] := by
    intro hnil
    simp [hnil] at hlast
  have hpositive : 0 < values.length :=
    List.length_pos_of_ne_nil hnonempty
  have hlength : values.length = (values.length - 1) + 1 := by
    omega
  exact (densePolynomial_isMonicOfDegree values
    (values.length - 1) hlength hlast).monic

/-- The dense representation agrees with the archived polynomial. -/
theorem voightPolynomial_eq_dense
    (row : VoightPolynomialRow) :
    row.polynomial =
      DensePolynomial.toPolynomial row.coefficients := by
  ext exponent
  simp [voightPolynomial_coeff]

/-- The rational dense representation agrees with the archived rational
polynomial. -/
theorem voightRationalPolynomial_eq_dense
    (row : VoightPolynomialRow) :
    row.rationalPolynomial =
      DensePolynomial.toPolynomial
        (row.coefficients.map (Int.castRingHom ℚ)) := by
  rw [VoightPolynomialRow.rationalPolynomial,
    voightPolynomial_eq_dense,
    DensePolynomial.toPolynomial_map]

/-- Horner evaluation of a finite coefficient vector is its usual finite
power sum. -/
theorem densePolynomial_eval_ofFn
    {R : Type*} [CommSemiring R]
    (d : ℕ) (coefficients : Fin d → R) (value : R) :
    DensePolynomial.eval (List.ofFn coefficients) value =
      ∑ i : Fin d, coefficients i * value ^ (i : ℕ) := by
  induction d with
  | zero => simp [DensePolynomial.eval]
  | succ d induction =>
      rw [List.ofFn_succ, DensePolynomial.eval,
        Fin.sum_univ_succ]
      rw [induction]
      simp only [Fin.val_succ, pow_succ]
      rw [Finset.mul_sum]
      simp only [Fin.val_zero, pow_zero, mul_one]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- The quotient map sends a dense column polynomial to the corresponding
linear combination of powers of the adjoined root. -/
theorem adjoinRoot_mk_dense_ofFn
    (q : ℚ[X]) (d : ℕ) (coefficients : Fin d → ℚ) :
    AdjoinRoot.mk q
        (DensePolynomial.toPolynomial (List.ofFn coefficients)) =
      ∑ i : Fin d,
        algebraMap ℚ (AdjoinRoot q) (coefficients i) *
          AdjoinRoot.root q ^ (i : ℕ) := by
  rw [← AdjoinRoot.aeval_eq]
  rw [Polynomial.aeval_def]
  rw [← Polynomial.eval_map,
    ← DensePolynomial.toPolynomial_map,
    DensePolynomial.eval_toPolynomial]
  rw [show (List.ofFn coefficients).map
      (algebraMap ℚ (AdjoinRoot q)) =
        List.ofFn (fun i ↦
          algebraMap ℚ (AdjoinRoot q) (coefficients i)) by
    simp [Function.comp_def]]
  exact densePolynomial_eval_ofFn d
    (fun i ↦ algebraMap ℚ (AdjoinRoot q) (coefficients i))
      (AdjoinRoot.root q)

/-- Data needed to certify one rational change of the power basis. -/
structure VoightIntegralBasisCertificate (d : ℕ) where
  matrix : Matrix (Fin d) (Fin d) ℚ
  annihilators : Fin d → List ℤ
  quotients : Fin d → List ℚ

/-- A certificate bundled with its degree and archived row. -/
structure VoightIntegralBasisCertificateEntry where
  degree : ℕ
  row : VoightPolynomialRow
  certificate : VoightIntegralBasisCertificate degree

/-- Selector for the squarefree rows whose recorded power-order index is
nontrivial. -/
def VoightPolynomialRow.squarefreeNontrivialIndex
    (row : VoightPolynomialRow) : Bool :=
  decide (Squarefree row.fieldDiscriminant) && decide (1 < row.index)

/-- The selector states exactly squarefreeness and nontrivial index. -/
theorem voightPolynomialRow_squarefreeNontrivialIndex_iff
    (row : VoightPolynomialRow) :
    row.squarefreeNontrivialIndex = true ↔
      Squarefree row.fieldDiscriminant ∧ 1 < row.index := by
  simp [VoightPolynomialRow.squarefreeNontrivialIndex]

/-- The archived squarefree rows requiring a nontrivial integral-basis
certificate. -/
def voightSquarefreeNontrivialIndexRows :
    List VoightPolynomialRow :=
  allVoightPolynomialRows.filter
    VoightPolynomialRow.squarefreeNontrivialIndex

/-- Dense coefficients of one proposed integral basis vector. -/
def VoightIntegralBasisCertificate.columnCoefficients
    {d : ℕ} (certificate : VoightIntegralBasisCertificate d)
    (column : Fin d) : List ℚ :=
  List.ofFn fun row ↦ certificate.matrix row column

/-- The proposed field element represented by one matrix column. -/
def VoightIntegralBasisCertificate.element
    {d : ℕ} (row : VoightPolynomialRow)
    (certificate : VoightIntegralBasisCertificate d)
    (column : Fin d) : AdjoinRoot row.rationalPolynomial :=
  AdjoinRoot.mk row.rationalPolynomial
    (DensePolynomial.toPolynomial
      (certificate.columnCoefficients column))

/-- One column is certified integral when its monic annihilator becomes a
multiple of the defining polynomial after substitution. -/
def VoightIntegralBasisCertificate.ElementValid
    {d : ℕ} (row : VoightPolynomialRow)
    (certificate : VoightIntegralBasisCertificate d)
    (column : Fin d) : Prop :=
  (certificate.annihilators column).getLast? = some 1 ∧
    DensePolynomial.equal
      (DensePolynomial.comp
        ((certificate.annihilators column).map
          (Int.castRingHom ℚ))
        (certificate.columnCoefficients column))
      (DensePolynomial.mul
        (row.coefficients.map (Int.castRingHom ℚ))
        (certificate.quotients column)) = true

/-- Executable version of one column certificate. -/
def VoightIntegralBasisCertificate.elementCheck
    {d : ℕ} (row : VoightPolynomialRow)
    (certificate : VoightIntegralBasisCertificate d)
    (column : Fin d) : Bool :=
  (certificate.annihilators column).getLast? == some 1 &&
    DensePolynomial.equal
      (DensePolynomial.comp
        ((certificate.annihilators column).map
          (Int.castRingHom ℚ))
        (certificate.columnCoefficients column))
      (DensePolynomial.mul
        (row.coefficients.map (Int.castRingHom ℚ))
        (certificate.quotients column))

/-- The executable column check has the stated mathematical semantics. -/
theorem VoightIntegralBasisCertificate.elementCheck_eq_true_iff
    {d : ℕ} (row : VoightPolynomialRow)
    (certificate : VoightIntegralBasisCertificate d)
    (column : Fin d) :
    certificate.elementCheck row column = true ↔
      certificate.ElementValid row column := by
  simp [elementCheck, ElementValid]

/-- Efficient finite check that the change-of-basis matrix is upper
triangular. This avoids expanding the factorial determinant formula in the
generated certificate replay. -/
def VoightIntegralBasisCertificate.upperTriangularCheck
    {d : ℕ} (certificate : VoightIntegralBasisCertificate d) : Bool :=
  (List.ofFn fun i : Fin d ↦
    (List.ofFn fun j : Fin d ↦
      decide ((j : ℕ) < (i : ℕ) →
        certificate.matrix i j = 0)).all id).all id

/-- The finite triangular check has the usual matrix semantics. -/
theorem VoightIntegralBasisCertificate.upperTriangularCheck_eq_true_iff
    {d : ℕ} (certificate : VoightIntegralBasisCertificate d) :
    certificate.upperTriangularCheck = true ↔
      certificate.matrix.BlockTriangular id := by
  simp only [upperTriangularCheck, List.all_eq_true,
    List.forall_mem_ofFn_iff, id_eq, decide_eq_true_eq,
    Matrix.BlockTriangular]
  constructor
  · intro h i j hji
    exact h i j hji
  · intro h i j hji
    exact h hji

/-- Product of the diagonal entries, used by the triangular determinant
certificate. -/
def VoightIntegralBasisCertificate.diagonalProduct
    {d : ℕ} (certificate : VoightIntegralBasisCertificate d) : ℚ :=
  ∏ i : Fin d, certificate.matrix i i

/-- Full validity: every column is integral and the rational determinant
cancels the square of the recorded power-order index. -/
def VoightIntegralBasisCertificate.Valid
    {d : ℕ} (row : VoightPolynomialRow)
    (certificate : VoightIntegralBasisCertificate d) : Prop :=
  (∀ column, certificate.ElementValid row column) ∧
    certificate.matrix.det ^ 2 * (row.index : ℚ) ^ 2 = 1

/-- A bundled certificate is valid when its degree is positive, its row
belongs to that archived degree table, and all algebraic checks succeed. -/
def VoightIntegralBasisCertificateEntry.Valid
    (entry : VoightIntegralBasisCertificateEntry) : Prop :=
  0 < entry.degree ∧
    entry.row ∈ voightPolynomialRows entry.degree ∧
      entry.certificate.Valid entry.row

/-- Executable certificate check. -/
def VoightIntegralBasisCertificate.check
    {d : ℕ} (row : VoightPolynomialRow)
    (certificate : VoightIntegralBasisCertificate d) : Bool :=
  (List.ofFn fun column ↦
      certificate.elementCheck row column).all id &&
    certificate.upperTriangularCheck &&
      decide (certificate.diagonalProduct ^ 2 *
        (row.index : ℚ) ^ 2 = 1)

/-- Executable check for a bundled row certificate. -/
def VoightIntegralBasisCertificateEntry.check
    (entry : VoightIntegralBasisCertificateEntry) : Bool :=
  decide (0 < entry.degree) &&
    decide (entry.row ∈ voightPolynomialRows entry.degree) &&
      entry.certificate.check entry.row

/-- A successful executable check exposes the semantic validity proposition. -/
theorem VoightIntegralBasisCertificate.valid_of_check_eq_true
    {d : ℕ} {row : VoightPolynomialRow}
    {certificate : VoightIntegralBasisCertificate d}
    (hcheck : certificate.check row = true) :
    certificate.Valid row := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  constructor
  · intro column
    apply (certificate.elementCheck_eq_true_iff row column).1
    have hall := List.all_eq_true.mp hcheck.1.1
    exact (List.forall_mem_ofFn_iff.mp hall) column
  · have htriangular : certificate.matrix.BlockTriangular id :=
      (certificate.upperTriangularCheck_eq_true_iff).1 hcheck.1.2
    rw [Matrix.det_of_upperTriangular htriangular]
    exact hcheck.2

/-- A successful executable bundled check exposes the semantic validity
proposition. -/
theorem VoightIntegralBasisCertificateEntry.valid_of_check_eq_true
    {entry : VoightIntegralBasisCertificateEntry}
    (hcheck : entry.check = true) : entry.Valid := by
  simp only [VoightIntegralBasisCertificateEntry.check,
    Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact ⟨hcheck.1.1, hcheck.1.2,
    entry.certificate.valid_of_check_eq_true hcheck.2⟩

/-- A valid column certificate proves that the represented field element is
integral over the integers. -/
theorem VoightIntegralBasisCertificate.element_isIntegral
    {d : ℕ} (row : VoightPolynomialRow)
    (certificate : VoightIntegralBasisCertificate d)
    (hvalid : certificate.Valid row) (column : Fin d) :
    IsIntegral ℤ (certificate.element row column) := by
  let annihilator : ℤ[X] :=
    DensePolynomial.toPolynomial
      (certificate.annihilators column)
  let elementPolynomial : ℚ[X] :=
    DensePolynomial.toPolynomial
      (certificate.columnCoefficients column)
  let quotient : ℚ[X] :=
    DensePolynomial.toPolynomial
      (certificate.quotients column)
  have hcolumn := hvalid.1 column
  have hmonic : annihilator.Monic := by
    exact densePolynomial_monic_of_getLast_eq_one
      (certificate.annihilators column) hcolumn.1
  have hequal :=
    DensePolynomial.toPolynomial_eq_of_equal hcolumn.2
  change DensePolynomial.toPolynomial
      (DensePolynomial.comp
        ((certificate.annihilators column).map
          (Int.castRingHom ℚ))
        (certificate.columnCoefficients column)) =
    DensePolynomial.toPolynomial
      (DensePolynomial.mul
        (row.coefficients.map (Int.castRingHom ℚ))
        (certificate.quotients column)) at hequal
  have hpolynomial :
      (annihilator.map (Int.castRingHom ℚ)).comp
          elementPolynomial =
        row.rationalPolynomial * quotient := by
    rw [DensePolynomial.toPolynomial_comp,
      DensePolynomial.toPolynomial_mul] at hequal
    have hannihilator :
        DensePolynomial.toPolynomial
            ((certificate.annihilators column).map
              (Int.castRingHom ℚ)) =
          annihilator.map (Int.castRingHom ℚ) := by
      exact DensePolynomial.toPolynomial_map
        (Int.castRingHom ℚ) (certificate.annihilators column)
    rw [hannihilator,
      ← voightRationalPolynomial_eq_dense] at hequal
    simpa only [elementPolynomial, quotient] using hequal
  have hdvd : row.rationalPolynomial ∣
      (annihilator.map (Int.castRingHom ℚ)).comp
        elementPolynomial := by
    exact ⟨quotient, hpolynomial⟩
  refine ⟨annihilator, hmonic, ?_⟩
  change Polynomial.eval₂
      (algebraMap ℤ (AdjoinRoot row.rationalPolynomial))
      (certificate.element row column) annihilator = 0
  calc
    Polynomial.eval₂
        (algebraMap ℤ (AdjoinRoot row.rationalPolynomial))
        (certificate.element row column) annihilator =
      Polynomial.aeval (certificate.element row column)
        (annihilator.map (Int.castRingHom ℚ)) := by
          rw [Polynomial.aeval_def, Polynomial.eval₂_map]
          rw [IsScalarTower.algebraMap_eq ℤ ℚ
            (AdjoinRoot row.rationalPolynomial)]
          rw [algebraMap_int_eq]
    _ = Polynomial.aeval (AdjoinRoot.root row.rationalPolynomial)
        ((annihilator.map (Int.castRingHom ℚ)).comp
          elementPolynomial) := by
          rw [Polynomial.aeval_comp, AdjoinRoot.aeval_eq]
          rfl
    _ = AdjoinRoot.mk row.rationalPolynomial
        ((annihilator.map (Int.castRingHom ℚ)).comp
          elementPolynomial) := by
          rw [AdjoinRoot.aeval_eq]
    _ = 0 := AdjoinRoot.mk_eq_zero.mpr hdvd

/-- A valid certificate whose recorded discriminant is squarefree identifies
the actual number-field discriminant. -/
theorem voight_fieldDiscriminant_eq_of_integralBasisCertificate
    (d : ℕ) (row : VoightPolynomialRow)
    (certificate : VoightIntegralBasisCertificate d)
    [Fact (Irreducible row.rationalPolynomial)]
    (hd : 0 < d)
    (hdegree : row.polynomial.IsMonicOfDegree d)
    (hsquarefree : Squarefree row.fieldDiscriminant)
    (hrecorded : row.polynomial.discr =
      (row.index : ℤ) ^ 2 * (row.fieldDiscriminant : ℤ))
    (hvalid : certificate.Valid row) :
    NumberField.discr (AdjoinRoot row.rationalPolynomial) =
      (row.fieldDiscriminant : ℤ) := by
  classical
  have hirrQ : Irreducible row.rationalPolynomial := Fact.out
  let K := AdjoinRoot row.rationalPolynomial
  have hdegreeK : Module.finrank ℚ K = d := by
    calc
      Module.finrank ℚ K = row.rationalPolynomial.natDegree :=
        adjoinRoot_finrank_eq_natDegree row.rationalPolynomial
      _ = row.polynomial.natDegree :=
        hdegree.monic.natDegree_map (Int.castRingHom ℚ)
      _ = d := hdegree.natDegree_eq
  let family : Fin d → RingOfIntegers K := fun column ↦
    ⟨certificate.element row column,
      certificate.element_isIntegral row hvalid column⟩
  apply fieldDiscriminant_eq_of_integralFamily_squarefree
    K d row.fieldDiscriminant hdegreeK family hsquarefree
  apply Rat.intCast_injective
  rw [discr_ringOfIntegers_cast]
  let pb : PowerBasis ℚ K := AdjoinRoot.powerBasis hirrQ.ne_zero
  have hpbdim : pb.dim = d := by
    change row.rationalPolynomial.natDegree = d
    exact (hdegree.monic.natDegree_map
      (Int.castRingHom ℚ)).trans hdegree.natDegree_eq
  let e : Fin pb.dim ≃ Fin d := finCongr hpbdim
  let b : Basis (Fin d) ℚ K := pb.basis.reindex e
  have hbasis (i : Fin d) :
      b i = AdjoinRoot.root row.rationalPolynomial ^ (i : ℕ) := by
    rw [show b i = pb.basis (e.symm i) by
      exact Basis.reindex_apply pb.basis e i]
    rw [pb.basis_eq_pow]
    congr 1
  have hfamilyCoe :
      (fun column ↦ ((family column : RingOfIntegers K) : K)) =
        Matrix.vecMul b
          (certificate.matrix.map (algebraMap ℚ K)) := by
    funext column
    change certificate.element row column = _
    rw [VoightIntegralBasisCertificate.element,
      VoightIntegralBasisCertificate.columnCoefficients,
      adjoinRoot_mk_dense_ofFn,
      Matrix.vecMul_apply_eq_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hbasis]
    simp [Matrix.map_apply, K, mul_comm]
  have hbdiscr : Algebra.discr ℚ b =
      (row.polynomial.discr : ℚ) := by
    calc
      Algebra.discr ℚ b = Algebra.discr ℚ pb.basis := by
        simpa [b] using Algebra.discr_reindex ℚ pb.basis e
      _ = (minpoly ℚ pb.gen).discr :=
        powerBasis_discr_eq_minpoly_discr pb
      _ = row.rationalPolynomial.discr := by
        have hqmonic : row.rationalPolynomial.Monic := by
          exact hdegree.monic.map (Int.castRingHom ℚ)
        rw [show minpoly ℚ pb.gen = row.rationalPolynomial by
          change minpoly ℚ
            (AdjoinRoot.root row.rationalPolynomial) =
              row.rationalPolynomial
          calc
            minpoly ℚ (AdjoinRoot.root row.rationalPolynomial) =
                row.rationalPolynomial *
                  C row.rationalPolynomial.leadingCoeff⁻¹ :=
              AdjoinRoot.minpoly_root hirrQ.ne_zero
            _ = row.rationalPolynomial := by
              rw [hqmonic.leadingCoeff]
              simp]
      _ = (row.polynomial.discr : ℚ) := by
        exact (intCast_discr_eq_discr_map row.polynomial
          hdegree.monic (hdegree.natDegree_eq ▸ hd)).symm
  have hrecordedQ : (row.polynomial.discr : ℚ) =
      (row.index : ℚ) ^ 2 * (row.fieldDiscriminant : ℚ) := by
    exact_mod_cast hrecorded
  calc
    Algebra.discr ℚ
        (fun column ↦ ((family column : RingOfIntegers K) : K)) =
      Algebra.discr ℚ
        (Matrix.vecMul b
          (certificate.matrix.map (algebraMap ℚ K))) := by
            rw [hfamilyCoe]
    _ = certificate.matrix.det ^ 2 * Algebra.discr ℚ b :=
      Algebra.discr_of_matrix_vecMul b certificate.matrix
    _ = certificate.matrix.det ^ 2 *
        (row.polynomial.discr : ℚ) := by rw [hbdiscr]
    _ = certificate.matrix.det ^ 2 *
        ((row.index : ℚ) ^ 2 *
          (row.fieldDiscriminant : ℚ)) := by rw [hrecordedQ]
    _ = (certificate.matrix.det ^ 2 *
          (row.index : ℚ) ^ 2) *
        (row.fieldDiscriminant : ℚ) := by ring
    _ = (row.fieldDiscriminant : ℚ) := by rw [hvalid.2, one_mul]

/-- The integral-basis certificate closes all exact number-field semantics
for one archived row. -/
theorem voightPolynomialRow_presentsExactTotallyRealNumberField_of_integralBasisCertificate
    (d : ℕ) (row : VoightPolynomialRow)
    (certificate : VoightIntegralBasisCertificate d)
    (hd : 0 < d)
    (hdegree : row.polynomial.IsMonicOfDegree d)
    (hirr : Irreducible row.polynomial)
    (hsplits : row.realPolynomial.Splits)
    (hsquarefree : Squarefree row.fieldDiscriminant)
    (hrecorded : row.polynomial.discr =
      (row.index : ℤ) ^ 2 * (row.fieldDiscriminant : ℤ))
    (hvalid : certificate.Valid row) :
    row.PresentsExactTotallyRealNumberField := by
  have hfull :=
    voightPolynomialRow_presentsTotallyRealNumberField row
      hdegree.monic hirr hsplits
  rcases hfull with ⟨hirrQ, hreal, hfieldDegree⟩
  refine ⟨hirrQ, ?_⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  change NumberField.IsTotallyReal
      (AdjoinRoot row.rationalPolynomial) ∧
    Module.finrank ℚ (AdjoinRoot row.rationalPolynomial) =
      row.polynomial.natDegree ∧
    NumberField.discr (AdjoinRoot row.rationalPolynomial) =
      (row.fieldDiscriminant : ℤ)
  exact ⟨hreal, hfieldDegree,
    voight_fieldDiscriminant_eq_of_integralBasisCertificate
      d row certificate hd hdegree hsquarefree
        hrecorded hvalid⟩

end

end TraceEuclidean
