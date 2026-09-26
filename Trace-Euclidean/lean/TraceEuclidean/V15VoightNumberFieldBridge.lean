import TraceEuclidean.V15VoightPolynomialBridge
import TraceEuclidean.V15VoightTotalRealityCertificates
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Number fields presented by the archived Voight polynomials

The archived tables supply integral defining polynomials.  Earlier modules
prove that all 2,773 polynomials are irreducible and split over the reals.
This module converts those polynomial statements into actual totally real
number fields of the expected degree.
-/

namespace TraceEuclidean

open Polynomial

noncomputable section

/-- If an irreducible rational polynomial splits after extension to the
reals, its `AdjoinRoot` number field is totally real. -/
theorem adjoinRoot_isTotallyReal_of_splits_over_real
    (q : ℚ[X]) [Fact (Irreducible q)]
    (hsplits : (q.map (algebraMap ℚ ℝ)).Splits) :
    NumberField.IsTotallyReal (AdjoinRoot q) := by
  rw [NumberField.isTotallyReal_iff]
  intro v
  rw [NumberField.InfinitePlace.isReal_iff,
    NumberField.ComplexEmbedding.isReal_iff]
  apply AdjoinRoot.ringHom_ext
  · exact RingHom.ext_rat _ _
  · let φ := v.embedding
    let z := φ (AdjoinRoot.root q)
    have hroot : (q.map (algebraMap ℚ ℂ)).IsRoot z := by
      have h := Polynomial.IsRoot.map (f := φ) (AdjoinRoot.isRoot_root q)
      simpa only [map_zero, Polynomial.map_map, z, φ,
        show φ.comp (AdjoinRoot.of q) = algebraMap ℚ ℂ from RingHom.ext_rat _ _] using h
    have hroot' :
        ((q.map (algebraMap ℚ ℝ)).map Complex.ofRealHom).IsRoot z := by
      rw [Polynomial.map_map,
        show Complex.ofRealHom.comp (algebraMap ℚ ℝ) = algebraMap ℚ ℂ from
          RingHom.ext_rat _ _]
      exact hroot
    have hz : z ∈ Complex.ofRealHom.range :=
      hsplits.mem_range_of_isRoot
        (Polynomial.map_ne_zero (Fact.out : Irreducible q).ne_zero) hroot'
    obtain ⟨r, hr⟩ := hz
    change star z = z
    rw [← hr]
    exact Complex.conj_ofReal r

/-- The rational defining polynomial attached to an archived Voight row. -/
def V15VoightPolynomialRow.rationalPolynomial
    (row : V15VoightPolynomialRow) : ℚ[X] :=
  row.polynomial.map (Int.castRingHom ℚ)

/-- Extending the rational defining polynomial to the reals gives the real
polynomial used by the root-isolation certificates. -/
theorem v15_rationalPolynomial_map_real
    (row : V15VoightPolynomialRow) :
    row.rationalPolynomial.map (algebraMap ℚ ℝ) = row.realPolynomial := by
  rw [V15VoightPolynomialRow.rationalPolynomial,
    V15VoightPolynomialRow.realPolynomial, Polynomial.map_map]
  congr 1

/-- A row presents a totally real number field when its rational polynomial
is irreducible, its `AdjoinRoot` field is totally real, and the field degree
equals the degree of the archived integral polynomial. -/
def V15VoightPolynomialRow.PresentsTotallyRealNumberField
    (row : V15VoightPolynomialRow) : Prop :=
  ∃ h : Irreducible row.rationalPolynomial,
    letI : Fact (Irreducible row.rationalPolynomial) := ⟨h⟩
    NumberField.IsTotallyReal (AdjoinRoot row.rationalPolynomial) ∧
      Module.finrank ℚ (AdjoinRoot row.rationalPolynomial) =
        row.polynomial.natDegree

/-- The degree of an irreducible `AdjoinRoot` field is the degree of its
defining polynomial. -/
theorem v15_adjoinRoot_finrank_eq_natDegree
    (q : ℚ[X]) [Fact (Irreducible q)] :
    Module.finrank ℚ (AdjoinRoot q) = q.natDegree := by
  calc
    Module.finrank ℚ (AdjoinRoot q) =
        (AdjoinRoot.powerBasis (Fact.out : Irreducible q).ne_zero).dim :=
      PowerBasis.finrank _
    _ = q.natDegree :=
      AdjoinRoot.powerBasis_dim (Fact.out : Irreducible q).ne_zero

/-- Monicity, integral irreducibility, and real splitting turn one archived
row into a totally real number-field presentation of the same degree. -/
theorem v15_voightPolynomialRow_presentsTotallyRealNumberField
    (row : V15VoightPolynomialRow)
    (hmonic : row.polynomial.Monic)
    (hirr : Irreducible row.polynomial)
    (hsplits : row.realPolynomial.Splits) :
    row.PresentsTotallyRealNumberField := by
  have hirrQ : Irreducible row.rationalPolynomial := by
    rw [V15VoightPolynomialRow.rationalPolynomial]
    exact hmonic.irreducible_iff_irreducible_map_fraction_map.mp hirr
  refine ⟨hirrQ, ?_⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  constructor
  · apply adjoinRoot_isTotallyReal_of_splits_over_real
    rwa [v15_rationalPolynomial_map_real]
  · rw [v15_adjoinRoot_finrank_eq_natDegree]
    exact hmonic.natDegree_map (Int.castRingHom ℚ)

/-- Every row in one archived degree table has a monic defining
polynomial. -/
theorem v15_voightPolynomialRows_monic (degree : ℕ) :
    ∀ row ∈ v15VoightPolynomialRows degree, row.polynomial.Monic := by
  intro row hrow
  have hvalid :=
    (List.all_eq_true.mp
      (v15_voightPolynomialRows_structural_certificate degree)) row hrow
  have hconditions :=
    (v15_voightPolynomialRow_structurallyValid_iff degree row).1 hvalid
  exact (v15VoightPolynomial_isMonicOfDegree degree row
    hconditions.1 hconditions.2.1).monic

/-- All archived degree 5 through 10 defining polynomials are monic. -/
theorem v15_allVoightPolynomialRows_monic :
    ∀ row ∈ v15AllVoightPolynomialRows, row.polynomial.Monic := by
  dsimp [v15AllVoightPolynomialRows]
  exact v15_forall_mem_append
    (v15_voightPolynomialRows_monic 5)
    (v15_forall_mem_append
      (v15_voightPolynomialRows_monic 6)
      (v15_forall_mem_append
        (v15_voightPolynomialRows_monic 7)
        (v15_forall_mem_append
          (v15_voightPolynomialRows_monic 8)
          (v15_forall_mem_append
            (v15_voightPolynomialRows_monic 9)
            (v15_voightPolynomialRows_monic 10)))))

/-- Every archived degree 5 through 10 row presents an actual totally real
number field whose degree is the defining-polynomial degree. -/
theorem v15_allVoightPolynomialRows_present_totallyRealNumberField :
    ∀ row ∈ v15AllVoightPolynomialRows,
      row.PresentsTotallyRealNumberField := by
  intro row hrow
  exact v15_voightPolynomialRow_presentsTotallyRealNumberField row
    (v15_allVoightPolynomialRows_monic row hrow)
    (v15_allVoightPolynomialRows_irreducible row hrow)
    (v15_allVoightPolynomialRows_splits row hrow)

end

end TraceEuclidean
