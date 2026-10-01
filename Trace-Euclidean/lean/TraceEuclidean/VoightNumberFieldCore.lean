import TraceEuclidean.RealRootIntervalCertificate
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Number-field semantics for one certified polynomial row

This module contains only the generic bridge from one irreducible real-split
polynomial to its totally real `AdjoinRoot` field.  It deliberately avoids
the aggregate archived Voight certificate modules, so a new kernel-replayed
row can use the bridge without inheriting their native-evaluation boundary.
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

/-- The rational defining polynomial attached to a certified row. -/
def VoightPolynomialRow.rationalPolynomial
    (row : VoightPolynomialRow) : ℚ[X] :=
  row.polynomial.map (Int.castRingHom ℚ)

/-- Extending the rational defining polynomial to the reals gives the real
polynomial used by the root-isolation certificates. -/
theorem rationalPolynomial_map_real
    (row : VoightPolynomialRow) :
    row.rationalPolynomial.map (algebraMap ℚ ℝ) = row.realPolynomial := by
  rw [VoightPolynomialRow.rationalPolynomial,
    VoightPolynomialRow.realPolynomial, Polynomial.map_map]
  congr 1

/-- A row presents a totally real number field when its rational polynomial
is irreducible, its `AdjoinRoot` field is totally real, and the field degree
equals the degree of the integral polynomial. -/
def VoightPolynomialRow.PresentsTotallyRealNumberField
    (row : VoightPolynomialRow) : Prop :=
  ∃ h : Irreducible row.rationalPolynomial,
    letI : Fact (Irreducible row.rationalPolynomial) := ⟨h⟩
    NumberField.IsTotallyReal (AdjoinRoot row.rationalPolynomial) ∧
      Module.finrank ℚ (AdjoinRoot row.rationalPolynomial) =
        row.polynomial.natDegree

/-- The degree of an irreducible `AdjoinRoot` field is the degree of its
defining polynomial. -/
theorem adjoinRoot_finrank_eq_natDegree
    (q : ℚ[X]) [Fact (Irreducible q)] :
    Module.finrank ℚ (AdjoinRoot q) = q.natDegree := by
  calc
    Module.finrank ℚ (AdjoinRoot q) =
        (AdjoinRoot.powerBasis (Fact.out : Irreducible q).ne_zero).dim :=
      PowerBasis.finrank _
    _ = q.natDegree :=
      AdjoinRoot.powerBasis_dim (Fact.out : Irreducible q).ne_zero

/-- Monicity, integral irreducibility, and real splitting turn one certified
row into a totally real number-field presentation of the same degree. -/
theorem voightPolynomialRow_presentsTotallyRealNumberField
    (row : VoightPolynomialRow)
    (hmonic : row.polynomial.Monic)
    (hirr : Irreducible row.polynomial)
    (hsplits : row.realPolynomial.Splits) :
    row.PresentsTotallyRealNumberField := by
  have hirrQ : Irreducible row.rationalPolynomial := by
    rw [VoightPolynomialRow.rationalPolynomial]
    exact hmonic.irreducible_iff_irreducible_map_fraction_map.mp hirr
  refine ⟨hirrQ, ?_⟩
  letI : Fact (Irreducible row.rationalPolynomial) := ⟨hirrQ⟩
  constructor
  · apply adjoinRoot_isTotallyReal_of_splits_over_real
    rwa [rationalPolynomial_map_real]
  · rw [adjoinRoot_finrank_eq_natDegree]
    exact hmonic.natDegree_map (Int.castRingHom ℚ)

end

end TraceEuclidean
