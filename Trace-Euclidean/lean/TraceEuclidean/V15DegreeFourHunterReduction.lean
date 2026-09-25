import TraceEuclidean.V15QuarticHermite
import TraceEuclidean.V15PrimitiveBasis

/-!
# Reduction of the quartic Hunter certificate to a primitive short generator

The finite quartic enumeration no longer needs to assume irreducibility, an
index-discriminant identity, or positivity of the third Hermite minor. This
module derives those parts from an actual primitive algebraic integer. The
remaining input is confined to constructing a primitive quartic Hunter
generator with the stated normalized coefficient and strict upper-spread
bounds.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Module Polynomial
open scoped NumberField

/-- A quartic ring of integers admits an integral basis indexed by `Fin 4`. -/
theorem v15_exists_ringOfIntegers_basis_fin_four
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4) :
    Nonempty (Basis (Fin 4) ℤ (𝓞 K)) := by
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin 4 :=
    Fintype.equivOfCardEq (by
      rw [← Module.finrank_eq_card_basis
        (NumberField.RingOfIntegers.basis K)]
      exact (NumberField.RingOfIntegers.rank K).trans hdegree)
  exact ⟨(NumberField.RingOfIntegers.basis K).reindex e⟩

/-- The residual mathematical content of the quartic Hunter step. It asks
for an actual primitive integral generator satisfying the normalized
coefficient and strict upper-spread bounds. -/
def V15DegreeFourPrimitiveGeneratorInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    Module.finrank ℚ K.1 = 4 →
      |K.discriminant| < 725 →
      ∃ a : 𝓞 K.1,
        IntermediateField.adjoin ℚ {((a : 𝓞 K.1) : K.1)} = ⊤ ∧
        (v15QuarticS1 K.1 a = 0 ∨ v15QuarticS1 K.1 a = 1 ∨
          v15QuarticS1 K.1 a = 2) ∧
        -24 ≤ v15QuarticS3 K.1 a ∧
        v15QuarticS3 K.1 a ≤ 24 ∧
        -4 ≤ v15QuarticS4 K.1 a ∧
        v15QuarticS4 K.1 a ≤ 4 ∧
        v15QuarticSpread (v15QuarticS1 K.1 a)
          (v15QuarticS2 K.1 a) < 29

/-- An actual primitive generator with the residual Hunter bounds supplies
the complete normalized certificate required by the finite quartic
enumeration. Irreducibility, the positive polynomial discriminant, and the
positive index relation are derived internally. -/
theorem v15_degree_four_hunterCertificate_of_primitiveGenerator
    (hGenerator : V15DegreeFourPrimitiveGeneratorInput) :
    V15DegreeFourHunterCertificateInput := by
  intro K hreal hdegree hdisc
  rcases hGenerator K hreal hdegree hdisc with
    ⟨a, hgen, hs1, hs3, hs3', hs4, hs4',
      hspreadLt⟩
  have hspreadPos :=
    v15_quarticSpread_pos K.1 hreal hdegree a hgen
  have hminor :=
    v15_quarticHermiteMinorThree_pos K.1 hreal hdegree a hgen
  obtain ⟨bO⟩ := v15_exists_ringOfIntegers_basis_fin_four K.1 hdegree
  obtain ⟨index, hindex, hrelation⟩ :=
    v15_quartic_exists_positive_index K.1 hdegree a hgen bO
  have hnoRoot :=
    v15_quartic_minpoly_no_integer_root K.1 hdegree a hgen
  have hnoQuadratic :=
    v15_quartic_minpoly_no_quadratic_factor K.1 hdegree a hgen
  letI : NumberField.IsTotallyReal K.1 := hreal
  have hsign : K.discriminant.sign = 1 := by
    rw [NumberFieldCode.discriminant, NumberField.sign_discr,
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero]
    norm_num
  have hfieldPos : 0 < K.discriminant :=
    Int.sign_eq_one_iff_pos.mp hsign
  have hindexInt : (0 : ℤ) < index := by exact_mod_cast hindex
  have hsquare : (0 : ℤ) < (index : ℤ) ^ 2 := sq_pos_of_pos hindexInt
  have hrelation' :
      v15QuarticDiscriminant (v15QuarticS1 K.1 a)
          (v15QuarticS2 K.1 a) (v15QuarticS3 K.1 a)
          (v15QuarticS4 K.1 a) =
        (index : ℤ) ^ 2 * K.discriminant := by
    simpa only [NumberFieldCode.discriminant] using hrelation
  have hdiscPos :
      0 < v15QuarticDiscriminant (v15QuarticS1 K.1 a)
        (v15QuarticS2 K.1 a) (v15QuarticS3 K.1 a)
        (v15QuarticS4 K.1 a) := by
    rw [hrelation']
    exact mul_pos hsquare hfieldPos
  exact ⟨v15QuarticS1 K.1 a, v15QuarticS2 K.1 a,
    v15QuarticS3 K.1 a, v15QuarticS4 K.1 a, index,
    hs1, hs3, hs3', hs4, hs4', hspreadPos, hspreadLt,
    hminor, hdiscPos, hnoRoot, hnoQuadratic, hindex, hrelation'⟩

end

end TraceEuclidean
