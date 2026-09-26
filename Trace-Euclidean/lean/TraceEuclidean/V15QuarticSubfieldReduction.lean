import TraceEuclidean.V15DegreeFourMinkowskiReduction
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Quartic subfield reduction

The unconditional Minkowski argument already supplies a projected vector of
spread below `35`.  Such a vector is automatically a primitive field
generator when the quartic field has no proper intermediate field.  This
module proves that statement and isolates the remaining imprimitive case as a
pure number-field input.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Module
open scoped NumberField

/-- The remaining imprimitive-field statement for the degree-four
discriminant bound: a totally real quartic field of discriminant below `725`
has no proper intermediate field. -/
def V15QuarticSmallDiscriminantNoProperSubfieldInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    Module.finrank ℚ K.1 = 4 → |K.discriminant| < 725 →
    ∀ E : IntermediateField ℚ K.1, E = ⊥ ∨ E = ⊤

/-- Source-facing form of the remaining imprimitive quartic result.  It asks
for the discriminant lower bound only when the quartic field actually has a
proper intermediate field. -/
def V15ImprimitiveTotallyRealQuarticMinimumInput : Prop :=
  ∀ (K : CodedNumberField), NumberField.IsTotallyReal K.1 →
    Module.finrank ℚ K.1 = 4 →
    (∃ E : IntermediateField ℚ K.1, E ≠ ⊥ ∧ E ≠ ⊤) →
    725 ≤ |K.discriminant|

/-- The source-facing imprimitive minimum immediately excludes every proper
subfield under the strict small-discriminant hypothesis. -/
theorem v15_quartic_noProperSubfield_of_imprimitiveMinimum
    (hMinimum : V15ImprimitiveTotallyRealQuarticMinimumInput) :
    V15QuarticSmallDiscriminantNoProperSubfieldInput := by
  intro K hreal hdegree hdisc E
  by_cases hbot : E = ⊥
  · exact Or.inl hbot
  by_cases htop : E = ⊤
  · exact Or.inr htop
  have hlower := hMinimum K hreal hdegree ⟨E, hbot, htop⟩
  omega

/-- Every proper intermediate field of a quartic number field is quadratic,
and the quartic field is quadratic over it. -/
theorem v15_quartic_properIntermediateField_finranks
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (E : IntermediateField ℚ K) (hbot : E ≠ ⊥) (htop : E ≠ ⊤) :
    Module.finrank ℚ E = 2 ∧ Module.finrank E K = 2 := by
  have hmul := Module.finrank_mul_finrank ℚ E K
  rw [hdegree] at hmul
  have hleft : Module.finrank ℚ E ≠ 1 := by
    intro h
    exact hbot (IntermediateField.finrank_eq_one_iff.mp h)
  have hright : Module.finrank E K ≠ 1 := by
    intro h
    exact htop (IntermediateField.finrank_eq_one_iff_eq_top.mp h)
  have hleftPos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hrightPos : 0 < Module.finrank E K := Module.finrank_pos
  have hleftLe : Module.finrank ℚ E ≤ 4 :=
    Nat.le_of_dvd (by norm_num)
      ⟨Module.finrank E K, hmul.symm⟩
  interval_cases hleftEq : Module.finrank ℚ E
  all_goals omega

/-- Exact discriminant tower formula for a proper intermediate field of a
quartic number field.  The relative factor is the absolute norm of the
different ideal. -/
theorem v15_quartic_discriminant_tower_of_properIntermediateField
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (E : IntermediateField ℚ K) (hbot : E ≠ ⊥) (htop : E ≠ ⊤) :
    (NumberField.discr K).natAbs =
      Ideal.absNorm (differentIdeal (𝓞 E) (𝓞 K)) *
        (NumberField.discr E).natAbs ^ 2 := by
  have hfin : Module.finrank E K = 2 :=
    (v15_quartic_properIntermediateField_finranks
      K hdegree E hbot htop).2
  have h :=
    NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
      E (𝓞 E) K (𝓞 K)
  simpa [hfin] using h

/-- In particular, the square of the quadratic-subfield discriminant divides
the quartic discriminant. -/
theorem v15_quartic_subfield_discriminant_sq_dvd
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (E : IntermediateField ℚ K) (hbot : E ≠ ⊥) (htop : E ≠ ⊤) :
    (NumberField.discr E).natAbs ^ 2 ∣
      (NumberField.discr K).natAbs := by
  refine ⟨Ideal.absNorm (differentIdeal (𝓞 E) (𝓞 K)), ?_⟩
  rw [v15_quartic_discriminant_tower_of_properIntermediateField
    K hdegree E hbot htop]
  exact (Nat.mul_comm _ _).symm

/-- The same tower formula gives the numerical lower bound furnished solely
by the quadratic subfield. -/
theorem v15_quartic_subfield_discriminant_sq_le
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (E : IntermediateField ℚ K) (hbot : E ≠ ⊥) (htop : E ≠ ⊤) :
    (NumberField.discr E).natAbs ^ 2 ≤
      (NumberField.discr K).natAbs := by
  exact Nat.le_of_dvd
    (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K))
    (v15_quartic_subfield_discriminant_sq_dvd
      K hdegree E hbot htop)

/-- Two distinct quadratic subfields with coprime discriminants generate the
quartic field, and the compositum discriminant is the product of the two
squared quadratic discriminants. -/
theorem v15_quartic_discriminant_eq_product_of_coprime_quadratic_subfields
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (E F : IntermediateField ℚ K)
    (hdegreeE : Module.finrank ℚ E = 2)
    (hdegreeF : Module.finrank ℚ F = 2)
    (hne : E ≠ F)
    (hcoprime : IsCoprime (NumberField.discr E)
      (NumberField.discr F)) :
    (NumberField.discr K).natAbs =
      (NumberField.discr E).natAbs ^ 2 *
        (NumberField.discr F).natAbs ^ 2 := by
  letI : Algebra.IsQuadraticExtension ℚ E := ⟨hdegreeE⟩
  have hlinear : E.LinearDisjoint F :=
    NumberField.linearDisjoint_of_isGalois_isCoprime_discr K E F hcoprime
  have hsup : E ⊔ F = ⊤ := by
    by_contra hnot
    have hEbot : E ≠ ⊥ := by
      intro hbot
      rw [hbot, IntermediateField.finrank_bot] at hdegreeE
      omega
    have hsupBot : E ⊔ F ≠ ⊥ := by
      intro hbot
      apply hEbot
      exact le_bot_iff.mp (hbot ▸ le_sup_left)
    have hdegreeSup : Module.finrank ℚ ↥(E ⊔ F) = 2 :=
      (v15_quartic_properIntermediateField_finranks
        K hdegree (E ⊔ F) hsupBot hnot).1
    have hEeq : E = E ⊔ F :=
      IntermediateField.eq_of_le_of_finrank_eq le_sup_left
        (hdegreeE.trans hdegreeSup.symm)
    have hFleE : F ≤ E := by
      rw [hEeq]
      exact le_sup_right
    have hFE : F = E :=
      IntermediateField.eq_of_le_of_finrank_eq hFleE
        (hdegreeF.trans hdegreeE.symm)
    exact hne hFE.symm
  have hdifferent :=
    NumberField.isCoprime_differentIdeal_of_isCoprime_discr K hcoprime
  simpa [hdegreeE, hdegreeF] using
    NumberField.natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow
      K E F hlinear hsup hdifferent

/-- Below the target quartic discriminant, every proper quadratic subfield
has absolute discriminant at most `26`.  Thus the remaining relative-different
analysis starts from a genuinely finite quadratic range. -/
theorem v15_quartic_properSubfield_natAbs_discr_le_twentySix
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (hdisc : |NumberField.discr K| < 725)
    (E : IntermediateField ℚ K) (hbot : E ≠ ⊥) (htop : E ≠ ⊤) :
    (NumberField.discr E).natAbs ≤ 26 := by
  have hdiscNat : (NumberField.discr K).natAbs < 725 := by
    rw [← Nat.cast_lt (α := ℤ), Int.natCast_natAbs]
    exact hdisc
  have hsquare := v15_quartic_subfield_discriminant_sq_le
    K hdegree E hbot htop
  by_contra hnot
  have htwentySeven : 27 ≤ (NumberField.discr E).natAbs := by omega
  have hpow : 27 ^ 2 ≤ (NumberField.discr E).natAbs ^ 2 :=
    Nat.pow_le_pow_left htwentySeven 2
  norm_num at hpow
  omega

open scoped Classical in
/-- In a field with no proper intermediate field, every nonzero projected
Hunter vector has a lift that generates the field. -/
theorem v15_quarticHunterAlgebraicIntegerLift_adjoin_eq_top_of_noProperSubfield
    (K : Type*) [Field K] [NumberField K]
    (bz : Basis (Fin 4) ℤ
      (NumberField.mixedEmbedding.euclidean.integerLattice K))
    (hbzero :
      (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
        NumberField.mixedEmbedding.euclidean.mixedSpace K)) =
          v15EuclideanOne K)
    (hNoProper :
      ∀ E : IntermediateField ℚ K, E = ⊥ ∨ E = ⊤)
    (x : v15QuarticHunterProjectedLattice (bz.ofZLatticeBasis ℝ))
    (hx : x ≠ 0) :
    IntermediateField.adjoin ℚ
      {((v15QuarticHunterAlgebraicIntegerLift K bz x : 𝓞 K) : K)} = ⊤ := by
  let a : K :=
    ((v15QuarticHunterAlgebraicIntegerLift K bz x : 𝓞 K) : K)
  have hnotRat : ¬ ∃ q : ℚ, a = algebraMap ℚ K q := by
    simpa [a] using
      v15_quarticHunterAlgebraicIntegerLift_not_rat K bz hbzero x hx
  let E : IntermediateField ℚ K := IntermediateField.adjoin ℚ {a}
  rcases hNoProper E with hbot | htop
  · have haE : a ∈ E := by
      exact IntermediateField.subset_adjoin ℚ {a} (Set.mem_singleton a)
    rw [hbot, IntermediateField.mem_bot] at haE
    rcases haE with ⟨q, hq⟩
    exact (hnotRat ⟨q, hq.symm⟩).elim
  · exact htop

/-- The imprimitive-field input implies the precise spread-`35` selection
statement used by the unconditional quartic Minkowski route. -/
theorem v15_quartic_primitiveShortSelectionThirtyFive_of_noProperSubfield
    (hNoProper : V15QuarticSmallDiscriminantNoProperSubfieldInput) :
    V15QuarticPrimitiveShortSelectionThirtyFiveInput := by
  intro K hreal hdegree hdisc bz hbzero hshort
  obtain ⟨x, hx, hxshort⟩ := hshort
  refine ⟨x, hx, ?_, hxshort⟩
  exact
    v15_quarticHunterAlgebraicIntegerLift_adjoin_eq_top_of_noProperSubfield
      K.1 bz hbzero (hNoProper K hreal hdegree hdisc) x hx

/-- It now suffices to exclude proper quadratic subfields below discriminant
`725`; all primitive quartic fields are handled by the kernel-checked
Minkowski and finite-enumeration argument. -/
theorem v15_coded_degree_four_discriminant_ge_725_of_noProperSubfield
    (hNoProper : V15QuarticSmallDiscriminantNoProperSubfieldInput)
    (K : CodedNumberField) (hreal : NumberField.IsTotallyReal K.1)
    (hdegree : Module.finrank ℚ K.1 = 4) :
    725 ≤ |K.discriminant| := by
  exact v15_coded_degree_four_discriminant_ge_725_of_minkowski_selection
    (v15_quartic_primitiveShortSelectionThirtyFive_of_noProperSubfield
      hNoProper)
    K hreal hdegree

/-- Combining the imprimitive minimum with the internal primitive-field
enumeration proves the full degree-four discriminant bound. -/
theorem v15_coded_degree_four_discriminant_ge_725_of_imprimitiveMinimum
    (hMinimum : V15ImprimitiveTotallyRealQuarticMinimumInput)
    (K : CodedNumberField) (hreal : NumberField.IsTotallyReal K.1)
    (hdegree : Module.finrank ℚ K.1 = 4) :
    725 ≤ |K.discriminant| := by
  exact v15_coded_degree_four_discriminant_ge_725_of_noProperSubfield
    (v15_quartic_noProperSubfield_of_imprimitiveMinimum hMinimum)
    K hreal hdegree

end

end TraceEuclidean
