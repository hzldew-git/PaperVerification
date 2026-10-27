import NormEuclidean.Reuse.Bong.Lattice.NumberFieldHasseRepresentationInduction
import NormEuclidean.Reuse.Bong.QuadraticSpace.FieldHyperbolicEmbedding
import NormEuclidean.Reuse.Bong.QuadraticSpace.FieldCodimensionOneDeterminant

namespace Bong.HeADCV5.Global

open scoped NumberField TensorProduct

namespace NumberFieldLattice

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- A regular quadratic space is isotropic when it has a nonzero vector of
quadratic value zero. -/
def IsIsotropicSpace {F V : Type u} [Field F]
    [AddCommGroup V] [Module F V] (q : Bong.QuadraticSpace F V) : Prop :=
  ∃ x : V, x ≠ 0 ∧ q.quadratic x = 0

theorem isIsotropicSpace_map
    {F V W : Type u} [Field F]
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    {q : Bong.QuadraticSpace F V} {r : Bong.QuadraticSpace F W}
    (f : Bong.QuadraticSpace.Isometry q r)
    (h : IsIsotropicSpace q) : IsIsotropicSpace r := by
  rcases h with ⟨x, hx, hqx⟩
  refine ⟨f.toLinearEquiv x, by
    simpa using f.toLinearEquiv.injective.ne hx, ?_⟩
  rw [f.map_quadratic, hqx]

private theorem representsScaledLineOfValue
    {F V : Type u} [Field F]
    [AddCommGroup V] [Module F V]
    (q : Bong.QuadraticSpace F V) (a : Fˣ) (x : V)
    (hx : q.quadratic x = (a : F)) :
    q.Represents (Bong.QuadraticSpace.scaledLine a) := by
  have hxne : x ≠ 0 := by
    intro hzero
    have : (a : F) = 0 := by
      rw [← hx, hzero]
      exact q.quadratic_zero
    exact Units.ne_zero a this
  refine ⟨{
    toLinearMap :=
      { toFun := fun c : F ↦ c • x
        map_add' := fun c d ↦ add_smul c d x
        map_smul' := fun c d ↦ by simp [mul_smul] }
    injective := ?_
    map_bilin := ?_ }⟩
  · intro c d hcd
    change c • x = d • x at hcd
    have hzero : (c - d) • x = 0 := by
      rw [sub_smul, hcd, sub_self]
    have : c - d = 0 := by
      simpa [hxne] using hzero
    exact sub_eq_zero.mp this
  · intro c d
    simp only [LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right,
      Bong.QuadraticSpace.scaledLine_bilin_apply]
    change d * (c * q.quadratic x) = (a : F) * c * d
    rw [hx]
    ring

private theorem representsScaledLineOfIsotropic
    {F V : Type u} [Field F] [CharZero F]
    [AddCommGroup V] [Module F V]
    (q : Bong.QuadraticSpace F V) (a : Fˣ)
    (h : IsIsotropicSpace q) :
    q.Represents (Bong.QuadraticSpace.scaledLine a) := by
  rcases h with ⟨x, hx, hqx⟩
  have hHyp := Bong.QuadraticSpace.represents_hyperbolicPlane_one_of_isotropic
    q x hx hqx
  let y : Fin 2 → F := ![1, (a : F) / 2]
  have hy : (Bong.QuadraticSpace.hyperbolicPlane (1 : Fˣ)).quadratic y =
      (a : F) := by
    simp [y, Bong.QuadraticSpace.hyperbolicPlane_quadratic_apply]
    field_simp
  exact hHyp.trans
    (representsScaledLineOfValue
      (Bong.QuadraticSpace.hyperbolicPlane (1 : Fˣ)) a y hy)

private theorem representsScaledLine_iff_negLine_sum_isotropic
    {F V : Type u} [Field F] [CharZero F]
    [AddCommGroup V] [Module F V]
    (q : Bong.QuadraticSpace F V) (a : Fˣ) :
    q.Represents (Bong.QuadraticSpace.scaledLine a) ↔
      IsIsotropicSpace
        ((Bong.QuadraticSpace.scaledLine (-a)).orthogonalSum q) := by
  constructor
  · rintro ⟨f⟩
    let z : F × V := (1, f.toLinearMap 1)
    refine ⟨z, ?_, ?_⟩
    · intro hz
      have := congrArg Prod.fst hz
      simp [z] at this
    · simp only [z, Bong.QuadraticSpace.orthogonalSum_quadratic_apply,
        Bong.QuadraticSpace.scaledLine_quadratic_apply,
        f.map_quadratic]
      simp
  · rintro ⟨⟨t, x⟩, hne, hzero⟩
    by_cases ht : t = 0
    · have hx : x ≠ 0 := by
        intro hx
        apply hne
        exact Prod.ext ht hx
      have hqx : q.quadratic x = 0 := by
        simpa [ht] using hzero
      exact representsScaledLineOfIsotropic q a ⟨x, hx, hqx⟩
    · have hqx : q.quadratic x = (a : F) * t ^ 2 := by
        have hz := hzero
        simp only [Bong.QuadraticSpace.orthogonalSum_quadratic_apply,
          Bong.QuadraticSpace.scaledLine_quadratic_apply] at hz
        simpa using (eq_neg_of_add_eq_zero_left hz).symm
      let y : V := t⁻¹ • x
      have hqy : q.quadratic y = (a : F) := by
        change q.quadratic (t⁻¹ • x) = (a : F)
        rw [q.quadratic_smul, hqx]
        field_simp
      exact representsScaledLineOfValue q a y hqy

/-- O'Meara 66:1 in the exact all-place form needed by the proof of 66:3. -/
def HasAllPlaceHasseIsotropy (K : Type u) [Field K] [NumberField K] : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (q : Bong.QuadraticSpace K V),
    (∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      IsIsotropicSpace (q.scalarExtension (E := p.adicCompletion K))) →
    (∀ p : NumberField.InfinitePlace K,
      IsIsotropicSpace (q.scalarExtension (E := p.Completion))) →
    IsIsotropicSpace q

private theorem scalarExtension_negLineSum_isometric
    {E V : Type u} [Field E] [CharZero E] [Algebra K E]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (q : Bong.QuadraticSpace K V) (a : Kˣ) :
    ((Bong.QuadraticSpace.scaledLine (-a)).orthogonalSum q).scalarExtension
        (E := E) |>.IsIsometric
      ((Bong.QuadraticSpace.scaledLine
          (-Units.map (algebraMap K E).toMonoidHom a)).orthogonalSum
        (q.scalarExtension (E := E))) := by
  let sumIso := Bong.QuadraticSpace.scalarExtensionOrthogonalSumIsometry
    (E := E) (Bong.QuadraticSpace.scaledLine (-a)) q
  let lineIso := Bong.QuadraticSpace.scalarExtensionScaledLineIsometry
    (E := E) (-a)
  have hneg : Units.map (algebraMap K E).toMonoidHom (-a) =
      -Units.map (algebraMap K E).toMonoidHom a := by
    ext
    simp
  rw [hneg] at lineIso
  exact ⟨sumIso.trans <|
    lineIso.fieldOrthogonalSum
      (Bong.QuadraticSpace.Isometry.refl (q.scalarExtension (E := E)))⟩

private theorem scaledLineHasse_of_hasseIsotropy
    (hiso : HasAllPlaceHasseIsotropy K)
    {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (q : Bong.QuadraticSpace K V) (a : Kˣ)
    (hFinite : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (q.scalarExtension (E := p.adicCompletion K)).Represents
        ((Bong.QuadraticSpace.scaledLine a).scalarExtension
          (E := p.adicCompletion K)))
    (hInfinite : ∀ p : NumberField.InfinitePlace K,
      (q.scalarExtension (E := p.Completion)).Represents
        ((Bong.QuadraticSpace.scaledLine a).scalarExtension
          (E := p.Completion))) :
    q.Represents (Bong.QuadraticSpace.scaledLine a) := by
  let augmented :=
    (Bong.QuadraticSpace.scaledLine (-a)).orthogonalSum q
  have hAugFinite : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      IsIsotropicSpace (augmented.scalarExtension
        (E := p.adicCompletion K)) := by
    intro p
    letI : CharZero (p.adicCompletion K) :=
      Algebra.charZero_of_charZero K (p.adicCompletion K)
    let aE := Units.map
      (algebraMap K (p.adicCompletion K)).toMonoidHom a
    have hline : (q.scalarExtension
        (E := p.adicCompletion K)).Represents
        (Bong.QuadraticSpace.scaledLine aE) := by
      rcases hFinite p with ⟨f⟩
      exact ⟨f.trans
        (Bong.QuadraticSpace.scalarExtensionScaledLineIsometry
          (E := p.adicCompletion K) a).symm.toRepresentation⟩
    have hnormalized :=
      (representsScaledLine_iff_negLine_sum_isotropic
        (q.scalarExtension (E := p.adicCompletion K)) aE).mp hline
    exact isIsotropicSpace_map
      (Classical.choice (scalarExtension_negLineSum_isometric q a)).symm
      hnormalized
  have hAugInfinite : ∀ p : NumberField.InfinitePlace K,
      IsIsotropicSpace (augmented.scalarExtension
        (E := p.Completion)) := by
    intro p
    letI : CharZero p.Completion :=
      Algebra.charZero_of_charZero K p.Completion
    let aE := Units.map (algebraMap K p.Completion).toMonoidHom a
    have hline : (q.scalarExtension (E := p.Completion)).Represents
        (Bong.QuadraticSpace.scaledLine aE) := by
      rcases hInfinite p with ⟨f⟩
      exact ⟨f.trans
        (Bong.QuadraticSpace.scalarExtensionScaledLineIsometry
          (E := p.Completion) a).symm.toRepresentation⟩
    have hnormalized :=
      (representsScaledLine_iff_negLine_sum_isotropic
        (q.scalarExtension (E := p.Completion)) aE).mp hline
    exact isIsotropicSpace_map
      (Classical.choice (scalarExtension_negLineSum_isometric q a)).symm
      hnormalized
  exact (representsScaledLine_iff_negLine_sum_isotropic q a).mpr
    (hiso augmented hAugFinite hAugInfinite)

/-- O'Meara 66:1 implies the uniform rank-one case used by the formalized
induction for 66:3. -/
theorem hasAllPlaceRankOneHasseRepresentation_of_hasseIsotropy
    (hiso : HasAllPlaceHasseIsotropy K) :
    HasAllPlaceRankOneHasseRepresentation K := by
  intro V _ _ _ q W _ _ _ r hrank hFinite hInfinite
  obtain ⟨a, ⟨e⟩⟩ :=
    Bong.QuadraticSpace.exists_field_rankOne_scaledLine r hrank
  have hLineFinite : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      (q.scalarExtension (E := p.adicCompletion K)).Represents
        ((Bong.QuadraticSpace.scaledLine a).scalarExtension
          (E := p.adicCompletion K)) := by
    intro p
    rcases hFinite p with ⟨f⟩
    exact ⟨f.trans e.symm.toRepresentation.scalarExtension⟩
  have hLineInfinite : ∀ p : NumberField.InfinitePlace K,
      (q.scalarExtension (E := p.Completion)).Represents
        ((Bong.QuadraticSpace.scaledLine a).scalarExtension
          (E := p.Completion)) := by
    intro p
    rcases hInfinite p with ⟨f⟩
    exact ⟨f.trans e.symm.toRepresentation.scalarExtension⟩
  have hLine := scaledLineHasse_of_hasseIsotropy
    hiso q a hLineFinite hLineInfinite
  exact hLine.trans ⟨e.toRepresentation⟩

/-- The exact representation theorem O'Meara 66:3 follows in every rank
from the all-place isotropy theorem 66:1. -/
theorem hasAllPlaceHasseRepresentationAtRank_of_hasseIsotropy
    (hiso : HasAllPlaceHasseIsotropy K)
    {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (q : Bong.QuadraticSpace K V) (n : Nat) :
    HasAllPlaceHasseRepresentationAtRank.{u, u, u} q n :=
  hasAllPlaceHasseRepresentationAtRank_of_rankOne
    (hasAllPlaceRankOneHasseRepresentation_of_hasseIsotropy hiso) q n

end NumberFieldLattice

end Bong.HeADCV5.Global
