import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldMathlibArtin
import NormEuclidean.IdealArtinConsequences

/-!
# Actual ordinary Hilbert class fields and arithmetic Artin reciprocity

The field is selected from the proved existence theorem for maximal
everywhere-unramified finite abelian extensions in the separable closure.
Its definition does not use a class number or a prime-splitting conclusion.
-/

noncomputable section

namespace NormEuclidean.HilbertClassFieldArithmetic

open IsDedekindDomain ExtensionIdeleNorm
open ClassFieldTheory.SmallHilbertClassFieldComparison
open scoped NumberField nonZeroDivisors NormEuclidean.CompletedExtensionProduct

variable (K : Type) [Field K] [NumberField K]

/-- The actual finite abelian extension supplied by Hilbert class-field existence. -/
def extension : ClassFieldTheory.FiniteAbelianExtension K :=
  Classical.choose (ClassFieldTheory.GlobalClassFieldComparison.exists_smallHilbertClassField K)

/-- The ordinary Hilbert class field as an actual intermediate field of the separable closure. -/
def field : IntermediateField K (SeparableClosure K) := (extension K).1

instance fieldFiniteDimensional : FiniteDimensional K (field K) := (extension K).2.1

instance fieldAbelian : IsAbelianGalois K (field K) := (extension K).2.2

instance fieldNumberField : NumberField (field K) := NumberField.of_module_finite K (field K)

/-- The selected field is unramified everywhere and contains every such finite abelian extension. -/
theorem specification : ClassFieldTheory.IsSmallHilbertClassField (extension K) :=
  Classical.choose_spec
    (ClassFieldTheory.GlobalClassFieldComparison.exists_smallHilbertClassField K)

/-- Every actual finite prime of the base is unramified in the ordinary Hilbert class field. -/
theorem finite_unramified (p : HeightOneSpectrum (𝓞 K)) :
    Algebra.IsUnramifiedIn (𝓞 (field K)) p.asIdeal := (specification K).1.1 p

/-- Every everywhere-unramified finite abelian field in the same closure is contained in it. -/
theorem contains_everywhere_unramified (F : ClassFieldTheory.FiniteAbelianExtension K)
    (hF : ClassFieldTheory.IsEverywhereUnramified K F) : F.1 ≤ field K := by
  letI : IsAbelianGalois K F.1 := F.2.2
  obtain ⟨φ⟩ := (specification K).2 F hF
  let f : F.1 →ₐ[K] SeparableClosure K := (field K).val.comp φ
  rw [← AlgHom.fieldRange_of_normal f]
  rintro x ⟨y, rfl⟩
  exact (φ y).property

/-- Arithmetic reciprocity identifies the actual Hilbert Galois group with the ordinary class
group. -/
def classGroupEquiv : ClassGroup (𝓞 K) ≃* ((field K) ≃ₐ[K] (field K)) :=
  (arithmeticSmallHilbertClassFieldGaloisEquivClassGroup_of_isSmall
      (extension K) (specification K)).symm

/-- The ideal Artin map induced by arithmetic reciprocity. -/
def artin : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* ((field K) ≃ₐ[K] (field K)) :=
  (classGroupEquiv K).toMonoidHom.comp (ClassGroup.mk K)

/-- The actual ideal Artin map is surjective. -/
theorem artin_surjective : Function.Surjective (artin K) := by
  apply (classGroupEquiv K).surjective.comp
  intro c
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective c
  exact ⟨FractionalIdeal.mk0 K I, (ClassGroup.mk_mk0 K I).trans hI⟩

/-- Cox 5.23: the actual ideal Artin kernel is exactly the principal fractional ideals. -/
theorem artin_ker : (artin K).ker = (toPrincipalIdeal (𝓞 K) K).range := by
  rw [← IdealArtinConsequences.class_projection_ker (K := K)]
  ext I
  change classGroupEquiv K (ClassGroup.mk K I) = 1 ↔ ClassGroup.mk K I = 1
  constructor
  · intro h
    exact (classGroupEquiv K).injective (h.trans (map_one (classGroupEquiv K)).symm)
  · intro h
    rw [h, map_one]

/-- The ideal Artin map is normalized by the actual integer-ring arithmetic Frobenius. -/
theorem artin_prime (p : HeightOneSpectrum (𝓞 K))
    (w : FinitePlacesAbove (E := field K) p) :
    artin K (IdealArtinConsequences.primeIdeal p) =
      FrobeniusSplitting.frobenius (K := K) w.1 := by
  let σ := GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
    (K := K) (L := extension K) p
  have hclass : (classGroupEquiv K).symm σ =
      ClassGroup.mk K (IdealArtinConsequences.primeIdeal p) :=
    arithmeticSmallHilbertClassFieldGaloisEquivClassGroup_prime
        (extension K) (specification K) p
  have hmap : artin K (IdealArtinConsequences.primeIdeal p) = σ := by
    apply (classGroupEquiv K).symm.injective
    exact ((classGroupEquiv K).symm_apply_apply _).trans hclass.symm
  have hlie : w.1.asIdeal.LiesOver p.asIdeal :=
    ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩
  have hunram : Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal :=
    finite_unramified K p _ w.1.isPrime hlie
  exact hmap.trans
    (ClassFieldTheory.GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
      p w.1 hlie hunram)

/-- The actual ordinary Hilbert class field has the ordinary class number as its degree. -/
theorem degree_eq_class_number : Module.finrank K (field K) = NumberField.classNumber K :=
  IdealArtinConsequences.degree_eq_class_number (artin K) (artin_surjective K) (artin_ker K)

/-- Cox 5.25 for actual ideals: complete splitting is equivalent to principality. -/
theorem split_iff_principal (p : HeightOneSpectrum (𝓞 K)) :
    (∀ w : FinitePlacesAbove (E := field K) p,
      w.1.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ w.1.asIdeal.inertiaDeg (𝓞 K) = 1) ↔
      p.asIdeal.IsPrincipal :=
  IdealArtinConsequences.split_iff_principal (artin K) (artin_ker K) p
    (finite_unramified K p) (artin_prime K p)

/-- Every principal finite prime has degree-one completions in the actual Hilbert class field. -/
theorem degree_one_of_principal (p : HeightOneSpectrum (𝓞 K))
    (hp : p.asIdeal.IsPrincipal) (w : FinitePlacesAbove (E := field K) p) :
    Module.finrank (p.adicCompletion K) (w.1.adicCompletion (field K)) = 1 :=
  IdealArtinConsequences.degree_one_of_principal (artin K) (artin_ker K) p
    (finite_unramified K p) (artin_prime K p) hp w

end NormEuclidean.HilbertClassFieldArithmetic
