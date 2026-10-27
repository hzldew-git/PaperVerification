import NormEuclidean.BinaryHilbertArtinNorm
import NormEuclidean.BinaryClassNumberCorrection

/-!
# Binary genus closure through the actual Hilbert Artin kernel

The class-number-two proof passes through actual Hilbert reciprocity,
unramified norm lifting, hyperbolic kernel strong approximation, and
cancellation. It compares only extensions of members of the original
ordinary genus, without asserting class number one for the enlarged genus.
-/

noncomputable section

namespace NormEuclidean.BinaryHilbertGenusClosure

open IsDedekindDomain CompletedIntegralLattice ProperSpinor AdelicOrthogonal
  AdelicComparison ExtensionIdeleNorm QuadraticExtensionNorm
open scoped NumberField

universe v
variable {K : Type} [Field K] [NumberField K]
  {V : Type v} [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- The actual Hilbert norm correction gives a proper stable isometry for each original genus
member. No enlarged-genus class number or approximation hypothesis is supplied. -/
theorem hyperbolic_proper_isometry_of_class_number_two
    (L M : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hclass : NumberField.classNumber K = 2)
    (hgen : SameGenus Q L M) :
    ProperlyGloballyIsometric (Hyperbolic.form Q) L.hyperbolic M.hyperbolic := by
  letI := L.finiteDimensional
  let hQ := quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA
  let h := LocalIntegralReflection.sameProperGenus_of_sameGenus Q hQ L M hgen
  let c := CompletedHyperbolicSpinorMap.comparison Q h
  let a := finiteComparisonSpinorIdele hQ h
  let b := fullComparisonSpinorIdele hQ h
  have hnorm : b ∈ (quadraticExtensionIdeleNorm theta htheta).range :=
    BinaryAdelicNorm.comparison_mem_norm_range f htheta hQ h
  have hartin : HilbertIdeleArtin.artin K b = 1 :=
    BinaryHilbertArtinNorm.norm L hA hE hdim theta htheta f hclass b hnorm
  have hprincipal : FiniteIdele.classHom a = 1 := by
    change b ∈ (FullIdeleClassKernel.classHom (K := K)).ker
    rw [← HilbertIdeleArtin.ker_eq]
    exact hartin
  have hscalar : ∀ p : HeightOneSpectrum (integerSubring K),
      properAmbientSpinorNormHom (form (integerSubring K) p (Hyperbolic.form Q))
        (form_polarBilin_nondegenerate _ p _
          (Hyperbolic.form_polarBilin_nondegenerate Q hQ)) (c.toAdelic p) =
        Bong.Dyadic.squareClass (LocalField (integerSubring K) p)
          (FiniteIdele.componentUnit p a) := by
    intro p
    rw [show c.toAdelic p = (CompletedHyperbolicSpinorMap.comparison Q h).toAdelic p from rfl,
      CompletedHyperbolicSpinorMap.comparison_spinorNorm]
    exact (squareClass_component_finiteComparisonSpinorIdele hQ h p).symm
  exact BinaryClassNumberCorrection.hyperbolic_isometry_of_class_kernel
    Q hQ (by omega) L c a hscalar hprincipal

/-- Original-genus cancellation closes the exceptional branch via the Hilbert field. -/
theorem class_number_one_of_class_number_two (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hclass : NumberField.classNumber K = 2) :
    HasLatticeClassNumberOne Q L := by
  apply hasLatticeClassNumberOne_of_genus_hyperbolic_isometry L hA hE
  intro M hgen
  exact ProperlyGloballyIsometric.globallyIsometric (Hyperbolic.form Q)
    (hyperbolic_proper_isometry_of_class_number_two L M hA hE hdim theta htheta f hclass hgen)

/-- Both field branches now close without a frame, root, unramifiedness, or correction input. -/
theorem class_number_one (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) : HasLatticeClassNumberOne Q L := by
  rcases BinaryFieldArithmetic.classNumber_eq_one_or_two L hA hE hdim with hone | htwo
  · letI := L.finiteDimensional
    letI : IsPrincipalIdealRing (integerSubring K) :=
      NumberField.classNumber_eq_one_iff.mp hone
    exact hasLatticeClassNumberOne_of_hyperbolic L hA hE
      (ClassNumberClosure.hyperbolic_classNumberOne L
        (quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA) (by omega))
  · letI := L.finiteDimensional
    obtain ⟨theta, htheta, ⟨f⟩⟩ := BinaryNormForm.exists_frame hA hdim
    exact class_number_one_of_class_number_two L hA hE hdim theta htheta f htwo

end NormEuclidean.BinaryHilbertGenusClosure
