import NormEuclidean.BinaryFieldArithmetic
import NormEuclidean.BinaryClassNumberCorrection
import NormEuclidean.UnaryClassNumber

/-!
# Unconditional ordinary binary lattice class number one

The original binary genus comparison has local norm representatives. Their
ordinary class is now proved principal from norm-Euclidean descent itself.
The existing correction, kernel strong approximation and restricted
hyperbolic cancellation therefore have no remaining arithmetic input.
-/

noncomputable section

namespace NormEuclidean.BinaryClassNumberClosure

open IsDedekindDomain CompletedIntegralLattice ProperSpinor AdelicOrthogonal
  AdelicComparison
open scoped NumberField

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- The original anisotropic norm-Euclidean binary lattice has ordinary class number one. -/
theorem classNumberOne (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) : HasLatticeClassNumberOne Q L := by
  letI := L.finiteDimensional
  let hQ := quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA
  obtain ⟨theta, _, ⟨f⟩⟩ := BinaryNormForm.exists_frame hA hdim
  apply hasLatticeClassNumberOne_of_genus_hyperbolic_isometry L hA hE
  intro M hgen
  let h := LocalIntegralReflection.sameProperGenus_of_sameGenus Q hQ L M hgen
  let c := CompletedHyperbolicSpinorMap.comparison Q h
  let a := finiteComparisonSpinorIdele hQ h
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
  have hprincipal : FiniteIdele.classHom a = 1 := by
    apply NormIdelePrincipality.classHom_eq_one L hA hE (by omega) f a
    intro p
    change Bong.Dyadic.IsQuadraticNorm _ _
      (FiniteIdele.componentUnit p (finiteComparisonSpinorIdele hQ h))
    rw [componentUnit_finiteComparisonSpinorIdele]
    exact BinaryAdelicNorm.comparison_representative_isNorm f hQ h p
  exact ProperlyGloballyIsometric.globallyIsometric (Hyperbolic.form Q)
    (BinaryClassNumberCorrection.hyperbolic_isometry_of_class_kernel Q hQ (by omega)
      L c a hscalar hprincipal)

/-- Both numerical binary class-number conclusions now follow from the original hypotheses. -/
theorem field_and_lattice_classNumber (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) :
    NumberField.classNumber K ≤ 2 ∧ HasLatticeClassNumberOne Q L :=
  ⟨BinaryFieldArithmetic.classNumber_le_two L hA hE hdim, classNumberOne L hA hE hdim⟩

end NormEuclidean.BinaryClassNumberClosure
