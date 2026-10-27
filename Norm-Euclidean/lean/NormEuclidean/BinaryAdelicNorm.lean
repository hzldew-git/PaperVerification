import NormEuclidean.BinarySpinorNorm
import NormEuclidean.AdelicComparison
import NormEuclidean.ChapterX.NormFiberAssembly
import NormEuclidean.ChapterX.LocalIntegralReflection

/-!
# Binary genus comparisons are actual idelic norms

The frame is transported to the tensor-product completions used by the
genus model. All finite places, including split and dyadic ones, are covered.
The normalized comparison has identity infinite components, and the existing
restricted-product norm assembly yields an actual extension idele.
-/

noncomputable section

namespace NormEuclidean.BinaryAdelicNorm

open IsDedekindDomain CompletedIntegralLattice ProperSpinor BinaryNormForm
  BinarySpinorNorm AdelicComparison QuadraticExtensionNorm ExtensionIdeleNorm
open scoped NumberField

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {theta : Kˣ}

local instance finiteCharZero (p : HeightOneSpectrum (integerSubring K)) :
    CharZero (LocalField (integerSubring K) p) := Algebra.charZero_of_charZero K _

/-- Equality of norm images in the actual finite completed quadratic space. -/
theorem completed_spinor_range_eq (f : Frame Q theta) (hQ : Q.polarBilin.Nondegenerate)
    (p : HeightOneSpectrum (integerSubring K)) :
    (properAmbientSpinorNormHom (form (integerSubring K) p Q)
      (form_polarBilin_nondegenerate (integerSubring K) p Q hQ)).range =
        normSquareClasses (Units.map (algebraMap K (LocalField (integerSubring K) p)) theta) :=
  proper_spinor_range_eq (f.baseChange (LocalField (integerSubring K) p))
    (form_polarBilin_nondegenerate (integerSubring K) p Q hQ)

/-- Every chosen finite comparison representative is a local quadratic norm. -/
theorem comparison_representative_isNorm (f : Frame Q theta)
    (hQ : Q.polarBilin.Nondegenerate) {L M : Lattice (integerSubring K) Q}
    (h : SameProperGenus Q L M) (p : HeightOneSpectrum (integerSubring K)) :
    Bong.Dyadic.IsQuadraticNorm (LocalField (integerSubring K) p)
      (Units.map (algebraMap K (LocalField (integerSubring K) p)) theta)
      (localSpinorRepresentative hQ h p) :=
  representative_isNorm (f.baseChange (LocalField (integerSubring K) p))
    (form_polarBilin_nondegenerate (integerSubring K) p Q hQ)
    (AdelicOrthogonal.localComparison h p) _ (squareClass_localSpinorRepresentative hQ h p)

/-- The comparison scalar idele lies in the actual extension norm image, before quotienting. -/
theorem comparison_mem_norm_range (f : Frame Q theta) (htheta : ¬ IsSquare theta)
    (hQ : Q.polarBilin.Nondegenerate) {L M : Lattice (integerSubring K) Q}
    (h : SameProperGenus Q L M) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    fullComparisonSpinorIdele hQ h ∈
      (extensionIdeleNorm (K := K) (E := QuadraticAlgebra K theta.val 0)).range := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  apply (NormFiberAssembly.mem_full_norm_range_iff theta htheta _).mpr
  constructor
  · intro p
    have he : ideleFiniteComponent p (fullComparisonSpinorIdele hQ h) =
        localSpinorRepresentative hQ h p := Units.ext rfl
    rw [he]
    exact comparison_representative_isNorm f hQ h p
  · intro v
    have he : ideleInfiniteComponent v (fullComparisonSpinorIdele hQ h) = 1 := Units.ext rfl
    rw [he]
    exact Bong.Dyadic.isQuadraticNorm_one _ _

/-- An actual extension idele whose norm equals the selected comparison scalar idele. -/
theorem exists_comparison_norm_preimage (f : Frame Q theta) (htheta : ¬ IsSquare theta)
    (hQ : Q.polarBilin.Nondegenerate) {L M : Lattice (integerSubring K) Q}
    (h : SameProperGenus Q L M) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ∃ beta : NumberFieldIdele (QuadraticAlgebra K theta.val 0),
      extensionIdeleNorm (K := K) beta = fullComparisonSpinorIdele hQ h :=
  comparison_mem_norm_range f htheta hQ h

omit [FiniteDimensional K V] in
/-- The original anisotropic binary lattice supplies every arithmetic model input.
The same quadratic extension works for every member of its ordinary genus. -/
theorem exists_norm_comparisons (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hdim : Module.finrank K V = 2) :
    letI := L.finiteDimensional
    ∃ theta : Kˣ, ∃ htheta : ¬ IsSquare theta,
      letI := quadraticExtensionField theta htheta
      letI := quadraticExtensionNumberField theta htheta
      ∀ (M : Lattice (integerSubring K) Q), SameGenus Q L M →
        ∃ h : SameProperGenus Q L M,
          ∃ beta : NumberFieldIdele (QuadraticAlgebra K theta.val 0),
            extensionIdeleNorm (K := K) beta = fullComparisonSpinorIdele
              (quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA) h := by
  letI := L.finiteDimensional
  obtain ⟨theta, htheta, ⟨f⟩⟩ := BinaryNormForm.exists_frame hA hdim
  refine ⟨theta, htheta, ?_⟩
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro M hgen
  let hQ := quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA
  let h := LocalIntegralReflection.sameProperGenus_of_sameGenus Q hQ L M hgen
  exact ⟨h, exists_comparison_norm_preimage f htheta hQ h⟩

end NormEuclidean.BinaryAdelicNorm
