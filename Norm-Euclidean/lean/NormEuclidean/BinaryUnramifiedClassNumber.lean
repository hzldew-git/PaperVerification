import NormEuclidean.BinaryClassNumberCorrection
import NormEuclidean.UnramifiedUnitNorms
import NormEuclidean.ChapterX.ClassNumberClosure

/-!
# The binary class-number conclusion from explicit local arithmetic conditions

Local even order, maximal dyadic defect and infinite splitting give actual
unit norm preimages. The geometric correction, strong approximation and
restricted cancellation are already proved. The field class-number bound
and these local conditions remain explicit arithmetic hypotheses.
-/

noncomputable section

namespace NormEuclidean.BinaryUnramifiedClassNumber

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm Bong.Dyadic
open scoped NumberField WithZero

variable {K : Type*} [Field K] [NumberField K]

/-- Concrete local square-class conditions imply norm surjectivity on ordinary unit ideles. -/
theorem unitIdeles_le_norm (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (hodd : ∀ (p : HeightOneSpectrum (𝓞 K)), (2 : 𝓞 K) ∉ p.asIdeal →
      Even (WithZero.log (p.valuation K (theta : K))))
    (hdyadic : ∀ (p : HeightOneSpectrum (𝓞 K)) (hp : (2 : 𝓞 K) ∈ p.asIdeal),
      letI := Bong.NumberFieldCompletion.dyadicContext p hp
      ((2 * ramificationIndex (p.adicCompletion K) : ℕ) : ℕ∞) ≤
        quadraticDefect (p.adicCompletion K)
          (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta))
    (hinfty : ∀ v : NumberField.InfinitePlace K,
      IsSquare (Units.map (algebraMap K v.Completion).toMonoidHom theta)) :
    FullIdeleClassKernel.unitIdeles ≤ (quadraticExtensionIdeleNorm theta htheta).range := by
  apply QuadraticIdeleClassCorrection.unitIdeles_le_norm theta htheta _ hinfty
  intro p a ha
  by_cases hp : (2 : 𝓞 K) ∈ p.asIdeal
  · exact UnramifiedUnitNorms.dyadic_unit_norm p hp _ a (hdyadic p hp) ha
  · apply UnramifiedUnitNorms.odd_unit_norm p hp _ a _ ha
    change Even (WithZero.log (Valued.v (algebraMap K (p.adicCompletion K) (theta : K))))
    have hval : Valued.v (algebraMap K (p.adicCompletion K) (theta : K)) =
        p.valuation K (theta : K) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p _
    rw [hval]
    exact hodd p hp

variable {V : Type*} [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- Original ordinary class number one in the exceptional binary branch,
with only the concrete global and local arithmetic inputs left explicit. -/
theorem classNumberOne_of_local_conditions (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hclass : NumberField.classNumber K = 2)
    (hodd : ∀ (p : HeightOneSpectrum (𝓞 K)), (2 : 𝓞 K) ∉ p.asIdeal →
      Even (WithZero.log (p.valuation K (theta : K))))
    (hdyadic : ∀ (p : HeightOneSpectrum (𝓞 K)) (hp : (2 : 𝓞 K) ∈ p.asIdeal),
      letI := Bong.NumberFieldCompletion.dyadicContext p hp
      ((2 * ramificationIndex (p.adicCompletion K) : ℕ) : ℕ∞) ≤
        quadraticDefect (p.adicCompletion K)
          (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta))
    (hinfty : ∀ v : NumberField.InfinitePlace K,
      IsSquare (Units.map (algebraMap K v.Completion).toMonoidHom theta)) :
    HasLatticeClassNumberOne Q L :=
  BinaryClassNumberCorrection.classNumberOne_of_norm_units Q L hA hE hdim theta htheta f hclass
    (unitIdeles_le_norm theta htheta hodd hdyadic hinfty)

/-- Both possible field class numbers are handled; the unramified local
conditions are required only in the class-number-two branch. -/
theorem classNumberOne_of_classNumber_le_two (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (hbound : NumberField.classNumber K ≤ 2)
    (hodd : NumberField.classNumber K = 2 →
      ∀ (p : HeightOneSpectrum (𝓞 K)), (2 : 𝓞 K) ∉ p.asIdeal →
        Even (WithZero.log (p.valuation K (theta : K))))
    (hdyadic : NumberField.classNumber K = 2 →
      ∀ (p : HeightOneSpectrum (𝓞 K)) (hp : (2 : 𝓞 K) ∈ p.asIdeal),
        letI := Bong.NumberFieldCompletion.dyadicContext p hp
        ((2 * ramificationIndex (p.adicCompletion K) : ℕ) : ℕ∞) ≤
          quadraticDefect (p.adicCompletion K)
            (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta))
    (hinfty : NumberField.classNumber K = 2 →
      ∀ v : NumberField.InfinitePlace K,
        IsSquare (Units.map (algebraMap K v.Completion).toMonoidHom theta)) :
    HasLatticeClassNumberOne Q L := by
  by_cases hclass : NumberField.classNumber K = 1
  · letI := L.finiteDimensional
    letI : IsPrincipalIdealRing (integerSubring K) :=
      NumberField.classNumber_eq_one_iff.mp hclass
    exact hasLatticeClassNumberOne_of_hyperbolic L hA hE
      (ClassNumberClosure.hyperbolic_classNumberOne L
        (quadraticForm_polarBilin_nondegenerate_of_anisotropic Q hA) (by omega))
  · have htwo : NumberField.classNumber K = 2 := by
      have hpos := NumberField.classNumber_pos K
      omega
    exact classNumberOne_of_local_conditions L hA hE hdim theta htheta f htwo
      (hodd htwo) (hdyadic htwo) (hinfty htwo)

end NormEuclidean.BinaryUnramifiedClassNumber
