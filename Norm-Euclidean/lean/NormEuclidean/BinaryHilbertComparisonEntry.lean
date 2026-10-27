import NormEuclidean.BinarySplittingPrimes
import NormEuclidean.QuadraticFieldGenerators
import NormEuclidean.QuadraticFieldComparison
import NormEuclidean.RootCompletionDescent

/-!
# The remaining Hilbert class-field arithmetic inputs

H is an actual intermediate number field in the same ambient field as the
binary discriminant extension. Degree-two presentations are constructed
internally. The degree/class-number identity and principal-prime splitting
remain explicit Cox 5.23/5.25 inputs; no Hilbert class field is defined by
the desired comparison, and no class-field existence theorem is asserted.
-/

noncomputable section

namespace NormEuclidean.BinaryHilbertComparisonEntry

open IsDedekindDomain ExtensionIdeleNorm
open scoped NumberField IntermediateField NormEuclidean.CompletedExtensionProduct

universe u v
variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  {V : Type v} [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- A quadratic candidate splitting every principal prime is the actual discriminant field. -/
theorem eq_of_degree_two_and_principal_splitting (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (r : Ω)
    (hr : r ^ 2 = algebraMap K Ω (theta : K))
    (H : IntermediateField K Ω) [NumberField H] (hdegree : Module.finrank K H = 2)
    (hprincipal : ∀ᶠ p : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      p.asIdeal.IsPrincipal → ∀ w : FinitePlacesAbove (E := H) p,
        Module.finrank (p.adicCompletion K) (w.1.adicCompletion H) = 1) :
    H = K⟮r⟯ := by
  obtain ⟨eta, heta, s, hs, hgen⟩ := QuadraticFieldGenerators.exists_root_generator hdegree
  have hsΩ : (s : Ω) ^ 2 = algebraMap K Ω (eta : K) := congrArg Subtype.val hs
  have hH : K⟮(s : Ω)⟯ = H := by
    have hh := congrArg (IntermediateField.lift (F := H)) hgen
    simpa only [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top] using hh
  have himp : ∀ᶠ p : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta) →
        IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom eta) := by
    filter_upwards [hprincipal] with p hp htheta
    have hpri := BinarySplittingPrimes.prime_isPrincipal_of_local_square
      L hA hE hdim f p htheta
    obtain ⟨w⟩ := finitePlacesAbove_nonempty (E := H) p
    exact RootCompletionDescent.isSquare_of_degree_one eta s hs p w (hp hpri w)
  exact hH.symm.trans (QuadraticFieldComparison.adjoin_eq_of_eventually_split_imp
    theta eta htheta heta r (s : Ω) hr hsΩ himp)

/-- The class-number-two branch needs only the actual Hilbert degree and splitting inputs. -/
theorem eq_of_class_number_two (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (r : Ω)
    (hr : r ^ 2 = algebraMap K Ω (theta : K))
    (H : IntermediateField K Ω) [NumberField H]
    (hdegree : Module.finrank K H = NumberField.classNumber K)
    (hprincipal : ∀ᶠ p : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      p.asIdeal.IsPrincipal → ∀ w : FinitePlacesAbove (E := H) p,
        Module.finrank (p.adicCompletion K) (w.1.adicCompletion H) = 1)
    (htwo : NumberField.classNumber K = 2) : H = K⟮r⟯ :=
  eq_of_degree_two_and_principal_splitting L hA hE hdim theta htheta f r hr H
    (hdegree.trans htwo) hprincipal

/-- Actual field containment and the equality characterization under the two Cox inputs. -/
theorem le_and_eq_iff_class_number_two (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (hdim : Module.finrank K V = 2) (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (f : BinaryNormForm.Frame Q theta) (r : Ω)
    (hr : r ^ 2 = algebraMap K Ω (theta : K))
    (H : IntermediateField K Ω) [NumberField H]
    (hdegree : Module.finrank K H = NumberField.classNumber K)
    (hprincipal : ∀ᶠ p : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      p.asIdeal.IsPrincipal → ∀ w : FinitePlacesAbove (E := H) p,
        Module.finrank (p.adicCompletion K) (w.1.adicCompletion H) = 1) :
    H ≤ K⟮r⟯ ∧ (NumberField.classNumber K = 2 ↔ H = K⟮r⟯) := by
  have heq := eq_of_class_number_two L hA hE hdim theta htheta f r hr H hdegree hprincipal
  refine ⟨?_, ⟨heq, ?_⟩⟩
  · rcases BinaryFieldArithmetic.classNumber_eq_one_or_two L hA hE hdim with hone | htwo
    · have hbot : H = ⊥ := IntermediateField.finrank_eq_one_iff.mp (hdegree.trans hone)
      rw [hbot]
      exact bot_le
    · exact (heq htwo).le
  · intro h
    exact hdegree.symm.trans (h ▸ QuadraticRootFields.finrank_adjoin theta htheta r hr)

end NormEuclidean.BinaryHilbertComparisonEntry
