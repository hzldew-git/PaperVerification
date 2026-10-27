import NormEuclidean.QuadraticRootFields
import NormEuclidean.QuadraticSplittingDetection
import NormEuclidean.QuadraticCompletionSplitting

/-!
# Quadratic field comparison from almost-everywhere splitting

The two fields are actual intermediate fields in a common ambient field.
The proved prime-selection theorem gives the quadratic special case of
Cox 8.19 directly, with finitely many exceptions permitted.
-/

noncomputable section

namespace NormEuclidean.QuadraticFieldComparison

open IsDedekindDomain QuadraticExtensionNorm ExtensionIdeleNorm
open scoped NumberField IntermediateField

variable {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]

/-- Containment of actual quadratic root fields is detected by their finite splitting sets. -/
theorem adjoin_le_iff_eventually_split_imp (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (eta : Kˣ) (r s : Ω) (hr : r ^ 2 = algebraMap K Ω (theta : K))
    (hs : s ^ 2 = algebraMap K Ω (eta : K)) :
    K⟮s⟯ ≤ K⟮r⟯ ↔
      ∀ᶠ p : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta) →
          IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom eta) :=
  (QuadraticRootFields.adjoin_le_iff theta htheta eta r s hr hs).trans
    (QuadraticSplittingDetection.eventually_split_imp_iff theta eta).symm

/-- Almost-everywhere one-way splitting inclusion already identifies two quadratic fields. -/
theorem adjoin_eq_of_eventually_split_imp (theta eta : Kˣ)
    (htheta : ¬ IsSquare theta) (heta : ¬ IsSquare eta) (r s : Ω)
    (hr : r ^ 2 = algebraMap K Ω (theta : K))
    (hs : s ^ 2 = algebraMap K Ω (eta : K))
    (h : ∀ᶠ p : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta) →
        IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom eta)) :
    K⟮s⟯ = K⟮r⟯ := by
  letI := QuadraticRootFields.finiteDimensional_adjoin theta htheta r hr
  have hle := (adjoin_le_iff_eventually_split_imp theta htheta eta r s hr hs).mpr h
  exact IntermediateField.eq_of_le_of_finrank_eq hle
    ((QuadraticRootFields.finrank_adjoin eta heta s hs).trans
      (QuadraticRootFields.finrank_adjoin theta htheta r hr).symm)

/-- The quadratic equality criterion is an equality of intermediate fields, not norm groups. -/
theorem adjoin_eq_iff_eventually_split_imp (theta eta : Kˣ)
    (htheta : ¬ IsSquare theta) (heta : ¬ IsSquare eta) (r s : Ω)
    (hr : r ^ 2 = algebraMap K Ω (theta : K))
    (hs : s ^ 2 = algebraMap K Ω (eta : K)) :
    K⟮s⟯ = K⟮r⟯ ↔
      ∀ᶠ p : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta) →
          IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom eta) := by
  constructor
  · intro h
    exact (adjoin_le_iff_eventually_split_imp theta htheta eta r s hr hs).mp h.le
  · exact adjoin_eq_of_eventually_split_imp theta eta htheta heta r s hr hs

/-- Cox's quadratic comparison expressed using actual prime ideals of the integer rings. -/
theorem adjoin_eq_of_eventually_prime_count_imp (theta eta : Kˣ)
    (htheta : ¬ IsSquare theta) (heta : ¬ IsSquare eta) (r s : Ω)
    (hr : r ^ 2 = algebraMap K Ω (theta : K))
    (hs : s ^ 2 = algebraMap K Ω (eta : K))
    (h : letI := quadraticExtensionField theta htheta
      letI := quadraticExtensionNumberField theta htheta
      letI := quadraticExtensionField eta heta
      letI := quadraticExtensionNumberField eta heta
      ∀ᶠ p : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        (p.asIdeal.primesOver (𝓞 (QuadraticAlgebra K theta.val 0))).ncard = 2 →
          (p.asIdeal.primesOver (𝓞 (QuadraticAlgebra K eta.val 0))).ncard = 2) :
    K⟮s⟯ = K⟮r⟯ := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  letI := quadraticExtensionField eta heta
  letI := quadraticExtensionNumberField eta heta
  apply adjoin_eq_of_eventually_split_imp theta eta htheta heta r s hr hs
  filter_upwards [h] with p hp hlocal
  exact (QuadraticCompletionSplitting.prime_count_two_iff_square eta heta p).mp
    (hp ((QuadraticCompletionSplitting.prime_count_two_iff_square theta htheta p).mpr hlocal))

end NormEuclidean.QuadraticFieldComparison
