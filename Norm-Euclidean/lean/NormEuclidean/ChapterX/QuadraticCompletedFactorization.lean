import NormEuclidean.ChapterX.CompletedFiberAutomorphism
import NormEuclidean.ChapterX.QuadraticStableKernel
import NormEuclidean.ChapterX.QuadraticCompletedNorm

/-!
# Quadratic completed factorization at every finite place

Actual automorphism transport in the complete prime fiber makes the kernel
stable under quadratic conjugation. The trace calculation then proves
injectivity, including split and dyadic places, without a local-degree input.
-/

noncomputable section

namespace NormEuclidean.QuadraticCompletedFactorization

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm QuadraticCompletedNorm
open scoped NumberField TensorProduct QuadraticAlgebra NormEuclidean.CompletedExtensionProduct

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- The local comparison sends the quadratic generator to the embedded global generator. -/
theorem localComparison_omega (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ∀ w : FinitePlacesAbove (E := QuadraticAlgebra K (theta : K) 0) p,
      localComparison theta htheta p ω w =
        algebraMap (QuadraticAlgebra K (theta : K) 0)
          (w.1.adicCompletion (QuadraticAlgebra K (theta : K) 0)) ω := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro w
  have ho : QuadraticScalarExtension.equiv (F := p.adicCompletion K) (theta : K)
      ((1 : p.adicCompletion K) ⊗ₜ[K] (ω : QuadraticAlgebra K (theta : K) 0)) = ω := by
    change QuadraticScalarExtension.comparison (F := p.adicCompletion K) (theta : K)
      ((1 : p.adicCompletion K) ⊗ₜ[K] (ω : QuadraticAlgebra K (theta : K) 0)) = _
    rw [QuadraticScalarExtension.comparison_tmul]
    ext <;> simp [QuadraticScalarExtension.coordinateMap, QuadraticAlgebra.omega]
  change CompletedExtensionProduct.comparison p
    ((QuadraticScalarExtension.equiv (theta : K)).symm ω) w = _
  rw [← ho, AlgEquiv.symm_apply_apply, CompletedExtensionProduct.comparison_tmul,
    map_one, one_mul]

/-- The actual comparison has the expected two-coordinate formula. -/
theorem localComparison_apply (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ∀ (z : QuadraticAlgebra (p.adicCompletion K)
        (algebraMap K (p.adicCompletion K) (theta : K)) 0)
      (w : FinitePlacesAbove (E := QuadraticAlgebra K (theta : K) 0) p),
      localComparison theta htheta p z w =
        finitePlaceAboveCompletionMap p w z.re +
          finitePlaceAboveCompletionMap p w z.im *
            algebraMap (QuadraticAlgebra K (theta : K) 0)
              (w.1.adicCompletion (QuadraticAlgebra K (theta : K) 0)) ω := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro z w
  let f := (Pi.evalAlgHom (p.adicCompletion K) _ w).comp (localComparison theta htheta p)
  have hd : z = algebraMap (p.adicCompletion K) _ z.re +
      algebraMap (p.adicCompletion K) _ z.im * ω := by ext <;> simp
  have hc (a : p.adicCompletion K) :
      f (algebraMap (p.adicCompletion K) _ a) = finitePlaceAboveCompletionMap p w a :=
    f.commutes a
  calc
    _ = f (algebraMap (p.adicCompletion K) _ z.re +
        algebraMap (p.adicCompletion K) _ z.im * ω) := congrArg f hd
    _ = _ := by rw [map_add, map_mul, hc, hc];
                exact congrArg (_ + finitePlaceAboveCompletionMap p w z.im * ·)
                  (localComparison_omega theta htheta p w)

/-- Completed transport by global conjugation agrees with local quadratic conjugation. -/
theorem localComparison_conjugation (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ∀ (z : QuadraticAlgebra (p.adicCompletion K)
        (algebraMap K (p.adicCompletion K) (theta : K)) 0)
      (w : FinitePlacesAbove (E := QuadraticAlgebra K (theta : K) 0) p),
      AdicAutomorphism.completionMap
        (QuadraticStableKernel.conjugation (theta : K)).toRingEquiv w.1
        (localComparison theta htheta p z
          (CompletedFiberAutomorphism.prime (QuadraticStableKernel.conjugation (theta : K)) p w)) =
        localComparison theta htheta p (star z) w := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro z w
  have ho : (QuadraticStableKernel.conjugation (theta : K)).toRingEquiv
      (ω : QuadraticAlgebra K (theta : K) 0) = -ω := by
    ext <;> simp [QuadraticStableKernel.conjugation, QuadraticAlgebra.omega]
  rw [localComparison_apply, map_add, map_mul,
    CompletedFiberAutomorphism.completionMap_base,
    CompletedFiberAutomorphism.completionMap_base,
    AdicAutomorphism.completionMap_global, ho, map_neg, localComparison_apply]
  simp only [QuadraticAlgebra.re_star, zero_mul, add_zero, QuadraticAlgebra.im_star, map_neg]
  ring

/-- The actual completed comparison is injective at every finite quadratic place,
including split places. No local nonsquare or degree hypothesis is supplied. -/
theorem comparison_injective (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    Function.Injective (CompletedExtensionProduct.comparison
      (E := QuadraticAlgebra K (theta : K) 0) p) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  letI := finitePlacesAbove_nonempty (E := QuadraticAlgebra K (theta : K) 0) p
  have hi : Function.Injective (localComparison theta htheta p) := by
    apply QuadraticStableKernel.injective_of_stable _ (by
      exact (map_ne_zero (algebraMap K (p.adicCompletion K))).mpr (Units.ne_zero theta))
    intro z hz
    funext w
    rw [← localComparison_conjugation]
    simpa only [Pi.zero_apply, map_zero] using
      congrArg (AdicAutomorphism.completionMap
        (QuadraticStableKernel.conjugation (theta : K)).toRingEquiv w.1)
        (congrFun hz (CompletedFiberAutomorphism.prime
          (QuadraticStableKernel.conjugation (theta : K)) p w))
  intro x y h
  apply (QuadraticScalarExtension.equiv (F := p.adicCompletion K) (theta : K)).injective
  apply hi
  change CompletedExtensionProduct.comparison p
      ((QuadraticScalarExtension.equiv (theta : K)).symm
        (QuadraticScalarExtension.equiv (theta : K) x)) =
    CompletedExtensionProduct.comparison p
      ((QuadraticScalarExtension.equiv (theta : K)).symm
        (QuadraticScalarExtension.equiv (theta : K) y))
  simpa only [AlgEquiv.symm_apply_apply] using h

/-- The actual quadratic completed tensor-product factorization at every finite place. -/
def equiv (theta : Kˣ) (htheta : ¬ IsSquare theta) (p : HeightOneSpectrum (𝓞 K)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (p.adicCompletion K ⊗[K] QuadraticAlgebra K (theta : K) 0) ≃ₐ[p.adicCompletion K]
      CompletedExtensionProduct.Product (E := QuadraticAlgebra K (theta : K) 0) p := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  exact AlgEquiv.ofBijective (CompletedExtensionProduct.comparison p)
    ⟨comparison_injective theta htheta p, CompletedExtensionProduct.comparison_surjective p⟩

end NormEuclidean.QuadraticCompletedFactorization
