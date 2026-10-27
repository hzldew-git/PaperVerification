import NormEuclidean.ChapterX.CompletedNormComparison
import NormEuclidean.ChapterX.QuadraticScalarExtension
import NormEuclidean.ChapterX.QuadraticExtensionNorm

/-!
# Actual completion norms at nonsplit quadratic places

At a place where the parameter remains nonsquare, the scalar-extended
quadratic algebra is a field. Its unital comparison map into the nonempty
product of actual completed extension fields is injective. Together with
the proved surjectivity this gives an actual algebra equivalence and norm
compatibility, without assuming a local-degree formula or a Hasse theorem.
The locally split places require a separate argument.
-/

noncomputable section

namespace NormEuclidean.QuadraticCompletedNorm

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm
open scoped NumberField TensorProduct NormEuclidean.CompletedExtensionProduct

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- Comparison from the scalar-extended quadratic algebra to the product
of the actual completed quadratic number field, above the given base place. -/
def localComparison (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    QuadraticAlgebra (p.adicCompletion K)
      (algebraMap K (p.adicCompletion K) (theta : K)) 0 →ₐ[p.adicCompletion K]
        CompletedExtensionProduct.Product (E := QuadraticAlgebra K (theta : K) 0) p := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  exact (CompletedExtensionProduct.comparison p).comp
    (QuadraticScalarExtension.equiv (F := p.adicCompletion K) (theta : K)).symm.toAlgHom

/-- This quadratic-algebra comparison is onto at every finite place,
including places where the parameter becomes a square. -/
theorem localComparison_surjective (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    Function.Surjective (localComparison theta htheta p) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  exact (CompletedExtensionProduct.comparison_surjective p).comp
    (QuadraticScalarExtension.equiv (F := p.adicCompletion K) (theta : K)).symm.surjective

/-- At a nonsplit finite place the actual tensor comparison is injective.
The local nonsquare assumption is the mathematical distinction of this branch. -/
theorem comparison_injective_of_nonsquare (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K))
    (hlocal : ¬ IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    Function.Injective (CompletedExtensionProduct.comparison
      (E := QuadraticAlgebra K (theta : K) 0) p) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  let thetap : (p.adicCompletion K)ˣ :=
    Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta
  letI : Fact (∀ r : p.adicCompletion K,
      r ^ 2 ≠ algebraMap K (p.adicCompletion K) (theta : K) + 0 * r) :=
    ⟨nonsquare_quadraticAlgebra_field_fact thetap hlocal⟩
  letI := finitePlacesAbove_nonempty (E := QuadraticAlgebra K (theta : K) 0) p
  have hi : Function.Injective (localComparison theta htheta p) := by
    intro x y hxy
    let f := localComparison theta htheta p
    have hz : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hn : algebraMap (p.adicCompletion K)
        (CompletedExtensionProduct.Product (E := QuadraticAlgebra K (theta : K) 0) p)
        (QuadraticAlgebra.norm (x - y)) = 0 := by
      rw [← f.commutes, QuadraticAlgebra.algebraMap_norm_eq_mul_star,
        map_mul, hz, zero_mul]
    have hn0 : QuadraticAlgebra.norm (x - y) = 0 :=
      (FaithfulSMul.algebraMap_injective (p.adicCompletion K)
        (CompletedExtensionProduct.Product (E := QuadraticAlgebra K (theta : K) 0) p))
          (hn.trans (map_zero _).symm)
    exact sub_eq_zero.mp (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp hn0)
  have he := (QuadraticScalarExtension.equiv (F := p.adicCompletion K)
    (theta : K)).injective
  intro x y h
  apply he
  apply hi
  change CompletedExtensionProduct.comparison p
      ((QuadraticScalarExtension.equiv (theta : K)).symm
        (QuadraticScalarExtension.equiv (theta : K) x)) =
    CompletedExtensionProduct.comparison p
      ((QuadraticScalarExtension.equiv (theta : K)).symm
        (QuadraticScalarExtension.equiv (theta : K) y))
  simpa only [AlgEquiv.symm_apply_apply] using h

/-- Actual tensor-product factorization at a nonsplit quadratic finite place. -/
def nonsplitEquiv (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K))
    (hlocal : ¬ IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (p.adicCompletion K ⊗[K] QuadraticAlgebra K (theta : K) 0) ≃ₐ[p.adicCompletion K]
      CompletedExtensionProduct.Product (E := QuadraticAlgebra K (theta : K) 0) p := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  exact AlgEquiv.ofBijective (CompletedExtensionProduct.comparison p)
    ⟨comparison_injective_of_nonsquare theta htheta p hlocal,
      CompletedExtensionProduct.comparison_surjective p⟩

/-- The global norm agrees with the product of actual completed field norms
at every finite place where the quadratic extension remains nonsplit. -/
theorem norm_global_nonsplit (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K))
    (hlocal : ¬ IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta))
    (x : QuadraticAlgebra K (theta : K) 0) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (∏ w : FinitePlacesAbove (E := QuadraticAlgebra K (theta : K) 0) p,
      Algebra.norm (p.adicCompletion K)
        (algebraMap (QuadraticAlgebra K (theta : K) 0)
          (w.1.adicCompletion (QuadraticAlgebra K (theta : K) 0)) x)) =
      algebraMap K (p.adicCompletion K) (Algebra.norm K x) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  exact CompletedNormComparison.norm_global_of_injective p
    (comparison_injective_of_nonsquare theta htheta p hlocal) x

end NormEuclidean.QuadraticCompletedNorm
