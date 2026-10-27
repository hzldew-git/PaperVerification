import NormEuclidean.ChapterX.QuadraticCompletedFactorization
import NormEuclidean.ChapterX.InfiniteCompletedNorm

/-!
# Quadratic norm images in actual completion fibers

The equivalences use every completion factor, including at split places.
They identify the product of the determinant norms with the quadratic norm
equation. No local norm index or Hilbert-symbol law is assumed.
-/

noncomputable section

namespace NormEuclidean.CompletedNormImages

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm
open scoped NumberField NormEuclidean.CompletedExtensionProduct
  NormEuclidean.InfiniteCompletedNorm NumberField.LiesOver

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- The local quadratic algebra is the product of all actual finite completions. -/
def finiteEquiv (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    QuadraticAlgebra (p.adicCompletion K)
        (algebraMap K (p.adicCompletion K) (theta : K)) 0 ≃ₐ[p.adicCompletion K]
      CompletedExtensionProduct.Product (E := QuadraticAlgebra K (theta : K) 0) p := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  exact (QuadraticScalarExtension.equiv (F := p.adicCompletion K) (theta : K)).symm.trans
    (QuadraticCompletedFactorization.equiv theta htheta p)

/-- The local quadratic algebra is the product of all actual infinite completions. -/
def infiniteEquiv (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (v : NumberField.InfinitePlace K) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    QuadraticAlgebra v.Completion (algebraMap K v.Completion (theta : K)) 0 ≃ₐ[v.Completion]
      InfiniteCompletedNorm.Product (E := QuadraticAlgebra K (theta : K) 0) v := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  exact (QuadraticScalarExtension.equiv (F := v.Completion) (theta : K)).symm.trans
    (InfiniteCompletedNorm.equiv v)

/-- Norms in an arbitrary finite product are represented by a unit of any
algebra identified with that product. -/
theorem mem_fiberNorm_range_iff {F A ι : Type*} [Field F] [CommRing A]
    [Algebra F A] [Fintype ι] (B : ι → Type*) [∀ i, CommRing (B i)]
    [∀ i, Algebra F (B i)] [∀ i, Module.Finite F (B i)]
    (e : A ≃ₐ[F] ((i : ι) → B i)) (a : Fˣ) :
    (∃ z : (i : ι) → (B i)ˣ, (∏ i, Units.map (Algebra.norm F) (z i)) = a) ↔
      a ∈ (Units.map (Algebra.norm F : A →* F)).range := by
  classical
  have hn (z : Aˣ) :
      (∏ i, Units.map (Algebra.norm F) (MulEquiv.piUnits (Units.map e.toMonoidHom z) i)) =
        Units.map (Algebra.norm F) z := by
    apply Units.ext
    rw [Units.coe_prod]
    change (∏ i, Algebra.norm F (e (z : A) i)) = Algebra.norm F (z : A)
    rw [← ProductNorm.norm_pi]
    exact Algebra.norm_eq_of_algEquiv e (z : A)
  constructor
  · rintro ⟨z, hz⟩
    let x : Aˣ := Units.map e.symm.toMonoidHom (MulEquiv.piUnits.symm z)
    refine ⟨x, ?_⟩
    rw [← hn x]
    have hpi : MulEquiv.piUnits (Units.map e.toMonoidHom x) = z := by
      apply MulEquiv.piUnits.symm.injective
      apply Units.ext
      change e (e.symm _) = _
      simp
    rw [hpi]
    exact hz
  · rintro ⟨z, rfl⟩
    exact ⟨MulEquiv.piUnits (Units.map e.toMonoidHom z), hn z⟩

set_option maxHeartbeats 600000 in
/-- Every finite-place quadratic norm equation is exactly the image of the
actual product of completed field norms, including the split case. -/
theorem finite_norm_range_iff (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K)) (a : (p.adicCompletion K)ˣ) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    a ∈ (finitePlaceFiberNormUnits (E := QuadraticAlgebra K (theta : K) 0) p).range ↔
      Bong.Dyadic.IsQuadraticNorm (p.adicCompletion K)
        (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta) a := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  have h := mem_fiberNorm_range_iff
    (fun w : FinitePlacesAbove (E := QuadraticAlgebra K (theta : K) 0) p ↦
      w.1.adicCompletion (QuadraticAlgebra K (theta : K) 0))
    (finiteEquiv theta htheta p) a
  exact h.trans (quadraticNorm_iff_mem_algebraNormUnits_range
    (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta) a).symm

set_option maxHeartbeats 600000 in
/-- The same exact image comparison holds at every infinite place. -/
theorem infinite_norm_range_iff (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (v : NumberField.InfinitePlace K) (a : v.Completionˣ) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    a ∈ (infinitePlaceFiberNormUnits (E := QuadraticAlgebra K (theta : K) 0) v).range ↔
      Bong.Dyadic.IsQuadraticNorm v.Completion
        (Units.map (algebraMap K v.Completion).toMonoidHom theta) a := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  have h := mem_fiberNorm_range_iff
    (fun w : InfinitePlacesAbove (E := QuadraticAlgebra K (theta : K) 0) v ↦ w.1.Completion)
    (infiniteEquiv theta htheta v) a
  exact h.trans (quadraticNorm_iff_mem_algebraNormUnits_range
    (Units.map (algebraMap K v.Completion).toMonoidHom theta) a).symm

end NormEuclidean.CompletedNormImages
