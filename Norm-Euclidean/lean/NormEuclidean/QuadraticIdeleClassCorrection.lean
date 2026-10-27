import NormEuclidean.FullIdeleClassKernel
import NormEuclidean.ChapterX.NormFiberAssembly

/-!
# Quadratic idelic norm correction at ordinary class number two

The index-two theorem and the ordinary class kernel give an actual
principal-times-unit decomposition. The remaining arithmetic premises are
displayed as local unit norm equations and splitting at infinite places.
-/

noncomputable section

namespace NormEuclidean.QuadraticIdeleClassCorrection

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm FullIdeleClassKernel
open Bong.Dyadic
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- A split infinite completion has no scalar norm obstruction. -/
theorem infinite_norm_of_square (v : NumberField.InfinitePlace K) (theta a : v.Completionˣ)
    (htheta : IsSquare theta) : IsQuadraticNorm v.Completion theta a := by
  letI : CharZero v.Completion := Algebra.charZero_of_charZero K _
  exact isQuadraticNorm_of_isSquare_left v.Completion htheta

set_option backward.isDefEq.respectTransparency false in
/-- Assemble the finite-unit and infinite local norm equations into an actual norm idele. -/
theorem unitIdeles_le_norm_of_local (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (hfinite : ∀ (p : HeightOneSpectrum (𝓞 K)) (a : (p.adicCompletion K)ˣ),
      Valued.v (a : p.adicCompletion K) = 1 → IsQuadraticNorm (p.adicCompletion K)
        (Units.map (algebraMap K (p.adicCompletion K)) theta) a)
    (hinfty : ∀ (v : NumberField.InfinitePlace K) (a : v.Completionˣ),
      IsQuadraticNorm v.Completion
        (Units.map (algebraMap K v.Completion).toMonoidHom theta) a) :
    unitIdeles ≤ (quadraticExtensionIdeleNorm theta htheta).range := by
  intro i hi
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  apply (NormFiberAssembly.mem_full_norm_range_iff theta htheta i).mpr
  constructor
  · intro p
    apply hfinite
    have hp : FiniteIdele.order (FullIdeleClassKernel.finiteProjection i) p = 0 := hi p
    exact (FiniteIdele.order_eq_zero_iff (R := 𝓞 K) (K := K)
      (FullIdeleClassKernel.finiteProjection i) p).mp hp
  · intro v
    exact hinfty v (ideleInfiniteComponent v i)

/-- Local unit norm equations and infinite splitting place all ordinary unit
ideles in the actual quadratic extension norm image. -/
theorem unitIdeles_le_norm (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (hfinite : ∀ (p : HeightOneSpectrum (𝓞 K)) (a : (p.adicCompletion K)ˣ),
      Valued.v (a : p.adicCompletion K) = 1 → IsQuadraticNorm (p.adicCompletion K)
        (Units.map (algebraMap K (p.adicCompletion K)) theta) a)
    (hinfty : ∀ v : NumberField.InfinitePlace K,
      IsSquare (Units.map (algebraMap K v.Completion).toMonoidHom theta)) :
    unitIdeles ≤ (quadraticExtensionIdeleNorm theta htheta).range :=
  unitIdeles_le_norm_of_local theta htheta hfinite
    (fun v a ↦ infinite_norm_of_square v _ a (hinfty v))

/-- Good odd primes require no further input; only the finite exceptional
places have to supply unit norm equations. -/
theorem unitIdeles_le_norm_of_exceptional (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (hexceptional : ∀ (p : HeightOneSpectrum (𝓞 K)),
      (2 : 𝓞 K) ∈ p.asIdeal ∨ p.valuation K (theta : K) ≠ 1 →
        ∀ a : (p.adicCompletion K)ˣ, Valued.v (a : p.adicCompletion K) = 1 →
          IsQuadraticNorm (p.adicCompletion K)
            (Units.map (algebraMap K (p.adicCompletion K)) theta) a)
    (hinfty : ∀ v : NumberField.InfinitePlace K,
      IsSquare (Units.map (algebraMap K v.Completion).toMonoidHom theta)) :
    unitIdeles ≤ (quadraticExtensionIdeleNorm theta htheta).range := by
  apply unitIdeles_le_norm theta htheta _ hinfty
  intro p a ha
  by_cases htwo : (2 : 𝓞 K) ∈ p.asIdeal
  · exact hexceptional p (Or.inl htwo) a ha
  by_cases hunit : p.valuation K (theta : K) = 1
  · apply GoodPlaceNorms.isQuadraticNorm_of_units p htwo _ a _ ha
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p (theta : K)).trans hunit
  · exact hexceptional p (Or.inr hunit) a ha

/-- At class number two, a genuine quadratic norm has trivial ordinary ideal class. -/
theorem norm_class_eq_one (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (hclass : NumberField.classNumber K = 2)
    (hunit : unitIdeles ≤ (quadraticExtensionIdeleNorm theta htheta).range)
    (i : NumberFieldIdele K) (hi : i ∈ (quadraticExtensionIdeleNorm theta htheta).range) :
    FullIdeleClassKernel.classHom i = 1 := by
  change i ∈ (FullIdeleClassKernel.classHom (K := K)).ker
  rw [← principal_norm_eq_kernel theta htheta hclass hunit]
  exact (show (quadraticExtensionIdeleNorm theta htheta).range ≤
    idelePrincipalEmbedding.range ⊔ (quadraticExtensionIdeleNorm theta htheta).range
    from le_sup_right) hi

/-- The scalar correction is realized in the actual full idele group. -/
theorem exists_norm_decomposition (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (hclass : NumberField.classNumber K = 2)
    (hunit : unitIdeles ≤ (quadraticExtensionIdeleNorm theta htheta).range)
    (i : NumberFieldIdele K) (hi : i ∈ (quadraticExtensionIdeleNorm theta htheta).range) :
    ∃ k : Kˣ, ∃ u : unitIdeles (K := K), i = idelePrincipalEmbedding k * u.1 :=
  exists_principal_mul_unit i (norm_class_eq_one theta htheta hclass hunit i hi)

end NormEuclidean.QuadraticIdeleClassCorrection
