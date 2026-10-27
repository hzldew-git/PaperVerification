import NormEuclidean.ChapterX.DyadicNormIndices
import NormEuclidean.ChapterX.OddRamifiedNormIndices
import NormEuclidean.ChapterX.InfiniteNormIndices
import NormEuclidean.ChapterX.NormIndexProduct

/-!
# O'Meara 65:8 for the actual quadratic S-idele norm

All local indices are computed, including nonsplit dyadic and infinite
places and odd parameters of arbitrary valuation. Their finite product is
the literal power of two indexed by nonsplit excluded places. Positivity
of this count and the exact S-unit norm index are separate obligations.
-/

noncomputable section

namespace NormEuclidean.SNormIndex

open IsDedekindDomain Bong.Dyadic QuadraticExtensionNorm ExtensionIdeleNorm NormIndexProduct
open scoped NumberField NormEuclidean.NormIndexProduct

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- The actual norm fiber index at every finite place, with no good-place
or oddness restriction. -/
theorem finite_index (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (finitePlaceFiberNormUnits (E := QuadraticAlgebra K theta.val 0) p).range.index =
      (by
        classical
        exact if IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta)
          then 1 else 2) := by
  classical
  by_cases hp : (2 : 𝓞 K) ∈ p.asIdeal
  · exact DyadicNormIndices.finite_dyadic_index theta htheta p hp
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  have heq : (finitePlaceFiberNormUnits (E := QuadraticAlgebra K theta.val 0) p).range =
      quadraticNormGroup (p.adicCompletion K)
        (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta) := by
    ext a
    exact CompletedNormImages.finite_norm_range_iff theta htheta p a
  rw [heq]
  exact OddRamifiedNormIndices.quadraticNormGroup_index p hp _

/-- The image of the parameter in each actual local factor of 65:8. -/
def localParameter (theta : Kˣ) {S : Set (HeightOneSpectrum (𝓞 K))}
    (q : Index S) : UnitsAt q := match q with
  | .inl p => Units.map (algebraMap K (p.1.adicCompletion K)).toMonoidHom theta
  | .inr v => Units.map (algebraMap K v.Completion).toMonoidHom theta

/-- Every factor in the actual local norm product has its computed index. -/
theorem local_index (theta : Kˣ) {S : Set (HeightOneSpectrum (𝓞 K))} (q : Index S) :
    (localNormGroup theta q).index =
      (by
        classical
        exact if IsSquare (localParameter theta q) then 1 else 2) := by
  classical
  cases q with
  | inl p =>
      by_cases hp : (2 : 𝓞 K) ∈ p.1.asIdeal
      · exact DyadicNormIndices.quadraticNormGroup_index p.1 hp _
      · exact OddRamifiedNormIndices.quadraticNormGroup_index p.1 hp _
  | inr v => exact InfiniteNormIndices.quadraticNormGroup_index v _

/-- The number b of nonsplit excluded finite places and nonsplit infinite
places. A finite S-complement is used literally, rather than a supplied b. -/
def nonsplitCount (theta : Kˣ) (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite) : ℕ := by
  classical
  letI : Fintype ↥(Sᶜ) := hS.fintype
  exact (Finset.univ.filter (fun q : Index S ↦ ¬ IsSquare (localParameter theta q))).card

/-- The local product equals the explicit power of two, without requiring
positivity of b as an input. -/
theorem local_product (theta : Kˣ) (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite) :
    letI : Fintype ↥(Sᶜ) := hS.fintype
    ∏ q : Index S, (localNormGroup theta q).index = 2 ^ nonsplitCount theta S hS := by
  classical
  letI : Fintype ↥(Sᶜ) := hS.fintype
  simp_rw [local_index]
  simp only [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const,
    nonsplitCount]

/-- O'Meara 65:8: the actual quadratic S-idele norm subgroup has relative
index 2^b for cofinite good S. All local and product inputs are proved. -/
theorem index_eq_pow (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite)
    (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal)
    (hunit : ∀ p ∈ S, p.valuation K theta.val = 1) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (sIdeleNormSubgroup (E := QuadraticAlgebra K theta.val 0) S).relIndex
      (finitePlaceSIdeleSubgroup S) = 2 ^ nonsplitCount theta S hS := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  rw [NormIndexProduct.index_product theta htheta S hS htwo hunit]
  exact local_product theta S hS

end NormEuclidean.SNormIndex
