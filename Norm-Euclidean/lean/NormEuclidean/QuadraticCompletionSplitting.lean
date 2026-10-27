import NormEuclidean.ChapterX.QuadraticPlaceCounts
import NormEuclidean.InfiniteUnramifiedSquareClasses

/-!
# Quadratic splitting in actual finite completions and prime fibers

Two extension primes, a square local discriminant, local degree one and
surjectivity of the actual completed-field map are equivalent. The results
include dyadic primes and impose no separate unramifiedness assumption.
-/

noncomputable section

namespace NormEuclidean.QuadraticCompletionSplitting

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm
open scoped NumberField QuadraticAlgebra NormEuclidean.CompletedExtensionProduct

/-- If a quadratic product has two field factors, each factor has degree one. -/
theorem degree_one_of_two_factors {F ι : Type*} [Field F] [Fintype ι]
    (B : ι → Type*) [∀ i, Field (B i)] [∀ i, Algebra F (B i)]
    [∀ i, Module.Finite F (B i)] (theta : Fˣ)
    (e : QuadraticAlgebra F theta.val 0 ≃ₐ[F] ((i : ι) → B i))
    (hcard : Fintype.card ι = 2) (i : ι) : Module.finrank F (B i) = 1 := by
  classical
  have hsum : (∑ j : ι, Module.finrank F (B j)) = 2 := by
    rw [← Module.finrank_pi_fintype]
    exact e.toLinearEquiv.finrank_eq.symm.trans (QuadraticAlgebra.finrank_eq_two _ _)
  have hle (j : ι) (_ : j ∈ Finset.univ) : 1 ≤ Module.finrank F (B j) :=
    Nat.succ_le_of_lt Module.finrank_pos
  have he : (∑ _ : ι, (1 : ℕ)) = ∑ j : ι, Module.finrank F (B j) := by
    simpa [hcard] using hsum.symm
  exact ((Finset.sum_eq_sum_iff_of_le hle).mp he i (Finset.mem_univ i)).symm

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- Two actual extension primes above p are equivalent to a square completed discriminant. -/
theorem card_two_iff_square (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    Nat.card (FinitePlacesAbove (E := QuadraticAlgebra K theta.val 0) p) = 2 ↔
      IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  classical
  rw [QuadraticPlaceCounts.finite_card]
  split_ifs <;> simp_all

/-- The same criterion counts actual prime ideals in the extension integer ring. -/
theorem prime_count_two_iff_square (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (p.asIdeal.primesOver (𝓞 (QuadraticAlgebra K theta.val 0))).ncard = 2 ↔
      IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  have hc := Nat.card_congr
    (finitePlacesAboveEquivPrimesOver (E := QuadraticAlgebra K theta.val 0) p)
  change Nat.card (p.asIdeal.primesOver (𝓞 (QuadraticAlgebra K theta.val 0))) = 2 ↔ _
  rw [← hc]
  exact card_two_iff_square theta htheta p

/-- A split finite prime has degree one at every actual completion above it. -/
theorem degree_one_of_square (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K))
    (hsquare : IsSquare
      (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ∀ w : FinitePlacesAbove (E := QuadraticAlgebra K theta.val 0) p,
      Module.finrank (p.adicCompletion K) (w.1.adicCompletion
        (QuadraticAlgebra K theta.val 0)) = 1 := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro w
  apply degree_one_of_two_factors
    (fun w : FinitePlacesAbove (E := QuadraticAlgebra K theta.val 0) p ↦
      w.1.adicCompletion (QuadraticAlgebra K theta.val 0))
    (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta)
    (CompletedNormImages.finiteEquiv theta htheta p)
  rw [← Nat.card_eq_fintype_card]
  exact (card_two_iff_square theta htheta p).mpr hsquare

/-- A single degree-one completion already forces the quadratic discriminant to split. -/
theorem square_of_degree_one (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ∀ (w : FinitePlacesAbove (E := QuadraticAlgebra K theta.val 0) p),
      Module.finrank (p.adicCompletion K) (w.1.adicCompletion
        (QuadraticAlgebra K theta.val 0)) = 1 →
      IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro w hw
  apply InfiniteUnramifiedSquareClasses.isSquare_of_local_degree_one hw _
    (algebraMap (QuadraticAlgebra K theta.val 0) (w.1.adicCompletion _) ω)
  rw [← map_pow]
  have homega : (ω : QuadraticAlgebra K theta.val 0) ^ 2 =
      algebraMap K _ (theta : K) := by ext <;> simp [pow_two]
  rw [homega]
  exact (finitePlaceAboveCompletionMap_global p w (theta : K)).symm

/-- The degree-one criterion uses the canonical actual completed-field algebra. -/
theorem degree_one_iff_square (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ∀ w : FinitePlacesAbove (E := QuadraticAlgebra K theta.val 0) p,
      Module.finrank (p.adicCompletion K) (w.1.adicCompletion
        (QuadraticAlgebra K theta.val 0)) = 1 ↔
      IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro w
  exact ⟨square_of_degree_one theta htheta p w, fun h ↦ degree_one_of_square theta htheta p h w⟩

/-- Splitting makes the actual finite completed-field inclusion surjective, and conversely. -/
theorem completionMap_surjective_iff_square (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ∀ w : FinitePlacesAbove (E := QuadraticAlgebra K theta.val 0) p,
      Function.Surjective (finitePlaceAboveCompletionMap p w) ↔
      IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro w
  rw [← degree_one_iff_square theta htheta p w]
  constructor
  · intro h
    exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
      ⟨(finitePlaceAboveCompletionMap p w).injective, h⟩
  · intro h
    exact (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h).2

end NormEuclidean.QuadraticCompletionSplitting
