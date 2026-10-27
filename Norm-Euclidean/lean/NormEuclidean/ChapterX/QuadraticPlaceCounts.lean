import NormEuclidean.ChapterX.CompletedNormUnitLifting
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Actual place counts in a quadratic extension

The completed algebra has dimension two. Each field factor contributes at
least one dimension. A nonsplit algebra is a field and has one factor; a
split algebra has zero divisors and cannot have only one field factor.
-/

noncomputable section

namespace NormEuclidean.QuadraticPlaceCounts

open IsDedekindDomain QuadraticExtensionNorm ExtensionIdeleNorm
open scoped NumberField QuadraticAlgebra NormEuclidean.CompletedExtensionProduct
  NormEuclidean.InfiniteCompletedNorm NumberField.LiesOver

/-- A product decomposition of a quadratic algebra has one or two field
factors, according to nonsquareness or squareness of the parameter. -/
theorem card_factors {F ι : Type*} [Field F] [CharZero F] [Fintype ι]
    (B : ι → Type*) [∀ i, Field (B i)] [∀ i, Algebra F (B i)]
    [∀ i, Module.Finite F (B i)] (theta : Fˣ)
    (e : QuadraticAlgebra F theta.val 0 ≃ₐ[F] ((i : ι) → B i)) :
    Fintype.card ι = (by
      classical
      exact if IsSquare theta then 2 else 1) := by
  classical
  letI : Nonempty ι := by
    by_contra h
    letI : IsEmpty ι := not_nonempty_iff.mp h
    have he : e 1 = e 0 := Subsingleton.elim _ _
    exact one_ne_zero (e.injective he)
  have hdim : Module.finrank F ((i : ι) → B i) = 2 :=
    e.toLinearEquiv.finrank_eq.symm.trans (QuadraticAlgebra.finrank_eq_two _ _)
  have hcard : Fintype.card ι ≤ 2 := by
    rw [← hdim, Module.finrank_pi_fintype]
    calc
      Fintype.card ι = ∑ i : ι, 1 := by simp
      _ ≤ ∑ i : ι, Module.finrank F (B i) :=
        Finset.sum_le_sum (fun i _ ↦
          Nat.succ_le_of_lt (show 0 < Module.finrank F (B i) from Module.finrank_pos))
  split_ifs with hs
  · have hnot : ¬ Subsingleton ι := by
      intro hi
      letI := hi
      let i₀ : ι := Classical.choice inferInstance
      have heval : Function.Injective (fun z ↦ e z i₀) := by
        intro x y h
        apply e.injective
        funext i
        cases Subsingleton.elim i i₀
        exact h
      obtain ⟨r, hr⟩ := hs
      let a : QuadraticAlgebra F theta.val 0 := ω - algebraMap F _ r.val
      let b : QuadraticAlgebra F theta.val 0 := ω + algebraMap F _ r.val
      have hab : a * b = 0 := by
        have ht : theta.val = r.val * r.val := congrArg Units.val hr
        ext <;> simp [a, b, ht] <;> ring
      have h := congrArg (fun z ↦ e z i₀) hab
      simp only [map_mul, Pi.mul_apply, map_zero, Pi.zero_apply] at h
      rcases mul_eq_zero.mp h with ha | hb
      · have ha0 : a = 0 := heval (ha.trans (by simp))
        have hh := congrArg QuadraticAlgebra.im ha0
        simpa [a] using hh
      · have hb0 : b = 0 := heval (hb.trans (by simp))
        have hh := congrArg QuadraticAlgebra.im hb0
        simpa [b] using hh
    have htwo : 2 ≤ Fintype.card ι := by
      by_contra! h
      exact hnot (Fintype.card_le_one_iff_subsingleton.mp (by omega))
    exact le_antisymm hcard htwo
  · letI : Fact (∀ r : F, r ^ 2 ≠ theta.val + 0 * r) :=
      ⟨nonsquare_quadraticAlgebra_field_fact theta hs⟩
    letI : IsDomain ((i : ι) → B i) := e.symm.toRingEquiv.toMulEquiv.isDomain _
    letI : Subsingleton ι := SplitNormUnits.subsingleton_of_pi_domain B
    have hle : Fintype.card ι ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr inferInstance
    have hpos : 0 < Fintype.card ι := Fintype.card_pos
    omega

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- The actual finite place fiber has cardinality one or two, as computed
by the local quadratic parameter. -/
theorem finite_card (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K)) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    Nat.card (FinitePlacesAbove (E := QuadraticAlgebra K theta.val 0) p) =
      (by
        classical
        exact if IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta)
          then 2 else 1) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  rw [Nat.card_eq_fintype_card]
  exact card_factors
    (fun w : FinitePlacesAbove (E := QuadraticAlgebra K theta.val 0) p ↦
      w.1.adicCompletion (QuadraticAlgebra K theta.val 0))
    (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta)
    (CompletedNormImages.finiteEquiv theta htheta p)

/-- The same count for the actual infinite place fiber. -/
theorem infinite_card (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (v : NumberField.InfinitePlace K) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    Nat.card (InfinitePlacesAbove (E := QuadraticAlgebra K theta.val 0) v) =
      (by
        classical
        exact if IsSquare (Units.map (algebraMap K v.Completion).toMonoidHom theta)
          then 2 else 1) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  rw [Nat.card_eq_fintype_card]
  exact card_factors
    (fun w : InfinitePlacesAbove (E := QuadraticAlgebra K theta.val 0) v ↦ w.1.Completion)
    (Units.map (algebraMap K v.Completion).toMonoidHom theta)
    (CompletedNormImages.infiniteEquiv theta htheta v)

end NormEuclidean.QuadraticPlaceCounts
