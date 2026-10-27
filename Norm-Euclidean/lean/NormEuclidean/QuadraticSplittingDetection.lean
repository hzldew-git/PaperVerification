import NormEuclidean.ChapterX.SquarePrimeSelection

/-!
# Quadratic square classes detected by splitting primes

The proved simultaneous prime selection separates two independent square
classes outside any finite exceptional set. Thus inclusion of the finite
completed splitting sets detects containment of quadratic square classes.
No Chebotarev or class-field input is supplied.
-/

noncomputable section

namespace NormEuclidean.QuadraticSplittingDetection

open IsDedekindDomain ExtensionIdeleNorm SquarePrimeSelection
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- Two independent square classes are separated by an actual prime outside any finite set. -/
theorem exists_separating_prime (theta eta : Kˣ)
    (heta : ¬ IsSquare eta) (hprod : ¬ IsSquare (eta * theta))
    (T : Set (HeightOneSpectrum (𝓞 K))) (hT : T.Finite) :
    ∃ p ∉ T,
      IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta) ∧
      ¬ IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom eta) := by
  classical
  let bad := T ∪ {p : HeightOneSpectrum (𝓞 K) | (2 : 𝓞 K) ∈ p.asIdeal} ∪
    {p | p.valuation K (eta : K) ≠ 1} ∪ {p | p.valuation K (theta : K) ≠ 1}
  have hbad : bad.Finite := ((hT.union finite_dyadic_primes).union
    (CofiniteLocalIsotropy.finite_nonunit_valuations (eta : K) eta.ne_zero)).union
      (CofiniteLocalIsotropy.finite_nonunit_valuations (theta : K) theta.ne_zero)
  let S := badᶜ
  have hgood (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ S) :
      p ∉ T ∧ (2 : 𝓞 K) ∉ p.asIdeal ∧
        p.valuation K (eta : K) = 1 ∧ p.valuation K (theta : K) = 1 := by
    simpa only [S, bad, Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq,
      not_or, not_not, and_assoc] using hp
  have hav : AvoidsSquares eta [theta] := by
    intro C hC
    rcases List.sublist_singleton.mp hC with rfl | rfl
    · simpa using heta
    · simpa using hprod
  obtain ⟨p, hp, hns, hs⟩ := exists_pattern 1 eta [theta] (by simp) hav S
    (by simpa only [S, compl_compl] using hbad)
    (fun p hp ↦ (hgood p hp).2.1) (fun p hp ↦ (hgood p hp).2.2.1)
    (by
      intro b hb
      obtain rfl := List.mem_singleton.mp hb
      exact fun p hp ↦ (hgood p hp).2.2.2)
  exact ⟨p, (hgood p hp).1, hs theta (by simp), hns⟩

/-- Almost-everywhere inclusion of quadratic splitting primes detects the global square class. -/
theorem square_or_mul_of_eventually_split_imp (theta eta : Kˣ)
    (h : ∀ᶠ p : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta) →
        IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom eta)) :
    IsSquare eta ∨ IsSquare (eta * theta) := by
  by_contra! hn
  let T : Set (HeightOneSpectrum (𝓞 K)) := {p | ¬
    (IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta) →
      IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom eta))}
  have hT : T.Finite := Filter.eventually_cofinite.mp h
  obtain ⟨p, hp, htheta, heta⟩ := exists_separating_prime theta eta hn.1 hn.2 T hT
  exact heta ((not_not.mp hp) htheta)

/-- The detected square-class relation gives splitting inclusion at every finite prime. -/
theorem split_imp_of_square_or_mul (theta eta : Kˣ)
    (h : IsSquare eta ∨ IsSquare (eta * theta)) (p : HeightOneSpectrum (𝓞 K))
    (htheta : IsSquare
      (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta)) :
    IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom eta) := by
  rcases h with h | h
  · exact h.map _
  · have hs := (h.map (Units.map
      (algebraMap K (p.adicCompletion K)).toMonoidHom)).mul htheta.inv
    simpa only [map_mul, mul_inv_cancel_right] using hs

/-- The quadratic splitting-set containment criterion, allowing finitely many exceptions. -/
theorem eventually_split_imp_iff (theta eta : Kˣ) :
    (∀ᶠ p : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta) →
        IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom eta)) ↔
      IsSquare eta ∨ IsSquare (eta * theta) := by
  constructor
  · exact square_or_mul_of_eventually_split_imp theta eta
  · intro h
    exact Filter.Eventually.of_forall (split_imp_of_square_or_mul theta eta h)

end NormEuclidean.QuadraticSplittingDetection
