import NormEuclidean.ChapterX.MixedScalarStrongApproximation
import NormEuclidean.ChapterX.ResidualScalar

/-!
# Mixed residual scalars with growth for O'Meara 104:3

The proved infinite-excluded branch of 33G is applied to an actual arithmetic
progression. Finite local unit inverses and nonzero infinite embeddings give
the transformed targets. Bezout gives residual divisibility; mixed approximation
and excluded-place growth are conclusions, not input laws.
-/

noncomputable section

namespace NormEuclidean.MixedResidualScalar

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation Filter Topology

variable {K : Type*} [Field K] [NumberField K]

set_option backward.isDefEq.respectTransparency false in
/-- An actual integral arithmetic progression has arbitrary finite integral
and other-infinite completed targets, with arbitrary growth at q. -/
theorem exists_congruence_with_growth
    (T : Finset (HeightOneSpectrum (integerSubring K))) (q : NumberField.InfinitePlace K)
    (m b : integerSubring K) (hm0 : m ≠ 0) (hm : ∀ v ∈ T, m ∉ v.asIdeal)
    (x : (v : T) → LocalRing (integerSubring K) v.1)
    (W : (v : T) → Set (LocalField (integerSubring K) v.1))
    (hW : ∀ v, W v ∈ 𝓝 (x v : LocalField (integerSubring K) v.1))
    (z : (w : {w : NumberField.InfinitePlace K // w ≠ q}) → w.1.Completion)
    (U : (w : {w : NumberField.InfinitePlace K // w ≠ q}) → Set w.1.Completion)
    (hU : ∀ w, U w ∈ 𝓝 (z w)) (B : ℝ) :
    ∃ β : integerSubring K, (∃ r : integerSubring K, β - b = m * r) ∧
      (∀ v : T, algebraMap K (LocalField (integerSubring K) v.1) (β : K) ∈ W v) ∧
      (∀ w : {w : NumberField.InfinitePlace K // w ≠ q},
        algebraMap K w.1.Completion (β : K) ∈ U w) ∧ B < q (β : K) := by
  classical
  have hmK : (m : K) ≠ 0 := by exact_mod_cast hm0
  have hu (v : T) : IsUnit (integerMap (integerSubring K) v.1 m) :=
    isUnit_algebraMap_localRing (integerSubring K) v.1 (hm v.1 v.2)
  let u (v : T) : (LocalRing (integerSubring K) v.1)ˣ := (hu v).unit
  let y (v : T) := (↑((u v)⁻¹) : LocalRing (integerSubring K) v.1) *
    (x v - integerMap (integerSubring K) v.1 b)
  have hxy (v : T) : integerMap (integerSubring K) v.1 m * y v +
      integerMap (integerSubring K) v.1 b = x v := by
    rw [← (hu v).unit_spec]
    change (u v : LocalRing (integerSubring K) v.1) *
      ((↑((u v)⁻¹) : LocalRing (integerSubring K) v.1) *
        (x v - integerMap (integerSubring K) v.1 b)) +
          integerMap (integerSubring K) v.1 b = x v
    rw [← mul_assoc, Units.mul_inv, one_mul, sub_add_cancel]
  let f (v : T) (s : LocalField (integerSubring K) v.1) :=
    algebraMap K (LocalField (integerSubring K) v.1) (m : K) * s +
      algebraMap K (LocalField (integerSubring K) v.1) (b : K)
  have hfy (v : T) : f v (y v) = x v :=
    congrArg (fun s : LocalRing (integerSubring K) v.1 ↦
      (s : LocalField (integerSubring K) v.1)) (hxy v)
  have hW' (v : T) : f v ⁻¹' W v ∈ 𝓝 (y v : LocalField (integerSubring K) v.1) := by
    have hf : Continuous (f v) :=
      (continuous_const.mul continuous_id).add continuous_const
    apply hf.continuousAt.preimage_mem_nhds
    simpa only [hfy] using hW v
  let t (w : {w : NumberField.InfinitePlace K // w ≠ q}) :=
    (z w - algebraMap K w.1.Completion (b : K)) /
      algebraMap K w.1.Completion (m : K)
  let g (w : {w : NumberField.InfinitePlace K // w ≠ q}) (s : w.1.Completion) :=
    algebraMap K w.1.Completion (m : K) * s + algebraMap K w.1.Completion (b : K)
  have hgt (w : {w : NumberField.InfinitePlace K // w ≠ q}) : g w (t w) = z w := by
    have hmw : algebraMap K w.1.Completion (m : K) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K w.1.Completion).injective).mpr hmK
    dsimp only [g, t]
    rw [mul_div_cancel₀ _ hmw, sub_add_cancel]
  have hU' (w : {w : NumberField.InfinitePlace K // w ≠ q}) :
      g w ⁻¹' U w ∈ 𝓝 (t w) := by
    have hg : Continuous (g w) :=
      (continuous_const.mul continuous_id).add continuous_const
    apply hg.continuousAt.preimage_mem_nhds
    simpa only [hgt] using hU w
  have hqm : 0 < q (m : K) := q.1.pos hmK
  obtain ⟨r, hrT, hrinf, hrq⟩ := MixedScalarStrongApproximation.exists_integer_with_growth
    T q y (fun v ↦ f v ⁻¹' W v) hW' t (fun w ↦ g w ⁻¹' U w) hU'
      ((B + q (b : K)) / q (m : K))
  refine ⟨m * r + b, ⟨r, by ring⟩, ?_, ?_, ?_⟩
  · intro v
    have h := hrT v
    change f v (algebraMap K (LocalField (integerSubring K) v.1) (r : K)) ∈ W v at h
    change algebraMap K (LocalField (integerSubring K) v.1)
      ((m : K) * (r : K) + (b : K)) ∈ W v
    simpa only [f, map_add, map_mul] using h
  · intro w
    have h := hrinf w
    change g w (algebraMap K w.1.Completion (r : K)) ∈ U w at h
    change algebraMap K w.1.Completion ((m : K) * (r : K) + (b : K)) ∈ U w
    simpa only [g, map_add, map_mul] using h
  · have hlarge : B + q (b : K) < q ((m : K) * (r : K)) := by
      rw [map_mul]
      exact (div_lt_iff₀ hqm).mp hrq |>.trans_eq (mul_comm _ _)
    have htri : q ((m : K) * (r : K)) ≤
        q ((m : K) * (r : K) + (b : K)) + q (b : K) := by
      have h := q.1.add_le ((m : K) * (r : K) + (b : K)) (-(b : K))
      rw [add_neg_cancel_right, map_neg_eq_map] at h
      exact h
    change B < q ((m : K) * (r : K) + (b : K))
    linarith

/-- The scalar needed in 104:3 is built with actual mixed completed targets,
residual divisibility and excluded infinite-place growth. It is globally integral. -/
theorem exists_divisible_residual_scalar
    (T : Finset (HeightOneSpectrum (integerSubring K))) (q : NumberField.InfinitePlace K)
    (c m : integerSubring K) (hm0 : m ≠ 0) (hcm : IsCoprime c m)
    (hm : ∀ v ∈ T, m ∉ v.asIdeal)
    (x : (v : T) → LocalRing (integerSubring K) v.1)
    (W : (v : T) → Set (LocalField (integerSubring K) v.1))
    (hW : ∀ v, W v ∈ 𝓝 (x v : LocalField (integerSubring K) v.1))
    (z : (w : {w : NumberField.InfinitePlace K // w ≠ q}) → w.1.Completion)
    (U : (w : {w : NumberField.InfinitePlace K // w ≠ q}) → Set w.1.Completion)
    (hU : ∀ w, U w ∈ 𝓝 (z w)) (B : ℝ) :
    ∃ β : integerSubring K,
      (∃ d : integerSubring K, 1 - (c : K) ^ 2 * (β : K) ^ 2 = (m : K) * (d : K)) ∧
      (∀ v : T, algebraMap K (LocalField (integerSubring K) v.1) (β : K) ∈ W v) ∧
      (∀ w : {w : NumberField.InfinitePlace K // w ≠ q},
        algebraMap K w.1.Completion (β : K) ∈ U w) ∧ B < q (β : K) := by
  obtain ⟨b, d, hbd⟩ := hcm
  obtain ⟨β, ⟨r, hr⟩, hβT, hβinf, hβq⟩ := exists_congruence_with_growth
    T q m b hm0 hm x W hW z U hU B
  have hβeq : β = b + m * r := by linear_combination hr
  have hdiv : 1 - c ^ 2 * β ^ 2 = m * ((d - c * r) * (1 + c * β)) := by
    calc
      1 - c ^ 2 * β ^ 2 = (1 - c * β) * (1 + c * β) := by ring
      _ = (m * (d - c * r)) * (1 + c * β) := by
        congr 1
        rw [hβeq]
        linear_combination -hbd
      _ = _ := by ring
  exact ⟨β, ⟨(d - c * r) * (1 + c * β),
    congrArg (fun s : integerSubring K ↦ (s : K)) hdiv⟩, hβT, hβinf, hβq⟩

end NormEuclidean.MixedResidualScalar
