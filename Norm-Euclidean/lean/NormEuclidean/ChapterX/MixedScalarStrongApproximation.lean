import NormEuclidean.ChapterX.FiniteResidueScalarCorrection
import NormEuclidean.ChapterX.ScalarNeighborhoods
import NormEuclidean.ChapterX.IntegralScalarGrowth

/-!
# O'Meara 33:11 and 33:11a with an excluded infinite number-field place

Mixed weak approximation gives an initial scalar. A finite quotient correction
removes its finitely many unwanted denominators while preserving the finite
and infinite targets. Integral perturbations then give arbitrary growth at the
excluded infinite place. All targets are actual completed scalars.

The excluded finite-place branch and global function fields are not asserted.
-/

noncomputable section

namespace NormEuclidean.MixedScalarStrongApproximation

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation
  ScalarNeighborhoods Filter Topology
open scoped WithZero

variable {K : Type*} [Field K] [NumberField K]

/-- The very strong scalar approximation theorem for a number field with
an excluded infinite place. Outside the prescribed finite set, integrality
is proved rather than supplied. Prescribed finite targets may be fractional. -/
theorem exists_scalar (T : Finset (HeightOneSpectrum (integerSubring K)))
    (q : NumberField.InfinitePlace K)
    (x : (v : T) → LocalField (integerSubring K) v.1)
    (W : (v : T) → Set (LocalField (integerSubring K) v.1))
    (hW : ∀ v, W v ∈ 𝓝 (x v))
    (z : (w : {w : NumberField.InfinitePlace K // w ≠ q}) → w.1.Completion)
    (U : (w : {w : NumberField.InfinitePlace K // w ≠ q}) → Set w.1.Completion)
    (hU : ∀ w, U w ∈ 𝓝 (z w)) :
    ∃ a : K, (∀ v : T, algebraMap K (LocalField (integerSubring K) v.1) a ∈ W v) ∧
      (∀ w : {w : NumberField.InfinitePlace K // w ≠ q},
        algebraMap K w.1.Completion a ∈ U w) ∧
      ∀ v : HeightOneSpectrum (integerSubring K), v ∉ T →
        algebraMap K (LocalField (integerSubring K) v) a ∈ LocalRing (integerSubring K) v := by
  classical
  choose O hOW hO hxO using fun v : T ↦ mem_nhds_iff.mp (hW v)
  choose P hPU hP hzP using fun w ↦ mem_nhds_iff.mp (hU w)
  obtain ⟨b, hbO, hbP⟩ := MixedScalarWeakApproximation.exists_finite_infinite T q x O
    (fun v ↦ (hO v).mem_nhds (hxO v)) z P (fun w ↦ (hP w).mem_nhds (hzP w))
  let bad := (finite_nonintegral_places b).toFinset
  let A := bad \ T
  have hTA : Disjoint T A := Finset.disjoint_left.mpr (fun _ ht ha ↦
    (Finset.mem_sdiff.mp ha).2 ht)
  let C (v : T) := {t : LocalField (integerSubring K) v.1 |
    algebraMap K (LocalField (integerSubring K) v.1) b * t ∈ O v}
  have hC (v : T) : C v ∈ 𝓝 (algebraMap K (LocalField (integerSubring K) v.1)
      ((1 : integerSubring K) : K)) := by
    apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
    simpa using (hO v).mem_nhds (hbO v)
  let D (w : {w : NumberField.InfinitePlace K // w ≠ q}) :=
    {t : w.1.Completion | algebraMap K w.1.Completion b * t ∈ P w}
  have hD (w : {w : NumberField.InfinitePlace K // w ≠ q}) :
      D w ∈ 𝓝 (algebraMap K w.1.Completion ((1 : integerSubring K) : K)) := by
    apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
    have h1 : algebraMap K w.1.Completion ((1 : integerSubring K) : K) = 1 :=
      map_one _
    change P w ∈ 𝓝 (algebraMap K w.1.Completion b *
      algebraMap K w.1.Completion ((1 : integerSubring K) : K))
    rw [h1, mul_one]
    exact (hP w).mem_nhds (hbP w)
  choose γ hγ using fun v : T ↦ finite_precision v.1 1 (C v) (hC v)
  choose δ hδ hδbound using fun w ↦ infinite_precision w.1 1 (D w) (hD w)
  let η (w : NumberField.InfinitePlace K) := if h : w ≠ q then δ ⟨w, h⟩ else 1
  have hη (w : NumberField.InfinitePlace K) (hw : w ≠ q) : 0 < η w := by
    simpa only [η, dif_pos hw] using hδ ⟨w, hw⟩
  have hbnonzero (v : A) :
      algebraMap K (LocalField (integerSubring K) v.1) b ≠ 0 := by
    have hbad : algebraMap K (LocalField (integerSubring K) v.1) b ∉
        LocalRing (integerSubring K) v.1 := by
      simpa only [bad, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using
        (Finset.mem_sdiff.mp v.2).1
    intro hz
    exact hbad (hz ▸ (LocalRing (integerSubring K) v.1).zero_mem)
  let θ (v : A) : (ℤᵐ⁰)ˣ := (Units.mk0
    (Valued.v (algebraMap K (LocalField (integerSubring K) v.1) b))
      ((Valuation.ne_zero_iff _).mpr (hbnonzero v)))⁻¹
  obtain ⟨β, hβT, hβA, hβinf⟩ := FiniteResidueScalarCorrection.exists_multiplier
    T A hTA q γ θ η hη
  refine ⟨b * (β : K), ?_, ?_, ?_⟩
  · intro v
    apply hOW v
    rw [map_mul]
    exact hγ v β (hβT v)
  · intro w
    apply hPU w
    rw [map_mul]
    apply hδbound w β
    simpa only [η, dif_pos w.2, Subring.coe_one] using hβinf w.1 w.2
  · intro v hvT
    by_cases hvA : v ∈ A
    · have hβval : Valued.v (algebraMap K (LocalField (integerSubring K) v)
          (β : K)) < (θ ⟨v, hvA⟩ : ℤᵐ⁰) := by
        rw [valuation_algebraMap]
        change v.valuation K (algebraMap (integerSubring K) K β) < _
        rw [HeightOneSpectrum.valuation_of_algebraMap]
        exact hβA ⟨v, hvA⟩
      change Valued.v (algebraMap K (LocalField (integerSubring K) v)
        (b * (β : K))) ≤ 1
      rw [map_mul, map_mul]
      have hpos : 0 < Valued.v (algebraMap K (LocalField (integerSubring K) v) b) :=
        (Valuation.pos_iff _).mpr (hbnonzero ⟨v, hvA⟩)
      have hlt := mul_lt_mul_of_pos_left hβval hpos
      simpa only [θ, Units.val_inv_eq_inv_val, Units.val_mk0,
        mul_inv_cancel₀ hpos.ne'] using hlt.le
    · have hbint : algebraMap K (LocalField (integerSubring K) v) b ∈
          LocalRing (integerSubring K) v := by
        by_contra h
        apply hvA
        exact Finset.mem_sdiff.mpr ⟨by simpa only [bad, Set.Finite.mem_toFinset,
          Set.mem_setOf_eq] using h, hvT⟩
      rw [map_mul]
      exact (LocalRing (integerSubring K) v).mul_mem hbint
        (algebraMap_mem (integerSubring K) v β.property)

set_option backward.isDefEq.respectTransparency false in
/-- The excluded infinite absolute value can also exceed any prescribed bound.
The perturbation is a genuine global integer, so outside-target integrality
survives the additive perturbation. -/
theorem exists_scalar_with_growth (T : Finset (HeightOneSpectrum (integerSubring K)))
    (q : NumberField.InfinitePlace K)
    (x : (v : T) → LocalField (integerSubring K) v.1)
    (W : (v : T) → Set (LocalField (integerSubring K) v.1))
    (hW : ∀ v, W v ∈ 𝓝 (x v))
    (z : (w : {w : NumberField.InfinitePlace K // w ≠ q}) → w.1.Completion)
    (U : (w : {w : NumberField.InfinitePlace K // w ≠ q}) → Set w.1.Completion)
    (hU : ∀ w, U w ∈ 𝓝 (z w)) (B : ℝ) :
    ∃ a : K, (∀ v : T, algebraMap K (LocalField (integerSubring K) v.1) a ∈ W v) ∧
      (∀ w : {w : NumberField.InfinitePlace K // w ≠ q},
        algebraMap K w.1.Completion a ∈ U w) ∧
      (∀ v : HeightOneSpectrum (integerSubring K), v ∉ T →
        algebraMap K (LocalField (integerSubring K) v) a ∈ LocalRing (integerSubring K) v) ∧
      B < q a := by
  classical
  choose O hOW hO hxO using fun v : T ↦ mem_nhds_iff.mp (hW v)
  choose P hPU hP hzP using fun w ↦ mem_nhds_iff.mp (hU w)
  obtain ⟨a, haO, haP, haint⟩ := exists_scalar T q x O
    (fun v ↦ (hO v).mem_nhds (hxO v)) z P (fun w ↦ (hP w).mem_nhds (hzP w))
  let C (v : T) := {t : LocalField (integerSubring K) v.1 |
    algebraMap K (LocalField (integerSubring K) v.1) a + t ∈ O v}
  have hC (v : T) : C v ∈ 𝓝 (algebraMap K (LocalField (integerSubring K) v.1)
      ((0 : integerSubring K) : K)) := by
    apply (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
    simpa using (hO v).mem_nhds (haO v)
  let D (w : {w : NumberField.InfinitePlace K // w ≠ q}) :=
    {t : w.1.Completion | algebraMap K w.1.Completion a + t ∈ P w}
  have hD (w : {w : NumberField.InfinitePlace K // w ≠ q}) :
      D w ∈ 𝓝 (algebraMap K w.1.Completion ((0 : integerSubring K) : K)) := by
    apply (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
    have h0 : algebraMap K w.1.Completion ((0 : integerSubring K) : K) = 0 :=
      map_zero _
    change P w ∈ 𝓝 (algebraMap K w.1.Completion a +
      algebraMap K w.1.Completion ((0 : integerSubring K) : K))
    rw [h0, add_zero]
    exact (hP w).mem_nhds (haP w)
  choose γ hγ using fun v : T ↦ finite_precision v.1 0 (C v) (hC v)
  choose δ hδ hδbound using fun w ↦ infinite_precision w.1 0 (D w) (hD w)
  let η (w : NumberField.InfinitePlace K) := if h : w ≠ q then δ ⟨w, h⟩ else 1
  obtain ⟨p, _, hpT, hpinf, hpq⟩ := IntegralScalarGrowth.exists_large_perturbation T q γ η
    (fun w hw ↦ by simpa only [η, dif_pos hw] using hδ ⟨w, hw⟩) (B + q a)
  refine ⟨a + (p : K), ?_, ?_, ?_, ?_⟩
  · intro v
    apply hOW v
    rw [map_add]
    apply hγ v p
    simpa only [sub_zero] using hpT v
  · intro w
    apply hPU w
    rw [map_add]
    apply hδbound w p
    simpa only [η, dif_pos w.2, Subring.coe_zero, sub_zero] using hpinf w.1 w.2
  · intro v hv
    rw [map_add]
    exact (LocalRing (integerSubring K) v).add_mem (haint v hv)
      (algebraMap_mem (integerSubring K) v p.property)
  · have htri : q (p : K) ≤ q (a + (p : K)) + q a := by
      have h := q.1.add_le (a + (p : K)) (-a)
      rw [add_neg_cancel_comm, map_neg_eq_map] at h
      exact h
    linarith

/-- When finite targets are local integers, the mixed approximation with
growth can be chosen in the actual global integer ring. -/
theorem exists_integer_with_growth (T : Finset (HeightOneSpectrum (integerSubring K)))
    (q : NumberField.InfinitePlace K)
    (x : (v : T) → LocalRing (integerSubring K) v.1)
    (W : (v : T) → Set (LocalField (integerSubring K) v.1))
    (hW : ∀ v, W v ∈ 𝓝 (x v : LocalField (integerSubring K) v.1))
    (z : (w : {w : NumberField.InfinitePlace K // w ≠ q}) → w.1.Completion)
    (U : (w : {w : NumberField.InfinitePlace K // w ≠ q}) → Set w.1.Completion)
    (hU : ∀ w, U w ∈ 𝓝 (z w)) (B : ℝ) :
    ∃ a : integerSubring K,
      (∀ v : T, algebraMap K (LocalField (integerSubring K) v.1) (a : K) ∈ W v) ∧
      (∀ w : {w : NumberField.InfinitePlace K // w ≠ q},
        algebraMap K w.1.Completion (a : K) ∈ U w) ∧ B < q (a : K) := by
  classical
  obtain ⟨a, haT, hainf, haint, haq⟩ := exists_scalar_with_growth T q
    (fun v ↦ (x v : LocalField (integerSubring K) v.1))
    (fun v ↦ W v ∩ LocalRing (integerSubring K) v.1)
    (fun v ↦ inter_mem (hW v)
      ((OrthogonalTopology.isOpen_localRing (integerSubring K) v.1).mem_nhds (x v).property))
    z U hU B
  have ha : a ∈ integerSubring K := mem_of_forall_finite_integral (integerSubring K) a
    (fun v ↦ by
      by_cases hv : v ∈ T
      · exact (haT ⟨v, hv⟩).2
      · exact haint v hv)
  exact ⟨⟨a, ha⟩, fun v ↦ (haT v).1, hainf, haq⟩

end NormEuclidean.MixedScalarStrongApproximation
