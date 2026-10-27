import NormEuclidean.BoundedVolumeIdeals
import NormEuclidean.FixedRankVolumeFiniteness

/-!
# Fixed-field finiteness for bounded volume in every fixed rank

The hypotheses concern the intrinsic half-polar volume of the original
norm-integral lattice. This proves the fixed-field bounded-volume lemma,
including nonfree lattices. A bound for ordinary class number alone is not
used to supply a rank or volume bound here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.BoundedVolumeFiniteness

open Module FixedFieldRankFiniteness
open scoped NumberField Classical nonZeroDivisors

universe v
variable {K : Type*} [Field K] [NumberField K]

local instance : Module.Free ℤ (integerSubring K) :=
  inferInstanceAs (Module.Free ℤ (𝓞 K))
local instance : Module.Finite ℤ (integerSubring K) :=
  inferInstanceAs (Module.Finite ℤ (𝓞 K))

/-- Finite actual integral-lattice models cover all anisotropic ambient
spaces of the chosen rank and numerical volume bound. -/
theorem exists_finite_models (n : ℕ) (C : ℝ) :
    ∃ A : Set (Model K n), A.Finite ∧
      ∀ (V : Type v) [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
        (L : Lattice (integerSubring K) Q), Q.Anisotropic → finrank K V = n →
        (FractionalIdeal.absNorm L.volumeIdeal : ℝ) ≤ C →
        ∃ M ∈ A, Nonempty (LatticeIsometry Q M.1 L.carrier M.2.carrier) := by
  obtain ⟨S, hS, hvol⟩ := BoundedVolumeIdeals.exists_finite_ideals (K := K) n C
  obtain ⟨A, hA, _, hcover⟩ := FixedRankVolumeFiniteness.exists_finite_models n S hS
  exact ⟨A, hA, fun V _ _ Q L hQ hr hv ↦ hcover V Q L hQ hr (hvol V Q L hr hv)⟩

def classes (n : ℕ) (C : ℝ) : Set (FixedFieldClassSet.ClassSet K n) :=
  {c | ∃ M : Model K n, M.1.Anisotropic ∧
    (FractionalIdeal.absNorm M.2.volumeIdeal : ℝ) ≤ C ∧ FixedFieldClassSet.classOf K M = c}

/-- Equality means an ambient field isometry carrying the entire integral
module onto the entire target module, rather than equality of genera. -/
theorem finite_classes (n : ℕ) (C : ℝ) : (classes (K := K) n C).Finite := by
  obtain ⟨A, hA, hcover⟩ := exists_finite_models (K := K) n C
  apply (hA.image (FixedFieldClassSet.classOf K)).subset
  rintro c ⟨M, hQ, hv, rfl⟩
  obtain ⟨N, hN, hi⟩ := hcover (Fin n → K) M.1 M.2 hQ (by simp) hv
  exact ⟨N, hN, ((FixedFieldClassSet.classOf_eq_iff K M N).mpr hi).symm⟩

/-- Representatives themselves can be chosen inside the original bounded
family, without assuming a free integral module or integral half-polar scale. -/
theorem exists_finite_representatives (n : ℕ) (C : ℝ) :
    ∃ A : Set (Model K n), A.Finite ∧
      (∀ M ∈ A, M.1.Anisotropic ∧ (FractionalIdeal.absNorm M.2.volumeIdeal : ℝ) ≤ C) ∧
      ∀ M : Model K n, M.1.Anisotropic →
        (FractionalIdeal.absNorm M.2.volumeIdeal : ℝ) ≤ C →
        ∃ N ∈ A, Nonempty (LatticeIsometry M.1 N.1 M.2.carrier N.2.carrier) := by
  let D := classes (K := K) n C
  letI : Finite D := finite_classes n C
  let rep (c : D) : Model K n := Classical.choose c.property
  have hrep (c : D) : (rep c).1.Anisotropic ∧
      (FractionalIdeal.absNorm (rep c).2.volumeIdeal : ℝ) ≤ C ∧
      FixedFieldClassSet.classOf K (rep c) = c.val := Classical.choose_spec c.property
  refine ⟨Set.range rep, Set.finite_range _, ?_, ?_⟩
  · rintro M ⟨c, rfl⟩
    exact ⟨(hrep c).1, (hrep c).2.1⟩
  · intro M hQ hv
    let c : D := ⟨FixedFieldClassSet.classOf K M, M, hQ, hv, rfl⟩
    refine ⟨rep c, Set.mem_range_self c, ?_⟩
    exact (FixedFieldClassSet.classOf_eq_iff K M (rep c)).mp (hrep c).2.2.symm

/-- Once a rank upper bound is supplied, a volume bound depending on the
rank still gives finitely many actual classes over the fixed field. -/
theorem finite_bounded_rank_classes (N : ℕ) (C : ℕ → ℝ) :
    {p : (n : ℕ) × FixedFieldClassSet.ClassSet K n |
      p.1 ≤ N ∧ p.2 ∈ classes (K := K) p.1 (C p.1)}.Finite := by
  apply ((Set.finite_Iic N).biUnion fun n _ ↦
    (finite_classes (K := K) n (C n)).image (Sigma.mk n)).subset
  rintro ⟨n, c⟩ ⟨hn, hc⟩
  exact Set.mem_iUnion_of_mem n (Set.mem_iUnion_of_mem hn ⟨c, hc, rfl⟩)

end NormEuclidean.BoundedVolumeFiniteness
