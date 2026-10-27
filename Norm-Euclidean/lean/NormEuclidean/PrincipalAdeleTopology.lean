import NormEuclidean.FiniteAdelicCharacterTopology
import NormEuclidean.CompletedHaarDensity
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Principal global adeles form a closed discrete subgroup

The isolating neighborhood is small at every infinite place and
integral at every finite place. Global integrality and the nonzero
integer norm contradict simultaneous archimedean smallness. No
discreteness or quotient-volume premise is assumed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.PrincipalAdeleTopology

open NumberField IsDedekindDomain Bong.NumberFieldCompletion
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField Classical

variable (F : Type*) [Field F] [NumberField F]

scoped instance infiniteT2 : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((w : InfinitePlace F) → w.Completion))

scoped instance finiteT2 : T2Space (FiniteAdeleRing (𝓞 F) F) := by
  unfold FiniteAdeleRing
  infer_instance

open scoped NormEuclidean.PrincipalAdeleTopology

scoped instance adeleT2 : T2Space (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

scoped instance adeleNontrivial : Nontrivial (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (Nontrivial (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

/-- Compact original completed integers give actual local compactness of the finite adeles. -/
scoped instance finiteLocallyCompact : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := by
  letI (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) :=
    CompletedHaarDensity.completedCompact v
  letI : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring (v.adicCompletion F)⟩
  unfold FiniteAdeleRing
  infer_instance

scoped instance adeleLocallyCompact : LocallyCompactSpace (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

/-- Global integrality is detected in the actual original finite completions. -/
theorem finite_integral_iff (x : F) :
    (∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) x ∈ integerRing v) ↔
      ∃ a : 𝓞 F, (a : F) = x := by
  constructor
  · intro hx
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) x
    intro v
    have h := hx v
    change Valued.v (x : v.adicCompletion F) ≤ 1 at h
    rwa [HeightOneSpectrum.adicCompletion.valued_coe F v] at h
  · rintro ⟨a, rfl⟩ v
    exact (integerEmbedding v a).property

/-- A nonzero element integral at all finite places has absolute global norm at least one. -/
theorem norm_lower_bound (x : F) (hx : x ≠ 0)
    (hi : ∀ v : HeightOneSpectrum (𝓞 F),
      algebraMap F (v.adicCompletion F) x ∈ integerRing v) :
    1 ≤ |(Algebra.norm ℚ x : ℝ)| := by
  obtain ⟨a, rfl⟩ := (finite_integral_iff F x).mp hi
  have hn : Algebra.norm ℤ a ≠ 0 := by
    intro h
    have h0 : Algebra.norm ℚ (a : F) = 0 := by rw [← Algebra.coe_norm_int a, h]; rfl
    exact hx (Algebra.norm_eq_zero_iff.mp h0)
  rw [← Algebra.coe_norm_int a, Rat.cast_intCast]
  exact_mod_cast Int.one_le_abs hn

theorem norm_infinite_diagonal (w : InfinitePlace F) (x : F) :
    ‖algebraMap F w.Completion x‖ = w x := by
  change ‖((WithAbs.equiv w.1).symm x : w.Completion)‖ = _
  rw [norm_coe]
  rfl

/-- The actual neighborhood small at infinity and integral at all finite places. -/
def isolatingNeighborhood : Set (AdeleRing (𝓞 F) F) :=
  {a | (∀ w : InfinitePlace F, ‖a.1 w‖ < 1) ∧
    ∀ v : HeightOneSpectrum (𝓞 F), a.2 v ∈ integerRing v}

theorem isolatingNeighborhood_open : IsOpen (isolatingNeighborhood F) := by
  have hi : IsOpen {a : InfiniteAdeleRing F | ∀ w : InfinitePlace F, ‖a w‖ < 1} := by
    rw [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro w
    exact isOpen_lt (continuous_apply w).norm continuous_const
  exact (hi.preimage continuous_fst).inter
    (FiniteAdelicCharacterTopology.integral_open.preimage continuous_snd)

theorem zero_mem : (0 : AdeleRing (𝓞 F) F) ∈ isolatingNeighborhood F := by
  constructor
  · intro w
    change ‖(0 : w.Completion)‖ < 1
    simp
  · intro v
    change (0 : v.adicCompletion F) ∈ integerRing v
    exact (integerRing v).zero_mem

/-- The neighborhood meets the principal global field only at zero. -/
theorem principal_mem_iff (x : F) :
    algebraMap F (AdeleRing (𝓞 F) F) x ∈ isolatingNeighborhood F ↔ x = 0 := by
  constructor
  · intro hx
    by_contra h0
    have hlo := norm_lower_bound F x h0 hx.2
    have hhi : |(Algebra.norm ℚ x : ℝ)| < 1 := by
      have h := Finset.prod_lt_prod_of_nonempty
        (fun (w : InfinitePlace F) _ ↦ pow_pos (pos_iff.mpr h0) w.mult)
        (fun (w : InfinitePlace F) _ ↦
          pow_lt_one₀ (apply_nonneg w x)
            ((norm_infinite_diagonal F w x) ▸ hx.1 w) mult_ne_zero)
        Finset.univ_nonempty
      simpa only [Finset.prod_const_one, InfinitePlace.prod_eq_abs_norm, Rat.cast_abs] using h
    exact (not_lt_of_ge hlo) hhi
  · rintro rfl
    rw [map_zero]
    exact zero_mem F

/-- The actual principal adelic subgroup is discrete, without an assumed embedding theorem. -/
theorem principal_discrete : DiscreteTopology (AdeleRing.principalSubgroup (𝓞 F) F) := by
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  have he : (Subtype.val : AdeleRing.principalSubgroup (𝓞 F) F → AdeleRing (𝓞 F) F) ⁻¹'
      isolatingNeighborhood F = {0} := by
    ext a
    obtain ⟨x, hx⟩ := a.property
    change (a : AdeleRing (𝓞 F) F) ∈ isolatingNeighborhood F ↔ a = 0
    rw [← hx, principal_mem_iff]
    constructor
    · rintro rfl
      apply Subtype.ext
      change (a : AdeleRing (𝓞 F) F) = 0
      simpa only [map_zero] using hx.symm
    · intro h
      apply (algebraMap F (AdeleRing (𝓞 F) F)).injective
      simpa only [h, ZeroMemClass.coe_zero, map_zero] using hx
  rw [← he]
  exact (isolatingNeighborhood_open F).preimage continuous_subtype_val

attribute [local instance] principal_discrete

/-- Discreteness in the actual Hausdorff adele group gives closedness of principal adeles. -/
theorem principal_closed : IsClosed (AdeleRing.principalSubgroup (𝓞 F) F :
    Set (AdeleRing (𝓞 F) F)) := AddSubgroup.isClosed_of_discrete

/-- The quotient by actual principal adeles is Hausdorff, without a closedness premise. -/
theorem quotient_t2 : T2Space (AdeleRing (𝓞 F) F ⧸
    AdeleRing.principalSubgroup (𝓞 F) F) := by
  letI := principal_closed F
  infer_instance

/-- The actual principal quotient is locally compact; no volume normalization is chosen. -/
theorem quotient_locallyCompact : LocallyCompactSpace (AdeleRing (𝓞 F) F ⧸
    AdeleRing.principalSubgroup (𝓞 F) F) := inferInstance

end NormEuclidean.PrincipalAdeleTopology
