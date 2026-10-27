import NormEuclidean.ChapterX.CompletedTopology
import NormEuclidean.CompletionDescent
import NormEuclidean.LocalIntegrality

/-!
# The fixed-value construction in O'Meara 104:3

This file records the exact algebraic construction and its actual-completion
membership and neighborhood control. Arithmetic existence of the scalar
and the orthogonal representation required by 104:3 is a separate input.
No full vector approximation principle is asserted here.
-/

noncomputable section

namespace NormEuclidean.FixedValueVectors

open IsDedekindDomain CompletedIntegralLattice Filter Topology
open scoped NormEuclidean.OrthogonalTopology

section Membership

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]

/-- Completed membership at all finite places recovers membership in the
actual global submodule. No finite-generation or freeness premise is needed. -/
theorem mem_of_all_completed (hR : ¬ IsField R) (L : Submodule R V) (x : V)
    (hx : ∀ v : HeightOneSpectrum R, inclusion R v x ∈ carrier R v L) : x ∈ L := by
  let N := L ⊔ Submodule.span R {x}
  have hLN : L ≤ N := le_sup_left
  have hcar : ∀ v : HeightOneSpectrum R, carrier R v L = carrier R v N := by
    intro v
    apply le_antisymm
    · exact Submodule.span_mono (Set.image_mono (fun y hy ↦ hLN hy))
    · apply Submodule.span_le.mpr
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨l, hl, r, hr, hsum⟩ := Submodule.mem_sup.mp hy
      obtain ⟨a, hax⟩ := Submodule.mem_span_singleton.mp hr
      rw [← hsum, ← hax, inclusion_add, inclusion_smul]
      exact (carrier R v L).add_mem (inclusion_mem R v L hl)
        ((carrier R v L).smul_mem _ (hx v))
  have heq : L = N := CompletionDescent.submodule_eq_of_completed_carriers_eq R hR hcar
  have hSN : Submodule.span R {x} ≤ N := le_sup_right
  have hxN : x ∈ N := hSN (Submodule.subset_span (Set.mem_singleton x))
  rwa [← heq] at hxN

theorem mem_iff_all_completed (hR : ¬ IsField R) (L : Submodule R V) (x : V) :
    x ∈ L ↔ ∀ v : HeightOneSpectrum R, inclusion R v x ∈ carrier R v L :=
  ⟨fun hx v ↦ inclusion_mem R v L hx, mem_of_all_completed R hR L x⟩

end Membership

section Algebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

/-- The identity in O'Meara 104:3, step 5. Orthogonality makes the
correction have precisely the prescribed quadratic value. -/
theorem value_of_orthogonal_correction (v y : V) (c β a : K)
    (hv : Q v = c ^ 2 * a) (hy : Q y = a * (1 - c ^ 2 * β ^ 2))
    (horth : QuadraticMap.polar Q v y = 0) : Q (β • v + y) = a := by
  rw [QuadraticMap.map_add (Q : V → K), Q.map_smul, Q.polar_smul_left, hv, hy, horth]
  simp only [smul_eq_mul, mul_zero, add_zero]
  ring

/-- A represented residual value in the orthogonal submodule yields an
actual global integral vector of the target value. The representation premise
is explicit; supplying it is part of the missing arithmetic argument. -/
theorem exists_fixed_value_of_orthogonal_representation (R : Subring K)
    (L U : Submodule R V) (hU : U ≤ L) (v : V) (hvL : v ∈ L) (c a : K) (β : R)
    (hv : Q v = c ^ 2 * a) (horth : ∀ y ∈ U, QuadraticMap.polar Q v y = 0)
    (hrep : ∃ y ∈ U, Q y = a * (1 - c ^ 2 * (β : K) ^ 2)) :
    ∃ z ∈ L, Q z = a := by
  obtain ⟨y, hy, hQy⟩ := hrep
  refine ⟨(β : K) • v + y, L.add_mem (L.smul_mem β hvL) (hU hy), ?_⟩
  exact value_of_orthogonal_correction Q v y c β a hv hQy (horth y hy)

end Algebra

section Topology

variable {F E : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [AddCommGroup E] [Module F E] [TopologicalSpace E] [IsModuleTopology F E]

omit [IsTopologicalRing F] in
/-- The two tolerances used in 104:3, step 5, for the affine correction
`β • v + y`. They are ordinary module-topology neighborhoods. -/
theorem exists_correction_neighborhoods (v : E) (W : Set E) (hW : W ∈ 𝓝 v) :
    ∃ (B : Set F) (Y : Set E), B ∈ 𝓝 (1 : F) ∧ Y ∈ 𝓝 (0 : E) ∧
      ∀ β ∈ B, ∀ y ∈ Y, β • v + y ∈ W := by
  letI := IsModuleTopology.topologicalAddGroup F E
  have hc : Continuous (fun p : F × E ↦ p.1 • v + p.2) :=
    (continuous_fst.smul continuous_const).add continuous_snd
  have hp : (fun p : F × E ↦ p.1 • v + p.2) ⁻¹' W ∈ 𝓝 ((1 : F), (0 : E)) :=
    hc.continuousAt.preimage_mem_nhds (by simpa only [one_smul, add_zero] using hW)
  obtain ⟨B, hB, Y, hY, hBY⟩ := mem_nhds_prod_iff.mp hp
  refine ⟨B, Y, hB, hY, ?_⟩
  intro β hβ y hy
  have hpoint : (β, y) ∈ B ×ˢ Y := ⟨hβ, hy⟩
  exact hBY hpoint

end Topology

end NormEuclidean.FixedValueVectors
