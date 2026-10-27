import NormEuclidean.ChapterX.ReflectionApproximation
import NormEuclidean.ChapterX.CompletedTopology

/-!
# Passing vector approximation to actual rotation neighborhoods in 104:4

Fixed-value fiber neighborhoods are replaced by ambient vector neighborhoods.
At the actual finite completions, any global equal-value vector meeting these
neighborhoods yields the prescribed proper reflection-pair neighborhoods and
has trivial global Wall spinor norm. Existence of that global vector remains
the separate 104:3 step.
-/

noncomputable section


namespace NormEuclidean.ReflectionVectorNeighborhoods

open ProperSpinor SpinorBaseChange ReflectionApproximation Filter Topology
open scoped NormEuclidean.OrthogonalTopology

section Local

variable {F E : Type*} [Field F] [CharZero F] [Invertible (2 : F)]
  [TopologicalSpace F] [IsTopologicalRing F] [ContinuousInv₀ F]
  [AddCommGroup E] [Module F E] [FiniteDimensional F E]
  [TopologicalSpace E] [IsModuleTopology F E]

/-- The exact proper reflection pair, kept opaque during neighborhood
elaboration so determinant and reflection proofs are not unfolded repeatedly. -/
@[irreducible] def valuePair (Q : QuadraticForm F E) (hQ : Q.polarBilin.Nondegenerate)
    (x : E) (hx : Q x ≠ 0) (y : {y : E // Q y = Q x}) : properGroup Q :=
  doubleReflection Q hQ x hx y.1 (y.2.trans_ne hx)

/-- The opaque elaboration wrapper is literally the original reflection pair. -/
theorem valuePair_eq (Q : QuadraticForm F E) (hQ : Q.polarBilin.Nondegenerate)
    (x : E) (hx : Q x ≠ 0) (y : {y : E // Q y = Q x}) :
    valuePair Q hQ x hx y = doubleReflection Q hQ x hx y.1 (y.2.trans_ne hx) := by
  rw [valuePair]

theorem continuous_valuePair (Q : QuadraticForm F E) (hQ : Q.polarBilin.Nondegenerate)
    (x : E) (hx : Q x ≠ 0) : Continuous (valuePair Q hQ x hx) := by
  unfold valuePair
  exact continuous_sameValue_doubleReflection Q hQ x hx

set_option backward.isDefEq.respectTransparency false in
/-- Actual ambient neighborhoods can be handed directly to the fixed-value
vector theorem, without treating continuity as a global approximation law. -/
theorem exists_ambient_neighborhood (Q : QuadraticForm F E)
    (hQ : Q.polarBilin.Nondegenerate) (x : E) (hx : Q x ≠ 0)
    (y : E) (hy : Q y = Q x) (U : Set (properGroup Q))
    (hU : U ∈ 𝓝 (valuePair Q hQ x hx ⟨y, hy⟩)) :
    ∃ W : Set E, W ∈ 𝓝 y ∧ ∀ z : E, ∀ hz : Q z = Q x, z ∈ W →
      valuePair Q hQ x hx ⟨z, hz⟩ ∈ U := by
  have hpre : valuePair Q hQ x hx ⁻¹' U ∈ 𝓝 (⟨y, hy⟩ : {y : E // Q y = Q x}) :=
    (continuous_valuePair Q hQ x hx).continuousAt.preimage_mem_nhds hU
  obtain ⟨W, hW, hsub⟩ := (mem_nhds_subtype {z : E | Q z = Q x} ⟨y, hy⟩ _).mp hpre
  refine ⟨W, hW, fun z hz hzW ↦ ?_⟩
  exact hsub (show (⟨z, hz⟩ : {z : E // Q z = Q x}) ∈ Subtype.val ⁻¹' W from hzW)

end Local

section Finite

open IsDedekindDomain CompletedIntegralLattice AdelicApproximation

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

local instance completedInvertibleTwo (v : HeightOneSpectrum (integerSubring K)) :
    Invertible (2 : LocalField (integerSubring K) v) := invertibleOfNonzero (by norm_num)

set_option backward.isDefEq.respectTransparency false in
/-- The actual finite-completion adapter for 104:4. The resulting global
reflection pair lies in the actual Wall kernel; a global fixed-value vector
meeting the constructed ambient neighborhoods suffices for every target. -/
theorem exists_finite_vector_neighborhoods (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (x : V) (hx : Q x ≠ 0)
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (y : (v : T) → Space (V := V) (integerSubring K) v.1)
    (hy : ∀ v, form (integerSubring K) v.1 Q (y v) =
      form (integerSubring K) v.1 Q (inclusion (integerSubring K) v.1 x))
    (U : (v : T) → Set (properGroup (form (integerSubring K) v.1 Q)))
    (hU : ∀ v, U v ∈ 𝓝 (valuePair
      (F := LocalField (integerSubring K) v.1) (E := Space (V := V) (integerSubring K) v.1)
      (form (integerSubring K) v.1 Q)
      (form_polarBilin_nondegenerate (integerSubring K) v.1 Q hQ)
      (inclusion (integerSubring K) v.1 x)
      (form_inclusion_ne_zero (integerSubring K) v.1 Q x hx) ⟨y v, hy v⟩)) :
    ∃ W : (v : T) → Set (Space (V := V) (integerSubring K) v.1),
      (∀ v, W v ∈ 𝓝 (y v)) ∧ ∀ z : V, ∀ hz : Q z = Q x,
      (∀ v : T, inclusion (integerSubring K) v.1 z ∈ W v) →
      properAmbientSpinorNormHom Q hQ (doubleReflection Q hQ x hx z (hz.trans_ne hx)) = 1 ∧
        ∀ v : T, localizeProper Q (doubleReflection Q hQ x hx z (hz.trans_ne hx)) v.1 ∈ U v := by
  choose W hW hcontrol using fun v : T ↦ exists_ambient_neighborhood
    (F := LocalField (integerSubring K) v.1) (E := Space (V := V) (integerSubring K) v.1)
    (form (integerSubring K) v.1 Q)
    (form_polarBilin_nondegenerate (integerSubring K) v.1 Q hQ)
    (inclusion (integerSubring K) v.1 x)
    (form_inclusion_ne_zero (integerSubring K) v.1 Q x hx) (y v) (hy v) (U v) (hU v)
  refine ⟨W, hW, fun z hz hzW ↦ ⟨?_, ?_⟩⟩
  · exact doubleReflection_spinorNorm_eq_one_of_value_eq Q hQ x hx z
      (hz.trans_ne hx) hz.symm
  · intro v
    have hvalue : form (integerSubring K) v.1 Q (inclusion (integerSubring K) v.1 z) =
        form (integerSubring K) v.1 Q (inclusion (integerSubring K) v.1 x) := by
      rw [form_inclusion, form_inclusion, hz]
    have hpair := hcontrol v (inclusion (integerSubring K) v.1 z) hvalue (hzW v)
    rw [valuePair_eq] at hpair
    have heq : localizeProper Q (doubleReflection Q hQ x hx z (hz.trans_ne hx)) v.1 =
        doubleReflection (form (integerSubring K) v.1 Q)
          (form_polarBilin_nondegenerate (integerSubring K) v.1 Q hQ)
          (inclusion (integerSubring K) v.1 x)
          (form_inclusion_ne_zero (integerSubring K) v.1 Q x hx)
          (inclusion (integerSubring K) v.1 z) (hvalue.trans_ne
            (form_inclusion_ne_zero (integerSubring K) v.1 Q x hx)) := by
      apply Subtype.ext
      apply Subtype.ext
      exact equiv_doubleReflection Q (integerSubring K) hQ x hx z (hz.trans_ne hx) v.1
    rw [heq]
    exact hpair

end Finite

end NormEuclidean.ReflectionVectorNeighborhoods
