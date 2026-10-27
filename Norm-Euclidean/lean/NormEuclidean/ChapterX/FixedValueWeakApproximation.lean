import NormEuclidean.ChapterX.FiniteWeakApproximation
import NormEuclidean.ChapterX.FixedValueTransitivity

/-!
# Global fixed-value vectors with finite local approximation

This proves the weak approximation step used to start O'Meara 104:3:
for a represented nonzero value, global vectors of exactly that value meet
arbitrary neighborhoods of finitely many local vectors of the same value.
Integrality outside those places, required by the full 104:3 theorem, is
not asserted. No density or proper-isometry existence law is assumed.
-/

noncomputable section

namespace NormEuclidean.FixedValueWeakApproximation

open QuadraticMap ProperSpinor SpinorBaseChange ReflectionApproximation
open FixedValueTransitivity FiniteWeakApproximation OrthogonalTopology
open CompletedIntegralLattice IsDedekindDomain Filter Topology
open scoped NormEuclidean.OrthogonalTopology

section Local

variable {F E : Type*} [Field F] [CharZero F] [TopologicalSpace F]
  [IsTopologicalRing F] [ContinuousInv₀ F] [T1Space F] [Invertible (2 : F)]
  [AddCommGroup E] [Module F E] [FiniteDimensional F E]
  [TopologicalSpace E] [IsModuleTopology F E]

/-- The reflecting-vector topology supplies an ambient pair neighborhood
where both reflections are defined and the image of a fixed vector lies in
the prescribed local target. -/
theorem exists_pair_neighborhood (Q : QuadraticForm F E) (hQ : Q.polarBilin.Nondegenerate)
    (x : E) (p : {u : E // Q u ≠ 0} × {u : E // Q u ≠ 0})
    (W : Set E) (hW : W ∈ 𝓝 ((doubleReflection Q hQ p.1.1 p.1.2 p.2.1 p.2.2).1.1 x)) :
    ∃ B : Set (E × E), B ∈ 𝓝 (p.1.1, p.2.1) ∧
      ∀ q ∈ B, ∃ (hu : Q q.1 ≠ 0) (hv : Q q.2 ≠ 0),
        (doubleReflection Q hQ q.1 hu q.2 hv).1.1 x ∈ W := by
  let X := {u : E // Q u ≠ 0} × {u : E // Q u ≠ 0}
  let f : X → E := fun q ↦ (doubleReflection Q hQ q.1.1 q.1.2 q.2.1 q.2.2).1.1 x
  have hf : Continuous f := (continuous_proper_apply Q x).comp (continuous_doubleReflection Q hQ)
  let i : X → E × E := Prod.map Subtype.val Subtype.val
  have hi : IsOpenMap i := (isOpen_reflectingVectors Q).isOpenMap_subtype_val.prodMap
    (isOpen_reflectingVectors Q).isOpenMap_subtype_val
  refine ⟨i '' (f ⁻¹' W), hi.image_mem_nhds (hf.continuousAt.preimage_mem_nhds hW), ?_⟩
  rintro q ⟨q', hq', rfl⟩
  exact ⟨q'.1.2, q'.2.2, hq'⟩

end Local

section NumberField

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)

/-- Simultaneous weak approximation of two-reflection images uses the
actual global reflecting vectors and their actual completed reflections. -/
theorem exists_global_twoReflection_images
    (T : Finset (HeightOneSpectrum (integerSubring K))) (hT : T.Nonempty) (x : V)
    (p : (v : T) → {u : Space (V := V) (integerSubring K) v.1 //
        form (integerSubring K) v.1 Q u ≠ 0} ×
      {u : Space (V := V) (integerSubring K) v.1 // form (integerSubring K) v.1 Q u ≠ 0})
    (W : (v : T) → Set (Space (V := V) (integerSubring K) v.1))
    (hW : ∀ v : T, W v ∈ 𝓝 ((doubleReflection (form (integerSubring K) v.1 Q)
      (form_polarBilin_nondegenerate (integerSubring K) v.1 Q hQ)
      (p v).1.1 (p v).1.2 (p v).2.1 (p v).2.2).1.1
        (inclusion (integerSubring K) v.1 x))) :
    ∃ z : V, Q z = Q x ∧ ∀ v : T, inclusion (integerSubring K) v.1 z ∈ W v := by
  classical
  have hex (v : T) : ∃ B : Set (Space (V := V) (integerSubring K) v.1 ×
      Space (V := V) (integerSubring K) v.1),
      B ∈ 𝓝 ((p v).1.1, (p v).2.1) ∧
      ∀ q ∈ B, ∃ (hu : form (integerSubring K) v.1 Q q.1 ≠ 0)
        (hv : form (integerSubring K) v.1 Q q.2 ≠ 0),
        (doubleReflection (form (integerSubring K) v.1 Q)
          (form_polarBilin_nondegenerate (integerSubring K) v.1 Q hQ)
          q.1 hu q.2 hv).1.1 (inclusion (integerSubring K) v.1 x) ∈ W v := by
    letI : Invertible (2 : LocalField (integerSubring K) v.1) := by
      exact (Invertible.map (algebraMap K (LocalField (integerSubring K) v.1)) 2).copy 2
        (map_ofNat _ _).symm
    exact exists_pair_neighborhood (form (integerSubring K) v.1 Q)
      (form_polarBilin_nondegenerate (integerSubring K) v.1 Q hQ)
      (inclusion (integerSubring K) v.1 x) (p v) (W v) (hW v)
  choose B hB hcontrol using hex
  let d : V → ((v : T) → Space (V := V) (integerSubring K) v.1) :=
    fun z v ↦ inclusion (integerSubring K) v.1 z
  have hd : DenseRange d := numberField_denseRange_inclusion T
  let h : (((v : T) → Space (V := V) (integerSubring K) v.1) ×
      ((v : T) → Space (V := V) (integerSubring K) v.1)) →
      ((v : T) → Space (V := V) (integerSubring K) v.1 ×
        Space (V := V) (integerSubring K) v.1) := fun q v ↦ (q.1 v, q.2 v)
  have hs : Function.Surjective h := fun z ↦ ⟨(fun v ↦ (z v).1, fun v ↦ (z v).2), rfl⟩
  have hc : Continuous h := continuous_pi (fun v ↦
    ((continuous_apply v).comp continuous_fst).prodMk
      ((continuous_apply v).comp continuous_snd))
  let dp : V × V → ((v : T) → Space (V := V) (integerSubring K) v.1 ×
      Space (V := V) (integerSubring K) v.1) :=
    fun q v ↦ (inclusion (integerSubring K) v.1 q.1, inclusion (integerSubring K) v.1 q.2)
  have hdp : DenseRange dp := by
    convert hs.denseRange.comp (hd.prodMap hd) hc using 1
    funext q v
    rfl
  let target := fun v : T ↦ ((p v).1.1, (p v).2.1)
  have hnb : {q | ∀ v : T, q v ∈ B v} ∈ 𝓝 target :=
    Filter.eventually_all.mpr (fun v ↦ ((continuous_apply v).tendsto target).eventually (hB v))
  obtain ⟨q, hq, r, rfl⟩ := (mem_closure_iff_nhds.mp (hdp target)) _ hnb
  obtain ⟨v0, hv0⟩ := hT
  obtain ⟨hu0, hw0, _⟩ := hcontrol ⟨v0, hv0⟩ (dp r ⟨v0, hv0⟩) (hq ⟨v0, hv0⟩)
  have hu : Q r.1 ≠ 0 := by
    intro hzero
    apply hu0
    rw [form_inclusion, hzero, map_zero]
  have hw : Q r.2 ≠ 0 := by
    intro hzero
    apply hw0
    rw [form_inclusion, hzero, map_zero]
  let g := doubleReflection Q hQ r.1 hu r.2 hw
  refine ⟨g.1.1 x, g.1.2 x, ?_⟩
  intro v
  obtain ⟨huv, hwv, himage⟩ := hcontrol v (dp r v) (hq v)
  rw [← equiv_inclusion, equiv_doubleReflection Q (integerSubring K) hQ r.1 hu r.2 hw v.1]
  exact himage

include hQ in
/-- The nonzero fixed-value weak approximation needed in 104:3, step 2.
The global vector has exactly value `a` and meets all finite local targets.
This conclusion has no assertion of integrality outside `T`. -/
theorem exists_global_fixed_value_weak_approximation
    (hdim : 2 ≤ Module.finrank K V) (a : K) (ha : a ≠ 0) (hrep : ∃ x : V, Q x = a)
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (z : (v : T) → Space (V := V) (integerSubring K) v.1)
    (hz : ∀ v : T, form (integerSubring K) v.1 Q (z v) =
      algebraMap K (LocalField (integerSubring K) v.1) a)
    (W : (v : T) → Set (Space (V := V) (integerSubring K) v.1))
    (hW : ∀ v : T, W v ∈ 𝓝 (z v)) :
    ∃ y : V, Q y = a ∧ ∀ v : T, inclusion (integerSubring K) v.1 y ∈ W v := by
  classical
  obtain ⟨x, hx⟩ := hrep
  by_cases hT : T.Nonempty
  · have hx0 : Q x ≠ 0 := hx.trans_ne ha
    obtain ⟨u, hu, hxu⟩ := exists_anisotropic_orthogonal Q hQ hdim x hx0
    have hex (v : T) : ∃ (r : Space (V := V) (integerSubring K) v.1)
        (hr : form (integerSubring K) v.1 Q r ≠ 0)
        (s : Space (V := V) (integerSubring K) v.1)
        (hs : form (integerSubring K) v.1 Q s ≠ 0),
        (doubleReflection (form (integerSubring K) v.1 Q)
          (form_polarBilin_nondegenerate (integerSubring K) v.1 Q hQ)
          r hr s hs).1.1 (inclusion (integerSubring K) v.1 x) = z v := by
      apply exists_doubleReflection_map (form (integerSubring K) v.1 Q)
        (form_polarBilin_nondegenerate (integerSubring K) v.1 Q hQ)
        (inclusion (integerSubring K) v.1 x) (z v) (inclusion (integerSubring K) v.1 u)
      · exact form_inclusion_ne_zero (integerSubring K) v.1 Q x hx0
      · rw [form_inclusion, hx, hz v]
      · exact form_inclusion_ne_zero (integerSubring K) v.1 Q u hu
      · have hux : polar Q u x = 0 := (polar_comm Q u x).trans hxu
        simpa only [QuadraticMap.polar, ← inclusion_add, form_inclusion,
          ← map_sub, map_zero] using congrArg (algebraMap K (LocalField (integerSubring K) v.1)) hux
    choose r hr s hs himage using hex
    let p := fun v : T ↦ ((⟨r v, hr v⟩ : {w // form (integerSubring K) v.1 Q w ≠ 0}),
      (⟨s v, hs v⟩ : {w // form (integerSubring K) v.1 Q w ≠ 0}))
    obtain ⟨y, hy, hyt⟩ := exists_global_twoReflection_images Q hQ T hT x p W (by
      intro v
      simpa only [p, himage] using hW v)
    exact ⟨y, hy.trans hx, hyt⟩
  · refine ⟨x, hx, ?_⟩
    intro v
    exact (hT ⟨v.1, v.2⟩).elim

include hQ in
/-- For the hyperbolic enlargement every nonzero scalar is represented.
Its weak approximation statement needs no separate global representation
or dimension premise. Integrality outside `T` is still not asserted. -/
theorem hyperbolic_exists_global_fixed_value_weak_approximation
    (a : K) (ha : a ≠ 0) (T : Finset (HeightOneSpectrum (integerSubring K)))
    (z : (v : T) → Space (V := Hyperbolic K V) (integerSubring K) v.1)
    (hz : ∀ v : T, form (integerSubring K) v.1 (Hyperbolic.form Q) (z v) =
      algebraMap K (LocalField (integerSubring K) v.1) a)
    (W : (v : T) → Set (Space (V := Hyperbolic K V) (integerSubring K) v.1))
    (hW : ∀ v : T, W v ∈ 𝓝 (z v)) :
    ∃ y : Hyperbolic K V, Hyperbolic.form Q y = a ∧
      ∀ v : T, inclusion (integerSubring K) v.1 y ∈ W v := by
  have hr : Module.finrank K (Hyperbolic K V) = Module.finrank K V + 2 := by
    simp [Hyperbolic, Module.finrank_prod]
  have hdim : 2 ≤ Module.finrank K (Hyperbolic K V) := by rw [hr]; omega
  have hrep : ∃ x : Hyperbolic K V, Hyperbolic.form Q x = a :=
    ⟨(0, 1, a), by simp [Hyperbolic.form_apply, Hyperbolic.q]⟩
  exact exists_global_fixed_value_weak_approximation (Hyperbolic.form Q)
    (Hyperbolic.form_polarBilin_nondegenerate Q hQ) hdim a ha hrep T z hz W hW

end NumberField

end NormEuclidean.FixedValueWeakApproximation
