import NormEuclidean.ChapterX.ProperReflectionGeneration
import NormEuclidean.ChapterX.FiniteWeakApproximation
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# Finite-place weak approximation of the actual proper orthogonal group

Reflection-pair generation and proved vector weak approximation give the
finite-place form of O'Meara 102:4. Integrality outside the target places
and spinor-kernel strong approximation are not conclusions of this file.
-/

noncomputable section

namespace NormEuclidean.ProperWeakApproximation

open ProperSpinor SpinorBaseChange ReflectionApproximation ProperReflectionGeneration
open FiniteWeakApproximation CompletedIntegralLattice AdelicApproximation AdelicSpinorKernel
open IsDedekindDomain Filter Topology
open scoped NormEuclidean.OrthogonalTopology

/-- Restricting a dense map to the preimage of an open set preserves density. -/
theorem denseRange_subtype_of_isOpen {X Y : Type*} [TopologicalSpace Y]
    (f : X → Y) (hf : DenseRange f) (s : Set Y) (hs : IsOpen s) :
    DenseRange (fun x : {x : X // f x ∈ s} ↦ (⟨f x.1, x.2⟩ : s)) := by
  intro y
  apply mem_closure_iff_nhds.mpr
  intro U hU
  obtain ⟨W, hW, hsub⟩ := (mem_nhds_subtype s y U).mp hU
  have hnb : W ∩ s ∈ 𝓝 y.1 := inter_mem hW (hs.mem_nhds y.2)
  obtain ⟨z, ⟨hzW, hzs⟩, x, rfl⟩ := (mem_closure_iff_nhds.mp (hf y.1)) _ hnb
  refine ⟨⟨f x, hzs⟩, ?_, ⟨⟨x, hzs⟩, rfl⟩⟩
  exact hsub (show (⟨f x, hzs⟩ : s) ∈ Subtype.val ⁻¹' W from hzW)

/-- Membership of all single-coordinate elements determines membership of
every finite tuple, including for noncommutative groups. -/
theorem subgroup_mem_of_singles {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : ι → Type*} [∀ i, Group (G i)] (H : Subgroup (∀ i, G i))
    (hH : ∀ i x, MonoidHom.mulSingle G i x ∈ H) (f : ∀ i, G i) : f ∈ H := by
  have ht (t : Finset ι) : ∀ f : ∀ i, G i, (∀ i ∉ t, f i = 1) → f ∈ H := by
    induction t using Finset.induction_on with
    | empty =>
      intro f hf
      have heq : f = 1 := funext fun i ↦ hf i (by simp)
      exact heq ▸ H.one_mem
    | @insert i t hi ih =>
      intro f hf
      let f' := (MonoidHom.mulSingle G i (f i))⁻¹ * f
      have hf' : f' ∈ H := ih f' (by
        intro j hj
        by_cases hji : j = i
        · subst j
          simp [f']
        · have hj' : j ∉ insert i t := by simp [hji, hj]
          simp [f', hji, hf j hj'])
      have heq : MonoidHom.mulSingle G i (f i) * f' = f := by simp [f', ← mul_assoc]
      exact heq ▸ H.mul_mem (hH i (f i)) hf'
  exact ht Finset.univ f (by simp)

/-- Continuous anisotropic vector families give a continuous actual proper pair. -/
theorem continuous_pair_of_continuous {X F E : Type*} [TopologicalSpace X]
    [Field F] [CharZero F] [TopologicalSpace F] [IsTopologicalRing F] [ContinuousInv₀ F]
    [Invertible (2 : F)] [AddCommGroup E] [Module F E] [FiniteDimensional F E]
    [TopologicalSpace E] [IsModuleTopology F E] (Q : QuadraticForm F E)
    (hQ : Q.polarBilin.Nondegenerate) (u w : X → E) (hu : Continuous u) (hw : Continuous w)
    (hu0 : ∀ x, Q (u x) ≠ 0) (hw0 : ∀ x, Q (w x) ≠ 0) :
    Continuous (fun x ↦ doubleReflection Q hQ (u x) (hu0 x) (w x) (hw0 x)) := by
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  change Continuous (fun x ↦ IntegralReflection.linearEquiv Q (u x) (hu0 x) *
    IntegralReflection.linearEquiv Q (w x) (hw0 x))
  have hur : Continuous (fun x ↦ IntegralReflection.linearEquiv Q (u x) (hu0 x)) :=
    (OrthogonalTopology.continuous_reflection Q).comp (hu.subtype_mk hu0)
  have hwr : Continuous (fun x ↦ IntegralReflection.linearEquiv Q (w x) (hw0 x)) :=
    (OrthogonalTopology.continuous_reflection Q).comp (hw.subtype_mk hw0)
  exact hur.mul hwr

section NumberField

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V)

/-- The actual proper diagonal restricted to finitely many completions. -/
def finiteProperDiagonal (T : Finset (HeightOneSpectrum (integerSubring K))) :
    properGroup Q →* ((v : T) → properGroup (form (integerSubring K) v.1 Q)) where
  toFun g v := localizeProper Q g v.1
  map_one' := by
    funext v
    apply Subtype.ext
    apply Subtype.ext
    exact LinearEquiv.baseChange_one K (LocalField (integerSubring K) v.1) V
  map_mul' g h := funext fun v ↦ localizeProper_mul Q g h v.1

abbrev PairData (_Q : QuadraticForm K V) (T : Finset (HeightOneSpectrum (integerSubring K))) :=
  (v : T) → Space (V := V) (integerSubring K) v.1 × Space (V := V) (integerSubring K) v.1

def pairDomain (T : Finset (HeightOneSpectrum (integerSubring K))) : Set (PairData Q T) :=
  {p | ∀ v : T, form (integerSubring K) v.1 Q (p v).1 ≠ 0 ∧
    form (integerSubring K) v.1 Q (p v).2 ≠ 0}

theorem isOpen_pairDomain (T : Finset (HeightOneSpectrum (integerSubring K))) :
    IsOpen (pairDomain Q T) := by
  have hv (v : T) : IsOpen {p : PairData Q T |
      form (integerSubring K) v.1 Q (p v).1 ≠ 0 ∧
        form (integerSubring K) v.1 Q (p v).2 ≠ 0} :=
    ((OrthogonalTopology.isOpen_reflectingVectors _).preimage (continuous_apply v).fst).inter
      ((OrthogonalTopology.isOpen_reflectingVectors _).preimage (continuous_apply v).snd)
  simpa only [pairDomain, Set.setOf_forall] using isOpen_iInter_of_finite hv

variable (hQ : Q.polarBilin.Nondegenerate)

def pairImage (T : Finset (HeightOneSpectrum (integerSubring K))) (p : pairDomain Q T) :
    (v : T) → properGroup (form (integerSubring K) v.1 Q) := fun v ↦
  doubleReflection (form (integerSubring K) v.1 Q)
    (form_polarBilin_nondegenerate (integerSubring K) v.1 Q hQ)
    (p.1 v).1 (p.2 v).1 (p.1 v).2 (p.2 v).2

theorem continuous_pairImage (T : Finset (HeightOneSpectrum (integerSubring K))) :
    Continuous (pairImage Q hQ T) := by
  apply continuous_pi
  intro v
  letI : Invertible (2 : LocalField (integerSubring K) v.1) := by
    exact (Invertible.map (algebraMap K (LocalField (integerSubring K) v.1)) 2).copy 2
      (map_ofNat _ _).symm
  exact continuous_pair_of_continuous (form (integerSubring K) v.1 Q)
    (form_polarBilin_nondegenerate (integerSubring K) v.1 Q hQ)
    (fun p : pairDomain Q T ↦ (p.1 v).1) (fun p : pairDomain Q T ↦ (p.1 v).2)
    ((continuous_apply v).comp continuous_subtype_val).fst
    ((continuous_apply v).comp continuous_subtype_val).snd (fun p ↦ (p.2 v).1) (fun p ↦ (p.2 v).2)

/-- Every tuple of local reflection pairs lies in the closure of the actual
global proper diagonal. The same global pair realizes each approximant. -/
theorem pairImage_mem_diagonal_closure (T : Finset (HeightOneSpectrum (integerSubring K)))
    (hT : T.Nonempty) (p : pairDomain Q T) :
    pairImage Q hQ T p ∈ (finiteProperDiagonal Q T).range.topologicalClosure := by
  let d : V → ((v : T) → Space (V := V) (integerSubring K) v.1) :=
    fun x v ↦ inclusion (integerSubring K) v.1 x
  have hd : DenseRange d := numberField_denseRange_inclusion T
  let h : (((v : T) → Space (V := V) (integerSubring K) v.1) ×
      ((v : T) → Space (V := V) (integerSubring K) v.1)) → PairData Q T :=
    fun q v ↦ (q.1 v, q.2 v)
  have hs : Function.Surjective h := fun q ↦ ⟨(fun v ↦ (q v).1, fun v ↦ (q v).2), rfl⟩
  have hc : Continuous h := continuous_pi (fun v ↦
    ((continuous_apply v).comp continuous_fst).prodMk
      ((continuous_apply v).comp continuous_snd))
  let dp : V × V → PairData Q T := fun r v ↦ (d r.1 v, d r.2 v)
  have hdp : DenseRange dp := by
    convert hs.denseRange.comp (hd.prodMap hd) hc using 1
    funext r v
    rfl
  let D : {r : V × V // dp r ∈ pairDomain Q T} → pairDomain Q T :=
    fun r ↦ ⟨dp r.1, r.2⟩
  have hD : DenseRange D := denseRange_subtype_of_isOpen dp hdp _ (isOpen_pairDomain Q T)
  let H := (finiteProperDiagonal Q T).range.topologicalClosure
  have hclosed : IsClosed ((pairImage Q hQ T) ⁻¹' (H : Set _)) :=
    (Subgroup.isClosed_topologicalClosure _).preimage (continuous_pairImage Q hQ T)
  have hrange : Set.range D ⊆ (pairImage Q hQ T) ⁻¹' (H : Set _) := by
    rintro _ ⟨r, rfl⟩
    obtain ⟨v0, hv0⟩ := hT
    have hu : Q r.1.1 ≠ 0 := by
      intro hzero
      apply (r.2 ⟨v0, hv0⟩).1
      simp only [dp, d, form_inclusion, hzero, map_zero]
    have hw : Q r.1.2 ≠ 0 := by
      intro hzero
      apply (r.2 ⟨v0, hv0⟩).2
      simp only [dp, d, form_inclusion, hzero, map_zero]
    let g := doubleReflection Q hQ r.1.1 hu r.1.2 hw
    apply (finiteProperDiagonal Q T).range.le_topologicalClosure
    refine ⟨g, ?_⟩
    funext v
    apply Subtype.ext
    apply Subtype.ext
    exact equiv_doubleReflection Q (integerSubring K) hQ r.1.1 hu r.1.2 hw v.1
  exact (hclosed.closure_subset_iff.mpr hrange) (hD p)

include hQ in
set_option maxHeartbeats 1200000 in
/-- O'Meara 102:4 at actual finite places in positive dimension. The proper
group generation and diagonal density are proved, not supplied as premises. -/
theorem denseRange_finiteProperDiagonal (hpos : 0 < Module.finrank K V)
    (T : Finset (HeightOneSpectrum (integerSubring K))) :
    DenseRange (finiteProperDiagonal Q T) := by
  classical
  intro a
  by_cases hT : T.Nonempty
  · obtain ⟨u, hu⟩ := (SpinorBridge.quadraticSpace Q hQ).exists_isAnisotropic_of_finrank_pos hpos
    have hu0 : Q u ≠ 0 := by simpa [Bong.QuadraticSpace.IsAnisotropic] using hu
    let G : T → Type _ := fun v ↦ ↥(properGroup (form (integerSubring K) v.1 Q))
    let H := (finiteProperDiagonal Q T).range.topologicalClosure
    have hsingle (v : T) (g : G v) : MonoidHom.mulSingle G v g ∈ H := by
      let P := H.comap (MonoidHom.mulSingle G v)
      apply proper_mem_of_contains_doubleReflections (form (integerSubring K) v.1 Q)
        (form_polarBilin_nondegenerate (integerSubring K) v.1 Q hQ) P _ g
      intro x hx y hy
      let p0 : PairData Q T := fun w ↦
        (inclusion (integerSubring K) w.1 u, inclusion (integerSubring K) w.1 u)
      let p := Function.update p0 v (x, y)
      have hp : p ∈ pairDomain Q T := by
        intro w
        by_cases hw : w = v
        · subst w
          simpa [p] using And.intro hx hy
        · simpa [p, p0, hw] using And.intro
            (form_inclusion_ne_zero (integerSubring K) w.1 Q u hu0)
            (form_inclusion_ne_zero (integerSubring K) w.1 Q u hu0)
      have hi := pairImage_mem_diagonal_closure Q hQ T hT ⟨p, hp⟩
      change MonoidHom.mulSingle G v (doubleReflection _ _ x hx y hy) ∈ H
      convert hi using 1
      funext w
      by_cases hw : w = v
      · subst w
        simp [pairImage, p]
      · simp [pairImage, p, p0, hw, doubleReflection_self]
    have ha : a ∈ H := subgroup_mem_of_singles H hsingle a
    exact ha
  · haveI : IsEmpty T := ⟨fun v ↦ hT ⟨v.1, v.2⟩⟩
    apply subset_closure
    exact ⟨1, Subsingleton.elim _ _⟩

include hQ in
/-- A global proper transformation meets arbitrary finitely many local
proper neighborhoods. No integrality at other places is claimed. -/
theorem exists_global_proper_weak_approximation (hpos : 0 < Module.finrank K V)
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (a : (v : T) → properGroup (form (integerSubring K) v.1 Q))
    (U : (v : T) → Set (properGroup (form (integerSubring K) v.1 Q)))
    (hU : ∀ v : T, U v ∈ 𝓝 (a v)) :
    ∃ g : properGroup Q, ∀ v : T, localizeProper Q g v.1 ∈ U v := by
  have hnb : {b | ∀ v : T, b v ∈ U v} ∈ 𝓝 a :=
    Filter.eventually_all.mpr (fun v ↦ ((continuous_apply v).tendsto a).eventually (hU v))
  obtain ⟨b, hb, g, rfl⟩ := (mem_closure_iff_nhds.mp
    (denseRange_finiteProperDiagonal Q hQ hpos T a)) _ hnb
  exact ⟨g, hb⟩

end NumberField

end NormEuclidean.ProperWeakApproximation
