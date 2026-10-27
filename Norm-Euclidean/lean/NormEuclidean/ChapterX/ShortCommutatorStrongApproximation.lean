import NormEuclidean.ChapterX.ReflectionPairStrongApproximation
import NormEuclidean.ChapterX.ProperWeakApproximation

/-!
# O'Meara 104:4, step 1(a), at arbitrary finite short commutators

Weak approximation first chooses two global reflecting vectors. The square
of their reflection pair is an equal-value pair. Strong vector approximation
then puts an approximant in the actual global Wall kernel while preserving
the original completed carrier at every finite prime outside the targets.
The target short commutators need not have a common global reflecting vector.
-/

noncomputable section

namespace NormEuclidean.ShortCommutatorStrongApproximation

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation
  ProperSpinor SpinorBaseChange AdelicOrthogonal AdelicApproximation AdelicSpinorKernel
  ReflectionApproximation ProperWeakApproximation Filter Topology
open scoped NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- Finite local short commutators can first be approached by one global short commutator. -/
theorem exists_global_short_near (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (T : Finset (HeightOneSpectrum (integerSubring K))) (hT : T.Nonempty)
    (p : pairDomain Q T)
    (U : (v : T) → Set (properGroup (form (integerSubring K) v.1 Q)))
    (hU : ∀ v, U v ∈ 𝓝 ((pairImage Q hQ T p v) ^ 2)) :
    ∃ (x : V) (hx : Q x ≠ 0) (y : V) (hy : Q y ≠ 0),
      ∀ v : T, U v ∈ 𝓝 (localizeProper Q (doubleReflection Q hQ x hx y hy ^ 2) v.1) := by
  classical
  choose O hsub hopen hmem using fun v ↦ mem_nhds_iff.mp (hU v)
  let d : V → ((v : T) → Space (V := V) (integerSubring K) v.1) :=
    fun x v ↦ inclusion (integerSubring K) v.1 x
  have hd : DenseRange d := FiniteWeakApproximation.numberField_denseRange_inclusion T
  let h : (((v : T) → Space (V := V) (integerSubring K) v.1) ×
      ((v : T) → Space (V := V) (integerSubring K) v.1)) → PairData Q T :=
    fun r v ↦ (r.1 v, r.2 v)
  have hs : Function.Surjective h := fun r ↦ ⟨(fun v ↦ (r v).1, fun v ↦ (r v).2), rfl⟩
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
  have hnb : {r : pairDomain Q T | ∀ v : T, (pairImage Q hQ T r v) ^ 2 ∈ O v} ∈
      𝓝 p := by
    apply Filter.eventually_all.mpr
    intro v
    have hcont := ((continuous_apply v).comp (continuous_pairImage Q hQ T)).pow 2
    exact hcont.continuousAt.preimage_mem_nhds ((hopen v).mem_nhds (hmem v))
  obtain ⟨_, hhit, r, rfl⟩ := (mem_closure_iff_nhds.mp (hD p)) _ hnb
  obtain ⟨v0, hv0⟩ := hT
  have hx : Q r.1.1 ≠ 0 := by
    intro hzero
    apply (r.2 ⟨v0, hv0⟩).1
    simp only [dp, d, form_inclusion, hzero, map_zero]
  have hy : Q r.1.2 ≠ 0 := by
    intro hzero
    apply (r.2 ⟨v0, hv0⟩).2
    simp only [dp, d, form_inclusion, hzero, map_zero]
  let g := doubleReflection Q hQ r.1.1 hx r.1.2 hy
  have heq (v : T) : pairImage Q hQ T (D r) v ^ 2 = localizeProper Q (g ^ 2) v.1 := by
    have hpair : pairImage Q hQ T (D r) v = localizeProper Q g v.1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact (equiv_doubleReflection Q (integerSubring K) hQ r.1.1 hx r.1.2 hy v.1).symm
    rw [hpair]
    exact (congrFun ((finiteProperDiagonal Q T).map_pow g 2) v).symm
  refine ⟨r.1.1, hx, r.1.2, hy, ?_⟩
  intro v
  apply Filter.mem_of_superset ((hopen v).mem_nhds ?_) (hsub v)
  exact heq v ▸ hhit v

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- The finite-place, excluded-infinite-place form of 104:4, step 1(a). -/
theorem exists_kernel_short (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : 4 ≤ Module.finrank K V) (L : Submodule (integerSubring K) V) (hfg : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤)
    (q : NumberField.InfinitePlace K) (hiso : ¬ (Q.baseChange q.Completion).Anisotropic)
    (T : Finset (HeightOneSpectrum (integerSubring K))) (p : pairDomain Q T)
    (U : (v : T) → Set (properGroup (form (integerSubring K) v.1 Q)))
    (hU : ∀ v, U v ∈ 𝓝 ((pairImage Q hQ T p v) ^ 2)) :
    ∃ g : properGroup Q, properAmbientSpinorNormHom Q hQ g = 1 ∧
      (∀ v : HeightOneSpectrum (integerSubring K), v ∉ T → localizeProper Q g v ∈
        properStabilizerWithin (form (integerSubring K) v Q) (carrier _ v L)) ∧
      ∀ v : T, localizeProper Q g v.1 ∈ U v := by
  classical
  by_cases hT : T.Nonempty
  · obtain ⟨x, hx, y, hy, hnear⟩ := exists_global_short_near Q hQ T hT p U hU
    let w := (ambientReflection Q y hy).1 x
    have hw : Q w = Q x := (ambientReflection Q y hy).2 x
    apply ReflectionPairStrongApproximation.exists_near_pair Q hQ hdim
      L hfg hfull q hiso x hx w hw T U
    intro v
    rw [← shortCommutator_eq_doubleReflection Q hQ x hx y hy]
    exact hnear v
  · haveI : IsEmpty T := ⟨fun v ↦ hT ⟨v.1, v.2⟩⟩
    refine ⟨1, map_one _, ?_, fun v ↦ isEmptyElim v⟩
    intro v _
    have h1 : localizeProper Q 1 v = 1 :=
      congrFun ((finiteProperDiagonal Q {v}).map_one) ⟨v, by simp⟩
    rw [h1]
    exact Subgroup.one_mem _

end NormEuclidean.ShortCommutatorStrongApproximation
