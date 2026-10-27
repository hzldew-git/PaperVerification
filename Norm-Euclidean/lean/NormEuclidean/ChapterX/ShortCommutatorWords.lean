import NormEuclidean.ChapterX.ShortCommutatorStrongApproximation

/-!
# Finite words of finite-place short commutators

The multiplication step of O'Meara 104:4, step 1(b), preserves both the
actual global Wall kernel and every off-target completed stabilizer.
Local group generation is not an input or a conclusion of this file:
the targets here are explicitly finite words of short commutators.
-/

noncomputable section

namespace NormEuclidean.ShortCommutatorWords

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation
  ProperSpinor AdelicOrthogonal AdelicApproximation AdelicSpinorKernel
  ProperWeakApproximation Filter Topology
open scoped NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The literal local product attached to a finite list of short commutators. -/
def wordImage (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (T : Finset (HeightOneSpectrum (integerSubring K))) (l : List (pairDomain Q T)) :
    (v : T) → properGroup (form (integerSubring K) v.1 Q) :=
  fun v ↦ (l.map (fun p ↦ pairImage Q hQ T p v ^ 2)).prod

@[simp] theorem wordImage_nil (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (T : Finset (HeightOneSpectrum (integerSubring K))) (v : T) :
    wordImage Q hQ T [] v = 1 := rfl

@[simp] theorem wordImage_cons (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (T : Finset (HeightOneSpectrum (integerSubring K))) (p : pairDomain Q T)
    (l : List (pairDomain Q T)) (v : T) :
    wordImage Q hQ T (p :: l) v = pairImage Q hQ T p v ^ 2 * wordImage Q hQ T l v := rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- Every finite short-commutator word has an actual strong approximant in the Wall kernel. -/
theorem exists_kernel_word (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : 4 ≤ Module.finrank K V) (L : Submodule (integerSubring K) V) (hfg : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤)
    (q : NumberField.InfinitePlace K) (hiso : ¬ (Q.baseChange q.Completion).Anisotropic)
    (T : Finset (HeightOneSpectrum (integerSubring K))) (l : List (pairDomain Q T))
    (U : (v : T) → Set (properGroup (form (integerSubring K) v.1 Q)))
    (hU : ∀ v, U v ∈ 𝓝 (wordImage Q hQ T l v)) :
    ∃ g : properGroup Q, properAmbientSpinorNormHom Q hQ g = 1 ∧
      (∀ v : HeightOneSpectrum (integerSubring K), v ∉ T → localizeProper Q g v ∈
        properStabilizerWithin (form (integerSubring K) v Q) (carrier _ v L)) ∧
      ∀ v : T, localizeProper Q g v.1 ∈ U v := by
  classical
  induction l generalizing U with
  | nil =>
      refine ⟨1, map_one _, ?_, ?_⟩
      · intro v _
        have h1 : localizeProper Q 1 v = 1 :=
          congrFun ((finiteProperDiagonal Q {v}).map_one) ⟨v, by simp⟩
        rw [h1]
        exact Subgroup.one_mem _
      · intro v
        have h1 : localizeProper Q 1 v.1 = 1 :=
          congrFun ((finiteProperDiagonal Q T).map_one) v
        rw [h1]
        exact mem_of_mem_nhds (hU v)
  | cons p l ih =>
      have hsplit (v : T) : ∃ A, A ∈ 𝓝 (pairImage Q hQ T p v ^ 2) ∧
          ∃ B, B ∈ 𝓝 (wordImage Q hQ T l v) ∧
            A ×ˢ B ⊆ {r | r.1 * r.2 ∈ U v} := by
        apply mem_nhds_prod_iff.mp
        exact (continuous_fst.mul continuous_snd).continuousAt.preimage_mem_nhds (hU v)
      choose A hA B hB hAB using hsplit
      obtain ⟨g, hg, hgout, hgnear⟩ :=
        ShortCommutatorStrongApproximation.exists_kernel_short Q hQ hdim
          L hfg hfull q hiso T p A hA
      obtain ⟨f, hf, hfout, hfnear⟩ := ih B hB
      refine ⟨g * f, ?_, ?_, ?_⟩
      · rw [map_mul, hg, hf, one_mul]
      · intro v hv
        rw [localizeProper_mul]
        exact Subgroup.mul_mem _ (hgout v hv) (hfout v hv)
      · intro v
        rw [localizeProper_mul]
        have hprod : (localizeProper Q g v.1, localizeProper Q f v.1) ∈ A v ×ˢ B v :=
          ⟨hgnear v, hfnear v⟩
        exact hAB v hprod

end NormEuclidean.ShortCommutatorWords
