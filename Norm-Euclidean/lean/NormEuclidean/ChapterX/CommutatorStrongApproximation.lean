import NormEuclidean.ChapterX.FiniteCommutatorWords

/-!
# O'Meara 104:4 step 1(b), at actual finite commutator targets

The actual derived-group condition is converted to a common finite word
using 43:6. The adelic corollary supplies a hit of the original open
integral-stabilizer coset; it is not yet a theorem for arbitrary Wall kernels.
-/

noncomputable section

namespace NormEuclidean.CommutatorStrongApproximation

open IsDedekindDomain CompletedIntegralLattice ProperSpinor AdelicOrthogonal
  AdelicApproximation AdelicSpinorKernel Filter Topology
open scoped NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

set_option backward.isDefEq.respectTransparency false in
/-- Arbitrary finite actual derived-group targets have strong global Wall-kernel approximants. -/
theorem exists_kernel_approximation (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : 4 ≤ Module.finrank K V) (L : Submodule (integerSubring K) V) (hfg : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤)
    (q : NumberField.InfinitePlace K) (hiso : ¬ (Q.baseChange q.Completion).Anisotropic)
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (a : (v : T) → properGroup (form (integerSubring K) v.1 Q))
    (ha : ∀ v, (a v).1 ∈ commutator (ambientGroup (form (integerSubring K) v.1 Q)))
    (U : (v : T) → Set (properGroup (form (integerSubring K) v.1 Q)))
    (hU : ∀ v, U v ∈ 𝓝 (a v)) :
    ∃ g : properGroup Q, properAmbientSpinorNormHom Q hQ g = 1 ∧
      (∀ v : HeightOneSpectrum (integerSubring K), v ∉ T → localizeProper Q g v ∈
        properStabilizerWithin (form (integerSubring K) v Q) (carrier _ v L)) ∧
      ∀ v : T, localizeProper Q g v.1 ∈ U v := by
  obtain ⟨l, hl⟩ := FiniteCommutatorWords.exists_word Q hQ (by omega) T a ha
  exact ShortCommutatorWords.exists_kernel_word Q hQ hdim L hfg hfull q hiso T l U
    (by simpa only [hl] using hU)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Restricted finite adelic derived-group targets admit an actual integral-coset hit. -/
theorem exists_adelic_hit (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : 4 ≤ Module.finrank K V)
    (q : NumberField.InfinitePlace K) (hiso : ¬ (Q.baseChange q.Completion).Anisotropic)
    (L : Lattice (integerSubring K) Q) (a : FiniteAdelicProperOrthogonal Q L)
    (ha : ∀ v, (a v).1 ∈ commutator (ambientGroup (form (integerSubring K) v Q))) :
    ∃ g : properGroup Q, properAmbientSpinorNormHom Q hQ g = 1 ∧
      InStabilizerCoset Q L a (finiteDiagonal Q L g) := by
  classical
  have hbad : {v | a v ∉ properStabilizerWithin (form (integerSubring K) v Q)
      (carrier _ v L.carrier)}.Finite := eventually_cofinite.mp a.2
  let T := hbad.toFinset
  let U (v : T) : Set (properGroup (form (integerSubring K) v.1 Q)) :=
    {g | (a v.1)⁻¹ * g ∈ properStabilizerWithin (form (integerSubring K) v.1 Q)
      (carrier _ v.1 L.carrier)}
  have hU (v : T) : U v ∈ 𝓝 (a v.1) := by
    have hopen := OrthogonalTopology.isOpen_properStabilizerWithin
      (form (integerSubring K) v.1 Q) (carrier _ v.1 L.carrier) (carrier_fg _ _ _ L.finite)
      (OrthogonalTopology.isOpen_of_full _ (OrthogonalTopology.isOpen_localRing _ _)
        _ (carrier_full _ _ _ L.full))
    exact (hopen.preimage (continuous_const.mul continuous_id)).mem_nhds
      (by
        change (a v.1)⁻¹ * a v.1 ∈ properStabilizerWithin
          (form (integerSubring K) v.1 Q) (carrier _ v.1 L.carrier)
        rw [inv_mul_cancel]
        exact Subgroup.one_mem _)
  obtain ⟨g, hg, hout, hnear⟩ := exists_kernel_approximation Q hQ hdim L.carrier L.finite
    L.full q hiso T (fun v ↦ a v.1) (fun v ↦ ha v.1) U hU
  refine ⟨g, hg, ?_⟩
  intro v
  by_cases hv : v ∈ T
  · exact hnear ⟨v, hv⟩
  · have hav : a v ∈ properStabilizerWithin (form (integerSubring K) v Q)
        (carrier _ v L.carrier) := by
      by_contra h
      exact hv (hbad.mem_toFinset.mpr h)
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hav) (hout v hv)

end NormEuclidean.CommutatorStrongApproximation
