import NormEuclidean.ChapterX.ApproximationGoodPrimes
import NormEuclidean.ChapterX.NonzeroValueStrongApproximation
import NormEuclidean.ChapterX.OffTargetReflectionPairs

/-!
# Strong approximation of equal-value reflection pairs

Over a number field, an isotropic infinite completion and rank at least
four give approximation at arbitrary finite targets, with the original
completed carrier preserved at every other finite prime. The first
reflecting vector is global; the second local vectors may be fractional.
No unit-value, good-prime-set or global integral-vector premise remains.
-/

noncomputable section

namespace NormEuclidean.ReflectionPairStrongApproximation

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation LocalPrimitivePairing
  ProperSpinor SpinorBaseChange AdelicOrthogonal AdelicApproximation AdelicSpinorKernel
  ReflectionApproximation ReflectionVectorNeighborhoods Filter Topology
open scoped NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

local instance finiteCharZero (p : HeightOneSpectrum (integerSubring K)) :
    CharZero (LocalField (integerSubring K) p) := Algebra.charZero_of_charZero K _

local instance finiteInvertibleTwo (p : HeightOneSpectrum (integerSubring K)) :
    Invertible (2 : LocalField (integerSubring K) p) := invertibleOfNonzero (by norm_num)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- Arbitrary finite equal-value targets are met in the actual global and local Wall kernels. -/
theorem exists_kernel_pair (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : 4 ≤ Module.finrank K V) (L : Submodule (integerSubring K) V) (hfg : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤)
    (q : NumberField.InfinitePlace K) (hiso : ¬ (Q.baseChange q.Completion).Anisotropic)
    (x : V) (hx : Q x ≠ 0) (T : Finset (HeightOneSpectrum (integerSubring K)))
    (z : (p : T) → Space (V := V) (integerSubring K) p.1)
    (hz : ∀ p, form (integerSubring K) p.1 Q (z p) =
      form (integerSubring K) p.1 Q (inclusion (integerSubring K) p.1 x))
    (U : (p : T) → Set (properGroup (form (integerSubring K) p.1 Q)))
    (hU : ∀ p, U p ∈ 𝓝 (valuePair
      (F := LocalField (integerSubring K) p.1) (E := Space (V := V) (integerSubring K) p.1)
      (form (integerSubring K) p.1 Q)
      (form_polarBilin_nondegenerate (integerSubring K) p.1 Q hQ)
      (inclusion (integerSubring K) p.1 x) (form_inclusion_ne_zero _ p.1 Q x hx)
      ⟨z p, hz p⟩)) :
    ∃ g : properGroup Q, properAmbientSpinorNormHom Q hQ g = 1 ∧
      (∀ p : HeightOneSpectrum (integerSubring K),
        properAmbientSpinorNormHom (form (integerSubring K) p Q)
          (form_polarBilin_nondegenerate (integerSubring K) p Q hQ)
          (localizeProper Q g p) = 1) ∧
      (∀ p : HeightOneSpectrum (integerSubring K), p ∉ T → localizeProper Q g p ∈
        properStabilizerWithin (form (integerSubring K) p Q) (carrier _ p L)) ∧
      ∀ p : T, localizeProper Q g p.1 ∈ U p := by
  classical
  obtain ⟨S, hTS, htwo, hunit, hself, hxout⟩ :=
    ApproximationGoodPrimes.exists_good_superset Q hQ L hfg hfull (Q x) hx x T
  let zS (p : S) : Space (V := V) (integerSubring K) p.1 :=
    if h : p.1 ∈ T then z ⟨p.1, h⟩ else inclusion (integerSubring K) p.1 x
  have hzS (p : S) : form (integerSubring K) p.1 Q (zS p) =
      form (integerSubring K) p.1 Q (inclusion (integerSubring K) p.1 x) := by
    dsimp only [zS]
    split_ifs with hp
    · exact hz ⟨p.1, hp⟩
    · rfl
  let US (p : S) : Set (properGroup (form (integerSubring K) p.1 Q)) :=
    if h : p.1 ∈ T then U ⟨p.1, h⟩ else
      properStabilizerWithin (form (integerSubring K) p.1 Q) (carrier _ p.1 L)
  have hUS (p : S) : US p ∈ 𝓝 (valuePair
      (F := LocalField (integerSubring K) p.1) (E := Space (V := V) (integerSubring K) p.1)
      (form (integerSubring K) p.1 Q)
      (form_polarBilin_nondegenerate (integerSubring K) p.1 Q hQ)
      (inclusion (integerSubring K) p.1 x) (form_inclusion_ne_zero _ p.1 Q x hx)
      ⟨zS p, hzS p⟩) := by
    by_cases hp : p.1 ∈ T
    · simpa only [US, zS, dif_pos hp] using hU ⟨p.1, hp⟩
    · have hopen := OrthogonalTopology.isOpen_properStabilizerWithin
        (form (integerSubring K) p.1 Q) (carrier _ p.1 L) (carrier_fg _ _ _ hfg)
        (OrthogonalTopology.isOpen_of_full _ (OrthogonalTopology.isOpen_localRing _ _)
          _ (carrier_full _ _ _ hfull))
      have hn := hopen.mem_nhds (Subgroup.one_mem
        (properStabilizerWithin (form (integerSubring K) p.1 Q) (carrier _ p.1 L)))
      simpa only [US, zS, dif_neg hp, valuePair_eq, doubleReflection_self] using hn
  obtain ⟨W, hW, hcontrol⟩ := exists_finite_vector_neighborhoods Q hQ x hx S zS hzS US hUS
  have hzval (p : S) : form (integerSubring K) p.1 Q (zS p) =
      algebraMap K (LocalField (integerSubring K) p.1) (Q x) := by
    rw [hzS, form_inclusion]
  obtain ⟨y, hy, hyT, hyout⟩ := NonzeroValueStrongApproximation.exists_vector Q hQ hdim
    L hfg hfull (Q x) hx ⟨x, rfl⟩ S hunit htwo hself q hiso zS hzval W hW
  have hy0 : Q y ≠ 0 := hy.trans_ne hx
  let g := doubleReflection Q hQ x hx y hy0
  have htargets := hcontrol y hy hyT
  refine ⟨g, htargets.1, ?_, ?_, ?_⟩
  · intro p
    exact OffTargetReflectionPairs.localize_pair_spinorNorm Q hQ x hx y hy0 hy.symm p
  · intro p hpT
    by_cases hpS : p ∈ S
    · have h := htargets.2 ⟨p, hpS⟩
      dsimp only [US] at h
      rw [dif_neg hpT] at h
      exact h
    · exact OffTargetReflectionPairs.localize_pair_mem_stabilizer Q hQ L
        x hx y hy0 hy.symm p (hself p hpS) (hxout p hpS) (hyout p hpS) (hunit p hpS)
  · intro p
    have h := htargets.2 ⟨p.1, hTS p.2⟩
    simpa only [US, dif_pos p.2] using h

set_option backward.isDefEq.respectTransparency false in
/-- The same construction is an actual restricted finite-adelic Wall-kernel approximant. -/
theorem exists_adelic_kernel_pair (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : 4 ≤ Module.finrank K V) (L : Lattice (integerSubring K) Q)
    (q : NumberField.InfinitePlace K) (hiso : ¬ (Q.baseChange q.Completion).Anisotropic)
    (x : V) (hx : Q x ≠ 0) (T : Finset (HeightOneSpectrum (integerSubring K)))
    (z : (p : T) → Space (V := V) (integerSubring K) p.1)
    (hz : ∀ p, form (integerSubring K) p.1 Q (z p) =
      form (integerSubring K) p.1 Q (inclusion (integerSubring K) p.1 x))
    (U : (p : T) → Set (properGroup (form (integerSubring K) p.1 Q)))
    (hU : ∀ p, U p ∈ 𝓝 (valuePair
      (F := LocalField (integerSubring K) p.1) (E := Space (V := V) (integerSubring K) p.1)
      (form (integerSubring K) p.1 Q)
      (form_polarBilin_nondegenerate (integerSubring K) p.1 Q hQ)
      (inclusion (integerSubring K) p.1 x) (form_inclusion_ne_zero _ p.1 Q x hx)
      ⟨z p, hz p⟩)) :
    ∃ g : properGroup Q, properAmbientSpinorNormHom Q hQ g = 1 ∧
      InSpinorKernel Q hQ L (finiteDiagonal Q L g) ∧
      (∀ p : HeightOneSpectrum (integerSubring K), p ∉ T → localizeProper Q g p ∈
        properStabilizerWithin (form (integerSubring K) p Q) (carrier _ p L.carrier)) ∧
      ∀ p : T, localizeProper Q g p.1 ∈ U p := by
  obtain ⟨g, hg, hall, hout, htargets⟩ := exists_kernel_pair Q hQ hdim
    L.carrier L.finite L.full q hiso x hx T z hz U hU
  exact ⟨g, hg, hall, hout, htargets⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Approximate a global equal-value pair with integral stabilizers away from the targets. -/
theorem exists_near_pair (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : 4 ≤ Module.finrank K V) (L : Submodule (integerSubring K) V) (hfg : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤)
    (q : NumberField.InfinitePlace K) (hiso : ¬ (Q.baseChange q.Completion).Anisotropic)
    (x : V) (hx : Q x ≠ 0) (y : V) (hy : Q y = Q x)
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (U : (p : T) → Set (properGroup (form (integerSubring K) p.1 Q)))
    (hU : ∀ p, U p ∈ 𝓝 (localizeProper Q
      (doubleReflection Q hQ x hx y (hy.trans_ne hx)) p.1)) :
    ∃ g : properGroup Q, properAmbientSpinorNormHom Q hQ g = 1 ∧
      (∀ p : HeightOneSpectrum (integerSubring K), p ∉ T → localizeProper Q g p ∈
        properStabilizerWithin (form (integerSubring K) p Q) (carrier _ p L)) ∧
      ∀ p : T, localizeProper Q g p.1 ∈ U p := by
  have hval (p : T) : form (integerSubring K) p.1 Q (inclusion _ p.1 y) =
      form (integerSubring K) p.1 Q (inclusion _ p.1 x) := by
    rw [form_inclusion, form_inclusion, hy]
  have htargets (p : T) : U p ∈ 𝓝 (valuePair
      (F := LocalField (integerSubring K) p.1) (E := Space (V := V) (integerSubring K) p.1)
      (form (integerSubring K) p.1 Q)
      (form_polarBilin_nondegenerate (integerSubring K) p.1 Q hQ)
      (inclusion _ p.1 x) (form_inclusion_ne_zero _ p.1 Q x hx)
      ⟨inclusion _ p.1 y, hval p⟩) := by
    rw [valuePair_eq, ← OffTargetReflectionPairs.localize_pair_eq]
    exact hU p
  obtain ⟨g, hg, _, hout, htargets⟩ := exists_kernel_pair Q hQ hdim L hfg hfull q hiso
    x hx T (fun p ↦ inclusion _ p.1 y) hval U htargets
  exact ⟨g, hg, hout, htargets⟩

end NormEuclidean.ReflectionPairStrongApproximation
