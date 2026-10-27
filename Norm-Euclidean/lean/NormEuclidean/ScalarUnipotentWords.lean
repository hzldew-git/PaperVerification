import NormEuclidean.ChapterX.FiniteScalarStrongApproximation
import NormEuclidean.ChapterX.ProperWeakApproximation

/-!
# Scalar approximation of finite unipotent words with off-target integrality

The word argument only uses continuity, actual scalar-extension compatibility,
and the integral-parameter property of the two families. The factors are kept
in their original order.
-/

noncomputable section

namespace NormEuclidean.ScalarUnipotentWords

open IsDedekindDomain CompletedIntegralLattice ProperSpinor AdelicOrthogonal
  AdelicApproximation AdelicSpinorKernel Filter Topology
open scoped NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A family selector and simultaneous scalar parameters at the selected finite places. -/
abbrev Parameters (T : Finset (HeightOneSpectrum (integerSubring K))) :=
  Bool × ((v : T) → LocalField (integerSubring K) v.1)

/-- A literal finite local word, with its noncommutative order retained. -/
def wordImage (Q : QuadraticForm K V)
    (B : (w : HeightOneSpectrum (integerSubring K)) → Bool →
      LocalField (integerSubring K) w → properGroup (form (integerSubring K) w Q))
    (T : Finset (HeightOneSpectrum (integerSubring K))) (l : List (Parameters T)) :
    (v : T) → properGroup (form (integerSubring K) v.1 Q) :=
  fun v ↦ (l.map (fun p ↦ B v.1 p.1 (p.2 v))).prod

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- Scalar strong approximation passes to every finite word and preserves every
completed stabilizer outside the specified set. -/
theorem exists_kernel_word (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (L : Submodule (integerSubring K) V)
    (A : Bool → K → properGroup Q)
    (B : (w : HeightOneSpectrum (integerSubring K)) → Bool →
      LocalField (integerSubring K) w → properGroup (form (integerSubring K) w Q))
    (hnorm : ∀ b t, properAmbientSpinorNormHom Q hQ (A b t) = 1)
    (hnat : ∀ b t w, localizeProper Q (A b t) w =
      B w b (algebraMap K (LocalField (integerSubring K) w) t))
    (hcont : ∀ w b, Continuous (B w b))
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (hint : ∀ b t w, w ∉ T →
      algebraMap K (LocalField (integerSubring K) w) t ∈ LocalRing (integerSubring K) w →
      localizeProper Q (A b t) w ∈
        properStabilizerWithin (form (integerSubring K) w Q) (carrier _ w L))
    (l : List (Parameters T))
    (U : (v : T) → Set (properGroup (form (integerSubring K) v.1 Q)))
    (hU : ∀ v, U v ∈ 𝓝 (wordImage Q B T l v)) :
    ∃ g : properGroup Q, properAmbientSpinorNormHom Q hQ g = 1 ∧
      (∀ w : HeightOneSpectrum (integerSubring K), w ∉ T → localizeProper Q g w ∈
        properStabilizerWithin (form (integerSubring K) w Q) (carrier _ w L)) ∧
      ∀ v : T, localizeProper Q g v.1 ∈ U v := by
  classical
  induction l generalizing U with
  | nil =>
      refine ⟨1, map_one _, ?_, ?_⟩
      · intro w _
        have h1 : localizeProper Q 1 w = 1 :=
          congrFun ((ProperWeakApproximation.finiteProperDiagonal Q {w}).map_one)
            ⟨w, by simp⟩
        rw [h1]
        exact Subgroup.one_mem _
      · intro v
        have h1 : localizeProper Q 1 v.1 = 1 :=
          congrFun ((ProperWeakApproximation.finiteProperDiagonal Q T).map_one) v
        rw [h1]
        exact mem_of_mem_nhds (hU v)
  | cons p l ih =>
      have hsplit (v : T) : ∃ C, C ∈ 𝓝 (B v.1 p.1 (p.2 v)) ∧
          ∃ D, D ∈ 𝓝 (wordImage Q B T l v) ∧
            C ×ˢ D ⊆ {r | r.1 * r.2 ∈ U v} := by
        apply mem_nhds_prod_iff.mp
        exact (continuous_fst.mul continuous_snd).continuousAt.preimage_mem_nhds (hU v)
      choose C hC D hD hCD using hsplit
      have hW (v : T) : (B v.1 p.1) ⁻¹' C v ∈ 𝓝 (p.2 v) :=
        (hcont v.1 p.1).continuousAt.preimage_mem_nhds (hC v)
      obtain ⟨t, ht, htout⟩ := FiniteScalarStrongApproximation.exists_scalar T p.2
        (fun v ↦ (B v.1 p.1) ⁻¹' C v) hW
      obtain ⟨f, hf, hfout, hfnear⟩ := ih D hD
      refine ⟨A p.1 t * f, ?_, ?_, ?_⟩
      · rw [map_mul, hnorm, hf, one_mul]
      · intro w hw
        rw [localizeProper_mul]
        exact Subgroup.mul_mem _ (hint p.1 t w hw (htout w hw)) (hfout w hw)
      · intro v
        rw [localizeProper_mul, hnat]
        have hh : B v.1 p.1 (algebraMap K (LocalField (integerSubring K) v.1) t) ∈ C v :=
          ht v
        exact hCD v (show
          (B v.1 p.1 (algebraMap K (LocalField (integerSubring K) v.1) t),
            localizeProper Q f v.1) ∈ C v ×ˢ D v from ⟨hh, hfnear v⟩)

end NormEuclidean.ScalarUnipotentWords
