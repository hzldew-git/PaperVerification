import NormEuclidean.FiniteUnipotentWords
import NormEuclidean.IntegralUnipotent
import NormEuclidean.ChapterX.RankOneVolumeFiniteness

/-!
# Strong approximation for finite ternary unipotent words
-/

noncomputable section

namespace NormEuclidean.TernaryWordApproximation

open IsDedekindDomain CompletedIntegralLattice ProperSpinor AdelicOrthogonal
  AdelicApproximation AdelicSpinorKernel TernaryKernelGeneration CompletedUnipotent
  Filter Topology
open scoped NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- Actual ternary kernel targets have global kernel approximants preserving the entire
completed hyperbolic lattice at every prime outside the target set. -/
theorem exists_kernel_approximation (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 1)
    (L : Lattice (integerSubring K) Q)
    (T : Finset (HeightOneSpectrum (integerSubring K)))
    (a : (v : T) → properGroup (form (integerSubring K) v.1 (Hyperbolic.form Q)))
    (ha : ∀ v : T, properAmbientSpinorNormHom
      (form (integerSubring K) v.1 (Hyperbolic.form Q))
      (form_polarBilin_nondegenerate (integerSubring K) v.1 (Hyperbolic.form Q)
        (Hyperbolic.form_polarBilin_nondegenerate Q hQ)) (a v) = 1)
    (U : (v : T) → Set (properGroup (form (integerSubring K) v.1 (Hyperbolic.form Q))))
    (hU : ∀ v, U v ∈ 𝓝 (a v)) :
    ∃ g : properGroup (Hyperbolic.form Q),
      properAmbientSpinorNormHom (Hyperbolic.form Q)
        (Hyperbolic.form_polarBilin_nondegenerate Q hQ) g = 1 ∧
      (∀ w : HeightOneSpectrum (integerSubring K), w ∉ T →
        localizeProper (Hyperbolic.form Q) g w ∈ properStabilizerWithin
          (form (integerSubring K) w (Hyperbolic.form Q))
          (carrier _ w L.hyperbolic.carrier)) ∧
      ∀ v : T, localizeProper (Hyperbolic.form Q) g v.1 ∈ U v := by
  let hA := UnaryClassNumber.anisotropic Q hQ hdim
  obtain ⟨u, hu, hu0⟩ := RankOneVolumeFiniteness.exists_nonzero_integral_value Q hQ
    (by omega) L
  obtain ⟨l, hl⟩ := FiniteUnipotentWords.exists_word Q hQ hdim u hu0 T a ha
  refine ScalarUnipotentWords.exists_kernel_word (Hyperbolic.form Q)
    (Hyperbolic.form_polarBilin_nondegenerate Q hQ) L.hyperbolic.carrier
    (fun b t ↦ family Q hQ hA b (t • u)) (fun w ↦ localFamily Q hQ hdim w u)
    (fun b t ↦ IntegralUnipotent.family_spinorNorm Q hQ hA b (t • u))
    (fun b t w ↦ localize_family Q hQ hdim hA w u b t)
    (fun w b ↦ continuous_localFamily Q hQ hdim w u b) T ?_ l U ?_
  · intro b t w _ ht
    rw [localize_family Q hQ hdim hA]
    exact IntegralUnipotent.localFamily_integral Q hQ hdim L u hu w b _ ht
  · intro v
    simpa only [hl] using hU v

end NormEuclidean.TernaryWordApproximation
