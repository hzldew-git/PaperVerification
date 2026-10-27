import NormEuclidean.ChapterX.HyperbolicKernelComparison
import NormEuclidean.ChapterX.OrthogonalTransport
import NormEuclidean.ArchimedeanComparison

/-!
# Kernel comparison in the actual completions of a hyperbolic extension

The tensor/product equivalence transports the actual Wall kernel to the
explicit hyperbolic model. It also supplies isotropy at every infinite place.
-/

noncomputable section

namespace NormEuclidean.CompletedHyperbolicKernel

open IsDedekindDomain CompletedIntegralLattice ProperSpinor OrthogonalTransport

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

local instance finiteCharZero (p : HeightOneSpectrum (integerSubring K)) :
    CharZero (LocalField (integerSubring K) p) := Algebra.charZero_of_charZero K _

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- The actual finite completed proper Wall kernel equals the ambient commutator group. -/
theorem kernel_iff_commutator (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (p : HeightOneSpectrum (integerSubring K))
    (g : properGroup (form (integerSubring K) p (Hyperbolic.form Q))) :
    properAmbientSpinorNormHom (form (integerSubring K) p (Hyperbolic.form Q))
      (form_polarBilin_nondegenerate (integerSubring K) p (Hyperbolic.form Q)
        (Hyperbolic.form_polarBilin_nondegenerate Q hQ)) g = 1 ↔
      g.1 ∈ commutator (ambientGroup (form (integerSubring K) p (Hyperbolic.form Q))) := by
  let P := form (integerSubring K) p Q
  let H := form (integerSubring K) p (Hyperbolic.form Q)
  let e := hyperbolicEquiv (V := V) (integerSubring K) p
  have he : ∀ z, Hyperbolic.form P (e z) = H z := hyperbolicEquiv_form _ p Q
  have hP : P.polarBilin.Nondegenerate := form_polarBilin_nondegenerate _ p Q hQ
  have hH : H.polarBilin.Nondegenerate := form_polarBilin_nondegenerate _ p _
    (Hyperbolic.form_polarBilin_nondegenerate Q hQ)
  let g' := properMap H (Hyperbolic.form P) e he g
  have hnorm := proper_spinorNorm_map H (Hyperbolic.form P) e he hH
    (Hyperbolic.form_polarBilin_nondegenerate P hP) g
  have hcomparison := HyperbolicKernelComparison.kernel_iff_commutator P hP g'
  constructor
  · intro hg
    have hmem := hcomparison.mp (hnorm.trans hg)
    exact (commutator_map_iff H (Hyperbolic.form P) e he g.1).mp hmem
  · intro hg
    exact Abelianization.commutator_subset_ker (ambientSpinorNormHom H hH) hg

set_option backward.isDefEq.respectTransparency false in
/-- Every actual infinite completion of the extension contains an isotropic hyperbolic vector. -/
theorem infinite_isotropic (Q : QuadraticForm K V) (v : NumberField.InfinitePlace K) :
    ¬ ((Hyperbolic.form Q).baseChange v.Completion).Anisotropic := by
  let e := (ArchimedeanComparison.hyperbolicIsometry v Q).toLinearEquiv
  let w : Hyperbolic v.Completion (ArchimedeanComparison.Space (V := V) v) := (0, 1, 0)
  rw [QuadraticMap.not_anisotropic_iff_exists]
  refine ⟨e.symm w, ?_, ?_⟩
  · intro hzero
    have h := congrArg e hzero
    rw [e.apply_symm_apply, map_zero] at h
    have hh := congrArg (fun z ↦ z.2.1) h
    exact one_ne_zero hh
  · have h := (ArchimedeanComparison.hyperbolicIsometry v Q).map_app (e.symm w)
    change Hyperbolic.form (ArchimedeanComparison.form v Q) (e (e.symm w)) = _ at h
    rw [e.apply_symm_apply] at h
    exact h.symm.trans (by simp [w, Hyperbolic.q])

end NormEuclidean.CompletedHyperbolicKernel
