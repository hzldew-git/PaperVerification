import NormEuclidean.ChapterX.CommutatorStrongApproximation
import NormEuclidean.ChapterX.CompletedHyperbolicKernel

/-!
# Actual finite-adelic Wall-kernel approximation for hyperbolic extensions

For original rank at least two, 104:4 step 1(b) and the proved isotropic
kernel comparison supply the formerly explicit adelic approximation input.
-/

noncomputable section

namespace NormEuclidean.HyperbolicStrongApproximation

open IsDedekindDomain CompletedIntegralLattice ProperSpinor AdelicOrthogonal
  AdelicApproximation AdelicSpinorKernel

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- The actual, uniform finite-adelic strong approximation input
for an extended rank at least four. -/
theorem spinorKernelStrongApproximation (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : 2 ≤ Module.finrank K V) :
    HasSpinorKernelStrongApproximation (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ) := by
  intro L a ha
  let q : NumberField.InfinitePlace K := Classical.arbitrary _
  have hr : Module.finrank K (Hyperbolic K V) = Module.finrank K V + 2 := by
    simp [Hyperbolic, Module.finrank_prod]
  exact CommutatorStrongApproximation.exists_adelic_hit (Hyperbolic.form Q)
    (Hyperbolic.form_polarBilin_nondegenerate Q hQ) (by omega) q
    (CompletedHyperbolicKernel.infinite_isotropic Q q) L a
    (fun v ↦ (CompletedHyperbolicKernel.kernel_iff_commutator Q hQ v (a v)).mp (ha v))

end NormEuclidean.HyperbolicStrongApproximation
