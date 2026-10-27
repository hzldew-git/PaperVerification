import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.Trace

/-!
# Trace-dual lattices commute with scalar extension of a separable field

The target is the actual tensor algebra, which need not be a field.
The proof uses the base-changed trace-dual basis and its exact trace
pairing. Thus it applies before decomposing the tensor algebra into
completed fields, including at split, ramified and dyadic primes.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.TraceTensorDuality

open Module Algebra
open scoped TensorProduct

variable {K L A : Type*} [Field K] [Field L] [Field A]
  [Algebra K L] [Algebra K A] [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual tensor algebra trace on an embedded global element is its scalar extension. -/
theorem trace_tmul (x : L) :
    Algebra.trace A (A ⊗[K] L) (1 ⊗ₜ[K] x) = algebraMap K A (Algebra.trace K L x) := by
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange,
    ← Algebra.trace_apply]

/-- The actual tensor trace pairing commutes with scalar extension. -/
theorem trace_tmul_mul (x y : L) :
    Algebra.trace A (A ⊗[K] L) ((1 ⊗ₜ[K] x) * (1 ⊗ₜ[K] y)) =
      algebraMap K A (Algebra.trace K L (x * y)) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_tmul]

/-- The two scalar-extended bases have the exact Kronecker trace pairing. -/
theorem trace_basis_dual (b : Basis ι K L) (i j : ι) :
    Algebra.trace A (A ⊗[K] L)
      (Algebra.TensorProduct.basis A b.traceDual i * Algebra.TensorProduct.basis A b j) =
        if j = i then 1 else 0 := by
  rw [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply, trace_tmul_mul,
    b.trace_traceDual_mul]
  split_ifs <;> simp only [map_one, map_zero]

/-- Trace pairing against the integral basis gives coordinates in the extended dual basis. -/
theorem repr_dual_trace (b : Basis ι K L) (x : A ⊗[K] L) (i : ι) :
    (Algebra.TensorProduct.basis A b.traceDual).repr x i =
      Algebra.trace A (A ⊗[K] L) (x * Algebra.TensorProduct.basis A b i) := by
  conv_rhs => rw [← (Algebra.TensorProduct.basis A b.traceDual).sum_repr x]
  simp only [Finset.sum_mul, Algebra.smul_mul_assoc, map_sum, map_smul, trace_basis_dual,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Scalar extension preserves nondegeneracy even when the tensor algebra splits. -/
theorem trace_nondegenerate (b : Basis ι K L) :
    (Algebra.traceForm A (A ⊗[K] L)).Nondegenerate := by
  have hl : (Algebra.traceForm A (A ⊗[K] L)).SeparatingLeft := by
    intro x hx
    apply (Algebra.TensorProduct.basis A b.traceDual).repr.injective
    ext i
    rw [map_zero, Finsupp.zero_apply, repr_dual_trace]
    exact hx _
  refine ⟨hl, ?_⟩
  intro x hx
  apply hl x
  intro y
  simpa only [Algebra.traceForm_apply, mul_comm] using hx y

variable (R : Type*) [CommRing R] [Algebra R A]

/-- The trace-dual integral span is the integral span of the scalar-extended global dual basis. -/
theorem dual_span (b : Basis ι K L) :
    (Algebra.traceForm A (A ⊗[K] L)).dualSubmodule
      (Submodule.span R (Set.range (Algebra.TensorProduct.basis A b))) =
        Submodule.span R (Set.range (Algebra.TensorProduct.basis A b.traceDual)) := by
  have hn := trace_nondegenerate (A := A) b
  rw [LinearMap.BilinForm.dualSubmodule_span_of_basis _ hn]
  congr 1
  apply congrArg Set.range
  apply (Algebra.traceForm A (A ⊗[K] L)).dualBasis_eq_iff hn _ _ |>.mpr
  intro i j
  exact trace_basis_dual b i j

end NormEuclidean.TraceTensorDuality
