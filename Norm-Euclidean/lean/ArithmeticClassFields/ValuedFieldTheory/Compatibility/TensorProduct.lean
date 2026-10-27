import Mathlib.LinearAlgebra.TensorProduct.Defs

/-!
# Two-case tensor-product induction for the pinned compiler

The newer source uses the pure-tensor and addition cases. Zero is already
a pure tensor, so the current three-case eliminator proves that interface.
-/

namespace TensorProduct

open scoped TensorProduct

universe u v w
variable {R : Type u} [CommSemiring R]
  {M : Type v} [AddCommMonoid M] [Module R M]
  {N : Type w} [AddCommMonoid N] [Module R N]

/-- Pure tensors and addition suffice for propositions about a tensor product. -/
@[elab_as_elim, induction_eliminator]
protected theorem inductionOn {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (tmul : ∀ x y, motive (x ⊗ₜ[R] y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z := by
  exact TensorProduct.induction_on (motive := motive) z
    (by simpa only [zero_tmul] using tmul (0 : M) (0 : N)) tmul add

end TensorProduct
