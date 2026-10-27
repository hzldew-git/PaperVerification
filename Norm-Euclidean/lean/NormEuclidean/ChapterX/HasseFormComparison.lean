import NormEuclidean.SpinorBridge
import Bong.QuadraticSpace.ScalarExtension

/-!
# Quadratic forms and the field spaces in the Hasse proof

The comparison preserves every quadratic value, including on the entire
scalar extension tensor space. It has no local-to-global hypothesis.
-/

noncomputable section

namespace NormEuclidean.HasseFormComparison

open scoped TensorProduct

variable {K F V : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]
  [AddCommGroup V] [Module K V]

/-- The quadratic form carried by a symmetric bilinear quadratic space. -/
def form (q : Bong.QuadraticSpace K V) : QuadraticForm K V := q.bilin.toQuadraticMap

omit [CharZero K] in
@[simp] theorem form_apply (q : Bong.QuadraticSpace K V) (x : V) :
    form q x = q.quadratic x := rfl

/-- The polar form is twice the nondegenerate symmetric bilinear form. -/
theorem regular (q : Bong.QuadraticSpace K V) : (form q).polarBilin.Nondegenerate := by
  have h (x y : V) : (form q).polarBilin x y = 2 * q.bilin x y := by
    rw [form, LinearMap.BilinMap.polarBilin_toQuadraticMap]
    change q.bilin x y + q.bilin y x = 2 * q.bilin x y
    rw [q.isSymm.eq y x]
    ring
  constructor
  · intro x hx
    apply q.nondegenerate.1 x
    intro y
    exact (mul_eq_zero.mp ((h x y).symm.trans (hx y))).resolve_left (by norm_num)
  · intro y hy
    apply q.nondegenerate.2 y
    intro x
    exact (mul_eq_zero.mp ((h x y).symm.trans (hy x))).resolve_left (by norm_num)

variable [FiniteDimensional K V] [Invertible (2 : K)]

/-- Agreement on the entire tensor space, rather than only on pure tensors. -/
theorem form_scalarExtension (q : Bong.QuadraticSpace K V) :
    form (q.scalarExtension (E := F)) = (form q).baseChange F := by
  apply _root_.baseChange_ext
  intro x
  simp only [form_apply, Bong.QuadraticSpace.scalarExtension_quadratic_tmul,
    QuadraticForm.baseChange_tmul, one_pow, one_mul]

/-- Value equality in the conventions used by the project's completed forms. -/
theorem scalarExtension_value (q : Bong.QuadraticSpace K V) (x : F ⊗[K] V) :
    (q.scalarExtension (E := F)).quadratic x = (form q).baseChange F x :=
  congrArg (fun P ↦ P x) (form_scalarExtension q)

/-- The two isotropy conditions on the actual scalar extension agree. -/
theorem scalarExtension_isotropic_iff (q : Bong.QuadraticSpace K V) :
    (∃ x, x ≠ 0 ∧ (q.scalarExtension (E := F)).quadratic x = 0) ↔
      ¬ ((form q).baseChange F).Anisotropic := by
  rw [QuadraticMap.not_anisotropic_iff_exists]
  simp only [scalarExtension_value]

omit [FiniteDimensional K V] [Invertible (2 : K)] in
/-- Returning from the project's half-polar space gives the original form. -/
@[simp] theorem form_quadraticSpace (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) : form (SpinorBridge.quadraticSpace Q hQ) = Q := by
  ext x
  exact SpinorBridge.quadraticSpace_quadratic Q hQ x

/-- The half-polar convention also agrees at every actual field extension. -/
theorem quadraticSpace_scalarExtension_value (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (x : F ⊗[K] V) :
    ((SpinorBridge.quadraticSpace Q hQ).scalarExtension (E := F)).quadratic x =
      Q.baseChange F x := by
  rw [scalarExtension_value, form_quadraticSpace]

end NormEuclidean.HasseFormComparison
