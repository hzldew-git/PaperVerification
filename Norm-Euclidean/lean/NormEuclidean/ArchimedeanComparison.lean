import NormEuclidean.CompletedHyperbolic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Actual archimedean quadratic spaces

At an infinite place the comparison is between quadratic spaces over the
actual absolute-value completion, with no integral lattice condition.
Both real and complex places occur in `InfinitePlace K`.
-/

open scoped TensorProduct
namespace NormEuclidean.ArchimedeanComparison

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
variable (v : NumberField.InfinitePlace K)

abbrev Space := v.Completion ⊗[K] V

noncomputable def equiv (e : V ≃ₗ[K] W) :
    Space (V := V) v ≃ₗ[v.Completion] Space (V := W) v :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) e

noncomputable def hyperbolicEquiv :
    Space (V := Hyperbolic K V) v ≃ₗ[v.Completion]
      Hyperbolic v.Completion (Space (V := V) v) :=
  TensorProduct.prodRight K v.Completion v.Completion V (K × K) ≪≫ₗ
    (LinearEquiv.refl v.Completion (Space (V := V) v)).prodCongr
      (TensorProduct.prodRight K v.Completion v.Completion K K ≪≫ₗ
        (TensorProduct.AlgebraTensorModule.rid K v.Completion v.Completion).prodCongr
          (TensorProduct.AlgebraTensorModule.rid K v.Completion v.Completion))

@[simp] theorem hyperbolicEquiv_tmul (a : v.Completion) (x : Hyperbolic K V) :
    hyperbolicEquiv v (a ⊗ₜ[K] x) =
      (a ⊗ₜ[K] x.1, algebraMap K v.Completion x.2.1 * a,
        algebraMap K v.Completion x.2.2 * a) := by
  simp [hyperbolicEquiv, Algebra.smul_def]

theorem finrank_space : Module.finrank v.Completion (Space (V := V) v) =
    Module.finrank K V := Module.finrank_baseChange

variable [Invertible (2 : K)]
noncomputable def form (Q : QuadraticForm K V) : QuadraticForm v.Completion (Space (V := V) v) :=
  Q.baseChange v.Completion

@[simp] theorem form_one_tmul (Q : QuadraticForm K V) (x : V) :
    form v Q (1 ⊗ₜ[K] x) = algebraMap K v.Completion (Q x) := by
  simp [form, Algebra.smul_def]

/-- Transport an actual ambient quadratic isometry to an infinite completion. -/
noncomputable def isometry {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    (e : Q.IsometryEquiv Q') : (form v Q).IsometryEquiv (form v Q') where
  toLinearEquiv := equiv v e.toLinearEquiv
  map_app' z := by
    have h : (form v Q').comp (equiv v e.toLinearEquiv).toLinearMap = form v Q := by
      apply baseChange_ext
      intro x
      change form v Q' (1 ⊗ₜ[K] e x) = form v Q (1 ⊗ₜ[K] x)
      simp only [form_one_tmul, e.map_app]
    exact DFunLike.congr_fun h z

/-- Completion commutes with adjoining the hyperbolic plane, at every real
and complex place. -/
noncomputable def hyperbolicIsometry (Q : QuadraticForm K V) :
    (form v (Hyperbolic.form Q)).IsometryEquiv (Hyperbolic.form (form v Q)) where
  toLinearEquiv := hyperbolicEquiv v
  map_app' z := by
    have h : (Hyperbolic.form (form v Q)).comp (hyperbolicEquiv v).toLinearMap =
        form v (Hyperbolic.form Q) := by
      apply baseChange_ext
      intro x
      change Hyperbolic.form (form v Q) (hyperbolicEquiv v (1 ⊗ₜ[K] x)) = _
      simp [Hyperbolic.q, form_one_tmul]
      apply NumberField.InfinitePlace.Completion.ext
      simp [UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_mul]
    exact DFunLike.congr_fun h z

/-- The completed hyperbolic extension represents every scalar at every
infinite place. This covers both real and complex places without a signature premise. -/
theorem hyperbolic_universal (Q : QuadraticForm K V) (t : v.Completion) :
    ∃ z : Space (V := Hyperbolic K V) v, form v (Hyperbolic.form Q) z = t := by
  let e := hyperbolicIsometry v Q
  refine ⟨e.symm (0, t, 1), ?_⟩
  rw [e.symm.map_app]
  simp [Hyperbolic.q]

end NormEuclidean.ArchimedeanComparison
