import NormEuclidean.ChapterX.QuadraticValueRepresentation
import NormEuclidean.QuadraticBaseChangeNondegenerate
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# The negative-line reduction at actual field extensions

The field extension of Q plus the negative target line is identified with
the negative line of the field-extended form. Thus representation at an
actual completion gives isotropy of the actual completed global form used
by 66:1. This algebraic comparison does not assert Hasse--Minkowski.
-/

noncomputable section

namespace NormEuclidean.NegativeLineBaseChange

open QuadraticValueRepresentation
open scoped TensorProduct

variable {K F V : Type*} [Field K] [Field F] [Algebra K F]
  [AddCommGroup V] [Module K V] [Invertible (2 : K)]

/-- The completed global negative-line space is the product of the
completed original space and the actual scalar extension field. -/
def spaceEquiv : F ⊗[K] (V × K) ≃ₗ[F] (F ⊗[K] V) × F :=
  (TensorProduct.prodRight K F F V K).trans
    ((LinearEquiv.refl F (F ⊗[K] V)).prodCongr (TensorProduct.AlgebraTensorModule.rid K F F))

@[simp] theorem spaceEquiv_one_tmul (x : V) (t : K) :
    spaceEquiv (F := F) ((1 : F) ⊗ₜ[K] (x, t)) =
      ((1 : F) ⊗ₜ[K] x, algebraMap K F t) := by
  simp [spaceEquiv, Algebra.smul_def]

/-- The quadratic forms agree on the entire actual tensor space. -/
theorem form_comp_spaceEquiv (Q : QuadraticForm K V) (a : K) :
    (negativeLine (Q.baseChange F) (algebraMap K F a)).comp
        (spaceEquiv (K := K) (F := F) (V := V)).toLinearMap =
      (negativeLine Q a).baseChange F := by
  apply _root_.baseChange_ext
  rintro ⟨x, t⟩
  simp only [QuadraticMap.comp_apply, LinearEquiv.coe_coe, spaceEquiv_one_tmul,
    negativeLine_apply, QuadraticForm.baseChange_tmul, one_mul, Algebra.smul_def,
    mul_one, map_sub, map_mul, map_pow]

/-- Isotropy is transported through the actual negative-line comparison. -/
theorem anisotropic_iff (Q : QuadraticForm K V) (a : K) :
    ((negativeLine Q a).baseChange F).Anisotropic ↔
      (negativeLine (Q.baseChange F) (algebraMap K F a)).Anisotropic := by
  have heval (z : F ⊗[K] (V × K)) :
      negativeLine (Q.baseChange F) (algebraMap K F a) (spaceEquiv z) =
        (negativeLine Q a).baseChange F z :=
    congrArg (fun H ↦ H z) (form_comp_spaceEquiv (F := F) Q a)
  constructor
  · intro h z hz
    obtain ⟨t, rfl⟩ := (spaceEquiv (K := K) (F := F) (V := V)).surjective z
    have ht := h t ((heval t).symm.trans hz)
    simpa only [ht, map_zero]
  · intro h z hz
    apply (spaceEquiv (K := K) (F := F) (V := V)).injective
    rw [map_zero]
    exact h _ ((heval z).trans hz)

variable [FiniteDimensional K V] [Invertible (2 : F)]

/-- The scalar case of 66:3 reduces to isotropy of the actual scalar
extension of the global negative-line form, with no comparison assumption. -/
theorem represents_iff_completed_negativeLine_isotropic (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (a : K) :
    (∃ x : F ⊗[K] V, Q.baseChange F x = algebraMap K F a) ↔
      ¬ ((negativeLine Q a).baseChange F).Anisotropic := by
  rw [anisotropic_iff]
  exact represents_iff_negativeLine_isotropic (Q.baseChange F)
    (quadraticForm_baseChange_polarBilin_nondegenerate Q hQ) _

end NormEuclidean.NegativeLineBaseChange
