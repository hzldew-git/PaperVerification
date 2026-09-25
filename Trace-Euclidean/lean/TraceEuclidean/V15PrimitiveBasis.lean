import Mathlib.LinearAlgebra.FreeModule.Int
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Extending a primitive vector to an integral basis

This module packages the Smith-normal-form step needed in the cubic Hunter
argument.  A primitive vector in a free rank-three `ℤ`-module occurs as the
first vector of an integral basis.
-/

namespace TraceEuclidean

noncomputable section

open Module Submodule

/-- A vector is primitive when it cannot be a nonunit integral multiple of
another vector. -/
def V15IsPrimitiveVector {M : Type*} [AddCommGroup M]
    (v : M) : Prop :=
  ∀ (a : ℤ) (x : M), a • x = v → IsUnit a

/-- A primitive vector in a free rank-three integral module extends to a basis
whose zeroth vector is the supplied vector. -/
theorem v15_exists_fin_three_basis_zero_eq_of_primitive
    {M : Type*} [AddCommGroup M]
    (b : Basis (Fin 3) ℤ M) (v : M)
    (hv : V15IsPrimitiveVector v) :
    ∃ b' : Basis (Fin 3) ℤ M, b' 0 = v := by
  have hv0 : v ≠ 0 := by
    intro hzero
    have hunit : IsUnit (0 : ℤ) := hv 0 0 (by simp [hzero])
    exact not_isUnit_zero hunit
  let N : Submodule ℤ M := ℤ ∙ v
  let data := N.smithNormalForm b
  obtain ⟨n, snf⟩ := data
  letI : Module.Free ℤ N := Module.Free.of_basis snf.bN
  have hfinN : Module.finrank ℤ N = 1 := by
    let vN : N := ⟨v, Submodule.mem_span_singleton_self v⟩
    apply finrank_eq_one vN
    · intro h
      exact hv0 (congrArg Subtype.val h)
    · intro w
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp w.2
      exact ⟨c, Subtype.ext hc⟩
  have hn : n = 1 := by
    have hcard := Module.finrank_eq_card_basis snf.bN
    simpa using hcard.symm.trans hfinN
  subst n
  let vN : N := ⟨v, Submodule.mem_span_singleton_self v⟩
  let d : ℤ := snf.bN.repr vN 0
  have hv_bN : vN = d • snf.bN 0 := by
    rw [← snf.bN.sum_repr vN]
    simp [d]
  have hvM : v = d • (snf.bN 0 : M) := by
    exact congrArg Subtype.val hv_bN
  have hv_bM : (d * snf.a 0) • snf.bM (snf.f 0) = v := by
    calc
      (d * snf.a 0) • snf.bM (snf.f 0) =
          d • (snf.a 0 • snf.bM (snf.f 0)) :=
        (smul_smul d (snf.a 0) (snf.bM (snf.f 0))).symm
      _ = d • (snf.bN 0 : M) :=
        congrArg (fun z : M ↦ d • z) (snf.snf 0).symm
      _ = v := hvM.symm
  have hunit : IsUnit (d * snf.a 0) :=
    hv (d * snf.a 0) (snf.bM (snf.f 0)) hv_bM
  let e : Fin 3 ≃ Fin 3 := Equiv.swap 0 (snf.f 0)
  let b' : Basis (Fin 3) ℤ M :=
    (snf.bM.reindex e).unitsSMul (fun _ ↦ hunit.unit)
  refine ⟨b', ?_⟩
  rw [show b' 0 = (hunit.unit : ℤ) • snf.bM (snf.f 0) by
    simp [b', e, Basis.unitsSMul_apply]]
  rw [hunit.unit_spec]
  exact hv_bM

end

end TraceEuclidean
