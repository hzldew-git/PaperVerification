import NormEuclidean.ChapterX.MultilinearSpan
import NormEuclidean.ChapterX.IntegralBiduality
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Intrinsic volume annihilates the integral dual quotient

An actual mixed determinant sends every integral-dual vector into the source
module when the pairing is integral on it. Adjugates provide integral coefficients.
Span induction extends this to the whole intrinsic volume ideal. No integral
basis, nondegeneracy or dual-index law is assumed.
-/

noncomputable section

namespace NormEuclidean.DualVolume

open Module IntegralVolume Matrix

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Every actual full-rank mixed determinant carries the integral dual back
into an integral-pairing source module, using actual adjugate coefficients. -/
theorem determinant_smul_dual_mem (B : LinearMap.BilinForm K V)
    (L : Submodule (integerSubring K) V)
    (hint : ∀ x ∈ L, ∀ y ∈ L, B x y ∈ integerSubring K)
    (x y : Fin (Module.finrank K V) → V) (hx : ∀ i, x i ∈ L) (hy : ∀ i, y i ∈ L)
    (z : V) (hz : z ∈ B.dualSubmodule L) : (pairingMatrix B x y).det • z ∈ L := by
  classical
  let R := integerSubring K
  let n := Module.finrank K V
  let A := pairingMatrix B x y
  by_cases hdet : A.det = 0
  · rw [hdet, zero_smul]
    exact L.zero_mem
  have hlin : LinearIndependent K x := by
    by_contra h
    exact hdet ((determinantLeft B n y).map_linearDependent x h)
  let b := basisOfLinearIndependentOfCardEqFinrank' x hlin (by simp)
  have hb (i : Fin n) : b i = x i := congrFun
    (coe_basisOfLinearIndependentOfCardEqFinrank' x hlin (by simp)) i
  let A₀ : Matrix (Fin n) (Fin n) R := fun i j ↦ ⟨B (x i) (y j), hint _ (hx i) _ (hy j)⟩
  have hA : A₀.map (algebraMap R K) = A := rfl
  have hzR (j : Fin n) : B z (y j) ∈ R := by
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hz (y j) (hy j))
    rw [← hr]
    exact r.property
  let w₀ : Fin n → R := fun j ↦ ⟨B z (y j), hzR j⟩
  let t : Fin n → R := w₀ ᵥ* A₀.adjugate
  have hw : (fun j ↦ (w₀ j : K)) = (fun i ↦ b.repr z i) ᵥ* A := by
    funext j
    change B z (y j) = ∑ i, b.repr z i * B (x i) (y j)
    conv_lhs => rw [← b.sum_repr z]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hb]
  have ht : (fun i ↦ (t i : K)) = A.det • (fun i ↦ b.repr z i) := by
    change (algebraMap R K) ∘ (w₀ ᵥ* A₀.adjugate) = _
    have hmap : (algebraMap R K) ∘ (w₀ ᵥ* A₀.adjugate) =
        ((algebraMap R K) ∘ w₀) ᵥ* (A₀.adjugate.map (algebraMap R K)) :=
      funext fun i ↦ RingHom.map_vecMul (algebraMap R K) A₀.adjugate w₀ i
    have hadj : A₀.adjugate.map (algebraMap R K) = A.adjugate :=
      (RingHom.map_adjugate (algebraMap R K) A₀).trans (congrArg Matrix.adjugate hA)
    rw [hmap, hadj]
    change (fun j ↦ (w₀ j : K)) ᵥ* A.adjugate = _
    rw [hw, vecMul_vecMul, mul_adjugate, vecMul_smul, vecMul_one]
  have heq : A.det • z = ∑ i, (t i : K) • x i := by
    conv_lhs => rw [← b.sum_repr z]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul, hb]
    have hi := congrFun ht i
    change (t i : K) = A.det * b.repr z i at hi
    rw [hi]
  rw [heq]
  exact L.sum_mem fun i _ ↦ L.smul_mem (t i) (hx i)

/-- The actual intrinsic volume ideal annihilates the integral-dual quotient.
It applies also to degenerate pairings and zero dimension. -/
theorem volume_smul_dual_mem (B : LinearMap.BilinForm K V)
    (L : Submodule (integerSubring K) V)
    (hint : ∀ x ∈ L, ∀ y ∈ L, B x y ∈ integerSubring K)
    (a : K) (ha : a ∈ volumeSubmodule B (Module.finrank K V) L)
    (z : V) (hz : z ∈ B.dualSubmodule L) : a • z ∈ L := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨p, rfl⟩ := ha
    exact determinant_smul_dual_mem B L hint _ _ (fun i ↦ (p.1 i).2)
      (fun i ↦ (p.2 i).2) z hz
  | zero => simpa only [zero_smul] using L.zero_mem
  | add a b _ _ ha hb => simpa only [add_smul] using L.add_mem ha hb
  | smul r a _ ha => simpa only [smul_assoc] using L.smul_mem r ha

end NormEuclidean.DualVolume
