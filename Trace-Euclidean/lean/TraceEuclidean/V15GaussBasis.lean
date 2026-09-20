import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
Elementary unimodular changes of a two-vector integer basis. These are the
coordinate moves needed for a direct proof of Gauss reduction.
-/

namespace TraceEuclidean

open Module

noncomputable section

def v15ShearCoordinates (k : ℤ) :
    (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun u := fun i ↦ if i = 0 then u 0 + k * u 1 else u 1
  invFun u := fun i ↦ if i = 0 then u 0 - k * u 1 else u 1
  left_inv u := by
    funext i
    fin_cases i <;> simp <;> ring
  right_inv u := by
    funext i
    fin_cases i <;> simp <;> ring
  map_add' u v := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' r u := by
    funext i
    fin_cases i <;> simp [smul_eq_mul] <;> ring

variable {M : Type*} [AddCommGroup M] [Module ℤ M]

def v15ShearBasis (B : Basis (Fin 2) ℤ M) (k : ℤ) : Basis (Fin 2) ℤ M :=
  Basis.ofEquivFun (B.equivFun.trans (v15ShearCoordinates k))

theorem v15ShearBasis_zero (B : Basis (Fin 2) ℤ M) (k : ℤ) :
    v15ShearBasis B k 0 = B 0 := by
  apply B.equivFun.injective
  ext i
  fin_cases i <;>
    simp [v15ShearBasis, v15ShearCoordinates, Basis.equivFun_ofEquivFun,
      Basis.equivFun_apply, Basis.equivFun_self]

theorem v15ShearBasis_one (B : Basis (Fin 2) ℤ M) (k : ℤ) :
    v15ShearBasis B k 1 = B 1 - k • B 0 := by
  apply B.equivFun.injective
  ext i
  fin_cases i <;>
    simp [v15ShearBasis, v15ShearCoordinates, Basis.equivFun_ofEquivFun,
      Basis.equivFun_apply, Basis.equivFun_self, smul_eq_mul] <;>
    ring

def v15SwapCoordinates :
    (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun u := fun i ↦ if i = 0 then u 1 else u 0
  invFun u := fun i ↦ if i = 0 then u 1 else u 0
  left_inv u := by funext i; fin_cases i <;> simp
  right_inv u := by funext i; fin_cases i <;> simp
  map_add' u v := by funext i; fin_cases i <;> simp <;> abel
  map_smul' r u := by funext i; fin_cases i <;> simp

def v15SwapBasis (B : Basis (Fin 2) ℤ M) : Basis (Fin 2) ℤ M :=
  Basis.ofEquivFun (B.equivFun.trans v15SwapCoordinates)

theorem v15SwapBasis_zero (B : Basis (Fin 2) ℤ M) :
    v15SwapBasis B 0 = B 1 := by
  apply B.equivFun.injective
  ext i
  fin_cases i <;>
    simp [v15SwapBasis, v15SwapCoordinates,
      Basis.equivFun_ofEquivFun, Basis.equivFun_apply, Basis.equivFun_self]

theorem v15SwapBasis_one (B : Basis (Fin 2) ℤ M) :
    v15SwapBasis B 1 = B 0 := by
  apply B.equivFun.injective
  ext i
  fin_cases i <;>
    simp [v15SwapBasis, v15SwapCoordinates,
      Basis.equivFun_ofEquivFun, Basis.equivFun_apply, Basis.equivFun_self]

def v15NegSecondCoordinates :
    (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun u := fun i ↦ if i = 0 then u 0 else -u 1
  invFun u := fun i ↦ if i = 0 then u 0 else -u 1
  left_inv u := by funext i; fin_cases i <;> simp
  right_inv u := by funext i; fin_cases i <;> simp
  map_add' u v := by funext i; fin_cases i <;> simp <;> abel
  map_smul' r u := by funext i; fin_cases i <;> simp

def v15NegSecondBasis (B : Basis (Fin 2) ℤ M) : Basis (Fin 2) ℤ M :=
  Basis.ofEquivFun (B.equivFun.trans v15NegSecondCoordinates)

theorem v15NegSecondBasis_zero (B : Basis (Fin 2) ℤ M) :
    v15NegSecondBasis B 0 = B 0 := by
  apply B.equivFun.injective
  ext i
  fin_cases i <;>
    simp [v15NegSecondBasis, v15NegSecondCoordinates,
      Basis.equivFun_ofEquivFun, Basis.equivFun_apply, Basis.equivFun_self]

theorem v15NegSecondBasis_one (B : Basis (Fin 2) ℤ M) :
    v15NegSecondBasis B 1 = -B 1 := by
  apply B.equivFun.injective
  ext i
  fin_cases i <;>
    simp [v15NegSecondBasis, v15NegSecondCoordinates,
      Basis.equivFun_ofEquivFun, Basis.equivFun_apply, Basis.equivFun_self]

/-- A two-dimensional nonnegative integral quadratic form admits a basis
with Gauss's inequalities. The proof minimizes the sum of diagonal values
over all bases and uses only elementary unimodular moves. -/
theorem v15_exists_gauss_basis
    (Bstart : Basis (Fin 2) ℤ M) (Q : M → ℕ) (C : M → M → ℤ)
    (hneg : ∀ x, Q (-x) = Q x)
    (hadd : ∀ x y, (Q (x + y) : ℤ) =
      (Q x : ℤ) + (Q y : ℤ) + 2 * C x y)
    (hsub : ∀ x y, (Q (x - y) : ℤ) =
      (Q x : ℤ) + (Q y : ℤ) - 2 * C x y)
    (hCneg : ∀ x y, C x (-y) = -C x y) :
    ∃ B : Basis (Fin 2) ℤ M,
      Q (B 0) ≤ Q (B 1) ∧
      0 ≤ C (B 0) (B 1) ∧
      2 * C (B 0) (B 1) ≤ (Q (B 0) : ℤ) := by
  classical
  let score (B : Basis (Fin 2) ℤ M) : ℕ := Q (B 0) + Q (B 1)
  have hex : ∃ s : ℕ, ∃ B : Basis (Fin 2) ℤ M, score B = s :=
    ⟨score Bstart, Bstart, rfl⟩
  obtain ⟨B, hB⟩ := Nat.find_spec hex
  have hmin (D : Basis (Fin 2) ℤ M) : score B ≤ score D := by
    rw [hB]
    exact Nat.find_min' hex ⟨D, rfl⟩
  have hbounds (D : Basis (Fin 2) ℤ M)
      (hDmin : ∀ E : Basis (Fin 2) ℤ M, score D ≤ score E) :
      2 * C (D 0) (D 1) ≤ (Q (D 0) : ℤ) ∧
        -(2 * C (D 0) (D 1)) ≤ (Q (D 0) : ℤ) := by
    have hminus := hDmin (v15ShearBasis D 1)
    simp only [score, v15ShearBasis_zero, v15ShearBasis_one,
      one_smul] at hminus
    have hminusZ : (Q (D 0) : ℤ) + Q (D 1) ≤
        (Q (D 0) : ℤ) + Q (D 1 - D 0) := by
      exact_mod_cast hminus
    have hswap : D 1 - D 0 = -(D 0 - D 1) := by abel
    have hsubQ : (Q (D 1 - D 0) : ℤ) =
        (Q (D 0) : ℤ) + Q (D 1) - 2 * C (D 0) (D 1) := by
      rw [hswap, hneg]
      exact hsub (D 0) (D 1)
    have hplus := hDmin (v15ShearBasis D (-1))
    have hplusBasis : v15ShearBasis D (-1) 1 = D 0 + D 1 := by
      rw [v15ShearBasis_one]
      simp
      abel
    simp only [score, v15ShearBasis_zero, hplusBasis] at hplus
    have hplusZ : (Q (D 0) : ℤ) + Q (D 1) ≤
        (Q (D 0) : ℤ) + Q (D 0 + D 1) := by
      exact_mod_cast hplus
    have haddQ := hadd (D 0) (D 1)
    omega
  let D : Basis (Fin 2) ℤ M :=
    if Q (B 0) ≤ Q (B 1) then B else v15SwapBasis B
  have hDscore : score D = score B := by
    by_cases h : Q (B 0) ≤ Q (B 1)
    · simp [D, h]
    · simp [D, h, score, v15SwapBasis_zero, v15SwapBasis_one,
        add_comm]
  have hDmin (E : Basis (Fin 2) ℤ M) : score D ≤ score E := by
    rw [hDscore]
    exact hmin E
  have hDorder : Q (D 0) ≤ Q (D 1) := by
    by_cases h : Q (B 0) ≤ Q (B 1)
    · simpa [D, h] using h
    · simp [D, h, v15SwapBasis_zero, v15SwapBasis_one]
      omega
  obtain ⟨hupper, hlower⟩ := hbounds D hDmin
  by_cases hcross : 0 ≤ C (D 0) (D 1)
  · exact ⟨D, hDorder, hcross, hupper⟩
  · let E := v15NegSecondBasis D
    refine ⟨E, ?_, ?_, ?_⟩
    · simpa [E, v15NegSecondBasis_zero, v15NegSecondBasis_one,
        hneg] using hDorder
    · rw [show E 0 = D 0 from v15NegSecondBasis_zero D,
        show E 1 = -D 1 from v15NegSecondBasis_one D,
        hCneg]
      omega
    · rw [show E 0 = D 0 from v15NegSecondBasis_zero D,
        show E 1 = -D 1 from v15NegSecondBasis_one D,
        hCneg]
      omega

end

end TraceEuclidean
