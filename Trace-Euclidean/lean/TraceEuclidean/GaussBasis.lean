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

def shearCoordinates (k : ℤ) :
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

def shearBasis (B : Basis (Fin 2) ℤ M) (k : ℤ) : Basis (Fin 2) ℤ M :=
  Basis.ofEquivFun (B.equivFun.trans (shearCoordinates k))

theorem shearBasis_zero (B : Basis (Fin 2) ℤ M) (k : ℤ) :
    shearBasis B k 0 = B 0 := by
  apply B.equivFun.injective
  ext i
  fin_cases i <;>
    simp [shearBasis, shearCoordinates, Basis.equivFun_ofEquivFun,
      Basis.equivFun_apply, Basis.equivFun_self]

theorem shearBasis_one (B : Basis (Fin 2) ℤ M) (k : ℤ) :
    shearBasis B k 1 = B 1 - k • B 0 := by
  apply B.equivFun.injective
  ext i
  fin_cases i <;>
    simp [shearBasis, shearCoordinates, Basis.equivFun_ofEquivFun,
      Basis.equivFun_apply, Basis.equivFun_self, smul_eq_mul] <;>
    ring

def swapCoordinates :
    (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun u := fun i ↦ if i = 0 then u 1 else u 0
  invFun u := fun i ↦ if i = 0 then u 1 else u 0
  left_inv u := by funext i; fin_cases i <;> simp
  right_inv u := by funext i; fin_cases i <;> simp
  map_add' u v := by funext i; fin_cases i <;> simp <;> abel
  map_smul' r u := by funext i; fin_cases i <;> simp

def swapBasis (B : Basis (Fin 2) ℤ M) : Basis (Fin 2) ℤ M :=
  Basis.ofEquivFun (B.equivFun.trans swapCoordinates)

theorem swapBasis_zero (B : Basis (Fin 2) ℤ M) :
    swapBasis B 0 = B 1 := by
  apply B.equivFun.injective
  ext i
  fin_cases i <;>
    simp [swapBasis, swapCoordinates,
      Basis.equivFun_ofEquivFun, Basis.equivFun_apply, Basis.equivFun_self]

theorem swapBasis_one (B : Basis (Fin 2) ℤ M) :
    swapBasis B 1 = B 0 := by
  apply B.equivFun.injective
  ext i
  fin_cases i <;>
    simp [swapBasis, swapCoordinates,
      Basis.equivFun_ofEquivFun, Basis.equivFun_apply, Basis.equivFun_self]

def negSecondCoordinates :
    (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun u := fun i ↦ if i = 0 then u 0 else -u 1
  invFun u := fun i ↦ if i = 0 then u 0 else -u 1
  left_inv u := by funext i; fin_cases i <;> simp
  right_inv u := by funext i; fin_cases i <;> simp
  map_add' u v := by funext i; fin_cases i <;> simp <;> abel
  map_smul' r u := by funext i; fin_cases i <;> simp

def negSecondBasis (B : Basis (Fin 2) ℤ M) : Basis (Fin 2) ℤ M :=
  Basis.ofEquivFun (B.equivFun.trans negSecondCoordinates)

theorem negSecondBasis_zero (B : Basis (Fin 2) ℤ M) :
    negSecondBasis B 0 = B 0 := by
  apply B.equivFun.injective
  ext i
  fin_cases i <;>
    simp [negSecondBasis, negSecondCoordinates,
      Basis.equivFun_ofEquivFun, Basis.equivFun_apply, Basis.equivFun_self]

theorem negSecondBasis_one (B : Basis (Fin 2) ℤ M) :
    negSecondBasis B 1 = -B 1 := by
  apply B.equivFun.injective
  ext i
  fin_cases i <;>
    simp [negSecondBasis, negSecondCoordinates,
      Basis.equivFun_ofEquivFun, Basis.equivFun_apply, Basis.equivFun_self]

/-- A two-dimensional nonnegative integral quadratic form admits a basis
with Gauss's inequalities. The proof minimizes the sum of diagonal values
over all bases and uses only elementary unimodular moves. -/
theorem exists_gauss_basis
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
    have hminus := hDmin (shearBasis D 1)
    simp only [score, shearBasis_zero, shearBasis_one,
      one_smul] at hminus
    have hminusZ : (Q (D 0) : ℤ) + Q (D 1) ≤
        (Q (D 0) : ℤ) + Q (D 1 - D 0) := by
      exact_mod_cast hminus
    have hswap : D 1 - D 0 = -(D 0 - D 1) := by abel
    have hsubQ : (Q (D 1 - D 0) : ℤ) =
        (Q (D 0) : ℤ) + Q (D 1) - 2 * C (D 0) (D 1) := by
      rw [hswap, hneg]
      exact hsub (D 0) (D 1)
    have hplus := hDmin (shearBasis D (-1))
    have hplusBasis : shearBasis D (-1) 1 = D 0 + D 1 := by
      rw [shearBasis_one]
      simp
      abel
    simp only [score, shearBasis_zero, hplusBasis] at hplus
    have hplusZ : (Q (D 0) : ℤ) + Q (D 1) ≤
        (Q (D 0) : ℤ) + Q (D 0 + D 1) := by
      exact_mod_cast hplus
    have haddQ := hadd (D 0) (D 1)
    omega
  let D : Basis (Fin 2) ℤ M :=
    if Q (B 0) ≤ Q (B 1) then B else swapBasis B
  have hDscore : score D = score B := by
    by_cases h : Q (B 0) ≤ Q (B 1)
    · simp [D, h]
    · simp [D, h, score, swapBasis_zero, swapBasis_one,
        add_comm]
  have hDmin (E : Basis (Fin 2) ℤ M) : score D ≤ score E := by
    rw [hDscore]
    exact hmin E
  have hDorder : Q (D 0) ≤ Q (D 1) := by
    by_cases h : Q (B 0) ≤ Q (B 1)
    · simpa [D, h] using h
    · simp [D, h, swapBasis_zero, swapBasis_one]
      omega
  obtain ⟨hupper, hlower⟩ := hbounds D hDmin
  by_cases hcross : 0 ≤ C (D 0) (D 1)
  · exact ⟨D, hDorder, hcross, hupper⟩
  · let E := negSecondBasis D
    refine ⟨E, ?_, ?_, ?_⟩
    · simpa [E, negSecondBasis_zero, negSecondBasis_one,
        hneg] using hDorder
    · rw [show E 0 = D 0 from negSecondBasis_zero D,
        show E 1 = -D 1 from negSecondBasis_one D,
        hCneg]
      omega
    · rw [show E 0 = D 0 from negSecondBasis_zero D,
        show E 1 = -D 1 from negSecondBasis_one D,
        hCneg]
      omega

end

end TraceEuclidean
