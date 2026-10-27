import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.Tactic

/-!
# The subgroup index calculation in O'Meara 65:13 and 65:21

The local norm and S-unit index values are separate arithmetic inputs.
This file proves the group-theoretic balance and the resulting 65:13
formula once those values are established. Infinite indices are represented
by zero and are explicitly excluded or ruled out in every cancellation.
-/

noncomputable section

namespace NormEuclidean.NormIndexReduction

variable {G : Type*} [CommGroup G]

/-- The local index equals the principal-intersection index times the global index. -/
theorem local_global_balance (P U A : Subgroup G) (hcover : P ⊔ U = ⊤) (hA : A ≤ U) :
    A.relIndex (P ⊓ U) * (P ⊔ A).index = A.relIndex U := by
  have htop : (P ⊔ A) ⊔ U = ⊤ := by
    rw [sup_assoc, sup_of_le_right hA, hcover]
  have hres : (P ⊔ A).relIndex U = (P ⊔ A).index := by
    rw [← Subgroup.relIndex_sup_left U (P ⊔ A), htop, Subgroup.relIndex_top_right]
  have hinter : (P ⊔ A) ⊓ U = (P ⊓ U) ⊔ A := by
    rw [sup_comm P A, sup_inf_assoc_of_le P hA, sup_comm]
  have hB : ((P ⊓ U) ⊔ A).relIndex U = (P ⊔ A).index := by
    rw [← hinter, Subgroup.inf_relIndex_right, hres]
  have h := Subgroup.relIndex_mul_relIndex A ((P ⊓ U) ⊔ A) U
    le_sup_right (sup_le inf_le_right hA)
  rwa [Subgroup.relIndex_sup_right, hB] at h

/-- The S-unit index decomposes at the principal local-norm intersection. -/
theorem unit_intersection_balance (P U A C : Subgroup G) (hC : C ≤ (P ⊓ U) ⊓ A) :
    C.relIndex ((P ⊓ U) ⊓ A) * A.relIndex (P ⊓ U) = C.relIndex (P ⊓ U) := by
  simpa only [Subgroup.inf_relIndex_left] using
    Subgroup.relIndex_mul_relIndex C ((P ⊓ U) ⊓ A) (P ⊓ U) hC inf_le_left

/-- The literal 65:13 formula follows from the separately stated local
and S-unit index values. These arithmetic values are not proved by this lemma. -/
theorem formula_of_local_unit_indices (P U A C : Subgroup G)
    (hcover : P ⊔ U = ⊤) (hA : A ≤ U) (hC : C ≤ (P ⊓ U) ⊓ A)
    (b : ℕ) (hb : 0 < b) (hlocal : A.relIndex U = 2 ^ b)
    (hunit : C.relIndex (P ⊓ U) = 2 ^ (b - 1)) :
    (P ⊔ A).index = 2 * C.relIndex ((P ⊓ U) ⊓ A) ∧
      C.relIndex ((P ⊓ U) ⊓ A) ≠ 0 := by
  have h1 := local_global_balance P U A hcover hA
  have h2 := unit_intersection_balance P U A C hC
  rw [hlocal] at h1
  rw [hunit] at h2
  have hp : 2 ^ b = 2 * 2 ^ (b - 1) := by
    have hb' : b = (b - 1) + 1 := by omega
    conv_lhs => rw [hb', pow_succ]
    ring
  have hq : A.relIndex (P ⊓ U) ≠ 0 := by
    intro h
    rw [h, zero_mul] at h1
    exact (pow_ne_zero b (by decide : (2 : ℕ) ≠ 0)) h1.symm
  have hCfinite : C.relIndex ((P ⊓ U) ⊓ A) ≠ 0 := by
    intro h
    rw [h, zero_mul] at h2
    exact (pow_ne_zero (b - 1) (by decide : (2 : ℕ) ≠ 0)) h2.symm
  refine ⟨?_, hCfinite⟩
  apply Nat.mul_left_cancel (Nat.pos_of_ne_zero hq)
  calc
    A.relIndex (P ⊓ U) * (P ⊔ A).index = 2 * 2 ^ (b - 1) := h1.trans hp
    _ = 2 * (C.relIndex ((P ⊓ U) ⊓ A) * A.relIndex (P ⊓ U)) := by rw [h2]
    _ = _ := by ring

/-- A strict chain of `n` inclusions costs at least `2^n` in index. -/
theorem strict_chain_bound (H : ℕ → Subgroup G) (n : ℕ)
    (hfinite : (H 0).index ≠ 0) (hchain : ∀ i < n, H i < H (i + 1)) :
    2 ^ n * (H n).index ≤ (H 0).index ∧ (H n).index ≠ 0 := by
  induction n with
  | zero => simpa using And.intro (le_refl (H 0).index) hfinite
  | succ n ih =>
    obtain ⟨hbound, hn⟩ := ih (fun i hi ↦ hchain i (by omega))
    have hlt := hchain n (by omega)
    have hd := Subgroup.index_dvd_of_le hlt.le
    have hn' : (H (n + 1)).index ≠ 0 := ne_zero_of_dvd_ne_zero hn hd
    have hr0 : (H n).relIndex (H (n + 1)) ≠ 0 :=
      ne_zero_of_dvd_ne_zero hn (Subgroup.relIndex_dvd_index_of_le hlt.le)
    have hr1 : (H n).relIndex (H (n + 1)) ≠ 1 := by
      intro h
      exact hlt.not_ge (Subgroup.relIndex_eq_one.mp h)
    have hr : 2 ≤ (H n).relIndex (H (n + 1)) := by omega
    have hstep : 2 * (H (n + 1)).index ≤ (H n).index := by
      calc
        _ ≤ (H n).relIndex (H (n + 1)) * (H (n + 1)).index :=
          Nat.mul_le_mul_right _ hr
        _ = _ := Subgroup.relIndex_mul_index hlt.le
    refine ⟨?_, hn'⟩
    calc
      2 ^ (n + 1) * (H (n + 1)).index = 2 ^ n * (2 * (H (n + 1)).index) := by
        rw [pow_succ]
        ring
      _ ≤ 2 ^ n * (H n).index := Nat.mul_le_mul_left _ hstep
      _ ≤ _ := hbound

/-- The group-counting conclusion used in 65:21: a chain of length `n`
inside a subgroup, starting with index `2^(n+1)`, gives index at most two. -/
theorem strict_chain_index_le_two (H : ℕ → Subgroup G) (A : Subgroup G) (n : ℕ)
    (hindex : (H 0).index = 2 ^ (n + 1))
    (hchain : ∀ i < n, H i < H (i + 1)) (hA : H n ≤ A) :
    A.index ≠ 0 ∧ A.index ≤ 2 := by
  have hfinite : (H 0).index ≠ 0 := by rw [hindex]; positivity
  obtain ⟨hbound, hn⟩ := strict_chain_bound H n hfinite hchain
  have hd := Subgroup.index_dvd_of_le hA
  have hfiniteA : A.index ≠ 0 := ne_zero_of_dvd_ne_zero hn hd
  have hle : A.index ≤ (H n).index := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  have hmul : 2 ^ n * A.index ≤ 2 ^ (n + 1) :=
    (Nat.mul_le_mul_left _ hle).trans (hbound.trans_eq hindex)
  rw [pow_succ] at hmul
  have hp : 0 < (2 : ℕ) ^ n := by positivity
  exact ⟨hfiniteA, by nlinarith⟩

end NormEuclidean.NormIndexReduction
