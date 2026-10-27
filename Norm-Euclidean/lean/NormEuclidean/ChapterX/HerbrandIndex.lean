import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Ring

/-!
# Herbrand's finite-index calculation (O'Meara 65:9)

The statement uses natural subgroup indices, so nonzero indices explicitly
record finiteness. The result proves the cross-multiplied ratio and both
global finiteness conclusions. No norm-index formula is an input.
-/

noncomputable section

namespace NormEuclidean.HerbrandIndex

variable {G : Type*} [CommGroup G]

/-- The index decomposes into the indices on the image and on the kernel. -/
theorem image_kernel_index (P : Subgroup G) (f : G →* G) :
    P.index = (P.map f).relIndex f.range * P.relIndex f.ker := by
  calc
    _ = P.relIndex (P ⊔ f.ker) * (P ⊔ f.ker).index :=
      (Subgroup.relIndex_mul_index le_sup_left).symm
    _ = P.relIndex f.ker * (P.map f).relIndex f.range := by
      rw [Subgroup.relIndex_sup_left, ← Subgroup.index_comap, Subgroup.comap_map_eq]
    _ = _ := Nat.mul_comm _ _

/-- One of the two counting identities in the proof of Herbrand's lemma. -/
theorem balance (P : Subgroup G) (N T : G →* G)
    (hNT : N.range ≤ T.ker) (hNP : P.map N ≤ P) :
    P.index * (P.map N).relIndex (P ⊓ T.ker) =
      ((P.map T).relIndex T.range * (P.map N).relIndex N.range) *
        N.range.relIndex T.ker := by
  have hsub : P.map N ≤ P ⊓ T.ker :=
    le_inf hNP ((P.map_le_range N).trans hNT)
  have h1 : (P.map N).relIndex (P ⊓ T.ker) * P.relIndex T.ker =
      (P.map N).relIndex T.ker := by
    simpa only [Subgroup.inf_relIndex_right] using
      Subgroup.relIndex_mul_relIndex (P.map N) (P ⊓ T.ker) T.ker hsub inf_le_right
  have h2 := Subgroup.relIndex_mul_relIndex (P.map N) N.range T.ker (P.map_le_range N) hNT
  calc
    _ = (P.map T).relIndex T.range *
        ((P.map N).relIndex (P ⊓ T.ker) * P.relIndex T.ker) := by
      rw [image_kernel_index P T]
      ring
    _ = (P.map T).relIndex T.range * (P.map N).relIndex T.ker := by rw [h1]
    _ = _ := by rw [← h2]; ring

/-- Herbrand's lemma, with finite input indices and finite output indices
stated explicitly. The cross multiplication avoids division by an infinite index. -/
theorem herbrand (P : Subgroup G) (N T : G →* G)
    (hP : P.index ≠ 0) (hNT : N.range ≤ T.ker) (hTN : T.range ≤ N.ker)
    (hNP : P.map N ≤ P) (hTP : P.map T ≤ P)
    (ha : (P.map N).relIndex (P ⊓ T.ker) ≠ 0)
    (hb : (P.map T).relIndex (P ⊓ N.ker) ≠ 0) :
    N.range.relIndex T.ker * (P.map T).relIndex (P ⊓ N.ker) =
        T.range.relIndex N.ker * (P.map N).relIndex (P ⊓ T.ker) ∧
      N.range.relIndex T.ker ≠ 0 ∧ T.range.relIndex N.ker ≠ 0 := by
  let a := (P.map N).relIndex (P ⊓ T.ker)
  let b := (P.map T).relIndex (P ⊓ N.ker)
  let A := N.range.relIndex T.ker
  let B := T.range.relIndex N.ker
  let c := (P.map T).relIndex T.range * (P.map N).relIndex N.range
  have h1 : P.index * a = c * A := balance P N T hNT hNP
  have h2 : P.index * b = c * B := by
    calc
      _ = ((P.map N).relIndex N.range * (P.map T).relIndex T.range) * B :=
        balance P T N hTN hTP
      _ = _ := by dsimp [c]; ring
  have hc : c ≠ 0 := by
    intro h
    rw [h, zero_mul] at h1
    exact (mul_ne_zero hP ha) h1
  have hA : A ≠ 0 := by
    intro h
    rw [h, mul_zero] at h1
    exact (mul_ne_zero hP ha) h1
  have hB : B ≠ 0 := by
    intro h
    rw [h, mul_zero] at h2
    exact (mul_ne_zero hP hb) h2
  refine ⟨?_, hA, hB⟩
  apply Nat.mul_left_cancel (Nat.pos_of_ne_zero hc)
  calc
    c * (A * b) = (c * A) * b := by ring
    _ = (P.index * a) * b := by rw [h1]
    _ = (P.index * b) * a := by ring
    _ = (c * B) * a := by rw [h2]
    _ = c * (B * a) := by ring

end NormEuclidean.HerbrandIndex
