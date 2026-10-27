import NormEuclidean.ChapterX.FinitelyGeneratedSquareIndex

/-!
# Square indices for groups embedded in field units

An injective field-unit embedding with minus one in its image has exactly
two elements of two-torsion. The finitely generated square-index formula
then gives two to the free rank plus one.
-/

noncomputable section

namespace NormEuclidean.FieldSquareIndex

open SquareIndex FinitelyGeneratedSquareIndex

/-- An embedded group containing minus one has exactly two elements of two-torsion. -/
theorem twoTorsion_card {G F : Type*} [CommGroup G] [Field F] [CharZero F]
    (i : G →* Fˣ) (hi : Function.Injective i) (n : G) (hn : i n = -1) :
    Nat.card (twoTorsion (Additive G)) = 2 := by
  have hn2 : n * n = 1 := by
    apply hi
    rw [map_mul, hn, map_one]
    simp
  let t : twoTorsion (Additive G) := ⟨Additive.ofMul n, by
    change (2 : ℕ) • Additive.ofMul n = 0
    rw [two_nsmul]
    exact congrArg Additive.ofMul hn2⟩
  have ht : t ≠ 0 := by
    intro h
    have hng : n = 1 := congrArg (fun x : twoTorsion (Additive G) ↦ x.val.toMul) h
    have hv := congrArg (fun g ↦ (i g).val) hng
    rw [hn, map_one] at hv
    norm_num at hv
  have hcases (x : twoTorsion (Additive G)) : x = 0 ∨ x = t := by
    have hx : (2 : ℕ) • x.val = 0 := x.property
    rw [two_nsmul] at hx
    have hmul : x.val.toMul * x.val.toMul = 1 := congrArg Additive.toMul hx
    have hv := congrArg (fun g ↦ (i g).val) hmul
    have hsq : (i x.val.toMul).val ^ 2 = 1 := by
      simpa only [map_mul, map_one, Units.val_mul, Units.val_one, pow_two] using hv
    rcases sq_eq_one_iff.mp hsq with h | h
    · left
      apply Subtype.ext
      apply Additive.toMul.injective
      apply hi
      apply Units.ext
      simpa using h
    · right
      apply Subtype.ext
      apply Additive.toMul.injective
      apply hi
      apply Units.ext
      exact h.trans (congrArg Units.val hn.symm)
  apply (Nat.card_eq_two_iff' (0 : twoTorsion (Additive G))).mpr
  exact ⟨t, ht, fun x hx ↦ (hcases x).resolve_left hx⟩

/-- The multiplicative square index, with the two-torsion contribution retained. -/
theorem square_index {G F : Type*} [CommGroup G] [Group.FG G] [Field F] [CharZero F]
    (i : G →* Fˣ) (hi : Function.Injective i) (n : G) (hn : i n = -1) :
    (powMonoidHom (α := G) 2).range.index =
      2 ^ (Module.finrank ℤ (Additive G) + 1) := by
  letI : Module.Finite ℤ (Additive G) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have heq : doubles (Additive G) =
      (powMonoidHom (α := G) 2).range.toAddSubgroup := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y.toMul, ?_⟩
      have h := congrArg Additive.toMul hy
      change y.toMul ^ 2 = x.toMul
      simpa only [nsmulAddMonoidHom_apply, toMul_nsmul] using h
    · rintro ⟨y, hy⟩
      refine ⟨Additive.ofMul y, ?_⟩
      apply Additive.toMul.injective
      rw [nsmulAddMonoidHom_apply, toMul_nsmul]
      simpa using hy
  have h := doubles_index (Additive G)
  rw [heq, Subgroup.index_toAddSubgroup, twoTorsion_card i hi n hn] at h
  simpa only [pow_succ] using h

end NormEuclidean.FieldSquareIndex
