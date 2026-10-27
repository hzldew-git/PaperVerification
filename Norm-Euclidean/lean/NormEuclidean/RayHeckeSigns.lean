import NormEuclidean.RayHeckeCharacter

/-!
# The actual real-place signs of a finite-order ray character

At a real place the local character is trivial on positive elements and
is determined by its value at minus one. That value is plus or minus one.
The latter case is exactly membership in the infinite conductor.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.RayHeckeSigns

open NumberField RayHeckeCharacter
open scoped NumberField Classical

variable {F : Type*} [Field F] [NumberField F] {m : RayClass.Modulus F}

def localCharacter (χ : Character m) (v : RayClass.RealPlace F) : v.1.Completionˣ →* ℂ :=
  (onIdeleClass χ).comp (IdeleGroup.infinitePlaceIdeleClass v.1)

/-- Positivity kills the local character even at a selected real place. -/
theorem positive (χ : Character m) (v : RayClass.RealPlace F) (x : v.1.Completionˣ)
    (hx : x ∈ RayClass.infinitePositiveSubgroup v.1) : localCharacter χ v x = 1 := by
  apply congruence_le_kernel χ
  rw [RayClass.Modulus.congruenceSubgroup]
  refine ⟨IdeleGroup.infinitePlaceIdele v.1 x, Subgroup.mem_sup_left ?_, rfl⟩
  rw [RayClass.Modulus.mem_ideleCongruenceSubgroup_iff]
  refine ⟨?_, ?_⟩
  · rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff]
    intro w _
    change IdeleGroup.infiniteComponent w.1 (IdeleGroup.infinitePlaceIdele v.1 x) ∈ _
    by_cases hw : w = v
    · subst w
      simpa only [IdeleGroup.infinitePlaceIdele_infiniteComponent_same] using hx
    · rw [IdeleGroup.infinitePlaceIdele_infiniteComponent_of_ne v.1 w.1 x
        (fun h ↦ hw (Subtype.ext h))]
      exact Subgroup.one_mem _
  · rw [RayClass.mem_finiteCongruenceSubgroup_iff]
    intro w
    change IdeleGroup.finiteComponent w (IdeleGroup.infinitePlaceIdele v.1 x) ∈ _
    rw [IdeleGroup.infinitePlaceIdele_finiteComponent]
    exact Subgroup.one_mem _

theorem negative_square (χ : Character m) (v : RayClass.RealPlace F) :
    localCharacter χ v (-1) ^ 2 = 1 := by
  rw [← map_pow]
  norm_num

theorem negative_cases (χ : Character m) (v : RayClass.RealPlace F) :
    localCharacter χ v (-1) = 1 ∨ localCharacter χ v (-1) = -1 :=
  sq_eq_one_iff.mp (negative_square χ v)

/-- The only other local value is the value of the character on minus one. -/
theorem of_not_positive (χ : Character m) (v : RayClass.RealPlace F)
    (x : v.1.Completionˣ) (hx : x ∉ RayClass.infinitePositiveSubgroup v.1) :
    localCharacter χ v x = localCharacter χ v (-1) := by
  let e := InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2
  have hx0 : e (x : v.1.Completion) ≠ 0 :=
    (map_ne_zero e).mpr (Units.ne_zero x)
  have hxneg : e (x : v.1.Completion) < 0 := by
    apply lt_of_le_of_ne
    · apply le_of_not_gt
      intro hp
      exact hx (fun _ ↦ hp)
    · exact hx0
  have hp : (-1 : v.1.Completionˣ) * x ∈ RayClass.infinitePositiveSubgroup v.1 := by
    intro _
    change 0 < e ((-1 : v.1.Completion) * (x : v.1.Completion))
    simpa only [map_mul, map_neg, map_one, neg_one_mul] using neg_pos.mpr hxneg
  have hh := positive χ v ((-1) * x) hp
  rw [map_mul] at hh
  have hs := negative_square χ v
  linear_combination localCharacter χ v (-1) * hh - localCharacter χ v x * hs

/-- The sign is nontrivial exactly at the real places in the actual conductor. -/
theorem conductor_iff_negative (χ : Character m) (v : RayClass.RealPlace F) :
    v ∈ (conductor χ).infinitePart ↔ localCharacter χ v (-1) = -1 := by
  rw [conductor_real_place]
  constructor
  · rintro ⟨x, hx⟩
    change localCharacter χ v x ≠ 1 at hx
    have hneg : localCharacter χ v (-1) ≠ 1 := by
      intro h
      by_cases hp : x ∈ RayClass.infinitePositiveSubgroup v.1
      · exact hx (positive χ v x hp)
      · exact hx ((of_not_positive χ v x hp).trans h)
    exact (negative_cases χ v).resolve_left hneg
  · intro h
    refine ⟨-1, ?_⟩
    change localCharacter χ v (-1) ≠ 1
    rw [h]
    norm_num

/-- The real parity is zero or one, using the actual infinite conductor. -/
def parity (χ : Character m) (v : RayClass.RealPlace F) : ℕ :=
  if v ∈ (conductor χ).infinitePart then 1 else 0

theorem parity_le_one (χ : Character m) (v : RayClass.RealPlace F) : parity χ v ≤ 1 := by
  unfold parity
  split_ifs <;> omega

theorem negative_eq_parity (χ : Character m) (v : RayClass.RealPlace F) :
    localCharacter χ v (-1) = (-1 : ℂ) ^ parity χ v := by
  by_cases hv : v ∈ (conductor χ).infinitePart
  · simpa [parity, hv] using (conductor_iff_negative χ v).mp hv
  · have hn : localCharacter χ v (-1) ≠ -1 :=
      fun h ↦ hv ((conductor_iff_negative χ v).mpr h)
    simpa [parity, hv] using (negative_cases χ v).resolve_right hn

end NormEuclidean.RayHeckeSigns
