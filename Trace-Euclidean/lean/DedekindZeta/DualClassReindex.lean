import DedekindZeta.GlobalContinuation

/-!
# The class-group permutation induced by the trace-dual ideal

The theta transformation takes an integral ideal `𝔞` to the fractional ideal
`(𝔞 𝔡)⁻¹`. Its class is obtained from `[𝔞]` by multiplying by the different
class and then inverting. This file isolates the finite class-group reindexing
needed when the reflected partial-zeta identities are summed.
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace DedekindZeta.DualClassReindex

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

private theorem different_ne_zero : Theta.differentFractionalIdeal K ≠ 0 := by
  exact_mod_cast (FractionalIdeal.coeIdeal_ne_zero).mpr differentIdeal_ne_bot

/-- The ideal class of the different of `K`. -/
def differentClass : ClassGroup (𝓞 K) :=
  ClassGroup.mk K (Units.mk0 (Theta.differentFractionalIdeal K) (different_ne_zero K))

/-- Multiplication by the different class followed by inversion is a
permutation of the finite ideal class group. -/
def dualClassPermutation : ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) :=
  (Equiv.mulRight (differentClass K)).trans (Equiv.inv _)

private theorem dualIdeal_ne_zero (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) :
    Theta.dualIdeal K 𝔞 ≠ 0 := by
  unfold Theta.dualIdeal
  apply inv_ne_zero
  apply mul_ne_zero
  · exact_mod_cast (FractionalIdeal.coeIdeal_ne_zero).mpr hne
  · exact different_ne_zero K

/-- The trace-dual fractional ideal has the class prescribed by the
class-group permutation. -/
theorem class_dualIdeal (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) :
    ClassGroup.mk K (Units.mk0 (Theta.dualIdeal K 𝔞) (dualIdeal_ne_zero K 𝔞 hne)) =
      dualClassPermutation K
        (ClassGroup.mk0 ⟨𝔞, mem_nonZeroDivisors_iff_ne_zero.mpr hne⟩) := by
  let a : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
    Units.mk0 (𝔞 : FractionalIdeal (𝓞 K)⁰ K)
      (by exact_mod_cast (FractionalIdeal.coeIdeal_ne_zero).mpr hne)
  let d : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
    Units.mk0 (Theta.differentFractionalIdeal K) (different_ne_zero K)
  have hdual : Units.mk0 (Theta.dualIdeal K 𝔞) (dualIdeal_ne_zero K 𝔞 hne) =
      (a * d)⁻¹ := by
    apply Units.ext
    simp [a, d, Theta.dualIdeal]
  have ha : ClassGroup.mk K a =
      ClassGroup.mk0 ⟨𝔞, mem_nonZeroDivisors_iff_ne_zero.mpr hne⟩ := by
    rw [← ClassGroup.mk_mk0 (K := K)]
    congr 1
  change ClassGroup.mk K _ =
    (ClassGroup.mk0 ⟨𝔞, mem_nonZeroDivisors_iff_ne_zero.mpr hne⟩ *
      differentClass K)⁻¹
  rw [hdual, map_inv, map_mul, ha]
  rfl

/-- The dual of the chosen integral representative of `c` lies in the class
selected by `dualClassPermutation`. -/
theorem class_dualIdeal_idealClassRep (c : ClassGroup (𝓞 K)) :
    ClassGroup.mk K
      (Units.mk0 (Theta.dualIdeal K (idealClassRep K c))
        (dualIdeal_ne_zero K (idealClassRep K c) (by
          unfold idealClassRep
          exact mem_nonZeroDivisors_iff_ne_zero.mp
            (Function.surjInv ClassGroup.mk0_surjective c).2))) =
      dualClassPermutation K c := by
  have hne : idealClassRep K c ≠ 0 := by
    unfold idealClassRep
    exact mem_nonZeroDivisors_iff_ne_zero.mp
      (Function.surjInv ClassGroup.mk0_surjective c).2
  rw [class_dualIdeal K (idealClassRep K c) hne]
  congr 1
  exact Function.surjInv_eq ClassGroup.mk0_surjective c

/-- Reindex a finite class sum by trace duality. -/
theorem sum_dualClassPermutation (f : ClassGroup (𝓞 K) → ℂ) :
    (∑ c : ClassGroup (𝓞 K), f (dualClassPermutation K c)) =
      ∑ c : ClassGroup (𝓞 K), f c :=
  Equiv.sum_comp (dualClassPermutation K) f

end
end DedekindZeta.DualClassReindex
