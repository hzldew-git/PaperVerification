import NormEuclidean.QuadraticRootFields
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Square-root presentations of actual degree-two fields

A primitive element has a monic quadratic minimal polynomial. Completing
the square constructs a nonsquare base parameter and a square-root
generator. No quadratic presentation is assumed of the input extension.
-/

noncomputable section

namespace NormEuclidean.QuadraticFieldGenerators

open scoped IntermediateField

variable {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E]

/-- Every actual degree-two extension has a nonsquare square-root generator. -/
theorem exists_root_generator (hdim : Module.finrank K E = 2) :
    ∃ (eta : Kˣ), ¬ IsSquare eta ∧ ∃ s : E,
      s ^ 2 = algebraMap K E (eta : K) ∧ K⟮s⟯ = ⊤ := by
  letI : Module.Finite K E := Module.finite_of_finrank_pos (by omega)
  letI : CharZero E := Algebra.charZero_of_charZero K E
  obtain ⟨x, hx⟩ := Field.exists_primitive_element K E
  have hxint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hd : (minpoly K x).natDegree = 2 := by
    rw [← IntermediateField.adjoin.finrank hxint, hx, IntermediateField.finrank_top', hdim]
  let b := (minpoly K x).coeff 1
  let c := (minpoly K x).coeff 0
  have hc2 : (minpoly K x).coeff 2 = 1 := by
    simpa only [hd] using (minpoly.monic hxint).coeff_natDegree
  have heq : x ^ 2 + algebraMap K E b * x + algebraMap K E c = 0 := by
    have he := minpoly.aeval K x
    rw [Polynomial.aeval_eq_sum_range, hd] at he
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
      pow_one, hc2, Algebra.smul_def, mul_one, map_one, one_mul] at he
    change algebraMap K E c + algebraMap K E b * x + x ^ 2 = 0 at he
    linear_combination he
  let s := (2 : E) * x + algebraMap K E b
  let d := b ^ 2 - 4 * c
  have hs : s ^ 2 = algebraMap K E d := by
    dsimp only [s, d]
    rw [map_sub, map_pow, map_mul, map_ofNat]
    linear_combination 4 * heq
  have hgen : K⟮s⟯ = ⊤ := by
    apply top_unique
    rw [← hx]
    apply IntermediateField.adjoin_le_iff.mpr
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    change x ∈ K⟮s⟯
    have hm : (s - algebraMap K E b) / (2 : E) ∈ K⟮s⟯ :=
      (K⟮s⟯).div_mem
        ((K⟮s⟯).sub_mem (IntermediateField.mem_adjoin_simple_self K s)
          ((K⟮s⟯).algebraMap_mem b))
        (by simpa only [map_ofNat] using (K⟮s⟯).algebraMap_mem (2 : K))
    have he : (s - algebraMap K E b) / (2 : E) = x := by
      dsimp only [s]
      field_simp
      ring
    rwa [he] at hm
  have hn : s ∉ (⊥ : IntermediateField K E) := by
    intro hm
    have hb := IntermediateField.adjoin_simple_eq_bot_iff.mpr hm
    have hh : (⊤ : IntermediateField K E) = ⊥ := hgen.symm.trans hb
    have he := congrArg (fun P : IntermediateField K E ↦ Module.finrank K P) hh
    have he2 : (2 : ℕ) = 1 := by
      simpa only [IntermediateField.finrank_top', IntermediateField.finrank_bot, hdim] using he
    omega
  have hdn : ¬ IsSquare d := by
    rintro ⟨a, ha⟩
    have he : s ^ 2 = (algebraMap K E a) ^ 2 := by rw [hs, ha, map_mul, pow_two]
    apply hn
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
    · rw [h]
      exact (⊥ : IntermediateField K E).algebraMap_mem a
    · rw [h]
      exact (⊥ : IntermediateField K E).neg_mem
        ((⊥ : IntermediateField K E).algebraMap_mem a)
  have hd0 : d ≠ 0 := fun h ↦ hdn (h ▸ IsSquare.zero)
  refine ⟨Units.mk0 d hd0, ?_, s, hs, hgen⟩
  rintro ⟨a, ha⟩
  exact hdn ⟨(a : K), congrArg Units.val ha⟩

end NormEuclidean.QuadraticFieldGenerators
