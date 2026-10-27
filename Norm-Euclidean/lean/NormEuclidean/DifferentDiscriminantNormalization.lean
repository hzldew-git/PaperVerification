import NormEuclidean.CMResidueComparison
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Actual trace duals and the discriminant normalization

The inverse different is identified with the actual trace dual, and the
absolute and relative different norms are compared with field discriminants.
The resulting square-root factors are connected with the previously proved
relative Dedekind zeta residue. These are arithmetic normalization theorems;
they do not assert a self-dual additive Haar measure or an adelic mass identity.
-/

noncomputable section

namespace NormEuclidean.DifferentDiscriminantNormalization

open NumberField
open scoped NumberField nonZeroDivisors Real

variable (F : Type*) [Field F] [NumberField F]

/-- The actual absolute inverse different in the original number field. -/
def codifferent : FractionalIdeal (𝓞 F)⁰ F :=
  (differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F)⁻¹

/-- The inverse different equals the actual dual under the rational trace form. -/
theorem codifferent_eq_traceDual :
    codifferent F = FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
  rw [codifferent, coeIdeal_differentIdeal ℤ ℚ F (𝓞 F), inv_inv]

/-- Membership is the literal integral trace-pairing condition, for every integral element. -/
theorem mem_codifferent (x : F) :
    x ∈ codifferent F ↔ ∀ a : 𝓞 F, Algebra.trace ℚ F (x * (a : F)) ∈
      (algebraMap ℤ ℚ).range := by
  rw [codifferent_eq_traceDual,
    FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0)]
  simp only [Algebra.traceForm_apply, FractionalIdeal.mem_one_iff]
  constructor
  · intro h a
    exact h a ⟨a, rfl⟩
  · rintro h a ⟨b, rfl⟩
    exact h b

/-- The original ring of integers is contained in its actual trace dual. -/
theorem integers_le_codifferent : (1 : FractionalIdeal (𝓞 F)⁰ F) ≤ codifferent F := by
  rw [codifferent_eq_traceDual]
  exact FractionalIdeal.one_le_dual_one ℤ ℚ

/-- The finite norm of the actual absolute different is the absolute field discriminant. -/
theorem absolute_norm :
    Ideal.absNorm (differentIdeal ℤ (𝓞 F)) = (discr F).natAbs :=
  NumberField.absNorm_differentIdeal F (𝓞 F)

/-- The real different norm is strictly positive. -/
theorem absolute_norm_pos : 0 < (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ) := by
  rw [absolute_norm]
  exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero F)

/-- The square root of the actual different norm retains precisely the discriminant factor. -/
theorem absolute_sqrt :
    Real.sqrt (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ) =
      Real.sqrt |(discr F : ℝ)| := by
  rw [absolute_norm]
  congr 1
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]

variable (E : Type*) [Field E] [NumberField E] [Algebra F E]

/-- The actual relative different norm gives the discriminant in the original extension. -/
theorem relative_norm :
    (discr E).natAbs = Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 E)) *
      (discr F).natAbs ^ Module.finrank F E :=
  NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E)

/-- The relative different norm is nonzero, without an added arithmetic input. -/
theorem relative_norm_pos : 0 < (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 E)) : ℝ) := by
  have h := relative_norm F E
  have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  have hn : Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 E)) ≠ 0 := by
    intro hz
    simp only [hz, zero_mul] at h
    exact hd h
  exact_mod_cast Nat.pos_of_ne_zero hn

/-- A quadratic extension has exactly the square of the base discriminant in the tower formula. -/
theorem quadratic_discriminant (hdegree : Module.finrank F E = 2) :
    |(discr E : ℝ)| = (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 E)) : ℝ) *
      |(discr F : ℝ)| ^ 2 := by
  have habs (z : ℤ) : (z.natAbs : ℝ) = |(z : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have h := congrArg (fun n : ℕ ↦ (n : ℝ)) (relative_norm F E)
  simpa only [Nat.cast_mul, Nat.cast_pow, hdegree, habs] using h

/-- The actual relative-different square root gives the full quadratic discriminant ratio. -/
theorem quadratic_sqrt (hdegree : Module.finrank F E = 2) :
    Real.sqrt |(discr E : ℝ)| =
      Real.sqrt (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 E)) : ℝ) * |(discr F : ℝ)| := by
  rw [quadratic_discriminant F E hdegree,
    Real.sqrt_mul (relative_norm_pos F E).le, Real.sqrt_sq_eq_abs, abs_abs]

/-- The square-root discriminant ratio appearing in the residue is explicit in the different. -/
theorem quadratic_sqrt_ratio (hdegree : Module.finrank F E = 2) :
    Real.sqrt |(discr F : ℝ)| / Real.sqrt |(discr E : ℝ)| =
      (Real.sqrt (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 E)) : ℝ) *
        Real.sqrt |(discr F : ℝ)|)⁻¹ := by
  have hd : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
  have hr : 0 < Real.sqrt (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 E)) : ℝ) :=
    Real.sqrt_pos_of_pos (relative_norm_pos F E)
  rw [quadratic_sqrt F E hdegree]
  have hs := Real.sq_sqrt hd.le
  have hp := Real.sqrt_pos_of_pos hd
  field_simp
  nlinarith

/-- The residue ratio times its actual different normalization leaves only signature and units. -/
theorem residue_normalized (hdegree : Module.finrank F E = 2) :
    RelativeZetaResidues.value F E *
        (Real.sqrt (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 E)) : ℝ) *
          Real.sqrt |(discr F : ℝ)|) =
      (2 ^ InfinitePlace.nrRealPlaces E * (2 * π) ^ InfinitePlace.nrComplexPlaces E *
          Units.regulator E * classNumber E * Units.torsionOrder F) /
        (2 ^ InfinitePlace.nrRealPlaces F * (2 * π) ^ InfinitePlace.nrComplexPlaces F *
          Units.regulator F * classNumber F * Units.torsionOrder E) := by
  have hdF : 0 < Real.sqrt |(discr F : ℝ)| :=
    Real.sqrt_pos_of_pos (abs_pos.mpr (by exact_mod_cast discr_ne_zero F))
  have hdE : 0 < Real.sqrt |(discr E : ℝ)| :=
    Real.sqrt_pos_of_pos (abs_pos.mpr (by exact_mod_cast discr_ne_zero E))
  have hdR := Real.sqrt_pos_of_pos (relative_norm_pos F E)
  have hregF := Units.regulator_pos F
  have htF : 0 < (Units.torsionOrder F : ℝ) := by exact_mod_cast Units.torsionOrder_pos F
  have htE : 0 < (Units.torsionOrder E : ℝ) := by exact_mod_cast Units.torsionOrder_pos E
  have hcF : 0 < (classNumber F : ℝ) := by exact_mod_cast classNumber_pos F
  have hpi : 0 < (2 * π : ℝ) := by positivity
  rw [RelativeZetaResidues.value_formula, quadratic_sqrt F E hdegree]
  have hs := Real.sq_sqrt (abs_nonneg (discr F : ℝ))
  field_simp
  simp [hs, (Real.sqrt_pos.mp hdF).ne']

end NormEuclidean.DifferentDiscriminantNormalization
