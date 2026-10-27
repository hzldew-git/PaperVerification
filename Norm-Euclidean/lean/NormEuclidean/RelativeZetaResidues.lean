import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# The actual relative Dedekind zeta value at one

The quotient of the two actual Dedekind zeta functions has a right-hand
limit at one, equal to the ratio of their positive residues. The residues
are supplied by mathlib's proved analytic class number formula. This does
not identify that quotient with an independently defined Hecke L-series.
-/

noncomputable section

namespace NormEuclidean.RelativeZetaResidues

open NumberField NumberField.InfinitePlace Filter Topology
open scoped Real

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]

/-- A real arithmetic invariant defined by the actual residues, with no analytic input supplied. -/
def value : ℝ := dedekindZeta_residue E / dedekindZeta_residue F

/-- The relative residue value is strictly positive. -/
theorem value_pos : 0 < value F E :=
  div_pos (dedekindZeta_residue_pos E) (dedekindZeta_residue_pos F)

/-- The quotient of the actual Dedekind zeta functions tends to the relative residue value. -/
theorem tendsto_quotient :
    Tendsto (fun s : ℝ ↦ dedekindZeta E s / dedekindZeta F s)
      (𝓝[>] 1) (𝓝 ((value F E : ℝ) : ℂ)) := by
  have h := (tendsto_sub_one_mul_dedekindZeta_nhdsGT E).div
    (tendsto_sub_one_mul_dedekindZeta_nhdsGT F)
    (by exact_mod_cast dedekindZeta_residue_ne_zero F)
  have hlimit : ((dedekindZeta_residue E : ℂ) / dedekindZeta_residue F) =
      ((value F E : ℝ) : ℂ) := by simp [value]
  rw [hlimit] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : (s : ℂ) - 1 ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr (ne_of_gt hs) : s - 1 ≠ 0)
  exact mul_div_mul_left _ _ hs0

/-- No normalization factor is suppressed: both signatures, regulators, roots of unity,
class numbers and absolute discriminants occur explicitly. -/
theorem value_formula :
    value F E =
      ((2 ^ nrRealPlaces E * (2 * π) ^ nrComplexPlaces E * Units.regulator E *
          classNumber E) / (Units.torsionOrder E * Real.sqrt |(discr E : ℝ)|)) /
      ((2 ^ nrRealPlaces F * (2 * π) ^ nrComplexPlaces F * Units.regulator F *
          classNumber F) / (Units.torsionOrder F * Real.sqrt |(discr F : ℝ)|)) := rfl

end NormEuclidean.RelativeZetaResidues
