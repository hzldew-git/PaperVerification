import TraceEuclidean.V15HunterGeometry
import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
# Number-field covolume input for the cubic Hunter argument

Mathlib already computes the full Minkowski integer-ring lattice covolume.
This module specializes that formula to totally real fields and records the
strict bound supplied by the contradiction hypothesis `|D_K| < 49`.
The remaining geometric step is the quotient/projection formula dividing this
full covolume by `sqrt 3`.
-/

namespace TraceEuclidean

noncomputable section

open NumberField
open scoped NumberField

open scoped Classical in
/-- The full integer-ring lattice of a totally real field has covolume
`sqrt(|D_K|)` in the Minkowski Euclidean space. -/
theorem v15_totallyReal_integerLattice_covolume_eq_sqrt_discr
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K) :
    ZLattice.covolume (NumberField.mixedEmbedding.integerLattice K) =
      Real.sqrt |NumberField.discr K| := by
  letI : NumberField.IsTotallyReal K := hreal
  rw [NumberField.mixedEmbedding.covolume_integerLattice,
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero]
  norm_num

open scoped Classical in
/-- The same covolume formula in mathlib's Euclidean `L^2` model of the
Minkowski space.  This is the model in which the orthogonal projection used
by Hunter is defined. -/
theorem v15_totallyReal_euclidean_integerLattice_covolume_eq_sqrt_discr
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K) :
    ZLattice.covolume
        (NumberField.mixedEmbedding.euclidean.integerLattice K) =
      Real.sqrt |NumberField.discr K| := by
  rw [NumberField.mixedEmbedding.euclidean.integerLattice,
    ZLattice.covolume_comap
      (NumberField.mixedEmbedding.integerLattice K)
      MeasureTheory.volume MeasureTheory.volume
      (NumberField.mixedEmbedding.euclidean.volumePreserving_toMixed K)]
  exact v15_totallyReal_integerLattice_covolume_eq_sqrt_discr K hreal

open scoped Classical in
/-- Under the cubic contradiction hypothesis, the full integer-ring lattice
has covolume strictly below seven. -/
theorem v15_totallyReal_integerLattice_covolume_lt_seven
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdisc : |NumberField.discr K| < 49) :
    ZLattice.covolume (NumberField.mixedEmbedding.integerLattice K) < 7 := by
  rw [v15_totallyReal_integerLattice_covolume_eq_sqrt_discr K hreal]
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 7)]
  exact_mod_cast hdisc

open scoped Classical in
/-- The numerical projected-covolume bound follows as soon as the geometric
projection formula identifies the projected covolume with the full covolume
divided by `sqrt 3`. -/
theorem v15_totallyReal_integerLattice_covolume_div_sqrt_three_lt
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdisc : |NumberField.discr K| < 49) :
    ZLattice.covolume (NumberField.mixedEmbedding.integerLattice K) /
        Real.sqrt 3 < 7 / Real.sqrt 3 := by
  exact div_lt_div_of_pos_right
    (v15_totallyReal_integerLattice_covolume_lt_seven K hreal hdisc)
    (Real.sqrt_pos.2 (by norm_num))

end

end TraceEuclidean
