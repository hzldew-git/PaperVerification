import NormEuclidean.ChapterX.HasseFormComparison
import NormEuclidean.ChapterX.CofiniteLocalIsotropy
import NormEuclidean.ChapterX.QuadraticHasseNorm
import NormEuclidean.Reuse.Bong.Lattice.NumberFieldHigherRankHasse

/-!
# Discharging the arithmetic inputs of O'Meara 66:1

Global Square 65:15, quadratic Hasse Norm 65:23 over every number field,
and cofinite finite-place isotropy 63:14 are the proved inputs of the
rank induction. No Hasse principle, class number, or approximation law
is supplied as a hypothesis to the resulting all-rank theorem.
-/

noncomputable section

namespace NormEuclidean.HasseArithmetic

open IsDedekindDomain
open Bong.HeADCV5.Global.NumberFieldLattice
open scoped NumberField TensorProduct

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- Negated anisotropy is the usual nonzero-vector isotropy condition. -/
theorem not_anisotropic_iff {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] (Q : QuadraticForm F V) :
    ¬ Q.Anisotropic ↔ ∃ x, x ≠ 0 ∧ Q x = 0 :=
  Q.not_anisotropic_iff_exists

/-- The Global Square input is the actual theorem already proved from idèle norms. -/
theorem globalSquare : HasCofiniteFinitePlaceGlobalSquare K :=
  fun a ha ↦ GlobalSquare.isSquare a ha

/-- The norm input is valid uniformly, including over discriminant extensions. -/
theorem universalQuadraticNorm : HasUniversalQuadraticHasseNorm.{u} := by
  intro E _ _ theta alpha htheta hf hi
  exact QuadraticHasseNorm.of_all_places theta alpha htheta hf hi

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The cofinite input uses the project's actual completed quadratic forms. -/
theorem cofiniteIsotropy : HasCofiniteFinitePlaceIsotropy K := by
  intro V _ _ _ q hdim
  letI : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  have h := CofiniteLocalIsotropy.eventually_isotropic
    (HasseFormComparison.form q) (HasseFormComparison.regular q) hdim
  exact h.mono fun p hp ↦
    (HasseFormComparison.scalarExtension_isotropic_iff (F := p.adicCompletion K) q).mpr hp

/-- O'Meara 66:1 in all ranks over a number field, with all arithmetic inputs proved. -/
theorem allPlaceIsotropy : HasAllPlaceHasseIsotropy K :=
  hasAllPlaceHasseIsotropy_of_arithmeticInputs globalSquare universalQuadraticNorm
    cofiniteIsotropy

end NormEuclidean.HasseArithmetic
