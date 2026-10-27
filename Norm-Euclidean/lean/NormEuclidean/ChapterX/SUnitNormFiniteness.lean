import NormEuclidean.ChapterX.SUnitFiniteness
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Finiteness of the actual S-unit norm index

Base S-units embed into extension S-units, and their quadratic norms are
their squares. Finite generation therefore proves that the norm image has
finite index. The exact power of two in 65:10 still requires the rank and
S-unit Hilbert 90 calculation.
-/

noncomputable section

namespace NormEuclidean.SUnitNormFiniteness

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm SUnitNormArithmetic
open scoped NumberField WithZero

universe u
variable {K E : Type u} [Field K] [NumberField K]
  [Field E] [NumberField E] [Algebra K E]

/-- A base S-unit remains an S-unit above the same base primes. The proof
uses the actual valuation and ramification formula, without unramifiedness. -/
theorem base_embedding_mem (S : Set (HeightOneSpectrum (𝓞 K)))
    (x : Kˣ) (hx : x ∈ sUnitSubgroup S) :
    Units.map (algebraMap K E).toMonoidHom x ∈
      sUnitSubgroup (finitePlacesOverSet (E := E) S) := by
  intro w hw
  let p := w.under (𝓞 K)
  letI : w.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  have h := HeightOneSpectrum.valuation_liesOver E p w x.val
  change w.valuation E (algebraMap K E x.val) = 1
  exact h.symm.trans (by rw [hx p hw, one_pow])

omit [Field E] [NumberField E] [Algebra K E] in
/-- The actual determinant norm restricted to extension and base S-unit groups. -/
def normSUnits (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    sUnitSubgroup (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S) →*
      sUnitSubgroup S := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  exact
    { toFun := fun x ↦ ⟨PrincipalNormComponents.globalNormUnits (K := K) x.val,
        global_norm_mem theta htheta S x⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y ↦ Subtype.ext (map_mul _ x.val y.val) }

omit [Field E] [NumberField E] [Algebra K E] in
/-- Every square of a base S-unit is an actual norm of an extension S-unit. -/
theorem squares_le_norm_range (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (powMonoidHom (α := sUnitSubgroup S) 2).range ≤ (normSUnits theta htheta S).range := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  rintro _ ⟨x, rfl⟩
  let z : sUnitSubgroup (finitePlacesOverSet (E := QuadraticAlgebra K theta.val 0) S) :=
    ⟨Units.map (algebraMap K (QuadraticAlgebra K theta.val 0)).toMonoidHom x.val,
      base_embedding_mem S x.val x.property⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  apply Units.ext
  change Algebra.norm K (algebraMap K (QuadraticAlgebra K theta.val 0) x.val.val) = _
  rw [algebra_norm_eq_quadraticAlgebra_norm, QuadraticAlgebra.norm_algebraMap]
  rfl

omit [Field E] [NumberField E] [Algebra K E] in
/-- The actual S-unit norm image has finite index on every cofinite S.
No numerical norm index or S-unit Hilbert 90 statement is assumed. -/
theorem finiteIndex_normSUnits (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    (normSUnits theta htheta S).range.FiniteIndex := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  letI : Module.Finite ℤ (Additive (sUnitSubgroup S)) :=
    SUnitFiniteness.moduleFinite_sUnits S hS
  letI : AddGroup.FG (Additive (sUnitSubgroup S)) :=
    Module.Finite.iff_addGroup_fg.mp inferInstance
  letI : Group.FG (sUnitSubgroup S) := GroupFG.iff_add_fg.mpr inferInstance
  letI : (powMonoidHom (α := sUnitSubgroup S) 2).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg _ (by decide : 2 ≠ 0)
  exact Subgroup.finiteIndex_of_le (squares_le_norm_range theta htheta S)

end NormEuclidean.SUnitNormFiniteness
