import NormEuclidean.ChapterX.SUnitNormArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Finite generation of the actual S-unit group

The valuation orders outside S map into a finite product of copies of the
integers. The kernel consists exactly of the ordinary integer-ring units.
Dirichlet's theorem and Noetherianity then prove finite generation. No
S-unit rank formula or norm-index value is assumed.
-/

noncomputable section

namespace NormEuclidean.SUnitFiniteness

open IsDedekindDomain SUnitNormArithmetic
open scoped NumberField WithZero

variable {K : Type*} [Field K] [NumberField K]

/-- The actual embedding of ordinary integer-ring units into field units. -/
def integerUnitEmbedding : (𝓞 K)ˣ →* Kˣ :=
  Units.map (algebraMap (𝓞 K) K).toMonoidHom

/-- A field unit is an ordinary integer-ring unit exactly when every finite
valuation is one. Both the element and its inverse are recovered as integers. -/
theorem mem_integerUnitEmbedding_range (x : Kˣ) :
    x ∈ (integerUnitEmbedding (K := K)).range ↔
      ∀ p : HeightOneSpectrum (𝓞 K), p.valuation K x.val = 1 := by
  constructor
  · rintro ⟨u, rfl⟩ p
    change p.valuation K (algebraMap (𝓞 K) K u.val) = 1
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (p.intValuation_eq_one_iff_mem_primeCompl _).mpr
      (p.asIdeal.notMem_of_isUnit u.isUnit)
  · intro h
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K x.val
      (fun p ↦ (h p).le)
    obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one
      (R := 𝓞 K) K (x⁻¹ : Kˣ).val (by
      intro p
      rw [Units.val_inv_eq_inv_val, map_inv₀, h p, inv_one])
    have hinj : Function.Injective (algebraMap (𝓞 K) K) :=
      FaithfulSMul.algebraMap_injective (𝓞 K) K
    have hab : a * b = 1 := by
      apply hinj
      rw [map_mul, map_one, ha, hb]
      simp
    have hba : b * a = 1 := by rwa [mul_comm]
    let u : (𝓞 K)ˣ := ⟨a, b, hab, hba⟩
    exact ⟨u, Units.ext ha⟩

/-- Ordinary units belong to every S-unit group. -/
def integerUnitsToS (S : Set (HeightOneSpectrum (𝓞 K))) : (𝓞 K)ˣ →* sUnitSubgroup S where
  toFun u := ⟨integerUnitEmbedding u,
    fun p _ ↦ (mem_integerUnitEmbedding_range _).mp ⟨u, rfl⟩ p⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x y)

/-- The additive finite-place orders outside S, as a homomorphism of Z-modules. -/
def orderLinear (S : Set (HeightOneSpectrum (𝓞 K))) :
    Additive (sUnitSubgroup S) →ₗ[ℤ] (↥(Sᶜ) → ℤ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x p ↦ -WithZero.log (p.1.valuation K x.toMul.val.val)
      map_zero' := by funext p; simp
      map_add' := by
        intro x y
        funext p
        change -WithZero.log (p.1.valuation K (x.toMul.val.val * y.toMul.val.val)) = _
        rw [map_mul, WithZero.log_mul
          ((Valuation.ne_zero_iff _).mpr x.toMul.val.ne_zero)
          ((Valuation.ne_zero_iff _).mpr y.toMul.val.ne_zero), neg_add]
        rfl }

/-- The valuation-order kernel is the image of the ordinary integer-ring units. -/
theorem orderLinear_ker (S : Set (HeightOneSpectrum (𝓞 K))) :
    (orderLinear S).ker =
      (MonoidHom.toAdditive (integerUnitsToS S)).toIntLinearMap.range := by
  ext x
  constructor
  · intro hx
    have hall (p : HeightOneSpectrum (𝓞 K)) : p.valuation K x.toMul.val.val = 1 := by
      by_cases hp : p ∈ S
      · exact x.toMul.property p hp
      · have hh := congrFun (show orderLinear S x = 0 from hx) ⟨p, hp⟩
        change -WithZero.log (p.valuation K x.toMul.val.val) = 0 at hh
        have he := WithZero.exp_log
          ((Valuation.ne_zero_iff (p.valuation K)).mpr x.toMul.val.ne_zero)
        rw [neg_eq_zero.mp hh, WithZero.exp_zero] at he
        exact he.symm
    obtain ⟨u, hu⟩ := (mem_integerUnitEmbedding_range x.toMul.val).mpr hall
    refine ⟨Additive.ofMul u, ?_⟩
    have he : integerUnitsToS S u = x.toMul := Subtype.ext hu
    exact congrArg Additive.ofMul he
  · rintro ⟨u, rfl⟩
    change orderLinear S _ = 0
    funext p
    have hu := (mem_integerUnitEmbedding_range (integerUnitEmbedding u.toMul)).mp
      ⟨u.toMul, rfl⟩ p.1
    change -WithZero.log (p.1.valuation K (integerUnitEmbedding u.toMul).val) = 0
    rw [hu, WithZero.log_one, neg_zero]

/-- The actual S-unit group is finitely generated whenever the excluded
finite-prime set is finite. This is the finite-generation input in 65:10. -/
theorem moduleFinite_sUnits (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite) :
    Module.Finite ℤ (Additive (sUnitSubgroup S)) := by
  letI : Finite ↥(Sᶜ) := hS.to_subtype
  letI : Fintype ↥(Sᶜ) := Fintype.ofFinite _
  let f := orderLinear S
  let l := (MonoidHom.toAdditive (integerUnitsToS S)).toIntLinearMap
  have hker : f.ker.FG := by
    rw [show f.ker = l.range from orderLinear_ker S, ← Submodule.map_top]
    exact Module.Finite.fg_top.map l
  apply Module.finite_def.mpr
  apply Submodule.fg_of_fg_map_of_fg_inf_ker f
  · exact IsNoetherian.noetherian _
  · simpa only [top_inf_eq] using hker

end NormEuclidean.SUnitFiniteness
