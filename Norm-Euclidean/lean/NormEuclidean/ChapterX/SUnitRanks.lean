import NormEuclidean.ChapterX.SUnitFiniteness
import NormEuclidean.ChapterX.NormFiberAssembly
import NormEuclidean.ChapterX.LocalNormIndices
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient

/-!
# Ranks of the actual cofinite S-unit groups

The ideal class-group order kills the cokernel of the finite-place order
map. Its image therefore has full rank; its kernel is the ordinary unit
group. Dirichlet's theorem and rank-nullity give the S-unit rank formula.
-/

noncomputable section

namespace NormEuclidean.SUnitRanks

open IsDedekindDomain ExtensionIdeleNorm SUnitNormArithmetic SUnitFiniteness
open scoped NumberField WithZero

variable {K : Type*} [Field K] [NumberField K]

/-- A positive exponent killing the ordinary ideal class group. -/
def classExponent (K : Type*) [Field K] [NumberField K] : ℕ := Nat.card (ClassGroup (𝓞 K))

/-- The class-group exponent used below is nonzero. -/
theorem classExponent_ne_zero : classExponent K ≠ 0 := Nat.card_pos.ne'

/-- Every excluded-prime order vector becomes the order vector of an
actual S-unit after multiplication by the class-group order. -/
theorem exists_multiple_orders (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite)
    (t : ↥(Sᶜ) → ℤ) :
    ∃ x : Additive (sUnitSubgroup S),
      orderLinear S x = (classExponent K : ℤ) • t := by
  classical
  let n (p : HeightOneSpectrum (𝓞 K)) : ℤ := if h : p ∉ S then t ⟨p, h⟩ else 0
  let pi (p : HeightOneSpectrum (𝓞 K)) := (LocalNormIndices.exists_uniformizer p).choose
  have hpi p : Valued.v (pi p).val = WithZero.exp (-1 : ℤ) :=
    (LocalNormIndices.exists_uniformizer p).choose_spec
  let f (p : HeightOneSpectrum (𝓞 K)) := pi p ^ n p
  have hf : ∀ᶠ p in Filter.cofinite, Valued.v (f p).val = 1 := by
    filter_upwards [Filter.eventually_cofinite.mpr hS] with p hp
    change p ∈ S at hp
    simp [f, n, hp]
  let j := NormFiberAssembly.ofComponents f hf (fun _ ↦ 1)
  let i := finiteProjection j
  have hcomp p : FiniteIdele.componentUnit p i = f p :=
    (component_finiteProjection p j).trans
      (NormFiberAssembly.finiteComponent_ofComponents f hf _ p)
  have hord p : FiniteIdele.order i p = n p := by
    change -WithZero.log (Valued.v (FiniteIdele.componentUnit p i).val) = n p
    rw [hcomp, Units.val_zpow_eq_zpow_val, map_zpow₀, hpi, ← WithZero.exp_zsmul,
      WithZero.log_exp]
    simp only [Int.zsmul_eq_mul, mul_neg, mul_one, neg_neg]
  have hpow (m : ℕ) p : FiniteIdele.order (i ^ m) p = (m : ℤ) * n p := by
    induction m with
    | zero => simp
    | succ m hm => simp only [pow_succ, FiniteIdele.order_mul, hm, hord, Nat.cast_add,
        Nat.cast_one]; ring
  have hclass : FiniteIdele.classHom (i ^ classExponent K) = 1 := by
    rw [map_pow]
    exact pow_card_eq_one'
  obtain ⟨a, u, hau⟩ := FiniteIdele.exists_diagonal_mul_localUnit_of_classHom_eq_one _ hclass
  have hdiag p : FiniteIdele.order (FiniteAdeleRing.unitEmbedding (𝓞 K) K a) p =
      -WithZero.log (p.valuation K a.val) := by
    change -WithZero.log (Valued.v (algebraMap K (p.adicCompletion K) a.val)) = _
    exact congrArg (fun q ↦ -WithZero.log q)
      (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p a.val)
  have haorder p : -WithZero.log (p.valuation K a.val) =
      (classExponent K : ℤ) * n p := by
    have h := congrArg (fun q ↦ FiniteIdele.order q p) hau
    rw [FiniteIdele.order_mul, u.property p, add_zero, hdiag, hpow] at h
    exact h.symm
  have ha : a ∈ sUnitSubgroup S := by
    intro p hp
    have ho : FiniteIdele.order (FiniteAdeleRing.unitEmbedding (𝓞 K) K a) p = 0 := by
      rw [hdiag, haorder]
      simp [n, hp]
    have hv := (FiniteIdele.order_eq_zero_iff _ p).mp ho
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p a.val).symm.trans hv
  refine ⟨Additive.ofMul ⟨a, ha⟩, ?_⟩
  funext p
  change -WithZero.log (p.1.valuation K a.val) = (classExponent K : ℤ) * t p
  rw [haorder]
  dsimp only [n]
  rw [dif_pos (show p.val ∉ S from p.property)]

/-- The actual finite-place order image has full rank. -/
theorem finrank_order_range (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite) :
    Module.finrank ℤ (orderLinear S).range = Nat.card ↥(Sᶜ) := by
  classical
  letI : Fintype ↥(Sᶜ) := hS.fintype
  let g := (LinearMap.lsmul ℤ (↥(Sᶜ) → ℤ) (classExponent K : ℤ)).codRestrict
    (orderLinear S).range (fun t ↦ exists_multiple_orders S hS t)
  have hg : Function.Injective g := by
    intro x y h
    have h' := congrArg Subtype.val h
    funext p
    have heq := congrFun h' p
    change (classExponent K : ℤ) * x p = (classExponent K : ℤ) * y p at heq
    exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr classExponent_ne_zero) heq
  apply le_antisymm
  · simpa only [Module.finrank_fintype_fun_eq_card, Module.finrank_self, mul_one,
      Nat.card_eq_fintype_card] using (Submodule.finrank_le (orderLinear S).range)
  · simpa only [Module.finrank_fintype_fun_eq_card, Module.finrank_self, mul_one,
      Nat.card_eq_fintype_card] using g.finrank_le_finrank_of_injective hg

/-- The order kernel has the ordinary Dirichlet unit rank. -/
theorem finrank_order_kernel (S : Set (HeightOneSpectrum (𝓞 K))) :
    Module.finrank ℤ (orderLinear S).ker = NumberField.Units.rank K := by
  let f := (MonoidHom.toAdditive (integerUnitsToS S)).toIntLinearMap
  have hf : Function.Injective f := by
    intro a b h
    apply Additive.toMul.injective
    apply Units.ext
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    exact congrArg (fun x : sUnitSubgroup S ↦ x.val.val) h
  rw [orderLinear_ker]
  exact (LinearMap.finrank_range_of_inj hf).trans (NumberField.Units.finrank_eq K)

/-- Dirichlet's rank formula for the actual cofinite S-unit group. -/
theorem finrank_sUnits (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite) :
    Module.finrank ℤ (Additive (sUnitSubgroup S)) =
      Nat.card ↥(Sᶜ) + NumberField.Units.rank K := by
  letI := moduleFinite_sUnits S hS
  have h := (orderLinear S).ker.finrank_quotient_add_finrank
  have he := (orderLinear S).quotKerEquivRange.finrank_eq
  rw [he, finrank_order_range S hS, finrank_order_kernel S] at h
  exact h.symm

end NormEuclidean.SUnitRanks
