import NormEuclidean.ChapterX.DiscreteSquareIndex
import NormEuclidean.ChapterX.QuadraticSquareDescent
import NormEuclidean.Reuse.Bong.Dyadic.UnitSquareClassCount

/-!
# Local square indices: valuation parity and unit squares

The full finite-completion square quotient splits into valuation parity
and the unit square quotient. The odd unit quotient has two elements;
the dyadic unit quotient uses the proved principal-unit filtration count.
-/

noncomputable section

namespace NormEuclidean.LocalSquareIndex

open IsDedekindDomain ExtensionIdeleNorm
open scoped NumberField WithZero

/-- Additive doubles and multiplicative squares are the same subgroup under type tags. -/
theorem doubles_eq_square (G : Type*) [CommGroup G] :
    SquareIndex.doubles (Additive G) = (Subgroup.square G).toAddSubgroup := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    rw [nsmulAddMonoidHom_apply, two_nsmul] at hy
    exact ⟨y.toMul, (congrArg Additive.toMul hy).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨Additive.ofMul y, ?_⟩
    rw [nsmulAddMonoidHom_apply, two_nsmul]
    exact (congrArg Additive.ofMul hy).symm

/-- The two versions of the square index agree. -/
theorem doubles_index_eq_square (G : Type*) [CommGroup G] :
    (SquareIndex.doubles (Additive G)).index = (Subgroup.square G).index := by
  rw [doubles_eq_square, Subgroup.index_toAddSubgroup]

variable {K : Type*} [Field K] [NumberField K]

/-- The actual integer-valued multiplicative order, with additive notation on field units. -/
def order (p : HeightOneSpectrum (𝓞 K)) : Additive ((p.adicCompletion K)ˣ) →+ ℤ where
  toFun x := WithZero.log (Valued.v x.toMul.val)
  map_zero' := by simp
  map_add' x y := by
    change WithZero.log (Valued.v (x.toMul.val * y.toMul.val)) = _
    rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.toMul.ne_zero)
      ((Valuation.ne_zero_iff _).mpr y.toMul.ne_zero)]

/-- Uniformizer powers attain every integer order. -/
theorem order_surjective (p : HeightOneSpectrum (𝓞 K)) : Function.Surjective (order p) := by
  obtain ⟨pi, hpi⟩ := LocalNormIndices.exists_uniformizer p
  intro n
  refine ⟨Additive.ofMul (pi ^ (-n)), ?_⟩
  change WithZero.log (Valued.v (pi ^ (-n)).val) = n
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hpi, ← WithZero.exp_zsmul, WithZero.log_exp]
  simp [Int.zsmul_eq_mul]

/-- The unit subgroup of the actual completed field. -/
def units (p : HeightOneSpectrum (𝓞 K)) : Subgroup ((p.adicCompletion K)ˣ) where
  carrier := {a | Valued.v a.val = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change Valued.v a.val = 1 at ha
    change Valued.v b.val = 1 at hb
    change Valued.v (a * b).val = 1
    rw [Units.val_mul, map_mul, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    change Valued.v a.val = 1 at ha
    change Valued.v a⁻¹.val = 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, ha, inv_one]

/-- The order kernel is precisely the group of local units. -/
def kernelEquiv (p : HeightOneSpectrum (𝓞 K)) : (order p).ker ≃+ Additive (units p) where
  toFun x := Additive.ofMul ⟨x.val.toMul, by
    have h : WithZero.log (Valued.v x.val.toMul.val) = 0 := x.property
    have hn : Valued.v x.val.toMul.val ≠ (0 : ℤᵐ⁰) :=
      (Valuation.ne_zero_iff _).mpr x.val.toMul.ne_zero
    have he := WithZero.exp_log hn
    rw [h, WithZero.exp_zero] at he
    exact he.symm⟩
  invFun x := ⟨Additive.ofMul x.toMul.val, by
    change WithZero.log (Valued.v x.toMul.val.val) = 0
    rw [x.toMul.property, WithZero.log_one]⟩
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl
  map_add' := fun _ _ ↦ rfl

/-- Splitting valuation parity gives the full square index in terms of local unit squares. -/
theorem index_eq_two_mul_units (p : HeightOneSpectrum (𝓞 K)) :
    (Subgroup.square ((p.adicCompletion K)ˣ)).index = 2 * (Subgroup.square (units p)).index := by
  rw [← doubles_index_eq_square, DiscreteSquareIndex.doubles_index _ _ (order_surjective p),
    SquareIndex.doubles_index_congr (kernelEquiv p), doubles_index_eq_square]

/-- A square root of a local unit is again a local unit. -/
theorem unit_square_iff (p : HeightOneSpectrum (𝓞 K)) (a : units p) :
    IsSquare a ↔ IsSquare a.val := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, rfl⟩
  · rintro ⟨r, hr⟩
    have hu : r ∈ units p := by
      change Valued.v r.val = 1
      have h : Valued.v a.val.val = 1 := a.property
      rw [show a.val.val = r.val * r.val from congrArg Units.val hr, map_mul] at h
      apply (pow_eq_one_iff_of_nonneg bot_le (by decide : 2 ≠ 0)).mp
      simpa only [pow_two] using h
    exact ⟨⟨r, hu⟩, Subtype.ext hr⟩

/-- There are exactly two local unit square classes at an odd finite prime. -/
theorem odd_unit_index (p : HeightOneSpectrum (𝓞 K)) (hp : (2 : 𝓞 K) ∉ p.asIdeal) :
    (Subgroup.square (units p)).index = 2 := by
  obtain ⟨d, hd, hns, hclass⟩ := OddRamifiedNormIndices.exists_unit_class p hp
  let D : units p := ⟨d, hd⟩
  apply Subgroup.index_eq_two_iff_exists_notMem_and.mpr
  refine ⟨D, fun h ↦ hns ((unit_square_iff p D).mp h), ?_⟩
  intro a
  rcases hclass a.val a.property with h | h
  · exact Or.inr ((unit_square_iff p a).mpr h)
  · exact Or.inl ((unit_square_iff p (a * D)).mpr h)

/-- Every odd finite completion has four field square classes. -/
theorem odd_index (p : HeightOneSpectrum (𝓞 K)) (hp : (2 : 𝓞 K) ∉ p.asIdeal) :
    (Subgroup.square ((p.adicCompletion K)ˣ)).index = 4 := by
  rw [index_eq_two_mul_units, odd_unit_index p hp]

end NormEuclidean.LocalSquareIndex
