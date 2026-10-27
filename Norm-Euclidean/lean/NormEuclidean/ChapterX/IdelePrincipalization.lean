import NormEuclidean.ChapterX.IdeleComponents
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.GroupTheory.Index

/-!
# Actual idèle principalization on a fixed cofinite core

The finite idèlic class map and its proved kernel decomposition reduce 33:14a
to finiteness of the ordinary ideal class group. One finite set supports all
chosen class representatives. Multiplication by a principal idèle makes any
idèle a valuation unit outside that set, uniformly after every shrinking.
The assertion applies to the extension number field as well as the base field.
-/

noncomputable section

namespace NormEuclidean.ExtensionIdeleNorm

open IsDedekindDomain
open scoped NumberField WithZero

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- Projection of a full idèle onto its actual finite restricted product. -/
def finiteProjection : NumberFieldIdele K →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  Units.map (RingHom.snd (NumberField.InfiniteAdeleRing K)
    (FiniteAdeleRing (𝓞 K) K)).toMonoidHom

@[simp] theorem finiteProjection_principal (a : Kˣ) :
    finiteProjection (idelePrincipalEmbedding a) = FiniteAdeleRing.unitEmbedding (𝓞 K) K a :=
  Units.ext rfl

/-- The full and finite idèle evaluation maps agree. -/
theorem component_finiteProjection (p : HeightOneSpectrum (𝓞 K)) (i : NumberFieldIdele K) :
    FiniteIdele.componentUnit p (finiteProjection i) = ideleFiniteComponent p i :=
  Units.ext rfl

/-- O'Meara's `J_K^S`: finite components are valuation units on `S`; infinite
components are unrestricted. -/
def finitePlaceSIdeleSubgroup (S : Set (HeightOneSpectrum (𝓞 K))) :
    Subgroup (NumberFieldIdele K) where
  carrier := {i | ∀ p ∈ S,
    Valued.v ((ideleFiniteComponent p i : (p.adicCompletion K)ˣ) : p.adicCompletion K) = 1}
  one_mem' := by intro p _; simp
  mul_mem' := by
    intro i j hi hj p hp
    simp only [map_mul, Units.val_mul, hi p hp, hj p hp, one_mul]
  inv_mem' := by
    intro i hi p hp
    simp only [map_inv, Units.val_inv_eq_inv_val, map_inv₀, hi p hp, inv_one]

/-- Every class has a finite idèle representative, and a single finite set
contains the nonunit support of all these representatives. -/
theorem exists_finite_support_class_representatives :
    ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧
      ∀ c : ClassGroup (𝓞 K), ∃ r : (FiniteAdeleRing (𝓞 K) K)ˣ,
        FiniteIdele.classHom r = c ∧
          ∀ p ∉ T, FiniteIdele.order r p = 0 := by
  classical
  let rep : ClassGroup (𝓞 K) → (FiniteAdeleRing (𝓞 K) K)ˣ :=
    fun c ↦ (FiniteIdele.classHom_surjective c).choose
  let T : Set (HeightOneSpectrum (𝓞 K)) := ⋃ c, Function.support (FiniteIdele.order (rep c))
  refine ⟨T, Set.finite_iUnion (fun c ↦ FiniteIdele.finite_support_order (rep c)), ?_⟩
  intro c
  refine ⟨rep c, (FiniteIdele.classHom_surjective c).choose_spec, ?_⟩
  intro p hp
  by_contra h
  exact hp (Set.mem_iUnion.mpr ⟨c, h⟩)

/-- Multiplication by a diagonal unit kills every valuation outside one fixed finite support. -/
theorem exists_fixed_core_finite_principalization :
    ∃ S₀ : Set (HeightOneSpectrum (𝓞 K)), S₀ᶜ.Finite ∧
      ∀ f : (FiniteAdeleRing (𝓞 K) K)ˣ, ∃ a : Kˣ,
        ∀ p ∈ S₀, FiniteIdele.order (f * FiniteAdeleRing.unitEmbedding (𝓞 K) K a) p = 0 := by
  obtain ⟨T, hT, hrep⟩ := exists_finite_support_class_representatives (K := K)
  refine ⟨Tᶜ, by simpa using hT, ?_⟩
  intro f
  obtain ⟨r, hr, hsupp⟩ := hrep (FiniteIdele.classHom f)
  have hclass : FiniteIdele.classHom (f * r⁻¹) = 1 := by simp [hr]
  obtain ⟨k, u, h⟩ := FiniteIdele.exists_diagonal_mul_localUnit_of_classHom_eq_one _ hclass
  refine ⟨k⁻¹, ?_⟩
  intro p hp
  have hord := congrArg (fun f ↦ FiniteIdele.order f p) h
  have hu : FiniteIdele.order u.1 p = 0 := u.2 p
  simp only [FiniteIdele.order_mul, FiniteIdele.order_inv, hsupp p hp, hu] at hord
  simp only [map_inv, FiniteIdele.order_mul, FiniteIdele.order_inv]
  omega

/-- O'Meara 33:14a for the actual full idèle group, uniformly after every shrinking. -/
theorem exists_fixed_core_idele_principalization :
    ∃ S₀ : Set (HeightOneSpectrum (𝓞 K)), S₀ᶜ.Finite ∧
      ∀ S : Set (HeightOneSpectrum (𝓞 K)), S ⊆ S₀ →
        ∀ i : NumberFieldIdele K, ∃ a : Kˣ,
          i * idelePrincipalEmbedding a ∈ finitePlaceSIdeleSubgroup S := by
  obtain ⟨S₀, hfinite, hcore⟩ := exists_fixed_core_finite_principalization (K := K)
  refine ⟨S₀, hfinite, ?_⟩
  intro S hS i
  obtain ⟨a, ha⟩ := hcore (finiteProjection i)
  refine ⟨a, ?_⟩
  intro p hp
  have hzero := ha p (hS hp)
  rw [← finiteProjection_principal, ← map_mul] at hzero
  have hval := (FiniteIdele.order_eq_zero_iff _ p).mp hzero
  simpa only [← component_finiteProjection, FiniteIdele.componentUnit_val] using hval

/-- Principal idèles and `S`-idèles generate the full idèle group on a fixed cofinite core. -/
theorem exists_fixed_core_principal_Sidele_eq_top :
    ∃ S₀ : Set (HeightOneSpectrum (𝓞 K)), S₀ᶜ.Finite ∧
      ∀ S : Set (HeightOneSpectrum (𝓞 K)), S ⊆ S₀ →
        idelePrincipalEmbedding.range ⊔ finitePlaceSIdeleSubgroup S = ⊤ := by
  obtain ⟨S₀, hfinite, hcore⟩ := exists_fixed_core_idele_principalization (K := K)
  refine ⟨S₀, hfinite, ?_⟩
  intro S hS
  apply (Subgroup.eq_top_iff' _).mpr
  intro i
  obtain ⟨a, ha⟩ := hcore S hS i
  have hp : idelePrincipalEmbedding a⁻¹ ∈ idelePrincipalEmbedding.range := ⟨a⁻¹, rfl⟩
  have h := Subgroup.mul_mem_sup hp ha
  convert h using 1
  simp [map_inv, mul_assoc, mul_comm]

end NormEuclidean.ExtensionIdeleNorm
