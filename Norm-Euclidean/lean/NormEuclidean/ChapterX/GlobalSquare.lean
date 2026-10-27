/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import NormEuclidean.ChapterX.SquareClassTopology
import NormEuclidean.ChapterX.MixedScalarWeakApproximation
import NormEuclidean.ChapterX.QuadraticNormIndexExact

/-!
# O'Meara 65:15: the global square theorem

Mixed weak approximation makes an arbitrary idele a local norm modulo
a principal idele if the parameter is almost everywhere a square.
This contradicts the proved 65:14 lower bound for a nonsquare parameter.
The argument follows HeADC's `NumberFieldGlobalSquareIdele` in the actual
extension-norm model, with its former index premise discharged.
-/

noncomputable section

namespace NormEuclidean.GlobalSquare

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm MixedScalarWeakApproximation
open scoped NumberField Topology

universe u
variable {K : Type u} [Field K] [NumberField K]

omit [NumberField K] in
/-- Squareness of a unit is equivalent to squareness of its nonzero field value. -/
theorem unit_square_iff (a : Kˣ) : IsSquare a ↔ IsSquare a.val := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, rfl⟩
  · rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := by
      intro h
      exact a.ne_zero (by simpa [h] using hx)
    exact ⟨Units.mk0 x hx0, Units.ext hx⟩

/-- Evaluation of an idele at either kind of actual number-field place. -/
def component (q : Place K) : NumberFieldIdele K →* (FieldAt q)ˣ := match q with
  | .inl p => ideleFiniteComponent p
  | .inr v => ideleInfiniteComponent v

/-- Nonzero scalars embed into the units at a mixed place. -/
def scalarAt (q : Place K) : Kˣ →* (FieldAt q)ˣ :=
  Units.map (algebraMap K (FieldAt q)).toMonoidHom

/-- The mixed component of a principal idele is the embedded scalar. -/
theorem component_principal (q : Place K) (a : Kˣ) :
    component q (idelePrincipalEmbedding a) = scalarAt q a := by cases q <;> rfl

/-- Nontriviality of the actual finite-completion norm follows from its prime absolute value. -/
@[implicit_reducible]
def finiteNontrivial (v : HeightOneSpectrum (𝓞 K)) :
    NontriviallyNormedField (v.adicCompletion K) := by
  letI : Module.Finite ℤ (integerSubring K) :=
    inferInstanceAs (Module.Finite ℤ (NumberField.RingOfIntegers K))
  letI : Module.Free ℤ (integerSubring K) :=
    inferInstanceAs (Module.Free ℤ (NumberField.RingOfIntegers K))
  apply NontriviallyNormedField.ofNormNeOne
  obtain ⟨a, ha0, ha1⟩ := FiniteWeakApproximation.adicAbv_isNontrivial (integerSubring K) v
  refine ⟨NumberField.FinitePlace.embedding v a, ?_, ?_⟩
  · exact (map_ne_zero (NumberField.FinitePlace.embedding v)).mpr ha0
  · rwa [NumberField.FinitePlace.norm_embedding]

/-- A residual element after square-class approximation is a square unit. -/
theorem residual_square {F : Type*} [Field F] (a x c : Fˣ)
    (h : a.val = x.val * c.val ^ 2) : IsSquare (a⁻¹ * x) := by
  have he : a = x * c ^ 2 := Units.ext h
  refine ⟨c⁻¹, ?_⟩
  rw [he]
  simp [pow_two, mul_comm]

set_option backward.isDefEq.respectTransparency false in
/-- Almost-everywhere finite-place squareness forces a global square unit. -/
theorem unit_isSquare (theta : Kˣ)
    (hlocal : ∀ᶠ p : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      IsSquare (algebraMap K (p.adicCompletion K) theta.val)) : IsSquare theta := by
  classical
  by_contra htheta
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  let bad : Set (HeightOneSpectrum (𝓞 K)) :=
    {p | ¬ IsSquare (algebraMap K (p.adicCompletion K) theta.val)}
  have hbad : bad.Finite := Filter.eventually_cofinite.mp hlocal
  letI : Fintype bad := hbad.fintype
  let I := bad ⊕ NumberField.InfinitePlace K
  let p : I → Place K := Sum.map Subtype.val id
  have hp : Function.Injective p := Sum.map_injective.mpr
    ⟨Subtype.val_injective, Function.injective_id⟩
  let P := idelePrincipalEmbedding.range ⊔
    (extensionIdeleNorm (K := K) (E := QuadraticAlgebra K theta.val 0)).range
  have htop : P = ⊤ := by
    apply eq_top_iff.mpr
    intro i _
    let W (q : I) : Set (FieldAt (p q)) :=
      {z | ∃ c : (FieldAt (p q))ˣ, z = (component (p q) i).val * c.val ^ 2}
    let target (q : I) : FieldAt (p q) := (component (p q) i).val
    have hW (q : I) : W q ∈ 𝓝 (target q) := by
      cases q with
      | inl v =>
        dsimp only [W, target, p, Sum.map, FieldAt, component]
        letI := finiteNontrivial v.val
        exact (SquareClassTopology.isOpen_squareClass (ideleFiniteComponent v.val i)).mem_nhds
          ⟨1, by simp⟩
      | inr v =>
        dsimp only [W, target, p, Sum.map, FieldAt, component]
        letI := infiniteCompletionNontriviallyNormedField v
        letI : CharZero v.Completion := Algebra.charZero_of_charZero K _
        exact (SquareClassTopology.isOpen_squareClass (ideleInfiniteComponent v i)).mem_nhds
          ⟨1, by simp⟩
    have hn : {z : (q : I) → FieldAt (p q) | ∀ q, z q ∈ W q} ∈ 𝓝 target :=
      Filter.eventually_all.mpr (fun q ↦ (continuous_apply q).tendsto target |>.eventually (hW q))
    obtain ⟨a, ha⟩ := (denseRange_diagonal_of_injective p hp).mem_nhds hn
    let v : NumberField.InfinitePlace K := Classical.choice inferInstance
    have ha0 : a ≠ 0 := by
      obtain ⟨c, hc⟩ := ha (.inr v)
      change algebraMap K (FieldAt (p (.inr v))) a =
        (component (p (.inr v)) i).val * c.val ^ 2 at hc
      have hnz : algebraMap K (FieldAt (p (.inr v))) a ≠ 0 := by
        rw [hc]
        exact mul_ne_zero (component (p (.inr v)) i).ne_zero (pow_ne_zero 2 c.ne_zero)
      intro hz
      exact hnz (by rw [hz, map_zero])
    let aU := Units.mk0 a ha0
    let j := idelePrincipalEmbedding aU⁻¹ * i
    have hj : j ∈ (extensionIdeleNorm (K := K)
        (E := QuadraticAlgebra K theta.val 0)).range := by
      apply (NormFiberAssembly.mem_full_norm_range_iff theta htheta j).mpr
      have hs (q : I) : IsSquare (component (p q) j) := by
        obtain ⟨c, hc⟩ := ha q
        have hcomp : component (p q) j = (scalarAt (p q) aU)⁻¹ * component (p q) i := by
          rw [show j = idelePrincipalEmbedding aU⁻¹ * i from rfl, map_mul,
            component_principal, map_inv]
        rw [hcomp]
        exact residual_square _ _ c hc
      constructor
      · intro v
        by_cases hv : v ∈ bad
        · exact Bong.Dyadic.isQuadraticNorm_of_isSquare_right _ (hs (.inl ⟨v, hv⟩))
        · have ht : IsSquare (scalarAt (.inl v) theta) :=
            (unit_square_iff (scalarAt (.inl v) theta)).mpr (not_not.mp hv)
          exact Bong.Dyadic.isQuadraticNorm_of_isSquare_left _ ht
      · intro v
        exact Bong.Dyadic.isQuadraticNorm_of_isSquare_right _ (hs (.inr v))
    have hmul := P.mul_mem (Subgroup.mem_sup_left ⟨aU, rfl⟩) (Subgroup.mem_sup_right hj)
    simpa only [j, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul] using hmul
  have h := (QuadraticNormIndexExact.global_index_finite_lower_bound theta htheta).1
  change 2 ≤ P.index at h
  rw [htop, Subgroup.index_top] at h
  omega

/-- The global square theorem includes zero and has no unresolved arithmetic premise. -/
theorem isSquare (a : K)
    (hlocal : ∀ᶠ p : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      IsSquare (algebraMap K (p.adicCompletion K) a)) : IsSquare a := by
  by_cases ha : a = 0
  · simp [ha]
  · exact (unit_square_iff (Units.mk0 a ha)).mp (unit_isSquare _ hlocal)

/-- A nonsquare remains nonsquare at some finite place outside any finite set. -/
theorem exists_nonsquare_place (a : K) (ha : ¬ IsSquare a)
    (T : Set (HeightOneSpectrum (𝓞 K))) (hT : T.Finite) :
    ∃ p ∉ T, ¬ IsSquare (algebraMap K (p.adicCompletion K) a) := by
  by_contra h
  push Not at h
  apply ha
  apply isSquare a
  have he : ∀ᶠ p in Filter.cofinite, p ∉ T :=
    Filter.eventually_cofinite.mpr (by simpa using hT)
  filter_upwards [he] with p hp
  exact h p hp

end NormEuclidean.GlobalSquare
