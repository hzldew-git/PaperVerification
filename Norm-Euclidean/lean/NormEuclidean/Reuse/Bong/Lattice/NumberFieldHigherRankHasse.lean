/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import NormEuclidean.ChapterX.HasseMixedApproximation
import Bong.QuadraticSpace.BinaryImproperIsometry
import NormEuclidean.Reuse.Bong.Lattice.NumberFieldQuaternaryDiscriminantHasse

/-!
# The higher-rank induction in the Hasse isotropy theorem

This file formalizes the rank-at-least-five weak-approximation induction in
O'Meara 66:1 and joins it to the existing rank-two, rank-three, and rank-four
proofs.  The resulting all-ranks theorem is conditional on the exact arithmetic
inputs Global Square 65:15, quadratic Hasse Norm 65:23, and the cofinite
finite-place isotropy statement used from Example 63:14.
-/

namespace Bong.HeADCV5.Global.NumberFieldLattice

open scoped NumberField TensorProduct Topology Valued
open scoped Bong.HeADCV5.Global
open Bong

universe u

private theorem representsScaledLineOfValue'
    {F V : Type u} [Field F]
    [AddCommGroup V] [Module F V]
    (q : QuadraticSpace F V) (a : Fˣ) (x : V)
    (hx : q.quadratic x = (a : F)) :
    q.Represents (QuadraticSpace.scaledLine a) := by
  have hxne : x ≠ 0 := by
    intro hzero
    have : (a : F) = 0 := by
      rw [← hx, hzero]
      exact q.quadratic_zero
    exact Units.ne_zero a this
  refine ⟨{
    toLinearMap :=
      { toFun := fun c : F ↦ c • x
        map_add' := fun c d ↦ add_smul c d x
        map_smul' := fun c d ↦ by simp [mul_smul] }
    injective := ?_
    map_bilin := ?_ }⟩
  · intro c d hcd
    change c • x = d • x at hcd
    have hzero : (c - d) • x = 0 := by
      rw [sub_smul, hcd, sub_self]
    have : c - d = 0 := by
      simpa [hxne] using hzero
    exact sub_eq_zero.mp this
  · intro c d
    simp only [LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right,
      QuadraticSpace.scaledLine_bilin_apply]
    change d * (c * q.quadratic x) = (a : F) * c * d
    rw [hx]
    ring

/-- An isotropic regular quadratic space over a characteristic-zero field
represents every nonzero one-dimensional space. -/
theorem isotropicSpace_represents_scaledLine
    {F V : Type u} [Field F] [CharZero F]
    [AddCommGroup V] [Module F V]
    (q : QuadraticSpace F V) (a : Fˣ)
    (h : IsIsotropicSpace q) :
    q.Represents (QuadraticSpace.scaledLine a) := by
  rcases h with ⟨x, hx, hqx⟩
  have hHyp := QuadraticSpace.represents_hyperbolicPlane_one_of_isotropic
    q x hx hqx
  let y : Fin 2 → F := ![1, (a : F) / 2]
  have hy : (QuadraticSpace.hyperbolicPlane (1 : Fˣ)).quadratic y =
      (a : F) := by
    simp [y, QuadraticSpace.hyperbolicPlane_quadratic_apply]
    field_simp
  exact hHyp.trans
    (representsScaledLineOfValue'
      (QuadraticSpace.hyperbolicPlane (1 : Fˣ)) a y hy)

/-- If a binary head plus a nonzero tail is isotropic while the tail is
anisotropic, the two factors represent opposite nonzero values. -/
theorem exists_common_nonzero_value_of_sum_isotropic
    {F U W : Type u} [Field F] [CharZero F]
    [AddCommGroup U] [Module F U]
    [AddCommGroup W] [Module F W]
    (qU : QuadraticSpace F U) (qW : QuadraticSpace F W)
    (z0 : W) (hz0 : z0 ≠ 0)
    (hSum : IsIsotropicSpace (qU.orthogonalSum qW))
    (hTail : ¬ IsIsotropicSpace qW) :
    ∃ y : U, ∃ z : W,
      qU.quadratic y ≠ 0 ∧
        qU.quadratic y + qW.quadratic z = 0 := by
  by_cases hHead : IsIsotropicSpace qU
  · have hzValue : qW.quadratic z0 ≠ 0 := by
      intro hz
      exact hTail ⟨z0, hz0, hz⟩
    let a : Fˣ := Units.mk0 (-qW.quadratic z0) (neg_ne_zero.mpr hzValue)
    rcases isotropicSpace_represents_scaledLine qU a hHead with ⟨f⟩
    let y : U := f.toLinearMap 1
    have hy : qU.quadratic y = (a : F) := by
      change qU.quadratic (f.toLinearMap 1) = (a : F)
      rw [f.map_quadratic]
      simp [QuadraticSpace.scaledLine_quadratic_apply]
    refine ⟨y, z0, ?_, ?_⟩
    · rw [hy]
      exact Units.ne_zero a
    · rw [hy]
      change -qW.quadratic z0 + qW.quadratic z0 = 0
      exact neg_add_cancel _
  · rcases hSum with ⟨⟨y, z⟩, hyz, hzero⟩
    refine ⟨y, z, ?_, ?_⟩
    · intro hy
      have hz : qW.quadratic z = 0 := by
        simpa [QuadraticSpace.orthogonalSum_quadratic_apply, hy] using hzero
      by_cases hz0' : z = 0
      · apply hyz
        apply Prod.ext
        · by_contra hy0
          exact hHead ⟨y, hy0, hy⟩
        · exact hz0'
      · exact hTail ⟨z, hz0', hz⟩
    · simpa [QuadraticSpace.orthogonalSum_quadratic_apply] using hzero

/-- A finite diagonal quadratic polynomial is continuous over a topological
ring. -/
theorem continuous_diagonalQuadratic
    {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    {n : Nat} (a : Fin n → F) :
    Continuous (diagonalQuadratic a) := by
  unfold diagonalQuadratic
  fun_prop

end Bong.HeADCV5.Global.NumberFieldLattice


namespace Bong.HeADCV5.Global.NumberFieldLattice

open scoped NumberField TensorProduct Topology Valued
open scoped Bong.HeADCV5.Global
open Bong

universe u

/-- The inverse image under a diagonal polynomial of a fixed nonzero square
class. -/
def diagonalSquareClassNeighborhood
    {F : Type u} [Field F] {n : Nat}
    (a : Fin n → F) (A : Fˣ) : Set (Fin n → F) :=
  {x | ∃ c : Fˣ, diagonalQuadratic a x = (A : F) * (c : F) ^ 2}

/-- Nonzero square-class neighborhoods for diagonal values are open over a
complete nontrivially normed field of characteristic zero. -/
theorem isOpen_diagonalSquareClassNeighborhood
    {F : Type u} [NontriviallyNormedField F] [CompleteSpace F]
    [CharZero F] {n : Nat} (a : Fin n → F) (A : Fˣ) :
    IsOpen (diagonalSquareClassNeighborhood a A) := by
  change IsOpen ((diagonalQuadratic a) ⁻¹'
    {z : F | ∃ c : Fˣ, z = (A : F) * (c : F) ^ 2})
  exact (QuadraticSpace.hasOpenNonzeroSquareClasses_of_complete A).preimage
    (continuous_diagonalQuadratic a)

/-- A point whose diagonal value is the chosen representative lies in its
square-class neighborhood. -/
theorem mem_diagonalSquareClassNeighborhood_of_eq
    {F : Type u} [Field F] {n : Nat}
    (a : Fin n → F) (A : Fˣ) (x : Fin n → F)
    (hx : diagonalQuadratic a x = (A : F)) :
    x ∈ diagonalSquareClassNeighborhood a A := by
  refine ⟨1, ?_⟩
  simpa using hx

/-- Diagonal quadratic values commute with a field algebra map. -/
theorem map_diagonalQuadratic
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    {n : Nat} (a x : Fin n → F) :
    algebraMap F E (diagonalQuadratic a x) =
      diagonalQuadratic (fun i ↦ algebraMap F E (a i))
        (fun i ↦ algebraMap F E (x i)) := by
  simp [diagonalQuadratic, map_sum, map_mul, map_pow]

/-- The local input furnished by O'Meara, Example 63:14: every regular
quadratic space of rank at least three is isotropic at all but finitely many
finite places. -/
def HasCofiniteFinitePlaceIsotropy
    (K : Type u) [Field K] [NumberField K] : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (q : QuadraticSpace K V),
    3 ≤ Module.finrank K V →
      ∀ᶠ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        IsIsotropicSpace (q.scalarExtension (E := p.adicCompletion K))

end Bong.HeADCV5.Global.NumberFieldLattice

namespace Bong.HeADCV5.Global.NumberFieldLattice

open scoped TensorProduct
open Bong

universe u

/-- At a bad place for the tail, local isotropy of a binary-head sum gives
opposite nonzero diagonal values after identifying scalar extensions with
mapped coefficient models. -/
theorem finiteDiagonal_scalarExtension_exists_common_nonzero_value
    {K E : Type u} [Field K] [Field E] [CharZero K] [CharZero E]
    [Algebra K E] {m : Nat} (hm : 0 < m)
    (a : Fin 2 → K) (ha : ∀ i, a i ≠ 0)
    (b : Fin m → K) (hb : ∀ i, b i ≠ 0)
    (hSum : IsIsotropicSpace
      (((QuadraticSpace.finiteDiagonal a ha).orthogonalSum
        (QuadraticSpace.finiteDiagonal b hb)).scalarExtension (E := E)))
    (hTail : ¬ IsIsotropicSpace
      ((QuadraticSpace.finiteDiagonal b hb).scalarExtension (E := E))) :
    ∃ y : Fin 2 → E, ∃ z : Fin m → E,
      diagonalQuadratic (fun i ↦ algebraMap K E (a i)) y ≠ 0 ∧
        diagonalQuadratic (fun i ↦ algebraMap K E (a i)) y +
          diagonalQuadratic (fun i ↦ algebraMap K E (b i)) z = 0 := by
  let aE : Fin 2 → E := fun i ↦ algebraMap K E (a i)
  let bE : Fin m → E := fun i ↦ algebraMap K E (b i)
  have haE : ∀ i, aE i ≠ 0 := fun i ↦
    (map_ne_zero (algebraMap K E)).mpr (ha i)
  have hbE : ∀ i, bE i ≠ 0 := fun i ↦
    (map_ne_zero (algebraMap K E)).mpr (hb i)
  let qUE := QuadraticSpace.finiteDiagonal aE haE
  let qWE := QuadraticSpace.finiteDiagonal bE hbE
  have hSplit : IsIsotropicSpace
      (((QuadraticSpace.finiteDiagonal a ha).scalarExtension (E := E)).orthogonalSum
        ((QuadraticSpace.finiteDiagonal b hb).scalarExtension (E := E))) :=
    isIsotropicSpace_map
      (QuadraticSpace.scalarExtensionOrthogonalSumIsometry
        (E := E) (QuadraticSpace.finiteDiagonal a ha)
          (QuadraticSpace.finiteDiagonal b hb)) hSum
  have hMapped : IsIsotropicSpace (qUE.orthogonalSum qWE) :=
    isIsotropicSpace_map
      ((QuadraticSpace.scalarExtensionFiniteDiagonalIsometry
          (E := E) a ha).fieldOrthogonalSum
        (QuadraticSpace.scalarExtensionFiniteDiagonalIsometry
          (E := E) b hb)) hSplit
  have hTailMapped : ¬ IsIsotropicSpace qWE := by
    intro h
    exact hTail (isIsotropicSpace_map
      (QuadraticSpace.scalarExtensionFiniteDiagonalIsometry
        (E := E) b hb).symm h)
  let j0 : Fin m := ⟨0, hm⟩
  let z0 : Fin m → E := fun j ↦ if j = j0 then 1 else 0
  have hz0 : z0 ≠ 0 := by
    intro hz
    have := congrFun hz j0
    simp [z0] at this
  rcases exists_common_nonzero_value_of_sum_isotropic
      qUE qWE z0 hz0 hMapped hTailMapped with
    ⟨y, z, hy, hyz⟩
  refine ⟨y, z, ?_, ?_⟩
  · simpa only [qUE, QuadraticSpace.finiteDiagonal_quadratic_apply] using hy
  · simpa only [qUE, qWE, QuadraticSpace.finiteDiagonal_quadratic_apply] using hyz

end Bong.HeADCV5.Global.NumberFieldLattice

namespace Bong.HeADCV5.Global.NumberFieldLattice

open Bong

universe u

/-- Componentwise product of quadratic-space representations. -/
noncomputable def QuadraticSpace.Representation.fieldOrthogonalSum
    {F U W U' W' : Type u} [Field F]
    [AddCommGroup U] [Module F U]
    [AddCommGroup W] [Module F W]
    [AddCommGroup U'] [Module F U']
    [AddCommGroup W'] [Module F W']
    {qU : QuadraticSpace F U} {qW : QuadraticSpace F W}
    {rU : QuadraticSpace F U'} {rW : QuadraticSpace F W'}
    (f : QuadraticSpace.Representation qU rU)
    (g : QuadraticSpace.Representation qW rW) :
    QuadraticSpace.Representation (qU.orthogonalSum qW)
      (rU.orthogonalSum rW) where
  toLinearMap :=
    { toFun := fun z ↦ (f.toLinearMap z.1, g.toLinearMap z.2)
      map_add' := by intro z z'; ext <;> simp
      map_smul' := by intro c z; ext <;> simp }
  injective := by
    intro x y hxy
    apply Prod.ext
    · exact f.injective (congrArg Prod.fst hxy)
    · exact g.injective (congrArg Prod.snd hxy)
  map_bilin := by
    intro x y
    change rU.bilin (f.toLinearMap x.1) (f.toLinearMap y.1) +
        rW.bilin (g.toLinearMap x.2) (g.toLinearMap y.2) =
      qU.bilin x.1 y.1 + qW.bilin x.2 y.2
    rw [f.map_bilin, g.map_bilin]

/-- Isotropy passes from a represented space to its host. -/
theorem isIsotropicSpace_of_representation
    {F U V : Type u} [Field F]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    {q : QuadraticSpace F U} {r : QuadraticSpace F V}
    (f : QuadraticSpace.Representation q r)
    (h : IsIsotropicSpace q) : IsIsotropicSpace r := by
  rcases h with ⟨x, hx, hqx⟩
  refine ⟨f.toLinearMap x, ?_, ?_⟩
  · intro hzero
    apply hx
    apply f.injective
    simpa using hzero
  rw [f.map_quadratic, hqx]

/-- An isotropic right summand makes an orthogonal sum isotropic. -/
theorem isIsotropicSpace_orthogonalSum_right
    {F U W : Type u} [Field F]
    [AddCommGroup U] [Module F U]
    [AddCommGroup W] [Module F W]
    (qU : QuadraticSpace F U) {qW : QuadraticSpace F W}
    (h : IsIsotropicSpace qW) :
    IsIsotropicSpace (qU.orthogonalSum qW) := by
  rcases h with ⟨z, hz, hqz⟩
  refine ⟨(0, z), ?_, ?_⟩
  · intro hzero
    exact hz (congrArg Prod.snd hzero)
  · simp [QuadraticSpace.orthogonalSum_quadratic_apply, hqz]

end Bong.HeADCV5.Global.NumberFieldLattice

namespace Bong.HeADCV5.Global.NumberFieldLattice

open scoped TensorProduct
open Bong

universe u

/-- A square-class match between a global line coefficient and a local
value represented with opposite sign by the tail makes the local line-tail
sum isotropic. -/
theorem scalarExtension_line_tail_isotropic_of_squareRelation
    {K E : Type u} [Field K] [Field E] [CharZero K] [CharZero E]
    [Algebra K E] {m : Nat}
    (b : Fin m → K) (hb : ∀ i, b i ≠ 0)
    (rho : Kˣ) (rhoLocal c : Eˣ) (z : Fin m → E)
    (hRho : algebraMap K E (rho : K) =
      (rhoLocal : E) * (c : E) ^ 2)
    (hz : diagonalQuadratic (fun i ↦ algebraMap K E (b i)) z =
      -(rhoLocal : E)) :
    IsIsotropicSpace
      (((QuadraticSpace.scaledLine rho).orthogonalSum
        (QuadraticSpace.finiteDiagonal b hb)).scalarExtension (E := E)) := by
  let rhoE := Units.map (algebraMap K E).toMonoidHom rho
  let bE : Fin m → E := fun i ↦ algebraMap K E (b i)
  have hbE : ∀ i, bE i ≠ 0 := fun i ↦
    (map_ne_zero (algebraMap K E)).mpr (hb i)
  let qMapped :=
    (QuadraticSpace.scaledLine rhoE).orthogonalSum
      (QuadraticSpace.finiteDiagonal bE hbE)
  have hMapped : IsIsotropicSpace qMapped := by
    refine ⟨(1, (c : E) • z), ?_, ?_⟩
    · intro hzero
      have := congrArg Prod.fst hzero
      simp at this
    · simp only [qMapped, QuadraticSpace.orthogonalSum_quadratic_apply,
        QuadraticSpace.scaledLine_quadratic_apply,
        QuadraticSpace.finiteDiagonal_quadratic_apply]
      rw [show (rhoE : E) = algebraMap K E (rho : K) from rfl, hRho]
      rw [show diagonalQuadratic bE ((c : E) • z) =
          (c : E) ^ 2 * diagonalQuadratic bE z by
        unfold diagonalQuadratic
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Pi.smul_apply, smul_eq_mul]
        ring]
      rw [hz]
      ring
  let sumIso := QuadraticSpace.scalarExtensionOrthogonalSumIsometry
    (E := E) (QuadraticSpace.scaledLine rho)
      (QuadraticSpace.finiteDiagonal b hb)
  let mappedIso :=
    (QuadraticSpace.scalarExtensionScaledLineIsometry
      (E := E) rho).fieldOrthogonalSum
    (QuadraticSpace.scalarExtensionFiniteDiagonalIsometry
      (E := E) b hb)
  exact isIsotropicSpace_map (sumIso.trans mappedIso).symm hMapped

end Bong.HeADCV5.Global.NumberFieldLattice

namespace Bong.HeADCV5.Global.NumberFieldLattice

open scoped TensorProduct
open Bong

universe u

/-- Local isotropy of the tail alone gives local isotropy after adjoining
any line. -/
theorem scalarExtension_line_tail_isotropic_of_tail
    {K E : Type u} [Field K] [Field E] [CharZero K] [CharZero E]
    [Algebra K E] {W : Type u} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W]
    (qW : QuadraticSpace K W) (rho : Kˣ)
    (hTail : IsIsotropicSpace (qW.scalarExtension (E := E))) :
    IsIsotropicSpace
      (((QuadraticSpace.scaledLine rho).orthogonalSum qW).scalarExtension
        (E := E)) := by
  have hSplit : IsIsotropicSpace
      (((QuadraticSpace.scaledLine rho).scalarExtension (E := E)).orthogonalSum
        (qW.scalarExtension (E := E))) :=
    isIsotropicSpace_orthogonalSum_right _ hTail
  exact isIsotropicSpace_map
    (QuadraticSpace.scalarExtensionOrthogonalSumIsometry
      (E := E) (QuadraticSpace.scaledLine rho) qW).symm hSplit

end Bong.HeADCV5.Global.NumberFieldLattice

namespace Bong.HeADCV5.Global.NumberFieldLattice

open scoped NumberField TensorProduct Topology Valued
open scoped Bong.HeADCV5.Global
open Bong
open IsDedekindDomain

universe u

/-- The canonical norm on an infinite-place completion is nontrivial. -/
@[implicit_reducible]
noncomputable def infinitePlaceCompletionNontriviallyNormedField
    {K : Type u} [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) :
    NontriviallyNormedField w.Completion where
  toNormedField := inferInstance
  non_trivial := by
    refine ⟨algebraMap K w.Completion (2 : K), ?_⟩
    have hnorm : ‖algebraMap K w.Completion (2 : K)‖ = 2 := by
      rw [NumberField.InfinitePlace.Completion.algebraMap_apply]
      rw [NumberField.InfinitePlace.Completion.norm_coe]
      exact NumberField.InfinitePlace.map_natCast w 2
    rw [hnorm]
    norm_num

/-- Square-class neighborhoods in a mixed family of actual number-field
completions, defined by cases so each coordinate retains its canonical field
structure. -/
def mixedDiagonalSquareClassNeighborhood
    {K : Type u} [Field K] [NumberField K]
    {ι κ : Type u}
    (p : ι → HeightOneSpectrum (𝓞 K))
    (q : κ → NumberField.InfinitePlace K)
    (a : Fin 2 → K)
    (AF : ∀ i, ((p i).adicCompletion K)ˣ)
    (AI : ∀ j, ((q j).Completion)ˣ) :
    (s : ι ⊕ κ) → Set (Fin 2 → mixedCompletion p q s)
  | Sum.inl i =>
      show Set (Fin 2 → (p i).adicCompletion K) from
        diagonalSquareClassNeighborhood
          (fun j ↦ algebraMap K ((p i).adicCompletion K) (a j)) (AF i)
  | Sum.inr j =>
      show Set (Fin 2 → (q j).Completion) from
        diagonalSquareClassNeighborhood
          (fun k ↦ algebraMap K ((q j).Completion) (a k)) (AI j)

/-- Assemble binary local vectors in a mixed family of completions. -/
def mixedBinaryLocalVector
    {K : Type u} [Field K] [NumberField K]
    {ι κ : Type u}
    (p : ι → HeightOneSpectrum (𝓞 K))
    (q : κ → NumberField.InfinitePlace K)
    (yF : ∀ i, Fin 2 → (p i).adicCompletion K)
    (yI : ∀ j, Fin 2 → (q j).Completion) :
    (s : ι ⊕ κ) → Fin 2 → mixedCompletion p q s
  | Sum.inl i => yF i
  | Sum.inr j => yI j

set_option maxHeartbeats 1000000 in
-- Dependent mixed-completion elaboration exceeds the default heartbeat limit.
/-- The weak-approximation construction in the higher-dimensional step of
O'Meara 66:1.  A binary value is chosen globally so that adjoining its line
to the tail is isotropic at every finite and infinite place. -/
theorem exists_binary_value_with_everywhere_isotropic_tail
    {K : Type u} [Field K] [NumberField K]
    (hCofinite : HasCofiniteFinitePlaceIsotropy K)
    {m : Nat} (hm : 3 ≤ m)
    (a : Fin 2 → K) (ha : ∀ i, a i ≠ 0)
    (b : Fin m → K) (hb : ∀ i, b i ≠ 0)
    (hFinite : ∀ p : HeightOneSpectrum (𝓞 K),
      IsIsotropicSpace
        (((QuadraticSpace.finiteDiagonal a ha).orthogonalSum
          (QuadraticSpace.finiteDiagonal b hb)).scalarExtension
            (E := p.adicCompletion K)))
    (hInfinite : ∀ w : NumberField.InfinitePlace K,
      IsIsotropicSpace
        (((QuadraticSpace.finiteDiagonal a ha).orthogonalSum
          (QuadraticSpace.finiteDiagonal b hb)).scalarExtension
            (E := w.Completion))) :
    ∃ x : Fin 2 → K, ∃ hx : diagonalQuadratic a x ≠ 0,
      let rho := Units.mk0 (diagonalQuadratic a x) hx
      (∀ p : HeightOneSpectrum (𝓞 K),
        IsIsotropicSpace
          (((QuadraticSpace.scaledLine rho).orthogonalSum
            (QuadraticSpace.finiteDiagonal b hb)).scalarExtension
              (E := p.adicCompletion K))) ∧
      (∀ w : NumberField.InfinitePlace K,
        IsIsotropicSpace
          (((QuadraticSpace.scaledLine rho).orthogonalSum
            (QuadraticSpace.finiteDiagonal b hb)).scalarExtension
              (E := w.Completion))) := by
  classical
  let qW := QuadraticSpace.finiteDiagonal b hb
  have hEventually :
      ∀ᶠ p : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        IsIsotropicSpace (qW.scalarExtension (E := p.adicCompletion K)) :=
    hCofinite qW (by simpa only [Module.finrank_fin_fun] using hm)
  let badFiniteSet : Set (HeightOneSpectrum (𝓞 K)) :=
    {p | ¬ IsIsotropicSpace
      (qW.scalarExtension (E := p.adicCompletion K))}
  have hbadFiniteSet : badFiniteSet.Finite := by
    exact Filter.eventually_cofinite.mp (by
      simpa only [badFiniteSet, Set.mem_setOf_eq] using hEventually)
  let BadFinite := ↥badFiniteSet
  letI : Fintype BadFinite := hbadFiniteSet.fintype
  let finitePlace : BadFinite → HeightOneSpectrum (𝓞 K) := Subtype.val
  have hLocalFinite (i : BadFinite) :
      ∃ y : Fin 2 → (finitePlace i).adicCompletion K,
        ∃ z : Fin m → (finitePlace i).adicCompletion K,
          diagonalQuadratic
              (fun j ↦ algebraMap K ((finitePlace i).adicCompletion K) (a j)) y ≠ 0 ∧
            diagonalQuadratic
                (fun j ↦ algebraMap K ((finitePlace i).adicCompletion K) (a j)) y +
              diagonalQuadratic
                (fun j ↦ algebraMap K ((finitePlace i).adicCompletion K) (b j)) z = 0 := by
    exact finiteDiagonal_scalarExtension_exists_common_nonzero_value
      (K := K) (E := (finitePlace i).adicCompletion K)
      (lt_of_lt_of_le (by omega : 0 < 3) hm) a ha b hb
      (hFinite (finitePlace i)) i.property
  have hLocalInfinite (w : NumberField.InfinitePlace K) :
      ∃ y : Fin 2 → w.Completion, ∃ z : Fin m → w.Completion,
        diagonalQuadratic
            (fun j ↦ algebraMap K w.Completion (a j)) y ≠ 0 ∧
          (¬ IsIsotropicSpace (qW.scalarExtension (E := w.Completion)) →
            diagonalQuadratic
                (fun j ↦ algebraMap K w.Completion (a j)) y +
              diagonalQuadratic
                (fun j ↦ algebraMap K w.Completion (b j)) z = 0) := by
    letI : CharZero w.Completion :=
      Algebra.charZero_of_charZero K w.Completion
    by_cases hbad : ¬ IsIsotropicSpace
        (qW.scalarExtension (E := w.Completion))
    · rcases finiteDiagonal_scalarExtension_exists_common_nonzero_value
          (K := K) (E := w.Completion)
          (lt_of_lt_of_le (by omega : 0 < 3) hm) a ha b hb
          (hInfinite w) hbad with ⟨y, z, hy, hyz⟩
      exact ⟨y, z, hy, fun _ ↦ hyz⟩
    · let y0 : Fin 2 → w.Completion := fun j ↦ if j = 0 then 1 else 0
      refine ⟨y0, 0, ?_, fun h ↦ (hbad h).elim⟩
      have ha0 : algebraMap K w.Completion (a 0) ≠ 0 :=
        (map_ne_zero (algebraMap K w.Completion)).mpr (ha 0)
      simpa [diagonalQuadratic, y0] using ha0
  let yFinite (i : BadFinite) : Fin 2 → (finitePlace i).adicCompletion K :=
    (hLocalFinite i).choose
  let zFinite (i : BadFinite) : Fin m → (finitePlace i).adicCompletion K :=
    (hLocalFinite i).choose_spec.choose
  have hyFinite (i : BadFinite) :
      diagonalQuadratic
          (fun j ↦ algebraMap K ((finitePlace i).adicCompletion K) (a j))
          (yFinite i) ≠ 0 :=
    (hLocalFinite i).choose_spec.choose_spec.1
  have hyzFinite (i : BadFinite) :
      diagonalQuadratic
          (fun j ↦ algebraMap K ((finitePlace i).adicCompletion K) (a j))
          (yFinite i) +
        diagonalQuadratic
          (fun j ↦ algebraMap K ((finitePlace i).adicCompletion K) (b j))
          (zFinite i) = 0 :=
    (hLocalFinite i).choose_spec.choose_spec.2
  let rhoFinite (i : BadFinite) : ((finitePlace i).adicCompletion K)ˣ :=
    Units.mk0 _ (hyFinite i)
  let yInfinite (w : NumberField.InfinitePlace K) : Fin 2 → w.Completion :=
    (hLocalInfinite w).choose
  let zInfinite (w : NumberField.InfinitePlace K) : Fin m → w.Completion :=
    (hLocalInfinite w).choose_spec.choose
  have hyInfinite (w : NumberField.InfinitePlace K) :
      diagonalQuadratic
          (fun j ↦ algebraMap K w.Completion (a j)) (yInfinite w) ≠ 0 :=
    (hLocalInfinite w).choose_spec.choose_spec.1
  have hyzInfinite (w : NumberField.InfinitePlace K)
      (hbad : ¬ IsIsotropicSpace
        (qW.scalarExtension (E := w.Completion))) :
      diagonalQuadratic
          (fun j ↦ algebraMap K w.Completion (a j)) (yInfinite w) +
        diagonalQuadratic
          (fun j ↦ algebraMap K w.Completion (b j)) (zInfinite w) = 0 :=
    (hLocalInfinite w).choose_spec.choose_spec.2 hbad
  let rhoInfinite (w : NumberField.InfinitePlace K) : w.Completionˣ :=
    Units.mk0 _ (hyInfinite w)
  let U := mixedDiagonalSquareClassNeighborhood finitePlace
    (fun w : NumberField.InfinitePlace K ↦ w) a rhoFinite rhoInfinite
  have hOpen : ∀ s, IsOpen (U s) := by
    intro s
    cases s with
    | inl i =>
        change IsOpen (diagonalSquareClassNeighborhood
          (fun j ↦ algebraMap K ((finitePlace i).adicCompletion K) (a j))
          (rhoFinite i))
        exact isOpen_diagonalSquareClassNeighborhood
          (F := (finitePlace i).adicCompletion K)
          (fun j ↦ algebraMap K ((finitePlace i).adicCompletion K) (a j))
          (rhoFinite i)
    | inr w =>
        letI : NontriviallyNormedField w.Completion :=
          infinitePlaceCompletionNontriviallyNormedField w
        letI : CharZero w.Completion :=
          Algebra.charZero_of_charZero K w.Completion
        change IsOpen (diagonalSquareClassNeighborhood
          (fun j ↦ algebraMap K w.Completion (a j)) (rhoInfinite w))
        exact isOpen_diagonalSquareClassNeighborhood
          (F := w.Completion)
          (fun j ↦ algebraMap K w.Completion (a j)) (rhoInfinite w)
  let yLocal := mixedBinaryLocalVector finitePlace
    (fun w : NumberField.InfinitePlace K ↦ w) yFinite yInfinite
  have hyLocal : ∀ s, yLocal s ∈ U s := by
    intro s
    cases s with
    | inl i =>
        change yFinite i ∈ diagonalSquareClassNeighborhood
          (fun j ↦ algebraMap K ((finitePlace i).adicCompletion K) (a j))
          (rhoFinite i)
        exact mem_diagonalSquareClassNeighborhood_of_eq
          (F := (finitePlace i).adicCompletion K)
          _ _ _ rfl
    | inr w =>
        change yInfinite w ∈ diagonalSquareClassNeighborhood
          (fun j ↦ algebraMap K w.Completion (a j)) (rhoInfinite w)
        exact mem_diagonalSquareClassNeighborhood_of_eq
          (F := w.Completion) _ _ _ rfl
  obtain ⟨x, hxLocal⟩ := exists_global_coordinate_in_mixed_local_opens
    finitePlace (fun w : NumberField.InfinitePlace K ↦ w)
    Subtype.val_injective Function.injective_id 2 U hOpen yLocal hyLocal
  have hx : diagonalQuadratic a x ≠ 0 := by
    let w0 : NumberField.InfinitePlace K := Classical.choice inferInstance
    have hw := hxLocal (Sum.inr w0)
    change (fun j : Fin 2 ↦ algebraMap K w0.Completion (x j)) ∈
      diagonalSquareClassNeighborhood
        (fun j ↦ algebraMap K w0.Completion (a j)) (rhoInfinite w0) at hw
    rcases hw with ⟨c, hc⟩
    apply (map_ne_zero (algebraMap K w0.Completion)).mp
    rw [map_diagonalQuadratic]
    rw [hc]
    exact mul_ne_zero (Units.ne_zero (rhoInfinite w0))
      (pow_ne_zero 2 (Units.ne_zero c))
  refine ⟨x, hx, ?_, ?_⟩
  · intro p
    by_cases hTail : IsIsotropicSpace
        (qW.scalarExtension (E := p.adicCompletion K))
    · exact scalarExtension_line_tail_isotropic_of_tail qW
        (Units.mk0 (diagonalQuadratic a x) hx) hTail
    · let i : BadFinite := ⟨p, hTail⟩
      have hi := hxLocal (Sum.inl i)
      change (fun j : Fin 2 ↦ algebraMap K (p.adicCompletion K) (x j)) ∈
        diagonalSquareClassNeighborhood
          (fun j ↦ algebraMap K (p.adicCompletion K) (a j))
          (rhoFinite i) at hi
      rcases hi with ⟨c, hc⟩
      apply scalarExtension_line_tail_isotropic_of_squareRelation
        b hb (Units.mk0 (diagonalQuadratic a x) hx) (rhoFinite i) c
          (zFinite i)
      · change algebraMap K (p.adicCompletion K)
          (diagonalQuadratic a x) = _
        rw [map_diagonalQuadratic, hc]
      · exact eq_neg_of_add_eq_zero_right (hyzFinite i)
  · intro w
    letI : CharZero w.Completion :=
      Algebra.charZero_of_charZero K w.Completion
    by_cases hTail : IsIsotropicSpace
        (qW.scalarExtension (E := w.Completion))
    · exact scalarExtension_line_tail_isotropic_of_tail qW
        (Units.mk0 (diagonalQuadratic a x) hx) hTail
    · have hw := hxLocal (Sum.inr w)
      change (fun j : Fin 2 ↦ algebraMap K w.Completion (x j)) ∈
        diagonalSquareClassNeighborhood
          (fun j ↦ algebraMap K w.Completion (a j))
          (rhoInfinite w) at hw
      rcases hw with ⟨c, hc⟩
      apply scalarExtension_line_tail_isotropic_of_squareRelation
        b hb (Units.mk0 (diagonalQuadratic a x) hx) (rhoInfinite w) c
          (zInfinite w)
      · change algebraMap K w.Completion (diagonalQuadratic a x) = _
        rw [map_diagonalQuadratic, hc]
      · exact eq_neg_of_add_eq_zero_right (hyzInfinite w hTail)

end Bong.HeADCV5.Global.NumberFieldLattice


namespace Bong.HeADCV5.Global.NumberFieldLattice

open scoped NumberField TensorProduct
open Bong
open IsDedekindDomain

universe u

/-- The rank-at-least-five diagonal induction step in O'Meara 66:1. -/
theorem finiteDiagonal_two_add_hasse_isotropy_of_induction
    {K : Type u} [Field K] [NumberField K]
    (hCofinite : HasCofiniteFinitePlaceIsotropy K)
    {m : Nat} (hm : 3 ≤ m)
    (a : Fin 2 → K) (ha : ∀ i, a i ≠ 0)
    (b : Fin m → K) (hb : ∀ i, b i ≠ 0)
    (hInd : ∀ {V : Type u} [AddCommGroup V] [Module K V]
      [FiniteDimensional K V] (q : QuadraticSpace K V),
      Module.finrank K V < 2 + m →
      (∀ p : HeightOneSpectrum (𝓞 K),
        IsIsotropicSpace (q.scalarExtension (E := p.adicCompletion K))) →
      (∀ w : NumberField.InfinitePlace K,
        IsIsotropicSpace (q.scalarExtension (E := w.Completion))) →
      IsIsotropicSpace q)
    (hFinite : ∀ p : HeightOneSpectrum (𝓞 K),
      IsIsotropicSpace
        (((QuadraticSpace.finiteDiagonal a ha).orthogonalSum
          (QuadraticSpace.finiteDiagonal b hb)).scalarExtension
            (E := p.adicCompletion K)))
    (hInfinite : ∀ w : NumberField.InfinitePlace K,
      IsIsotropicSpace
        (((QuadraticSpace.finiteDiagonal a ha).orthogonalSum
          (QuadraticSpace.finiteDiagonal b hb)).scalarExtension
            (E := w.Completion))) :
    IsIsotropicSpace
      ((QuadraticSpace.finiteDiagonal a ha).orthogonalSum
        (QuadraticSpace.finiteDiagonal b hb)) := by
  obtain ⟨x, hx, hAugFinite, hAugInfinite⟩ :=
    exists_binary_value_with_everywhere_isotropic_tail
      hCofinite hm a ha b hb hFinite hInfinite
  let rho : Kˣ := Units.mk0 (diagonalQuadratic a x) hx
  let qW := QuadraticSpace.finiteDiagonal b hb
  let augmented := (QuadraticSpace.scaledLine rho).orthogonalSum qW
  have hRankAug : Module.finrank K (K × (Fin m → K)) < 2 + m := by
    simp only [Module.finrank_prod, Module.finrank_self,
      Module.finrank_fin_fun]
    omega
  have hAug : IsIsotropicSpace augmented :=
    hInd augmented hRankAug hAugFinite hAugInfinite
  rcases QuadraticSpace.fieldFiniteDiagonalRepresentsScaledLineOfValue
      a ha rho x rfl with ⟨f⟩
  let total := QuadraticSpace.Representation.fieldOrthogonalSum f
    (QuadraticSpace.Representation.refl qW)
  exact isIsotropicSpace_of_representation total hAug

end Bong.HeADCV5.Global.NumberFieldLattice

namespace Bong.HeADCV5.Global.NumberFieldLattice

open Bong

universe u

/-- The first two coefficients of a chosen diagonal presentation of a space
whose rank is `2 + m`. -/
noncomputable def fieldBinaryHeadCoefficients
    {F V : Type u} [Field F] [CharZero F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : QuadraticSpace F V) {m : Nat}
    (hRank : Module.finrank F V = 2 + m) : Fin 2 → F :=
  fun i ↦ q.fieldDiagonalCoefficients
    ((finCongr hRank).symm (Fin.castAdd m i))

/-- The remaining coefficients after the first two in the same diagonal
presentation. -/
noncomputable def fieldBinaryTailCoefficients
    {F V : Type u} [Field F] [CharZero F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : QuadraticSpace F V) {m : Nat}
    (hRank : Module.finrank F V = 2 + m) : Fin m → F :=
  fun i ↦ q.fieldDiagonalCoefficients
    ((finCongr hRank).symm (Fin.natAdd 2 i))

theorem fieldBinaryHeadCoefficients_ne_zero
    {F V : Type u} [Field F] [CharZero F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : QuadraticSpace F V) {m : Nat}
    (hRank : Module.finrank F V = 2 + m) :
    ∀ i, fieldBinaryHeadCoefficients q hRank i ≠ 0 :=
  fun i ↦ by
    change q.fieldDiagonalCoefficients
      ((finCongr hRank).symm (Fin.castAdd m i)) ≠ 0
    exact q.fieldDiagonalCoefficients_ne_zero _

theorem fieldBinaryTailCoefficients_ne_zero
    {F V : Type u} [Field F] [CharZero F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : QuadraticSpace F V) {m : Nat}
    (hRank : Module.finrank F V = 2 + m) :
    ∀ i, fieldBinaryTailCoefficients q hRank i ≠ 0 :=
  fun i ↦ by
    change q.fieldDiagonalCoefficients
      ((finCongr hRank).symm (Fin.natAdd 2 i)) ≠ 0
    exact q.fieldDiagonalCoefficients_ne_zero _

/-- An arbitrary regular space of rank `2 + m` is explicitly isometric to
the orthogonal sum of its chosen binary head and `m`-dimensional tail. -/
noncomputable def fieldBinaryTailSplitIsometry
    {F V : Type u} [Field F] [CharZero F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : QuadraticSpace F V) {m : Nat}
    (hRank : Module.finrank F V = 2 + m) :
    QuadraticSpace.Isometry q
      ((QuadraticSpace.finiteDiagonal
        (fieldBinaryHeadCoefficients q hRank)
        (fieldBinaryHeadCoefficients_ne_zero q hRank)).orthogonalSum
      (QuadraticSpace.finiteDiagonal
        (fieldBinaryTailCoefficients q hRank)
        (fieldBinaryTailCoefficients_ne_zero q hRank))) := by
  let e : Fin (2 + m) ≃ Fin (Module.finrank F V) :=
    (finCongr hRank).symm
  let c : Fin (2 + m) → F := fun i ↦ q.fieldDiagonalCoefficients (e i)
  have hc : ∀ i, c i ≠ 0 := fun i ↦
    q.fieldDiagonalCoefficients_ne_zero (e i)
  let a := fieldBinaryHeadCoefficients q hRank
  let b := fieldBinaryTailCoefficients q hRank
  have ha : ∀ i, a i ≠ 0 := fieldBinaryHeadCoefficients_ne_zero q hRank
  have hb : ∀ i, b i ≠ 0 := fieldBinaryTailCoefficients_ne_zero q hRank
  let reindex := QuadraticSpace.finiteDiagonalReindexIsometry
    q.fieldDiagonalCoefficients q.fieldDiagonalCoefficients_ne_zero e
  let split := QuadraticSpace.fieldFiniteDiagonalOrthogonalSumIsometry
    a b ha hb
  have hAppend : Fin.append a b = c := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp [a, b, c, e, fieldBinaryHeadCoefficients]
    · simp [a, b, c, e, fieldBinaryTailCoefficients]
  have split' : QuadraticSpace.Isometry
      ((QuadraticSpace.finiteDiagonal a ha).orthogonalSum
        (QuadraticSpace.finiteDiagonal b hb))
      (QuadraticSpace.finiteDiagonal c hc) := by
    simpa only [hAppend] using split
  exact q.fieldDiagonalizationIsometry.trans (reindex.trans split'.symm)

end Bong.HeADCV5.Global.NumberFieldLattice

namespace Bong.HeADCV5.Global.NumberFieldLattice

open scoped NumberField
open Bong
open IsDedekindDomain

universe u

/-- The arbitrary-space rank-at-least-five induction step in O'Meara 66:1,
conditional on the cited cofinite local-isotropy theorem. -/
theorem higherRank_hasse_isotropy_of_induction
    {K V : Type u} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hCofinite : HasCofiniteFinitePlaceIsotropy K)
    (q : QuadraticSpace K V) {m : Nat} (hm : 3 ≤ m)
    (hRank : Module.finrank K V = 2 + m)
    (hInd : ∀ {W : Type u} [AddCommGroup W] [Module K W]
      [FiniteDimensional K W] (r : QuadraticSpace K W),
      Module.finrank K W < 2 + m →
      (∀ p : HeightOneSpectrum (𝓞 K),
        IsIsotropicSpace (r.scalarExtension (E := p.adicCompletion K))) →
      (∀ w : NumberField.InfinitePlace K,
        IsIsotropicSpace (r.scalarExtension (E := w.Completion))) →
      IsIsotropicSpace r)
    (hFinite : ∀ p : HeightOneSpectrum (𝓞 K),
      IsIsotropicSpace (q.scalarExtension (E := p.adicCompletion K)))
    (hInfinite : ∀ w : NumberField.InfinitePlace K,
      IsIsotropicSpace (q.scalarExtension (E := w.Completion))) :
    IsIsotropicSpace q := by
  let a := fieldBinaryHeadCoefficients q hRank
  let b := fieldBinaryTailCoefficients q hRank
  have ha : ∀ i, a i ≠ 0 := fieldBinaryHeadCoefficients_ne_zero q hRank
  have hb : ∀ i, b i ≠ 0 := fieldBinaryTailCoefficients_ne_zero q hRank
  let split := fieldBinaryTailSplitIsometry q hRank
  have hFiniteSplit : ∀ p : HeightOneSpectrum (𝓞 K),
      IsIsotropicSpace
        (((QuadraticSpace.finiteDiagonal a ha).orthogonalSum
          (QuadraticSpace.finiteDiagonal b hb)).scalarExtension
            (E := p.adicCompletion K)) := by
    intro p
    exact isIsotropicSpace_map
      (split.scalarExtension (E := p.adicCompletion K)) (hFinite p)
  have hInfiniteSplit : ∀ w : NumberField.InfinitePlace K,
      IsIsotropicSpace
        (((QuadraticSpace.finiteDiagonal a ha).orthogonalSum
          (QuadraticSpace.finiteDiagonal b hb)).scalarExtension
            (E := w.Completion)) := by
    intro w
    exact isIsotropicSpace_map
      (split.scalarExtension (E := w.Completion)) (hInfinite w)
  have hSplit := finiteDiagonal_two_add_hasse_isotropy_of_induction
    hCofinite hm a ha b hb hInd hFiniteSplit hInfiniteSplit
  exact isIsotropicSpace_map split.symm hSplit

end Bong.HeADCV5.Global.NumberFieldLattice

namespace Bong.HeADCV5.Global.NumberFieldLattice

open scoped TensorProduct NumberField
open Bong
open IsDedekindDomain

universe u

/-- Scalar extension preserves finite dimension. -/
theorem finrank_scalarExtension_space
    {F E V : Type u} [Field F] [Field E] [Algebra F E]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] :
    Module.finrank E (E ⊗[F] V) = Module.finrank F V := by
  rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul]

/-- O'Meara 66:1 in all ranks, conditional precisely on Global Square
65:15, the universally quantified quadratic Hasse Norm theorem 65:23, and
the cofinite local-isotropy input of Example 63:14. -/
theorem hasAllPlaceHasseIsotropy_of_arithmeticInputs
    {K : Type u} [Field K] [NumberField K]
    (hSquare : HasCofiniteFinitePlaceGlobalSquare K)
    (hNorm : HasUniversalQuadraticHasseNorm.{u})
    (hCofinite : HasCofiniteFinitePlaceIsotropy K) :
    HasAllPlaceHasseIsotropy K := by
  let P : Nat → Prop := fun n ↦
    ∀ {V : Type u} [AddCommGroup V] [Module K V]
      [FiniteDimensional K V] (q : QuadraticSpace K V),
      Module.finrank K V = n →
      (∀ p : HeightOneSpectrum (𝓞 K),
        IsIsotropicSpace (q.scalarExtension (E := p.adicCompletion K))) →
      (∀ w : NumberField.InfinitePlace K,
        IsIsotropicSpace (q.scalarExtension (E := w.Completion))) →
      IsIsotropicSpace q
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro V _ _ _ q hRank hFinite hInfinite
        by_cases hn0 : n = 0
        · let w0 : NumberField.InfinitePlace K := Classical.choice inferInstance
          rcases hInfinite w0 with ⟨x, hx, _⟩
          have hLocalRank : Module.finrank w0.Completion
              (w0.Completion ⊗[K] V) = 0 := by
            rw [finrank_scalarExtension_space, hRank, hn0]
          letI : Subsingleton (w0.Completion ⊗[K] V) :=
            Module.finrank_zero_iff.mp hLocalRank
          exact (hx (Subsingleton.elim x 0)).elim
        · by_cases hn1 : n = 1
          · let w0 : NumberField.InfinitePlace K := Classical.choice inferInstance
            letI : CharZero w0.Completion :=
              Algebra.charZero_of_charZero K w0.Completion
            rcases hInfinite w0 with ⟨x, hx, hqx⟩
            have hLocalRank : Module.finrank w0.Completion
                (w0.Completion ⊗[K] V) = 1 := by
              rw [finrank_scalarExtension_space, hRank, hn1]
            exact ((QuadraticSpace.isAnisotropic_of_ne_zero_of_finrank_eq_one
              (q := q.scalarExtension (E := w0.Completion))
              hLocalRank hx) hqx).elim
          · by_cases hn2 : n = 2
            · exact rankTwo_hasse_isotropy_of_globalSquare
                hSquare q (hRank.trans hn2) hFinite
            · by_cases hn3 : n = 3
              · exact rankThree_hasse_isotropy_of_hasseNorm
                  (hNorm K) q (hRank.trans hn3) hFinite hInfinite
              · by_cases hn4 : n = 4
                · exact rankFour_hasse_isotropy_of_universal_hasseNorm
                    hNorm q (hRank.trans hn4) hFinite hInfinite
                · let m := n - 2
                  have hm : 3 ≤ m := by
                    dsimp [m]
                    omega
                  have hTwoAdd : 2 + m = n := by
                    dsimp [m]
                    omega
                  apply higherRank_hasse_isotropy_of_induction
                    hCofinite q hm (hRank.trans hTwoAdd.symm)
                  · intro W _ _ _ r hWRank hWFinite hWInfinite
                    apply ih (Module.finrank K W)
                    · omega
                    · rfl
                    · exact hWFinite
                    · exact hWInfinite
                  · exact hFinite
                  · exact hInfinite
  intro V _ _ _ q hFinite hInfinite
  exact hP (Module.finrank K V) q rfl hFinite hInfinite

end Bong.HeADCV5.Global.NumberFieldLattice
