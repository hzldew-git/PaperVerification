import NormEuclidean.ProperSpinor
import Bong.QuadraticSpace.FieldDiagonalization
import Mathlib.LinearAlgebra.Projection

/-!
# Witt extension for regular subspaces

The actual extension is constructed from orthogonal decompositions and the
pinned field-generic Witt cancellation theorem. No local classification,
dyadic context, extension law, or supplied ambient transporter is assumed.
-/

noncomputable section

namespace NormEuclidean.WittExtension

open Bong.QuadraticSpace

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- The actual restricted regular space on a subspace. -/
def restrictedSpace (q : Bong.QuadraticSpace K V) (U : Submodule K V)
    (hU : (q.bilin.restrict U).Nondegenerate) : Bong.QuadraticSpace K U where
  bilin := q.bilin.restrict U
  isSymm := ⟨fun x y ↦ q.isSymm.eq x.1 y.1⟩
  nondegenerate := hU

omit [CharZero K] in
/-- The complementary space is regular when both the ambient space and
the subspace are regular. -/
theorem orthogonal_restrict_nondegenerate (q : Bong.QuadraticSpace K V)
    (U : Submodule K V) (hU : (q.bilin.restrict U).Nondegenerate) :
    (q.bilin.restrict (q.bilin.orthogonal U)).Nondegenerate := by
  have hcomp := q.bilin.isCompl_orthogonal_of_restrict_nondegenerate q.isSymm.isRefl hU
  apply q.bilin.nondegenerate_restrict_of_disjoint_orthogonal q.isSymm.isRefl
  rw [q.bilin.orthogonal_orthogonal q.nondegenerate q.isSymm.isRefl]
  exact hcomp.disjoint.symm

def complementarySpace (q : Bong.QuadraticSpace K V) (U : Submodule K V)
    (hU : (q.bilin.restrict U).Nondegenerate) :
    Bong.QuadraticSpace K (q.bilin.orthogonal U) :=
  restrictedSpace q _ (orthogonal_restrict_nondegenerate q U hU)

/-- Orthogonal decomposition as an actual isometry into the ambient space. -/
def decompositionIsometry (q : Bong.QuadraticSpace K V) (U : Submodule K V)
    (hU : (q.bilin.restrict U).Nondegenerate) :
    Isometry ((restrictedSpace q U hU).orthogonalSum (complementarySpace q U hU)) q where
  toLinearEquiv := Submodule.prodEquivOfIsCompl U (q.bilin.orthogonal U)
    (q.bilin.isCompl_orthogonal_of_restrict_nondegenerate q.isSymm.isRefl hU)
  map_bilin x y := by
    change q.bilin ((x.1 : V) + (x.2 : V)) ((y.1 : V) + (y.2 : V)) =
      q.bilin x.1 y.1 + q.bilin x.2 y.2
    have hxy : q.bilin x.1 y.2 = 0 := y.2.property x.1 x.1.property
    have hyx : q.bilin x.2 y.1 = 0 :=
      (q.isSymm.eq _ _).trans (x.2.property y.1 y.1.property)
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hxy, hyx,
      add_zero, zero_add]

omit [CharZero K] [FiniteDimensional K V] in
/-- A bilinear-form-preserving map on a regular subspace is injective. -/
theorem injective_of_preserves_bilin (q : Bong.QuadraticSpace K V) (U : Submodule K V)
    (hU : (q.bilin.restrict U).Nondegenerate) (f : U →ₗ[K] V)
    (hf : ∀ x y : U, q.bilin (f x) (f y) = q.bilin x y) : Function.Injective f := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm
  · intro x hx
    change f x = 0 at hx
    change x = 0
    apply hU.1 x
    intro y
    change q.bilin x y = 0
    rw [← hf, hx]
    simp
  · exact bot_le

omit [CharZero K] [FiniteDimensional K V] in
/-- The image of the regular subspace is itself regular. -/
theorem range_restrict_nondegenerate (q : Bong.QuadraticSpace K V) (U : Submodule K V)
    (hU : (q.bilin.restrict U).Nondegenerate) (f : U →ₗ[K] V)
    (hf : ∀ x y : U, q.bilin (f x) (f y) = q.bilin x y) :
    (q.bilin.restrict (LinearMap.range f)).Nondegenerate := by
  constructor
  · intro z hz
    obtain ⟨x, hx⟩ := z.property
    have hx0 : x = 0 := hU.1 x (fun y ↦ by
      change q.bilin x y = 0
      have h := hz (⟨f y, LinearMap.mem_range_self f y⟩ : LinearMap.range f)
      change q.bilin z.1 (f y) = 0 at h
      rw [← hx, hf] at h
      exact h)
    apply Subtype.ext
    change z.1 = 0
    rw [← hx, hx0, map_zero]
  · intro z hz
    obtain ⟨x, hx⟩ := z.property
    have hx0 : x = 0 := hU.2 x (fun y ↦ by
      change q.bilin y x = 0
      have h := hz (⟨f y, LinearMap.mem_range_self f y⟩ : LinearMap.range f)
      change q.bilin (f y) z.1 = 0 at h
      rw [← hx, hf] at h
      exact h)
    apply Subtype.ext
    change z.1 = 0
    rw [← hx, hx0, map_zero]

/-- Witt extension on a regular subspace, over any characteristic-zero
field. The ambient isometry is a conclusion and agrees with the given map. -/
theorem exists_bilinear_extension (q : Bong.QuadraticSpace K V) (U : Submodule K V)
    (hU : (q.bilin.restrict U).Nondegenerate) (f : U →ₗ[K] V)
    (hf : ∀ x y : U, q.bilin (f x) (f y) = q.bilin x y) :
    ∃ g : Isometry q q, ∀ x : U, g.toLinearEquiv x = f x := by
  let W := LinearMap.range f
  have hW : (q.bilin.restrict W).Nondegenerate := range_restrict_nondegenerate q U hU f hf
  let e : U ≃ₗ[K] W := LinearEquiv.ofBijective f.rangeRestrict
    ⟨(LinearMap.injective_rangeRestrict_iff f).mpr (injective_of_preserves_bilin q U hU f hf),
      f.surjective_rangeRestrict⟩
  let head : Isometry (restrictedSpace q U hU) (restrictedSpace q W hW) :=
    { toLinearEquiv := e
      map_bilin := hf }
  let dU := decompositionIsometry q U hU
  let dW := decompositionIsometry q W hW
  let tail := fieldOrthogonalSumCancel (restrictedSpace q U hU) (restrictedSpace q W hW)
    (complementarySpace q U hU) (complementarySpace q W hW) head (dU.trans dW.symm)
  let g := (dU.symm.trans (head.fieldOrthogonalSum tail)).trans dW
  have hUc := q.bilin.isCompl_orthogonal_of_restrict_nondegenerate q.isSymm.isRefl hU
  have hWc := q.bilin.isCompl_orthogonal_of_restrict_nondegenerate q.isSymm.isRefl hW
  refine ⟨g, ?_⟩
  intro x
  change (Submodule.prodEquivOfIsCompl W (q.bilin.orthogonal W) hWc)
    (e ((Submodule.prodEquivOfIsCompl U (q.bilin.orthogonal U) hUc).symm x).1,
      tail.toLinearEquiv ((Submodule.prodEquivOfIsCompl U
        (q.bilin.orthogonal U) hUc).symm x).2) = f x
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
  simp only [map_zero, Submodule.coe_prodEquivOfIsCompl', Submodule.coe_zero, add_zero]
  rfl

omit [CharZero K] [FiniteDimensional K V] in
/-- An isometric bilinear embedding of a regular source is injective. -/
theorem injective_bilinear_embedding {E : Type*} [AddCommGroup E] [Module K E]
    (p : Bong.QuadraticSpace K E) (q : Bong.QuadraticSpace K V) (i : E →ₗ[K] V)
    (hi : ∀ x y, q.bilin (i x) (i y) = p.bilin x y) : Function.Injective i := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro x hx
    change i x = 0 at hx
    change x = 0
    apply p.nondegenerate.1 x
    intro y
    rw [← hi, hx]
    simp
  · exact bot_le

omit [CharZero K] [FiniteDimensional K V] in
/-- A regular source gives a regular image under an actual bilinear embedding. -/
theorem range_nondegenerate_bilinear_embedding {E : Type*} [AddCommGroup E] [Module K E]
    (p : Bong.QuadraticSpace K E) (q : Bong.QuadraticSpace K V) (i : E →ₗ[K] V)
    (hi : ∀ x y, q.bilin (i x) (i y) = p.bilin x y) :
    (q.bilin.restrict (LinearMap.range i)).Nondegenerate := by
  constructor
  · intro z hz
    obtain ⟨x, hx⟩ := z.property
    have hx0 : x = 0 := p.nondegenerate.1 x (fun y ↦ by
      have h := hz (⟨i y, LinearMap.mem_range_self i y⟩ : LinearMap.range i)
      change q.bilin z.1 (i y) = 0 at h
      rw [← hx, hi] at h
      exact h)
    apply Subtype.ext
    change z.1 = 0
    rw [← hx, hx0, map_zero]
  · intro z hz
    obtain ⟨x, hx⟩ := z.property
    have hx0 : x = 0 := p.nondegenerate.2 x (fun y ↦ by
      have h := hz (⟨i y, LinearMap.mem_range_self i y⟩ : LinearMap.range i)
      change q.bilin (i y) z.1 = 0 at h
      rw [← hx, hi] at h
      exact h)
    apply Subtype.ext
    change z.1 = 0
    rw [← hx, hx0, map_zero]

/-- Extend between two embeddings of one regular source. The ambient
isometry identifies their images pointwise, even when the source has smaller rank. -/
theorem exists_extension_of_bilinear_embeddings {E : Type*} [AddCommGroup E] [Module K E]
    (p : Bong.QuadraticSpace K E) (q : Bong.QuadraticSpace K V) (i f : E →ₗ[K] V)
    (hi : ∀ x y, q.bilin (i x) (i y) = p.bilin x y)
    (hf : ∀ x y, q.bilin (f x) (f y) = p.bilin x y) :
    ∃ g : Isometry q q, ∀ x : E, g.toLinearEquiv (i x) = f x := by
  let U := LinearMap.range i
  have hU : (q.bilin.restrict U).Nondegenerate :=
    range_nondegenerate_bilinear_embedding p q i hi
  let e : E ≃ₗ[K] U := LinearEquiv.ofBijective i.rangeRestrict
    ⟨(LinearMap.injective_rangeRestrict_iff i).mpr (injective_bilinear_embedding p q i hi),
      i.surjective_rangeRestrict⟩
  let j := f.comp e.symm.toLinearMap
  have hj : ∀ x y : U, q.bilin (j x) (j y) = q.bilin x y := by
    intro x y
    have hx : i (e.symm x) = x.1 := congrArg Subtype.val (e.apply_symm_apply x)
    have hy : i (e.symm y) = y.1 := congrArg Subtype.val (e.apply_symm_apply y)
    change q.bilin (f (e.symm x)) (f (e.symm y)) = _
    rw [hf, ← hx, ← hy, hi]
  obtain ⟨g, hg⟩ := exists_bilinear_extension q U hU j hj
  refine ⟨g, ?_⟩
  intro x
  have h := hg (e x)
  change g.toLinearEquiv (i x) = f (e.symm (e x)) at h
  simpa only [LinearEquiv.symm_apply_apply] using h

omit [FiniteDimensional K V] in
/-- Quadratic isometries preserve the literal half-polar bilinear convention. -/
theorem quadratic_isometry_preserves_bilin {E : Type*} [AddCommGroup E] [Module K E]
    (P : QuadraticForm K E) (hP : P.polarBilin.Nondegenerate)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (f : P →qᵢ Q) (x y : E) :
    (SpinorBridge.quadraticSpace Q hQ).bilin (f x) (f y) =
      (SpinorBridge.quadraticSpace P hP).bilin x y := by
  simp only [SpinorBridge.quadraticSpace_bilin, QuadraticMap.polar]
  rw [← map_add f, f.map_app, f.map_app, f.map_app]

/-- Witt extension for actual quadratic isometries from a regular source,
expressed directly in the project's ambient orthogonal group. -/
theorem exists_extension_of_quadratic_isometries {E : Type*} [AddCommGroup E] [Module K E]
    (P : QuadraticForm K E) (hP : P.polarBilin.Nondegenerate)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) (i f : P →qᵢ Q) :
    ∃ g : ProperSpinor.ambientGroup Q, ∀ x : E, g.1 (i x) = f x := by
  obtain ⟨g, hg⟩ := exists_extension_of_bilinear_embeddings
    (SpinorBridge.quadraticSpace P hP) (SpinorBridge.quadraticSpace Q hQ)
    i.toLinearMap f.toLinearMap (quadratic_isometry_preserves_bilin P hP Q hQ i)
    (quadratic_isometry_preserves_bilin P hP Q hQ f)
  refine ⟨⟨g.toLinearEquiv, ?_⟩, hg⟩
  intro x
  simpa only [SpinorBridge.quadraticSpace_quadratic] using g.map_quadratic x

end NormEuclidean.WittExtension
