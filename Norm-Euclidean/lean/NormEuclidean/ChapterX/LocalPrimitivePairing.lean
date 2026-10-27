import NormEuclidean.ChapterX.CompletionHensel
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Primitive pairing in a self-dual local lattice

This is the forward primitive-pairing argument of O'Meara 82:17. The
coefficient ring is a local subring with principal maximal ideal; no dyadic
context, quadratic value-set law, or integral inverse of two is assumed.
-/

noncomputable section

namespace NormEuclidean.LocalPrimitivePairing

open scoped Pointwise

variable {F E : Type*} [Field F] [AddCommGroup E] [Module F E]

/-- Self-duality expressed with literal integral pairings in the ambient field. -/
def SelfDual (S : Subring F) (B : LinearMap.BilinForm F E) (L : Submodule S E) : Prop :=
  ∀ x : E, x ∈ L ↔ ∀ y ∈ L, B x y ∈ S

/-- The pairing of two members of a self-dual lattice is an actual ring element. -/
def pairing {S : Subring F} {B : LinearMap.BilinForm F E} {L : Submodule S E}
    (hL : SelfDual S B L) (x y : L) : S := ⟨B x y, (hL x).mp x.property y y.property⟩

@[simp] theorem coe_pairing {S : Subring F} {B : LinearMap.BilinForm F E}
    {L : Submodule S E} (hL : SelfDual S B L) (x y : L) :
    (pairing hL x y : F) = B x y := rfl

/-- The literal integral pairing as a coefficient-ring bilinear form. -/
def pairingForm {S : Subring F} {B : LinearMap.BilinForm F E} {L : Submodule S E}
    (hL : SelfDual S B L) : LinearMap.BilinForm S L where
  toFun x :=
    { toFun := pairing hL x
      map_add' y z := by apply Subtype.ext; simp [pairing]
      map_smul' r y := by apply Subtype.ext; simp [pairing, Subring.smul_def] }
  map_add' x y := by apply LinearMap.ext; intro z; apply Subtype.ext; simp [pairing]
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    simp [pairing, Subring.smul_def]

@[simp] theorem pairingForm_apply {S : Subring F} {B : LinearMap.BilinForm F E}
    {L : Submodule S E} (hL : SelfDual S B L) (x y : L) :
    pairingForm hL x y = pairing hL x y := rfl

/-- Symmetry of the ambient form descends to the actual integral pairing. -/
theorem pairingForm_isSymm {S : Subring F} {B : LinearMap.BilinForm F E}
    (hB : B.IsSymm) {L : Submodule S E} (hL : SelfDual S B L) :
    (pairingForm hL).IsSymm := ⟨fun x y ↦ Subtype.ext (hB.eq x y)⟩

/-- A primitive vector has a unit pairing. If all pairings acquired a
uniformizer factor, the inverse-scaled vector would belong to the dual,
and self-duality would contradict primitivity. -/
theorem exists_unit_pairing (S : Subring F) [IsLocalRing S]
    (B : LinearMap.BilinForm F E) (L : Submodule S E) (hL : SelfDual S B L)
    (π : S) (hπ : (π : F) ≠ 0)
    (hmax : IsLocalRing.maximalIdeal S = Ideal.span {π})
    (x : L) (hx : (x : E) ∉ (π : F) • L) :
    ∃ y : L, IsUnit (pairing hL x y) := by
  classical
  by_contra! hnone
  have hinv : (π : F)⁻¹ • (x : E) ∈ L := by
    apply (hL _).mpr
    intro y hy
    have hpair : pairing hL x ⟨y, hy⟩ ∈ IsLocalRing.maximalIdeal S :=
      (IsLocalRing.mem_maximalIdeal _).mpr (hnone ⟨y, hy⟩)
    rw [hmax, Ideal.mem_span_singleton] at hpair
    obtain ⟨b, hb⟩ := hpair
    have hfield : B (x : E) y = (π : F) * (b : F) := congrArg Subtype.val hb
    rw [LinearMap.BilinForm.smul_left, hfield, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul]
    exact b.property
  apply hx
  exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
    ⟨(π : F)⁻¹ • (x : E), hinv, by simp only [smul_smul, mul_inv_cancel₀ hπ, one_smul]⟩

/-- Normalize the unit pairing to one by a coefficient-ring unit. -/
theorem exists_pairing_one (S : Subring F) [IsLocalRing S]
    (B : LinearMap.BilinForm F E) (L : Submodule S E) (hL : SelfDual S B L)
    (π : S) (hπ : (π : F) ≠ 0)
    (hmax : IsLocalRing.maximalIdeal S = Ideal.span {π})
    (x : L) (hx : (x : E) ∉ (π : F) • L) :
    ∃ y ∈ L, B (x : E) y = 1 := by
  obtain ⟨y, u, hu⟩ := exists_unit_pairing S B L hL π hπ hmax x hx
  refine ⟨(↑(u⁻¹) : S) • (y : E), L.smul_mem _ y.property, ?_⟩
  rw [← IsScalarTower.algebraMap_smul F (↑(u⁻¹) : S), LinearMap.BilinForm.smul_right]
  have huF : ((u : S) : F) = B (x : E) y := congrArg Subtype.val hu
  rw [← huF]
  exact congrArg (fun a : S ↦ (a : F)) u.inv_mul

end NormEuclidean.LocalPrimitivePairing
