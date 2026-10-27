import NormEuclidean.ChapterX.LocalPrimitivePairing
import NormEuclidean.ChapterX.ComplementIntersection
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Integral orthogonal splitting at a unit-norm vector

The orthogonal component of every integral vector is integral, and the
literal local intersection is self-dual. These statements use the original
ambient pairing and require no dyadic local-field structure.
-/

noncomputable section

namespace NormEuclidean.LocalOrthogonalSplitting

open LocalPrimitivePairing
open scoped Pointwise

variable {F E : Type*} [Field F] [AddCommGroup E] [Module F E]

/-- The projection coefficient belongs to the actual coefficient ring when
the norm of the splitting vector is a ring unit. -/
theorem projection_coefficient_integral (S : Subring F) (B : LinearMap.BilinForm F E)
    (L : Submodule S E) (hL : SelfDual S B L) (e : L) (u : Sˣ)
    (hu : B (e : E) e = ((u : S) : F)) (y : L) : B (e : E) y / B e e ∈ S := by
  have hinv : ((↑(u⁻¹) : S) : F) = (((u : S) : F))⁻¹ := by
    exact (map_units_inv S.subtype u)
  have h := S.mul_mem ((hL e).mp e.property y y.property) (↑(u⁻¹) : S).property
  simpa only [div_eq_mul_inv, hu, hinv] using h

/-- The literal intersection with the orthogonal complement of a unit-norm
line is self-dual for the restricted ambient form. -/
theorem selfDual_orthogonal_intersection (S : Subring F) (B : LinearMap.BilinForm F E)
    (hB : B.IsSymm) (L : Submodule S E) (hL : SelfDual S B L) (e : L) (u : Sˣ)
    (hu : B (e : E) e = ((u : S) : F)) :
    SelfDual S (B.restrict (B.orthogonal (F ∙ (e : E))))
      (ComplementIntersection.onSubspace S L (B.orthogonal (F ∙ (e : E)))) := by
  let W := B.orthogonal (F ∙ (e : E))
  have hu0 : B (e : E) e ≠ 0 := by
    rw [hu]
    exact_mod_cast Units.ne_zero u
  intro z
  constructor
  · intro hz y hy
    exact (hL z).mp hz y hy
  · intro hz
    apply (hL (z : E)).mpr
    intro y hy
    let r := B (e : E) y / B e e
    have hr : r ∈ S := projection_coefficient_integral S B L hL e u hu ⟨y, hy⟩
    have hy' : y - r • (e : E) ∈ L := L.sub_mem hy (L.smul_mem (⟨r, hr⟩ : S) e.property)
    have hperp : y - r • (e : E) ∈ W := by
      dsimp only [W]
      rw [LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker]
      change B (e : E) (y - r • (e : E)) = 0
      rw [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right,
        div_mul_cancel₀ _ hu0, sub_self]
    have hze : B (z : E) (e : E) = 0 :=
      hB.eq (e : E) (z : E) ▸ z.property (e : E) (Submodule.mem_span_singleton_self _)
    have h := hz ⟨y - r • (e : E), hperp⟩ hy'
    change B (z : E) (y - r • (e : E)) ∈ S at h
    simpa only [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right,
      hze, mul_zero, sub_zero] using h

/-- A finite free nontrivial self-dual local lattice has a unit norm when
two is a unit. This is the non-dyadic first step of integral diagonalization. -/
theorem exists_unit_norm (S : Subring F) [IsLocalRing S]
    (B : LinearMap.BilinForm F E) (hB : B.IsSymm)
    (L : Submodule S E) [Module.Free S L] [Nontrivial L] (hL : SelfDual S B L)
    (π : S) (hπ : (π : F) ≠ 0) (hπnonunit : ¬ IsUnit π)
    (hmax : IsLocalRing.maximalIdeal S = Ideal.span {π}) (htwo : IsUnit (2 : S)) :
    ∃ x : L, IsUnit (pairing hL x x) := by
  classical
  let b := Module.Free.chooseBasis S L
  let i := Classical.arbitrary (Module.Free.ChooseBasisIndex S L)
  have hprim : ((b i : L) : E) ∉ (π : F) • L := by
    rintro ⟨y, hy, heq⟩
    have hLmap : π • (⟨y, hy⟩ : L) = b i := Subtype.ext heq
    have hcoord := congrArg (fun z : L ↦ b.repr z i) hLmap
    have hprod : π * b.repr ⟨y, hy⟩ i = 1 := by simpa only [map_smul, Finsupp.smul_apply,
      smul_eq_mul, Module.Basis.repr_self, Finsupp.single_eq_same] using hcoord
    exact hπnonunit (isUnit_iff_dvd_one.mpr ⟨b.repr ⟨y, hy⟩ i, hprod.symm⟩)
  obtain ⟨y, hy⟩ := exists_unit_pairing S B L hL π hπ hmax (b i) hprim
  by_cases hx : IsUnit (pairing hL (b i) (b i))
  · exact ⟨b i, hx⟩
  by_cases hyself : IsUnit (pairing hL y y)
  · exact ⟨y, hyself⟩
  refine ⟨b i + y, ?_⟩
  by_contra hsum
  let I := IsLocalRing.maximalIdeal S
  have hxI : pairing hL (b i) (b i) ∈ I := hx
  have hyI : pairing hL y y ∈ I := hyself
  have hsumI : pairing hL (b i + y) (b i + y) ∈ I := hsum
  have heq : pairing hL (b i + y) (b i + y) - pairing hL (b i) (b i) -
      pairing hL y y = 2 * pairing hL (b i) y := by
    apply Subtype.ext
    change B ((b i : E) + (y : E)) ((b i : E) + (y : E)) - B (b i) (b i) - B y y =
      ((2 : S) : F) * B (b i) y
    have htwoF : ((2 : S) : F) = 2 := rfl
    rw [htwoF, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.add_right, LinearMap.BilinForm.add_right, hB.eq (y : E) (b i)]
    ring
  have htwoI : 2 * pairing hL (b i) y ∈ I := heq ▸ I.sub_mem (I.sub_mem hsumI hxI) hyI
  exact (show ¬ IsUnit (2 * pairing hL (b i) y) from htwoI) (htwo.mul hy)

end NormEuclidean.LocalOrthogonalSplitting
