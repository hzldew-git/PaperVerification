import NormEuclidean.ChapterX.LocalUnitFrames
import NormEuclidean.ChapterX.LocalOrthogonalPair

/-!
# Binary unit frames in the complement of any local lattice vector

A primitive factor is constructed by the coordinate ideal. A unit-norm
primitive factor splits one line. Otherwise its unit mixed pairing supplies
two orthogonal unit lines containing it. Splitting these lines leaves a
self-dual lattice of rank at least two, in which the binary frame is
constructed. This proves the geometric step used at denominator divisors.
-/

noncomputable section

namespace NormEuclidean.LocalComplementFrames

open LocalPrimitivePairing LocalOrthogonalSplitting LocalUnitFrames Module
open scoped Pointwise

variable {F E : Type*} [Field F] [AddCommGroup E] [Module F E] [FiniteDimensional F E]
variable (S : Subring F) [IsLocalRing S] [IsPrincipalIdealRing S] [IsFractionRing S F]

/-- A rank-four or larger self-dual local lattice contains a binary
orthogonal unit frame perpendicular to any nonzero vector of that lattice. -/
theorem exists_binary_frame_in_orthogonal (B : LinearMap.BilinForm F E) (hB : B.IsSymm)
    (hreg : B.Nondegenerate) (L : Submodule S E) (hfg : L.FG)
    (hfull : Submodule.span F (L : Set E) = ⊤) (hL : SelfDual S B L)
    (hdim : 4 ≤ Module.finrank F E) (v : L) (hv : (v : E) ≠ 0)
    (π : S) (hπ : (π : F) ≠ 0) (hπnonunit : ¬ IsUnit π)
    (hmax : IsLocalRing.maximalIdeal S = Ideal.span {π}) (htwo : IsUnit (2 : S)) :
    ∃ (a b : Sˣ) (e f : E), e ∈ L ∧ f ∈ L ∧
      B e e = ((a : S) : F) ∧ B f f = ((b : S) : F) ∧ B e f = 0 ∧
      B (v : E) e = 0 ∧ B (v : E) f = 0 := by
  classical
  letI : Module.Finite S L := Module.Finite.of_fg hfg
  letI : IsTorsionFree S E := Module.IsTorsionFree.of_smul_eq_zero (fun r z h ↦ by
    change (r : F) • z = 0 at h
    rcases smul_eq_zero.mp h with hr | hz
    · exact Or.inl (Subtype.val_injective hr)
    · exact Or.inr hz)
  letI : Module.Free S L := inferInstance
  have hvL : v ≠ 0 := fun h ↦ hv (congrArg Subtype.val h)
  obtain ⟨d, w, hd, hdw, hw⟩ :=
    LocalPrimitiveVector.exists_primitive_factor v hvL π hπnonunit
  have hvw : (v : E) = (d : F) • (w : E) := (congrArg Subtype.val hdw).symm
  by_cases hnorm : IsUnit (pairing hL w w)
  · have hu : B (w : E) w = ((hnorm.unit : S) : F) :=
      congrArg Subtype.val hnorm.unit_spec.symm
    obtain ⟨a, b, e, f, he, hf, ha, hb, hef, hwe, hwf⟩ :=
      exists_binary_frame_orthogonal_unit_vector S B hB hreg L hfg hfull hL
        (by omega) w hnorm.unit hu π hπ hπnonunit hmax htwo
    exact ⟨a, b, e, f, he, hf, ha, hb, hef,
      by simp only [hvw, LinearMap.BilinForm.smul_left, hwe, mul_zero],
      by simp only [hvw, LinearMap.BilinForm.smul_left, hwf, mul_zero]⟩
  · have hprim : (w : E) ∉ (π : F) • L := by
      rintro ⟨y, hy, heq⟩
      exact hw ⟨y, hy⟩ (Subtype.ext heq)
    obtain ⟨y, hy⟩ := exists_unit_pairing S B L hL π hπ hmax w hprim
    obtain ⟨e, f, r, he, hf, hef, hsplit⟩ := LocalOrthogonalPair.exists_orthogonal_pair
      (pairingForm hL) (pairingForm_isSymm hB hL) htwo w y hnorm hy
    have heF : B (e : E) e = ((he.unit : S) : F) :=
      congrArg Subtype.val he.unit_spec.symm
    have hfF : B (f : E) f = ((hf.unit : S) : F) :=
      congrArg Subtype.val hf.unit_spec.symm
    have hefF : B (e : E) f = 0 := congrArg Subtype.val hef
    let W := B.orthogonal (F ∙ (e : E))
    let N := ComplementIntersection.onSubspace S L W
    have he0 : B (e : E) e ≠ 0 := by rw [heF]; exact_mod_cast Units.ne_zero he.unit
    have hevec : (e : E) ≠ 0 := by intro h; exact he0 (by simp [h])
    have hdimW : 3 ≤ Module.finrank F W := by
      have h := B.finrank_orthogonal hreg (F ∙ (e : E))
      rw [finrank_span_singleton hevec] at h
      dsimp only [W]
      omega
    have hfW : (f : E) ∈ W := by
      dsimp only [W]
      rw [LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker]
      exact hefF
    let fN : N := ⟨⟨(f : E), hfW⟩, f.property⟩
    have hWreg : (B.restrict W).Nondegenerate :=
      LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton
        B hreg hB.isRefl he0
    obtain ⟨a, b, g, h, hg, hh, ha, hb, hgh, hfg, hfh⟩ :=
      exists_binary_frame_orthogonal_unit_vector S (B.restrict W)
        ⟨fun x y ↦ hB.eq x y⟩ hWreg N
        (ComplementIntersection.onSubspace_fg S L hfg W)
        (ComplementIntersection.onSubspace_full S L hfull W)
        (selfDual_orthogonal_intersection S B hB L hL e he.unit heF)
        hdimW fN hf.unit hfF π hπ hπnonunit hmax htwo
    have hweq : (w : E) = (f : E) + (r : F) • (e : E) := congrArg Subtype.val hsplit
    have heg : B (e : E) (g : E) = 0 :=
      g.property (e : E) (Submodule.mem_span_singleton_self _)
    have heh : B (e : E) (h : E) = 0 :=
      h.property (e : E) (Submodule.mem_span_singleton_self _)
    exact ⟨a, b, g, h, hg, hh, ha, hb, hgh,
      by simp only [hvw, hweq, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.add_left,
        show B (f : E) (g : E) = 0 from hfg, heg, mul_zero, add_zero],
      by simp only [hvw, hweq, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.add_left,
        show B (f : E) (h : E) = 0 from hfh, heh, mul_zero, add_zero]⟩

end NormEuclidean.LocalComplementFrames
