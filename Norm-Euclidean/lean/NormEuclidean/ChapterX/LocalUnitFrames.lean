import NormEuclidean.ChapterX.LocalOrthogonalSplitting
import NormEuclidean.ChapterX.LocalPrimitiveVector

/-!
# Orthogonal unit frames in self-dual local lattices

Primitive pairing and integral unit-line splitting construct the frame.
The coefficient ring is a local PID in its fraction field; no dyadic
context or assumed diagonalization is used.
-/

noncomputable section

namespace NormEuclidean.LocalUnitFrames

open LocalPrimitivePairing LocalOrthogonalSplitting Module

variable {F E : Type*} [Field F] [AddCommGroup E] [Module F E]
variable (S : Subring F) [IsLocalRing S] [IsPrincipalIdealRing S] [IsFractionRing S F]

/-- Positive ambient dimension makes a finite full module nontrivial;
the primitive pairing argument then constructs a unit-norm vector. -/
theorem exists_unit_vector (B : LinearMap.BilinForm F E) (hB : B.IsSymm)
    (L : Submodule S E) (hfg : L.FG) (hfull : Submodule.span F (L : Set E) = ⊤)
    (hL : SelfDual S B L) (hpos : 0 < Module.finrank F E)
    (π : S) (hπ : (π : F) ≠ 0) (hπnonunit : ¬ IsUnit π)
    (hmax : IsLocalRing.maximalIdeal S = Ideal.span {π}) (htwo : IsUnit (2 : S)) :
    ∃ (x : L) (u : Sˣ), B (x : E) x = ((u : S) : F) := by
  letI : Module.Finite S L := Module.Finite.of_fg hfg
  letI : IsTorsionFree S E := Module.IsTorsionFree.of_smul_eq_zero (fun r z h ↦ by
    change (r : F) • z = 0 at h
    rcases smul_eq_zero.mp h with hr | hz
    · exact Or.inl (Subtype.val_injective hr)
    · exact Or.inr hz)
  letI : Module.Free S L := inferInstance
  letI : FiniteDimensional F E := Module.finite_of_finrank_pos hpos
  obtain ⟨y, hy⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  obtain ⟨d, hd, hdy⟩ := ScalarExtension.exists_denominator L hfull y
  have hdF : (d : F) ≠ 0 := by exact_mod_cast hd
  have hdy0 : (d : F) • y ≠ 0 := smul_ne_zero hdF hy
  letI : Nontrivial L := nontrivial_of_ne (⟨(d : F) • y, hdy⟩ : L) 0
    (fun h ↦ hdy0 (congrArg Subtype.val h))
  obtain ⟨x, hx⟩ := exists_unit_norm S B hB L hL π hπ hπnonunit hmax htwo
  exact ⟨x, hx.unit, congrArg Subtype.val hx.unit_spec.symm⟩

variable [FiniteDimensional F E]

/-- Two orthogonal unit-norm vectors are constructed in every self-dual
local lattice of rank at least two. -/
theorem exists_binary_unit_frame (B : LinearMap.BilinForm F E) (hB : B.IsSymm)
    (hreg : B.Nondegenerate) (L : Submodule S E) (hfg : L.FG)
    (hfull : Submodule.span F (L : Set E) = ⊤) (hL : SelfDual S B L)
    (hdim : 2 ≤ Module.finrank F E)
    (π : S) (hπ : (π : F) ≠ 0) (hπnonunit : ¬ IsUnit π)
    (hmax : IsLocalRing.maximalIdeal S = Ideal.span {π}) (htwo : IsUnit (2 : S)) :
    ∃ (a b : Sˣ) (e f : E), e ∈ L ∧ f ∈ L ∧
      B e e = ((a : S) : F) ∧ B f f = ((b : S) : F) ∧ B e f = 0 := by
  obtain ⟨e, a, ha⟩ := exists_unit_vector S B hB L hfg hfull hL (by omega)
    π hπ hπnonunit hmax htwo
  let W := B.orthogonal (F ∙ (e : E))
  let N := ComplementIntersection.onSubspace S L W
  have ha0 : B (e : E) e ≠ 0 := by rw [ha]; exact_mod_cast Units.ne_zero a
  have he0 : (e : E) ≠ 0 := by intro he; exact ha0 (by simp [he])
  have hdimW : Module.finrank F W + 1 = Module.finrank F E := by
    have h := B.finrank_orthogonal hreg (F ∙ (e : E))
    rw [finrank_span_singleton he0] at h
    dsimp only [W]
    omega
  have hN : SelfDual S (B.restrict W) N :=
    selfDual_orthogonal_intersection S B hB L hL e a ha
  obtain ⟨f, b, hb⟩ := exists_unit_vector S (B.restrict W)
    ⟨fun x y ↦ hB.eq x y⟩ N (ComplementIntersection.onSubspace_fg S L hfg W)
    (ComplementIntersection.onSubspace_full S L hfull W) hN (by omega)
    π hπ hπnonunit hmax htwo
  exact ⟨a, b, e, (f : W), e.property, f.property, ha, hb,
    (f : W).property (e : E) (Submodule.mem_span_singleton_self _)⟩

/-- A unit line splits off integrally, leaving enough self-dual rank to
construct a binary unit frame orthogonal to that line. -/
theorem exists_binary_frame_orthogonal_unit_vector (B : LinearMap.BilinForm F E)
    (hB : B.IsSymm) (hreg : B.Nondegenerate) (L : Submodule S E) (hfg : L.FG)
    (hfull : Submodule.span F (L : Set E) = ⊤) (hL : SelfDual S B L)
    (hdim : 3 ≤ Module.finrank F E) (v : L) (u : Sˣ)
    (hu : B (v : E) v = ((u : S) : F))
    (π : S) (hπ : (π : F) ≠ 0) (hπnonunit : ¬ IsUnit π)
    (hmax : IsLocalRing.maximalIdeal S = Ideal.span {π}) (htwo : IsUnit (2 : S)) :
    ∃ (a b : Sˣ) (e f : E), e ∈ L ∧ f ∈ L ∧
      B e e = ((a : S) : F) ∧ B f f = ((b : S) : F) ∧ B e f = 0 ∧
      B (v : E) e = 0 ∧ B (v : E) f = 0 := by
  let W := B.orthogonal (F ∙ (v : E))
  let N := ComplementIntersection.onSubspace S L W
  have hu0 : B (v : E) v ≠ 0 := by rw [hu]; exact_mod_cast Units.ne_zero u
  have hv0 : (v : E) ≠ 0 := by intro hv; exact hu0 (by simp [hv])
  have hdimW : 2 ≤ Module.finrank F W := by
    have h := B.finrank_orthogonal hreg (F ∙ (v : E))
    rw [finrank_span_singleton hv0] at h
    dsimp only [W]
    omega
  have hWreg : (B.restrict W).Nondegenerate :=
    LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton B hreg hB.isRefl hu0
  obtain ⟨a, b, e, f, he, hf, ha, hb, hef⟩ := exists_binary_unit_frame S
    (B.restrict W) ⟨fun x y ↦ hB.eq x y⟩ hWreg N
    (ComplementIntersection.onSubspace_fg S L hfg W)
    (ComplementIntersection.onSubspace_full S L hfull W)
    (selfDual_orthogonal_intersection S B hB L hL v u hu)
    hdimW π hπ hπnonunit hmax htwo
  exact ⟨a, b, e, f, he, hf, ha, hb, hef,
    e.property (v : E) (Submodule.mem_span_singleton_self _),
    f.property (v : E) (Submodule.mem_span_singleton_self _)⟩

end NormEuclidean.LocalUnitFrames
