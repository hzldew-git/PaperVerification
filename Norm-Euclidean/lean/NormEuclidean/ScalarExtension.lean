import NormEuclidean.Cancellation
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Extending a lattice-module isometry to the ambient fraction field

A full submodule becomes the ambient vector space after localization.
Consequently an isometry of the integral modules extends to an ambient
linear isometry. The construction neither chooses nor assumes a lattice
basis. Finite generation is not needed for this extension step.
-/

namespace NormEuclidean

open scoped nonZeroDivisors

namespace ScalarExtension

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable {R : Subring K} [IsFractionRing R K]

/-- Fullness permits clearing a denominator for every ambient vector. -/
theorem exists_denominator (L : Submodule R V)
    (hfull : Submodule.span K (L : Set V) = ⊤) (v : V) :
    ∃ d : R, d ≠ 0 ∧ (d : K) • v ∈ L := by
  have hv : v ∈ Submodule.span K (L : Set V) := by rw [hfull]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨b, hb, hby⟩ := hy
      refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
      have h := L.add_mem (L.smul_mem b hax) (L.smul_mem a hby)
      convert h using 1
      simp only [Subring.coe_mul, smul_add, smul_smul, Subring.smul_def]
      rw [mul_comm (b : K) (a : K)]
  | smul c x _ hx =>
      obtain ⟨d, hd, hdx⟩ := hx
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := R) c
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      have hbK : (b : K) ≠ 0 := by exact_mod_cast hb0
      refine ⟨b * d, mul_ne_zero hb0 hd, ?_⟩
      have h := L.smul_mem a hdx
      convert h using 1
      change (((b : K) * (d : K)) • (c • x)) = (a : K) • ((d : K) • x)
      rw [smul_smul, smul_smul]
      congr 1
      change (a : K) / (b : K) = c at hab
      rw [← hab]
      field_simp

/-- The inclusion of a full submodule realizes localization at all nonzero scalars. -/
theorem localizedSubtype (L : Submodule R V)
    (hfull : Submodule.span K (L : Set V) = ⊤) :
    IsLocalizedModule R⁰ L.subtype where
  map_units s := by
    rw [Module.End.isUnit_iff]
    have hs : (s : R) ≠ 0 := nonZeroDivisors.coe_ne_zero s
    have hsK : ((s : R) : K) ≠ 0 := by exact_mod_cast hs
    exact (LinearEquiv.smulOfNeZero K V ((s : R) : K) hsK).bijective
  surj v := by
    obtain ⟨d, hd, hdv⟩ := exists_denominator L hfull v
    exact ⟨(⟨(d : K) • v, hdv⟩, ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩), rfl⟩
  exists_of_eq h := by
    refine ⟨1, ?_⟩
    simpa using L.subtype_injective h

/-- Extend an integral-module equivalence by localization. -/
noncomputable def ambientEquiv (L : Submodule R V) (L' : Submodule R W)
    (hfull : Submodule.span K (L : Set V) = ⊤)
    (hfull' : Submodule.span K (L' : Set W) = ⊤)
    (φ : L ≃ₗ[R] L') : V ≃ₗ[K] W := by
  letI := localizedSubtype L hfull
  letI := localizedSubtype L' hfull'
  exact IsLocalizedModule.mapEquiv R⁰ L.subtype L'.subtype K φ

@[simp] theorem ambientEquiv_apply (L : Submodule R V) (L' : Submodule R W)
    (hfull : Submodule.span K (L : Set V) = ⊤)
    (hfull' : Submodule.span K (L' : Set W) = ⊤)
    (φ : L ≃ₗ[R] L') (v : L) :
    ambientEquiv L L' hfull hfull' φ (v : V) = (φ v : W) := by
  letI := localizedSubtype L hfull
  letI := localizedSubtype L' hfull'
  exact IsLocalizedModule.map_apply R⁰ L.subtype L'.subtype φ.toLinearMap v

/-- The input bridge from the manuscript's module-isometry definition to
its ambient-isometry realization. -/
noncomputable def isometry (Q : QuadraticForm K V) (Q' : QuadraticForm K W)
    (L : Submodule R V) (L' : Submodule R W)
    (hfull : Submodule.span K (L : Set V) = ⊤)
    (hfull' : Submodule.span K (L' : Set W) = ⊤)
    (φ : L ≃ₗ[R] L') (hφ : ∀ v : L, Q' (φ v : W) = Q (v : V)) :
    LatticeIsometry Q Q' L L' where
  toLinearEquiv := ambientEquiv L L' hfull hfull' φ
  q_eq v := by
    let g := ambientEquiv L L' hfull hfull' φ
    obtain ⟨d, hd, hdv⟩ := exists_denominator L hfull v
    have hdK : (d : K) ≠ 0 := by exact_mod_cast hd
    have hscaled : Q' ((d : K) • g v) = Q ((d : K) • v) := by
      rw [← g.map_smul]
      change Q' (ambientEquiv L L' hfull hfull' φ
        ((⟨(d : K) • v, hdv⟩ : L) : V)) = _
      rw [ambientEquiv_apply]
      exact hφ ⟨(d : K) • v, hdv⟩
    simp only [Q'.map_smul, Q.map_smul, smul_eq_mul] at hscaled
    exact mul_left_cancel₀ (mul_ne_zero hdK hdK) hscaled
  mem_iff v := by
    let g := ambientEquiv L L' hfull hfull' φ
    constructor
    · intro hv
      let w : L' := ⟨g v, hv⟩
      have h : g (φ.symm w : V) = g v := by
        change ambientEquiv L L' hfull hfull' φ (φ.symm w : V) = g v
        rw [ambientEquiv_apply, φ.apply_symm_apply]
      have heq : (φ.symm w : V) = v := g.injective h
      rw [← heq]
      exact (φ.symm w).property
    · intro hv
      change ambientEquiv L L' hfull hfull' φ v ∈ L'
      have h := ambientEquiv_apply L L' hfull hfull' φ ⟨v, hv⟩
      rw [h]
      exact (φ ⟨v, hv⟩).property

end ScalarExtension
end NormEuclidean
