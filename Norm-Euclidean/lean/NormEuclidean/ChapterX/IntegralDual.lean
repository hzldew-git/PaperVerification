import NormEuclidean.ScaleIdeal
import NormEuclidean.SpinorBridge
import NormEuclidean.IntegralDiagonalFrame
import NormEuclidean.ChapterX.LatticeInterval
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.RingTheory.Noetherian.Basic

/-!
# The actual half-polar integral dual in O'Meara 103:4

The dual is defined by `B(x,L) ⊆ R`, with `B(x,x)=Q(x)`. It is finite
and full for a regular number-field lattice, without integral freeness.
Its quadratic values need not be integral, so it is a submodule rather
than an instance of the project's norm-integral `Lattice` structure.
-/

noncomputable section

namespace NormEuclidean.IntegralDual

open QuadraticMap

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

/-- The literal associated-bilinear integral dual; no integral inverse of two is assumed. -/
def dual (L : Submodule (integerSubring K) V) : Submodule (integerSubring K) V :=
  (halfPolar Q).dualSubmodule L

omit [NumberField K] [Invertible (2 : K)] in
@[simp] theorem mem_dual (L : Submodule (integerSubring K) V) (x : V) :
    x ∈ dual Q L ↔ ∀ y ∈ L, halfPolar Q x y ∈ integerSubring K := by
  simp only [dual, LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one]
  constructor
  · intro h y hy
    obtain ⟨r, hr⟩ := h y hy
    exact hr ▸ r.property
  · intro h y hy
    exact ⟨⟨halfPolar Q x y, h y hy⟩, rfl⟩

omit [NumberField K] [Invertible (2 : K)] in
theorem dual_antitone {L M : Submodule (integerSubring K) V} (h : L ≤ M) :
    dual Q M ≤ dual Q L := fun _ hx y hy ↦ hx y (h hy)

omit [Invertible (2 : K)] in
/-- Norm integrality gives `2L ⊆ L#`, including at dyadic places.
It does not in general give `L ⊆ L#`. -/
theorem two_smul_mem_dual (L : Lattice (integerSubring K) Q) (x : V) (hx : x ∈ L.carrier) :
    (2 : K) • x ∈ dual Q L.carrier := by
  apply (mem_dual Q L.carrier _).mpr
  intro y hy
  rw [LinearMap.BilinForm.smul_left, two_mul_halfPolar]
  exact Hyperbolic.polar_mem L.carrier L.integral hx hy

omit [Invertible (2 : K)] in
/-- The integral dual remains full; multiplying by two suffices even when
the original half-polar scale is not integral. -/
theorem dual_full (L : Lattice (integerSubring K) Q) :
    Submodule.span K (dual Q L.carrier : Set V) = ⊤ := by
  apply top_unique
  rw [← L.full]
  apply Submodule.span_le.mpr
  intro x hx
  change x ∈ Submodule.span K (dual Q L.carrier : Set V)
  have h2 : (2 : K) • x ∈ Submodule.span K (dual Q L.carrier : Set V) :=
    Submodule.subset_span (two_smul_mem_dual Q L x hx)
  have hi := (Submodule.span K (dual Q L.carrier : Set V)).smul_mem (2 : K)⁻¹ h2
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : K) ≠ 0), one_smul] using hi

/-- A field basis inside the original lattice bounds its dual by the free
dual-basis model. Noetherianity gives finite generation of the actual dual. -/
theorem dual_fg (hQ : Q.polarBilin.Nondegenerate) (L : Lattice (integerSubring K) Q) :
    (dual Q L.carrier).FG := by
  classical
  let F := L.integralDiagonalFrame
  have hB : (halfPolar Q).Nondegenerate := (SpinorBridge.quadraticSpace Q hQ).nondegenerate
  have hle : dual Q L.carrier ≤
      (halfPolar Q).dualSubmodule (Submodule.span (integerSubring K) (Set.range F.basis)) :=
    dual_antitone Q F.span_le
  rw [LinearMap.BilinForm.dualSubmodule_span_of_basis _ hB F.basis] at hle
  exact (Submodule.fg_span (Set.finite_range ((halfPolar Q).dualBasis hB F.basis))).of_le hle

omit [Invertible (2 : K)] in
/-- Containment in the literal dual is exactly integrality of the half-polar scale. -/
theorem le_dual_iff_scale_integral (L : Lattice (integerSubring K) Q) :
    L.carrier ≤ dual Q L.carrier ↔ L.scaleIdeal ≤ 1 := by
  rw [← FractionalIdeal.coe_le_coe, Lattice.coe_scaleIdeal, FractionalIdeal.coe_one]
  change L.carrier ≤ (halfPolar Q).dualSubmodule L.carrier ↔
    L.scaleSubmodule ≤ (1 : Submodule (NumberField.RingOfIntegers K) K)
  constructor
  · intro h
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    exact h x.2 y y.2
  · intro h x hx y hy
    apply h
    exact Submodule.subset_span ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩

/-- The finite dual interval in the 103:4 induction is valid for actual
possibly nonfree lattices with integral scale. -/
theorem finite_dual_interval (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice (integerSubring K) Q) (hscale : L.scaleIdeal ≤ 1) :
    L.carrier ≤ dual Q L.carrier ∧
      {M : Submodule (integerSubring K) V | L.carrier ≤ M ∧ M ≤ dual Q L.carrier}.Finite := by
  letI : Ring.HasFiniteQuotients (integerSubring K) :=
    inferInstanceAs (Ring.HasFiniteQuotients (NumberField.RingOfIntegers K))
  exact ⟨(le_dual_iff_scale_integral Q L).mpr hscale,
    LatticeInterval.finite_interval_of_full (integerSubring K) L.carrier (dual Q L.carrier)
      L.full (dual_fg Q hQ L)⟩

omit [Invertible (2 : K)] in
/-- The standard norm-integral hyperbolic basis vector is in the half-polar
dual exactly when the coefficient ring contains one half. This exposes the
dyadic normalization issue instead of asserting self-duality from norm integrality. -/
theorem hyperbolic_e_mem_dual_iff (L : Lattice (integerSubring K) Q) :
    (Hyperbolic.e : Hyperbolic K V) ∈ dual (Hyperbolic.form Q) L.hyperbolic.carrier ↔
      (2 : K)⁻¹ ∈ integerSubring K := by
  constructor
  · intro he
    have hf := (mem_dual (Hyperbolic.form Q) L.hyperbolic.carrier _).mp he
      (Hyperbolic.f : Hyperbolic K V) (Hyperbolic.mem_f L.carrier)
    simpa [halfPolar_apply, polar, Hyperbolic.form_apply, Hyperbolic.q,
      Hyperbolic.e, Hyperbolic.f] using hf
  · intro hhalf
    apply (mem_dual (Hyperbolic.form Q) L.hyperbolic.carrier _).mpr
    intro z hz
    change Hyperbolic.Mem L.carrier z at hz
    have heq : halfPolar (Hyperbolic.form Q) (Hyperbolic.e : Hyperbolic K V) z =
        (2 : K)⁻¹ * z.2.2 := by
      simp [halfPolar_apply, polar, Hyperbolic.form_apply, Hyperbolic.q, Hyperbolic.e]
      ring
    rw [heq]
    exact (integerSubring K).mul_mem hhalf hz.2.2

end NormEuclidean.IntegralDual
