import NormEuclidean.ChapterX.IntegralBiduality
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Finite integral overmodules of a full field frame

An integral quadratic lattice containing a field basis lies between its
integer span and the integral dual for the polar form. The actual finite
module interval controls all overmodules, including nonfree ones.
-/

noncomputable section

namespace NormEuclidean.IntegralFrameIntervals

open Module

variable {K V W : Type*} [Field K] [NumberField K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {Q : QuadraticForm K V} {P : QuadraticForm K W}

/-- The integer span of a full field frame. -/
def frameModule {n : ℕ} (b : Basis (Fin n) K V) : Submodule (integerSubring K) V :=
  Submodule.span (integerSubring K) (Set.range b)

omit [NumberField K] in
/-- A finite field frame has finitely generated integer span. -/
theorem frameModule_fg {n : ℕ} (b : Basis (Fin n) K V) : (frameModule b).FG :=
  Submodule.fg_span (Set.finite_range b)

omit [NumberField K] in
/-- Its integer span is full without claiming that it is the original lattice. -/
theorem frameModule_full {n : ℕ} (b : Basis (Fin n) K V) :
    Submodule.span K (frameModule b : Set V) = ⊤ := by
  rw [frameModule, Submodule.span_span_of_tower, b.span_eq]

omit [NumberField K] in
/-- A lattice object is determined by its actual carrier; the remaining fields are proofs. -/
theorem carrier_injective : Function.Injective
    (fun L : Lattice (integerSubring K) Q ↦ L.carrier) := by
  intro L M h
  cases L
  cases M
  cases h
  rfl

/-- Only finitely many norm-integral lattices contain any specified full field frame. -/
theorem finite_overmodules (hQ : Q.polarBilin.Nondegenerate) {n : ℕ}
    (b : Basis (Fin n) K V) :
    {L : Lattice (integerSubring K) Q | ∀ i, b i ∈ L.carrier}.Finite := by
  letI : Ring.HasFiniteQuotients (integerSubring K) :=
    inferInstanceAs (Ring.HasFiniteQuotients (NumberField.RingOfIntegers K))
  let U := LinearMap.BilinForm.dualSubmodule Q.polarBilin (frameModule b)
  have hU : U.FG := IntegralBiduality.dual_fg Q.polarBilin hQ _
    (frameModule_fg b) (frameModule_full b)
  have hinterval := LatticeInterval.finite_interval_of_full (integerSubring K)
    (frameModule b) U (frameModule_full b) hU
  have hpre := Set.Finite.preimage (carrier_injective (Q := Q)).injOn hinterval
  apply hpre.subset
  intro L hL
  have hle : frameModule b ≤ L.carrier := Submodule.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact hL i)
  refine ⟨hle, ?_⟩
  intro x hx y hy
  have hint := Hyperbolic.polar_mem L.carrier L.integral hx (hle hy)
  exact Submodule.mem_one.mpr ⟨⟨Q.polarBilin x y, hint⟩, rfl⟩

/-- Transport a norm-integral lattice through an actual ambient quadratic isometry. -/
def map (L : Lattice (integerSubring K) Q) (e : Q.IsometryEquiv P) :
    Lattice (integerSubring K) P where
  carrier := L.carrier.map (e.toLinearEquiv.toLinearMap.restrictScalars (integerSubring K))
  finite := L.finite.map _
  full := by
    change Submodule.span K (e.toLinearEquiv.toLinearMap '' (L.carrier : Set V)) = ⊤
    rw [← Submodule.map_span, L.full, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective
  integral := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_app x ▸ L.integral x hx

/-- The transport is an isometry of the original integral modules as well. -/
def mapIsometry (L : Lattice (integerSubring K) Q) (e : Q.IsometryEquiv P) :
    LatticeIsometry Q P L.carrier (map L e).carrier where
  toLinearEquiv := e.toLinearEquiv
  q_eq := e.map_app
  mem_iff x := by
    constructor
    · rintro ⟨y, hy, heq⟩
      rwa [e.injective heq] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩

end NormEuclidean.IntegralFrameIntervals
