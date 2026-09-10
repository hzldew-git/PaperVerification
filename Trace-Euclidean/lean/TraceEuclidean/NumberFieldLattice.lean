import TraceEuclidean.Basic
import Mathlib.Algebra.Module.Lattice
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm

/-!
The number-field and lattice semantics used by the manuscript.  Unlike the
generic predicates in `Basic`, every definition here mentions the field trace,
the ring of integers, a full lattice, and a quadratic form explicitly.
-/

namespace TraceEuclidean

open scoped NumberField

noncomputable section

section OneField

variable {F V : Type*} [Field F] [NumberField F]
variable [NumberField.IsTotallyReal F]
variable [AddCommGroup V] [Module F V]
variable [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V]

/-- An element of a totally real field is positive at every real embedding. -/
def TotallyPositive (a : F) : Prop :=
  ∀ σ : F →+* ℝ, 0 < σ a

/-- Positive definiteness in the sense used for quadratic spaces over `F`. -/
def TotallyPositiveDefinite (Q : QuadraticForm F V) : Prop :=
  ∀ x : V, x ≠ 0 → TotallyPositive (Q x)

/-- The manuscript's trace of the quadratic displacement, viewed in `ℝ`. -/
def traceCost (Q : QuadraticForm F V) (x y : V) : ℝ :=
  ((Algebra.trace ℚ F (Q (x - y)) : ℚ) : ℝ)

/-- Definition 1.1(i): strict `t`-trace Euclideanity of an `𝓞_F`-lattice. -/
def IsTraceEuclidean (Q : QuadraticForm F V) (L : Submodule (𝓞 F) V)
    (t : ℝ) : Prop :=
  ∀ x : V, ∃ y : L, traceCost Q x y.1 < t

/-- The closed trace inequality occurring in Lemma 2.2. -/
def IsClosedTraceEuclidean (Q : QuadraticForm F V)
    (L : Submodule (𝓞 F) V) (t : ℝ) : Prop :=
  ∀ x : V, ∃ y : L, traceCost Q x y.1 ≤ t

/-- Integrality: all quadratic values on the lattice lie in `𝓞_F`. -/
def LatticeIntegral (Q : QuadraticForm F V)
    (L : Submodule (𝓞 F) V) : Prop :=
  ∀ x : L, _root_.IsIntegral ℤ (Q x.1)

/-- Classic integrality: all associated bilinear values lie in `𝓞_F`. -/
def LatticeClassicIntegral (Q : QuadraticForm F V)
    (L : Submodule (𝓞 F) V) : Prop :=
  ∀ x y : L,
    _root_.IsIntegral ℤ (QuadraticMap.associated Q x.1 y.1)

/-- Data of a positive definite integral lattice on a nondegenerate space. -/
structure NumberFieldLattice where
  Q : QuadraticForm F V
  L : Submodule (𝓞 F) V
  full : L.IsLattice F
  nondegenerate : Q.Nondegenerate
  positiveDefinite : TotallyPositiveDefinite Q
  integral : LatticeIntegral Q L

namespace NumberFieldLattice

/-- Rank of the quadratic space, hence also the rank of its full lattice. -/
def rank (_M : NumberFieldLattice (F := F) (V := V)) : ℕ :=
  Module.finrank F V

/-- Degree of the ground field. -/
def degree (_M : NumberFieldLattice (F := F) (V := V)) : ℕ :=
  Module.finrank ℚ F

/-- The additional scale-integrality condition in Theorem 1.2. -/
def IsClassicIntegral (M : NumberFieldLattice (F := F) (V := V)) : Prop :=
  LatticeClassicIntegral M.Q M.L

/-- Trace Euclideanity of the bundled lattice. -/
def IsTraceEuclidean (M : NumberFieldLattice (F := F) (V := V))
    (t : ℝ) : Prop :=
  TraceEuclidean.IsTraceEuclidean M.Q M.L t

end NumberFieldLattice

omit [NumberField.IsTotallyReal F] [IsScalarTower (NumberField.RingOfIntegers F) F V] in
theorem isTraceEuclidean_iff_strictEuclidean
    (Q : QuadraticForm F V) (L : Submodule (𝓞 F) V) (t : ℝ) :
    IsTraceEuclidean Q L t ↔
      StrictEuclidean (fun x (y : L) ↦ traceCost Q x y.1) t :=
  Iff.rfl

omit [NumberField.IsTotallyReal F] [IsScalarTower (NumberField.RingOfIntegers F) F V] in
theorem isClosedTraceEuclidean_iff_closedEuclidean
    (Q : QuadraticForm F V) (L : Submodule (𝓞 F) V) (t : ℝ) :
    IsClosedTraceEuclidean Q L t ↔
      ClosedEuclidean (fun x (y : L) ↦ traceCost Q x y.1) t :=
  Iff.rfl

/-- Definition 1.7 specialized to the square form on the ring of integers. -/
def IsFieldTraceEuclidean (t : ℝ) : Prop :=
  ∀ x : F, ∃ y : 𝓞 F,
    ((Algebra.trace ℚ F ((x - (y : F)) ^ 2) : ℚ) : ℝ) < t

end OneField

section VaryingFields

variable {F F' V V' : Type*}
variable [Field F] [Field F'] [NumberField F] [NumberField F']
variable [NumberField.IsTotallyReal F] [NumberField.IsTotallyReal F']
variable [AddCommGroup V] [AddCommGroup V'] [Module F V] [Module F' V']
variable [Module (𝓞 F) V] [Module (𝓞 F') V']
variable [IsScalarTower (𝓞 F) F V] [IsScalarTower (𝓞 F') F' V']

/--
The equivalence relation described immediately before Theorem 1.2: a field
isomorphism and a semilinear isometry carrying one lattice onto the other.
-/
structure NumberFieldLatticeEquiv
    (M : NumberFieldLattice (F := F) (V := V))
    (M' : NumberFieldLattice (F := F') (V := V')) where
  fieldEquiv : F ≃+* F'
  spaceEquiv : V ≃+ V'
  map_smul : ∀ a x, spaceEquiv (a • x) = fieldEquiv a • spaceEquiv x
  mapsLattice : ∀ x : V, x ∈ M.L ↔ spaceEquiv x ∈ M'.L
  mapQuadratic : ∀ x : V, M'.Q (spaceEquiv x) = fieldEquiv (M.Q x)

end VaryingFields

end

end TraceEuclidean
