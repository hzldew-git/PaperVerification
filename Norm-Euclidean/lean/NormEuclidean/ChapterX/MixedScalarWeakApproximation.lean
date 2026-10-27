import NormEuclidean.ChapterX.FiniteWeakApproximation
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Weak approximation in actual finite and infinite completions

Finite prime absolute values and infinite absolute values are proved
inequivalent, including dyadic primes. The absolute-value weak approximation
theorem is then transferred to the actual completed fields on both sides.
This is simultaneous weak approximation, without outside-target integrality.
-/

noncomputable section

namespace NormEuclidean.MixedScalarWeakApproximation

open IsDedekindDomain CompletedIntegralLattice Filter Topology

variable {K : Type*} [Field K] [NumberField K]

local instance : Module.Finite ℤ (integerSubring K) :=
  inferInstanceAs (Module.Finite ℤ (NumberField.RingOfIntegers K))
local instance : Module.Free ℤ (integerSubring K) :=
  inferInstanceAs (Module.Free ℤ (NumberField.RingOfIntegers K))

theorem norm_infinite_map (w : NumberField.InfinitePlace K) (x : WithAbs w.1) :
    ‖algebraMap K w.Completion (WithAbs.equiv w.1 x)‖ = ‖x‖ := by
  change ‖(x : w.Completion)‖ = ‖x‖
  rw [NumberField.InfinitePlace.Completion.norm_coe]
  rfl

/-- An actual finite or infinite number-field place. -/
abbrev Place (K : Type*) [Field K] [NumberField K] :=
  HeightOneSpectrum (integerSubring K) ⊕ NumberField.InfinitePlace K

/-- The absolute value attached to either kind of actual place. -/
def absoluteValue : Place K → AbsoluteValue K ℝ
  | .inl v => NumberField.HeightOneSpectrum.adicAbv K v
  | .inr w => w.1

/-- The actual completed field at a finite or infinite place. -/
abbrev FieldAt : Place K → Type _
  | .inl v => LocalField (integerSubring K) v
  | .inr w => w.Completion

instance (p : Place K) : NormedField (FieldAt p) := by
  cases p <;> dsimp only [FieldAt] <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
instance (p : Place K) : Algebra K (FieldAt p) := by
  cases p <;> dsimp only [FieldAt] <;> infer_instance

/-- Finite and infinite prime absolute values cannot be equivalent: the
integer two has finite absolute value at most one and infinite value two. -/
theorem finite_infinite_not_isEquiv (v : HeightOneSpectrum (integerSubring K))
    (w : NumberField.InfinitePlace K) :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv w.1 := by
  intro h
  have htwo := h.le_one_iff.mp
    (NumberField.HeightOneSpectrum.adicAbv_natCast_le_one (K := K) v 2)
  change w (2 : K) ≤ 1 at htwo
  have hw : w (2 : K) = (2 : ℝ) := w.map_natCast 2
  rw [hw] at htwo
  norm_num at htwo

theorem absoluteValue_isNontrivial (p : Place K) : (absoluteValue p).IsNontrivial := by
  cases p with
  | inl v => exact FiniteWeakApproximation.adicAbv_isNontrivial (integerSubring K) v
  | inr w => exact w.isNontrivial

theorem absoluteValue_inequivalent :
    Pairwise fun p r : Place K ↦ ¬ (absoluteValue p).IsEquiv (absoluteValue r) := by
  intro p r hpr h
  cases p with
  | inl v =>
    cases r with
    | inl u => exact hpr (congrArg Sum.inl
        (FiniteWeakApproximation.eq_of_adicAbv_isEquiv (integerSubring K) h))
    | inr w => exact finite_infinite_not_isEquiv v w h
  | inr w =>
    cases r with
    | inl v => exact finite_infinite_not_isEquiv v w h.symm
    | inr z => exact hpr (congrArg Sum.inr (NumberField.InfinitePlace.eq_iff_isEquiv.mpr h))

/-- The absolute-value copy maps to the actual completion at the same place. -/
def completionMap (p : Place K) : WithAbs (absoluteValue p) →+* FieldAt p :=
  (algebraMap K (FieldAt p)).comp (WithAbs.equiv (absoluteValue p)).toRingHom

theorem norm_completionMap (p : Place K) (x : WithAbs (absoluteValue p)) :
    ‖completionMap p x‖ = ‖x‖ := by
  cases p with
  | inl v => exact FiniteWeakApproximation.norm_completionMap (integerSubring K) v x
  | inr w => exact norm_infinite_map w x

theorem isometry_completionMap (p : Place K) : Isometry (completionMap p) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm_sub, dist_eq_norm_sub, ← map_sub, norm_completionMap]

theorem denseRange_completionMap (p : Place K) : DenseRange (completionMap p) := by
  cases p with
  | inl v => exact FiniteWeakApproximation.denseRange_completionMap (integerSubring K) v
  | inr w =>
    change DenseRange ((↑) : WithAbs w.1 → w.Completion)
    exact NumberField.InfinitePlace.Completion.denseRange_coe w

/-- Simultaneous weak approximation at any finite mixed set of actual
completed fields. No mixed density hypothesis is supplied. -/
theorem denseRange_diagonal (T : Finset (Place K)) :
    DenseRange (fun a : K ↦ fun p : T ↦ algebraMap K (FieldAt p.1) a) := by
  let w : T → AbsoluteValue K ℝ := fun p ↦ absoluteValue p.1
  have hn : ∀ p : T, (w p).IsNontrivial := fun p ↦ absoluteValue_isNontrivial p.1
  have hi : Pairwise fun p r : T ↦ ¬ (w p).IsEquiv (w r) :=
    fun p r hpr ↦ absoluteValue_inequivalent (Subtype.coe_injective.ne hpr)
  have hd := AbsoluteValue.denseRange_algebraMap_pi hn hi
  have hp : DenseRange (Pi.map (fun p : T ↦ completionMap p.1)) :=
    DenseRange.piMap (fun p ↦ denseRange_completionMap p.1)
  have hc : Continuous (Pi.map (fun p : T ↦ completionMap p.1)) :=
    continuous_pi (fun p ↦ (isometry_completionMap p.1).continuous.comp (continuous_apply p))
  convert hp.comp hd hc using 1
  funext a p
  rfl

theorem exists_scalar (T : Finset (Place K)) (x : (p : T) → FieldAt p.1)
    (W : (p : T) → Set (FieldAt p.1)) (hW : ∀ p, W p ∈ 𝓝 (x p)) :
    ∃ a : K, ∀ p : T, algebraMap K (FieldAt p.1) a ∈ W p := by
  have hnb : {z | ∀ p : T, z p ∈ W p} ∈ 𝓝 x :=
    Filter.eventually_all.mpr (fun p ↦ (continuous_apply p).tendsto x |>.eventually (hW p))
  exact (denseRange_diagonal T).mem_nhds hnb

theorem denseRange_diagonal_of_injective {ι : Type*} [Fintype ι]
    (p : ι → Place K) (hi : Function.Injective p) :
    DenseRange (fun a : K ↦ fun i ↦ algebraMap K (FieldAt (p i)) a) := by
  let w : ι → AbsoluteValue K ℝ := fun i ↦ absoluteValue (p i)
  have hn : ∀ i, (w i).IsNontrivial := fun i ↦ absoluteValue_isNontrivial (p i)
  have he : Pairwise fun i j ↦ ¬ (w i).IsEquiv (w j) :=
    fun i j hij ↦ absoluteValue_inequivalent (hi.ne hij)
  have hd := AbsoluteValue.denseRange_algebraMap_pi hn he
  have hp : DenseRange (Pi.map (fun i ↦ completionMap (p i))) :=
    DenseRange.piMap (fun i ↦ denseRange_completionMap (p i))
  have hc : Continuous (Pi.map (fun i ↦ completionMap (p i))) :=
    continuous_pi (fun i ↦ (isometry_completionMap (p i)).continuous.comp (continuous_apply i))
  convert hp.comp hd hc using 1
  funext a i
  rfl

/-- Mixed weak approximation in the exact finite/infinite indexing used by
33G when one infinite place is excluded. Both kinds of targets are actual
completed scalars, and may be arbitrary or fractional. -/
theorem exists_finite_infinite (T : Finset (HeightOneSpectrum (integerSubring K)))
    (q : NumberField.InfinitePlace K)
    (x : (v : T) → LocalField (integerSubring K) v.1)
    (W : (v : T) → Set (LocalField (integerSubring K) v.1))
    (hW : ∀ v, W v ∈ 𝓝 (x v))
    (z : (w : {w : NumberField.InfinitePlace K // w ≠ q}) → w.1.Completion)
    (U : (w : {w : NumberField.InfinitePlace K // w ≠ q}) → Set w.1.Completion)
    (hU : ∀ w, U w ∈ 𝓝 (z w)) :
    ∃ a : K, (∀ v : T, algebraMap K (LocalField (integerSubring K) v.1) a ∈ W v) ∧
      ∀ w : {w : NumberField.InfinitePlace K // w ≠ q},
        algebraMap K w.1.Completion a ∈ U w := by
  classical
  let ι := T ⊕ {w : NumberField.InfinitePlace K // w ≠ q}
  let p : ι → Place K := Sum.map Subtype.val Subtype.val
  have hp : Function.Injective p := Sum.map_injective.mpr
    ⟨Subtype.coe_injective, Subtype.coe_injective⟩
  let target : (i : ι) → FieldAt (p i)
    | .inl v => x v
    | .inr w => z w
  let B : (i : ι) → Set (FieldAt (p i))
    | .inl v => W v
    | .inr w => U w
  have hB (i : ι) : B i ∈ 𝓝 (target i) := by
    cases i with
    | inl v => exact hW v
    | inr w => exact hU w
  have hnb : {b | ∀ i : ι, b i ∈ B i} ∈ 𝓝 target :=
    Filter.eventually_all.mpr (fun i ↦ (continuous_apply i).tendsto target |>.eventually (hB i))
  obtain ⟨a, ha⟩ := (denseRange_diagonal_of_injective p hp).mem_nhds hnb
  exact ⟨a, fun v ↦ ha (.inl v), fun w ↦ ha (.inr w)⟩

end NormEuclidean.MixedScalarWeakApproximation
