import Mathlib

/-!
Abstract definitions and the strict/closed covering-radius bridge used in the
paper.  The cost function represents the squared trace distance.
-/

namespace TraceEuclidean

/-- Every point has a lattice representative whose cost is strictly below `t`. -/
def StrictEuclidean {X Y : Type*} (cost : X → Y → ℝ) (t : ℝ) : Prop :=
  ∀ x, ∃ y, cost x y < t

/-- Every point has a lattice representative whose cost is at most `t`. -/
def ClosedEuclidean {X Y : Type*} (cost : X → Y → ℝ) (t : ℝ) : Prop :=
  ∀ x, ∃ y, cost x y ≤ t

/--
An order-theoretic specification of a squared covering radius.  `upper` gives
the covering inequality, while `sharp` says that every smaller proposed bound
fails somewhere.
-/
structure SquaredCoveringRadiusSpec {X Y : Type*}
    (cost : X → Y → ℝ) (ρsq : ℝ) : Prop where
  upper : ∀ x, ∃ y, cost x y ≤ ρsq
  sharp : ∀ r, r < ρsq → ∃ x, ∀ y, r < cost x y

/-- A strict radius bound implies the strict Euclidean condition. -/
theorem strictEuclidean_of_radius_lt {X Y : Type*} {cost : X → Y → ℝ}
    {ρsq t : ℝ} (hρ : SquaredCoveringRadiusSpec cost ρsq) (hlt : ρsq < t) :
    StrictEuclidean cost t := by
  intro x
  obtain ⟨y, hy⟩ := hρ.upper x
  exact ⟨y, lt_of_le_of_lt hy hlt⟩

/-- The strict Euclidean condition forces the squared covering radius to be at most `t`. -/
theorem radius_le_of_strictEuclidean {X Y : Type*} {cost : X → Y → ℝ}
    {ρsq t : ℝ} (hρ : SquaredCoveringRadiusSpec cost ρsq)
    (hE : StrictEuclidean cost t) : ρsq ≤ t := by
  by_contra h
  have htρ : t < ρsq := lt_of_not_ge h
  obtain ⟨x, hx⟩ := hρ.sharp t htρ
  obtain ⟨y, hy⟩ := hE x
  exact (lt_asymm (hx y)) hy

/-- A point whose cost is always at least `t` obstructs strict Euclideanity. -/
theorem not_strictEuclidean_of_witness {X Y : Type*} {cost : X → Y → ℝ}
    {t : ℝ} (x : X) (hx : ∀ y, t ≤ cost x y) :
    ¬ StrictEuclidean cost t := by
  intro hE
  obtain ⟨y, hy⟩ := hE x
  exact (not_lt_of_ge (hx y)) hy

/-- Pointwise domination transfers a strict Euclidean property in the needed direction. -/
theorem strictEuclidean_of_pointwise_le {X Y : Type*}
    {small large : X → Y → ℝ} {t : ℝ}
    (hdom : ∀ x y, small x y ≤ large x y)
    (hlarge : StrictEuclidean large t) : StrictEuclidean small t := by
  intro x
  obtain ⟨y, hy⟩ := hlarge x
  exact ⟨y, lt_of_le_of_lt (hdom x y) hy⟩

/-- The quantifier step used after the power-mean inequality in the p-norm corollary. -/
theorem pNormEuclidean_imp_traceEuclidean {X Y : Type*}
    {traceMean pMean : X → Y → ℝ}
    (powerMean : ∀ x y, traceMean x y ≤ pMean x y)
    (hp : StrictEuclidean pMean 1) : StrictEuclidean traceMean 1 :=
  strictEuclidean_of_pointwise_le powerMean hp

end TraceEuclidean
