import NormEuclidean.AdelicComparison
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
# The finite adelic target for strong approximation

A global proper orthogonal transformation has a genuine restricted finite
adelic diagonal relative to any integral lattice.  Restrictedness is proved
by transporting the lattice globally and using equality of completed carriers
away from finitely many primes.

For an adelic comparison from `L` to `M`, its right coset by the completed
proper stabilizer of `L` is the exact approximation target.  Any global
diagonal which hits this coset maps the completed carrier of `L` onto that of
`M` at every finite place.  This file identifies and proves the algebraic
target; it does not assert that a diagonal Spin element hits the target.
-/

noncomputable section

namespace NormEuclidean.AdelicApproximation

open Filter IsDedekindDomain CompletedIntegralLattice ProperSpinor
open AdelicOrthogonal
open scoped NumberField RestrictedProduct

variable {K V : Type*} [Field K] [NumberField K]
  [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

/-- Transport a lattice through an ambient orthogonal transformation. -/
def transportLattice (g : ambientGroup Q)
    (L : Lattice (integerSubring K) Q) : Lattice (integerSubring K) Q where
  carrier := L.carrier.map (g.1.toLinearMap.restrictScalars (integerSubring K))
  finite := L.finite.map _
  full := by
    apply top_unique
    intro y _
    have hx : g.1.symm y ∈ Submodule.span K (L.carrier : Set V) := by
      rw [L.full]
      exact Submodule.mem_top
    have hmap : ∀ x ∈ Submodule.span K (L.carrier : Set V),
        g.1 x ∈ Submodule.span K
          ((L.carrier.map (g.1.toLinearMap.restrictScalars (integerSubring K)) :
            Submodule (integerSubring K) V) : Set V) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
          apply Submodule.subset_span
          exact ⟨x, hx, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
      | smul a x _ hx => simpa using Submodule.smul_mem _ a hx
    simpa using hmap (g.1.symm y) hx
  integral := by
    intro y hy
    rcases hy with ⟨x, hx, hxy⟩
    rw [← hxy]
    change Q (g.1 x) ∈ integerSubring K
    rw [g.2 x]
    exact L.integral x hx

omit [NumberField K] in
@[simp] theorem mem_transportLattice (g : ambientGroup Q)
    (L : Lattice (integerSubring K) Q) (x : V) :
    g.1 x ∈ (transportLattice Q g L).carrier ↔ x ∈ L.carrier := by
  constructor
  · rintro ⟨y, hy, heq⟩
    have : y = x := g.1.injective heq
    simpa [this] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

variable [Invertible (2 : K)]

/-- The right stabilizer coset around an adelic comparison.  This is the
finite-place approximation neighborhood which a global diagonal must hit. -/
def InComparisonNeighborhood
    {L M : Lattice (integerSubring K) Q}
    (c : FiniteAdelicProperComparison Q L M)
    (a : FiniteAdelicProperOrthogonal Q L) : Prop :=
  ∀ v : HeightOneSpectrum (integerSubring K),
    (c.toAdelic v)⁻¹ * a v ∈
      properStabilizerWithin (form (integerSubring K) v Q)
        (carrier (integerSubring K) v L.carrier)

/-- The comparison itself lies in its stabilizer coset. -/
theorem comparison_mem_neighborhood
    {L M : Lattice (integerSubring K) Q}
    (c : FiniteAdelicProperComparison Q L M) :
    InComparisonNeighborhood Q c c.toAdelic := by
  intro v
  rw [inv_mul_cancel]
  exact Subgroup.one_mem _

/-- Every adelic element in the comparison coset maps the completed base
carrier onto the completed target carrier at every finite place. -/
theorem maps_carrier_of_mem_comparisonNeighborhood
    {L M : Lattice (integerSubring K) Q}
    (c : FiniteAdelicProperComparison Q L M)
    (a : FiniteAdelicProperOrthogonal Q L)
    (ha : InComparisonNeighborhood Q c a)
    (v : HeightOneSpectrum (integerSubring K))
    (x : Space (V := V) (integerSubring K) v) :
    (a v).1.1 x ∈ carrier (integerSubring K) v M.carrier ↔
      x ∈ carrier (integerSubring K) v L.carrier := by
  let y := ((c.toAdelic v)⁻¹).1.1 ((a v).1.1 x)
  have hc := c.maps_carrier v y
  have hcy : (c.toAdelic v).1.1 y = (a v).1.1 x := by
    simp only [y, Subgroup.coe_inv, LinearEquiv.coe_inv,
      LinearEquiv.apply_symm_apply]
  rw [hcy] at hc
  have hs := ha v
  change ∀ z,
    (((c.toAdelic v)⁻¹ * a v).1.1 z ∈
      carrier (integerSubring K) v L.carrier ↔
      z ∈ carrier (integerSubring K) v L.carrier) at hs
  have hsx := hs x
  change y ∈ carrier (integerSubring K) v L.carrier ↔
      x ∈ carrier (integerSubring K) v L.carrier at hsx
  exact hc.trans hsx

variable [FiniteDimensional K V]

/-- Scalar extension of a global proper orthogonal transformation to one
actual finite completion. -/
def localizeProper (g : properGroup Q)
    (v : HeightOneSpectrum (integerSubring K)) :
    properGroup (form (integerSubring K) v Q) :=
  ⟨⟨equiv (integerSubring K) v g.1.1,
      equiv_form (integerSubring K) v Q Q g.1.1 g.1.2⟩, by
    change LinearEquiv.det
      (g.1.1.baseChange K (LocalField (integerSubring K) v) V V) = 1
    have hg : LinearEquiv.det g.1.1 = 1 := g.2
    rw [LinearEquiv.det_baseChange, hg]
    simp⟩

/-- A global proper transformation stabilizes the completed lattice away
from finitely many finite places. -/
theorem localizeProper_eventually_mem_stabilizer
    (g : properGroup Q) (L : Lattice (integerSubring K) Q) :
    ∀ᶠ v : HeightOneSpectrum (integerSubring K) in cofinite,
      localizeProper Q g v ∈
        properStabilizerWithin (form (integerSubring K) v Q)
          (carrier (integerSubring K) v L.carrier) := by
  filter_upwards [carrier_eventually_eq (integerSubring K) L
    (transportLattice Q g.1 L)] with v heq
  intro x
  have hmap := equiv_carrier (integerSubring K) v L.carrier
    (transportLattice Q g.1 L).carrier g.1.1
    (mem_transportLattice Q g.1 L) x
  change equiv (integerSubring K) v g.1.1 x ∈
      carrier (integerSubring K) v L.carrier ↔
    x ∈ carrier (integerSubring K) v L.carrier
  rwa [← heq] at hmap

/-- The genuine restricted finite adelic diagonal of a global proper
orthogonal transformation. -/
def finiteDiagonal (L : Lattice (integerSubring K) Q) (g : properGroup Q) :
    FiniteAdelicProperOrthogonal Q L :=
  ⟨fun v ↦ localizeProper Q g v,
    localizeProper_eventually_mem_stabilizer Q g L⟩

/-- The exact existence statement which the geometric strong-approximation
step must supply for one adelic comparison. -/
def HasGlobalProperHit
    {L M : Lattice (integerSubring K) Q}
    (c : FiniteAdelicProperComparison Q L M) : Prop :=
  ∃ g : properGroup Q,
    InComparisonNeighborhood Q c (finiteDiagonal Q L g)

/-- Hitting the comparison neighborhood gives the exact completed-carrier
identifications required at every finite place. -/
theorem finiteDiagonal_maps_carrier_of_hit
    {L M : Lattice (integerSubring K) Q}
    (c : FiniteAdelicProperComparison Q L M)
    (g : properGroup Q)
    (hg : InComparisonNeighborhood Q c (finiteDiagonal Q L g))
    (v : HeightOneSpectrum (integerSubring K))
    (x : Space (V := V) (integerSubring K) v) :
    equiv (integerSubring K) v g.1.1 x ∈
        carrier (integerSubring K) v M.carrier ↔
      x ∈ carrier (integerSubring K) v L.carrier :=
  maps_carrier_of_mem_comparisonNeighborhood Q c (finiteDiagonal Q L g) hg v x

/-- A global hit supplies one global proper transformation whose scalar
extensions identify all completed carriers. -/
theorem exists_globalProper_maps_all_completed_carriers_of_hit
    {L M : Lattice (integerSubring K) Q}
    (c : FiniteAdelicProperComparison Q L M)
    (h : HasGlobalProperHit Q c) :
    ∃ g : properGroup Q,
      ∀ (v : HeightOneSpectrum (integerSubring K))
        (x : Space (V := V) (integerSubring K) v),
        equiv (integerSubring K) v g.1.1 x ∈
            carrier (integerSubring K) v M.carrier ↔
          x ∈ carrier (integerSubring K) v L.carrier := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, finiteDiagonal_maps_carrier_of_hit Q c g hg⟩

end NormEuclidean.AdelicApproximation
