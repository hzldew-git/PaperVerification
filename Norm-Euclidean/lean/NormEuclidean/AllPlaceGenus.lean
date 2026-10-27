import NormEuclidean.ArchimedeanComparison
import NormEuclidean.FinitePlaceIsometry
import NormEuclidean.LatticeOperations

/-!
# All-place comparison and the fixed-space genus

`AllPlaceLocallyIsometric` compares integral lattices at every finite place
of the full number ring and ambient quadratic spaces at every infinite place.
`SameGenus` restricts this relation to lattices in one fixed quadratic space,
as in the manuscript. No global or stable isometry is part of either definition.
-/
namespace NormEuclidean

namespace LatticeIsometry
variable {K V W U : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup U] [Module K U] {R : Subring K}
  {Q : QuadraticForm K V} {Q' : QuadraticForm K W} {Q'' : QuadraticForm K U}
  {L : Submodule R V} {L' : Submodule R W} {L'' : Submodule R U}

def inverse (e : LatticeIsometry Q Q' L L') : LatticeIsometry Q' Q L' L where
  toLinearEquiv := e.toLinearEquiv.symm
  q_eq z := by simpa using (e.q_eq (e.toLinearEquiv.symm z)).symm
  mem_iff z := by simpa using (e.mem_iff (e.toLinearEquiv.symm z)).symm

def compose (e : LatticeIsometry Q Q' L L') (f : LatticeIsometry Q' Q'' L' L'') :
    LatticeIsometry Q Q'' L L'' where
  toLinearEquiv := e.toLinearEquiv.trans f.toLinearEquiv
  q_eq z := (f.q_eq (e.toLinearEquiv z)).trans (e.q_eq z)
  mem_iff z := (f.mem_iff (e.toLinearEquiv z)).trans (e.mem_iff z)

/-- Extend an integral ambient isometry by the identity of the hyperbolic plane. -/
def hyperbolic (e : LatticeIsometry Q Q' L L') :
    LatticeIsometry (Hyperbolic.form Q) (Hyperbolic.form Q')
      (Hyperbolic.submodule L) (Hyperbolic.submodule L') where
  toLinearEquiv := e.toLinearEquiv.prodCongr (LinearEquiv.refl K (K × K))
  q_eq z := by simpa [Hyperbolic.q] using congrArg (fun t => t + z.2.1 * z.2.2) (e.q_eq z.1)
  mem_iff z := by
    change (e.toLinearEquiv z.1 ∈ L' ∧ z.2.1 ∈ R ∧ z.2.2 ∈ R) ↔
      (z.1 ∈ L ∧ z.2.1 ∈ R ∧ z.2.2 ∈ R)
    rw [e.mem_iff]
end LatticeIsometry

namespace ArchimedeanComparison
variable {K V W U : Type*} [Field K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup U] [Module K U]

/-- Actual ambient quadratic isometries at all real and complex completions. -/
def InfinitelyLocallyIsometric (Q : QuadraticForm K V) (Q' : QuadraticForm K W) : Prop :=
  ∀ v : NumberField.InfinitePlace K, (form v Q).Equivalent (form v Q')

theorem infinitelyLocallyIsometric_refl (Q : QuadraticForm K V) :
    InfinitelyLocallyIsometric Q Q := fun _ => QuadraticMap.Equivalent.refl _

theorem infinitelyLocallyIsometric_symm {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    (h : InfinitelyLocallyIsometric Q Q') : InfinitelyLocallyIsometric Q' Q :=
  fun v => (h v).symm

theorem infinitelyLocallyIsometric_trans {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    {Q'' : QuadraticForm K U} (h : InfinitelyLocallyIsometric Q Q')
    (h' : InfinitelyLocallyIsometric Q' Q'') : InfinitelyLocallyIsometric Q Q'' :=
  fun v => (h v).trans (h' v)

theorem infinitelyLocallyIsometric_of_isometry {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    (e : Q.IsometryEquiv Q') : InfinitelyLocallyIsometric Q Q' := fun v => ⟨isometry v e⟩

def extendHyperbolic {F A B : Type*} [Field F] [AddCommGroup A] [Module F A]
    [AddCommGroup B] [Module F B] {P : QuadraticForm F A} {P' : QuadraticForm F B}
    (e : P.IsometryEquiv P') : (Hyperbolic.form P).IsometryEquiv (Hyperbolic.form P') where
  toLinearEquiv := e.toLinearEquiv.prodCongr (LinearEquiv.refl F (F × F))
  map_app' z := by
    simp [Hyperbolic.q, e.map_app]

theorem infinitelyLocallyIsometric_hyperbolic {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    (h : InfinitelyLocallyIsometric Q Q') :
    InfinitelyLocallyIsometric (Hyperbolic.form Q) (Hyperbolic.form Q') := by
  intro v
  obtain ⟨e⟩ := h v
  exact ⟨((hyperbolicIsometry v Q).trans (extendHyperbolic e)).trans
    (hyperbolicIsometry v Q').symm⟩
end ArchimedeanComparison

open CompletedIntegralLattice ArchimedeanComparison
open scoped NumberField
variable {K V W U : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup U] [Module K U]

/-- All finite integral and infinite ambient comparisons. The finite-place
index is the full ring of integers, never an arbitrary localization. -/
def AllPlaceLocallyIsometric (Q : QuadraticForm K V) (Q' : QuadraticForm K W)
    (L : Submodule (integerSubring K) V) (L' : Submodule (integerSubring K) W) : Prop :=
  FiniteLocallyIsometric (integerSubring K) Q Q' L L' ∧ InfinitelyLocallyIsometric Q Q'

theorem allPlaceLocallyIsometric_refl (Q : QuadraticForm K V)
    (L : Submodule (integerSubring K) V) : AllPlaceLocallyIsometric Q Q L L :=
  ⟨finiteLocallyIsometric_refl _ Q L, infinitelyLocallyIsometric_refl Q⟩

theorem allPlaceLocallyIsometric_symm {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    {L : Submodule (integerSubring K) V} {L' : Submodule (integerSubring K) W}
    (h : AllPlaceLocallyIsometric Q Q' L L') : AllPlaceLocallyIsometric Q' Q L' L :=
  ⟨finiteLocallyIsometric_symm _ h.1, infinitelyLocallyIsometric_symm h.2⟩

theorem allPlaceLocallyIsometric_trans {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    {Q'' : QuadraticForm K U} {L : Submodule (integerSubring K) V}
    {L' : Submodule (integerSubring K) W} {L'' : Submodule (integerSubring K) U}
    (h : AllPlaceLocallyIsometric Q Q' L L') (h' : AllPlaceLocallyIsometric Q' Q'' L' L'') :
    AllPlaceLocallyIsometric Q Q'' L L'' :=
  ⟨finiteLocallyIsometric_trans _ h.1 h'.1, infinitelyLocallyIsometric_trans h.2 h'.2⟩

theorem allPlaceLocallyIsometric_of_isometry {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    {L : Submodule (integerSubring K) V} {L' : Submodule (integerSubring K) W}
    (e : LatticeIsometry Q Q' L L') : AllPlaceLocallyIsometric Q Q' L L' :=
  ⟨finiteLocallyIsometric_of_isometry _ e,
    infinitelyLocallyIsometric_of_isometry ⟨e.toLinearEquiv, e.q_eq⟩⟩

/-- The manuscript genus compares lattices on a fixed ambient quadratic space. -/
def SameGenus (Q : QuadraticForm K V) (L L' : Lattice (integerSubring K) Q) : Prop :=
  AllPlaceLocallyIsometric Q Q L.carrier L'.carrier

/-- In a fixed ambient space the infinite comparisons are automatic, so the
all-place definition agrees with the manuscript's finite-place convention. -/
theorem sameGenus_iff_finite (Q : QuadraticForm K V) (L L' : Lattice (integerSubring K) Q) :
    SameGenus Q L L' ↔ FiniteLocallyIsometric (integerSubring K) Q Q L.carrier L'.carrier :=
  ⟨And.left, fun h => ⟨h, infinitelyLocallyIsometric_refl Q⟩⟩

theorem allPlaceLocallyIsometric_hyperbolic {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    {L : Submodule (integerSubring K) V} {L' : Submodule (integerSubring K) W}
    (h : AllPlaceLocallyIsometric Q Q' L L') :
    AllPlaceLocallyIsometric (Hyperbolic.form Q) (Hyperbolic.form Q')
      (Hyperbolic.submodule L) (Hyperbolic.submodule L') := by
  refine ⟨?_, infinitelyLocallyIsometric_hyperbolic h.2⟩
  intro v
  obtain ⟨e⟩ := h.1 v
  exact ⟨((CompletedIntegralLattice.hyperbolicIsometry _ v Q L).compose e.hyperbolic).compose
    (CompletedIntegralLattice.hyperbolicIsometry _ v Q' L').inverse⟩

/-- The fixed-space genus is an equivalence relation on actual integral lattices. -/
def genusSetoid (Q : QuadraticForm K V) : Setoid (Lattice (integerSubring K) Q) where
  r := SameGenus Q
  iseqv := ⟨fun L => allPlaceLocallyIsometric_refl Q L.carrier,
    fun h => allPlaceLocallyIsometric_symm h,
    fun h h' => allPlaceLocallyIsometric_trans h h'⟩

theorem sameGenus_hyperbolic {Q : QuadraticForm K V}
    {L L' : Lattice (integerSubring K) Q} (h : SameGenus Q L L') :
    SameGenus (Hyperbolic.form Q) L.hyperbolic L'.hyperbolic :=
  allPlaceLocallyIsometric_hyperbolic h

end NormEuclidean
