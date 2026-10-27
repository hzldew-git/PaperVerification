import NormEuclidean.CompletedHyperbolic
import NormEuclidean.FinitePlaceIsometry
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Genuine hyperbolic universality at finite completions

For every value in an actual completed valuation ring, the completed
hyperbolic lattice contains an integral vector representing that value.
The witness is transported from `(0,a,1)` through `hyperbolicIsometry`.
In particular the proof makes no assumption of local universality and
requires no inverse of two in the completed valuation ring.

The same explicit representation transports across actual finite local
integral isometries. Ambient dimensions are preserved by completion, by
`Module.finrank_baseChange`.
-/

open IsDedekindDomain

namespace NormEuclidean.CompletedIntegralLattice

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

/-- Completion preserves the dimension of the ambient quadratic space.
No freeness hypothesis on an integral lattice is involved. -/
theorem finrank_space :
    Module.finrank (LocalField R v) (Space (V := V) R v) = Module.finrank K V := by
  exact Module.finrank_baseChange

/-- The completed hyperbolic extension has two more ambient dimensions. -/
theorem finrank_hyperbolic_space [FiniteDimensional K V] :
    Module.finrank (LocalField R v) (Space (V := Hyperbolic K V) R v) =
      Module.finrank K V + 2 := by
  rw [finrank_space]
  simp [Hyperbolic, Module.finrank_prod]

variable [Invertible (2 : K)]

/-- An explicit completed vector representing `a`, obtained through the
actual integral isometry commuting completion with hyperbolic extension. -/
noncomputable def hyperbolicRepresentation (Q : QuadraticForm K V) (L : Submodule R V)
    (a : LocalRing R v) : Space (V := Hyperbolic K V) R v :=
  (hyperbolicIsometry R v Q L).toLinearEquiv.symm (0, (a : LocalField R v), 1)

/-- The explicit representing vector is integral over the completed valuation ring. -/
theorem hyperbolicRepresentation_mem (Q : QuadraticForm K V) (L : Submodule R V)
    (a : LocalRing R v) :
    hyperbolicRepresentation R v Q L a ∈ carrier R v (Hyperbolic.submodule L) := by
  apply ((hyperbolicIsometry R v Q L).mem_iff _).1
  simpa only [hyperbolicRepresentation, LinearEquiv.apply_symm_apply] using
    (show (0, (a : LocalField R v), 1) ∈ Hyperbolic.submodule (carrier R v L) from
      ⟨(carrier R v L).zero_mem, a.property, (LocalRing R v).one_mem⟩)

/-- Its completed quadratic value is exactly the prescribed local integer. -/
@[simp] theorem form_hyperbolicRepresentation (Q : QuadraticForm K V) (L : Submodule R V)
    (a : LocalRing R v) :
    form R v (Hyperbolic.form Q) (hyperbolicRepresentation R v Q L a) =
      (a : LocalField R v) := by
  rw [← (hyperbolicIsometry R v Q L).q_eq]
  simp [hyperbolicRepresentation, Hyperbolic.q]

/-- Every completed valuation-ring value is represented by an actual integral
vector in the completion of the global hyperbolic extension, including at dyadic places. -/
theorem hyperbolic_represents (Q : QuadraticForm K V) (L : Submodule R V)
    (a : LocalRing R v) :
    ∃ z ∈ carrier R v (Hyperbolic.submodule L),
      form R v (Hyperbolic.form Q) z = (a : LocalField R v) :=
  ⟨hyperbolicRepresentation R v Q L a, hyperbolicRepresentation_mem R v Q L a,
    form_hyperbolicRepresentation R v Q L a⟩

/-- Representation of every value in an actual completed valuation ring by
an actual vector of the completed carrier. On an arbitrary submodule this
is a representation-only predicate: integrality must be supplied separately
to conclude that the value image equals the completed valuation ring. -/
def FiniteLocallyUniversal (Q : QuadraticForm K V) (L : Submodule R V) : Prop :=
  ∀ (v : HeightOneSpectrum R) (a : LocalRing R v),
    ∃ z ∈ carrier R v L, form R v Q z = (a : LocalField R v)

/-- The completed standard hyperbolic extension is universal at every finite place. -/
theorem hyperbolic_finiteLocallyUniversal (Q : QuadraticForm K V) (L : Submodule R V) :
    FiniteLocallyUniversal R (Hyperbolic.form Q) (Hyperbolic.submodule L) :=
  fun v a => hyperbolic_represents R v Q L a

/-- Actual finite integral isometries carry representing integral vectors to
representing integral vectors. -/
theorem finiteLocallyUniversal_of_finiteLocallyIsometric
    {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    {L : Submodule R V} {L' : Submodule R W}
    (h : FiniteLocallyIsometric R Q Q' L L') (hQ : FiniteLocallyUniversal R Q L) :
    FiniteLocallyUniversal R Q' L' := by
  intro v a
  obtain ⟨e⟩ := h v
  obtain ⟨z, hz, hza⟩ := hQ v a
  exact ⟨e.toLinearEquiv z, (e.mem_iff z).2 hz, (e.q_eq z).trans hza⟩

/-- Universality for any lattice actually locally isometric to a global
hyperbolic extension; no local-universality premise is supplied. -/
theorem finiteLocallyUniversal_of_hyperbolic_finiteLocallyIsometric
    (Q : QuadraticForm K V) (L : Submodule R V)
    {Q' : QuadraticForm K W} {L' : Submodule R W}
    (h : FiniteLocallyIsometric R (Hyperbolic.form Q) Q' (Hyperbolic.submodule L) L') :
    FiniteLocallyUniversal R Q' L' :=
  finiteLocallyUniversal_of_finiteLocallyIsometric R h
    (hyperbolic_finiteLocallyUniversal R Q L)

/-- Even one actual completed isometry identifies the original ambient dimensions. -/
theorem finrank_eq_of_completed_isometry
    {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    {L : Submodule R V} {L' : Submodule R W}
    (e : LatticeIsometry (form R v Q) (form R v Q') (carrier R v L) (carrier R v L')) :
    Module.finrank K V = Module.finrank K W := by
  rw [← finrank_space R v, ← finrank_space (V := W) R v]
  exact e.toLinearEquiv.finrank_eq

/-- Under global integrality, finite local representation of all local integers
is exactly the assertion that the completed value image is the local ring. -/
theorem value_image_eq_localRing_of_finiteLocallyUniversal
    (Q : QuadraticForm K V) (L : Submodule R V)
    (hQ : ∀ x ∈ L, Q x ∈ R) (hU : FiniteLocallyUniversal R Q L) :
    form R v Q '' (carrier R v L : Set (Space (V := V) R v)) =
      (LocalRing R v : Set (LocalField R v)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact carrier_integral R v Q L hQ z hz
  · intro a ha
    obtain ⟨z, hz, hza⟩ := hU v ⟨a, ha⟩
    exact ⟨z, hz, hza⟩

/-- The value image of a completed integral hyperbolic extension is precisely
the completed valuation ring, at every finite place, including dyadic places. -/
theorem hyperbolic_value_image_eq_localRing (Q : QuadraticForm K V) (L : Submodule R V)
    (hQ : ∀ x ∈ L, Q x ∈ R) :
    form R v (Hyperbolic.form Q) ''
        (carrier R v (Hyperbolic.submodule L) : Set (Space (V := Hyperbolic K V) R v)) =
      (LocalRing R v : Set (LocalField R v)) :=
  value_image_eq_localRing_of_finiteLocallyUniversal R v
    (Hyperbolic.form Q) (Hyperbolic.submodule L)
    (Hyperbolic.submodule_integral Q L hQ) (hyperbolic_finiteLocallyUniversal R Q L)

/-- Bundled integral lattices have the exact finite-place hyperbolic value image. -/
theorem lattice_hyperbolic_value_image_eq_localRing (Q : QuadraticForm K V) (L : Lattice R Q) :
    form R v (Hyperbolic.form Q) ''
        (carrier R v (Hyperbolic.submodule L.carrier) :
          Set (Space (V := Hyperbolic K V) R v)) =
      (LocalRing R v : Set (LocalField R v)) :=
  hyperbolic_value_image_eq_localRing R v Q L.carrier L.integral

end NormEuclidean.CompletedIntegralLattice
