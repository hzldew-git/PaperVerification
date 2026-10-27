import NormEuclidean.AllPlaceGenus
import NormEuclidean.LocalHyperbolicUniversality

/-!
# Exact universality at all places

The finite condition is equality of the quadratic-value image with the
completed valuation ring, not merely representation of integral scalars.
The infinite condition is surjectivity onto each actual completion.
This supplies the universality hypothesis for the future arithmetic theorem;
it does not assert that theorem or proper-class uniqueness.
-/
namespace NormEuclidean
open scoped NumberField
variable {K V W : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Exact finite value images and representation of all archimedean scalars. -/
def AllPlaceUniversal (Q : QuadraticForm K V) (L : Lattice (integerSubring K) Q) : Prop :=
  (∀ v : IsDedekindDomain.HeightOneSpectrum (integerSubring K),
    CompletedIntegralLattice.form (integerSubring K) v Q ''
      (CompletedIntegralLattice.carrier (integerSubring K) v L.carrier : Set _) =
      (CompletedIntegralLattice.LocalRing (integerSubring K) v : Set _)) ∧
  ∀ (v : NumberField.InfinitePlace K) (a : v.Completion),
    ∃ z : ArchimedeanComparison.Space (V := V) v, ArchimedeanComparison.form v Q z = a

/-- The hyperbolic extension of every actual integral lattice is universal
at all places, including dyadic, real, and complex places. -/
theorem hyperbolic_allPlaceUniversal (Q : QuadraticForm K V)
    (L : Lattice (integerSubring K) Q) : AllPlaceUniversal (Hyperbolic.form Q) L.hyperbolic :=
  ⟨fun v => CompletedIntegralLattice.lattice_hyperbolic_value_image_eq_localRing
      (integerSubring K) v Q L,
    fun v a => ArchimedeanComparison.hyperbolic_universal v Q a⟩

/-- Actual all-place isometries preserve the exact universality conditions. -/
theorem allPlaceUniversal_of_isometric {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    {L : Lattice (integerSubring K) Q} {L' : Lattice (integerSubring K) Q'}
    (h : AllPlaceLocallyIsometric Q Q' L.carrier L'.carrier) (hU : AllPlaceUniversal Q L) :
    AllPlaceUniversal Q' L' := by
  constructor
  · intro v
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact CompletedIntegralLattice.carrier_integral _ v Q' L'.carrier L'.integral z hz
    · intro a ha
      have ha' : a ∈ CompletedIntegralLattice.form (integerSubring K) v Q ''
          (CompletedIntegralLattice.carrier (integerSubring K) v L.carrier : Set _) := by
        rw [hU.1 v]
        exact ha
      obtain ⟨z, hz, hza⟩ := ha'
      obtain ⟨e⟩ := h.1 v
      exact ⟨e.toLinearEquiv z, (e.mem_iff z).2 hz, (e.q_eq z).trans hza⟩
  · intro v a
    obtain ⟨z, hz⟩ := hU.2 v a
    obtain ⟨e⟩ := h.2 v
    exact ⟨e z, (e.map_app z).trans hz⟩

theorem sameGenus_hyperbolic_universal {Q : QuadraticForm K V}
    (L : Lattice (integerSubring K) Q)
    {M : Lattice (integerSubring K) (Hyperbolic.form Q)}
    (h : SameGenus (Hyperbolic.form Q) L.hyperbolic M) :
    AllPlaceUniversal (Hyperbolic.form Q) M :=
  allPlaceUniversal_of_isometric h (hyperbolic_allPlaceUniversal Q L)

end NormEuclidean
