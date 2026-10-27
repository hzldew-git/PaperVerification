import NormEuclidean.AllPlaceGenus
import NormEuclidean.QuadraticRescaling

/-!
# Common rescaling at finite and infinite places

Base change carries a scalar `a : K` to its image in every completion.  Since
that image is nonzero when `a` is nonzero, the common factor can be cancelled
from actual finite integral isometries and infinite ambient isometries.

The final fixed-lattice result applies this to two lattices already integral
for the original form.  It does not assert a bijection between all integral
lattices for `Q` and all integral lattices for `a • Q`.
-/

namespace NormEuclidean

namespace CompletedIntegralLattice

open IsDedekindDomain

variable {K V W : Type*} [Field K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]
variable {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
variable {L : Submodule R V} {L' : Submodule R W}

/-- Scalar multiplication commutes with finite-place base change. -/
theorem form_rescale (v : HeightOneSpectrum R) (a : K) (P : QuadraticForm K V) :
    form R v (a • P) =
      (algebraMap K (LocalField R v) a) • form R v P := by
  apply baseChange_ext
  intro x
  simp [form, Algebra.smul_def]

/-- Actual integral isometry at every finite place is invariant under common
nonzero rescaling of the two global forms. -/
theorem finiteLocallyIsometric_rescale_iff (a : K) (ha : a ≠ 0) :
    FiniteLocallyIsometric R (a • Q) (a • Q') L L' ↔
      FiniteLocallyIsometric R Q Q' L L' := by
  constructor
  · intro h v
    obtain ⟨e⟩ := h v
    rw [form_rescale R v a Q, form_rescale R v a Q'] at e
    exact ⟨LatticeIsometry.of_rescale (algebraMap K (LocalField R v) a)
      ((map_ne_zero (algebraMap K (LocalField R v))).2 ha) e⟩
  · intro h v
    obtain ⟨e⟩ := h v
    have e' := LatticeIsometry.rescale (algebraMap K (LocalField R v) a) e
    rw [← form_rescale R v a Q, ← form_rescale R v a Q'] at e'
    exact ⟨e'⟩

end CompletedIntegralLattice

namespace ArchimedeanComparison

variable {K V W : Type*} [Field K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable {Q : QuadraticForm K V} {Q' : QuadraticForm K W}

/-- Scalar multiplication commutes with archimedean base change. -/
theorem form_rescale (v : NumberField.InfinitePlace K) (a : K) (P : QuadraticForm K V) :
    form v (a • P) = (algebraMap K v.Completion a) • form v P := by
  apply baseChange_ext
  intro x
  simp [form, Algebra.smul_def]
  apply NumberField.InfinitePlace.Completion.ext
  simp [UniformSpace.Completion.coe_mul]

/-- Ambient isometry at every infinite place is invariant under common
nonzero rescaling. -/
theorem infinitelyLocallyIsometric_rescale_iff (a : K) (ha : a ≠ 0) :
    InfinitelyLocallyIsometric (a • Q) (a • Q') ↔
      InfinitelyLocallyIsometric Q Q' := by
  constructor
  · intro h v
    have hv := h v
    rw [form_rescale v a Q, form_rescale v a Q'] at hv
    exact (QuadraticIsometry.equivalent_rescale_iff
      (algebraMap K v.Completion a)
      ((map_ne_zero (algebraMap K v.Completion)).2 ha)).mp hv
  · intro h v
    have hv := h v
    rw [form_rescale v a Q, form_rescale v a Q']
    exact (QuadraticIsometry.equivalent_rescale_iff
      (algebraMap K v.Completion a)
      ((map_ne_zero (algebraMap K v.Completion)).2 ha)).mpr hv

end ArchimedeanComparison

open CompletedIntegralLattice ArchimedeanComparison
open scoped NumberField

variable {K V W : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
variable {L : Submodule (integerSubring K) V}
variable {L' : Submodule (integerSubring K) W}

/-- All-place local isometry is invariant under common nonzero rescaling. -/
theorem allPlaceLocallyIsometric_rescale_iff (a : K) (ha : a ≠ 0) :
    AllPlaceLocallyIsometric (a • Q) (a • Q') L L' ↔
      AllPlaceLocallyIsometric Q Q' L L' := by
  constructor
  · intro h
    exact ⟨(finiteLocallyIsometric_rescale_iff (integerSubring K) a ha).mp h.1,
      (infinitelyLocallyIsometric_rescale_iff a ha).mp h.2⟩
  · intro h
    exact ⟨(finiteLocallyIsometric_rescale_iff (integerSubring K) a ha).mpr h.1,
      (infinitelyLocallyIsometric_rescale_iff a ha).mpr h.2⟩

/-- For two lattices already integral for `Q`, passing both to the same
integrally rescaled form preserves their fixed-space genus relation. -/
theorem sameGenus_rescale_iff {Q : QuadraticForm K V}
    (M M' : Lattice (integerSubring K) Q) (a : integerSubring K)
    (ha : (a : K) ≠ 0) :
    SameGenus ((a : K) • Q) (M.rescale a) (M'.rescale a) ↔
      SameGenus Q M M' :=
  allPlaceLocallyIsometric_rescale_iff (a : K) ha

/-- Doubling both integral lattices preserves their fixed-space genus
relation. -/
theorem sameGenus_two_rescale_iff {Q : QuadraticForm K V}
    (M M' : Lattice (integerSubring K) Q) :
    SameGenus ((2 : K) • Q)
        (M.rescale (2 : integerSubring K)) (M'.rescale (2 : integerSubring K)) ↔
      SameGenus Q M M' :=
  sameGenus_rescale_iff M M' (2 : integerSubring K) (by norm_num)

end NormEuclidean
