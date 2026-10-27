import NormEuclidean.AdelicOrthogonal
import NormEuclidean.AdelicSpinor
import Mathlib.Topology.Algebra.RestrictedProduct.Units

/-!
# Spinor ideles attached to adelic lattice comparisons

A normalized finite adelic proper comparison is the identity away from
finitely many places.  Its local Wall spinor norms therefore have
representatives which are one away from finitely many places.  These
representatives form an actual finite idele, and adjoining the identity at
the infinite places gives an actual full idele.

For a hyperbolic enlargement over a PID, the previously proved scalar
calculation decomposes this comparison idele as a principal idele times an
idele in the lifted local spinor subgroup.  This is the precise scalar input
to the remaining geometric strong-approximation step.
-/

noncomputable section

namespace NormEuclidean.AdelicComparison

open Filter IsDedekindDomain CompletedIntegralLattice ProperSpinor
open scoped NumberField RestrictedProduct

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {Q : QuadraticForm K V}

/-- The local Wall spinor norm of the normalized proper comparison. -/
noncomputable def localSpinorNorm
    (hQ : Q.polarBilin.Nondegenerate)
    {L M : Lattice (integerSubring K) Q} (h : SameProperGenus Q L M)
    (v : HeightOneSpectrum (integerSubring K)) :
    Bong.Dyadic.SquareClass (LocalField (integerSubring K) v) :=
  properAmbientSpinorNormHom (form (integerSubring K) v Q)
    (form_polarBilin_nondegenerate (integerSubring K) v Q hQ)
    (AdelicOrthogonal.localComparison h v)

@[simp] theorem localSpinorNorm_of_carrier_eq
    (hQ : Q.polarBilin.Nondegenerate)
    {L M : Lattice (integerSubring K) Q} (h : SameProperGenus Q L M)
    (v : HeightOneSpectrum (integerSubring K))
    (heq : carrier (integerSubring K) v L.carrier =
      carrier (integerSubring K) v M.carrier) :
    localSpinorNorm hQ h v = 1 := by
  rw [localSpinorNorm, AdelicOrthogonal.localComparison_of_carrier_eq h v heq,
    map_one]

/-- A representative of the local comparison spinor norm, chosen to be one
when the completed carriers are equal. -/
noncomputable def localSpinorRepresentative
    (hQ : Q.polarBilin.Nondegenerate)
    {L M : Lattice (integerSubring K) Q} (h : SameProperGenus Q L M)
    (v : HeightOneSpectrum (integerSubring K)) :
    (LocalField (integerSubring K) v)ˣ := by
  classical
  by_cases heq : carrier (integerSubring K) v L.carrier =
      carrier (integerSubring K) v M.carrier
  · exact 1
  · exact Classical.choose
      (QuotientGroup.mk'_surjective (Subgroup.square (LocalField (integerSubring K) v)ˣ)
        (localSpinorNorm hQ h v))

@[simp] theorem localSpinorRepresentative_of_carrier_eq
    (hQ : Q.polarBilin.Nondegenerate)
    {L M : Lattice (integerSubring K) Q} (h : SameProperGenus Q L M)
    (v : HeightOneSpectrum (integerSubring K))
    (heq : carrier (integerSubring K) v L.carrier =
      carrier (integerSubring K) v M.carrier) :
    localSpinorRepresentative hQ h v = 1 := by
  classical
  simp only [localSpinorRepresentative, dif_pos heq]

/-- The chosen representative has exactly the local comparison's Wall
square class. -/
theorem squareClass_localSpinorRepresentative
    (hQ : Q.polarBilin.Nondegenerate)
    {L M : Lattice (integerSubring K) Q} (h : SameProperGenus Q L M)
    (v : HeightOneSpectrum (integerSubring K)) :
    Bong.Dyadic.squareClass (LocalField (integerSubring K) v)
      (localSpinorRepresentative hQ h v) = localSpinorNorm hQ h v := by
  classical
  by_cases heq : carrier (integerSubring K) v L.carrier =
      carrier (integerSubring K) v M.carrier
  · rw [localSpinorRepresentative_of_carrier_eq hQ h v heq,
      localSpinorNorm_of_carrier_eq hQ h v heq]
    exact map_one _
  · simpa only [Bong.Dyadic.squareClass, localSpinorRepresentative, dif_neg heq] using
      Classical.choose_spec
        (QuotientGroup.mk'_surjective (Subgroup.square (LocalField (integerSubring K) v)ˣ)
          (localSpinorNorm hQ h v))

/-- The local representatives form a genuine finite idele. -/
noncomputable def finiteComparisonSpinorIdele
    (hQ : Q.polarBilin.Nondegenerate)
    {L M : Lattice (integerSubring K) Q} (h : SameProperGenus Q L M) :
    (FiniteAdeleRing (integerSubring K) K)ˣ :=
  RestrictedProduct.mkUnit
    (fun v ↦ localSpinorRepresentative hQ h v)
    (by
      filter_upwards [carrier_eventually_eq (integerSubring K) L M] with v heq
      rw [localSpinorRepresentative_of_carrier_eq hQ h v heq]
      exact Submonoid.one_mem _)

@[simp] theorem componentUnit_finiteComparisonSpinorIdele
    (hQ : Q.polarBilin.Nondegenerate)
    {L M : Lattice (integerSubring K) Q} (h : SameProperGenus Q L M)
    (v : HeightOneSpectrum (integerSubring K)) :
    FiniteIdele.componentUnit v (finiteComparisonSpinorIdele hQ h) =
      localSpinorRepresentative hQ h v := by
  apply Units.ext
  rfl

/-- Componentwise, the actual finite comparison idele records the Wall
spinor norm of the actual local proper isometry. -/
theorem squareClass_component_finiteComparisonSpinorIdele
    (hQ : Q.polarBilin.Nondegenerate)
    {L M : Lattice (integerSubring K) Q} (h : SameProperGenus Q L M)
    (v : HeightOneSpectrum (integerSubring K)) :
    Bong.Dyadic.squareClass (LocalField (integerSubring K) v)
        (FiniteIdele.componentUnit v (finiteComparisonSpinorIdele hQ h)) =
      localSpinorNorm hQ h v := by
  rw [componentUnit_finiteComparisonSpinorIdele,
    squareClass_localSpinorRepresentative]

/-- The normalized comparison spinor idele is one at almost every finite
place. -/
theorem finiteComparisonSpinorIdele_eventually_eq_one
    (hQ : Q.polarBilin.Nondegenerate)
    {L M : Lattice (integerSubring K) Q} (h : SameProperGenus Q L M) :
    ∀ᶠ v : HeightOneSpectrum (integerSubring K) in cofinite,
      FiniteIdele.componentUnit v (finiteComparisonSpinorIdele hQ h) = 1 := by
  filter_upwards [carrier_eventually_eq (integerSubring K) L M] with v heq
  rw [componentUnit_finiteComparisonSpinorIdele,
    localSpinorRepresentative_of_carrier_eq hQ h v heq]

/-- Adjoin the identity at every infinite place to a finite idele. -/
def fullOfFiniteIdele (a : (FiniteAdeleRing (integerSubring K) K)ˣ) :
    (NumberField.AdeleRing (integerSubring K) K)ˣ :=
  MulEquiv.prodUnits.symm (1, a)

omit [Invertible (2 : K)] in
@[simp] theorem finiteProjection_fullOfFiniteIdele
    (a : (FiniteAdeleRing (integerSubring K) K)ˣ) :
    AdelicSpinor.finiteProjection (integerSubring K) (fullOfFiniteIdele a) = a := by
  apply Units.ext
  rfl

omit [Invertible (2 : K)] in
@[simp] theorem infiniteComponentUnit_fullOfFiniteIdele
    (a : (FiniteAdeleRing (integerSubring K) K)ˣ)
    (v : NumberField.InfinitePlace K) :
    AdelicSpinor.infiniteComponentUnit (integerSubring K) v (fullOfFiniteIdele a) = 1 := by
  apply Units.ext
  rfl

/-- The full spinor idele attached to the normalized adelic comparison. -/
noncomputable def fullComparisonSpinorIdele
    (hQ : Q.polarBilin.Nondegenerate)
    {L M : Lattice (integerSubring K) Q} (h : SameProperGenus Q L M) :
    (NumberField.AdeleRing (integerSubring K) K)ˣ :=
  fullOfFiniteIdele (finiteComparisonSpinorIdele hQ h)

/-- Over a PID, the full comparison spinor idele of a hyperbolic enlargement
is a principal idele times an idele in the actual lifted local spinor
subgroup. -/
theorem hyperbolic_fullComparisonSpinorIdele_decomposition
    [IsPrincipalIdealRing (integerSubring K)]
    (P : QuadraticForm K V) (hP : P.polarBilin.Nondegenerate)
    (L : Lattice (integerSubring K) P)
    {M : Lattice (integerSubring K) (Hyperbolic.form P)}
    (h : SameProperGenus (Hyperbolic.form P) L.hyperbolic M) :
    ∃ k : Kˣ, ∃ b : AdelicSpinor.spinorIdeles (integerSubring K)
        (Hyperbolic.form P) (Hyperbolic.form_polarBilin_nondegenerate P hP) L.hyperbolic,
      fullComparisonSpinorIdele (Hyperbolic.form_polarBilin_nondegenerate P hP) h =
        AdelicSpinor.diagonal (integerSubring K) k * b.1 :=
  AdelicSpinor.hyperbolic_exists_diagonal_mul_spinorIdele
    (integerSubring K) P hP L
    (fullComparisonSpinorIdele (Hyperbolic.form_polarBilin_nondegenerate P hP) h)

end NormEuclidean.AdelicComparison
