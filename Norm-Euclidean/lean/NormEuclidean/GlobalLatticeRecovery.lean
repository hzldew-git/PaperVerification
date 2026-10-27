import NormEuclidean.AdelicApproximation
import NormEuclidean.CompletionDescent
import NormEuclidean.LocalizationLatticeRecovery
import NormEuclidean.ProperGenus

/-!
# Recovering a global lattice from a finite adelic hit

An adelic hit first identifies the completion of the globally transported
base lattice with the completion of the target lattice at every finite place.
This file proves that step and supplies global recovery through the proved
completion-descent theorem. Once the adelic hit principle is available, the
proper and ordinary class-number-one conclusions follow.

The completion-descent proposition is proved below. The adelic hit principle
is still explicit and requires spinor correction and strong approximation;
it is not asserted as a theorem.
-/

noncomputable section

namespace NormEuclidean.AdelicApproximation

open IsDedekindDomain CompletedIntegralLattice ProperSpinor
open AdelicOrthogonal
open scoped NumberField

variable {K V : Type*} [Field K] [NumberField K]
  [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

/-- Equality at every actual finite completion recovers equality of global
lattice carriers. This proposition is proved by completion descent below. -/
def CompletedCarriersRecoverGlobalLattices : Prop :=
  ∀ A B : Lattice (integerSubring K) Q,
    (∀ v : HeightOneSpectrum (integerSubring K),
      carrier (integerSubring K) v A.carrier =
        carrier (integerSubring K) v B.carrier) →
      A.carrier = B.carrier

/-- Equality of completed carriers determines equality of the corresponding
maximal localizations, as in O'Meara's standard local-to-global recovery step. -/
def CompletedCarriersDetermineMaximalLocalizations : Prop :=
  ∀ A B : Lattice (integerSubring K) Q,
    (∀ v : HeightOneSpectrum (integerSubring K),
      carrier (integerSubring K) v A.carrier =
        carrier (integerSubring K) v B.carrier) →
    ∀ (P : Ideal (integerSubring K)) [P.IsMaximal],
      A.carrier.localized' (Localization.AtPrime P) P.primeCompl
          (LocalizedModule.mkLinearMap P.primeCompl V) =
        B.carrier.localized' (Localization.AtPrime P) P.primeCompl
          (LocalizedModule.mkLinearMap P.primeCompl V)

/-- The completion-to-localization comparison, together with the algebraic
maximal-localization theorem, recovers the global lattice carriers. -/
theorem completedCarriersRecoverGlobalLattices_of_maximalLocalizations
    (hlocal : CompletedCarriersDetermineMaximalLocalizations Q) :
    CompletedCarriersRecoverGlobalLattices Q := by
  intro A B hcompleted
  exact LocalizationLatticeRecovery.submodule_eq_of_maximal_localizations_eq
    (hlocal A B hcompleted)

/-- The actual finite completions recover global lattice carriers over the
integer ring of a number field.  This discharges the recovery proposition
using faithfully flat local descent and maximal-localization recovery. -/
theorem completedCarriersRecoverGlobalLattices :
    CompletedCarriersRecoverGlobalLattices Q := by
  intro A B hcompleted
  exact CompletionDescent.submodule_eq_of_completed_carriers_eq (integerSubring K)
    (NumberField.RingOfIntegers.not_isField K) hcompleted

/-- Completed-carrier equality also determines the canonical localized-module
images at every maximal ideal. -/
theorem completedCarriersDetermineMaximalLocalizations :
    CompletedCarriersDetermineMaximalLocalizations Q := by
  intro A B hcompleted P _
  rw [completedCarriersRecoverGlobalLattices Q A B hcompleted]

variable [Invertible (2 : K)] [FiniteDimensional K V]

/-- Every finite adelic proper comparison has a global proper diagonal in its
stabilizer coset. This required hit principle combines spinor correction with
strong approximation. O'Meara 104:4 alone only treats the spinor kernel. -/
def HasFiniteAdelicStrongApproximation : Prop :=
  ∀ (L M : Lattice (integerSubring K) Q)
    (c : FiniteAdelicProperComparison Q L M),
      HasGlobalProperHit Q c

/-- One global hit makes the completion of the globally transported lattice
equal to the target completion at every finite place. -/
theorem completed_transport_eq_of_mem_comparisonNeighborhood
    {L M : Lattice (integerSubring K) Q}
    (c : FiniteAdelicProperComparison Q L M)
    (g : properGroup Q)
    (hg : InComparisonNeighborhood Q c (finiteDiagonal Q L g))
    (v : HeightOneSpectrum (integerSubring K)) :
    carrier (integerSubring K) v (transportLattice Q g.1 L).carrier =
      carrier (integerSubring K) v M.carrier := by
  ext y
  let x := (equiv (integerSubring K) v g.1.1).symm y
  have htransport := equiv_carrier (integerSubring K) v L.carrier
    (transportLattice Q g.1 L).carrier g.1.1
    (mem_transportLattice Q g.1 L) x
  have htarget := finiteDiagonal_maps_carrier_of_hit Q c g hg v x
  have h := htransport.trans htarget.symm
  simpa only [x, LinearEquiv.apply_symm_apply] using h

/-- A global hit therefore supplies a proper global transformation whose
transported lattice has the same carrier as the target at every completion. -/
theorem exists_globalProper_completed_transport_eq_of_hit
    {L M : Lattice (integerSubring K) Q}
    (c : FiniteAdelicProperComparison Q L M)
    (h : HasGlobalProperHit Q c) :
    ∃ g : properGroup Q,
      ∀ v : HeightOneSpectrum (integerSubring K),
        carrier (integerSubring K) v (transportLattice Q g.1 L).carrier =
          carrier (integerSubring K) v M.carrier := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, completed_transport_eq_of_mem_comparisonNeighborhood Q c g hg⟩

/-- If transport by a proper ambient transformation has the target carrier,
the transformation is a proper integral lattice isometry. -/
def latticeIsometryOfTransportCarrierEq
    {L M : Lattice (integerSubring K) Q}
    (g : properGroup Q)
    (hcarrier : (transportLattice Q g.1 L).carrier = M.carrier) :
    LatticeIsometry Q Q L.carrier M.carrier where
  toLinearEquiv := g.1.1
  q_eq := g.1.2
  mem_iff := fun x => by
    have h := mem_transportLattice Q g.1 L x
    rwa [hcarrier] at h

/-- Completion recovery upgrades one finite adelic hit to a proper global
integral isometry. -/
theorem properlyGloballyIsometric_of_hit
    (hrecover : CompletedCarriersRecoverGlobalLattices Q)
    {L M : Lattice (integerSubring K) Q}
    (c : FiniteAdelicProperComparison Q L M)
    (h : HasGlobalProperHit Q c) :
    ProperlyGloballyIsometric Q L M := by
  obtain ⟨g, hg⟩ := exists_globalProper_completed_transport_eq_of_hit Q c h
  have hcarrier : (transportLattice Q g.1 L).carrier = M.carrier :=
    hrecover (transportLattice Q g.1 L) M hg
  exact ⟨latticeIsometryOfTransportCarrierEq Q g hcarrier, g.2⟩

/-- An actual finite adelic global hit gives a proper global integral
isometry, with the completion-descent step supplied by the preceding theorem. -/
theorem properlyGloballyIsometric_of_globalProperHit
    {L M : Lattice (integerSubring K) Q}
    (c : FiniteAdelicProperComparison Q L M)
    (h : HasGlobalProperHit Q c) :
    ProperlyGloballyIsometric Q L M :=
  properlyGloballyIsometric_of_hit Q (completedCarriersRecoverGlobalLattices Q) c h

/-- If ordinary local classes can be made proper, completion recovery and
finite adelic strong approximation imply proper class number one. -/
theorem hasProperLatticeClassNumberOne_of_strongApproximation
    (L : Lattice (integerSubring K) Q)
    (hrecover : CompletedCarriersRecoverGlobalLattices Q)
    (hproper : ∀ M : Lattice (integerSubring K) Q,
      SameGenus Q L M → SameProperGenus Q L M)
    (happrox : HasFiniteAdelicStrongApproximation Q) :
    HasProperLatticeClassNumberOne Q L := by
  rw [hasProperLatticeClassNumberOne_iff]
  intro M hgen
  have hp : SameProperGenus Q L M := hproper M hgen
  let c := comparisonOfSameProperGenus hp
  exact properlyGloballyIsometric_of_hit Q hrecover c (happrox L M c)

/-- For a hyperbolic enlargement, reflections make every ordinary local
comparison proper.  Thus recovery plus Spin strong approximation proves
proper class number one for the enlarged lattice. -/
theorem hyperbolic_hasProperLatticeClassNumberOne
    (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice (integerSubring K) Q)
    (hrecover : CompletedCarriersRecoverGlobalLattices (Hyperbolic.form Q))
    (happrox : HasFiniteAdelicStrongApproximation (Hyperbolic.form Q)) :
    HasProperLatticeClassNumberOne (Hyperbolic.form Q) L.hyperbolic := by
  apply hasProperLatticeClassNumberOne_of_strongApproximation
    (Hyperbolic.form Q) L.hyperbolic hrecover
  · intro M hgen
    exact (hyperbolic_sameGenus_iff_sameProperGenus Q hQ L M).mp hgen
  · exact happrox

/-- The corresponding ordinary class number of the enlarged lattice is one. -/
theorem hyperbolic_hasLatticeClassNumberOne
    (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice (integerSubring K) Q)
    (hrecover : CompletedCarriersRecoverGlobalLattices (Hyperbolic.form Q))
    (happrox : HasFiniteAdelicStrongApproximation (Hyperbolic.form Q)) :
    HasLatticeClassNumberOne (Hyperbolic.form Q) L.hyperbolic :=
  hasLatticeClassNumberOne_of_proper (Hyperbolic.form Q) L.hyperbolic
    (hyperbolic_hasProperLatticeClassNumberOne Q hQ L hrecover happrox)

/-- With completion descent now proved, the remaining adelic hit principle
alone implies proper class number one for the hyperbolic enlargement. The
hit principle still requires the spinor correction and strong-approximation
proof; O'Meara 104:4 only approximates elements of the spinor kernel. -/
theorem hyperbolic_hasProperLatticeClassNumberOne_of_adelicHits
    (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice (integerSubring K) Q)
    (happrox : HasFiniteAdelicStrongApproximation (Hyperbolic.form Q)) :
    HasProperLatticeClassNumberOne (Hyperbolic.form Q) L.hyperbolic :=
  hyperbolic_hasProperLatticeClassNumberOne Q hQ L
    (completedCarriersRecoverGlobalLattices (Hyperbolic.form Q)) happrox

/-- The corresponding ordinary hyperbolic class-number-one conclusion, with
completion descent proved and the adelic hit principle still explicit. -/
theorem hyperbolic_hasLatticeClassNumberOne_of_adelicHits
    (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice (integerSubring K) Q)
    (happrox : HasFiniteAdelicStrongApproximation (Hyperbolic.form Q)) :
    HasLatticeClassNumberOne (Hyperbolic.form Q) L.hyperbolic :=
  hasLatticeClassNumberOne_of_proper (Hyperbolic.form Q) L.hyperbolic
    (hyperbolic_hasProperLatticeClassNumberOne_of_adelicHits Q hQ L happrox)

end NormEuclidean.AdelicApproximation
