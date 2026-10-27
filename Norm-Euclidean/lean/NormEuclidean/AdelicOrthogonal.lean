import NormEuclidean.ProperGenus
import NormEuclidean.LatticeCommensurability
import NormEuclidean.ProperSpinor
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Topology.Algebra.RestrictedProduct.Basic

/-!
# Finite adelic proper orthogonal comparisons

The finite adelic proper orthogonal group is the restricted product of the
actual determinant-one orthogonal groups at the finite completions, relative
to the proper integral stabilizers of a fixed lattice.  A proper genus
comparison determines an element of this restricted product.

The restrictedness is proved rather than assumed.  Two finite full lattices
in one ambient vector space have equal completed carriers away from finitely
many height-one primes.  We prove this by clearing a common denominator in
both directions and observing that the denominators are local units away from
their finite sets of prime divisors.
-/

noncomputable section

open scoped RestrictedProduct

namespace NormEuclidean.CompletedIntegralLattice

open Filter IsDedekindDomain

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]

/-- Only finitely many height-one primes contain a fixed nonzero element. -/
theorem finite_primes_containing (a : R) (ha : a ≠ 0) :
    {v : HeightOneSpectrum R | a ∈ v.asIdeal}.Finite := by
  have hspan : (Ideal.span {a} : Ideal R) ≠ 0 := by
    simpa only [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using ha
  have heq : {v : HeightOneSpectrum R | a ∈ v.asIdeal} =
      {v : HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {a}} := by
    ext v
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) v a).symm.trans
      (HeightOneSpectrum.valuation_lt_one_iff_dvd (K := K) v a)
  rw [heq]
  exact Ideal.finite_factors hspan

variable (v : HeightOneSpectrum R)

/-- A global integer avoiding `v` becomes a unit of the completed local
integer ring. -/
theorem isUnit_algebraMap_localRing {a : R} (ha : a ∉ v.asIdeal) :
    IsUnit (⟨algebraMap K (LocalField R v) (a : K),
      algebraMap_mem R v a.property⟩ : LocalRing R v) := by
  rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  change Valued.v ((a : K) : LocalField R v) = 1
  rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (HeightOneSpectrum.valuation_eq_one_iff_notMem v).mpr ha

/-- If a nonzero global scalar sends `L` into `M` and is a unit at `v`,
then the completed carrier of `L` is contained in that of `M`. -/
theorem carrier_le_of_scaled_le_of_not_mem
    (L M : Submodule R V) (a : R)
    (haLM : ∀ x ∈ L, (a : K) • x ∈ M) (ha : a ∉ v.asIdeal) :
    carrier R v L ≤ carrier R v M := by
  apply Submodule.span_le.2
  rintro _ ⟨x, hx, rfl⟩
  let aO : LocalRing R v :=
    ⟨algebraMap K (LocalField R v) (a : K), algebraMap_mem R v a.property⟩
  have huaO : IsUnit aO := isUnit_algebraMap_localRing R v ha
  have hax : inclusion R v ((a : K) • x) ∈ carrier R v M :=
    inclusion_mem R v M (haLM x hx)
  have hinc : inclusion R v ((a : K) • x) = aO • inclusion R v x := by
    simpa only [aO, Subring.smul_def] using inclusion_smul R v a x
  rw [hinc] at hax
  have hscaled := (carrier R v M).smul_mem
    (↑(huaO.unit⁻¹) : LocalRing R v) hax
  change (↑(huaO.unit⁻¹) : LocalRing R v) •
      (aO • inclusion R v x) ∈ carrier R v M at hscaled
  have hcancel : (↑(huaO.unit⁻¹) : LocalRing R v) * aO = 1 := by
    calc
      (↑(huaO.unit⁻¹) : LocalRing R v) * aO =
          (↑(huaO.unit⁻¹) : LocalRing R v) * (↑huaO.unit : LocalRing R v) :=
        congrArg ((↑(huaO.unit⁻¹) : LocalRing R v) * ·) huaO.unit_spec.symm
      _ = 1 := Units.inv_mul huaO.unit
  rw [← mul_smul, hcancel, one_smul] at hscaled
  exact hscaled

variable {Q : QuadraticForm K V}

/-- The completed carriers of two finite full lattices agree at all but
finitely many height-one primes. -/
theorem carrier_eventually_eq (L M : Lattice R Q) :
    ∀ᶠ v : HeightOneSpectrum R in cofinite, carrier R v L.carrier = carrier R v M.carrier := by
  obtain ⟨a, ha0, ha⟩ :=
    exists_lattice_denominator L.carrier M.carrier L.finite M.full
  obtain ⟨b, hb0, hb⟩ :=
    exists_lattice_denominator M.carrier L.carrier M.finite L.full
  have haev : ∀ᶠ v : HeightOneSpectrum R in cofinite, a ∉ v.asIdeal := by
    rw [eventually_cofinite]
    simpa only [not_not] using finite_primes_containing (K := K) R a ha0
  have hbev : ∀ᶠ v : HeightOneSpectrum R in cofinite, b ∉ v.asIdeal := by
    rw [eventually_cofinite]
    simpa only [not_not] using finite_primes_containing (K := K) R b hb0
  filter_upwards [haev, hbev] with v hva hvb
  exact le_antisymm
    (carrier_le_of_scaled_le_of_not_mem R v L.carrier M.carrier a ha hva)
    (carrier_le_of_scaled_le_of_not_mem R v M.carrier L.carrier b hb hvb)

end NormEuclidean.CompletedIntegralLattice

namespace NormEuclidean.AdelicOrthogonal

open Filter IsDedekindDomain CompletedIntegralLattice ProperSpinor
open scoped NumberField

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

/-- The proper integral stabilizer, regarded as a subgroup of the proper
ambient orthogonal group. -/
def properStabilizerWithin {F W : Type*} [Field F] [AddCommGroup W] [Module F W]
    (P : QuadraticForm F W) {S : Subring F} (N : Submodule S W) :
    Subgroup (properGroup P) :=
  (integralStabilizer P N).comap (properGroup P).subtype

@[simp] theorem mem_properStabilizerWithin_iff
    {F W : Type*} [Field F] [AddCommGroup W] [Module F W]
    (P : QuadraticForm F W) {S : Subring F} (N : Submodule S W)
    (g : properGroup P) :
    g ∈ properStabilizerWithin P N ↔ ∀ x, g.1.1 x ∈ N ↔ x ∈ N := Iff.rfl

/-- The finite adelic proper orthogonal group relative to `L`. -/
abbrev FiniteAdelicProperOrthogonal (L : Lattice (integerSubring K) Q) :=
  Πʳ v : HeightOneSpectrum (integerSubring K),
    [properGroup (form (integerSubring K) v Q),
      properStabilizerWithin (form (integerSubring K) v Q)
        (carrier (integerSubring K) v L.carrier)]

/-- A finite adelic proper isometry carrying the completed base lattice to
the completed target lattice at every finite place. -/
structure FiniteAdelicProperComparison
    (L M : Lattice (integerSubring K) Q) where
  toAdelic : FiniteAdelicProperOrthogonal Q L
  maps_carrier : ∀ (v : HeightOneSpectrum (integerSubring K)) x,
    toAdelic v |>.1.1 x ∈ carrier (integerSubring K) v M.carrier ↔
      x ∈ carrier (integerSubring K) v L.carrier

variable {Q}

/-- At one finite place choose the identity comparison whenever the two
completed carriers are equal.  This normalization makes the comparison
eventually equal to one, not merely eventually integral. -/
noncomputable def chosenLocalProperIsometry
    {L M : Lattice (integerSubring K) Q} (h : SameProperGenus Q L M)
    (v : HeightOneSpectrum (integerSubring K)) :
    {e : LatticeIsometry (form (integerSubring K) v Q)
        (form (integerSubring K) v Q)
        (carrier (integerSubring K) v L.carrier)
        (carrier (integerSubring K) v M.carrier) //
      LinearEquiv.det e.toLinearEquiv = 1} := by
  classical
  by_cases heq : carrier (integerSubring K) v L.carrier =
      carrier (integerSubring K) v M.carrier
  · exact ⟨
      { toLinearEquiv := LinearEquiv.refl _ _
        q_eq := fun _ ↦ rfl
        mem_iff := fun x ↦ by
          simp only [LinearEquiv.refl_apply, ← heq] },
      LinearEquiv.det_refl⟩
  · exact ⟨Classical.choose (h v), (Classical.choose_spec (h v))⟩

@[simp] theorem chosenLocalProperIsometry_of_carrier_eq
    {L M : Lattice (integerSubring K) Q} (h : SameProperGenus Q L M)
    (v : HeightOneSpectrum (integerSubring K))
    (heq : carrier (integerSubring K) v L.carrier =
      carrier (integerSubring K) v M.carrier) :
    (chosenLocalProperIsometry h v).1.toLinearEquiv = LinearEquiv.refl _ _ := by
  classical
  simp only [chosenLocalProperIsometry, dif_pos heq]

/-- The chosen proper ambient comparison at one finite place. -/
def properAmbientOfComparison
    {F W : Type*} [Field F] [AddCommGroup W] [Module F W]
    {P : QuadraticForm F W} {S : Subring F} {A B : Submodule S W}
    (e : LatticeIsometry P P A B) (he : LinearEquiv.det e.toLinearEquiv = 1) :
    properGroup P :=
  ⟨⟨e.toLinearEquiv, e.q_eq⟩, he⟩

noncomputable def localComparison
    {L M : Lattice (integerSubring K) Q} (h : SameProperGenus Q L M)
    (v : HeightOneSpectrum (integerSubring K)) :
    properGroup (form (integerSubring K) v Q) :=
  properAmbientOfComparison (chosenLocalProperIsometry h v).1
    (chosenLocalProperIsometry h v).2

theorem localComparison_maps_carrier
    {L M : Lattice (integerSubring K) Q} (h : SameProperGenus Q L M)
    (v : HeightOneSpectrum (integerSubring K)) (x :
      Space (V := V) (integerSubring K) v) :
    (localComparison h v).1.1 x ∈ carrier (integerSubring K) v M.carrier ↔
      x ∈ carrier (integerSubring K) v L.carrier :=
  (chosenLocalProperIsometry h v).1.mem_iff x

@[simp] theorem localComparison_of_carrier_eq
    {L M : Lattice (integerSubring K) Q} (h : SameProperGenus Q L M)
    (v : HeightOneSpectrum (integerSubring K))
    (heq : carrier (integerSubring K) v L.carrier =
      carrier (integerSubring K) v M.carrier) :
    localComparison h v = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  exact chosenLocalProperIsometry_of_carrier_eq h v heq

/-- A proper genus comparison gives an actual restricted finite adelic
proper orthogonal element. -/
noncomputable def comparisonOfSameProperGenus
    {L M : Lattice (integerSubring K) Q} (h : SameProperGenus Q L M) :
    FiniteAdelicProperComparison Q L M where
  toAdelic := ⟨fun v ↦ localComparison h v, by
    filter_upwards [carrier_eventually_eq (integerSubring K) L M] with v heq
    rw [localComparison_of_carrier_eq h v heq]
    exact Subgroup.one_mem _⟩
  maps_carrier := localComparison_maps_carrier h

/-- Conversely, an actual finite adelic proper comparison supplies the
proper local isometries in the definition of the proper genus. -/
theorem sameProperGenus_of_comparison
    {L M : Lattice (integerSubring K) Q}
    (c : FiniteAdelicProperComparison Q L M) : SameProperGenus Q L M := by
  intro v
  let e : LatticeIsometry (form (integerSubring K) v Q)
      (form (integerSubring K) v Q)
      (carrier (integerSubring K) v L.carrier)
      (carrier (integerSubring K) v M.carrier) :=
    { toLinearEquiv := (c.toAdelic v).1.1
      q_eq := (c.toAdelic v).1.2
      mem_iff := c.maps_carrier v }
  exact ⟨e, (c.toAdelic v).2⟩

/-- Proper genus comparison is equivalent to existence of an actual finite
adelic proper comparison. -/
theorem sameProperGenus_iff_nonempty_comparison
    (L M : Lattice (integerSubring K) Q) :
    SameProperGenus Q L M ↔ Nonempty (FiniteAdelicProperComparison Q L M) := by
  constructor
  · exact fun h ↦ ⟨comparisonOfSameProperGenus h⟩
  · rintro ⟨c⟩
    exact sameProperGenus_of_comparison c

/-- The normalized adelic comparison is equal to one at almost every finite
place. -/
theorem comparison_eventually_eq_one
    {L M : Lattice (integerSubring K) Q} (h : SameProperGenus Q L M) :
    ∀ᶠ v : HeightOneSpectrum (integerSubring K) in cofinite,
      (comparisonOfSameProperGenus h).toAdelic v = 1 := by
  filter_upwards [carrier_eventually_eq (integerSubring K) L M] with v heq
  exact localComparison_of_carrier_eq h v heq

end NormEuclidean.AdelicOrthogonal
