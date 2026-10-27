import NormEuclidean.ChapterX.ProperWeakApproximation
import NormEuclidean.ChapterX.CompletedTopology

/-!
# Normalizing actual proper-genus representatives at prescribed places

Open integral stabilizer cosets and proved proper weak approximation construct
the global transport in O'Meara 102:4. The completions agree exactly at the
target places. No strong approximation or outside-set stabilization is used.
-/

noncomputable section

namespace NormEuclidean.GenusNormalization

open ProperSpinor AdelicOrthogonal AdelicApproximation CompletedIntegralLattice
open ProperWeakApproximation OrthogonalTopology IsDedekindDomain Filter Topology
open scoped NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V)

omit [FiniteDimensional K V] in
theorem sameProperGenus_symm {L M : Lattice (integerSubring K) Q}
    (h : SameProperGenus Q L M) : SameProperGenus Q M L := by
  intro v
  obtain ⟨e, he⟩ := h v
  refine ⟨e.inverse, ?_⟩
  change LinearEquiv.det e.toLinearEquiv.symm = 1
  rw [LinearEquiv.det_symm, map_inv, he, inv_one]

omit [NumberField K] [Invertible (2 : K)] [FiniteDimensional K V] in
/-- Global proper transport is an actual integral isometry of its two lattices. -/
theorem properlyGloballyIsometric_transport (M : Lattice (integerSubring K) Q)
    (g : properGroup Q) : ProperlyGloballyIsometric Q M (transportLattice Q g.1 M) :=
  ⟨{ toLinearEquiv := g.1.1, q_eq := g.1.2,
      mem_iff := mem_transportLattice Q g.1 M }, g.2⟩

omit [FiniteDimensional K V] in
/-- One local stabilizer coset gives the exact completed-carrier map. -/
theorem maps_carrier_of_local_coset {L M : Lattice (integerSubring K) Q}
    (c : FiniteAdelicProperComparison Q M L) (v : HeightOneSpectrum (integerSubring K))
    (b : properGroup (form (integerSubring K) v Q))
    (hb : (c.toAdelic v)⁻¹ * b ∈ properStabilizerWithin (form (integerSubring K) v Q)
      (carrier (integerSubring K) v M.carrier))
    (x : Space (V := V) (integerSubring K) v) :
    b.1.1 x ∈ carrier (integerSubring K) v L.carrier ↔
      x ∈ carrier (integerSubring K) v M.carrier := by
  let y := ((c.toAdelic v)⁻¹ * b).1.1 x
  have hc := c.maps_carrier v y
  have heq : (c.toAdelic v).1.1 y = b.1.1 x := by
    simp only [y, Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
  rw [heq] at hc
  exact hc.trans (hb x)

/-- A global proper isometry normalizes a proper-genus member at every
specified finite completion. Both the transport and equality are conclusions. -/
theorem exists_normalized_lattice (hQ : Q.polarBilin.Nondegenerate)
    (hpos : 0 < Module.finrank K V) (L M : Lattice (integerSubring K) Q)
    (hM : SameProperGenus Q L M) (T : Finset (HeightOneSpectrum (integerSubring K))) :
    ∃ N : Lattice (integerSubring K) Q, ProperlyGloballyIsometric Q M N ∧
      ∀ v ∈ T, carrier (integerSubring K) v N.carrier = carrier (integerSubring K) v L.carrier := by
  let c := comparisonOfSameProperGenus (sameProperGenus_symm Q hM)
  let a := fun v : T ↦ c.toAdelic v.1
  let U := fun v : T ↦ {g : properGroup (form (integerSubring K) v.1 Q) |
    (a v)⁻¹ * g ∈ properStabilizerWithin (form (integerSubring K) v.1 Q)
      (carrier (integerSubring K) v.1 M.carrier)}
  have hU : ∀ v : T, U v ∈ 𝓝 (a v) := fun v ↦
    completedProperCoset_mem_nhds (integerSubring K) v.1 Q M (a v)
  obtain ⟨g, hg⟩ := exists_global_proper_weak_approximation Q hQ hpos T a U hU
  refine ⟨transportLattice Q g.1 M, properlyGloballyIsometric_transport Q M g, ?_⟩
  intro v hv
  have hmap := maps_carrier_of_local_coset Q c v (localizeProper Q g v) (hg ⟨v, hv⟩)
  ext y
  let x := (localizeProper Q g v).1.1.symm y
  have ht := equiv_carrier (integerSubring K) v M.carrier
    (transportLattice Q g.1 M).carrier g.1.1 (mem_transportLattice Q g.1 M) x
  have ht' : y ∈ carrier (integerSubring K) v (transportLattice Q g.1 M).carrier ↔
      x ∈ carrier (integerSubring K) v M.carrier := by
    change (localizeProper Q g v).1.1 x ∈ _ ↔ _ at ht
    simpa only [x, LinearEquiv.apply_symm_apply] using ht
  have hl : y ∈ carrier (integerSubring K) v L.carrier ↔
      x ∈ carrier (integerSubring K) v M.carrier := by
    simpa only [x, LinearEquiv.apply_symm_apply] using hmap x
  exact ht'.trans hl.symm

/-- An actual finite family of proper-genus members can be normalized
simultaneously, with one actual proper integral isometry for each member. -/
theorem exists_normalized_family {ι : Type*} [Finite ι]
    (hQ : Q.polarBilin.Nondegenerate) (hpos : 0 < Module.finrank K V)
    (L : Lattice (integerSubring K) Q) (M : ι → Lattice (integerSubring K) Q)
    (hM : ∀ i, SameProperGenus Q L (M i)) (T : Finset (HeightOneSpectrum (integerSubring K))) :
    ∃ N : ι → Lattice (integerSubring K) Q,
      (∀ i, ProperlyGloballyIsometric Q (M i) (N i)) ∧
      ∀ i v, v ∈ T → carrier (integerSubring K) v (N i).carrier =
        carrier (integerSubring K) v L.carrier := by
  choose N hN hlocal using fun i ↦ exists_normalized_lattice Q hQ hpos L (M i) (hM i) T
  exact ⟨N, hN, hlocal⟩

end NormEuclidean.GenusNormalization
