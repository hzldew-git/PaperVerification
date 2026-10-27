import NormEuclidean.ChapterX.OrthogonalTopology
import NormEuclidean.AdelicSpinorKernel
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Open stabilizers at actual finite completions

O'Meara 101:4(ii)-(iii) is connected to the project's completed lattice
carriers and its existing proper stabilizer cosets. The topology is the
finite-dimensional module topology over the actual valued completion.
The integral coefficient ring is open by its valuation, including dyadic
places. No basis of the global integral lattice is assumed.
-/

noncomputable section

namespace NormEuclidean.OrthogonalTopology

open Filter Topology ProperSpinor AdelicOrthogonal CompletedIntegralLattice IsDedekindDomain
open scoped NormEuclidean.OrthogonalTopology

section Stabilizers

variable {F E : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [AddCommGroup E] [Module F E] [Module.Finite F E]
  [TopologicalSpace E] [IsModuleTopology F E]

/-- The actual integral stabilizer remains open inside the proper group. -/
theorem isOpen_properStabilizerWithin (Q : QuadraticForm F E) {R : Subring F}
    (L : Submodule R E) (hfg : L.FG) (hopen : IsOpen (L : Set E)) :
    IsOpen (properStabilizerWithin Q L : Set (properGroup Q)) :=
  (isOpen_integralStabilizer Q L hfg hopen).preimage continuous_subtype_val

/-- O'Meara 101:4(iii): comparisons with the same lattice image form an open coset. -/
theorem isOpen_properStabilizerCoset (Q : QuadraticForm F E) {R : Subring F}
    (L : Submodule R E) (hfg : L.FG) (hopen : IsOpen (L : Set E)) (g : properGroup Q) :
    IsOpen {a : properGroup Q | g⁻¹ * a ∈ properStabilizerWithin Q L} :=
  (isOpen_properStabilizerWithin Q L hfg hopen).preimage (continuous_const.mul continuous_id)

/-- Sufficiently close actual proper transformations hit the exact integral coset. -/
theorem properStabilizerCoset_mem_nhds (Q : QuadraticForm F E) {R : Subring F}
    (L : Submodule R E) (hfg : L.FG) (hopen : IsOpen (L : Set E)) (g : properGroup Q) :
    {a : properGroup Q | g⁻¹ * a ∈ properStabilizerWithin Q L} ∈ 𝓝 g :=
  (isOpen_properStabilizerCoset Q L hfg hopen g).mem_nhds (by simp)

end Stabilizers

section Completions

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

scoped instance completionSpaceTopology : TopologicalSpace (Space (V := V) R v) :=
  moduleTopology (LocalField R v) (Space (V := V) R v)

scoped instance completionSpaceTopologicalAddGroup :
    IsTopologicalAddGroup (Space (V := V) R v) :=
  IsModuleTopology.topologicalAddGroup (LocalField R v) (Space (V := V) R v)

/-- The actual completed integer ring is open in the actual local field. -/
theorem isOpen_localRing : IsOpen (LocalRing R v : Set (LocalField R v)) :=
  Valued.isOpen_valuationSubring (LocalField R v)

variable [FiniteDimensional K V]

/-- The finite completed carrier of a full global lattice is an open subset
of its actual tensor-product ambient space. -/
theorem isOpen_completedCarrier (Q : QuadraticForm K V) (L : Lattice R Q) :
    IsOpen (carrier R v L.carrier : Set (Space (V := V) R v)) :=
  isOpen_of_full (LocalRing R v) (isOpen_localRing R v) (carrier R v L.carrier)
    (carrier_full R v L.carrier L.full)

variable [Invertible (2 : K)]

/-- O'Meara 101:2 for the actual completed reflection, including dyadic places. -/
theorem continuous_completedReflection (Q : QuadraticForm K V) :
    Continuous (fun x : {x : Space (V := V) R v // form R v Q x ≠ 0} ↦
      IntegralReflection.linearEquiv (form R v Q) x.1 x.2) := by
  letI : Invertible (2 : LocalField R v) := by
    exact (Invertible.map (algebraMap K (LocalField R v)) 2).copy 2 (map_ofNat _ _).symm
  exact continuous_reflection (form R v Q)

/-- O'Meara 101:4(ii) for the completed carrier and the existing proper group. -/
theorem isOpen_completedProperStabilizer (Q : QuadraticForm K V) (L : Lattice R Q) :
    IsOpen (properStabilizerWithin (form R v Q) (carrier R v L.carrier) :
      Set (properGroup (form R v Q))) :=
  isOpen_properStabilizerWithin (form R v Q) (carrier R v L.carrier)
    (carrier_fg R v L.carrier L.finite) (isOpen_completedCarrier R v Q L)

/-- The exact local coset used in the adelic hit condition is a neighborhood
of each given local proper comparison. -/
theorem completedProperCoset_mem_nhds (Q : QuadraticForm K V) (L : Lattice R Q)
    (g : properGroup (form R v Q)) :
    {a : properGroup (form R v Q) |
      g⁻¹ * a ∈ properStabilizerWithin (form R v Q) (carrier R v L.carrier)} ∈ 𝓝 g :=
  properStabilizerCoset_mem_nhds (form R v Q) (carrier R v L.carrier)
    (carrier_fg R v L.carrier L.finite) (isOpen_completedCarrier R v Q L) g

end Completions

section Adeles

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The actual finite adelic integral stabilizer is open in the restricted
product topology, by the proved local stabilizer openness at every place. -/
theorem isOpen_integralAdelic (Q : QuadraticForm K V)
    (L : Lattice (integerSubring K) Q) :
    IsOpen {s : FiniteAdelicProperOrthogonal Q L | AdelicSpinorKernel.IsIntegralAdelic Q L s} :=
  RestrictedProduct.isOpen_forall_mem
    (fun v ↦ isOpen_completedProperStabilizer (integerSubring K) v Q L)

set_option maxHeartbeats 800000 in
/-- The exact finite adelic stabilizer coset in the hit condition is open. -/
theorem isOpen_adelicStabilizerCoset (Q : QuadraticForm K V)
    (L : Lattice (integerSubring K) Q) (a : FiniteAdelicProperOrthogonal Q L) :
    IsOpen {b : FiniteAdelicProperOrthogonal Q L |
      AdelicSpinorKernel.InStabilizerCoset Q L a b} := by
  letI : Fact (∀ v : HeightOneSpectrum (integerSubring K),
      IsOpen (properStabilizerWithin (form (integerSubring K) v Q)
        (carrier (integerSubring K) v L.carrier) :
          Set (properGroup (form (integerSubring K) v Q)))) :=
    ⟨fun v ↦ isOpen_completedProperStabilizer (integerSubring K) v Q L⟩
  have hc : Continuous (fun b : FiniteAdelicProperOrthogonal Q L ↦ a⁻¹ * b) :=
    continuous_const.mul continuous_id
  have heq : {b : FiniteAdelicProperOrthogonal Q L |
      AdelicSpinorKernel.InStabilizerCoset Q L a b} =
      (fun b : FiniteAdelicProperOrthogonal Q L ↦ a⁻¹ * b) ⁻¹'
        {s | AdelicSpinorKernel.IsIntegralAdelic Q L s} := by
    ext b
    rfl
  rw [heq]
  exact (isOpen_integralAdelic Q L).preimage hc

/-- The open adelic coset contains the comparison itself. Density must still
be proved before a global diagonal hit can be obtained from this neighborhood. -/
theorem adelicStabilizerCoset_mem_nhds (Q : QuadraticForm K V)
    (L : Lattice (integerSubring K) Q) (a : FiniteAdelicProperOrthogonal Q L) :
    {b : FiniteAdelicProperOrthogonal Q L |
      AdelicSpinorKernel.InStabilizerCoset Q L a b} ∈ 𝓝 a :=
  (isOpen_adelicStabilizerCoset Q L a).mem_nhds (by
    intro v
    change (a v)⁻¹ * a v ∈ _
    simpa only [inv_mul_cancel] using
      (properStabilizerWithin (form (integerSubring K) v Q)
        (carrier (integerSubring K) v L.carrier)).one_mem)

end Adeles

end NormEuclidean.OrthogonalTopology
