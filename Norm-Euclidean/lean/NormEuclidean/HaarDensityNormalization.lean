import NormEuclidean.UniformCongruenceMeasure
import NormEuclidean.GramScaling
import Bong.Dyadic.NumberFieldCompletion
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Actual additive Haar volume normalization for binary Gram congruences

The compact completed integer ring carries its constructed Haar
probability measure. Every ideal is measurable by its principal compact
image. The literal matrix congruence locus has Haar volume equal to its
finite solution count divided by q^(4N), giving the proved q^(3N)/2
conversion to the project's raw Gram density.
-/

noncomputable section

namespace NormEuclidean.HaarDensityNormalization

open MeasureTheory MeasureTheory.Measure TopologicalSpace IsLocalRing Set
open scoped ENNReal

section CompactGroup

variable (X : Type*) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The actual additive Haar measure, normalized on the whole compact group. -/
def normalizedHaar : Measure X :=
  addHaarMeasure (⟨⟨univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts X)

/-- The chosen normalization has total mass exactly one. -/
theorem normalizedHaar_univ : normalizedHaar X univ = 1 := addHaarMeasure_self

instance normalizedHaarProbability : IsProbabilityMeasure (normalizedHaar X) :=
  ⟨normalizedHaar_univ X⟩

instance normalizedHaarInvariant : IsAddLeftInvariant (normalizedHaar X) := by
  unfold normalizedHaar
  infer_instance

end CompactGroup

section Ring

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Finite (ResidueField R)] [TopologicalSpace R] [IsTopologicalRing R]
  [T2Space R] [CompactSpace R] [SecondCountableTopology R]
  [MeasurableSpace R] [BorelSpace R]

local instance matrixMeasurable : MeasurableSpace (Matrix (Fin 2) (Fin 2) R) :=
  inferInstanceAs (MeasurableSpace (Fin 2 → Fin 2 → R))

local instance matrixCompact : CompactSpace (Matrix (Fin 2) (Fin 2) R) :=
  inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → R))

local instance matrixBorel : BorelSpace (Matrix (Fin 2) (Fin 2) R) :=
  inferInstanceAs (BorelSpace (Fin 2 → Fin 2 → R))

local instance matrixMeasurableAdd : MeasurableAdd (Matrix (Fin 2) (Fin 2) R) :=
  inferInstanceAs (MeasurableAdd (Fin 2 → Fin 2 → R))

/-- Every actual DVR ideal is a measurable compact scalar image. -/
theorem ideal_measurable (I : Ideal R) : MeasurableSet (I : Set R) := by
  let s := Submodule.IsPrincipal.generator I
  have hs : Ideal.span ({s} : Set R) = I := Ideal.span_singleton_generator I
  have he : (I : Set R) = range (fun x : R ↦ s * x) := by
    ext x
    change x ∈ I ↔ ∃ y, s * y = x
    rw [← hs, Ideal.mem_span_singleton]
    exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩, fun ⟨y, hy⟩ ↦ ⟨y, hy.symm⟩⟩
  rw [he]
  exact (isCompact_range (continuous_const.mul continuous_id)).isClosed.measurableSet

/-- Entrywise reduction has a measurable actual additive kernel. -/
theorem matrix_kernel_measurable (I : Ideal R) :
    MeasurableSet (((Ideal.Quotient.mk I).mapMatrix : Matrix (Fin 2) (Fin 2) R →+*
      Matrix (Fin 2) (Fin 2) (R ⧸ I)).toAddMonoidHom.ker :
      Set (Matrix (Fin 2) (Fin 2) R)) := by
  have he : (((Ideal.Quotient.mk I).mapMatrix : Matrix (Fin 2) (Fin 2) R →+*
      Matrix (Fin 2) (Fin 2) (R ⧸ I)).toAddMonoidHom.ker :
      Set (Matrix (Fin 2) (Fin 2) R)) =
        ⋂ i : Fin 2, ⋂ j : Fin 2, {M | M i j ∈ I} := by
    ext M
    simp only [mem_iInter, mem_setOf_eq]
    change (M.map (Ideal.Quotient.mk I) = 0) ↔ ∀ i j, M i j ∈ I
    constructor
    · intro h i j
      exact Ideal.Quotient.eq_zero_iff_mem.mp (congrFun (congrFun h i) j)
    · intro h
      ext i j
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (h i j)
  rw [he]
  exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦
    (ideal_measurable R I).preimage ((measurable_pi_apply j).comp (measurable_pi_apply i))

/-- The actual set of integral matrices satisfying the indicated Gram congruence. -/
def congruenceLocus (G : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    Set (Matrix (Fin 2) (Fin 2) R) :=
  {M | (M.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))).transpose *
    G.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) *
      M.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) =
        G.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))}

/-- Haar volume of the actual Gram congruence locus is its exact finite counting proportion. -/
theorem congruence_volume (G : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    (normalizedHaar (Matrix (Fin 2) (Fin 2) R) (congruenceLocus R G n)).toReal =
      (Nat.card (GramDensityTransport.Solutions
        (G.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))))) : ℝ) /
          (Nat.card (ResidueField R) : ℝ) ^ (4 * (n + 1)) := by
  let A := UnramifiedBinaryDensity.Level R n
  let q := Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))
  let F : Matrix (Fin 2) (Fin 2) R →+ Matrix (Fin 2) (Fin 2) A := q.mapMatrix.toAddMonoidHom
  have hf : Function.Surjective F := by
    intro M
    choose x hx using fun i j ↦ Ideal.Quotient.mk_surjective (M i j)
    exact ⟨Matrix.of x, by ext i j; exact hx i j⟩
  have hc : Nat.card (Matrix (Fin 2) (Fin 2) A) = Nat.card (ResidueField R) ^ (4 * (n + 1)) := by
    change Nat.card (Fin 2 → Fin 2 → A) = _
    rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, UnramifiedBinaryDensity.level_card]
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  have hm := UniformCongruenceMeasure.preimage_real_measure
    (normalizedHaar (Matrix (Fin 2) (Fin 2) R)) F hf
    (matrix_kernel_measurable R (maximalIdeal R ^ (n + 1)))
    {M : Matrix (Fin 2) (Fin 2) A | M.transpose * G.map q * M = G.map q}
  rw [hc, Nat.cast_pow] at hm
  exact hm

/-- The raw Gram density is derived from actual Haar volume with the factor q^(3N)/2. -/
theorem density_eq_volume (G : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    IntegralBinaryDensity.levelDensity R G n =
      (1 / 2 : ℝ) * (Nat.card (ResidueField R) : ℝ) ^ (3 * (n + 1)) *
        (normalizedHaar (Matrix (Fin 2) (Fin 2) R) (congruenceLocus R G n)).toReal := by
  rw [congruence_volume, IntegralBinaryDensity.levelDensity, GramDensityTransport.density,
    UnramifiedBinaryDensity.level_card, Nat.cast_pow]
  have hq : (Nat.card (ResidueField R) : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  let C : ℝ := Nat.card (GramDensityTransport.Solutions
    (G.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))))
  change C / (2 * (Nat.card (ResidueField R) : ℝ) ^ (n + 1)) =
    (1 / 2 : ℝ) * (Nat.card (ResidueField R) : ℝ) ^ (3 * (n + 1)) *
      (C / (Nat.card (ResidueField R) : ℝ) ^ (4 * (n + 1)))
  rw [show 4 * (n + 1) = 3 * (n + 1) + (n + 1) by omega,
    pow_add (Nat.card (ResidueField R) : ℝ) (3 * (n + 1)) (n + 1)]
  field_simp

end Ring

end NormEuclidean.HaarDensityNormalization
