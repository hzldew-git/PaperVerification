import NormEuclidean.HaarDensityNormalization
import NormEuclidean.BinaryPlaceDensity

/-!
# Haar normalization at actual number-field completions

Compactness, Borel measurability and normalized Haar measure are
constructed for the original completed integer ring. The residue
cardinality is identified with the original prime-ideal norm.
-/

noncomputable section

namespace NormEuclidean.CompletedHaarDensity

open IsDedekindDomain Bong.NumberFieldCompletion MeasureTheory TopologicalSpace
open HaarDensityNormalization
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

local instance completedMeasurable (p : HeightOneSpectrum (𝓞 K)) :
    MeasurableSpace (integerRing p) := borel (integerRing p)

local instance completedBorel (p : HeightOneSpectrum (𝓞 K)) : BorelSpace (integerRing p) := ⟨rfl⟩

local instance completedCompact (p : HeightOneSpectrum (𝓞 K)) : CompactSpace (integerRing p) :=
  (Valued.integer.properSpace_iff_compactSpace_integer (K := p.adicCompletion K)).mp inferInstance

local instance completedSecondCountable (p : HeightOneSpectrum (𝓞 K)) :
    SecondCountableTopology (integerRing p) := by infer_instance

local instance residueFinite (p : HeightOneSpectrum (𝓞 K)) :
    Finite (IsLocalRing.ResidueField (integerRing p)) := finiteResidueField p

attribute [local instance] HaarDensityNormalization.matrixMeasurable
  HaarDensityNormalization.matrixCompact HaarDensityNormalization.matrixBorel
  HaarDensityNormalization.matrixMeasurableAdd

/-- The actual completed congruence locus has its exact prime-norm Haar volume. -/
theorem congruence_volume (p : HeightOneSpectrum (𝓞 K))
    (G : Matrix (Fin 2) (Fin 2) (integerRing p)) (n : ℕ) :
    (normalizedHaar (Matrix (Fin 2) (Fin 2) (integerRing p))
      (congruenceLocus (integerRing p) G n)).toReal =
        (Nat.card (GramDensityTransport.Solutions
          (G.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (integerRing p) ^ (n + 1))))) : ℝ) /
            (Ideal.absNorm p.asIdeal : ℝ) ^ (4 * (n + 1)) := by
  simpa only [BinaryPlaceDensity.residue_card] using
    HaarDensityNormalization.congruence_volume (integerRing p) G n

/-- The raw density/Haar-volume conversion has no unproved local normalization premise. -/
theorem density_normalization (p : HeightOneSpectrum (𝓞 K))
    (G : Matrix (Fin 2) (Fin 2) (integerRing p)) (n : ℕ) :
    IntegralBinaryDensity.levelDensity (integerRing p) G n =
      (1 / 2 : ℝ) * (Ideal.absNorm p.asIdeal : ℝ) ^ (3 * (n + 1)) *
        (normalizedHaar (Matrix (Fin 2) (Fin 2) (integerRing p))
          (congruenceLocus (integerRing p) G n)).toReal := by
  simpa only [BinaryPlaceDensity.residue_card] using
    HaarDensityNormalization.density_eq_volume (integerRing p) G n

end NormEuclidean.CompletedHaarDensity
