import NormEuclidean.ChapterX.CompletedNormImages
import NormEuclidean.ChapterX.BinaryUnitRepresentation
import NormEuclidean.ChapterX.ScalarIntegralApproximation

/-!
# Unit norm surjectivity at good finite places

The binary Hensel theorem gives a literal integral representation of every
unit by x squared minus theta times y squared when two and theta are units.
It is transported to the actual completed quadratic norm product. No local
norm-index law or local class-field theory is used.
-/

noncomputable section

namespace NormEuclidean.GoodPlaceNorms

open IsDedekindDomain CompletedIntegralLattice QuadraticExtensionNorm ExtensionIdeleNorm
  ScalarIntegralApproximation
open scoped NumberField WithZero

/-- Every unit is a quadratic norm over a Henselian local ring with finite
odd residue field. The representation has integral coordinates. -/
theorem henselian_unit_norm {S : Type*} [CommRing S] [IsLocalRing S]
    [Finite (IsLocalRing.ResidueField S)]
    [HenselianRing S (IsLocalRing.maximalIdeal S)]
    (htwo : IsUnit (2 : S)) (theta a : Sˣ) :
    ∃ x y : S, x ^ 2 - (theta : S) * y ^ 2 = (a : S) := by
  obtain ⟨x, y, h⟩ := BinaryUnitRepresentation.henselian_binary_represents_unit
    htwo 1 (-theta) a
  exact ⟨x, y, by simpa only [Units.val_one, one_mul, Units.val_neg, neg_mul,
    ← sub_eq_add_neg] using h⟩

variable {K : Type*} [Field K] [NumberField K]

/-- Actual local units are quadratic norms at every odd place where the
parameter is a unit. Both coordinates are in the actual completed integer ring. -/
theorem local_unit_norm (p : HeightOneSpectrum (𝓞 K))
    (htwo : (2 : 𝓞 K) ∉ p.asIdeal) (theta a : (p.adicCompletion K)ˣ)
    (htheta : Valued.v (theta : p.adicCompletion K) = 1)
    (ha : Valued.v (a : p.adicCompletion K) = 1) :
    ∃ x y : p.adicCompletionIntegers K,
      (x : p.adicCompletion K) ^ 2 - (theta : p.adicCompletion K) *
        (y : p.adicCompletion K) ^ 2 = (a : p.adicCompletion K) := by
  let S := LocalRing (integerSubring K) p
  letI : Finite (IsLocalRing.ResidueField S) := CompletionHensel.finite_residue_field p
  letI : HenselianRing S (IsLocalRing.maximalIdeal S) :=
    CompletionHensel.henselian_completed_integers p
  let t : S := ⟨(theta : p.adicCompletion K), htheta.le⟩
  let b : S := ⟨(a : p.adicCompletion K), ha.le⟩
  have ht : IsUnit t :=
    (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mpr htheta
  have hb : IsUnit b :=
    (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mpr ha
  have htwoS : IsUnit (2 : S) := by
    have h := isUnit_algebraMap_localRing (integerSubring K) p htwo
    convert h using 1
    apply Subtype.ext
    exact (map_ofNat (algebraMap K (p.adicCompletion K)) 2).symm
  obtain ⟨x, y, h⟩ := henselian_unit_norm htwoS ht.unit hb.unit
  refine ⟨x, y, ?_⟩
  have hv := congrArg S.subtype h
  rw [map_sub, map_mul, map_pow, map_pow, ht.unit_spec, hb.unit_spec] at hv
  exact hv

/-- The preceding integral representation supplies the local norm equation. -/
theorem isQuadraticNorm_of_units (p : HeightOneSpectrum (𝓞 K))
    (htwo : (2 : 𝓞 K) ∉ p.asIdeal) (theta a : (p.adicCompletion K)ˣ)
    (htheta : Valued.v (theta : p.adicCompletion K) = 1)
    (ha : Valued.v (a : p.adicCompletion K) = 1) :
    Bong.Dyadic.IsQuadraticNorm (p.adicCompletion K) theta a := by
  obtain ⟨x, y, h⟩ := local_unit_norm p htwo theta a htheta ha
  exact ⟨x, y, h⟩

universe u
variable {F : Type u} [Field F] [NumberField F]

/-- Every unit belongs to the actual completed extension norm image at a
good prime, without a supplied local representation or norm-index premise. -/
theorem mem_actual_norm_range (theta : Fˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 F)) (htwo : (2 : 𝓞 F) ∉ p.asIdeal)
    (hthetaUnit : p.valuation F (theta : F) = 1) (a : (p.adicCompletion F)ˣ)
    (ha : Valued.v (a : p.adicCompletion F) = 1) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    a ∈ (finitePlaceFiberNormUnits (E := QuadraticAlgebra F (theta : F) 0) p).range := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  apply (CompletedNormImages.finite_norm_range_iff theta htheta p a).mpr
  apply isQuadraticNorm_of_units p htwo _ a _ ha
  change Valued.v (algebraMap F (p.adicCompletion F) (theta : F)) = 1
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p (theta : F)).trans hthetaUnit

end NormEuclidean.GoodPlaceNorms
