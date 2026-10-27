import NormEuclidean.CompletedIdealFactors

/-!
# Canonical prime-power quotient equivalences for the original completion

The actual global integer embedding induces a bijective ring map modulo
every prime power. This includes exponent zero and all residue
characteristics. Injectivity is proved from valuations; equal finite
cardinalities then give surjectivity, without an approximation premise.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.CompletedIdealQuotients

open IsDedekindDomain IsLocalRing Bong.NumberFieldCompletion CompletedPrimeIdeals
open scoped NumberField WithZero

variable {F : Type*} [Field F] [NumberField F]

/-- A completed maximal-ideal power is the actual original valuation ball. -/
theorem mem_maximal_power_iff (v : HeightOneSpectrum (𝓞 F)) (x : integerRing v) (n : ℕ) :
    x ∈ maximalIdeal (integerRing v) ^ n ↔
      Valued.v (x : v.adicCompletion F) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [← globalUniformizer_span v, Ideal.span_singleton_pow]
  change x ∈ (Ideal.span {integerEmbedding v (globalUniformizer v) ^ n} : Set (integerRing v)) ↔ _
  rw [Valuation.integer.coe_span_singleton_eq_setOf_le_v_coe]
  change Valued.v (x : v.adicCompletion F) ≤
    Valued.v (((integerEmbedding v (globalUniformizer v) : integerRing v) :
      v.adicCompletion F) ^ n) ↔ _
  rw [map_pow, embedding_valuation, globalUniformizer_valuation, ← WithZero.exp_nsmul]
  simp only [nsmul_eq_mul, mul_neg, mul_one]

/-- The embedding detects all prime-power congruences, not just the residue field. -/
theorem embedding_mem_power (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) (n : ℕ) :
    integerEmbedding v a ∈ maximalIdeal (integerRing v) ^ n ↔ a ∈ v.asIdeal ^ n := by
  rw [mem_maximal_power_iff, embedding_valuation, v.intValuation_le_pow_iff_mem]

/-- Contraction recovers precisely the original prime power. -/
theorem comap_maximal_power (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    (maximalIdeal (integerRing v) ^ n).comap (integerEmbedding v) = v.asIdeal ^ n := by
  ext a
  exact embedding_mem_power v a n

/-- The canonical ring map from a global prime-power quotient to the completed quotient. -/
def primePowerMap (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    (𝓞 F ⧸ v.asIdeal ^ n) →+* (integerRing v ⧸ maximalIdeal (integerRing v) ^ n) :=
  Ideal.quotientMap _ (integerEmbedding v) (by rw [comap_maximal_power])

theorem primePowerMap_mk (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (a : 𝓞 F) :
    primePowerMap v n (Ideal.Quotient.mk (v.asIdeal ^ n) a) =
      Ideal.Quotient.mk (maximalIdeal (integerRing v) ^ n) (integerEmbedding v a) := rfl

/-- The canonical prime-power map is injective by the actual valuation criterion. -/
theorem primePowerMap_injective (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    Function.Injective (primePowerMap v n) := by
  apply Ideal.quotientMap_injective'
  rw [comap_maximal_power]

/-- Both actual prime-power quotient rings have the same finite cardinality. -/
theorem prime_power_card (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    Nat.card (𝓞 F ⧸ v.asIdeal ^ n) =
      Nat.card (integerRing v ⧸ maximalIdeal (integerRing v) ^ n) := by
  calc
    Nat.card (𝓞 F ⧸ v.asIdeal ^ n) = Ideal.absNorm (v.asIdeal ^ n) :=
      (Ideal.absNorm_apply _).symm
    _ = Nat.card (integerRing v ⧸ maximalIdeal (integerRing v) ^ n) := by
      rw [map_pow, DyadicTwoRootCount.quotient_card, BinaryPlaceDensity.residue_card]

/-- Finite cardinality upgrades the proved injection to an actual bijection. -/
theorem primePowerMap_bijective (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    Function.Bijective (primePowerMap v n) := by
  letI : Finite (integerRing v ⧸ maximalIdeal (integerRing v)) := finiteResidueField v
  letI : Finite (integerRing v ⧸ maximalIdeal (integerRing v) ^ n) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
  exact (Nat.bijective_iff_injective_and_card (primePowerMap v n)).mpr
    ⟨primePowerMap_injective v n, prime_power_card v n⟩

/-- The canonical global-to-completed prime-power comparison is a ring equivalence. -/
def primePowerEquiv (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    (𝓞 F ⧸ v.asIdeal ^ n) ≃+* (integerRing v ⧸ maximalIdeal (integerRing v) ^ n) :=
  RingEquiv.ofBijective (primePowerMap v n) (primePowerMap_bijective v n)

theorem primePowerEquiv_mk (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (a : 𝓞 F) :
    primePowerEquiv v n (Ideal.Quotient.mk (v.asIdeal ^ n) a) =
      Ideal.Quotient.mk (maximalIdeal (integerRing v) ^ n) (integerEmbedding v a) := rfl

/-- Every completed integral class at every finite precision has a global integral lift. -/
theorem exists_integral_lift (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (x : integerRing v) :
    ∃ a : 𝓞 F, integerEmbedding v a - x ∈ maximalIdeal (integerRing v) ^ n := by
  obtain ⟨y, hy⟩ := (primePowerMap_bijective v n).surjective
    (Ideal.Quotient.mk (maximalIdeal (integerRing v) ^ n) x)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨a, Ideal.Quotient.eq.mp hy⟩

/-- Contraction of a completed nonzero ideal is its original primary component. -/
theorem comap_map (v : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    (I.map (integerEmbedding v)).comap (integerEmbedding v) = v.maxPowDividing I := by
  rw [CompletedIdealFactors.map_eq_maximal_power v I hI, comap_maximal_power,
    v.maxPowDividing_eq_pow_multiplicity hI]

/-- The canonical primary-component quotient map for any actual nonzero global ideal. -/
def primePartMap (v : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    (𝓞 F ⧸ v.maxPowDividing I) →+* (integerRing v ⧸ I.map (integerEmbedding v)) :=
  Ideal.quotientMap _ (integerEmbedding v) (by rw [comap_map v I hI])

theorem primePartMap_bijective (v : HeightOneSpectrum (𝓞 F))
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    Function.Bijective (primePartMap v I hI) := by
  letI := CompletedIdealFactors.quotient_finite v I hI
  apply (Nat.bijective_iff_injective_and_card (primePartMap v I hI)).mpr
  constructor
  · apply Ideal.quotientMap_injective'
    rw [comap_map v I hI]
  · exact (Ideal.absNorm_apply (v.maxPowDividing I)).symm.trans
      (CompletedIdealFactors.quotient_card_eq_prime_norm v I hI).symm

/-- The completed quotient is canonically the original primary-component quotient. -/
def primePartEquiv (v : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    (𝓞 F ⧸ v.maxPowDividing I) ≃+* (integerRing v ⧸ I.map (integerEmbedding v)) :=
  RingEquiv.ofBijective (primePartMap v I hI) (primePartMap_bijective v I hI)

theorem primePartEquiv_mk (v : HeightOneSpectrum (𝓞 F))
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (a : 𝓞 F) :
    primePartEquiv v I hI (Ideal.Quotient.mk (v.maxPowDividing I) a) =
      Ideal.Quotient.mk (I.map (integerEmbedding v)) (integerEmbedding v a) := rfl

/-- The canonical comparisons commute with every decrease in precision. -/
theorem primePowerMap_reduction (v : HeightOneSpectrum (𝓞 F))
    (m n : ℕ) (hmn : m ≤ n) (x : 𝓞 F ⧸ v.asIdeal ^ n) :
    primePowerMap v m (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) x) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) (primePowerMap v n x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end NormEuclidean.CompletedIdealQuotients
