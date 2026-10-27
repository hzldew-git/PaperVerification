import NormEuclidean.CompletedPrimeIdeals

/-!
# The exact local quotient norm of every completed global ideal

Global Dedekind factorization and the actual prime-ideal comparison show
that completion retains exactly the current prime-power factor. Counting
the quotient in the original completed DVR gives its absolute ideal norm.
No comparison of local and global trace differents is assumed here.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.CompletedIdealFactors

open IsDedekindDomain IsLocalRing Bong.NumberFieldCompletion CompletedPrimeIdeals
open scoped NumberField Classical

variable {F : Type*} [Field F] [NumberField F]

/-- Completion kills all prime factors except the defining one. -/
theorem map_eq_map_prime_part (v : HeightOneSpectrum (𝓞 F))
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    I.map (integerEmbedding v) = (v.maxPowDividing I).map (integerEmbedding v) := by
  calc
    I.map (integerEmbedding v) =
        (∏ᶠ w : HeightOneSpectrum (𝓞 F), w.maxPowDividing I).map (integerEmbedding v) :=
      congrArg (Ideal.map (integerEmbedding v))
        (Ideal.finprod_heightOneSpectrum_factorization hI).symm
    _ = ∏ᶠ w : HeightOneSpectrum (𝓞 F),
        (w.maxPowDividing I).map (integerEmbedding v) :=
      (Ideal.mapHom (integerEmbedding v)).toMonoidHom.map_finprod (Ideal.hasFiniteMulSupport hI)
    _ = (v.maxPowDividing I).map (integerEmbedding v) :=
      finprod_eq_single _ v fun w hw ↦ by rw [map_prime_factor v w I, if_neg hw]

/-- The original global exponent is the exponent of the completed ideal. -/
theorem map_eq_maximal_power (v : HeightOneSpectrum (𝓞 F))
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    I.map (integerEmbedding v) =
      maximalIdeal (integerRing v) ^ multiplicity v.asIdeal I := by
  rw [map_eq_map_prime_part v I hI, v.maxPowDividing_eq_pow_multiplicity hI, map_prime_power]

/-- The actual completed quotient has the prime norm raised to the original exponent. -/
theorem quotient_card (v : HeightOneSpectrum (𝓞 F))
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    Nat.card (integerRing v ⧸ I.map (integerEmbedding v)) =
      Ideal.absNorm v.asIdeal ^ multiplicity v.asIdeal I := by
  rw [map_eq_maximal_power v I hI, DyadicTwoRootCount.quotient_card,
    BinaryPlaceDensity.residue_card]

/-- Its cardinality is exactly the absolute norm of the maximal prime-power divisor. -/
theorem quotient_card_eq_prime_norm (v : HeightOneSpectrum (𝓞 F))
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    Nat.card (integerRing v ⧸ I.map (integerEmbedding v)) =
      Ideal.absNorm (v.maxPowDividing I) := by
  rw [quotient_card v I hI, v.maxPowDividing_eq_pow_multiplicity hI, map_pow]

/-- A nonzero global ideal stays nonzero in the original completion. -/
theorem map_ne_bot (v : HeightOneSpectrum (𝓞 F))
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    I.map (integerEmbedding v) ≠ ⊥ := by
  rw [map_eq_maximal_power v I hI]
  exact pow_ne_zero _ (IsDiscreteValuationRing.not_a_field (integerRing v))

/-- The completed quotient is finite, including the zero quotient at exponent zero. -/
theorem quotient_finite (v : HeightOneSpectrum (𝓞 F))
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    Finite (integerRing v ⧸ I.map (integerEmbedding v)) := by
  apply Nat.finite_of_card_ne_zero
  rw [quotient_card v I hI]
  exact pow_ne_zero _ (by
    have h := NumberField.HeightOneSpectrum.one_lt_absNorm v
    omega)

end NormEuclidean.CompletedIdealFactors
