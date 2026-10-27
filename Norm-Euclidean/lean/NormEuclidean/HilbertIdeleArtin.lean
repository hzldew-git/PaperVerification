import NormEuclidean.HilbertClassFieldArithmetic
import NormEuclidean.FullIdeleClassKernel

/-!
# The ordinary Hilbert Artin map on actual full ideles

The map takes the actual finite-idele fractional ideal and applies the
arithmetic ideal Artin map. Infinite signs are unrestricted. Its kernel
and its value at actual prime representatives are proved, not stipulated.
-/

noncomputable section

namespace NormEuclidean.HilbertIdeleArtin

open IsDedekindDomain ExtensionIdeleNorm
open scoped NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- The actual fractional ideal of a full idele, retaining its finite valuations. -/
def ideal : NumberFieldIdele K →* (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  FiniteIdele.idealUnitHom.comp FullIdeleClassKernel.finiteProjection

/-- Arithmetic reciprocity on full ideles for the ordinary Hilbert class field. -/
def artin : NumberFieldIdele K →*
    ((HilbertClassFieldArithmetic.field K) ≃ₐ[K] (HilbertClassFieldArithmetic.field K)) :=
  (HilbertClassFieldArithmetic.classGroupEquiv K).toMonoidHom.comp
    FullIdeleClassKernel.classHom

/-- The full-idele map is the arithmetic ideal Artin map of its actual fractional ideal. -/
theorem artin_eq_ideal_artin (i : NumberFieldIdele K) :
    artin K i = HilbertClassFieldArithmetic.artin K (ideal K i) := rfl

/-- The full-idele arithmetic Artin map is surjective onto the actual Hilbert Galois group. -/
theorem surjective : Function.Surjective (artin K) :=
  (HilbertClassFieldArithmetic.classGroupEquiv K).surjective.comp
    FullIdeleClassKernel.classHom_surjective

/-- Its kernel is the ordinary ideal class kernel, with no positivity restriction at infinity. -/
theorem ker_eq : (artin K).ker = (FullIdeleClassKernel.classHom (K := K)).ker := by
  ext i
  change HilbertClassFieldArithmetic.classGroupEquiv K
      (FullIdeleClassKernel.classHom i) = 1 ↔ FullIdeleClassKernel.classHom i = 1
  constructor
  · intro h
    exact (HilbertClassFieldArithmetic.classGroupEquiv K).injective
      (h.trans (map_one (HilbertClassFieldArithmetic.classGroupEquiv K)).symm)
  · intro h
    rw [h, map_one]

/-- The actual Hilbert Artin kernel consists exactly of principal times ordinary unit ideles. -/
theorem ker_eq_principal_units : (artin K).ker =
    idelePrincipalEmbedding.range ⊔ FullIdeleClassKernel.unitIdeles :=
  (ker_eq K).trans FullIdeleClassKernel.ker_eq

/-- A principal full idele acts trivially on the ordinary Hilbert class field. -/
theorem principal (c : Kˣ) : artin K (idelePrincipalEmbedding c) = 1 := by
  change HilbertClassFieldArithmetic.classGroupEquiv K
    (FullIdeleClassKernel.classHom (idelePrincipalEmbedding c)) = 1
  rw [FullIdeleClassKernel.classHom_principal, map_one]

/-- Every ordinary unit idele, with arbitrary infinite signs, has trivial Artin image. -/
theorem unit (i : FullIdeleClassKernel.unitIdeles (K := K)) : artin K i.1 = 1 := by
  change i.1 ∈ (artin K).ker
  rw [ker_eq_principal_units]
  exact (show FullIdeleClassKernel.unitIdeles ≤
    idelePrincipalEmbedding.range ⊔ FullIdeleClassKernel.unitIdeles from le_sup_right) i.2

/-- A prime representative is an actual full idele with its prescribed prime fractional ideal. -/
def primeIdele (p : HeightOneSpectrum (𝓞 K)) : NumberFieldIdele K :=
  MulEquiv.prodUnits.symm (1, Classical.choose
    (FiniteIdele.idealUnitHom_surjective (IdealArtinConsequences.primeIdeal p)))

/-- The prime representative has precisely the actual prime ideal, not just its ideal class. -/
theorem ideal_primeIdele (p : HeightOneSpectrum (𝓞 K)) :
    ideal K (primeIdele K p) = IdealArtinConsequences.primeIdeal p :=
  Classical.choose_spec
    (FiniteIdele.idealUnitHom_surjective (IdealArtinConsequences.primeIdeal p))

/-- The idele Artin map at a prime representative is the actual arithmetic Frobenius. -/
theorem prime (p : HeightOneSpectrum (𝓞 K))
    (w : FinitePlacesAbove (E := HilbertClassFieldArithmetic.field K) p) :
    artin K (primeIdele K p) = FrobeniusSplitting.frobenius (K := K) w.1 := by
  rw [artin_eq_ideal_artin, ideal_primeIdele]
  exact HilbertClassFieldArithmetic.artin_prime K p w

/-- The ordinary principal-times-unit idele quotient is the actual Hilbert Galois group. -/
def quotientEquiv : NumberFieldIdele K ⧸
    (idelePrincipalEmbedding.range ⊔ FullIdeleClassKernel.unitIdeles) ≃*
      ((HilbertClassFieldArithmetic.field K) ≃ₐ[K] (HilbertClassFieldArithmetic.field K)) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_eq_principal_units K).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (artin K) (surjective K))

/-- The quotient equivalence sends a represented idele to its arithmetic Artin automorphism. -/
theorem quotientEquiv_mk (i : NumberFieldIdele K) :
    quotientEquiv K (QuotientGroup.mk i) = artin K i := rfl

end NormEuclidean.HilbertIdeleArtin
