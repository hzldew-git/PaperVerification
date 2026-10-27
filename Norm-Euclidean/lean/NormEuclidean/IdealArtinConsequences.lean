import NormEuclidean.FrobeniusSplitting
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# The degree and splitting consequences of ideal Artin reciprocity

These are implications for an actual ideal-group homomorphism into the
actual field automorphism group. Frobenius normalization is imposed at the
actual prime fractional ideals. Construction of that homomorphism, its
reciprocity theorem and the Hilbert class field remain separate tasks.
-/

noncomputable section

namespace NormEuclidean.IdealArtinConsequences

open IsDedekindDomain ExtensionIdeleNorm
open scoped NumberField nonZeroDivisors NormEuclidean.CompletedExtensionProduct

universe u
variable {K E : Type u} [Field K] [NumberField K]
  [Field E] [NumberField E] [Algebra K E]

/-- The actual invertible fractional ideal represented by a nonzero finite prime. -/
def primeIdeal (p : HeightOneSpectrum (𝓞 K)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (p.asIdeal : FractionalIdeal (𝓞 K)⁰ K)
    (FractionalIdeal.coeIdeal_ne_zero.mpr p.ne_bot)

/-- The actual ideal class projection has precisely the principal fractional ideal kernel. -/
theorem class_projection_ker :
    (ClassGroup.mk K).ker = (toPrincipalIdeal (𝓞 K) K).range := by
  ext I
  rw [MonoidHom.mem_ker, ← (ClassGroup.equiv K).injective.eq_iff]
  simp [ClassGroup.equiv_mk, QuotientGroup.eq_one_iff]

/-- A prime's actual fractional ideal represents the trivial ordinary class iff principal. -/
theorem prime_class_eq_one_iff (p : HeightOneSpectrum (𝓞 K)) :
    ClassGroup.mk K (primeIdeal p) = 1 ↔ p.asIdeal.IsPrincipal := by
  rw [ClassGroup.mk_eq_one_iff]
  exact IsFractionRing.coeSubmodule_isPrincipal (𝓞 K) K

/-- Surjectivity and the principal kernel yield the actual class-group/Galois equivalence. -/
def classGroupEquiv (artin : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (E ≃ₐ[K] E))
    (hsurj : Function.Surjective artin)
    (hker : artin.ker = (toPrincipalIdeal (𝓞 K) K).range) :
    ClassGroup (𝓞 K) ≃* (E ≃ₐ[K] E) :=
  ((ClassGroup.equiv K).trans (QuotientGroup.quotientMulEquivOfEq hker.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective artin hsurj)

omit [NumberField E] in
/-- The two kernels alone detect principal prime ideals, without a degree premise. -/
theorem prime_artin_eq_one_iff (artin : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (E ≃ₐ[K] E))
    (hker : artin.ker = (toPrincipalIdeal (𝓞 K) K).range)
    (p : HeightOneSpectrum (𝓞 K)) : artin (primeIdeal p) = 1 ↔ p.asIdeal.IsPrincipal := by
  have h := Subgroup.ext_iff.mp (hker.trans (class_projection_ker (K := K)).symm)
    (primeIdeal p)
  exact h.trans (prime_class_eq_one_iff p)

section Galois

variable [IsGalois K E]

/-- The degree formula follows from ideal Artin reciprocity and actual Galois theory. -/
theorem degree_eq_class_number (artin : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (E ≃ₐ[K] E))
    (hsurj : Function.Surjective artin)
    (hker : artin.ker = (toPrincipalIdeal (𝓞 K) K).range) :
    Module.finrank K E = NumberField.classNumber K := by
  rw [← IsGalois.card_aut_eq_finrank, NumberField.classNumber,
    ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (classGroupEquiv artin hsurj hker).symm.toEquiv

end Galois

variable [IsAbelianGalois K E]

/-- Cox 5.25 follows from a principal Artin kernel and actual Frobenius normalization. -/
theorem split_iff_principal (artin : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (E ≃ₐ[K] E))
    (hker : artin.ker = (toPrincipalIdeal (𝓞 K) K).range)
    (p : HeightOneSpectrum (𝓞 K)) (hunram : Algebra.IsUnramifiedIn (𝓞 E) p.asIdeal)
    (hprime : ∀ w : FinitePlacesAbove (E := E) p,
      artin (primeIdeal p) = FrobeniusSplitting.frobenius (K := K) w.1) :
    (∀ w : FinitePlacesAbove (E := E) p,
      w.1.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ w.1.asIdeal.inertiaDeg (𝓞 K) = 1) ↔
      p.asIdeal.IsPrincipal := by
  obtain ⟨w⟩ := finitePlacesAbove_nonempty (E := E) p
  rw [← FrobeniusSplitting.eq_one_iff_split p hunram w, ← hprime w]
  exact prime_artin_eq_one_iff artin hker p

/-- A principal prime has all completed degrees one under actual ideal Artin reciprocity. -/
theorem degree_one_of_principal (artin : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (E ≃ₐ[K] E))
    (hker : artin.ker = (toPrincipalIdeal (𝓞 K) K).range)
    (p : HeightOneSpectrum (𝓞 K)) (hunram : Algebra.IsUnramifiedIn (𝓞 E) p.asIdeal)
    (hprime : ∀ w : FinitePlacesAbove (E := E) p,
      artin (primeIdeal p) = FrobeniusSplitting.frobenius (K := K) w.1)
    (hp : p.asIdeal.IsPrincipal) (w : FinitePlacesAbove (E := E) p) :
    Module.finrank (p.adicCompletion K) (w.1.adicCompletion E) = 1 :=
  FinitePrimeSplitting.degree_one_of_ramification_inertia_one p
    ((split_iff_principal artin hker p hunram hprime).mpr hp) w

end NormEuclidean.IdealArtinConsequences
