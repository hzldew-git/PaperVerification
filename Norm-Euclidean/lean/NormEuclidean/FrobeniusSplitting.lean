/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license in NormEuclidean/Reuse/LICENSE.
Adapted from the fixed class-field source recorded in the reuse audit.
-/
import NormEuclidean.FinitePrimeSplitting
import Mathlib.RingTheory.Frobenius
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.RamificationInertia.Unramified

/-!
# Arithmetic Frobenius and complete splitting

The order and conjugacy arguments are adapted from Naganori Yamaguchi's
`MathlibFrobeniusHilbertComparison` at commit
`01b4bcb786c458c9af029860c9bbdbd67dd7c978`. They use actual integer-ring
Frobenius elements, without a class-field or reciprocity hypothesis.
-/

noncomputable section

namespace NormEuclidean.FrobeniusSplitting

open IsDedekindDomain ExtensionIdeleNorm
open scoped NumberField Pointwise NormEuclidean.CompletedExtensionProduct

universe u
variable {K E : Type u} [Field K] [NumberField K]
  [Field E] [NumberField E] [Algebra K E]

private instance residueFinite (w : HeightOneSpectrum (𝓞 E)) : Finite ((𝓞 E) ⧸ w.asIdeal) :=
  Ring.HasFiniteQuotients.finiteQuotient w.ne_bot

section Galois

variable [IsGalois K E]

/-- The actual arithmetic Frobenius lift acting on the extension field. -/
def frobenius (w : HeightOneSpectrum (𝓞 E)) : E ≃ₐ[K] E :=
  arithFrobAt (𝓞 K) (E ≃ₐ[K] E) w.asIdeal

/-- The chosen field automorphism acts by the residue-field cardinal power. -/
theorem isArithFrobAt (w : HeightOneSpectrum (𝓞 E)) :
    IsArithFrobAt (𝓞 K) (frobenius (K := K) w) w.asIdeal :=
  IsArithFrobAt.arithFrobAt (𝓞 K) (E ≃ₐ[K] E) w.asIdeal

/-- The actual Frobenius lift is unique at an unramified extension prime. -/
theorem unique_of_unramified (w : HeightOneSpectrum (𝓞 E))
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) (σ : E ≃ₐ[K] E)
    (hσ : IsArithFrobAt (𝓞 K) σ w.asIdeal) : σ = frobenius (K := K) w := by
  letI : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := hunram
  letI : FaithfulSMul (E ≃ₐ[K] E) (𝓞 E) := IsGaloisGroup.faithful (𝓞 K)
  apply MulSemiringAction.toAlgHom_injective (𝓞 K) (𝓞 E)
  exact hσ.eq_of_isUnramifiedAt (isArithFrobAt w) w.asIdeal.primeCompl_le_nonZeroDivisors

/-- At an actual unramified prime, Frobenius order equals the inertia degree. -/
theorem order_eq_inertia_degree (p : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 E)) (hw : w.asIdeal.LiesOver p.asIdeal)
    (hunram : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    orderOf (frobenius (K := K) w) = w.asIdeal.inertiaDeg (𝓞 K) := by
  classical
  let P : Ideal (𝓞 K) := p.asIdeal
  let Q : Ideal (𝓞 E) := w.asIdeal
  let G := E ≃ₐ[K] E
  let g : G := frobenius (K := K) w
  letI : Q.LiesOver P := hw
  letI : Algebra.IsUnramifiedAt (𝓞 K) Q := hunram
  letI : Field ((𝓞 K) ⧸ P) := Ideal.Quotient.field P
  letI : Field ((𝓞 E) ⧸ Q) := Ideal.Quotient.field Q
  letI : Finite ((𝓞 K) ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient p.ne_bot
  letI : Finite ((𝓞 E) ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  letI : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
  have hF : IsArithFrobAt (𝓞 K) g Q := isArithFrobAt w
  let gs : MulAction.stabilizer G Q := ⟨g, hF.mem_stabilizer⟩
  have hImage : Ideal.Quotient.stabilizerHom Q P G gs =
      FiniteField.frobeniusAlgEquivOfAlgebraic ((𝓞 K) ⧸ P) ((𝓞 E) ⧸ Q) := by
    apply AlgEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.stabilizerHom_apply]
    simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    have h := hF.mk_apply y
    have hQP : Q.under (𝓞 K) = P := hw.over.symm
    rw [hQP, Nat.card_eq_fintype_card] at h
    exact h
  have hImageOrder : orderOf (Ideal.Quotient.stabilizerHom Q P G gs) =
      Q.inertiaDeg (𝓞 K) := by
    rw [hImage, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
    exact (Ideal.inertiaDeg_eq_of_isMaximal P Q).symm
  have hCard : Nat.card (MulAction.stabilizer G Q) = Q.inertiaDeg (𝓞 K) := by
    rw [Ideal.card_stabilizer_eq (G := G) P Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx P Q G,
      Ideal.inertiaDegIn_eq_inertiaDeg P Q G,
      Ideal.ramificationIdx_eq_one Q (𝓞 K), one_mul]
  have hUpper : orderOf gs ∣ Q.inertiaDeg (𝓞 K) := by
    rw [← hCard]
    exact orderOf_dvd_natCard gs
  have hLower : Q.inertiaDeg (𝓞 K) ∣ orderOf gs := by
    rw [← hImageOrder]
    exact orderOf_map_dvd (Ideal.Quotient.stabilizerHom Q P G) gs
  exact (Subgroup.orderOf_coe gs).trans (Nat.dvd_antisymm hUpper hLower)

end Galois

variable [IsAbelianGalois K E]

/-- In an abelian extension, the actual lift is independent of the prime above p. -/
theorem independent_of_prime (p : HeightOneSpectrum (𝓞 K))
    (w w' : HeightOneSpectrum (𝓞 E)) (hw : w.asIdeal.LiesOver p.asIdeal)
    (hw' : w'.asIdeal.LiesOver p.asIdeal) :
    frobenius (K := K) w = frobenius (K := K) w' := by
  obtain ⟨τ, hτ⟩ := isConj_iff.mp
    (isConj_arithFrobAt (𝓞 K) (E ≃ₐ[K] E) w.asIdeal w'.asIdeal
      (hw.over.symm.trans hw'.over))
  calc
    frobenius (K := K) w = τ * frobenius (K := K) w * τ⁻¹ := by
      rw [IsMulCommutative.is_comm.comm τ (frobenius (K := K) w), mul_assoc,
        mul_inv_cancel, mul_one]
    _ = frobenius (K := K) w' := hτ

/-- At an unramified base prime, Frobenius is trivial exactly when all primes split. -/
theorem eq_one_iff_split (p : HeightOneSpectrum (𝓞 K))
    (hunram : Algebra.IsUnramifiedIn (𝓞 E) p.asIdeal)
    (w : FinitePlacesAbove (E := E) p) :
    frobenius (K := K) w.1 = 1 ↔
      ∀ z : FinitePlacesAbove (E := E) p,
        z.1.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ z.1.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  have hlie (z : FinitePlacesAbove (E := E) p) : z.1.asIdeal.LiesOver p.asIdeal :=
    ⟨(congrArg HeightOneSpectrum.asIdeal z.2).symm⟩
  have hz (z : FinitePlacesAbove (E := E) p) :
      Algebra.IsUnramifiedAt (𝓞 K) z.1.asIdeal := hunram _ z.1.isPrime (hlie z)
  constructor
  · intro h z
    letI : Algebra.IsUnramifiedAt (𝓞 K) z.1.asIdeal := hz z
    refine ⟨Ideal.ramificationIdx_eq_one z.1.asIdeal (𝓞 K), ?_⟩
    rw [← order_eq_inertia_degree p z.1 (hlie z) (hz z),
      ← independent_of_prime p w.1 z.1 (hlie w) (hlie z), h, orderOf_one]
  · intro h
    apply orderOf_eq_one_iff.mp
    rw [order_eq_inertia_degree p w.1 (hlie w) (hz w), (h w).2]

/-- Trivial Frobenius supplies the actual completed-degree input of field comparison. -/
theorem degree_one_of_frobenius_eq_one (p : HeightOneSpectrum (𝓞 K))
    (hunram : Algebra.IsUnramifiedIn (𝓞 E) p.asIdeal)
    (w : FinitePlacesAbove (E := E) p) (hF : frobenius (K := K) w.1 = 1)
    (z : FinitePlacesAbove (E := E) p) :
    Module.finrank (p.adicCompletion K) (z.1.adicCompletion E) = 1 :=
  FinitePrimeSplitting.degree_one_of_ramification_inertia_one p
    ((eq_one_iff_split p hunram w).mp hF) z

end NormEuclidean.FrobeniusSplitting
