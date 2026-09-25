import DedekindZeta.DualClassReindex
import TraceEuclidean.V15AnalyticMellinBridge

/-!
# Rescaling fractional-ideal theta kernels

This file supplies the analytic scaling bridge needed after the class-group
reindexing of trace-dual fractional ideals.
-/

open NumberField IsDedekindDomain
open MeasureTheory
open scoped nonZeroDivisors

namespace DedekindZeta.FractionalIdealRescaling

open DedekindZeta.ConeRadialReduction DedekindZeta.MellinPrinciple

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

private def mulRightMeasurableEquiv (c : mixedEmbedding.mixedSpace K)
    (hc : mixedEmbedding.norm c ≠ 0) :
    mixedEmbedding.mixedSpace K ≃ᵐ mixedEmbedding.mixedSpace K where
  toEquiv :=
    { toFun := fun y ↦ y * c
      invFun := fun y ↦ y * c⁻¹
      left_inv := fun y ↦ by
        dsimp
        rw [mul_assoc, Theta.mul_inv_cancel_of_norm_ne_zero K hc, mul_one]
      right_inv := fun y ↦ by
        dsimp
        rw [mul_assoc, mul_comm c⁻¹ c, Theta.mul_inv_cancel_of_norm_ne_zero K hc, mul_one] }
  measurable_toFun := measurable_mul_right_mixedSpace (K := K) c
  measurable_invFun := measurable_mul_right_mixedSpace (K := K) c⁻¹

private theorem measurePreserving_mulRight (c : mixedEmbedding.mixedSpace K)
    (hc : mixedEmbedding.norm c ≠ 0) :
    MeasurePreserving (mulRightMeasurableEquiv K c hc)
      (mixedMulHaar K) (mixedMulHaar K) := by
  refine ⟨(mulRightMeasurableEquiv K c hc).measurable, ?_⟩
  exact mixedMulHaar_map_mul_right (K := K) hc

local instance coneMulAction :
    MulAction (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
      (mixedEmbedding.mixedSpace K) :=
  MulAction.compHom _ (coneUnitHom (K := K))

local instance coneMeasurableConstSMul :
    MeasurableConstSMul (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
      (mixedEmbedding.mixedSpace K) :=
  ⟨fun g ↦ measurable_unitSMul (coneUnitHom g)⟩

local instance coneCountable :
    Countable (Multiplicative (Fin (NumberField.Units.rank K) → ℤ)) :=
  inferInstanceAs (Countable (Fin (NumberField.Units.rank K) → ℤ))

local instance coneSMulInvariantMeasure :
    SMulInvariantMeasure (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
      (mixedEmbedding.mixedSpace K) (mixedMulHaar K) :=
  ⟨fun g _s hs ↦
    (measurePreserving_unitSMul (coneUnitHom g)).measure_preimage hs.nullMeasurableSet⟩

/-- Right translation by a nonzero archimedean element does not change a
unit-invariant integral over the fundamental cone. -/
theorem integral_comp_mulRight_fundamentalCone_eq
    (c : mixedEmbedding.mixedSpace K) (hc : mixedEmbedding.norm c ≠ 0)
    (f : mixedEmbedding.mixedSpace K → ℂ)
    (hf : ∀ (u : (𝓞 K)ˣ) y, f (u • y) = f y) :
    (∫ y in mixedEmbedding.fundamentalCone K, f (y * c) ∂(mixedMulHaar K)) =
      ∫ y in mixedEmbedding.fundamentalCone K, f y ∂(mixedMulHaar K) := by
  let e := mulRightMeasurableEquiv K c hc
  have hepres : MeasurePreserving e (mixedMulHaar K) (mixedMulHaar K) :=
    measurePreserving_mulRight K c hc
  have hsemiconj : ∀ g : Multiplicative (Fin (NumberField.Units.rank K) → ℤ),
      Function.Semiconj e (g • ·) (g • ·) := by
    intro g y
    change (g • y) * c = g • (y * c)
    simp only [coneSMul_def, NumberField.mixedEmbedding.unitSMul_smul]
    ring
  have himage : IsFundamentalDomain
      (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
      (e '' mixedEmbedding.fundamentalCone K) (mixedMulHaar K) :=
    (isFundamentalDomain_fundamentalCone (K := K)).image_of_equiv e.toEquiv
      (MeasurePreserving.symm e hepres).quasiMeasurePreserving (Equiv.refl _) hsemiconj
  have hf' : ∀ (g : Multiplicative (Fin (NumberField.Units.rank K) → ℤ)) y,
      f (g • y) = f y := fun g y ↦ hf (coneUnitHom g) y
  have hdomain := (isFundamentalDomain_fundamentalCone (K := K)).setIntegral_eq
    himage hf'
  have hchange := hepres.setIntegral_image_emb e.measurableEmbedding f
    (mixedEmbedding.fundamentalCone K)
  exact hchange.symm.trans hdomain.symm

/-- Multiplying a fractional ideal by a principal fractional ideal is the
same as translating the multiplicative theta variable. -/
theorem mixedThetaKernel_spanSingleton_mul (x : K) (hx : x ≠ 0)
    (J : FractionalIdeal (𝓞 K)⁰ K) (y : mixedEmbedding.mixedSpace K) :
    Theta.mixedThetaKernel K (FractionalIdeal.spanSingleton (𝓞 K)⁰ x * J) y =
      Theta.mixedThetaKernel K J (y * mixedEmbedding K x) := by
  let e : {b : K // b ∈ (J : Submodule (𝓞 K) K) ∧ b ≠ 0} ≃
      {a : K //
        a ∈ ((FractionalIdeal.spanSingleton (𝓞 K)⁰ x * J :
          FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ∧ a ≠ 0} :=
    Equiv.ofBijective
      (fun b ↦ ⟨x * b.1,
        (FractionalIdeal.mem_singleton_mul.mpr ⟨b.1, b.2.1, rfl⟩),
        mul_ne_zero hx b.2.2⟩)
      ⟨by
          intro a b hab
          apply Subtype.ext
          exact mul_left_cancel₀ hx (Subtype.ext_iff.mp hab),
        by
          rintro ⟨a, ha, hane⟩
          obtain ⟨b, hb, hab⟩ := FractionalIdeal.mem_singleton_mul.mp ha
          have hbne : b ≠ 0 := by
            intro hb0
            subst b
            simp only [mul_zero] at hab
            exact hane hab
          refine ⟨⟨b, hb, hbne⟩, ?_⟩
          apply Subtype.ext
          exact hab.symm⟩
  unfold Theta.mixedThetaKernel
  rw [← Equiv.tsum_eq e]
  apply tsum_congr
  intro b
  congr 2
  change y * mixedEmbedding K (x * (b : K)) =
    y * mixedEmbedding K x * mixedEmbedding K (b : K)
  rw [map_mul]
  ring

/-- The cone Mellin integral of a principal multiple of an integral ideal
acquires the expected inverse norm power. -/
theorem coneMellin_spanSingleton_mul_coeIdeal
    (x : K) (hx : x ≠ 0) (𝔟 : Ideal (𝓞 K)) (s : ℂ) :
    (∫ y in mixedEmbedding.fundamentalCone K,
        Theta.mixedThetaKernel K
            (FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
              (𝔟 : FractionalIdeal (𝓞 K)⁰ K)) y *
          (mixedEmbedding.norm y : ℂ) ^ s ∂(mixedMulHaar K)) =
      (mixedEmbedding.norm (mixedEmbedding K x) : ℂ) ^ (-s) *
        ∫ y in mixedEmbedding.fundamentalCone K,
          Theta.idealThetaKernel K 𝔟 y *
            (mixedEmbedding.norm y : ℂ) ^ s ∂(mixedMulHaar K) := by
  let c : mixedEmbedding.mixedSpace K := mixedEmbedding K x
  have hc : mixedEmbedding.norm c ≠ 0 := by
    have hn : Algebra.norm ℚ x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
    change mixedEmbedding.norm (mixedEmbedding K x) ≠ 0
    rw [mixedEmbedding.norm_eq_norm]
    exact_mod_cast abs_ne_zero.mpr hn
  have hcpos : 0 < mixedEmbedding.norm c :=
    (mixedEmbedding.norm_nonneg c).lt_of_ne (Ne.symm hc)
  let F : mixedEmbedding.mixedSpace K → ℂ := fun y ↦
    Theta.idealThetaKernel K 𝔟 y * (mixedEmbedding.norm y : ℂ) ^ s
  have hFunit : ∀ (u : (𝓞 K)ˣ) y, F (u • y) = F y := by
    intro u y
    simp only [F, Theta.idealThetaKernel_unitSMul, Theta.norm_unitSMul]
  have hcancel : (mixedEmbedding.norm c : ℂ) ^ (-s) *
      (mixedEmbedding.norm c : ℂ) ^ s = 1 := by
    rw [← Complex.cpow_add _ _ (by exact_mod_cast hc), neg_add_cancel,
      Complex.cpow_zero]
  have hpoint : ∀ y : mixedEmbedding.mixedSpace K,
      Theta.mixedThetaKernel K
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
            (𝔟 : FractionalIdeal (𝓞 K)⁰ K)) y *
        (mixedEmbedding.norm y : ℂ) ^ s =
      (mixedEmbedding.norm c : ℂ) ^ (-s) * F (y * c) := by
    intro y
    rw [mixedThetaKernel_spanSingleton_mul K x hx, ← Theta.idealThetaKernel_eq_mixed]
    change Theta.idealThetaKernel K 𝔟 (y * c) * (mixedEmbedding.norm y : ℂ) ^ s =
      (mixedEmbedding.norm c : ℂ) ^ (-s) *
        (Theta.idealThetaKernel K 𝔟 (y * c) *
          (mixedEmbedding.norm (y * c) : ℂ) ^ s)
    rw [map_mul mixedEmbedding.norm y c, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (mixedEmbedding.norm_nonneg y) hcpos.le s]
    ring_nf at hcancel ⊢
    rw [hcancel]
    ring
  calc
    (∫ y in mixedEmbedding.fundamentalCone K,
        Theta.mixedThetaKernel K
            (FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
              (𝔟 : FractionalIdeal (𝓞 K)⁰ K)) y *
          (mixedEmbedding.norm y : ℂ) ^ s ∂(mixedMulHaar K))
        = ∫ y in mixedEmbedding.fundamentalCone K,
            (mixedEmbedding.norm c : ℂ) ^ (-s) * F (y * c) ∂(mixedMulHaar K) := by
          exact setIntegral_congr_fun (mixedEmbedding.measurableSet_fundamentalCone K)
            (fun y _ ↦ hpoint y)
    _ = (mixedEmbedding.norm c : ℂ) ^ (-s) *
          ∫ y in mixedEmbedding.fundamentalCone K, F (y * c) ∂(mixedMulHaar K) := by
          rw [integral_const_mul]
    _ = (mixedEmbedding.norm c : ℂ) ^ (-s) *
          ∫ y in mixedEmbedding.fundamentalCone K, F y ∂(mixedMulHaar K) := by
          rw [integral_comp_mulRight_fundamentalCone_eq K c hc F hFunit]
    _ = (mixedEmbedding.norm (mixedEmbedding K x) : ℂ) ^ (-s) *
          ∫ y in mixedEmbedding.fundamentalCone K,
            Theta.idealThetaKernel K 𝔟 y *
              (mixedEmbedding.norm y : ℂ) ^ s ∂(mixedMulHaar K) := by
          rfl

/-- Radial decomposition of the cone Mellin integral for a fractional ideal. -/
theorem coneMellin_mixedThetaKernel_eq_radial
    (I : FractionalIdeal (𝓞 K)⁰ K) (s : ℂ)
    (hh : IntegrableOn
      (fun y ↦ Theta.mixedThetaKernel K I y * (mixedEmbedding.norm y : ℂ) ^ s)
      (mixedEmbedding.fundamentalCone K) (mixedMulHaar K)) :
    (∫ y in mixedEmbedding.fundamentalCone K,
        Theta.mixedThetaKernel K I y * (mixedEmbedding.norm y : ℂ) ^ s
          ∂(mixedMulHaar K)) =
      ∫ r in Set.Ioi (0 : ℝ),
        orbitThetaFrac K I r * (r : ℂ) ^ s * (r : ℝ)⁻¹ ∂volume := by
  rw [setIntegral_cone_eq_radial _ hh]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr ↦ ?_)
  have hr0 : (0 : ℝ) < r := hr
  have hinner :
      (∫ σ in normEqOneSurface K,
          Theta.mixedThetaKernel K I (radialMap K r σ) *
            (mixedEmbedding.norm (radialMap K r σ) : ℂ) ^ s
            ∂(surfaceMeasure K)) =
        orbitThetaFrac K I r * (r : ℂ) ^ s := by
    rw [orbitThetaFrac, ← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_normEqOneSurface (fun σ hσ ↦ ?_)
    rw [norm_radialMap_of_mem r hr0 hσ]
  rw [hinner]

/-- The fractional radial integral is the ordinary Mellin transform of its
orbit-integrated theta function. -/
theorem radialIntegral_orbitThetaFrac_eq_mellin
    (I : FractionalIdeal (𝓞 K)⁰ K) (s : ℂ) :
    (∫ r in Set.Ioi (0 : ℝ),
        orbitThetaFrac K I r * (r : ℂ) ^ s * (r : ℝ)⁻¹ ∂volume) =
      mellin (orbitThetaFrac K I) s := by
  rw [mellin]
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr ↦ ?_)
  have hr0 : (0 : ℝ) < r := hr
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  rw [smul_eq_mul, Complex.ofReal_inv, Complex.cpow_sub _ _ hrne, Complex.cpow_one]
  field_simp

/-- Cone-to-Mellin reduction for an arbitrary fractional ideal. -/
theorem coneMellin_mixedThetaKernel_eq_mellin
    (I : FractionalIdeal (𝓞 K)⁰ K) (s : ℂ)
    (hh : IntegrableOn
      (fun y ↦ Theta.mixedThetaKernel K I y * (mixedEmbedding.norm y : ℂ) ^ s)
      (mixedEmbedding.fundamentalCone K) (mixedMulHaar K)) :
    (∫ y in mixedEmbedding.fundamentalCone K,
        Theta.mixedThetaKernel K I y * (mixedEmbedding.norm y : ℂ) ^ s
          ∂(mixedMulHaar K)) =
      mellin (orbitThetaFrac K I) s := by
  rw [coneMellin_mixedThetaKernel_eq_radial K I s hh,
    radialIntegral_orbitThetaFrac_eq_mellin K I s]

/-- Removing the zero-lattice constant from the completed dual radial theta
recovers the fractional-ideal orbit theta. -/
theorem reducedMellin_radialThetaDual (𝔞 : Ideal (𝓞 K)) (s : ℂ) :
    reducedMellin (radialThetaDual K 𝔞) (surfaceVolume K) s =
      mellin (orbitThetaFrac K (Theta.dualIdeal K 𝔞)) s := by
  unfold reducedMellin radialThetaDual
  simp

/-- On its convergence half-plane, the swapped Mellin continuation is the
cone Mellin integral of the trace-dual fractional ideal. -/
theorem coneMellin_dualIdeal_eq_swappedContinuation
    (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    (∫ y in mixedEmbedding.fundamentalCone K,
        Theta.mixedThetaKernel K (Theta.dualIdeal K 𝔞) y *
          (mixedEmbedding.norm y : ℂ) ^ s ∂(mixedMulHaar K)) =
      mellinContinuation (radialThetaDual K 𝔞) (radialTheta K 𝔞)
        (surfaceVolume K) (surfaceVolume K)
        ((Theta.covolume K 𝔞 : ℂ)⁻¹)⁻¹ 1 s := by
  obtain ⟨c, α, hpair⟩ := exists_isMellinPair_radialTheta (K := K) 𝔞 h𝔞
  have hint := integrable_indicator_mixedThetaKernel_mul_norm_cpow K
    (Theta.dualIdeal K 𝔞) s hs
  rw [integrable_indicator_iff (mixedEmbedding.measurableSet_fundamentalCone K)] at hint
  rw [coneMellin_mixedThetaKernel_eq_mellin K _ s hint,
    ← reducedMellin_radialThetaDual K 𝔞 s,
    ← mellinContinuation_eq hpair.swap (show (1 : ℝ) < s.re by exact_mod_cast hs)]

/-- If the trace-dual fractional ideal is `x𝔟`, its swapped continuation is
the continuation for `𝔟` multiplied by `|N(x)|^{-s}`. -/
theorem swappedContinuation_eq_scaled_idealClassRep
    (𝔞 𝔟 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ 0) (h𝔟 : 𝔟 ≠ 0)
    (x : K) (hx : x ≠ 0)
    (hdual : Theta.dualIdeal K 𝔞 =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
        (𝔟 : FractionalIdeal (𝓞 K)⁰ K))
    {s : ℂ} (hs : 1 < s.re) :
    mellinContinuation (radialThetaDual K 𝔞) (radialTheta K 𝔞)
        (surfaceVolume K) (surfaceVolume K)
        ((Theta.covolume K 𝔞 : ℂ)⁻¹)⁻¹ 1 s =
      (mixedEmbedding.norm (mixedEmbedding K x) : ℂ) ^ (-s) *
        mellinContinuation (radialTheta K 𝔟) (radialThetaDual K 𝔟)
          (surfaceVolume K) (surfaceVolume K)
          ((Theta.covolume K 𝔟 : ℂ)⁻¹) 1 s := by
  have hdualMellin := coneMellin_dualIdeal_eq_swappedContinuation K 𝔞 h𝔞 hs
  have hscale := coneMellin_spanSingleton_mul_coeIdeal K x hx 𝔟 s
  have h𝔟Mellin := ConeMellinBridge.coneMellin_eq_mellinContinuation 𝔟 h𝔟 hs
  calc
    mellinContinuation (radialThetaDual K 𝔞) (radialTheta K 𝔞)
          (surfaceVolume K) (surfaceVolume K)
          ((Theta.covolume K 𝔞 : ℂ)⁻¹)⁻¹ 1 s =
        ∫ y in mixedEmbedding.fundamentalCone K,
          Theta.mixedThetaKernel K (Theta.dualIdeal K 𝔞) y *
            (mixedEmbedding.norm y : ℂ) ^ s ∂(mixedMulHaar K) := hdualMellin.symm
    _ = ∫ y in mixedEmbedding.fundamentalCone K,
          Theta.mixedThetaKernel K
              (FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
                (𝔟 : FractionalIdeal (𝓞 K)⁰ K)) y *
            (mixedEmbedding.norm y : ℂ) ^ s ∂(mixedMulHaar K) := by rw [hdual]
    _ = (mixedEmbedding.norm (mixedEmbedding K x) : ℂ) ^ (-s) *
          ∫ y in mixedEmbedding.fundamentalCone K,
            Theta.idealThetaKernel K 𝔟 y *
              (mixedEmbedding.norm y : ℂ) ^ s ∂(mixedMulHaar K) := hscale
    _ = (mixedEmbedding.norm (mixedEmbedding K x) : ℂ) ^ (-s) *
          mellinContinuation (radialTheta K 𝔟) (radialThetaDual K 𝔟)
            (surfaceVolume K) (surfaceVolume K)
            ((Theta.covolume K 𝔟 : ℂ)⁻¹) 1 s := by rw [h𝔟Mellin]

/-- The scalar identity which converts the reflected theta factor into the
standard completed-zeta factor of the dual ideal class. -/
private theorem completedFactor_rescale
    (A B D Q : ℝ) (hA : 0 < A) (hB : 0 < B) (hD : 0 < D) (hQ : 0 < Q)
    (hrel : Q * B = (A * D)⁻¹) (s : ℂ) :
    (A : ℂ) ^ s * (D : ℂ) ^ (s / 2) *
          ((A * Real.sqrt D : ℝ) : ℂ)⁻¹ * (Q : ℂ) ^ (-(1 - s)) =
      (B : ℂ) ^ (1 - s) * (D : ℂ) ^ ((1 - s) / 2) := by
  have hA0 : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hB0 : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB.ne'
  have hD0 : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD.ne'
  have hQ0 : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  have hsqrt : ((Real.sqrt D : ℝ) : ℂ) = (D : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hD.le]
    norm_num
  have hAQ : A * Q = (B * D)⁻¹ := by
    field_simp [hB.ne', hD.ne']
    field_simp [hA.ne', hD.ne'] at hrel
    ring_nf at hrel ⊢
    exact hrel
  have hAQpow : (A : ℂ) ^ (s - 1) * (Q : ℂ) ^ (s - 1) =
      (B : ℂ) ^ (1 - s) * (D : ℂ) ^ (1 - s) := by
    have hAQc : (A : ℂ) * (Q : ℂ) = (((B * D)⁻¹ : ℝ) : ℂ) := by
      exact_mod_cast hAQ
    rw [← Complex.mul_cpow_ofReal_nonneg hA.le hQ.le,
      hAQc, DedekindZeta.ofReal_inv_cpow (mul_nonneg hB.le hD.le),
      Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hB.le hD.le]
    have hexp : -(s - 1) = 1 - s := by ring
    rw [hexp]
  rw [Complex.ofReal_mul, hsqrt, mul_inv_rev]
  rw [← Complex.cpow_neg_one (A : ℂ),
    ← Complex.cpow_neg (D : ℂ) (1 / 2 : ℂ)]
  rw [show -(1 - s) = s - 1 by ring]
  calc
    (A : ℂ) ^ s * (D : ℂ) ^ (s / 2) *
          ((D : ℂ) ^ (-(1 / 2 : ℂ)) * (A : ℂ) ^ (-1 : ℂ)) *
            (Q : ℂ) ^ (s - 1) =
        ((A : ℂ) ^ s * (A : ℂ) ^ (-1 : ℂ)) *
          ((D : ℂ) ^ (s / 2) * (D : ℂ) ^ (-(1 / 2 : ℂ))) *
            (Q : ℂ) ^ (s - 1) := by ring
    _ = (A : ℂ) ^ (s - 1) * (D : ℂ) ^ ((s - 1) / 2) *
          (Q : ℂ) ^ (s - 1) := by
      rw [← Complex.cpow_add s (-1) hA0,
        ← Complex.cpow_add (s / 2) (-(1 / 2)) hD0]
      ring_nf
    _ = ((A : ℂ) ^ (s - 1) * (Q : ℂ) ^ (s - 1)) *
          (D : ℂ) ^ ((s - 1) / 2) := by ring
    _ = ((B : ℂ) ^ (1 - s) * (D : ℂ) ^ (1 - s)) *
          (D : ℂ) ^ ((s - 1) / 2) := by rw [hAQpow]
    _ = (B : ℂ) ^ (1 - s) *
          ((D : ℂ) ^ (1 - s) * (D : ℂ) ^ ((s - 1) / 2)) := by ring
    _ = (B : ℂ) ^ (1 - s) * (D : ℂ) ^ ((1 - s) / 2) := by
      rw [← Complex.cpow_add (1 - s) ((s - 1) / 2) hD0]
      congr 2
      ring

/-- Norm bookkeeping for a principal presentation of the trace-dual ideal. -/
theorem absNorm_mul_absNorm_eq_inv_discriminant
    (𝔞 𝔟 : Ideal (𝓞 K)) (x : K)
    (hdual : Theta.dualIdeal K 𝔞 =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
        (𝔟 : FractionalIdeal (𝓞 K)⁰ K)) :
    |Algebra.norm ℚ x| * (Ideal.absNorm 𝔟 : ℚ) =
      ((Ideal.absNorm 𝔞 : ℚ) * (NumberField.discr K).natAbs)⁻¹ := by
  have hnorm := congrArg FractionalIdeal.absNorm hdual
  have hdiff : (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℚ) =
      (NumberField.discr K).natAbs := by
    exact_mod_cast NumberField.absNorm_differentIdeal K (𝓞 K)
  simpa [Theta.dualIdeal, Theta.differentFractionalIdeal, map_mul,
    FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.absNorm_span_singleton,
    hdiff] using hnorm.symm

/-- Fractional ideals representing the same ideal class differ by
multiplication by a nonzero principal fractional ideal. -/
theorem exists_eq_spanSingleton_mul_of_mk_eq
    (I J : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hclass : ClassGroup.mk K (Units.mk0 I hI) =
      ClassGroup.mk K (Units.mk0 J hJ)) :
    ∃ x : K, x ≠ 0 ∧ I = FractionalIdeal.spanSingleton (𝓞 K)⁰ x * J := by
  let uI : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 I hI
  let uJ : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 J hJ
  have hprincipal :
      ((uI * uJ⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        Submodule (𝓞 K) K).IsPrincipal := by
    rw [← ClassGroup.mk_eq_one_iff]
    change ClassGroup.mk K (Units.mk0 I hI * (Units.mk0 J hJ)⁻¹) = 1
    rw [map_mul, map_inv, hclass, mul_inv_cancel]
  have hprincipal' : ((I * J⁻¹ : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K).IsPrincipal := by
    simpa only [uI, uJ, Units.val_mul, Units.val_mk0,
      Units.val_inv_eq_inv_val] using hprincipal
  letI : ((I * J⁻¹ : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K).IsPrincipal := hprincipal'
  let x : K := Submodule.IsPrincipal.generator
    ((I * J⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
  have hspan : I * J⁻¹ = FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
    exact FractionalIdeal.eq_spanSingleton_of_principal (I * J⁻¹)
  have hx : x ≠ 0 := by
    intro hx0
    have hzero : I * J⁻¹ = 0 := by
      rw [hspan, hx0, FractionalIdeal.spanSingleton_zero]
    exact (mul_ne_zero hI (inv_ne_zero hJ)) hzero
  refine ⟨x, hx, ?_⟩
  calc
    I = (I * J⁻¹) * J := by rw [mul_assoc, inv_mul_cancel₀ hJ, mul_one]
    _ = FractionalIdeal.spanSingleton (𝓞 K)⁰ x * J := by rw [hspan]

private theorem idealClassRep_ne_zero (c : ClassGroup (𝓞 K)) :
    idealClassRep K c ≠ 0 := by
  unfold idealClassRep
  exact mem_nonZeroDivisors_iff_ne_zero.mp
    (Function.surjInv ClassGroup.mk0_surjective c).2

/-- The trace dual of the chosen representative of `c` is a nonzero principal
multiple of the chosen integral representative of the dual class. -/
theorem exists_dualIdeal_eq_spanSingleton_mul_idealClassRep
    (c : ClassGroup (𝓞 K)) :
    ∃ x : K, x ≠ 0 ∧
      Theta.dualIdeal K (idealClassRep K c) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
          (idealClassRep K (DualClassReindex.dualClassPermutation K c) :
            FractionalIdeal (𝓞 K)⁰ K) := by
  let 𝔞 : Ideal (𝓞 K) := idealClassRep K c
  let d : ClassGroup (𝓞 K) := DualClassReindex.dualClassPermutation K c
  let 𝔟 : Ideal (𝓞 K) := idealClassRep K d
  have h𝔞 : 𝔞 ≠ 0 := idealClassRep_ne_zero K c
  have h𝔟 : 𝔟 ≠ 0 := idealClassRep_ne_zero K d
  have hdual : Theta.dualIdeal K 𝔞 ≠ 0 := by
    unfold Theta.dualIdeal
    apply inv_ne_zero
    apply mul_ne_zero
    · exact_mod_cast (FractionalIdeal.coeIdeal_ne_zero).mpr h𝔞
    · exact_mod_cast (FractionalIdeal.coeIdeal_ne_zero).mpr differentIdeal_ne_bot
  have h𝔟frac : (𝔟 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.coeIdeal_ne_zero).mpr h𝔟
  have hclass : ClassGroup.mk K (Units.mk0 (Theta.dualIdeal K 𝔞) hdual) =
      ClassGroup.mk K (Units.mk0 (𝔟 : FractionalIdeal (𝓞 K)⁰ K) h𝔟frac) := by
    have hd := DualClassReindex.class_dualIdeal_idealClassRep K c
    have h𝔟mk : ClassGroup.mk K
        (Units.mk0 (𝔟 : FractionalIdeal (𝓞 K)⁰ K) h𝔟frac) = d := by
      rw [show Units.mk0 (𝔟 : FractionalIdeal (𝓞 K)⁰ K) h𝔟frac =
        FractionalIdeal.mk0 K
          ⟨𝔟, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔟⟩ from rfl,
        ClassGroup.mk_mk0]
      exact Function.surjInv_eq ClassGroup.mk0_surjective d
    simpa only [𝔞, d, 𝔟, h𝔟mk] using hd
  simpa only [𝔞, d, 𝔟] using
    exists_eq_spanSingleton_mul_of_mk_eq K
      (Theta.dualIdeal K 𝔞) (𝔟 : FractionalIdeal (𝓞 K)⁰ K)
      hdual h𝔟frac hclass

/-- The continued partial completed zeta attached to an ideal is the reflected
partial completed zeta of any integral representative of its trace-dual
fractional ideal. -/
theorem completedPartialZetaContinuation_reflection_of_dual
    (𝔞 𝔟 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ 0) (h𝔟 : 𝔟 ≠ 0)
    (x : K) (hx : x ≠ 0)
    (hdual : Theta.dualIdeal K 𝔞 =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
        (𝔟 : FractionalIdeal (𝓞 K)⁰ K))
    (s : ℂ) (hs : s.re < 0) :
    GlobalContinuation.completedPartialZetaContinuation K 𝔞 s =
      GlobalContinuation.completedPartialZetaContinuation K 𝔟 (1 - s) := by
  have hs₀ : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hs₁ : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have ht : 1 < (1 - s).re := by
    change 1 < 1 - s.re
    linarith
  obtain ⟨c, α, hpair⟩ := exists_isMellinPair_radialTheta (K := K) 𝔞 h𝔞
  have href := TraceEuclidean.V15AnalyticMellin.mellinContinuation_reflection
    hpair s hs₀ hs₁
  simp only [Complex.ofReal_one, inv_inv] at href
  have hswap := swappedContinuation_eq_scaled_idealClassRep K
    𝔞 𝔟 h𝔞 h𝔟 x hx hdual ht
  simp only [inv_inv] at hswap
  have hAposNat : 0 < Ideal.absNorm 𝔞 :=
    Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞)
  have hBposNat : 0 < Ideal.absNorm 𝔟 :=
    Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mpr h𝔟)
  have hApos : 0 < (Ideal.absNorm 𝔞 : ℝ) := by exact_mod_cast hAposNat
  have hBpos : 0 < (Ideal.absNorm 𝔟 : ℝ) := by exact_mod_cast hBposNat
  have hDposNat : 0 < (NumberField.discr K).natAbs :=
    Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)
  have hDpos : 0 < ((NumberField.discr K).natAbs : ℝ) := by
    exact_mod_cast hDposNat
  have hQpos : 0 < mixedEmbedding.norm (mixedEmbedding K x) := by
    rw [mixedEmbedding.norm_eq_norm]
    exact_mod_cast abs_pos.mpr ((Algebra.norm_ne_zero_iff (R := ℚ)).mpr hx)
  have hDreal : ((NumberField.discr K).natAbs : ℝ) =
      |(NumberField.discr K : ℝ)| := by
    norm_num
  have hnormQ :
      mixedEmbedding.norm (mixedEmbedding K x) * (Ideal.absNorm 𝔟 : ℝ) =
        ((Ideal.absNorm 𝔞 : ℝ) *
          ((NumberField.discr K).natAbs : ℝ))⁻¹ := by
    rw [mixedEmbedding.norm_eq_norm]
    have hrat := absNorm_mul_absNorm_eq_inv_discriminant K 𝔞 𝔟 x hdual
    have hcast := congrArg (fun q : ℚ ↦ (q : ℝ)) hrat
    norm_num at hcast
    rw [Rat.cast_abs, hDreal, mul_inv_rev]
    exact hcast
  have hDcomplex : ((((NumberField.discr K).natAbs : ℝ) : ℂ)) =
      (((|NumberField.discr K| : ℤ) : ℂ)) := by
    rw [Complex.ofReal_natCast]
    rw [← Int.natCast_natAbs]
    norm_num
  have hcoeff := completedFactor_rescale
    (Ideal.absNorm 𝔞 : ℝ) (Ideal.absNorm 𝔟 : ℝ)
    ((NumberField.discr K).natAbs : ℝ)
    (mixedEmbedding.norm (mixedEmbedding K x))
    hApos hBpos hDpos hQpos hnormQ s
  rw [hDcomplex, hDreal] at hcoeff
  have hcoeff' :
      (Ideal.absNorm 𝔞 : ℂ) ^ s *
            (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2)) *
            (Theta.covolume K 𝔞 : ℂ)⁻¹ *
            (mixedEmbedding.norm (mixedEmbedding K x) : ℂ) ^ (-(1 - s)) =
        (Ideal.absNorm 𝔟 : ℂ) ^ (1 - s) *
          (((|NumberField.discr K| : ℤ) : ℂ) ^ ((1 - s) / 2)) := by
    simpa only [Theta.covolume, Complex.ofReal_natCast, Nat.cast_ofNat] using hcoeff
  unfold GlobalContinuation.completedPartialZetaContinuation
  rw [href, hswap]
  calc
    _ =
        (1 / (Units.torsionOrder K : ℂ)) *
          ((Ideal.absNorm 𝔞 : ℂ) ^ s *
            (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2)) *
            (Theta.covolume K 𝔞 : ℂ)⁻¹ *
            (mixedEmbedding.norm (mixedEmbedding K x) : ℂ) ^ (-(1 - s))) *
          mellinContinuation (radialTheta K 𝔟) (radialThetaDual K 𝔟)
            (surfaceVolume K) (surfaceVolume K)
            ((Theta.covolume K 𝔟 : ℂ)⁻¹) 1 (1 - s) := by ring
    _ = (1 / (Units.torsionOrder K : ℂ)) *
          ((Ideal.absNorm 𝔟 : ℂ) ^ (1 - s) *
            (((|NumberField.discr K| : ℤ) : ℂ) ^ ((1 - s) / 2))) *
          mellinContinuation (radialTheta K 𝔟) (radialThetaDual K 𝔟)
            (surfaceVolume K) (surfaceVolume K)
            ((Theta.covolume K 𝔟 : ℂ)⁻¹) 1 (1 - s) := by rw [hcoeff']
    _ = (1 / (Units.torsionOrder K : ℂ)) *
          (Ideal.absNorm 𝔟 : ℂ) ^ (1 - s) *
          (((|NumberField.discr K| : ℤ) : ℂ) ^ ((1 - s) / 2)) *
          mellinContinuation (radialTheta K 𝔟) (radialThetaDual K 𝔟)
            (surfaceVolume K) (surfaceVolume K)
            ((Theta.covolume K 𝔟 : ℂ)⁻¹) 1 (1 - s) := by ring

/-- On the left half-plane, summing the reflected partial identities and
reindexing by trace duality gives the completed-zeta functional equation. -/
theorem completedZetaContinuation_reflection_left
    (s : ℂ) (hs : s.re < 0) :
    GlobalContinuation.completedZetaContinuation K s =
      GlobalContinuation.completedZetaContinuation K (1 - s) := by
  classical
  unfold GlobalContinuation.completedZetaContinuation
  calc
    (∑ c : ClassGroup (𝓞 K),
        GlobalContinuation.completedPartialZetaContinuation K
          (idealClassRep K c) s) =
      ∑ c : ClassGroup (𝓞 K),
        GlobalContinuation.completedPartialZetaContinuation K
          (idealClassRep K (DualClassReindex.dualClassPermutation K c)) (1 - s) := by
        apply Finset.sum_congr rfl
        intro c _
        obtain ⟨x, hx, hdual⟩ :=
          exists_dualIdeal_eq_spanSingleton_mul_idealClassRep K c
        exact completedPartialZetaContinuation_reflection_of_dual K
          (idealClassRep K c)
          (idealClassRep K (DualClassReindex.dualClassPermutation K c))
          (idealClassRep_ne_zero K c)
          (idealClassRep_ne_zero K (DualClassReindex.dualClassPermutation K c))
          x hx hdual s hs
    _ = ∑ c : ClassGroup (𝓞 K),
        GlobalContinuation.completedPartialZetaContinuation K
          (idealClassRep K c) (1 - s) :=
      DualClassReindex.sum_dualClassPermutation K
        (fun c ↦ GlobalContinuation.completedPartialZetaContinuation K
          (idealClassRep K c) (1 - s))

/-- The pole-removed completed zeta satisfies the functional equation on the
open left half-plane. -/
theorem completedZetaPoleRemoved_reflection_left
    (s : ℂ) (hs : s.re < 0) :
    GlobalContinuation.completedZetaPoleRemoved K s =
      GlobalContinuation.completedZetaPoleRemoved K (1 - s) := by
  have hs₀ : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hs₁ : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have ht₀ : 1 - s ≠ 0 := by
    intro h
    apply hs₁
    linear_combination -h
  have ht₁ : 1 - s ≠ 1 := by
    intro h
    apply hs₀
    linear_combination -h
  rw [GlobalContinuation.completedZetaPoleRemoved_eq K s hs₀ hs₁,
    GlobalContinuation.completedZetaPoleRemoved_eq K (1 - s) ht₀ ht₁,
    completedZetaContinuation_reflection_left K s hs]
  ring

/-- The completed Dedekind zeta constructed from the number-field theta
integral satisfies its global functional equation, including the two former
pole locations. -/
theorem completedZetaPoleRemoved_reflection (s : ℂ) :
    GlobalContinuation.completedZetaPoleRemoved K s =
      GlobalContinuation.completedZetaPoleRemoved K (1 - s) := by
  have hF := GlobalContinuation.completedZetaPoleRemoved_analyticOn K
  have hFref : AnalyticOnNhd ℂ
      (fun z : ℂ ↦ GlobalContinuation.completedZetaPoleRemoved K (1 - z))
      Set.univ := by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    intro z
    exact ((Complex.analyticOnNhd_univ_iff_differentiable.mp hF) (1 - z)).comp z
      (by fun_prop)
  have hfun : GlobalContinuation.completedZetaPoleRemoved K =
      (fun z : ℂ ↦ GlobalContinuation.completedZetaPoleRemoved K (1 - z)) := by
    apply AnalyticOnNhd.eq_of_eventuallyEq hF hFref (z₀ := (-1 : ℂ))
    filter_upwards [
      (Complex.continuous_re.isOpen_preimage _ isOpen_Iio).mem_nhds
        (by norm_num : (-1 : ℂ) ∈ {z : ℂ | z.re < 0})] with z hz
    exact completedZetaPoleRemoved_reflection_left K z hz
  exact congrFun hfun s

/-- Away from the two original poles, the meromorphic completed-zeta
continuation itself satisfies `Λ_K(s) = Λ_K(1-s)`. -/
theorem completedZetaContinuation_reflection
    (s : ℂ) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    GlobalContinuation.completedZetaContinuation K s =
      GlobalContinuation.completedZetaContinuation K (1 - s) := by
  have ht₀ : 1 - s ≠ 0 := by
    intro h
    apply hs₁
    linear_combination -h
  have ht₁ : 1 - s ≠ 1 := by
    intro h
    apply hs₀
    linear_combination -h
  have href := completedZetaPoleRemoved_reflection K s
  rw [GlobalContinuation.completedZetaPoleRemoved_eq K s hs₀ hs₁,
    GlobalContinuation.completedZetaPoleRemoved_eq K (1 - s) ht₀ ht₁] at href
  have hfactor : (1 - s) * (1 - s - 1) = s * (s - 1) := by ring
  rw [hfactor] at href
  exact mul_left_cancel₀ (mul_ne_zero hs₀ (sub_ne_zero.mpr hs₁)) href

end
end DedekindZeta.FractionalIdealRescaling
