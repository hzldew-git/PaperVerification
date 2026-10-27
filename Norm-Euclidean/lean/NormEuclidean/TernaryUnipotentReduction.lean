import NormEuclidean.TernaryStabilizer
import NormEuclidean.TernaryUnipotentDilation

/-!
# Gauss reduction of ternary proper isometries by actual unipotents
-/

noncomputable section

namespace NormEuclidean.TernaryUnipotentReduction

open ProperSpinor SpinorBaseChange HyperbolicUnipotentGroup QuadraticMap

variable {F E : Type*} [Field F] [CharZero F] [AddCommGroup E] [Module F E]
  [FiniteDimensional F E] (Q : QuadraticForm F E) (hQ : Q.polarBilin.Nondegenerate)
  (hA : Q.Anisotropic)

/-- An isotropic vector with nonzero first hyperbolic coordinate is reduced exactly. -/
theorem upper_normalize (z : Hyperbolic F E) (hz : Hyperbolic.form Q z = 0)
    (ha : z.2.1 ≠ 0) :
    (upper Q hQ hA (z.2.1⁻¹ • z.1)).1.1 z = z.2.1 • Hyperbolic.e := by
  rw [HyperbolicUnipotent.element_apply]
  have hb := Hyperbolic.descent_identity Q z (z.2.1⁻¹ • z.1) hz ha
  simp only [sub_self, Q.map_zero, mul_zero, neg_zero] at hb
  apply Prod.ext
  · simp [Hyperbolic.transvection, smul_smul, mul_inv_cancel₀ ha, Hyperbolic.e]
  · apply Prod.ext
    · simp [Hyperbolic.transvection, Hyperbolic.e]
    · simpa [Hyperbolic.e] using hb

/-- A proper isometry carrying the first axis to a scalar multiple can be reduced to a dilation. -/
theorem reduce_axis (hdim : Module.finrank F E = 1)
    (g : properGroup (Hyperbolic.form Q)) (a : Fˣ)
    (he : g.1.1 Hyperbolic.e = (a : F) • Hyperbolic.e) :
    ∃ r ∈ generated Q hQ hA, r * g = hyperbolicCorrection Q hQ a := by
  let w := g.1.1 Hyperbolic.f
  have hp : polar (Hyperbolic.form Q) (g.1.1 Hyperbolic.e) w = 1 := by
    dsimp [w]
    rw [polar, ← map_add, g.1.2, g.1.2, g.1.2]
    simp [Hyperbolic.q, Hyperbolic.e, Hyperbolic.f]
  have hp' : (a : F) * w.2.2 = 1 := by
    rw [he, polar_smul_left, HyperbolicUnipotent.polar_apply] at hp
    simpa [Hyperbolic.e] using hp
  have hb : w.2.2 = (a : F)⁻¹ := by
    apply mul_left_cancel₀ a.ne_zero
    rw [hp', mul_inv_cancel₀ a.ne_zero]
  let r := lower Q hQ hA ((a : F) • w.1)
  let k := r * g
  have hke : k.1.1 Hyperbolic.e = (a : F) • Hyperbolic.e := by
    change r.1.1 (g.1.1 Hyperbolic.e) = _
    rw [he]
    simp [r, lower, OppositeHyperbolicUnipotent.element_apply, Hyperbolic.e]
  have hkv : (k.1.1 Hyperbolic.f).1 = 0 := by
    change (r.1.1 w).1 = 0
    simp [r, lower, OppositeHyperbolicUnipotent.element_apply, hb, smul_smul,
      inv_mul_cancel₀ a.ne_zero]
  have hkb : (k.1.1 Hyperbolic.f).2.2 = (a : F)⁻¹ := by
    change (r.1.1 w).2.2 = _
    simpa [r, lower, OppositeHyperbolicUnipotent.element_apply] using hb
  have hka : (k.1.1 Hyperbolic.f).2.1 = 0 := by
    have hkq := k.1.2 Hyperbolic.f
    have hf0 : Hyperbolic.form Q (Hyperbolic.f : Hyperbolic F E) = 0 := by
      simp [Hyperbolic.q, Hyperbolic.f]
    rw [hf0] at hkq
    change Q (k.1.1 Hyperbolic.f).1 +
      (k.1.1 Hyperbolic.f).2.1 * (k.1.1 Hyperbolic.f).2.2 = 0 at hkq
    rw [hkv, Q.map_zero, zero_add, hkb] at hkq
    exact (mul_eq_zero.mp hkq).resolve_right (inv_ne_zero a.ne_zero)
  have hkf : k.1.1 Hyperbolic.f = (a : F)⁻¹ • Hyperbolic.f := by
    have hc : k.1.1 Hyperbolic.f = (0, 0, (a : F)⁻¹) :=
      Prod.ext hkv (Prod.ext hka hkb)
    simpa [Hyperbolic.f] using hc
  let d := HyperbolicAbelianization.correctionHom Q hQ
  have hm : d (a⁻¹) * k = 1 := by
    apply TernaryStabilizer.eq_one_of_fix_basis Q hdim
    · change (d (a⁻¹)).1.1 (k.1.1 Hyperbolic.e) = _
      rw [hke]
      simp [d, HyperbolicAbelianization.correctionHom,
        HyperbolicAbelianization.correction_apply, Hyperbolic.e]
    · change (d (a⁻¹)).1.1 (k.1.1 Hyperbolic.f) = _
      rw [hkf]
      simp [d, HyperbolicAbelianization.correctionHom,
        HyperbolicAbelianization.correction_apply, Hyperbolic.f]
  have hk : k = d a := by
    have hh := congrArg (fun t ↦ d a * t) hm
    simpa only [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul, mul_one] using hh
  exact ⟨r, lower_mem Q hQ hA _, hk⟩

/-- Every ternary proper isometry reduces to one dilation by a finite unipotent word. -/
theorem exists_reduction (hdim : Module.finrank F E = 1) (u : E) (hu : Q u ≠ 0)
    (g : properGroup (Hyperbolic.form Q)) :
    ∃ r ∈ generated Q hQ hA, ∃ a : Fˣ, r * g = hyperbolicCorrection Q hQ a := by
  have hfirst : ∃ r ∈ generated Q hQ hA,
      ((r * g).1.1 Hyperbolic.e).2.1 ≠ 0 := by
    by_cases ha : (g.1.1 Hyperbolic.e).2.1 ≠ 0
    · exact ⟨1, (generated Q hQ hA).one_mem, by simpa using ha⟩
    · have ha0 := not_ne_iff.mp ha
      have hv : (g.1.1 Hyperbolic.e).1 = 0 := by
        apply hA
        have h := g.1.2 Hyperbolic.e
        have he0 : Hyperbolic.form Q (Hyperbolic.e : Hyperbolic F E) = 0 := by
          simp [Hyperbolic.q, Hyperbolic.e]
        rw [he0] at h
        change Q (g.1.1 Hyperbolic.e).1 +
          (g.1.1 Hyperbolic.e).2.1 * (g.1.1 Hyperbolic.e).2.2 = 0 at h
        simpa only [ha0, zero_mul, add_zero] using h
      have hb : (g.1.1 Hyperbolic.e).2.2 ≠ 0 := by
        intro hb0
        have hz : g.1.1 Hyperbolic.e = 0 := by ext <;> simp [hv, ha0, hb0]
        have he0 := g.1.1.injective (hz.trans (map_zero g.1.1).symm)
        have hone : (1 : F) = 0 := congrArg (fun z : Hyperbolic F E ↦ z.2.1) he0
        exact one_ne_zero hone
      refine ⟨lower Q hQ hA u, lower_mem Q hQ hA u, ?_⟩
      change ((lower Q hQ hA u).1.1 (g.1.1 Hyperbolic.e)).2.1 ≠ 0
      simpa [lower, OppositeHyperbolicUnipotent.element_apply, hv, ha0] using
        neg_ne_zero.mpr (mul_ne_zero hb hu)
  obtain ⟨r, hr, ha⟩ := hfirst
  let z := (r * g).1.1 Hyperbolic.e
  have hz : Hyperbolic.form Q z = 0 := by
    simpa [z, Hyperbolic.q, Hyperbolic.e] using (r * g).1.2 Hyperbolic.e
  let s := upper Q hQ hA (z.2.1⁻¹ • z.1)
  let a : Fˣ := Units.mk0 z.2.1 ha
  have he : (s * (r * g)).1.1 Hyperbolic.e = (a : F) • Hyperbolic.e :=
    upper_normalize Q hQ hA z hz ha
  obtain ⟨t, ht, hta⟩ := reduce_axis Q hQ hA hdim (s * (r * g)) a he
  refine ⟨t * s * r, (generated Q hQ hA).mul_mem
    ((generated Q hQ hA).mul_mem ht (upper_mem Q hQ hA _)) hr, a, ?_⟩
  simpa only [mul_assoc] using hta

end NormEuclidean.TernaryUnipotentReduction
