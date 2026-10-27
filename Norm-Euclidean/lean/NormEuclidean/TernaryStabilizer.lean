import NormEuclidean.HyperbolicSpinorMap
import NormEuclidean.UnaryClassNumber

/-!
# The proper pointwise stabilizer of a hyperbolic plane in dimension three
-/

noncomputable section

namespace NormEuclidean.TernaryStabilizer

open ProperSpinor

variable {F E : Type*} [Field F] [AddCommGroup E] [Module F E]
  [FiniteDimensional F E]

/-- A determinant-one automorphism of a one-dimensional vector space is the identity. -/
theorem line_eq_one (hdim : Module.finrank F E = 1) (g : E ≃ₗ[F] E)
    (hdet : g.det = 1) : g = 1 := by
  apply LinearEquiv.ext
  intro x
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim hx (g x)
  have hlin : g.toLinearMap = c • (LinearMap.id : E →ₗ[F] E) := by
    ext y
    obtain ⟨b, rfl⟩ := exists_smul_eq_of_finrank_eq_one hdim hx y
    simp only [LinearEquiv.coe_coe, map_smul, ← hc, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq, smul_smul]
  have hc1 : c = 1 := by
    have hd := congrArg (fun a : Fˣ ↦ (a : F)) hdet
    rw [LinearEquiv.coe_det, hlin, LinearMap.det_smul, LinearMap.det_id,
      hdim, pow_one, mul_one] at hd
    exact hd
  simpa [hc1] using hc.symm

/-- Fixing both hyperbolic basis vectors leaves no proper transformation on a line. -/
theorem eq_one_of_fix_basis (Q : QuadraticForm F E) (hdim : Module.finrank F E = 1)
    (g : properGroup (Hyperbolic.form Q))
    (he : g.1.1 Hyperbolic.e = Hyperbolic.e)
    (hf : g.1.1 Hyperbolic.f = Hyperbolic.f) : g = 1 := by
  let phi : Hyperbolic.Isometry Q Q (⊤ : Submodule (⊤ : Subring F) E) ⊤ :=
    { toLinearEquiv := g.1.1
      q_eq := g.1.2
      mem_iff := fun z ↦ by simp [Hyperbolic.Mem] }
  let r := phi.restrict he hf
  let a : ambientGroup Q := ⟨r.toLinearEquiv, r.q_eq⟩
  have hblock : HyperbolicSpinorMap.ambientMap Q a = g.1 := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    have hz : z = Hyperbolic.embed z.1 + z.2.1 • Hyperbolic.e +
        z.2.2 • Hyperbolic.f := by
      ext <;> simp [Hyperbolic.embed, Hyperbolic.e, Hyperbolic.f]
    have hzmap := congrArg g.1.1 hz
    rw [map_add, map_add, map_smul, map_smul, he, hf] at hzmap
    have hb := phi.map_embed he hf z.1
    change g.1.1 (Hyperbolic.embed z.1) =
      Hyperbolic.embed (r.toLinearEquiv z.1) at hb
    rw [hb] at hzmap
    simpa [HyperbolicSpinorMap.ambientMap_apply, a, Hyperbolic.embed,
      Hyperbolic.e, Hyperbolic.f] using hzmap.symm
  have hd : r.toLinearEquiv.det = 1 := by
    change determinantHom Q a = 1
    rw [← HyperbolicSpinorMap.determinant_map Q a, hblock]
    exact g.2
  have hr := line_eq_one hdim r.toLinearEquiv hd
  have ha : a = 1 := Subtype.ext hr
  apply Subtype.ext
  rw [← hblock, ha, map_one]
  rfl

end NormEuclidean.TernaryStabilizer
