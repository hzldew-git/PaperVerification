import NormEuclidean.NumberField
import NormEuclidean.HyperbolicModule
import NormEuclidean.ScalarExtension

/-!
# Lemma 3.1 (reference manuscript) with integral-module isometries

This endpoint starts and ends with isometries of the actual integral
modules. The input is an R-linear equivalence on `L' × R × R` and
`L × R × R`, preserving `Q(v)+a*b`. Its ambient extension is proved
using full span and fraction-field localization, not assumed.
-/

namespace NormEuclidean

open Hyperbolic

variable {K V W : Type*} [Field K] [NumberField K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable (Q : QuadraticForm K V) (Q' : QuadraticForm K W)

/-- Lemma 3.1 (reference manuscript), stated using integral module isometries throughout.
`L` is the norm-Euclidean target. Neither lattice is assumed free. -/
theorem numberField_hyperbolic_cancellation_from_module
    (L : Lattice (integerSubring K) Q) (L' : Lattice (integerSubring K) Q')
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    (φ : (L'.carrier × integerSubring K × integerSubring K) ≃ₗ[integerSubring K]
      (L.carrier × integerSubring K × integerSubring K))
    (hφ : ∀ z, productQ Q L.carrier (φ z) = productQ Q' L'.carrier z) :
    ∃ ψ : L'.carrier ≃ₗ[integerSubring K] L.carrier,
      ∀ v : L'.carrier, Q (ψ v : V) = Q' (v : W) := by
  let ψ := (moduleEquivProduct L'.carrier).trans
    (φ.trans (moduleEquivProduct L.carrier).symm)
  have hψ : ∀ z : submodule L'.carrier,
      form Q (ψ z : Hyperbolic K V) = form Q' (z : Hyperbolic K W) := by
    intro z
    simpa only [ψ, LinearEquiv.trans_apply, form_moduleEquivProduct_symm,
      LinearEquiv.apply_symm_apply, ← productQ_moduleEquivProduct] using
      hφ (moduleEquivProduct L'.carrier z)
  let Ψ := ScalarExtension.isometry (form Q') (form Q)
    (submodule L'.carrier) (submodule L.carrier)
    (submodule_full L'.carrier L'.full) (submodule_full L.carrier L.full) ψ hψ
  let Φ : Isometry Q' Q L'.carrier L.carrier := {
    toLinearEquiv := Ψ.toLinearEquiv
    q_eq := Ψ.q_eq
    mem_iff := Ψ.mem_iff }
  obtain ⟨g⟩ := norm_euclidean_cancellation (numberFieldNorm K) L.integral hA hE Φ
  exact ⟨g.toModuleEquiv, g.toModuleEquiv_q⟩

end NormEuclidean
