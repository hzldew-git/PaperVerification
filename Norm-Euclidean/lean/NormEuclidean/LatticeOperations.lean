import NormEuclidean.ContentMembership
import NormEuclidean.ContentFunctoriality
import NormEuclidean.ContentCoordinates
import NormEuclidean.NumberField

/-!
# Total lattice content and the hyperbolic lattice

These wrappers expose the general content calculus directly on the finite,
full integral lattice structure used by the manuscript-level endpoints.
-/

namespace NormEuclidean

open scoped nonZeroDivisors

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K} {Q : QuadraticForm K V}

namespace Lattice

/-- Adjoin the standard integral hyperbolic plane. -/
def hyperbolic (L : Lattice R Q) : Lattice R (Hyperbolic.form Q) where
  carrier := Hyperbolic.submodule L.carrier
  finite := GeneralContent.hyperbolicSubmodule_fg L.carrier L.finite
  full := Hyperbolic.submodule_full L.carrier L.full
  integral := Hyperbolic.submodule_integral Q L.carrier L.integral

variable [IsFractionRing R K]

/-- The manuscript's total content ideal, including its zero convention. -/
noncomputable def content (L : Lattice R Q) (x : V) : FractionalIdeal R⁰ K :=
  GeneralContent.contentIdeal L.carrier L.finite x

@[simp] theorem content_zero (L : Lattice R Q) : L.content (0 : V) = 0 :=
  GeneralContent.contentIdeal_zero L.carrier L.finite

@[simp] theorem content_eq_zero_iff (L : Lattice R Q) (x : V) :
    L.content x = 0 ↔ x = 0 :=
  GeneralContent.contentIdeal_eq_zero_iff L.carrier L.finite L.full x

theorem mem_ideal_smul_iff_content_le [IsDedekindDomain R]
    (L : Lattice R Q) (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) (x : V) :
    x ∈ (I : Submodule R K) • L.carrier ↔ L.content x ≤ I :=
  GeneralContent.mem_ideal_smul_iff_content_le L.carrier L.finite L.full I hI x

theorem content_smul [IsDedekindDomain R] (L : Lattice R Q) (a : K) (x : V) :
    L.content (a • x) = FractionalIdeal.spanSingleton R⁰ a * L.content x :=
  GeneralContent.contentIdeal_smul L.carrier L.finite a x

end Lattice

variable [NumberField K] (Q)

/-- Lemma 2.4 using the global, total content function of Proposition 2.1. -/
theorem numberField_norm_descent_total_content
    (L : Lattice (integerSubring K) Q)
    (hA : Q.Anisotropic) (hE : HasNumberFieldApproximation Q L.carrier)
    {z : Hyperbolic K V} (hz : Hyperbolic.Mem L.carrier z) (hz0 : z ≠ 0)
    (hiso : Hyperbolic.q Q z = 0) :
    ∃ g : Hyperbolic.Aut (Q := Q) L.carrier, ∃ c : K,
      c ∈ integerSubring K ∧ c ≠ 0 ∧ g z = c • (Hyperbolic.e : Hyperbolic K V) ∧
      L.hyperbolic.content z = FractionalIdeal.spanSingleton (integerSubring K)⁰ c := by
  obtain ⟨g, c, hc, hc0, hg, hfrac, _, hcontent⟩ :=
    numberField_norm_descent Q L hA hE hz hz0 hiso
  refine ⟨g, c, hc, hc0, hg, ?_⟩
  change GeneralContent.contentIdeal (Hyperbolic.submodule L.carrier)
    (GeneralContent.hyperbolicSubmodule_fg L.carrier L.finite) z = _
  rw [GeneralContent.contentIdeal_hyperbolic L.carrier L.finite z hz0 hfrac]
  exact hcontent

end NormEuclidean
