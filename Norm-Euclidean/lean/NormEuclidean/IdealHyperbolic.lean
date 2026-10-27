import NormEuclidean.FractionalIdealLattice
import NormEuclidean.AllPlaceGenus
import Mathlib.LinearAlgebra.Prod

/-!
# Actual ideal hyperbolic lattices

The plane associated with a nonzero fractional ideal `I` is `I × I⁻¹`, with
quadratic form `x * y`. Its orthogonal sum with a lattice uses the existing
ambient hyperbolic space. The construction does not assume that `I` is principal.
-/

noncomputable section

namespace NormEuclidean.IdealHyperbolic

open scoped nonZeroDivisors
open FractionalIdealLattice

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K} [IsFractionRing R K] [IsDedekindDomain R]
variable {Q : QuadraticForm K V}

/-- The split binary quadratic form with the manuscript's normalization `Q(x,y)=xy`. -/
def planeForm : QuadraticForm K (K × K) :=
  QuadraticMap.linMulLin (LinearMap.fst K K K) (LinearMap.snd K K K)

@[simp] theorem planeForm_apply (z : K × K) : planeForm z = z.1 * z.2 := rfl

/-- The actual ideal hyperbolic plane; both summands may be nonprincipal. -/
def plane (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) : Lattice R planeForm where
  carrier := (I : Submodule R K).prod ((I⁻¹ : FractionalIdeal R⁰ K) : Submodule R K)
  finite := (fg I).prod (fg I⁻¹)
  full := by
    change Submodule.span K ((I : Set K) ×ˢ ((I⁻¹ : FractionalIdeal R⁰ K) : Set K)) = ⊤
    rw [Submodule.span_prod_eq K I.zero_mem (I⁻¹).zero_mem,
      FractionalIdealLattice.full I hI, FractionalIdealLattice.full I⁻¹ (inv_ne_zero hI)]
    exact (Submodule.prod_eq_top_iff K K K).mpr ⟨rfl, rfl⟩
  integral := by
    intro z hz
    apply (FractionalIdealLattice.mem_one_iff _).mp
    have h := FractionalIdeal.mul_mem_mul hz.1 hz.2
    rwa [mul_inv_cancel₀ hI] at h

/-- The integral module underlying `L` orthogonally summed with the ideal plane. -/
def submodule (L : Submodule R V) (I : FractionalIdeal R⁰ K) :
    Submodule R (Hyperbolic K V) :=
  L.prod ((I : Submodule R K).prod ((I⁻¹ : FractionalIdeal R⁰ K) : Submodule R K))

omit [IsDedekindDomain R] in
@[simp] theorem mem_submodule (L : Submodule R V) (I : FractionalIdeal R⁰ K)
    (z : Hyperbolic K V) :
    z ∈ submodule L I ↔ z.1 ∈ L ∧ z.2.1 ∈ I ∧ z.2.2 ∈ I⁻¹ := Iff.rfl

/-- The full norm-integral orthogonal sum with an ideal hyperbolic plane. -/
def lattice (L : Lattice R Q) (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) :
    Lattice R (Hyperbolic.form Q) where
  carrier := submodule L.carrier I
  finite := L.finite.prod (plane I hI).finite
  full := by
    change Submodule.span K ((L.carrier : Set V) ×ˢ ((plane I hI).carrier : Set (K × K))) = ⊤
    rw [Submodule.span_prod_eq K L.carrier.zero_mem (plane I hI).carrier.zero_mem,
      L.full, (plane I hI).full]
    exact (Submodule.prod_eq_top_iff K V (K × K)).mpr ⟨rfl, rfl⟩
  integral := by
    intro z hz
    exact R.add_mem (L.integral _ hz.1) ((plane I hI).integral z.2 hz.2)

omit [IsDedekindDomain R] in
/-- The unit ideal recovers the existing standard hyperbolic module. -/
@[simp] theorem submodule_one (L : Submodule R V) :
    submodule L 1 = Hyperbolic.submodule L := by
  ext z
  simp only [mem_submodule, inv_one, FractionalIdealLattice.mem_one_iff,
    Hyperbolic.mem_submodule, Hyperbolic.Mem]

/-- The unit ideal recovers the existing standard hyperbolic lattice. -/
theorem lattice_one (L : Lattice R Q) : lattice L 1 one_ne_zero = L.hyperbolic := by
  have hext (A B : Lattice R (Hyperbolic.form Q)) (h : A.carrier = B.carrier) : A = B := by
    cases A
    cases B
    cases h
    rfl
  exact hext _ _ (submodule_one L.carrier)

/-- The content of the first standard isotropic direction is the inverse ideal. -/
theorem content_e (L : Lattice R Q) (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) :
    (lattice L I hI).content (Hyperbolic.e : Hyperbolic K V) = I⁻¹ := by
  change GeneralContent.contentIdeal
    (L.carrier.prod ((I : Submodule R K).prod ((I⁻¹ : FractionalIdeal R⁰ K) : Submodule R K)))
    (L.finite.prod ((fg I).prod (fg I⁻¹))) (0, (1, 0)) = I⁻¹
  rw [GeneralContent.contentIdeal_zero_prod _ _ L.finite ((fg I).prod (fg I⁻¹)),
    GeneralContent.contentIdeal_prod_zero _ _ (fg I) (fg I⁻¹),
    FractionalIdealLattice.content_one]

/-- The manuscript content formula holds for every scalar, including zero. -/
theorem content_smul_e (L : Lattice R Q) (I : FractionalIdeal R⁰ K) (hI : I ≠ 0)
    (a : K) :
    (lattice L I hI).content (a • (Hyperbolic.e : Hyperbolic K V)) =
      FractionalIdeal.spanSingleton R⁰ a * I⁻¹ := by
  rw [Lattice.content_smul, content_e]

/-- Explicit reciprocal diagonal scaling identifies a principal ideal plane with the
standard plane and fixes the original lattice pointwise. -/
def principalIsometry (L : Lattice R Q) (a : K) (ha : a ≠ 0) :
    LatticeIsometry (Hyperbolic.form Q) (Hyperbolic.form Q)
      (submodule L.carrier (FractionalIdeal.spanSingleton R⁰ a)) L.hyperbolic.carrier where
  toLinearEquiv := (LinearEquiv.refl K V).prodCongr
    ((LinearEquiv.smulOfNeZero K K a⁻¹ (inv_ne_zero ha)).prodCongr
      (LinearEquiv.smulOfNeZero K K a ha))
  q_eq z := by
    change Q z.1 + (a⁻¹ * z.2.1) * (a * z.2.2) = Q z.1 + z.2.1 * z.2.2
    congr 1
    field_simp
  mem_iff z := by
    change (z.1 ∈ L.carrier ∧ a⁻¹ * z.2.1 ∈ R ∧ a * z.2.2 ∈ R) ↔
      (z.1 ∈ L.carrier ∧ z.2.1 ∈ FractionalIdeal.spanSingleton R⁰ a ∧
        z.2.2 ∈ (FractionalIdeal.spanSingleton R⁰ a)⁻¹)
    rw [FractionalIdeal.spanSingleton_inv,
      FractionalIdealLattice.mem_spanSingleton_iff a ha,
      FractionalIdealLattice.mem_spanSingleton_iff a⁻¹ (inv_ne_zero ha), inv_inv]

end NormEuclidean.IdealHyperbolic
