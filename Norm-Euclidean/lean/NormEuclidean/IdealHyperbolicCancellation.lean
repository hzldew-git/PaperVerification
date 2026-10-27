import NormEuclidean.IdealHyperbolic
import NormEuclidean.NumberFieldCancellation
import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Cancellation of an arbitrary ideal hyperbolic plane

An isometry from `J ⊥ H(I)` to the standard stabilization of a norm-Euclidean
lattice forces `I` to be principal, by intrinsic content descent. Reciprocal
diagonal scaling then reduces to the existing full hyperbolic cancellation.
The statement imposes no genus, freeness, or class-number hypothesis on `J`.
-/

noncomputable section

namespace NormEuclidean.IdealHyperbolic

open scoped nonZeroDivisors

variable {K V W : Type*} [Field K] [NumberField K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable {Q : QuadraticForm K V} {P : QuadraticForm K W}

/-- Intrinsic content descent forces the ideal in an arbitrary stabilized source to be
principal whenever the target is the standard stabilization of a norm-Euclidean lattice. -/
theorem isPrincipal_of_isometry (L : Lattice (integerSubring K) Q)
    (J : Lattice (integerSubring K) P) (I : FractionalIdeal (integerSubring K)⁰ K)
    (hI : I ≠ 0) (hA : Q.Anisotropic)
    (hE : HasNumberFieldApproximation Q L.carrier)
    (e : LatticeIsometry (Hyperbolic.form P) (Hyperbolic.form Q)
      (lattice J I hI).carrier L.hyperbolic.carrier) :
    (I : Submodule (integerSubring K) K).IsPrincipal := by
  obtain ⟨a, ha, ha0⟩ := FractionalIdealLattice.exists_nonzero I hI
  let z : Hyperbolic K W := a • Hyperbolic.e
  have hz : z ∈ (lattice J I hI).carrier := by
    change z ∈ submodule J.carrier I
    simpa [z, Hyperbolic.e] using
      (show (0 : W) ∈ J.carrier ∧ a ∈ I ∧ (0 : K) ∈ I⁻¹ from
        ⟨J.carrier.zero_mem, ha, (I⁻¹).zero_mem⟩)
  have hz0 : z ≠ 0 := by
    intro h
    have hcoord := congrArg (fun w : Hyperbolic K W ↦ w.2.1) h
    exact ha0 (by simpa [z, Hyperbolic.e] using hcoord)
  have hiso : Hyperbolic.q Q (e.toLinearEquiv z) = 0 := by
    change Hyperbolic.form Q (e.toLinearEquiv z) = 0
    rw [e.q_eq]
    simp [z, Hyperbolic.q, Hyperbolic.e]
  obtain ⟨_, c, _, hc0, _, hc⟩ := numberField_norm_descent_total_content Q L hA hE
    ((e.mem_iff z).mpr hz) (e.toLinearEquiv.map_ne_zero_iff.mpr hz0) hiso
  have hcontent := GeneralContent.contentIdeal_equiv
    (lattice J I hI).carrier L.hyperbolic.carrier (lattice J I hI).finite
    L.hyperbolic.finite e.toLinearEquiv e.mem_iff z
  change L.hyperbolic.content (e.toLinearEquiv z) = (lattice J I hI).content z at hcontent
  have h : FractionalIdeal.spanSingleton (integerSubring K)⁰ a * I⁻¹ =
      FractionalIdeal.spanSingleton (integerSubring K)⁰ c := by
    rw [← content_smul_e J I hI a]
    exact hcontent.symm.trans hc
  have hprod : FractionalIdeal.spanSingleton (integerSubring K)⁰ a =
      FractionalIdeal.spanSingleton (integerSubring K)⁰ c * I := by
    simpa only [mul_assoc, inv_mul_cancel₀ hI, mul_one] using
      congrArg (fun D ↦ D * I) h
  apply (FractionalIdeal.isPrincipal_iff I).mpr
  refine ⟨c⁻¹ * a, ?_⟩
  calc
    I = (FractionalIdeal.spanSingleton (integerSubring K)⁰ c)⁻¹ *
        FractionalIdeal.spanSingleton (integerSubring K)⁰ a := by
      rw [hprod, ← mul_assoc,
        inv_mul_cancel₀ (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hc0), one_mul]
    _ = FractionalIdeal.spanSingleton (integerSubring K)⁰ (c⁻¹ * a) := by
      rw [FractionalIdeal.spanSingleton_inv, FractionalIdeal.spanSingleton_mul_spanSingleton]

/-- Full ideal hyperbolic cancellation, for arbitrary integral source lattices.
The ideal must be principal, and the unstabilized lattices must be integrally isometric. -/
theorem cancellation_iff (L : Lattice (integerSubring K) Q)
    (J : Lattice (integerSubring K) P) (I : FractionalIdeal (integerSubring K)⁰ K)
    (hI : I ≠ 0) (hA : Q.Anisotropic)
    (hE : HasNumberFieldApproximation Q L.carrier) :
    Nonempty (LatticeIsometry (Hyperbolic.form P) (Hyperbolic.form Q)
      (lattice J I hI).carrier L.hyperbolic.carrier) ↔
      (I : Submodule (integerSubring K) K).IsPrincipal ∧
        Nonempty (LatticeIsometry P Q J.carrier L.carrier) := by
  constructor
  · rintro ⟨e⟩
    have hprincipal := isPrincipal_of_isometry L J I hI hA hE e
    refine ⟨hprincipal, ?_⟩
    obtain ⟨a, ha⟩ := (FractionalIdeal.isPrincipal_iff I).mp hprincipal
    have ha0 : a ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mp (ha ▸ hI)
    let s := principalIsometry J a ha0
    have e' : LatticeIsometry (Hyperbolic.form P) (Hyperbolic.form Q)
        (submodule J.carrier (FractionalIdeal.spanSingleton (integerSubring K)⁰ a))
        L.hyperbolic.carrier := by
      simpa only [lattice, ha] using e
    let f := s.inverse.compose e'
    exact numberField_hyperbolic_cancellation_ambient Q P L J hA hE
      ⟨f.toLinearEquiv, f.q_eq, f.mem_iff⟩
  · rintro ⟨hprincipal, ⟨e⟩⟩
    obtain ⟨a, ha⟩ := (FractionalIdeal.isPrincipal_iff I).mp hprincipal
    have ha0 : a ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mp (ha ▸ hI)
    have f := (principalIsometry J a ha0).compose e.hyperbolic
    refine ⟨?_⟩
    simpa only [lattice, ha, Lattice.hyperbolic] using f

/-- The ideal obstruction is exactly triviality in the ordinary ideal class group. -/
theorem cancellation_iff_classGroup (L : Lattice (integerSubring K) Q)
    (J : Lattice (integerSubring K) P) (I : FractionalIdeal (integerSubring K)⁰ K)
    (hI : I ≠ 0) (hA : Q.Anisotropic)
    (hE : HasNumberFieldApproximation Q L.carrier) :
    Nonempty (LatticeIsometry (Hyperbolic.form P) (Hyperbolic.form Q)
      (lattice J I hI).carrier L.hyperbolic.carrier) ↔
      ClassGroup.mk K (Units.mk0 I hI) = 1 ∧
        Nonempty (LatticeIsometry P Q J.carrier L.carrier) := by
  rw [cancellation_iff L J I hI hA hE, ClassGroup.mk_eq_one_iff]
  rfl

/-- The same cancellation statement starts with isometries of the actual integral modules;
ambient extension follows from fullness, and is not an extra hypothesis. -/
theorem cancellation_from_module (L : Lattice (integerSubring K) Q)
    (J : Lattice (integerSubring K) P) (I : FractionalIdeal (integerSubring K)⁰ K)
    (hI : I ≠ 0) (hA : Q.Anisotropic)
    (hE : HasNumberFieldApproximation Q L.carrier)
    (e : (lattice J I hI).carrier ≃ₗ[integerSubring K] L.hyperbolic.carrier)
    (he : ∀ z, Hyperbolic.form Q (e z : Hyperbolic K V) =
      Hyperbolic.form P (z : Hyperbolic K W)) :
    (I : Submodule (integerSubring K) K).IsPrincipal ∧
      ∃ f : J.carrier ≃ₗ[integerSubring K] L.carrier,
        ∀ x : J.carrier, Q (f x : V) = P (x : W) := by
  let f := ScalarExtension.isometry (Hyperbolic.form P) (Hyperbolic.form Q)
    (lattice J I hI).carrier L.hyperbolic.carrier (lattice J I hI).full
    L.hyperbolic.full e he
  obtain ⟨hprincipal, ⟨g⟩⟩ := (cancellation_iff L J I hI hA hE).mp ⟨f⟩
  exact ⟨hprincipal, g.toModuleEquiv, g.toModuleEquiv_q⟩

end NormEuclidean.IdealHyperbolic
