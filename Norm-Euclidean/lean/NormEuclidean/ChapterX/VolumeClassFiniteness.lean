import NormEuclidean.ChapterX.ClassFiniteness
import NormEuclidean.ChapterX.ProperClassFiniteness

/-!
# Actual ordinary and proper classes of the whole bounded-volume family

These quotients range over all norm-integral lattices on the fixed space,
not only members of one genus. The proved finite ordinary representatives
and actual two-determinant-sign fibers give the literal proper-class
finiteness conclusion for integral scale and prescribed nonzero volume.
-/

noncomputable section

namespace NormEuclidean.VolumeClassFiniteness

open ClassFinitenessInduction
open scoped nonZeroDivisors

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def ordinarySetoid (Q : QuadraticForm K V) : Setoid (Lattice (integerSubring K) Q) where
  r := GloballyIsometric Q
  iseqv := ⟨GloballyIsometric.refl Q, GloballyIsometric.symm Q, GloballyIsometric.trans Q⟩

def properSetoid (Q : QuadraticForm K V) : Setoid (Lattice (integerSubring K) Q) where
  r := ProperlyGloballyIsometric Q
  iseqv := ⟨ProperlyGloballyIsometric.refl Q, ProperlyGloballyIsometric.symm Q,
    ProperlyGloballyIsometric.trans Q⟩

def OrdinaryClassSet (Q : QuadraticForm K V) := Quotient (ordinarySetoid Q)
def ProperClassSet (Q : QuadraticForm K V) := Quotient (properSetoid Q)

def ordinaryClass (Q : QuadraticForm K V) (L : Lattice (integerSubring K) Q) :
    OrdinaryClassSet Q := Quotient.mk (ordinarySetoid Q) L

def properClass (Q : QuadraticForm K V) (L : Lattice (integerSubring K) Q) :
    ProperClassSet Q := Quotient.mk (properSetoid Q) L

def forgetProper (Q : QuadraticForm K V) : ProperClassSet Q → OrdinaryClassSet Q :=
  Quotient.map id (fun _ _ h ↦ ProperlyGloballyIsometric.globallyIsometric Q h)

omit [NumberField K] [Invertible (2 : K)] [FiniteDimensional K V] in
theorem forgetProper_out (Q : QuadraticForm K V) (p : ProperClassSet Q) :
    forgetProper Q p = ordinaryClass Q p.out := by
  nth_rw 1 [← Quotient.out_eq p]
  rfl

omit [Invertible (2 : K)] in
/-- The actual proper-to-ordinary quotient fiber for all lattices is finite,
by the two determinant signs; no genus membership is part of these quotients. -/
theorem finite_forgetProper_fiber (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (q : OrdinaryClassSet Q) : Finite {p : ProperClassSet Q // forgetProper Q p = q} := by
  classical
  let A := q.out
  have hIso (p : {p : ProperClassSet Q // forgetProper Q p = q}) :
      GloballyIsometric Q A p.1.out := by
    have h : ordinaryClass Q A = ordinaryClass Q p.1.out :=
      (Quotient.out_eq q).trans (p.2.symm.trans (forgetProper_out Q p.1))
    exact Quotient.exact h
  let e (p : {p : ProperClassSet Q // forgetProper Q p = q}) :
      LatticeIsometry Q Q A.carrier p.1.out.carrier := Classical.choice (hIso p)
  let D := {d : Kˣ // d = 1 ∨ d = -1}
  haveI : Finite D := by
    change {d : Kˣ | d = 1 ∨ d = -1}.Finite
    have heq : {d : Kˣ | d = 1 ∨ d = -1} = ({1, -1} : Set Kˣ) := by ext d; simp
    rw [heq]
    exact (Set.finite_singleton (-1 : Kˣ)).insert (1 : Kˣ)
  let orientation : {p : ProperClassSet Q // forgetProper Q p = q} → D := fun p ↦
    ⟨LinearEquiv.det (e p).toLinearEquiv,
      (SpinorBridge.toBongIsometry hQ hQ (e p)).det_eq_one_or_neg_one⟩
  apply Finite.of_injective orientation
  intro p p' h
  have hdet : LinearEquiv.det (e p).toLinearEquiv = LinearEquiv.det (e p').toLinearEquiv :=
    congrArg Subtype.val h
  have hp := ProperClassFiniteness.properlyGloballyIsometric_of_det_eq Q
    A p.1.out p'.1.out (e p) (e p') hdet
  apply Subtype.ext
  have heq : properClass Q p.1.out = properClass Q p'.1.out :=
    @Quotient.sound _ (properSetoid Q) _ _ hp
  exact (Quotient.out_eq p.1).symm.trans (heq.trans (Quotient.out_eq p'.1))

/-- Actual ordinary classes of the entire integral-scale bounded-volume
family form a finite set on the fixed regular number-field space. -/
theorem finite_bounded_ordinary_classes (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (c : FractionalIdeal (integerSubring K)⁰ K)
    (hc : c ≠ 0) :
    (ordinaryClass Q '' {L : Lattice (integerSubring K) Q |
      L.scaleIdeal ≤ 1 ∧ c ≤ L.volumeIdeal}).Finite := by
  obtain ⟨A, hA, hcover⟩ := ClassFiniteness.finite_volume_classes Q hQ c hc
  apply (hA.image (ordinaryClass Q)).subset
  rintro _ ⟨L, ⟨hs, hvol⟩, rfl⟩
  obtain ⟨N, hN, hLN⟩ := hcover L hs hvol
  exact ⟨N, hN, Quotient.sound (GloballyIsometric.symm Q hLN)⟩

/-- The number-field proper-class conclusion of 103:4, strengthened to a
nonzero lower volume bound and covering all genera on the fixed space. -/
theorem finite_bounded_proper_classes (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (c : FractionalIdeal (integerSubring K)⁰ K)
    (hc : c ≠ 0) :
    (properClass Q '' {L : Lattice (integerSubring K) Q |
      L.scaleIdeal ≤ 1 ∧ c ≤ L.volumeIdeal}).Finite := by
  have hO := finite_bounded_ordinary_classes Q hQ c hc
  have hpre : (forgetProper Q ⁻¹' (ordinaryClass Q ''
      {L : Lattice (integerSubring K) Q | L.scaleIdeal ≤ 1 ∧ c ≤ L.volumeIdeal})).Finite := by
    apply hO.preimage'
    intro q _
    change {p : ProperClassSet Q | forgetProper Q p = q}.Finite
    exact @Set.toFinite (ProperClassSet Q) {p | forgetProper Q p = q}
      (finite_forgetProper_fiber Q hQ q)
  apply hpre.subset
  rintro _ ⟨L, hL, rfl⟩
  exact ⟨L, hL, rfl⟩

/-- In particular, proper classes with integral scale and a prescribed
nonzero intrinsic volume ideal are finite on the fixed regular space. -/
theorem finite_proper_classes_of_volume (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (c : FractionalIdeal (integerSubring K)⁰ K)
    (hc : c ≠ 0) :
    (properClass Q '' {L : Lattice (integerSubring K) Q |
      L.scaleIdeal ≤ 1 ∧ L.volumeIdeal = c}).Finite :=
  (finite_bounded_proper_classes Q hQ c hc).subset
    (Set.image_mono (fun _ h ↦ ⟨h.1, le_of_eq h.2.symm⟩))

end NormEuclidean.VolumeClassFiniteness
