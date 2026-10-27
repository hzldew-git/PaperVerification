import NormEuclidean.ProperGenus

/-!
# Ordinary and proper finiteness in O'Meara 103:4

The proof of 103:4 first bounds ordinary classes and then uses that each
ordinary class contains at most two proper classes. This file proves the
required finite-fiber statement for the project's actual genus quotients.
The ordinary-class finiteness remains an explicit theorem premise; its
global validity is not asserted here.
-/

noncomputable section

namespace NormEuclidean.ProperClassFiniteness

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

/-- Isometries from one base with the same determinant give a proper
integral isometry between their targets. -/
theorem properlyGloballyIsometric_of_det_eq {R : Subring K}
    (A B C : Lattice R Q) (e : LatticeIsometry Q Q A.carrier B.carrier)
    (f : LatticeIsometry Q Q A.carrier C.carrier)
    (h : LinearEquiv.det e.toLinearEquiv = LinearEquiv.det f.toLinearEquiv) :
    ProperlyGloballyIsometric Q B C := by
  refine ⟨e.inverse.compose f, ?_⟩
  change LinearEquiv.det (e.toLinearEquiv.symm.trans f.toLinearEquiv) = 1
  rw [LinearEquiv.det_trans, LinearEquiv.det_symm, map_inv, h]
  simp

section Genus

variable [NumberField K] [Invertible (2 : K)] [FiniteDimensional K V]
variable (hQ : Q.polarBilin.Nondegenerate) (L : Lattice (integerSubring K) Q)

omit [FiniteDimensional K V] in
theorem properToOrdinaryClass_out (c : ProperGenusClassSet Q L) :
    properToOrdinaryClass Q L c = Quotient.mk (genusClassSetoid Q L) c.out := by
  nth_rw 1 [← Quotient.out_eq c]
  rfl

include hQ in
/-- An ordinary genus class has a finite fiber of proper classes, by the
two determinant signs. No global reflection or positivity premise is needed. -/
theorem finite_properToOrdinaryClass_fiber (q : GenusClassSet Q L) :
    Finite {c : ProperGenusClassSet Q L // properToOrdinaryClass Q L c = q} := by
  let A : GenusMember Q L := q.out
  have hIso (c : {c : ProperGenusClassSet Q L // properToOrdinaryClass Q L c = q}) :
      GloballyIsometric Q A.1 c.1.out.1 := by
    have h : Quotient.mk (genusClassSetoid Q L) A =
        Quotient.mk (genusClassSetoid Q L) c.1.out :=
      (Quotient.out_eq q).trans (c.2.symm.trans (properToOrdinaryClass_out Q L c.1))
    exact Quotient.exact h
  let e (c : {c : ProperGenusClassSet Q L // properToOrdinaryClass Q L c = q}) :
      LatticeIsometry Q Q A.1.carrier c.1.out.1.carrier := Classical.choice (hIso c)
  let D := {d : Kˣ // d = 1 ∨ d = -1}
  haveI : Finite D := by
    change {d : Kˣ | d = 1 ∨ d = -1}.Finite
    have heq : {d : Kˣ | d = 1 ∨ d = -1} = ({1, -1} : Set Kˣ) := by
      ext d
      simp
    rw [heq]
    exact (Set.finite_singleton (-1 : Kˣ)).insert (1 : Kˣ)
  let orientation : {c : ProperGenusClassSet Q L // properToOrdinaryClass Q L c = q} → D :=
    fun c ↦ ⟨LinearEquiv.det (e c).toLinearEquiv,
      (SpinorBridge.toBongIsometry hQ hQ (e c)).det_eq_one_or_neg_one⟩
  apply Finite.of_injective orientation
  intro c c' h
  have hdet : LinearEquiv.det (e c).toLinearEquiv = LinearEquiv.det (e c').toLinearEquiv :=
    congrArg Subtype.val h
  have hp := properlyGloballyIsometric_of_det_eq Q A.1 c.1.out.1 c'.1.out.1 (e c) (e c') hdet
  apply Subtype.ext
  have heq : Quotient.mk (properGenusClassSetoid Q L) c.1.out =
      Quotient.mk (properGenusClassSetoid Q L) c'.1.out :=
    @Quotient.sound (GenusMember Q L) (properGenusClassSetoid Q L) _ _ hp
  exact (Quotient.out_eq c.1).symm.trans (heq.trans (Quotient.out_eq c'.1))

include hQ in
/-- The ordinary-to-proper finiteness passage in the proof of 103:4.
The ordinary finiteness premise remains explicit until that induction is proved. -/
theorem finite_proper_classes_of_finite_classes (h : Finite (GenusClassSet Q L)) :
    Finite (ProperGenusClassSet Q L) := by
  letI := h
  letI (q : GenusClassSet Q L) :
      Finite {c : ProperGenusClassSet Q L // properToOrdinaryClass Q L c = q} :=
    finite_properToOrdinaryClass_fiber Q hQ L q
  exact Finite.of_surjective
    (fun x : (Σ q : GenusClassSet Q L,
      {c : ProperGenusClassSet Q L // properToOrdinaryClass Q L c = q}) ↦ x.2.1)
    (fun c ↦ ⟨⟨properToOrdinaryClass Q L c, ⟨c, rfl⟩⟩, rfl⟩)

include hQ in
theorem finite_proper_classes_iff_finite_classes :
    Finite (ProperGenusClassSet Q L) ↔ Finite (GenusClassSet Q L) := by
  constructor
  · intro h
    letI := h
    exact Finite.of_surjective (properToOrdinaryClass Q L) (properToOrdinaryClass_surjective Q L)
  · exact finite_proper_classes_of_finite_classes Q hQ L

end Genus

end NormEuclidean.ProperClassFiniteness
