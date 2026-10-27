import NormEuclidean.SpinorBridge
import NormEuclidean.ProperSpinor
import NormEuclidean.GenusPrerequisites

/-!
# Full ambient spinor norms of a hyperbolic enlargement

Universality and the two-reflection construction give every field squareclass
as the spinor norm of a proper ambient isometry. The archimedean statements use
the actual real or complex completions. They impose no sign restriction.
These are ambient results; they do not assert global integral isometry or
uniqueness of a spinor genus or an ordinary genus class.
-/

namespace NormEuclidean.SpinorBridge

variable {K V : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A universal quadratic space realizes every field unit squareclass through
a proper ambient isometry, with no lattice condition on the vectors. -/
theorem exists_proper_ambient_isometry_of_universal (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hU : ∀ a : K, ∃ x : V, Q x = a) (u : Kˣ) :
    ∃ e : LatticeIsometry Q Q (⊤ : Submodule (⊤ : Subring K) V) ⊤,
      LinearEquiv.det e.toLinearEquiv = 1 ∧
        spinorNorm hQ e = Bong.Dyadic.squareClass K u := by
  let uTop : (⊤ : Subring K)ˣ := Units.map Subring.topEquiv.symm.toMonoidHom u
  have hu : Units.map (⊤ : Subring K).subtype.toMonoidHom uTop = u := by
    apply Units.ext
    rfl
  have hrep : ∃ x ∈ (⊤ : Submodule (⊤ : Subring K) V),
      Q x = ((uTop : (⊤ : Subring K)) : K) := by
    obtain ⟨x, hx⟩ := hU u
    exact ⟨x, Submodule.mem_top, hx⟩
  have hOne : ∃ x ∈ (⊤ : Submodule (⊤ : Subring K) V), Q x = 1 := by
    obtain ⟨x, hx⟩ := hU 1
    exact ⟨x, Submodule.mem_top, hx⟩
  simpa only [hu] using exists_proper_isometry_of_represented_unit Q hQ ⊤ ⊤
    (fun _ _ ↦ trivial) uTop hrep hOne

/-- Adjoining a hyperbolic plane gives full proper ambient spinor norm over
the original field. The prescribed class is represented by a genuine isometry. -/
theorem hyperbolic_exists_proper_ambient_isometry (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (u : Kˣ) :
    ∃ e : LatticeIsometry (Hyperbolic.form Q) (Hyperbolic.form Q)
        (⊤ : Submodule (⊤ : Subring K) (Hyperbolic K V)) ⊤,
      LinearEquiv.det e.toLinearEquiv = 1 ∧
        spinorNorm (Hyperbolic.form_polarBilin_nondegenerate Q hQ) e =
          Bong.Dyadic.squareClass K u := by
  apply exists_proper_ambient_isometry_of_universal
    (Hyperbolic.form Q) (Hyperbolic.form_polarBilin_nondegenerate Q hQ)
  intro a
  exact ⟨(0, a, 1), by simp [Hyperbolic.q]⟩

end NormEuclidean.SpinorBridge

namespace NormEuclidean.ArchimedeanComparison

variable {K V : Type*} [Field K] [CharZero K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

instance completion_charZero (v : NumberField.InfinitePlace K) : CharZero v.Completion :=
  Algebra.charZero_of_charZero K v.Completion

/-- At every actual infinite completion the proper ambient spinor norm of
the hyperbolic enlargement contains every local field squareclass. In particular,
real negative classes are allowed, as required by the ordinary class-group route. -/
theorem hyperbolic_exists_proper_ambient_isometry
    (v : NumberField.InfinitePlace K) (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (u : v.Completionˣ) :
    ∃ e : LatticeIsometry (form v (Hyperbolic.form Q)) (form v (Hyperbolic.form Q))
        (⊤ : Submodule (⊤ : Subring v.Completion)
          (Space (V := Hyperbolic K V) v)) ⊤,
      LinearEquiv.det e.toLinearEquiv = 1 ∧
        SpinorBridge.spinorNorm
          (archimedean_form_polarBilin_nondegenerate v
            (Hyperbolic.form_polarBilin_nondegenerate Q hQ)) e =
          Bong.Dyadic.squareClass v.Completion u :=
  SpinorBridge.exists_proper_ambient_isometry_of_universal _
    (archimedean_form_polarBilin_nondegenerate v
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ))
    (hyperbolic_universal v Q) u

end NormEuclidean.ArchimedeanComparison

namespace NormEuclidean.ProperSpinor

variable {K V : Type*} [Field K] [CharZero K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Universality makes the proper ambient Wall homomorphism surjective onto
the entire field squareclass group. -/
theorem properAmbientSpinorNormHom_surjective_of_universal (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hU : ∀ a : K, ∃ x : V, Q x = a) :
    Function.Surjective (properAmbientSpinorNormHom Q hQ) := by
  intro a
  refine QuotientGroup.induction_on a ?_
  intro u
  obtain ⟨e, he, hs⟩ := SpinorBridge.exists_proper_ambient_isometry_of_universal Q hQ hU u
  exact ⟨properAmbientOfLatticeIsometry e he, hs⟩

theorem hyperbolic_properAmbientSpinorNormHom_surjective (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) :
    Function.Surjective (properAmbientSpinorNormHom (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ)) := by
  apply properAmbientSpinorNormHom_surjective_of_universal
  intro a
  exact ⟨(0, a, 1), by simp [Hyperbolic.q]⟩

variable [Invertible (2 : K)]

/-- The range at an actual infinite completion is the full squareclass group. -/
theorem archimedean_hyperbolic_properSpinorImage_eq_top
    (v : NumberField.InfinitePlace K) (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) :
    (properAmbientSpinorNormHom (ArchimedeanComparison.form v (Hyperbolic.form Q))
      (archimedean_form_polarBilin_nondegenerate v
        (Hyperbolic.form_polarBilin_nondegenerate Q hQ))).range = ⊤ :=
  MonoidHom.range_eq_top.mpr (properAmbientSpinorNormHom_surjective_of_universal _ _
    (ArchimedeanComparison.hyperbolic_universal v Q))

end NormEuclidean.ProperSpinor
