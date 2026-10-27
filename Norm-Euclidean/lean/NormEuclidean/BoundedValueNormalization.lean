import NormEuclidean.UnaryFiniteness

/-!
# Finite integral value representatives modulo unit squares

An absolute field norm bound leaves infinitely many unit multiples. The
proved unary coefficient quotient supplies an actual finite set of values
after multiplication by squares of integral units. No positivity or PID
hypothesis is needed.
-/

noncomputable section

namespace NormEuclidean.BoundedValueNormalization

open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The absolute norm of the principal value ideal is the actual field norm. -/
theorem principal_absNorm (a : 𝓞 K) :
    (Ideal.absNorm (Ideal.span {a}) : ℚ) = fieldAbsNorm K (a : K) := by
  rw [Ideal.absNorm_span_singleton, ← integralNormMeasure_coe K]
  exact integralNormMeasure_spec K (a : K) a.property

/-- Bounded nonzero integral values have finitely many representatives under unit squares.
The bound and nonvanishing hold for the representatives as well. -/
theorem exists_finite_representatives (B : ℕ) :
    ∃ Φ : Set (𝓞 K), Φ.Finite ∧ (∀ a ∈ Φ, a ≠ 0 ∧
      Ideal.absNorm (Ideal.span {a}) < B) ∧
      ∀ a : 𝓞 K, a ≠ 0 → Ideal.absNorm (Ideal.span {a}) < B →
        ∃ u : (𝓞 K)ˣ, a * (u : 𝓞 K) ^ 2 ∈ Φ := by
  classical
  let C : Set (UnaryIntegralClass (𝓞 K)) :=
    {c | ∃ a : 𝓞 K, a ≠ 0 ∧ Ideal.absNorm (Ideal.span {a}) < B ∧ Quotient.mk _ a = c}
  have hC : C.Finite := (finite_bounded_unaryClasses K B).subset (by
    rintro c ⟨a, _, ha, hc⟩
    exact ⟨a, ha, hc⟩)
  letI : Finite C := hC
  let rep : C → 𝓞 K := fun c ↦ Classical.choose c.property
  have hrep (c : C) : rep c ≠ 0 ∧ Ideal.absNorm (Ideal.span {rep c}) < B ∧
      Quotient.mk (unaryCoefficientSetoid (𝓞 K)) (rep c) = c.val :=
    Classical.choose_spec c.property
  refine ⟨Set.range rep, Set.finite_range rep, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨(hrep c).1, (hrep c).2.1⟩
  · intro a ha hbound
    let c : C := ⟨Quotient.mk _ a, a, ha, hbound, rfl⟩
    have heq : Quotient.mk (unaryCoefficientSetoid (𝓞 K)) a =
        Quotient.mk _ (rep c) := (hrep c).2.2.symm
    obtain ⟨u, hu⟩ := Quotient.exact heq
    refine ⟨u, ?_⟩
    rw [hu]
    exact Set.mem_range_self c

end NormEuclidean.BoundedValueNormalization
