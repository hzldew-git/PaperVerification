import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Primitive representatives in a finite free module over a PID

The coordinate ideal is divided by its generator. This extracts the
primitive-vector step needed at non-dyadic completions without importing
the unrelated dyadic context of the existing local-lattice API.
-/

noncomputable section

namespace NormEuclidean.LocalPrimitiveVector

variable {S M : Type*} [CommRing S] [IsDomain S] [IsPrincipalIdealRing S]
  [AddCommGroup M] [Module S M] [Module.Free S M] [Module.Finite S M]

/-- A nonzero vector has a primitive factor with respect to any nonunit.
The nonzero common factor and the actual equality are part of the conclusion. -/
theorem exists_primitive_factor (x : M) (hx : x ≠ 0) (π : S) (hπ : ¬ IsUnit π) :
    ∃ (d : S) (w : M), d ≠ 0 ∧ d • w = x ∧ ∀ y : M, π • y ≠ w := by
  classical
  let b := Module.Free.chooseBasis S M
  let I := Ideal.span (Set.range (b.repr x))
  let d := Submodule.IsPrincipal.generator I
  have hcoord (i : Module.Free.ChooseBasisIndex S M) : b.repr x i ∈ I :=
    Ideal.subset_span ⟨i, rfl⟩
  have hd : d ≠ 0 := by
    intro hd
    apply hx
    apply b.repr.injective
    ext i
    have h := hcoord i
    rw [← Ideal.span_singleton_generator I,
      show Submodule.IsPrincipal.generator I = 0 from hd] at h
    simpa using h
  have hdiv (i : Module.Free.ChooseBasisIndex S M) : d ∣ b.repr x i := by
    rw [← Ideal.mem_span_singleton, Ideal.span_singleton_generator]
    exact hcoord i
  choose q hq using hdiv
  let w := ∑ i, q i • b i
  have hdw : d • w = x := by
    rw [← b.sum_repr x]
    simp only [w, Finset.smul_sum, smul_smul, ← hq]
  refine ⟨d, w, hd, hdw, ?_⟩
  intro y hy
  have hI : I ≤ Ideal.span {d * π} := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Ideal.mem_span_singleton.mpr
    refine ⟨b.repr y i, ?_⟩
    have h := congrArg (fun z : M ↦ b.repr z i) hdw
    rw [← hy] at h
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_assoc] using h.symm
  have hdI : d ∈ Ideal.span {d * π} := hI (Submodule.IsPrincipal.generator_mem I)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hdI
  have hprod : π * a = 1 := by
    apply mul_left_cancel₀ hd
    simpa only [mul_one, mul_assoc] using ha.symm
  exact hπ (isUnit_iff_dvd_one.mpr ⟨a, hprod.symm⟩)

end NormEuclidean.LocalPrimitiveVector
