import NormEuclidean.NumberFieldNorm
import NormEuclidean.Lattice
import Mathlib.LinearAlgebra.FreeModule.PID

namespace NormEuclidean
open scoped NumberField
variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V}

/-- A nonzero full lattice has an element that is not twice a lattice element.
Only freeness over the integers is used; freeness over the ring of integers is
neither assumed nor needed. -/
theorem Lattice.exists_not_two_smul [Nontrivial V]
    (L : Lattice (integerSubring K) Q) :
    ∃ w₀ ∈ L.carrier, ∀ y ∈ L.carrier, w₀ ≠ (2 : K) • y := by
  classical
  letI : Module.Finite (integerSubring K) L.carrier := Module.Finite.iff_fg.mpr L.finite
  letI : Module.Finite ℤ (integerSubring K) := inferInstanceAs (Module.Finite ℤ (𝓞 K))
  letI : Module.Finite ℤ L.carrier := Module.Finite.trans (integerSubring K) L.carrier
  letI : IsAddTorsionFree V := IsAddTorsionFree.of_isTorsionFree K V
  letI : NoZeroSMulDivisors ℤ V := inferInstance
  letI : IsAddTorsionFree L.carrier := {
    nsmul_right_injective := by
      intro n hn x y hxy
      apply Subtype.ext
      exact IsAddTorsionFree.nsmul_right_injective hn (congrArg Subtype.val hxy) }
  letI : NoZeroSMulDivisors ℤ L.carrier := inferInstance
  have hL : L.carrier ≠ ⊥ := by
    intro hbot
    have hf := L.full
    rw [hbot] at hf
    simp at hf
  letI : Nontrivial L.carrier := Submodule.nontrivial_iff_ne_bot.mpr hL
  let b := Module.Free.chooseBasis ℤ L.carrier
  obtain ⟨i⟩ := b.index_nonempty
  refine ⟨(b i : V), (b i).property, ?_⟩
  intro y hy heq
  have hb : b i = (2 : ℤ) • (⟨y, hy⟩ : L.carrier) := by
    apply Subtype.ext
    change (b i : V) = (2 : ℤ) • y
    simpa only [← Int.cast_smul_eq_zsmul K, Int.cast_ofNat] using heq
  have hi := congrArg (fun x : L.carrier => b.repr x i) hb
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, b.repr_self, Finsupp.single_eq_same] at hi
  omega

end NormEuclidean
