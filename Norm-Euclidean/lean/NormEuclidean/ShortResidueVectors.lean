import NormEuclidean.NormBound
import NormEuclidean.IntegralDiagonalFrame
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Small representatives of every residue class modulo twice the lattice

The strict approximation applies to each half-vector. Passing to any proper
field quotient proves that the resulting small vectors span the full space.
No integral basis, principal ideal ring or positivity is required.
-/

noncomputable section

namespace NormEuclidean.ShortResidueVectors

open Module
open scoped NumberField

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- Actual lattice vectors satisfying the uniform strict norm bound. -/
def small (L : Lattice (integerSubring K) Q) : Set V :=
  {w | w ∈ L.carrier ∧ fieldAbsNorm K (Q w) < (4 : ℚ) ^ Module.finrank ℚ K}

/-- Every residue class modulo twice the lattice has a small representative, including zero. -/
theorem exists_in_residue (L : Lattice (integerSubring K) Q)
    (hE : HasNumberFieldApproximation Q L.carrier) {w₀ : V} (hw₀ : w₀ ∈ L.carrier) :
    ∃ w ∈ small L, ∃ y ∈ L.carrier, w = w₀ - (2 : K) • y := by
  let x : V := (2 : K)⁻¹ • w₀
  obtain ⟨y, hy, happ⟩ := hE x
  let w : V := w₀ - (2 : K) • y
  have hw : w ∈ L.carrier := L.carrier.sub_mem hw₀
    (L.carrier.smul_mem (2 : integerSubring K) hy)
  have heq : w = (2 : K) • (x - y) := by
    dsimp only [w, x]
    rw [smul_sub, smul_smul, mul_inv_cancel₀ (by norm_num : (2 : K) ≠ 0), one_smul]
  have hQ : Q w = (4 : K) * Q (x - y) := by
    rw [heq, Q.map_smul]
    norm_num [smul_eq_mul]
  refine ⟨w, ⟨hw, ?_⟩, y, hy, rfl⟩
  rw [hQ, fieldAbsNorm_four_mul]
  change fieldAbsNorm K (Q (x - y)) < 1 at happ
  simpa only [mul_one] using mul_lt_mul_of_pos_left happ
    (by positivity : (0 : ℚ) < (4 : ℚ) ^ Module.finrank ℚ K)

/-- The image of a full lattice in a field quotient, with the harmless zero form. -/
def quotientLattice (L : Lattice (integerSubring K) Q) (W : Submodule K V) :
    Lattice (integerSubring K) (0 : QuadraticForm K (V ⧸ W)) where
  carrier := L.carrier.map (W.mkQ.restrictScalars (integerSubring K))
  finite := L.finite.map _
  full := by
    change Submodule.span K (W.mkQ '' (L.carrier : Set V)) = ⊤
    rw [← Submodule.map_span, L.full, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr W.mkQ_surjective
  integral := by intros; exact (integerSubring K).zero_mem

/-- A small lattice vector lies outside each proper field subspace.
The quotient argument uses only finite generation over the integers. -/
theorem exists_not_mem (L : Lattice (integerSubring K) Q)
    (hE : HasNumberFieldApproximation Q L.carrier) (W : Submodule K V) (hW : W ≠ ⊤) :
    ∃ w ∈ small L, w ∉ W := by
  letI : Nontrivial (V ⧸ W) := Submodule.Quotient.nontrivial_iff.mpr hW
  obtain ⟨z, hz, hdiv⟩ := (quotientLattice L W).exists_not_two_smul
  obtain ⟨w₀, hw₀, rfl⟩ := hz
  obtain ⟨w, hw, y, hy, heq⟩ := exists_in_residue L hE hw₀
  refine ⟨w, hw, ?_⟩
  intro hwW
  apply hdiv (W.mkQ y) ⟨y, hy, rfl⟩
  have hzero : W.mkQ w = 0 := by
    change (Submodule.Quotient.mk w : V ⧸ W) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hwW
  rw [heq, map_sub, map_smul] at hzero
  exact sub_eq_zero.mp hzero

/-- All small vectors together span the ambient field space. -/
theorem span_eq_top (L : Lattice (integerSubring K) Q)
    (hE : HasNumberFieldApproximation Q L.carrier) : Submodule.span K (small L) = ⊤ := by
  by_contra h
  obtain ⟨w, hw, hnot⟩ := exists_not_mem L hE (Submodule.span K (small L)) h
  exact hnot (Submodule.subset_span hw)

/-- A full field basis can be chosen among the original small lattice vectors.
This is a field basis, not a claim that a possibly nonfree lattice has an integral basis. -/
theorem exists_basis (L : Lattice (integerSubring K) Q)
    (hE : HasNumberFieldApproximation Q L.carrier) :
    ∃ b : Basis (Fin (Module.finrank K V)) K V, ∀ i, b i ∈ small L := by
  classical
  letI := L.finiteDimensional
  let b := Basis.ofSpan (le_of_eq (span_eq_top L hE).symm)
  letI := FiniteDimensional.fintypeBasisIndex b
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  refine ⟨b.reindex e, ?_⟩
  intro i
  exact Basis.ofSpan_subset (le_of_eq (span_eq_top L hE).symm)
    ⟨e.symm i, by simp only [Basis.reindex_apply]; rfl⟩

end NormEuclidean.ShortResidueVectors
