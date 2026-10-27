import NormEuclidean.LatticeCommensurability
import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Integral diagonal frames

A finite full integral lattice contains a diagonal basis of its ambient field
space. Its integral span need not equal the lattice, but contains a nonzero
scalar multiple of it. No freeness hypothesis on the lattice is required.
-/

namespace NormEuclidean

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K} {Q : QuadraticForm K V}

/-- A diagonal ambient basis lying in a lattice, together with a common
integral denominator for the quotient by its integral span. -/
structure IntegralDiagonalFrame (L : Lattice R Q) (ι : Type*) [Fintype ι] where
  basis : Basis ι K V
  basis_mem : ∀ i, basis i ∈ L.carrier
  coeff : ι → R
  diagonal : ∀ x : ι → K,
    Q (basis.equivFun.symm x) = ∑ i, (coeff i : K) * x i ^ 2
  denominator : R
  denominator_ne_zero : denominator ≠ 0
  denominator_mem : ∀ v ∈ L.carrier,
    (denominator : K) • v ∈ Submodule.span R (Set.range basis)

namespace IntegralDiagonalFrame

variable {L : Lattice R Q} {ι : Type*} [Fintype ι]

/-- The integral span of a frame lies in its lattice. -/
theorem span_le (F : IntegralDiagonalFrame L ι) :
    Submodule.span R (Set.range F.basis) ≤ L.carrier := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact F.basis_mem i

/-- The integral span of a frame remains full in the ambient field space. -/
theorem span_full (F : IntegralDiagonalFrame L ι) :
    Submodule.span K (Submodule.span R (Set.range F.basis) : Set V) = ⊤ := by
  rw [Submodule.span_span_of_tower, F.basis.span_eq]

/-- The diagonal coefficients are precisely the values on the frame vectors. -/
@[simp] theorem coeff_eq (F : IntegralDiagonalFrame L ι) (i : ι) :
    (F.coeff i : K) = Q (F.basis i) := by
  classical
  have h := (F.diagonal (F.basis.equivFun (F.basis i))).symm
  rw [F.basis.equivFun.symm_apply_apply] at h
  simpa [Basis.equivFun_self] using h

/-- Evaluate the form using a vector's frame coordinates. -/
theorem diagonal_repr (F : IntegralDiagonalFrame L ι) (v : V) :
    Q v = ∑ i, (F.coeff i : K) * F.basis.repr v i ^ 2 := by
  simpa using F.diagonal (F.basis.equivFun v)

end IntegralDiagonalFrame

/-- Finite generation and fullness of a lattice imply finite dimension of its
ambient field space, independently of any freeness of the integral lattice. -/
theorem Lattice.finiteDimensional (L : Lattice R Q) : FiniteDimensional K V := by
  obtain ⟨s, hs⟩ := L.finite
  have hspan : Submodule.span K (s : Set V) = ⊤ := by
    rw [← Submodule.span_span_of_tower R, hs]
    exact L.full
  exact Module.finite_def.mpr (show (⊤ : Submodule K V).FG from ⟨s, hspan⟩)

variable [IsFractionRing R K] [Invertible (2 : K)]

/-- Every finite full integral lattice admits an integral diagonal frame.
The index set has its ambient field dimension; finite dimension is derived
from the lattice hypotheses rather than assumed. -/
theorem Lattice.nonempty_integralDiagonalFrame (L : Lattice R Q) :
    Nonempty (IntegralDiagonalFrame L (Fin (finrank K V))) := by
  classical
  letI := L.finiteDimensional
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (QuadraticForm.associated_isSymm K Q)
  choose d hd hdb using fun i =>
    ScalarExtension.exists_denominator L.carrier L.full (b i)
  have hdK : ∀ i, (d i : K) ≠ 0 := fun i => by exact_mod_cast hd i
  let u : Fin (finrank K V) → Kˣ := fun i => Units.mk0 (d i : K) (hdK i)
  let b' := b.unitsSMul u
  have hb'eq : ∀ i, b' i = (d i : K) • b i := by
    intro i
    simp [b', Basis.unitsSMul_apply, u, Units.smul_def]
  have hb'mem : ∀ i, b' i ∈ L.carrier := by
    intro i
    rw [hb'eq]
    exact hdb i
  have hb'ortho : (QuadraticMap.associated Q).IsOrthoᵢ b' := by
    intro i j hij
    have hz : (QuadraticMap.associated Q) (b i) (b j) = 0 := hb hij
    change (QuadraticMap.associated Q) (b' i) (b' j) = 0
    simp only [hb'eq, LinearMap.map_smul, LinearMap.smul_apply,
      smul_eq_mul, hz, mul_zero]
  let a : Fin (finrank K V) → R := fun i => ⟨Q (b' i), L.integral _ (hb'mem i)⟩
  have hdiag : ∀ x : Fin (finrank K V) → K,
      Q (b'.equivFun.symm x) = ∑ i, (a i : K) * x i ^ 2 := by
    intro x
    have h := congrArg (fun q : QuadraticForm K (Fin (finrank K V) → K) => q x)
      (Q.basisRepr_eq_of_iIsOrtho b' hb'ortho)
    simpa [QuadraticMap.basisRepr, QuadraticMap.weightedSumSquares_apply,
      smul_eq_mul, pow_two, a] using h
  have hfull : Submodule.span K (Submodule.span R (Set.range b') : Set V) = ⊤ := by
    rw [Submodule.span_span_of_tower, b'.span_eq]
  obtain ⟨t, ht, htv⟩ := exists_lattice_denominator L.carrier
    (Submodule.span R (Set.range b')) L.finite hfull
  exact ⟨⟨b', hb'mem, a, hdiag, t, ht, htv⟩⟩

/-- A chosen integral diagonal frame, constructed without a basis of the
integral lattice itself. -/
noncomputable def Lattice.integralDiagonalFrame (L : Lattice R Q) :
    IntegralDiagonalFrame L (Fin (finrank K V)) :=
  Classical.choice L.nonempty_integralDiagonalFrame

end NormEuclidean
