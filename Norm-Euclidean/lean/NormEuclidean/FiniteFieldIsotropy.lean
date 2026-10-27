import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Isotropy over finite fields

Chevalley–Warning gives a nonzero zero of a quadratic form in at least three
variables. This file supplies the adapter from actual quadratic forms to
polynomials, using an orthogonal basis when two is invertible.
-/

namespace NormEuclidean

open Module MvPolynomial

/-- A polynomial of degree below the number of variables which vanishes at the
origin has a further zero over a finite field. -/
theorem exists_nonzero_zero_of_totalDegree_lt
    {K ι : Type*} [Field K] [Fintype K] [Fintype ι]
    (f : MvPolynomial ι K) (hdeg : f.totalDegree < Fintype.card ι)
    (hzero : MvPolynomial.eval 0 f = 0) :
    ∃ x : ι → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0 := by
  classical
  by_contra h
  have hunique : ∀ x : ι → K, MvPolynomial.eval x f = 0 → x = 0 := by
    intro x hx
    by_contra hne
    exact h ⟨x, hne, hx⟩
  letI : Unique { x : ι → K // MvPolynomial.eval x f = 0 } :=
    { default := ⟨0, hzero⟩
      uniq := fun x => Subtype.ext (hunique x.val x.property) }
  have hdvd := char_dvd_card_solutions (ringChar K) hdeg
  rw [Fintype.card_unique] at hdvd
  exact CharP.ringChar_ne_one (Nat.dvd_one.mp hdvd)

/-- The polynomial representing a diagonal quadratic form. -/
noncomputable def diagonalQuadraticPolynomial
    {K ι : Type*} [CommSemiring K] [Fintype ι] (a : ι → K) : MvPolynomial ι K :=
  ∑ i, MvPolynomial.C (a i) * MvPolynomial.X i ^ 2

/-- A diagonal quadratic polynomial has total degree at most two. -/
theorem diagonalQuadraticPolynomial_totalDegree_le
    {K ι : Type*} [Field K] [Fintype ι] (a : ι → K) :
    (diagonalQuadraticPolynomial a).totalDegree ≤ 2 := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

@[simp] theorem eval_diagonalQuadraticPolynomial
    {K ι : Type*} [CommSemiring K] [Fintype ι] (a x : ι → K) :
    MvPolynomial.eval x (diagonalQuadraticPolynomial a) = ∑ i, a i * x i ^ 2 := by
  classical
  simp [diagonalQuadraticPolynomial]

/-- Every quadratic form of dimension at least three over a finite field of
characteristic different from two has a nonzero isotropic vector. No
nondegeneracy assumption is needed. -/
theorem quadraticForm_exists_nonzero_isotropic
    {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Invertible (2 : K)]
    (Q : QuadraticForm K V) (hdim : 3 ≤ finrank K V) :
    ∃ v : V, v ≠ 0 ∧ Q v = 0 := by
  classical
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (QuadraticForm.associated_isSymm K Q)
  let a : Fin (finrank K V) → K := fun i => Q (b i)
  let f := diagonalQuadraticPolynomial a
  have hdeg : f.totalDegree < Fintype.card (Fin (finrank K V)) := by
    have hle := diagonalQuadraticPolynomial_totalDegree_le a
    simpa only [Fintype.card_fin] using lt_of_le_of_lt hle (by omega)
  obtain ⟨x, hx, hfx⟩ := exists_nonzero_zero_of_totalDegree_lt f hdeg (by
    change MvPolynomial.eval 0 (diagonalQuadraticPolynomial a) = 0
    rw [eval_diagonalQuadraticPolynomial]
    simp)
  refine ⟨b.equivFun.symm x, ?_, ?_⟩
  · intro hv
    exact hx (b.equivFun.symm.injective (hv.trans (map_zero _).symm))
  · have hbasis := Q.basisRepr_eq_of_iIsOrtho b hb
    have heval := congrArg (fun P : QuadraticForm K (Fin (finrank K V) → K) => P x) hbasis
    change Q (b.equivFun.symm x) = _ at heval
    rw [heval]
    simpa [f, a, QuadraticMap.weightedSumSquares_apply, smul_eq_mul, pow_two] using hfx

/-- A version with an explicit `2 ≠ 0` hypothesis and only propositional
finiteness of the field. -/
theorem quadraticForm_exists_nonzero_isotropic_of_two_ne_zero
    {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V)
    (htwo : (2 : K) ≠ 0) (hdim : 3 ≤ finrank K V) :
    ∃ v : V, v ≠ 0 ∧ Q v = 0 := by
  letI := Fintype.ofFinite K
  letI : Invertible (2 : K) := invertibleOfNonzero htwo
  exact quadraticForm_exists_nonzero_isotropic Q hdim

/-- In particular, every form of rank at least three over an odd
finite residue field is isotropic. -/
theorem quadraticForm_exists_nonzero_isotropic_of_char_ne_two
    {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hchar : ringChar K ≠ 2) (hdim : 3 ≤ finrank K V) :
    ∃ v : V, v ≠ 0 ∧ Q v = 0 :=
  quadraticForm_exists_nonzero_isotropic_of_two_ne_zero Q
    (Ring.two_ne_zero hchar) hdim

/-- An anisotropic quadratic form over an odd finite field has rank at most two. -/
theorem finrank_le_two_of_quadraticForm_anisotropic
    {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hchar : ringChar K ≠ 2) (hQ : Q.Anisotropic) : finrank K V ≤ 2 := by
  by_contra hdim
  obtain ⟨v, hv, hQv⟩ :=
    quadraticForm_exists_nonzero_isotropic_of_char_ne_two Q hchar (by omega)
  exact hv (hQ v hQv)

end NormEuclidean
