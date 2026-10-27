/-
Adapted from the generic NumberFieldLatticeModule section of the author's
TraceEuclidean/PseudoBasisDeterminant.lean. No totally real or positive-definite
presentation layer is imported. The original source is kept unchanged.
-/

import NormEuclidean.ChapterX.ModulePseudoBasis
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

namespace NormEuclidean

open Module Matrix
open scoped NumberField nonZeroDivisors

noncomputable section

namespace NumberFieldLatticeModule

variable {K : Type*} [Field K] [NumberField K]

/-- The coordinate submodule is tautologically the product of its fractional
ideal coordinate types. -/
def coordinateModulePiEquiv (n : ℕ)
    (ideals : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
    coordinateModule n ideals ≃ₗ[𝓞 K]
      ((i : Fin n) → (ideals i).coeToSubmodule) where
  toFun x i :=
    ⟨x.1 i, Submodule.mem_pi.mp x.2 i (Set.mem_univ i)⟩
  invFun x :=
    ⟨fun i ↦ (x i : K), by
      rw [coordinateModule, Submodule.mem_pi]
      intro i _
      exact (x i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- A common indexing of a fractional-ideal basis by the selected integral
basis index of the number field. -/
def fractionalIdealIndexEquiv
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI : I ≠ 0) :
    Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃
      Module.Free.ChooseBasisIndex ℤ I := by
  classical
  let U : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ := Units.mk0 I hI
  refine Fintype.equivOfCardEq ?_
  rw [← Module.finrank_eq_card_chooseBasisIndex,
    ← Module.finrank_eq_card_chooseBasisIndex]
  change Module.finrank ℤ (𝓞 K) = Module.finrank ℤ (U :
    FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  exact (NumberField.fractionalIdeal_rank K U).symm

/-- The chosen integer basis of a fractional ideal, reindexed by the common
field integral-basis index. -/
def fractionalIdealCommonBasis
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI : I ≠ 0) :
    Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℤ I :=
  (NumberField.fractionalIdealBasis K I).reindex
    (fractionalIdealIndexEquiv I hI).symm

private theorem fractionalIdealIsLocalizedModule
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI : I ≠ 0) :
    IsLocalizedModule ℤ⁰
      ((Submodule.subtype I.coeToSubmodule).restrictScalars ℤ) := by
  rw [← Units.val_mk0 hI]
  infer_instance

/-- The rational basis of the number field obtained from the same selected
integer basis of a nonzero fractional ideal. -/
def fractionalIdealCommonFieldBasis
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI : I ≠ 0) :
    Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ K :=
  letI := fractionalIdealIsLocalizedModule I hI
  (fractionalIdealCommonBasis I hI).ofIsLocalizedModule ℚ ℤ⁰
    ((Submodule.subtype I.coeToSubmodule).restrictScalars ℤ)

@[simp]
theorem fractionalIdealCommonFieldBasis_apply
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI : I ≠ 0)
    (a : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    fractionalIdealCommonFieldBasis I hI a =
      ((fractionalIdealCommonBasis I hI a : I) : K) := by
  letI := fractionalIdealIsLocalizedModule I hI
  exact (fractionalIdealCommonBasis I hI).ofIsLocalizedModule_apply
    ℚ ℤ⁰ ((Submodule.subtype I.coeToSubmodule).restrictScalars ℤ) a

/-- Coordinate map whose inverse sends a standard coefficient vector to the
corresponding product of fractional-ideal basis vectors. -/
def coordinateBasisRepr (n : ℕ)
    (ideals : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (hne : ∀ i, ideals i ≠ 0) :
    coordinateModule n ideals ≃ₗ[ℤ]
      (Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 K) → ℤ) :=
  ((coordinateModulePiEquiv n ideals).restrictScalars ℤ).trans <|
    (LinearEquiv.piCongrRight fun i ↦
      (fractionalIdealCommonBasis (ideals i) (hne i)).equivFun).trans <|
        (LinearEquiv.curry ℤ ℤ (Fin n)
          (Module.Free.ChooseBasisIndex ℤ (𝓞 K))).symm

/-- The product integer basis of a coordinate pseudolattice. -/
def coordinateBasis (n : ℕ)
    (ideals : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (hne : ∀ i, ideals i ≠ 0) :
    Basis (Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℤ
      (coordinateModule n ideals) :=
  Basis.ofEquivFun (coordinateBasisRepr n ideals hne)

@[simp]
theorem coordinateBasis_apply_val (n : ℕ)
    (ideals : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (hne : ∀ i, ideals i ≠ 0)
    (ia : Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    ((coordinateBasis n ideals hne ia : coordinateModule n ideals) :
        Fin n → K) =
      Pi.single ia.1
        ((fractionalIdealCommonBasis (ideals ia.1) (hne ia.1) ia.2 :
          ideals ia.1) : K) := by
  classical
  rcases ia with ⟨i, a⟩
  let vfun : Fin n → K :=
    Pi.single i
      ((fractionalIdealCommonBasis (ideals i) (hne i) a :
        ideals i) : K)
  have hvfun : vfun ∈ coordinateModule n ideals := by
    rw [coordinateModule, Submodule.mem_pi]
    intro j _
    by_cases hji : j = i
    · subst j
      simpa [vfun] using
        (fractionalIdealCommonBasis (ideals i) (hne i) a).2
    · simp [vfun, hji]
  let v : coordinateModule n ideals := ⟨vfun, hvfun⟩
  have hv : coordinateBasis n ideals hne (i, a) = v := by
    apply (coordinateBasisRepr n ideals hne).injective
    ext jb
    have hleft :
        coordinateBasisRepr n ideals hne (coordinateBasis n ideals hne (i, a)) jb =
          if (i, a) = jb then 1 else 0 := by
      rw [← Basis.equivFun_ofEquivFun (coordinateBasisRepr n ideals hne)]
      exact (coordinateBasis n ideals hne).equivFun_self (i, a) jb
    have hright :
        coordinateBasisRepr n ideals hne v jb =
          if (i, a) = jb then 1 else 0 := by
      rcases jb with ⟨j, b⟩
      by_cases hij : i = j <;> by_cases hab : a = b
      · subst j
        subst b
        simp [coordinateBasisRepr, coordinateModulePiEquiv,
          v, vfun, fractionalIdealCommonBasis]
      · subst j
        simp [coordinateBasisRepr, coordinateModulePiEquiv,
          v, vfun, fractionalIdealCommonBasis, hab]
      · simp [coordinateBasisRepr, coordinateModulePiEquiv,
          v, vfun, fractionalIdealCommonBasis, hij]
        change ((NumberField.fractionalIdealBasis K (ideals j)).repr
          (0 : (ideals j).coeToSubmodule))
            ((fractionalIdealIndexEquiv (ideals j) (hne j)) b) = 0
        simp
      · simp [coordinateBasisRepr, coordinateModulePiEquiv,
          v, vfun, fractionalIdealCommonBasis, hij]
        change ((NumberField.fractionalIdealBasis K (ideals j)).repr
          (0 : (ideals j).coeToSubmodule))
            ((fractionalIdealIndexEquiv (ideals j) (hne j)) b) = 0
        simp
    exact hleft.trans hright.symm
  exact congrArg Subtype.val hv

/-- The rational product basis obtained from the common rational bases of
the fractional ideals.  The integral-basis index is placed first so that its
change matrix is literally block diagonal. -/
def coordinateFieldBasis (n : ℕ)
    (ideals : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (hne : ∀ i, ideals i ≠ 0) :
    Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 K) × Fin n) ℚ
      (Fin n → K) :=
  (Pi.basis fun i ↦ fractionalIdealCommonFieldBasis (ideals i) (hne i)).reindex
    ((Equiv.sigmaEquivProd (Fin n)
      (Module.Free.ChooseBasisIndex ℤ (𝓞 K))).trans
        (Equiv.prodComm (Fin n)
          (Module.Free.ChooseBasisIndex ℤ (𝓞 K))))

@[simp]
theorem coordinateFieldBasis_apply (n : ℕ)
    (ideals : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (hne : ∀ i, ideals i ≠ 0)
    (ai : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × Fin n) :
    coordinateFieldBasis n ideals hne ai =
      Pi.single ai.2
        (fractionalIdealCommonFieldBasis (ideals ai.2) (hne ai.2) ai.1) := by
  classical
  rcases ai with ⟨a, i⟩
  simp [coordinateFieldBasis]

/-- The coordinatewise integral basis of the number field, with the same
block ordering as `coordinateFieldBasis`. -/
def standardCoordinateFieldBasis (n : ℕ) :
    Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 K) × Fin n) ℚ
      (Fin n → K) :=
  (Pi.basis fun _ : Fin n ↦ NumberField.integralBasis K).reindex
    ((Equiv.sigmaEquivProd (Fin n)
      (Module.Free.ChooseBasisIndex ℤ (𝓞 K))).trans
        (Equiv.prodComm (Fin n)
          (Module.Free.ChooseBasisIndex ℤ (𝓞 K))))

@[simp]
theorem standardCoordinateFieldBasis_apply (n : ℕ)
    (ai : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × Fin n) :
    standardCoordinateFieldBasis (K := K) n ai =
      Pi.single ai.2 (NumberField.integralBasis K ai.1) := by
  classical
  rcases ai with ⟨a, i⟩
  simp [standardCoordinateFieldBasis]

@[simp]
theorem standardCoordinateFieldBasis_repr (n : ℕ) (x : Fin n → K)
    (ai : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × Fin n) :
    (standardCoordinateFieldBasis (K := K) n).repr x ai =
      (NumberField.integralBasis K).repr (x ai.2) ai.1 := by
  rcases ai with ⟨a, i⟩
  unfold standardCoordinateFieldBasis
  rw [Basis.repr_reindex_apply]
  rfl

/-- The coordinatewise change from the integral basis to the fractional-ideal
bases is block diagonal. -/
theorem standardCoordinateFieldBasis_toMatrix_coordinateFieldBasis
    (n : ℕ)
    (ideals : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (hne : ∀ i, ideals i ≠ 0) :
    (standardCoordinateFieldBasis (K := K) n).toMatrix
        (coordinateFieldBasis n ideals hne) =
      Matrix.blockDiagonal (fun i ↦
        (NumberField.integralBasis K).toMatrix
          (fractionalIdealCommonFieldBasis (ideals i) (hne i))) := by
  classical
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [Basis.toMatrix_apply, Matrix.blockDiagonal_apply]
  by_cases hij : i = j
  · subst j
    simp [Basis.toMatrix_apply]
  · simp [hij]

/-- The absolute determinant of a common fractional-ideal basis is its
fractional ideal norm. -/
theorem abs_det_fractionalIdealCommonFieldBasis
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI : I ≠ 0) :
    |(NumberField.integralBasis K).det
        (fractionalIdealCommonFieldBasis I hI)| =
      FractionalIdeal.absNorm I := by
  letI := fractionalIdealIsLocalizedModule I hI
  rw [show (fractionalIdealCommonFieldBasis I hI :
      Module.Free.ChooseBasisIndex ℤ (𝓞 K) → K) =
      fun a ↦ ((fractionalIdealCommonBasis I hI a : I) : K) by
    funext a
    exact fractionalIdealCommonFieldBasis_apply I hI a]
  unfold NumberField.integralBasis
  convert
    (FractionalIdeal.abs_det_basis_change
      (NumberField.RingOfIntegers.basis K) I
      (fractionalIdealCommonBasis I hI)) using 1 <;> rfl

/-- The product fractional-ideal norm is the absolute determinant of the
coordinatewise change of rational bases. -/
theorem abs_det_standardCoordinateFieldBasis_coordinateFieldBasis
    (n : ℕ)
    (ideals : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (hne : ∀ i, ideals i ≠ 0) :
    |(standardCoordinateFieldBasis (K := K) n).det
        (coordinateFieldBasis n ideals hne)| =
      ∏ i, FractionalIdeal.absNorm (ideals i) := by
  rw [Basis.det_apply,
    standardCoordinateFieldBasis_toMatrix_coordinateFieldBasis,
    Matrix.det_blockDiagonal, Finset.abs_prod]
  apply Finset.prod_congr rfl
  intro i _hi
  exact abs_det_fractionalIdealCommonFieldBasis (ideals i) (hne i)

/-- Principal fractional ideals commute with finite products. -/
theorem prod_spanSingleton {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → K) :
    ∏ i ∈ s, FractionalIdeal.spanSingleton
        (nonZeroDivisors (𝓞 K)) (f i) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
        (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, ih, FractionalIdeal.spanSingleton_mul_spanSingleton]

end NumberFieldLatticeModule

end

end NormEuclidean
