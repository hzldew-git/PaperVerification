import TraceEuclidean.PseudoBasis
import TraceEuclidean.TraceBasisDeterminant
import TraceEuclidean.TraceVolumeBridge
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Determinants attached to a pseudobasis

This file combines the integral bases of the fractional ideals in a
pseudobasis and compares the resulting rational basis with the canonical
ring-of-integers tower basis.  It supplies the determinant factor used by the
general covolume--discriminant bound.
-/

namespace TraceEuclidean

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

namespace GlobalLatticePresentation

/-- A selected pseudobasis for the full ring-of-integers lattice. -/
def pseudoBasis (P : GlobalLatticePresentation) :
    NumberFieldLatticeModule.PseudoBasis P.rank P.L :=
  Classical.choice
    (NumberFieldLatticeModule.exists_pseudoBasis P.rank P.L P.full)

/-- The field basis supplied by scalar extension of the selected
pseudobasis. -/
def pseudoFieldBasis (P : GlobalLatticePresentation) :
    Basis (Fin P.rank) P.field.1 (Fin P.rank → P.field.1) :=
  (Pi.basisFun P.field.1 (Fin P.rank)).map
    (P.pseudoBasis.ambientEquiv P.full)

@[simp]
theorem pseudoFieldBasis_apply (P : GlobalLatticePresentation)
    (i : Fin P.rank) :
    P.pseudoFieldBasis i =
      P.pseudoBasis.ambientEquiv P.full
        (Pi.single i (1 : P.field.1)) := by
  simp [pseudoFieldBasis, Pi.basisFun_apply]

/-- The product of the chosen integer bases of the pseudobasis ideals,
transported to the actual underlying integer lattice. -/
def pseudoIntegralBasis (P : GlobalLatticePresentation) :
    Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 P.field.1) × Fin P.rank)
      ℤ P.integralRestriction :=
  (((NumberFieldLatticeModule.coordinateBasis P.rank
      P.pseudoBasis.ideals P.pseudoBasis.ideals_ne).reindex
        (Equiv.prodComm (Fin P.rank)
          (Module.Free.ChooseBasisIndex ℤ (𝓞 P.field.1)))).map
      (P.pseudoBasis.equiv.restrictScalars ℤ)).map
        P.latticeEquivIntegralRestriction

/-- The rational product of the fractional-ideal bases, transported by the
ambient pseudobasis equivalence. -/
def pseudoRationalBasis (P : GlobalLatticePresentation) :
    Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 P.field.1) × Fin P.rank)
      ℚ (Fin P.rank → P.field.1) :=
  (NumberFieldLatticeModule.coordinateFieldBasis P.rank
      P.pseudoBasis.ideals P.pseudoBasis.ideals_ne).map
    ((P.pseudoBasis.ambientEquiv P.full).restrictScalars ℚ)

/-- The coordinatewise integral-basis product, transported through the same
ambient pseudobasis equivalence. -/
def pseudoStandardRationalBasis (P : GlobalLatticePresentation) :
    Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 P.field.1) × Fin P.rank)
      ℚ (Fin P.rank → P.field.1) :=
  (NumberFieldLatticeModule.standardCoordinateFieldBasis
      (K := P.field.1) P.rank).map
    ((P.pseudoBasis.ambientEquiv P.full).restrictScalars ℚ)

/-- The field Gram matrix in the field basis supplied by the pseudobasis. -/
def pseudoFieldGramMatrix (P : GlobalLatticePresentation) :
    Matrix (Fin P.rank) (Fin P.rank) P.field.1 :=
  LinearMap.BilinForm.toMatrix P.pseudoFieldBasis P.Q.associated

/-- Gram matrix of an arbitrary field-valued bilinear form in the field basis
supplied by the pseudobasis. -/
def pseudoGramMatrix (P : GlobalLatticePresentation)
    (B : LinearMap.BilinForm P.field.1
      (Fin P.rank → P.field.1)) :
    Matrix (Fin P.rank) (Fin P.rank) P.field.1 :=
  LinearMap.BilinForm.toMatrix P.pseudoFieldBasis B

@[simp]
theorem pseudoGramMatrix_associated (P : GlobalLatticePresentation) :
    P.pseudoGramMatrix P.Q.associated = P.pseudoFieldGramMatrix :=
  rfl

/-- The determinant fractional ideal attached to a bilinear form and a
pseudobasis: `(det B_z) (prod I_i)^2`. -/
def pseudoDeterminantFractionalIdeal (P : GlobalLatticePresentation)
    (B : LinearMap.BilinForm P.field.1
      (Fin P.rank → P.field.1)) :
    FractionalIdeal (nonZeroDivisors (𝓞 P.field.1)) P.field.1 :=
  FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 P.field.1))
      (P.pseudoGramMatrix B).det *
    (∏ i, P.pseudoBasis.ideals i) ^ (2 : ℕ)

/-- A pseudobasis coordinate `a e_i`, transported to an actual lattice
vector. -/
def pseudoLatticeVector (P : GlobalLatticePresentation)
    (i : Fin P.rank) (a : P.field.1)
    (ha : a ∈ P.pseudoBasis.ideals i) : P.L :=
  P.pseudoBasis.equiv
    ⟨Pi.single i a, by
      rw [NumberFieldLatticeModule.coordinateModule, Submodule.mem_pi]
      intro j _
      by_cases hji : j = i
      · subst j
        simpa using ha
      · simp [hji]⟩

@[simp]
theorem pseudoLatticeVector_val (P : GlobalLatticePresentation)
    (i : Fin P.rank) (a : P.field.1)
    (ha : a ∈ P.pseudoBasis.ideals i) :
    (P.pseudoLatticeVector i a ha).1 = a • P.pseudoFieldBasis i := by
  classical
  rw [pseudoLatticeVector, ← P.pseudoBasis.ambientEquiv_apply_mem P.full,
    P.pseudoFieldBasis_apply, ← map_smul]
  congr 1
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

/-- Integrality of a bilinear form on the lattice makes every pseudobasis
matrix entry integral after multiplication by its two coefficient ideals. -/
theorem pseudoGram_entry_ideal_le_one
    (P : GlobalLatticePresentation)
    (B : LinearMap.BilinForm P.field.1
      (Fin P.rank → P.field.1))
    (hB : ∀ x y : P.L, _root_.IsIntegral ℤ (B x.1 y.1))
    (i j : Fin P.rank) :
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 P.field.1))
          (P.pseudoGramMatrix B i j) *
        P.pseudoBasis.ideals i * P.pseudoBasis.ideals j ≤ 1 := by
  rw [mul_assoc, FractionalIdeal.spanSingleton_mul_le_iff]
  intro z hz
  refine FractionalIdeal.mul_induction_on hz ?_ ?_
  · intro a ha b hb
    rw [FractionalIdeal.mem_one_iff]
    have hInt := hB (P.pseudoLatticeVector i a ha)
      (P.pseudoLatticeVector j b hb)
    rw [P.pseudoLatticeVector_val, P.pseudoLatticeVector_val,
      map_smul, LinearMap.map_smul₂] at hInt
    obtain ⟨r, hr⟩ :=
      (IsIntegralClosure.isIntegral_iff
        (A := 𝓞 P.field.1)).mp hInt
    refine ⟨r, ?_⟩
    rw [hr]
    simp [pseudoGramMatrix, LinearMap.BilinForm.toMatrix_apply,
      smul_eq_mul]
    ring
  · intro x y hx hy
    simpa [mul_add] using
      (Submodule.add_mem
        ((1 : FractionalIdeal (nonZeroDivisors (𝓞 P.field.1))
          P.field.1).coeToSubmodule) hx hy)

/-- If a bilinear form is integral on the lattice, its pseudobasis
determinant fractional ideal is an integral ideal. -/
theorem pseudoDeterminantFractionalIdeal_le_one
    (P : GlobalLatticePresentation)
    (B : LinearMap.BilinForm P.field.1
      (Fin P.rank → P.field.1))
    (hB : ∀ x y : P.L, _root_.IsIntegral ℤ (B x.1 y.1)) :
    P.pseudoDeterminantFractionalIdeal B ≤ 1 := by
  classical
  let I : FractionalIdeal (nonZeroDivisors (𝓞 P.field.1)) P.field.1 :=
    ∏ i, P.pseudoBasis.ideals i
  let G := P.pseudoGramMatrix B
  have hperm (σ : Equiv.Perm (Fin P.rank)) :
      ∏ i, P.pseudoBasis.ideals (σ i) = I := by
    dsimp [I]
    simpa using
      (σ.prod_comp Finset.univ P.pseudoBasis.ideals (by simp))
  have hspan (σ : Equiv.Perm (Fin P.rank)) :
      ∏ i, FractionalIdeal.spanSingleton
          (nonZeroDivisors (𝓞 P.field.1)) (G (σ i) i) =
        FractionalIdeal.spanSingleton
          (nonZeroDivisors (𝓞 P.field.1)) (∏ i, G (σ i) i) := by
    simpa using
      (NumberFieldLatticeModule.prod_spanSingleton
        (K := P.field.1) Finset.univ (fun i ↦ G (σ i) i))
  have hterm (σ : Equiv.Perm (Fin P.rank)) :
      FractionalIdeal.spanSingleton
            (nonZeroDivisors (𝓞 P.field.1)) (∏ i, G (σ i) i) *
          I ^ (2 : ℕ) ≤ 1 := by
    have hprod :
        (∏ i, (FractionalIdeal.spanSingleton
              (nonZeroDivisors (𝓞 P.field.1)) (G (σ i) i) *
            P.pseudoBasis.ideals (σ i) * P.pseudoBasis.ideals i)) ≤
          (∏ _i : Fin P.rank,
            (1 : FractionalIdeal (nonZeroDivisors (𝓞 P.field.1))
              P.field.1)) := by
      apply Finset.prod_le_prod
      · intro i _hi
        exact bot_le
      intro i _hi
      exact P.pseudoGram_entry_ideal_le_one B hB (σ i) i
    have heq :
        (∏ i, (FractionalIdeal.spanSingleton
              (nonZeroDivisors (𝓞 P.field.1)) (G (σ i) i) *
            P.pseudoBasis.ideals (σ i) * P.pseudoBasis.ideals i)) =
          FractionalIdeal.spanSingleton
              (nonZeroDivisors (𝓞 P.field.1)) (∏ i, G (σ i) i) *
            I ^ (2 : ℕ) := by
      simp only [Finset.prod_mul_distrib]
      rw [hspan σ, hperm σ]
      simp only [pow_two]
      ac_rfl
    rw [← heq]
    exact hprod.trans_eq (by simp)
  unfold pseudoDeterminantFractionalIdeal
  change FractionalIdeal.spanSingleton
      (nonZeroDivisors (𝓞 P.field.1)) G.det * I ^ (2 : ℕ) ≤ 1
  rw [FractionalIdeal.spanSingleton_mul_le_iff]
  intro z hz
  rw [Matrix.det_apply, Finset.sum_mul]
  apply Submodule.sum_mem
  intro σ _hσ
  have ht :=
    (FractionalIdeal.spanSingleton_mul_le_iff.mp (hterm σ)) z hz
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs] using ht
  · simpa [hs] using
      (Submodule.neg_mem
        ((1 : FractionalIdeal (nonZeroDivisors (𝓞 P.field.1))
          P.field.1).coeToSubmodule) ht)

/-- Absolute norm of the pseudobasis determinant ideal. -/
theorem absNorm_pseudoDeterminantFractionalIdeal
    (P : GlobalLatticePresentation)
    (B : LinearMap.BilinForm P.field.1
      (Fin P.rank → P.field.1)) :
    FractionalIdeal.absNorm (P.pseudoDeterminantFractionalIdeal B) =
      |Algebra.norm ℚ (P.pseudoGramMatrix B).det| *
        (∏ i, FractionalIdeal.absNorm (P.pseudoBasis.ideals i)) ^
          (2 : ℕ) := by
  unfold pseudoDeterminantFractionalIdeal
  rw [map_mul, FractionalIdeal.absNorm_span_singleton,
    map_pow, map_prod]

/-- Nondegeneracy of the bilinear form makes the pseudobasis determinant
ideal nonzero. -/
theorem pseudoDeterminantFractionalIdeal_ne_zero
    (P : GlobalLatticePresentation)
    (B : LinearMap.BilinForm P.field.1
      (Fin P.rank → P.field.1))
    (hB : B.Nondegenerate) :
    P.pseudoDeterminantFractionalIdeal B ≠ 0 := by
  have hdet : (P.pseudoGramMatrix B).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
      P.pseudoFieldBasis).mp hB
  unfold pseudoDeterminantFractionalIdeal
  apply mul_ne_zero
  · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr hdet
  · apply pow_ne_zero
    exact Finset.prod_ne_zero_iff.mpr
      (fun i _hi ↦ P.pseudoBasis.ideals_ne i)

/-- A nonzero integral pseudobasis determinant ideal has absolute norm at
least one. -/
theorem one_le_absNorm_pseudoDeterminantFractionalIdeal
    (P : GlobalLatticePresentation)
    (B : LinearMap.BilinForm P.field.1
      (Fin P.rank → P.field.1))
    (hIntegral : ∀ x y : P.L, _root_.IsIntegral ℤ (B x.1 y.1))
    (hB : B.Nondegenerate) :
    (1 : ℚ) ≤
      FractionalIdeal.absNorm (P.pseudoDeterminantFractionalIdeal B) := by
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp
    (P.pseudoDeterminantFractionalIdeal_le_one B hIntegral)
  have hJne : J ≠ ⊥ := by
    intro hzero
    apply P.pseudoDeterminantFractionalIdeal_ne_zero B hB
    rw [← hJ, hzero]
    exact FractionalIdeal.coeIdeal_bot
  rw [← hJ, FractionalIdeal.coeIdeal_absNorm]
  exact_mod_cast
    (Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr hJne))

/-- Twice the associated bilinear form, whose values are integral for every
integral quadratic lattice. -/
def scaledAssociatedBilinearForm (P : GlobalLatticePresentation) :
    LinearMap.BilinForm P.field.1 (Fin P.rank → P.field.1) :=
  LinearMap.mk₂ P.field.1
    (fun x y ↦ 2 * QuadraticMap.associated P.Q x y)
    (by intro x x' y; simp only [map_add, LinearMap.add_apply, mul_add])
    (by intro a x y; simp [mul_left_comm])
    (by intro x y y'; simp [mul_add])
    (by intro a x y; simp [mul_left_comm])

@[simp]
theorem scaledAssociatedBilinearForm_apply
    (P : GlobalLatticePresentation)
    (x y : Fin P.rank → P.field.1) :
    P.scaledAssociatedBilinearForm x y =
      2 * QuadraticMap.associated P.Q x y := by
  rfl

/-- The scale-two bilinear form is integral on the lattice. -/
theorem scaledAssociatedBilinearForm_integral
    (P : GlobalLatticePresentation) (x y : P.L) :
    _root_.IsIntegral ℤ (P.scaledAssociatedBilinearForm x.1 y.1) := by
  have h := (P.scaledBilinearInteger x y).isIntegral_coe
  change _root_.IsIntegral ℤ
    (2 * QuadraticMap.associated P.Q x.1 y.1)
  rw [← P.scaledBilinearInteger_eq_two_associated x y]
  exact h

/-- Scaling the nondegenerate associated form by two preserves
nondegeneracy. -/
theorem scaledAssociatedBilinearForm_nondegenerate
    (P : GlobalLatticePresentation) :
    P.scaledAssociatedBilinearForm.Nondegenerate := by
  have hQ : P.Q.associated.Nondegenerate :=
    QuadraticMap.nondegenerate_associated_iff.mpr P.nondegenerate
  constructor
  · intro x hx
    exact hQ.1 x fun y ↦ by
      have hxy := hx y
      rw [P.scaledAssociatedBilinearForm_apply] at hxy
      exact (mul_eq_zero.mp hxy).resolve_left (by norm_num)
  · intro y hy
    exact hQ.2 y fun x ↦ by
      have hxy := hy x
      rw [P.scaledAssociatedBilinearForm_apply] at hxy
      exact (mul_eq_zero.mp hxy).resolve_left (by norm_num)

/-- Matrix of the scale-two form in the pseudobasis field basis. -/
theorem pseudoGramMatrix_scaledAssociated
    (P : GlobalLatticePresentation) :
    P.pseudoGramMatrix P.scaledAssociatedBilinearForm =
      (2 : P.field.1) • P.pseudoFieldGramMatrix := by
  ext i j
  simp [pseudoGramMatrix, pseudoFieldGramMatrix,
    LinearMap.BilinForm.toMatrix_apply]

/-- Scaling by two multiplies the pseudobasis field Gram determinant by
`2^rank`. -/
theorem det_pseudoGramMatrix_scaledAssociated
    (P : GlobalLatticePresentation) :
    (P.pseudoGramMatrix P.scaledAssociatedBilinearForm).det =
      (2 : P.field.1) ^ P.rank * P.pseudoFieldGramMatrix.det := by
  rw [P.pseudoGramMatrix_scaledAssociated, Matrix.det_smul]
  simp

/-- The scale-two determinant ideal norm has the exact factor
`2^(rank*degree)`. -/
theorem absNorm_pseudoDeterminantFractionalIdeal_scaledAssociated
    (P : GlobalLatticePresentation) :
    FractionalIdeal.absNorm
        (P.pseudoDeterminantFractionalIdeal
          P.scaledAssociatedBilinearForm) =
      (2 : ℚ) ^ (P.rank * P.degree) *
        FractionalIdeal.absNorm
          (P.pseudoDeterminantFractionalIdeal P.Q.associated) := by
  rw [P.absNorm_pseudoDeterminantFractionalIdeal,
    P.absNorm_pseudoDeterminantFractionalIdeal,
    P.det_pseudoGramMatrix_scaledAssociated,
    map_mul, map_pow, P.pseudoGramMatrix_associated]
  have hnormtwo :
      Algebra.norm ℚ (2 : P.field.1) = (2 : ℚ) ^ P.degree := by
    simpa [GlobalLatticePresentation.degree] using
      (Algebra.norm_natCast (R := ℚ) (S := P.field.1) 2)
  rw [hnormtwo]
  have hpow :
      ((2 : ℚ) ^ P.degree) ^ P.rank =
        (2 : ℚ) ^ (P.rank * P.degree) := by
    rw [← pow_mul, Nat.mul_comm P.degree P.rank]
  rw [abs_mul]
  simp only [abs_pow, abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 2)]
  rw [hpow]
  ring

@[simp]
theorem pseudoIntegralBasis_apply_val (P : GlobalLatticePresentation)
    (ai : Module.Free.ChooseBasisIndex ℤ (𝓞 P.field.1) × Fin P.rank) :
    (P.pseudoIntegralBasis ai).1 =
      P.pseudoBasis.ambientEquiv P.full
        (Pi.single ai.2
          (NumberFieldLatticeModule.fractionalIdealCommonFieldBasis
            (P.pseudoBasis.ideals ai.2)
            (P.pseudoBasis.ideals_ne ai.2) ai.1)) := by
  classical
  rcases ai with ⟨a, i⟩
  rw [pseudoIntegralBasis, Basis.map_apply, Basis.map_apply,
    Basis.reindex_apply]
  change
    (P.pseudoBasis.equiv
      ((NumberFieldLatticeModule.coordinateBasis P.rank
        P.pseudoBasis.ideals P.pseudoBasis.ideals_ne)
          ((i, a)))).1 = _
  rw [← P.pseudoBasis.ambientEquiv_apply_mem P.full]
  congr 1
  rw [NumberFieldLatticeModule.coordinateBasis_apply_val]
  simp

@[simp]
theorem pseudoRationalBasis_apply (P : GlobalLatticePresentation)
    (ai : Module.Free.ChooseBasisIndex ℤ (𝓞 P.field.1) × Fin P.rank) :
    P.pseudoRationalBasis ai =
      P.pseudoBasis.ambientEquiv P.full
        (Pi.single ai.2
          (NumberFieldLatticeModule.fractionalIdealCommonFieldBasis
            (P.pseudoBasis.ideals ai.2)
            (P.pseudoBasis.ideals_ne ai.2) ai.1)) := by
  simp [pseudoRationalBasis]

@[simp]
theorem pseudoStandardRationalBasis_apply
    (P : GlobalLatticePresentation)
    (ai : Module.Free.ChooseBasisIndex ℤ (𝓞 P.field.1) × Fin P.rank) :
    P.pseudoStandardRationalBasis ai =
      NumberField.integralBasis P.field.1 ai.1 •
        P.pseudoFieldBasis ai.2 := by
  classical
  rcases ai with ⟨a, i⟩
  rw [pseudoStandardRationalBasis, Basis.map_apply,
    NumberFieldLatticeModule.standardCoordinateFieldBasis_apply,
    P.pseudoFieldBasis_apply]
  change P.pseudoBasis.ambientEquiv P.full
      (Pi.single i (NumberField.integralBasis P.field.1 a)) =
    NumberField.integralBasis P.field.1 a •
      P.pseudoBasis.ambientEquiv P.full (Pi.single i 1)
  rw [← map_smul]
  congr 1
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

/-- Extending the transported integer pseudobasis to `ℚ` gives the
transported rational product basis. -/
theorem pseudoIntegralBasis_extend (P : GlobalLatticePresentation) :
    P.pseudoIntegralBasis.extendOfIsLattice ℚ = P.pseudoRationalBasis := by
  apply DFunLike.ext _ _
  intro ai
  rw [Basis.extendOfIsLattice_apply, P.pseudoRationalBasis_apply]
  exact P.pseudoIntegralBasis_apply_val ai

/-- Transporting both coordinate bases preserves their change matrix. -/
theorem pseudoStandard_toMatrix_pseudoRational
    (P : GlobalLatticePresentation) :
    P.pseudoStandardRationalBasis.toMatrix P.pseudoRationalBasis =
      (NumberFieldLatticeModule.standardCoordinateFieldBasis
        (K := P.field.1) P.rank).toMatrix
          (NumberFieldLatticeModule.coordinateFieldBasis P.rank
            P.pseudoBasis.ideals P.pseudoBasis.ideals_ne) := by
  ext i j
  simp [pseudoStandardRationalBasis, pseudoRationalBasis,
    Basis.toMatrix_apply]

/-- The absolute determinant of the pseudobasis change is the product of the
fractional ideal norms. -/
theorem abs_det_pseudoStandard_pseudoRational
    (P : GlobalLatticePresentation) :
    |P.pseudoStandardRationalBasis.det P.pseudoRationalBasis| =
      ∏ i, FractionalIdeal.absNorm (P.pseudoBasis.ideals i) := by
  rw [Basis.det_apply, P.pseudoStandard_toMatrix_pseudoRational,
    ← Basis.det_apply]
  exact
    NumberFieldLatticeModule.abs_det_standardCoordinateFieldBasis_coordinateFieldBasis
      P.rank P.pseudoBasis.ideals P.pseudoBasis.ideals_ne

/-- In the transported standard product basis, the trace Gram matrix is the
generic trace block matrix, with the two product indices swapped. -/
theorem traceGram_pseudoStandardRationalBasis_eq
    (P : GlobalLatticePresentation) :
    LinearMap.BilinForm.toMatrix P.pseudoStandardRationalBasis
        P.traceQuadraticForm.associated =
      Matrix.reindex
        (Equiv.prodComm (Fin P.rank)
          (Module.Free.ChooseBasisIndex ℤ (𝓞 P.field.1)))
        (Equiv.prodComm (Fin P.rank)
          (Module.Free.ChooseBasisIndex ℤ (𝓞 P.field.1)))
        (traceBlockMatrix (NumberField.integralBasis P.field.1)
          P.pseudoFieldGramMatrix) := by
  ext ⟨a, i⟩ ⟨c, j⟩
  rw [LinearMap.BilinForm.toMatrix_apply,
    P.pseudoStandardRationalBasis_apply,
    P.pseudoStandardRationalBasis_apply,
    P.traceQuadraticForm_associated]
  change
    Algebra.trace ℚ P.field.1
        (QuadraticMap.associated P.Q
          (NumberField.integralBasis P.field.1 a • P.pseudoFieldBasis i)
          (NumberField.integralBasis P.field.1 c • P.pseudoFieldBasis j)) =
      Algebra.trace ℚ P.field.1
        (NumberField.integralBasis P.field.1 a *
          NumberField.integralBasis P.field.1 c *
            P.pseudoFieldGramMatrix i j)
  rw [map_smul, LinearMap.map_smul₂]
  simp [pseudoFieldGramMatrix, LinearMap.BilinForm.toMatrix_apply,
    smul_eq_mul, mul_assoc, mul_left_comm]

/-- Exact trace determinant in the standard rational product basis attached
to the pseudobasis field basis. -/
theorem det_traceGram_pseudoStandardRationalBasis
    (P : GlobalLatticePresentation) :
    (LinearMap.BilinForm.toMatrix P.pseudoStandardRationalBasis
        P.traceQuadraticForm.associated).det =
      (NumberField.discr P.field.1 : ℚ) ^ P.rank *
        Algebra.norm ℚ P.pseudoFieldGramMatrix.det := by
  rw [P.traceGram_pseudoStandardRationalBasis_eq,
    Matrix.det_reindex_self, det_traceBlockMatrix,
    ← NumberField.coe_discr]
  simp

/-- Change-of-basis factorization of the trace determinant in the actual
pseudobasis product basis. -/
theorem det_traceGram_pseudoRationalBasis
    (P : GlobalLatticePresentation) :
    (LinearMap.BilinForm.toMatrix P.pseudoRationalBasis
        P.traceQuadraticForm.associated).det =
      (P.pseudoStandardRationalBasis.det P.pseudoRationalBasis) ^ (2 : ℕ) *
        ((NumberField.discr P.field.1 : ℚ) ^ P.rank *
          Algebra.norm ℚ P.pseudoFieldGramMatrix.det) := by
  rw [← P.det_traceGram_pseudoStandardRationalBasis]
  rw [← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
    (b := P.pseudoStandardRationalBasis) P.pseudoRationalBasis
    P.traceQuadraticForm.associated]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Basis.det_apply]
  ring

/-- Scalar extension sends an integral change-of-basis matrix to its rational
coefficientwise cast. -/
theorem integralBasisExtendedChangeMatrix_eq_map
    (P : GlobalLatticePresentation)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b b' : Basis ι ℤ P.integralRestriction) :
    (b.extendOfIsLattice ℚ).toMatrix (b'.extendOfIsLattice ℚ) =
      (algebraMap ℤ ℚ).mapMatrix (b.toMatrix b') := by
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Basis.toMatrix_apply,
    Basis.toMatrix_apply]
  let c : P.integralRestriction := b' j
  have hc := b.sum_repr c
  have hcval := congrArg (fun x : P.integralRestriction =>
    (x.1 : Fin P.rank → P.field.1)) hc
  rw [Basis.extendOfIsLattice_apply]
  have hsum :
      (c.1 : Fin P.rank → P.field.1) =
        ∑ k, ((b.repr c k : ℤ) : ℚ) • (b.extendOfIsLattice ℚ) k := by
    rw [← hcval]
    simp only [Basis.extendOfIsLattice_apply]
    rw [Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    exact (Submodule.coe_smul_of_tower (b.repr c k) (b k)).symm
  rw [hsum, map_sum]
  simp only [map_smul, Basis.repr_self]
  let f : ι →₀ ℚ :=
    Finsupp.mapRange (fun z : ℤ ↦ (z : ℚ)) (by simp) (b.repr c)
  have hfsum : ∑ x, f x • Finsupp.single x (1 : ℚ) = f := by
    calc
      _ = ∑ x, Finsupp.single x (f x) := by
        apply Finset.sum_congr rfl
        intro x _hx
        exact Finsupp.smul_single_one x (f x)
      _ = f.sum Finsupp.single := by
        rw [Finsupp.sum_fintype]
        intro x
        simp
      _ = f := Finsupp.sum_single f
  change (∑ x, ((b.repr c x : ℤ) : ℚ) •
    Finsupp.single x (1 : ℚ)) i = _
  have hfcoeff (x) : ((b.repr c x : ℤ) : ℚ) = f x := by
    simp [f]
  simp_rw [hfcoeff]
  rw [hfsum]
  simp [f, c]

/-- A change between two integer bases has determinant square one after
casting to the rationals. -/
theorem integralBasisChangeDet_sq
    (P : GlobalLatticePresentation)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b b' : Basis ι ℤ P.integralRestriction) :
    ((b.toMatrix b').det : ℚ) ^ (2 : ℕ) = 1 := by
  have hu : IsUnit (b.det b') := b.isUnit_det b'
  rw [b.det_apply, Int.isUnit_iff] at hu
  rcases hu with hu | hu <;> rw [hu] <;> norm_num

/-- The chosen integral lattice basis, reindexed by the product index of the
pseudobasis. -/
def integralLatticeBasisOnPseudoIndex (P : GlobalLatticePresentation) :
    Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 P.field.1) × Fin P.rank)
      ℤ P.integralRestriction :=
  P.integralRestrictionBasis.reindex
    (P.integralRestrictionBasis.indexEquiv P.pseudoIntegralBasis)

/-- Extending the reindexed chosen basis gives the corresponding reindexing
of the selected rational trace basis. -/
theorem integralLatticeBasisOnPseudoIndex_extend
    (P : GlobalLatticePresentation) :
    P.integralLatticeBasisOnPseudoIndex.extendOfIsLattice ℚ =
      P.rationalTraceBasis.reindex
        (P.integralRestrictionBasis.indexEquiv P.pseudoIntegralBasis) := by
  ext i
  simp [integralLatticeBasisOnPseudoIndex,
    GlobalLatticePresentation.rationalTraceBasis]

/-- The trace Gram determinant in the reindexed chosen basis is the existing
integral trace Gram determinant. -/
theorem det_traceGram_integralLatticeBasisOnPseudoIndex
    (P : GlobalLatticePresentation) :
    (LinearMap.BilinForm.toMatrix
        (P.integralLatticeBasisOnPseudoIndex.extendOfIsLattice ℚ)
        P.traceQuadraticForm.associated).det =
      P.integralTraceGramMatrix.det := by
  rw [P.integralLatticeBasisOnPseudoIndex_extend]
  have hmatrix :
      LinearMap.BilinForm.toMatrix
          (P.rationalTraceBasis.reindex
            (P.integralRestrictionBasis.indexEquiv P.pseudoIntegralBasis))
          P.traceQuadraticForm.associated =
        Matrix.reindex
          (P.integralRestrictionBasis.indexEquiv P.pseudoIntegralBasis)
          (P.integralRestrictionBasis.indexEquiv P.pseudoIntegralBasis)
          P.integralTraceGramMatrix := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, Matrix.reindex_apply,
      integralTraceGramMatrix, P.traceQuadraticForm_associated]
  rw [hmatrix, Matrix.det_reindex_self]

/-- The trace Gram determinant in the transported pseudobasis product basis
is the determinant of the actual integral trace lattice. -/
theorem det_traceGram_pseudoRationalBasis_eq_integralTraceGramMatrix
    (P : GlobalLatticePresentation) :
    (LinearMap.BilinForm.toMatrix P.pseudoRationalBasis
        P.traceQuadraticForm.associated).det =
      P.integralTraceGramMatrix.det := by
  let b := P.pseudoIntegralBasis
  let b' := P.integralLatticeBasisOnPseudoIndex
  have hchange :
      P.pseudoRationalBasis.toMatrix
          (P.integralLatticeBasisOnPseudoIndex.extendOfIsLattice ℚ) =
        (algebraMap ℤ ℚ).mapMatrix
          (P.pseudoIntegralBasis.toMatrix
            P.integralLatticeBasisOnPseudoIndex) := by
    rw [← P.pseudoIntegralBasis_extend]
    exact P.integralBasisExtendedChangeMatrix_eq_map
      P.pseudoIntegralBasis P.integralLatticeBasisOnPseudoIndex
  have hfactor := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
    (b := P.pseudoRationalBasis)
    (P.integralLatticeBasisOnPseudoIndex.extendOfIsLattice ℚ)
    P.traceQuadraticForm.associated
  rw [← P.det_traceGram_integralLatticeBasisOnPseudoIndex]
  symm
  rw [← hfactor, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    hchange, ← RingHom.map_det]
  calc
    (algebraMap ℤ ℚ)
          (P.pseudoIntegralBasis.toMatrix
            P.integralLatticeBasisOnPseudoIndex).det *
        (LinearMap.BilinForm.toMatrix P.pseudoRationalBasis
          P.traceQuadraticForm.associated).det *
        (algebraMap ℤ ℚ)
          (P.pseudoIntegralBasis.toMatrix
            P.integralLatticeBasisOnPseudoIndex).det =
      ((P.pseudoIntegralBasis.toMatrix
        P.integralLatticeBasisOnPseudoIndex).det : ℚ) ^ (2 : ℕ) *
        (LinearMap.BilinForm.toMatrix P.pseudoRationalBasis
          P.traceQuadraticForm.associated).det := by
      change ((P.pseudoIntegralBasis.toMatrix
          P.integralLatticeBasisOnPseudoIndex).det : ℚ) * _ *
        ((P.pseudoIntegralBasis.toMatrix
          P.integralLatticeBasisOnPseudoIndex).det : ℚ) = _
      ring
    _ = (LinearMap.BilinForm.toMatrix P.pseudoRationalBasis
          P.traceQuadraticForm.associated).det := by
      rw [P.integralBasisChangeDet_sq P.pseudoIntegralBasis
        P.integralLatticeBasisOnPseudoIndex, one_mul]

/-- Absolute determinant form of the general pseudobasis trace-volume
identity. -/
theorem abs_integralTraceGramDet_eq_discr_pow_absNorm_pseudo
    (P : GlobalLatticePresentation) :
    |P.integralTraceGramMatrix.det| =
      |(NumberField.discr P.field.1 : ℚ)| ^ P.rank *
        FractionalIdeal.absNorm
          (P.pseudoDeterminantFractionalIdeal P.Q.associated) := by
  rw [← P.det_traceGram_pseudoRationalBasis_eq_integralTraceGramMatrix,
    P.det_traceGram_pseudoRationalBasis,
    abs_mul, abs_pow, abs_mul, abs_pow,
    P.absNorm_pseudoDeterminantFractionalIdeal,
    P.abs_det_pseudoStandard_pseudoRational]
  change
    (∏ i, FractionalIdeal.absNorm (P.pseudoBasis.ideals i)) ^ 2 *
        (|(NumberField.discr P.field.1 : ℚ)| ^ P.rank *
          |Algebra.norm ℚ P.pseudoFieldGramMatrix.det|) =
      |(NumberField.discr P.field.1 : ℚ)| ^ P.rank *
        (|Algebra.norm ℚ P.pseudoFieldGramMatrix.det| *
          (∏ i, FractionalIdeal.absNorm (P.pseudoBasis.ideals i)) ^ 2)
  ring

/-- Real covolume form of the pseudobasis trace-volume identity. -/
theorem euclideanCovolume_sq_eq_discr_pow_absNorm_pseudo
    (P : GlobalLatticePresentation) :
    ZLattice.covolume P.euclideanIntegralLattice ^ (2 : ℕ) =
      ((|NumberField.discr P.field.1| : ℤ) : ℝ) ^ P.rank *
        ((FractionalIdeal.absNorm
          (P.pseudoDeterminantFractionalIdeal P.Q.associated) : ℚ) : ℝ) := by
  have hnonneg : 0 ≤ P.integralTraceGramMatrix.det := by
    have hreal :
        (0 : ℝ) ≤ ((P.integralTraceGramMatrix.det : ℚ) : ℝ) := by
      rw [← P.euclideanCovolume_sq_eq_integralTraceGramDet]
      positivity
    exact_mod_cast hreal
  rw [P.euclideanCovolume_sq_eq_integralTraceGramDet,
    ← abs_of_nonneg hnonneg,
    P.abs_integralTraceGramDet_eq_discr_pow_absNorm_pseudo]
  norm_cast

/-- Classic integrality gives the sharp lower bound by the field
discriminant.  This is the projective-lattice version: no freeness
assumption is present. -/
theorem discriminant_pow_le_euclideanCovolume_sq_of_classic
    (P : GlobalLatticePresentation) (hclassic : P.IsClassicIntegral) :
    ((|NumberField.discr P.field.1| : ℤ) : ℝ) ^ P.rank ≤
      ZLattice.covolume P.euclideanIntegralLattice ^ (2 : ℕ) := by
  have hnormQ :
      (1 : ℚ) ≤ FractionalIdeal.absNorm
        (P.pseudoDeterminantFractionalIdeal P.Q.associated) :=
    P.one_le_absNorm_pseudoDeterminantFractionalIdeal P.Q.associated
      hclassic
      (QuadraticMap.nondegenerate_associated_iff.mpr P.nondegenerate)
  have hnormR :
      (1 : ℝ) ≤
        ((FractionalIdeal.absNorm
          (P.pseudoDeterminantFractionalIdeal P.Q.associated) : ℚ) : ℝ) := by
    exact_mod_cast hnormQ
  rw [P.euclideanCovolume_sq_eq_discr_pow_absNorm_pseudo]
  nlinarith [mul_le_mul_of_nonneg_left hnormR
    (show 0 ≤ ((|NumberField.discr P.field.1| : ℤ) : ℝ) ^ P.rank by positivity)]

/-- Ordinary integrality gives the corresponding scale-two lower bound.
The factor is exactly `2^(rank*degree)`. -/
theorem discriminant_pow_le_two_pow_mul_euclideanCovolume_sq
    (P : GlobalLatticePresentation) :
    ((|NumberField.discr P.field.1| : ℤ) : ℝ) ^ P.rank ≤
      (2 : ℝ) ^ (P.rank * P.degree) *
        ZLattice.covolume P.euclideanIntegralLattice ^ (2 : ℕ) := by
  have hscaledQ :
      (1 : ℚ) ≤ FractionalIdeal.absNorm
        (P.pseudoDeterminantFractionalIdeal
          P.scaledAssociatedBilinearForm) :=
    P.one_le_absNorm_pseudoDeterminantFractionalIdeal
      P.scaledAssociatedBilinearForm
      P.scaledAssociatedBilinearForm_integral
      P.scaledAssociatedBilinearForm_nondegenerate
  rw [P.absNorm_pseudoDeterminantFractionalIdeal_scaledAssociated] at hscaledQ
  have hscaledR :
      (1 : ℝ) ≤ (2 : ℝ) ^ (P.rank * P.degree) *
        ((FractionalIdeal.absNorm
          (P.pseudoDeterminantFractionalIdeal P.Q.associated) : ℚ) : ℝ) := by
    exact_mod_cast hscaledQ
  rw [P.euclideanCovolume_sq_eq_discr_pow_absNorm_pseudo]
  have hdisc :
      0 ≤ ((|NumberField.discr P.field.1| : ℤ) : ℝ) ^ P.rank := by
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hscaledR hdisc]

end GlobalLatticePresentation

end

end TraceEuclidean
