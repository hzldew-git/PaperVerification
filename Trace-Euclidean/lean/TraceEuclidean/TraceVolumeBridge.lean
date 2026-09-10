import TraceEuclidean.TraceCovering
import TraceEuclidean.TraceDeterminant
import TraceEuclidean.VolumeIdeals
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
The arithmetic bridge between the rational trace Gram determinant and the
classic volume ideal.  The main results in this file cover lattices that are
free over the ring of integers.  This includes the principal-ideal case and
isolates the additional determinant-module input needed for a general
projective lattice over a Dedekind domain.
-/

namespace TraceEuclidean

open Module
open Matrix
open scoped NumberField

noncomputable section

namespace GlobalLatticePresentation

/-- Install the lattice condition when extending a basis to the fraction field. -/
private local instance (P : GlobalLatticePresentation) :
    P.L.IsLattice P.field.1 :=
  P.full

/-- A free full lattice has the manuscript rank over the ring of integers. -/
theorem freeLattice_finrank (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] :
    Module.finrank (𝓞 P.field.1) P.L = P.rank := by
  let b := Module.Free.chooseBasis (𝓞 P.field.1) P.L
  rw [Module.finrank_eq_card_basis b,
    ← Module.finrank_eq_card_basis (b.extendOfIsLattice P.field.1)]
  simp

/-- A chosen ring-of-integers basis of a free lattice, indexed by its rank. -/
def freeLatticeBasis (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] :
    Basis (Fin P.rank) (𝓞 P.field.1) P.L :=
  Module.finBasisOfFinrankEq (𝓞 P.field.1) P.L P.freeLattice_finrank

/-- The field basis obtained by extending the chosen free lattice basis. -/
def freeLatticeFieldBasis (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] :
    Basis (Fin P.rank) P.field.1 (Fin P.rank → P.field.1) :=
  P.freeLatticeBasis.extendOfIsLattice P.field.1

@[simp]
theorem freeLatticeFieldBasis_apply (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] (i : Fin P.rank) :
    P.freeLatticeFieldBasis i = (P.freeLatticeBasis i).1 := by
  simp [freeLatticeFieldBasis]

/-- The classic integral pairing as a bilinear form on a free lattice. -/
def classicBilinearForm (P : GlobalLatticePresentation)
    (hclassic : P.IsClassicIntegral) :
    LinearMap.BilinForm (𝓞 P.field.1) P.L :=
  LinearMap.mk₂ (𝓞 P.field.1) (fun x y ↦ P.classicBilinearInteger hclassic x y)
    (by
      intro x x' y
      apply NumberField.RingOfIntegers.coe_injective
      simp [classicBilinearInteger])
    (by
      intro a x y
      apply NumberField.RingOfIntegers.coe_injective
      simp [classicBilinearInteger, Algebra.smul_def])
    (by
      intro x y y'
      apply NumberField.RingOfIntegers.coe_injective
      simp [classicBilinearInteger])
    (by
      intro a x y
      apply NumberField.RingOfIntegers.coe_injective
      simp [classicBilinearInteger, Algebra.smul_def])

@[simp]
theorem classicBilinearForm_apply (P : GlobalLatticePresentation)
    (hclassic : P.IsClassicIntegral) (x y : P.L) :
    P.classicBilinearForm hclassic x y =
      P.classicBilinearInteger hclassic x y :=
  rfl

/-- The existing Gram matrix is the matrix of the integral bilinear form. -/
theorem classicGramMatrix_eq_toMatrix (P : GlobalLatticePresentation)
    (hclassic : P.IsClassicIntegral) (v : Fin P.rank → P.L) :
    P.classicGramMatrix hclassic v =
      Matrix.of fun i j ↦ P.classicBilinearForm hclassic (v i) (v j) := by
  rfl

/-- Basis-specialized form of `classicGramMatrix_eq_toMatrix`. -/
theorem classicGramMatrix_eq_bilin_toMatrix (P : GlobalLatticePresentation)
    (hclassic : P.IsClassicIntegral) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι (𝓞 P.field.1) P.L) :
    Matrix.of (fun i j ↦ P.classicBilinearInteger hclassic (b i) (b j)) =
      LinearMap.BilinForm.toMatrix b (P.classicBilinearForm hclassic) := by
  ext i j
  simp [LinearMap.BilinForm.toMatrix_apply]

/-- The lattice endomorphism carrying the selected free basis to `v`. -/
def freeLatticeEnd (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] (v : Fin P.rank → P.L) :
    P.L →ₗ[𝓞 P.field.1] P.L :=
  P.freeLatticeBasis.constr (𝓞 P.field.1) v

@[simp]
theorem freeLatticeEnd_basis (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] (v : Fin P.rank → P.L)
    (i : Fin P.rank) :
    P.freeLatticeEnd v (P.freeLatticeBasis i) = v i := by
  simp [freeLatticeEnd]

/-- Gram matrices of lattice tuples are obtained by integral congruence from
the Gram matrix of a free lattice basis. -/
theorem classicGramMatrix_eq_congruence_free (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] (hclassic : P.IsClassicIntegral)
    (v : Fin P.rank → P.L) :
    P.classicGramMatrix hclassic v =
      Matrix.transpose
          (LinearMap.toMatrix P.freeLatticeBasis P.freeLatticeBasis
            (P.freeLatticeEnd v)) *
        P.classicGramMatrix hclassic P.freeLatticeBasis *
      LinearMap.toMatrix P.freeLatticeBasis P.freeLatticeBasis
        (P.freeLatticeEnd v) := by
  let B := P.classicBilinearForm hclassic
  let f := P.freeLatticeEnd v
  calc
    P.classicGramMatrix hclassic v =
        LinearMap.BilinForm.toMatrix P.freeLatticeBasis (B.comp f f) := by
      ext i j
      simp [B, f, classicGramMatrix, LinearMap.BilinForm.toMatrix_apply]
    _ = Matrix.transpose
          (LinearMap.toMatrix P.freeLatticeBasis P.freeLatticeBasis f) *
          LinearMap.BilinForm.toMatrix P.freeLatticeBasis B *
        LinearMap.toMatrix P.freeLatticeBasis P.freeLatticeBasis f :=
      B.toMatrix_comp P.freeLatticeBasis P.freeLatticeBasis f f
    _ = (LinearMap.toMatrix P.freeLatticeBasis P.freeLatticeBasis
          (P.freeLatticeEnd v))ᵀ *
          P.classicGramMatrix hclassic P.freeLatticeBasis *
        LinearMap.toMatrix P.freeLatticeBasis P.freeLatticeBasis
          (P.freeLatticeEnd v) := by
      dsimp only [B, f]
      rw [← P.classicGramMatrix_eq_bilin_toMatrix hclassic P.freeLatticeBasis]
      rfl

/-- Every full Gram determinant is a multiple of the determinant on a free
lattice basis. -/
theorem classicGramDet_basis_dvd (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] (hclassic : P.IsClassicIntegral)
    (v : Fin P.rank → P.L) :
    P.classicGramDet hclassic P.freeLatticeBasis ∣
      P.classicGramDet hclassic v := by
  let A := LinearMap.toMatrix P.freeLatticeBasis P.freeLatticeBasis
    (P.freeLatticeEnd v)
  refine ⟨A.det ^ 2, ?_⟩
  rw [classicGramDet, P.classicGramMatrix_eq_congruence_free hclassic v,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  change A.det * (P.classicGramMatrix hclassic P.freeLatticeBasis).det * A.det =
    (P.classicGramMatrix hclassic P.freeLatticeBasis).det * A.det ^ 2
  ring

/-- For a free lattice the intrinsic volume ideal is principal, generated by
the Gram determinant of any integral basis. -/
theorem classicVolumeIdealOf_eq_span_freeGramDet
    (P : GlobalLatticePresentation) [Module.Free (𝓞 P.field.1) P.L]
    (hclassic : P.IsClassicIntegral) :
    P.classicVolumeIdealOf hclassic =
      Ideal.span ({P.classicGramDet hclassic P.freeLatticeBasis} :
        Set (𝓞 P.field.1)) := by
  apply le_antisymm
  · rw [classicVolumeIdealOf]
    refine Ideal.span_le.2 ?_
    rintro x ⟨v, rfl⟩
    exact Ideal.mem_span_singleton.2 (P.classicGramDet_basis_dvd hclassic v)
  · refine Ideal.span_le.2 ?_
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact Ideal.subset_span
      (show P.classicGramDet hclassic P.freeLatticeBasis ∈
        Set.range (P.classicGramDet hclassic) from
          ⟨P.freeLatticeBasis, rfl⟩)

/-- The field-valued Gram matrix on the extended free lattice basis. -/
def freeFieldGramMatrix (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] :
    Matrix (Fin P.rank) (Fin P.rank) P.field.1 :=
  LinearMap.BilinForm.toMatrix P.freeLatticeFieldBasis P.Q.associated

/-- Coercing the integral Gram matrix to the number field gives the field Gram matrix. -/
theorem map_freeClassicGramMatrix (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] (hclassic : P.IsClassicIntegral) :
    (algebraMap (𝓞 P.field.1) P.field.1).mapMatrix
        (P.classicGramMatrix hclassic P.freeLatticeBasis) =
      P.freeFieldGramMatrix := by
  ext i j
  simp [freeFieldGramMatrix, classicGramMatrix,
    LinearMap.BilinForm.toMatrix_apply]

/-- The field Gram determinant is the coercion of the integral Gram determinant. -/
theorem det_freeFieldGramMatrix (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] (hclassic : P.IsClassicIntegral) :
    P.freeFieldGramMatrix.det =
      algebraMap (𝓞 P.field.1) P.field.1
        (P.classicGramDet hclassic P.freeLatticeBasis) := by
  rw [← P.map_freeClassicGramMatrix hclassic,
    ← (algebraMap (𝓞 P.field.1) P.field.1).map_det]
  rfl

/-- Determinant of the trace Gram matrix in the free tower basis, expressed
with the number-field discriminant and the integral Gram norm. -/
theorem det_freeTraceBlockMatrix (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] (hclassic : P.IsClassicIntegral) :
    (traceBlockMatrix (NumberField.integralBasis P.field.1)
        P.freeFieldGramMatrix).det =
      (NumberField.discr P.field.1 : ℚ) ^ P.rank *
        (Algebra.norm ℤ
          (P.classicGramDet hclassic P.freeLatticeBasis) : ℚ) := by
  rw [det_traceBlockMatrix, ← NumberField.coe_discr,
    P.det_freeFieldGramMatrix hclassic,
    ← Algebra.coe_norm_int]
  simp

/-- Absolute-value form of the free trace determinant identity, in terms of
the intrinsic classic volume ideal. -/
theorem abs_det_freeTraceBlockMatrix (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] (hclassic : P.IsClassicIntegral) :
    |(traceBlockMatrix (NumberField.integralBasis P.field.1)
        P.freeFieldGramMatrix).det| =
      |(NumberField.discr P.field.1 : ℚ)| ^ P.rank *
        (Ideal.absNorm (P.classicVolumeIdealOf hclassic) : ℚ) := by
  rw [P.det_freeTraceBlockMatrix hclassic, abs_mul, abs_pow,
    P.classicVolumeIdealOf_eq_span_freeGramDet hclassic,
    Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs]

/-- The product basis of a free lattice over `ℤ`, with lattice index first. -/
def latticeEquivIntegralRestriction (P : GlobalLatticePresentation) :
    P.L ≃ₗ[ℤ] P.integralRestriction where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def freeIntegralTowerBasis (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] :
    Basis (Fin P.rank × Module.Free.ChooseBasisIndex ℤ (𝓞 P.field.1))
      ℤ P.integralRestriction :=
  ((NumberField.RingOfIntegers.basis P.field.1).smulTower'
    P.freeLatticeBasis).map P.latticeEquivIntegralRestriction

@[simp]
theorem freeIntegralTowerBasis_apply (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L]
    (ia : Fin P.rank × Module.Free.ChooseBasisIndex ℤ (𝓞 P.field.1)) :
    (P.freeIntegralTowerBasis ia).1 =
      algebraMap (𝓞 P.field.1) P.field.1
          (NumberField.RingOfIntegers.basis P.field.1 ia.2) •
        (P.freeLatticeBasis ia.1).1 := by
  change
    (P.latticeEquivIntegralRestriction
      (((NumberField.RingOfIntegers.basis P.field.1).smulTower'
        P.freeLatticeBasis) ia)).1 = _
  rw [Basis.smulTower'_apply]
  rfl

/-- The corresponding product basis after extension to `ℚ`. -/
def freeRationalTowerBasis (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] :
    Basis (Fin P.rank × Module.Free.ChooseBasisIndex ℤ (𝓞 P.field.1))
      ℚ (Fin P.rank → P.field.1) :=
  (NumberField.integralBasis P.field.1).smulTower'
    P.freeLatticeFieldBasis

@[simp]
theorem freeRationalTowerBasis_apply (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L]
    (ia : Fin P.rank × Module.Free.ChooseBasisIndex ℤ (𝓞 P.field.1)) :
    P.freeRationalTowerBasis ia =
      NumberField.integralBasis P.field.1 ia.2 •
        P.freeLatticeFieldBasis ia.1 := by
  simp [freeRationalTowerBasis, Basis.smulTower'_apply]

/-- Extending the integral product basis to `ℚ` gives the rational product basis. -/
theorem freeIntegralTowerBasis_extend (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] :
    P.freeIntegralTowerBasis.extendOfIsLattice ℚ =
      P.freeRationalTowerBasis := by
  apply DFunLike.ext _ _
  intro ia
  rw [Basis.extendOfIsLattice_apply, P.freeRationalTowerBasis_apply]
  funext x
  change (P.freeIntegralTowerBasis ia).1 x =
    (NumberField.integralBasis P.field.1 ia.2 •
      P.freeLatticeFieldBasis ia.1) x
  rw [P.freeIntegralTowerBasis_apply, NumberField.integralBasis_apply,
    P.freeLatticeFieldBasis_apply]

/-- The chosen integral lattice basis, reindexed by the product index of a
free integer-ring basis and the integral basis of the field. -/
def freeIntegralLatticeBasisOnTowerIndex (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] :
    Basis (Fin P.rank × Module.Free.ChooseBasisIndex ℤ (𝓞 P.field.1))
      ℤ P.integralRestriction :=
  P.integralRestrictionBasis.reindex
    (P.integralRestrictionBasis.indexEquiv P.freeIntegralTowerBasis)

/-- Extending the reindexed integral lattice basis gives the corresponding
reindexing of the selected rational trace basis. -/
theorem freeIntegralLatticeBasisOnTowerIndex_extend
    (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] :
    P.freeIntegralLatticeBasisOnTowerIndex.extendOfIsLattice ℚ =
      P.rationalTraceBasis.reindex
        (P.integralRestrictionBasis.indexEquiv P.freeIntegralTowerBasis) := by
  ext i
  simp [freeIntegralLatticeBasisOnTowerIndex,
    GlobalLatticePresentation.rationalTraceBasis]

/-- Extending a change-of-integral-basis matrix from `ℤ` to `ℚ` gives the
change matrix between the extended rational bases. -/
theorem freeExtendedChangeMatrix_eq_map (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] :
    (P.freeIntegralTowerBasis.extendOfIsLattice ℚ).toMatrix
        (P.freeIntegralLatticeBasisOnTowerIndex.extendOfIsLattice ℚ) =
      (algebraMap ℤ ℚ).mapMatrix
        (P.freeIntegralTowerBasis.toMatrix
          P.freeIntegralLatticeBasisOnTowerIndex) := by
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Basis.toMatrix_apply,
    Basis.toMatrix_apply]
  let c : P.integralRestriction :=
    P.freeIntegralLatticeBasisOnTowerIndex j
  have hc := P.freeIntegralTowerBasis.sum_repr c
  have hcval := congrArg (fun x : P.integralRestriction =>
    (x.1 : Fin P.rank → P.field.1)) hc
  rw [Basis.extendOfIsLattice_apply]
  have hsum :
      (c.1 : Fin P.rank → P.field.1) =
        ∑ k, ((P.freeIntegralTowerBasis.repr c k : ℤ) : ℚ) •
          (P.freeIntegralTowerBasis.extendOfIsLattice ℚ) k := by
    rw [← hcval]
    simp only [Basis.extendOfIsLattice_apply]
    rw [Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    exact (Submodule.coe_smul_of_tower
      (P.freeIntegralTowerBasis.repr c k)
      (P.freeIntegralTowerBasis k)).symm
  rw [hsum, map_sum]
  simp only [map_smul, Basis.repr_self]
  let f :
      (Fin P.rank × Module.Free.ChooseBasisIndex ℤ (𝓞 P.field.1)) →₀ ℚ :=
    Finsupp.mapRange (fun z : ℤ ↦ (z : ℚ)) (by simp)
      (P.freeIntegralTowerBasis.repr c)
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
  change (∑ x, ((P.freeIntegralTowerBasis.repr c x : ℤ) : ℚ) •
    Finsupp.single x (1 : ℚ)) i = _
  have hfcoeff (x) :
      ((P.freeIntegralTowerBasis.repr c x : ℤ) : ℚ) = f x := by
    simp [f]
  simp_rw [hfcoeff]
  rw [hfsum]
  simp [f, c]

/-- The square of the determinant of the integral change matrix is one. -/
theorem freeIntegralChangeDet_sq (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] :
    ((P.freeIntegralTowerBasis.toMatrix
      P.freeIntegralLatticeBasisOnTowerIndex).det : ℚ) ^ (2 : ℕ) = 1 := by
  have hu : IsUnit
      (P.freeIntegralTowerBasis.det
        P.freeIntegralLatticeBasisOnTowerIndex) :=
    P.freeIntegralTowerBasis.isUnit_det
      P.freeIntegralLatticeBasisOnTowerIndex
  rw [P.freeIntegralTowerBasis.det_apply, Int.isUnit_iff] at hu
  rcases hu with hu | hu <;> rw [hu] <;> norm_num

/-- In the free product basis, the rational trace Gram matrix is the generic
trace block matrix. -/
theorem traceGram_freeRationalTowerBasis_eq
    (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] :
    LinearMap.BilinForm.toMatrix P.freeRationalTowerBasis
        P.traceQuadraticForm.associated =
      traceBlockMatrix (NumberField.integralBasis P.field.1)
        P.freeFieldGramMatrix := by
  ext ⟨i, a⟩ ⟨j, c⟩
  rw [LinearMap.BilinForm.toMatrix_apply, traceBlockMatrix,
    P.freeRationalTowerBasis_apply, P.freeRationalTowerBasis_apply,
    P.traceQuadraticForm_associated]
  rw [map_smul, LinearMap.map_smul₂]
  simp [freeFieldGramMatrix, LinearMap.BilinForm.toMatrix_apply,
    smul_eq_mul, mul_assoc, mul_left_comm]

/-- The determinant in the reindexed extended integral basis is the existing
determinant of the actual integral trace Gram matrix. -/
theorem det_traceGram_freeIntegralLatticeBasisOnTowerIndex
    (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] :
    (LinearMap.BilinForm.toMatrix
        (P.freeIntegralLatticeBasisOnTowerIndex.extendOfIsLattice ℚ)
        P.traceQuadraticForm.associated).det =
      P.integralTraceGramMatrix.det := by
  rw [P.freeIntegralLatticeBasisOnTowerIndex_extend]
  have hmatrix :
      LinearMap.BilinForm.toMatrix
          (P.rationalTraceBasis.reindex
            (P.integralRestrictionBasis.indexEquiv
              P.freeIntegralTowerBasis))
          P.traceQuadraticForm.associated =
        Matrix.reindex
          (P.integralRestrictionBasis.indexEquiv P.freeIntegralTowerBasis)
          (P.integralRestrictionBasis.indexEquiv P.freeIntegralTowerBasis)
          P.integralTraceGramMatrix := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, Matrix.reindex_apply,
      integralTraceGramMatrix, P.traceQuadraticForm_associated]
  rw [hmatrix, Matrix.det_reindex_self]

/-- For a free integer-ring lattice, the determinant in the actual integral
trace basis equals the determinant in the canonical product basis. -/
theorem integralTraceGramDet_eq_freeTraceBlockMatrix
    (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] :
    P.integralTraceGramMatrix.det =
      (traceBlockMatrix (NumberField.integralBasis P.field.1)
        P.freeFieldGramMatrix).det := by
  have hfactor := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
    (b := P.freeRationalTowerBasis)
    (P.freeIntegralLatticeBasisOnTowerIndex.extendOfIsLattice ℚ)
    P.traceQuadraticForm.associated
  have hchange :
      P.freeRationalTowerBasis.toMatrix
          (P.freeIntegralLatticeBasisOnTowerIndex.extendOfIsLattice ℚ) =
        (algebraMap ℤ ℚ).mapMatrix
          (P.freeIntegralTowerBasis.toMatrix
            P.freeIntegralLatticeBasisOnTowerIndex) := by
    rw [← P.freeIntegralTowerBasis_extend]
    exact P.freeExtendedChangeMatrix_eq_map
  rw [← P.det_traceGram_freeIntegralLatticeBasisOnTowerIndex, ← hfactor,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    P.traceGram_freeRationalTowerBasis_eq]
  rw [hchange, ← RingHom.map_det]
  calc
    (algebraMap ℤ ℚ)
          (P.freeIntegralTowerBasis.toMatrix
            P.freeIntegralLatticeBasisOnTowerIndex).det *
        (traceBlockMatrix (NumberField.integralBasis P.field.1)
          P.freeFieldGramMatrix).det *
        (algebraMap ℤ ℚ)
          (P.freeIntegralTowerBasis.toMatrix
            P.freeIntegralLatticeBasisOnTowerIndex).det =
      ((P.freeIntegralTowerBasis.toMatrix
        P.freeIntegralLatticeBasisOnTowerIndex).det : ℚ) ^ (2 : ℕ) *
        (traceBlockMatrix (NumberField.integralBasis P.field.1)
          P.freeFieldGramMatrix).det := by
      change ((P.freeIntegralTowerBasis.toMatrix
          P.freeIntegralLatticeBasisOnTowerIndex).det : ℚ) *
        (traceBlockMatrix (NumberField.integralBasis P.field.1)
          P.freeFieldGramMatrix).det *
        ((P.freeIntegralTowerBasis.toMatrix
          P.freeIntegralLatticeBasisOnTowerIndex).det : ℚ) = _
      ring
    _ = (traceBlockMatrix (NumberField.integralBasis P.field.1)
          P.freeFieldGramMatrix).det := by
      rw [P.freeIntegralChangeDet_sq, one_mul]

/-- Absolute-value form of Lemma 3.1 for the actual integral trace basis of a
free integer-ring lattice. -/
theorem abs_integralTraceGramDet_eq_discr_pow_absNorm_free
    (P : GlobalLatticePresentation)
    [Module.Free (𝓞 P.field.1) P.L] (hclassic : P.IsClassicIntegral) :
    |P.integralTraceGramMatrix.det| =
      |(NumberField.discr P.field.1 : ℚ)| ^ P.rank *
        (Ideal.absNorm (P.classicVolumeIdealOf hclassic) : ℚ) := by
  rw [P.integralTraceGramDet_eq_freeTraceBlockMatrix,
    P.abs_det_freeTraceBlockMatrix hclassic]

end GlobalLatticePresentation

end

end TraceEuclidean
