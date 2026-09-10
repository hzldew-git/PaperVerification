import TraceEuclidean.TraceDeterminant
import TraceEuclidean.TraceCovering
import TraceEuclidean.VolumeIdeals
import Mathlib.NumberTheory.NumberField.Discriminant.Defs

/-!
The trace determinant identity on the canonical tower basis attached to a
number-field integral basis and a field basis of the quadratic space.  This
connects the generic block determinant calculation to the concrete global
lattice presentations.
-/

namespace TraceEuclidean

open Module
open scoped NumberField

noncomputable section

namespace GlobalLatticePresentation

/-- The field-valued Gram matrix in the selected lattice field basis. -/
def fieldGramMatrix (P : GlobalLatticePresentation) :
    Matrix (Fin P.rank) (Fin P.rank) P.field.1 :=
  LinearMap.BilinForm.toMatrix P.latticeFieldBasis P.Q.associated

/-- The rational tower basis obtained by multiplying the integral basis of the
number field with the selected field basis of the quadratic space. -/
def integralTowerBasis (P : GlobalLatticePresentation) :
    Basis ((Fin P.rank) ×
      Module.Free.ChooseBasisIndex ℤ (𝓞 P.field.1)) ℚ
      (Fin P.rank → P.field.1) :=
  (NumberField.integralBasis P.field.1).smulTower' P.latticeFieldBasis

@[simp]
theorem integralTowerBasis_apply (P : GlobalLatticePresentation)
    (i : Fin P.rank)
    (a : Module.Free.ChooseBasisIndex ℤ (𝓞 P.field.1)) :
    P.integralTowerBasis (i, a) =
      (NumberField.integralBasis P.field.1 a) • P.latticeFieldBasis i := by
  exact Basis.smulTower'_apply _ _ (i, a)

/-- The Gram matrix of the rational trace form in the tower basis is exactly
the generic trace block matrix. -/
theorem traceGram_integralTowerBasis_eq (P : GlobalLatticePresentation) :
    LinearMap.BilinForm.toMatrix P.integralTowerBasis
        P.traceQuadraticForm.associated =
      traceBlockMatrix (NumberField.integralBasis P.field.1)
        P.fieldGramMatrix := by
  ext ⟨i, a⟩ ⟨j, c⟩
  rw [LinearMap.BilinForm.toMatrix_apply,
    traceBlockMatrix, P.integralTowerBasis_apply,
    P.integralTowerBasis_apply, P.traceQuadraticForm_associated]
  rw [map_smul, LinearMap.map_smul₂]
  simp [fieldGramMatrix, LinearMap.BilinForm.toMatrix_apply,
    smul_eq_mul, mul_assoc, mul_left_comm]

/-- Exact determinant of the trace form on the canonical tower basis. -/
theorem det_traceGram_integralTowerBasis (P : GlobalLatticePresentation) :
    (LinearMap.BilinForm.toMatrix P.integralTowerBasis
        P.traceQuadraticForm.associated).det =
      (NumberField.discr P.field.1 : ℚ) ^ P.rank *
        Algebra.norm ℚ P.fieldGramMatrix.det := by
  rw [P.traceGram_integralTowerBasis_eq,
    det_traceBlockMatrix, ← NumberField.coe_discr]
  simp

/-- The chosen integral lattice basis, reindexed by the tower-basis index. -/
def integralLatticeBasisOnTowerIndex (P : GlobalLatticePresentation) :
    Basis ((Fin P.rank) ×
      Module.Free.ChooseBasisIndex ℤ (𝓞 P.field.1)) ℚ
      (Fin P.rank → P.field.1) :=
  P.rationalTraceBasis.reindex
    (P.rationalTraceBasis.indexEquiv P.integralTowerBasis)

/-- Coordinate matrix of the actual integral lattice basis in the canonical
number-field tower basis. -/
def integralLatticeChangeMatrix (P : GlobalLatticePresentation) :
    Matrix ((Fin P.rank) ×
      Module.Free.ChooseBasisIndex ℤ (𝓞 P.field.1))
      ((Fin P.rank) ×
        Module.Free.ChooseBasisIndex ℤ (𝓞 P.field.1)) ℚ :=
  P.integralTowerBasis.toMatrix P.integralLatticeBasisOnTowerIndex

/-- Reindexing the Gram matrix of the chosen integral lattice basis gives the
Gram matrix in `integralLatticeBasisOnTowerIndex`. -/
theorem traceGram_integralLatticeBasisOnTowerIndex_eq
    (P : GlobalLatticePresentation) :
    LinearMap.BilinForm.toMatrix P.integralLatticeBasisOnTowerIndex
        P.traceQuadraticForm.associated =
      Matrix.reindex
        (P.rationalTraceBasis.indexEquiv P.integralTowerBasis)
        (P.rationalTraceBasis.indexEquiv P.integralTowerBasis)
        P.integralTraceGramMatrix := by
  ext i j
  simp [LinearMap.BilinForm.toMatrix_apply,
    integralLatticeBasisOnTowerIndex, Matrix.reindex_apply,
    integralTraceGramMatrix, P.traceQuadraticForm_associated]

/-- The integral trace Gram determinant is unchanged by the common row and
column reindexing. -/
theorem det_traceGram_integralLatticeBasisOnTowerIndex
    (P : GlobalLatticePresentation) :
    (LinearMap.BilinForm.toMatrix P.integralLatticeBasisOnTowerIndex
        P.traceQuadraticForm.associated).det =
      P.integralTraceGramMatrix.det := by
  rw [P.traceGram_integralLatticeBasisOnTowerIndex_eq,
    Matrix.det_reindex_self]

/-- Exact change-of-basis factorization for the trace Gram matrix of the
actual lattice. -/
theorem traceGram_integralLatticeBasisOnTowerIndex_factorization
    (P : GlobalLatticePresentation) :
    LinearMap.BilinForm.toMatrix P.integralLatticeBasisOnTowerIndex
        P.traceQuadraticForm.associated =
      P.integralLatticeChangeMatrix.transpose *
        LinearMap.BilinForm.toMatrix P.integralTowerBasis
          P.traceQuadraticForm.associated *
        P.integralLatticeChangeMatrix := by
  exact
    (LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
      (b := P.integralTowerBasis) P.integralLatticeBasisOnTowerIndex
      P.traceQuadraticForm.associated).symm

/-- Fully unconditional determinant formula for the actual rational trace
lattice basis.  The square of the displayed change determinant is precisely
the remaining lattice-index factor that a pseudobasis/Steinitz argument must
identify with the ideal norm in the manuscript's volume formula. -/
theorem integralTraceGramDet_eq_change_sq_mul_discr_pow_mul_norm
    (P : GlobalLatticePresentation) :
    P.integralTraceGramMatrix.det =
      P.integralLatticeChangeMatrix.det ^ (2 : ℕ) *
        ((NumberField.discr P.field.1 : ℚ) ^ P.rank *
          Algebra.norm ℚ P.fieldGramMatrix.det) := by
  rw [← P.det_traceGram_integralLatticeBasisOnTowerIndex,
    P.traceGram_integralLatticeBasisOnTowerIndex_factorization,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    P.det_traceGram_integralTowerBasis]
  ring

/-- Real covolume form of the exact trace determinant factorization. -/
theorem euclideanCovolume_sq_eq_change_sq_mul_discr_pow_mul_norm
    (P : GlobalLatticePresentation) :
    ZLattice.covolume P.euclideanIntegralLattice ^ (2 : ℕ) =
      (P.integralLatticeChangeMatrix.det : ℝ) ^ (2 : ℕ) *
        (((NumberField.discr P.field.1 : ℚ) : ℝ) ^ P.rank *
          ((Algebra.norm ℚ P.fieldGramMatrix.det : ℚ) : ℝ)) := by
  rw [P.euclideanCovolume_sq_eq_integralTraceGramDet,
    P.integralTraceGramDet_eq_change_sq_mul_discr_pow_mul_norm]
  norm_cast

end GlobalLatticePresentation

end

end TraceEuclidean
