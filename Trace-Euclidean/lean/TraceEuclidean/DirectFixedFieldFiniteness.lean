import TraceEuclidean.ShortFieldBasis
import TraceEuclidean.FiniteReductionCodes
import TraceEuclidean.TraceVolumeBridge
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Direct fixed-field finiteness

This file replaces the external fixed-volume reduction certificate by a
finite code built from a short field basis.  The code stores the full
field-valued Gram matrix and the determinant-normalized coordinate module.
Keeping the field-valued matrix is essential: a trace Gram matrix alone does
not determine the original quadratic space over the number field.
-/

namespace TraceEuclidean

open Module
open scoped NumberField

noncomputable section

/-- A presentation whose coded number field and rank are fixed at the type
level.  This is only a transport-friendly wrapper around
`GlobalLatticePresentation`. -/
structure FixedFieldLatticePresentation (K : CodedNumberField) (n : ℕ) where
  totallyReal : NumberField.IsTotallyReal K.1
  rankPositive : 0 < n
  Q : QuadraticForm K.1 (Fin n → K.1)
  L : Submodule (𝓞 K.1) (Fin n → K.1)
  full : L.IsLattice K.1
  nondegenerate : Q.Nondegenerate
  positiveDefinite :
    ∀ x : Fin n → K.1, x ≠ 0 → ∀ σ : K.1 →+* ℝ, 0 < σ (Q x)
  integral : ∀ x : L, _root_.IsIntegral ℤ (Q x.1)

namespace FixedFieldLatticePresentation

variable {K : CodedNumberField} {n : ℕ}

/-- Forget that the field and rank have been fixed in the type. -/
abbrev toGlobal (P : FixedFieldLatticePresentation K n) :
    GlobalLatticePresentation where
  field := K
  totallyReal := P.totallyReal
  rank := n
  rankPositive := P.rankPositive
  Q := P.Q
  L := P.L
  full := P.full
  nondegenerate := P.nondegenerate
  positiveDefinite := P.positiveDefinite
  integral := P.integral

@[simp] theorem toGlobal_field (P : FixedFieldLatticePresentation K n) :
    P.toGlobal.field = K := rfl

@[simp] theorem toGlobal_rank (P : FixedFieldLatticePresentation K n) :
    P.toGlobal.rank = n := rfl

/-- Transport a global presentation to an exactly fixed field and rank. -/
def ofGlobal (P : GlobalLatticePresentation) (hK : P.field = K)
    (hn : P.rank = n) : FixedFieldLatticePresentation K n := by
  subst K
  subst n
  exact
    { totallyReal := P.totallyReal
      rankPositive := P.rankPositive
      Q := P.Q
      L := P.L
      full := P.full
      nondegenerate := P.nondegenerate
      positiveDefinite := P.positiveDefinite
      integral := P.integral }

@[simp] theorem toGlobal_ofGlobal (P : GlobalLatticePresentation)
    (hK : P.field = K) (hn : P.rank = n) :
    (ofGlobal P hK hn).toGlobal = P := by
  subst K
  subst n
  rfl

/-- Classic integrality for an exact presentation. -/
def IsClassicIntegral (P : FixedFieldLatticePresentation K n) : Prop :=
  P.toGlobal.IsClassicIntegral

/-- Strict trace-Euclideanity for an exact presentation. -/
def IsTraceEuclidean (P : FixedFieldLatticePresentation K n) (t : ℝ) : Prop :=
  P.toGlobal.IsTraceEuclidean t

/-- The integral pairing vector against a selected classic basis tuple. -/
def classicPairingCoordinates (P : FixedFieldLatticePresentation K n)
    (hclassic : P.IsClassicIntegral) (w : Fin n → P.L) :
    P.L →ₗ[𝓞 K.1] (Fin n → 𝓞 K.1) :=
  LinearMap.pi fun i ↦ P.toGlobal.classicBilinearForm hclassic (w i)

@[simp] theorem classicPairingCoordinates_apply
    (P : FixedFieldLatticePresentation K n)
    (hclassic : P.IsClassicIntegral) (w : Fin n → P.L) (x : P.L)
    (i : Fin n) :
    P.classicPairingCoordinates hclassic w x i =
      P.toGlobal.classicBilinearInteger hclassic (w i) x :=
  rfl

/-- The integral pairing vector for the bilinear form associated with `2Q`. -/
def scaledPairingCoordinates (P : FixedFieldLatticePresentation K n)
    (w : Fin n → P.L) : P.L →ₗ[𝓞 K.1] (Fin n → 𝓞 K.1) :=
  LinearMap.pi fun i ↦
    { toFun := fun x ↦ P.toGlobal.scaledBilinearInteger (w i) x
      map_add' := by
        intro x y
        apply NumberField.RingOfIntegers.coe_injective
        simp only [P.toGlobal.scaledBilinearInteger_eq_two_associated,
          Submodule.coe_add, map_add]
        ring
      map_smul' := by
        intro a x
        apply NumberField.RingOfIntegers.coe_injective
        change
          (P.toGlobal.scaledBilinearInteger (w i) (a • x) : K.1) =
            (a : K.1) *
              (P.toGlobal.scaledBilinearInteger (w i) x : K.1)
        rw [P.toGlobal.scaledBilinearInteger_eq_two_associated,
          P.toGlobal.scaledBilinearInteger_eq_two_associated]
        rw [Submodule.coe_smul_of_tower,
          ← IsScalarTower.algebraMap_smul K.1 a x.1, map_smul]
        simp
        ring }

@[simp] theorem scaledPairingCoordinates_apply
    (P : FixedFieldLatticePresentation K n) (w : Fin n → P.L) (x : P.L)
    (i : Fin n) :
    P.scaledPairingCoordinates w x i =
      P.toGlobal.scaledBilinearInteger (w i) x :=
  rfl

/-- The classic integral Gram matrix of a selected lattice field basis. -/
def classicGramMatrix (P : FixedFieldLatticePresentation K n)
    (hclassic : P.IsClassicIntegral) (w : Fin n → P.L) :
    Matrix (Fin n) (Fin n) (𝓞 K.1) :=
  fun i j ↦ P.classicPairingCoordinates hclassic w (w j) i

/-- The integral Gram matrix of `2Q` on a selected lattice field basis. -/
def scaledGramMatrix (P : FixedFieldLatticePresentation K n)
    (w : Fin n → P.L) : Matrix (Fin n) (Fin n) (𝓞 K.1) :=
  fun i j ↦ P.scaledPairingCoordinates w (w j) i

/-- Coercing the classic integral Gram matrix gives the field-valued matrix
of the associated bilinear form. -/
theorem map_classicGramMatrix
    (P : FixedFieldLatticePresentation K n)
    (hclassic : P.IsClassicIntegral) (w : Fin n → P.L)
    (b : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (hb : ∀ i, b i = (w i).1) :
    (algebraMap (𝓞 K.1) K.1).mapMatrix
        (P.classicGramMatrix hclassic w) =
      LinearMap.BilinForm.toMatrix b P.Q.associated := by
  apply Matrix.ext
  intro i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
    LinearMap.BilinForm.toMatrix_apply]
  change QuadraticMap.associated P.Q (w i).1 (w j).1 =
    QuadraticMap.associated P.Q (b i) (b j)
  rw [hb i, hb j]

/-- Coercing the integral scale-two Gram matrix gives the matrix of twice
the associated bilinear form. -/
theorem map_scaledGramMatrix
    (P : FixedFieldLatticePresentation K n) (w : Fin n → P.L)
    (b : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (hb : ∀ i, b i = (w i).1) :
    (algebraMap (𝓞 K.1) K.1).mapMatrix (P.scaledGramMatrix w) =
      (2 : K.1) • LinearMap.BilinForm.toMatrix b P.Q.associated := by
  apply Matrix.ext
  intro i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply,
    LinearMap.BilinForm.toMatrix_apply, smul_eq_mul]
  simp only [scaledGramMatrix, scaledPairingCoordinates_apply,
    P.toGlobal.scaledBilinearInteger_eq_two_associated]
  rw [hb i, hb j]

/-- Expanding the second argument in a field basis is matrix-vector
multiplication by the associated Gram matrix. -/
theorem associated_eq_gram_mulVec
    (P : FixedFieldLatticePresentation K n)
    (b : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (i : Fin n) (x : Fin n → K.1) :
    QuadraticMap.associated P.Q (b i) x =
      (LinearMap.BilinForm.toMatrix b P.Q.associated).mulVec
        (b.equivFun x) i := by
  have hx := congrArg (fun y : Fin n → K.1 ↦
      QuadraticMap.associated P.Q (b i) y) (b.sum_repr x)
  simp only [map_sum, map_smul] at hx
  rw [Matrix.mulVec, dotProduct]
  simpa [Basis.equivFun_apply, mul_comm] using hx.symm

/-- Pairing coordinates are matrix multiplication by the classic Gram
matrix in the selected field basis. -/
theorem map_classicPairingCoordinates
    (P : FixedFieldLatticePresentation K n)
    (hclassic : P.IsClassicIntegral) (w : Fin n → P.L)
    (b : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (hb : ∀ i, b i = (w i).1) (x : P.L) :
    (fun i ↦ (P.classicPairingCoordinates hclassic w x i : K.1)) =
      ((algebraMap (𝓞 K.1) K.1).mapMatrix
        (P.classicGramMatrix hclassic w)).mulVec (b.equivFun x.1) := by
  rw [P.map_classicGramMatrix hclassic w b hb]
  funext i
  change QuadraticMap.associated P.Q (w i).1 x.1 = _
  rw [← hb i]
  exact P.associated_eq_gram_mulVec b i x.1

/-- Pairing coordinates are matrix multiplication by the scale-two Gram
matrix in the selected field basis. -/
theorem map_scaledPairingCoordinates
    (P : FixedFieldLatticePresentation K n) (w : Fin n → P.L)
    (b : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (hb : ∀ i, b i = (w i).1) (x : P.L) :
    (fun i ↦ (P.scaledPairingCoordinates w x i : K.1)) =
      ((algebraMap (𝓞 K.1) K.1).mapMatrix
        (P.scaledGramMatrix w)).mulVec (b.equivFun x.1) := by
  rw [P.map_scaledGramMatrix w b hb]
  funext i
  rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  rw [scaledPairingCoordinates_apply,
    P.toGlobal.scaledBilinearInteger_eq_two_associated]
  change (2 : K.1) * QuadraticMap.associated P.Q (w i).1 x.1 =
    2 * (LinearMap.BilinForm.toMatrix b P.Q.associated).mulVec
      (b.equivFun x.1) i
  rw [← hb i, P.associated_eq_gram_mulVec b i x.1]

/-- A classic Gram matrix on a field basis is nonsingular. -/
theorem classicGramMatrix_det_ne_zero
    (P : FixedFieldLatticePresentation K n)
    (hclassic : P.IsClassicIntegral) (w : Fin n → P.L)
    (b : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (hb : ∀ i, b i = (w i).1) :
    (P.classicGramMatrix hclassic w).det ≠ 0 := by
  intro hzero
  have hdet :
      (LinearMap.BilinForm.toMatrix b P.Q.associated).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
      (QuadraticMap.nondegenerate_associated_iff.mpr P.nondegenerate)
  apply hdet
  have hmatrix := P.map_classicGramMatrix hclassic w b hb
  rw [← hmatrix, ← (algebraMap (𝓞 K.1) K.1).map_det, hzero, map_zero]

/-- A scale-two Gram matrix on a field basis is nonsingular. -/
theorem scaledGramMatrix_det_ne_zero
    (P : FixedFieldLatticePresentation K n) (w : Fin n → P.L)
    (b : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (hb : ∀ i, b i = (w i).1) :
    (P.scaledGramMatrix w).det ≠ 0 := by
  intro hzero
  have hdet :
      ((2 : K.1) • LinearMap.BilinForm.toMatrix b P.Q.associated).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
        (QuadraticMap.nondegenerate_associated_iff.mpr P.nondegenerate))
  apply hdet
  have hmatrix :
      (algebraMap (𝓞 K.1) K.1).mapMatrix (P.scaledGramMatrix w) =
        (2 : K.1) • LinearMap.BilinForm.toMatrix b P.Q.associated := by
    exact P.map_scaledGramMatrix w b hb
  rw [← hmatrix, ← (algebraMap (𝓞 K.1) K.1).map_det, hzero, map_zero]

/-- Determinant-normalized classic coordinates. -/
def classicNormalizedCoordinates
    (P : FixedFieldLatticePresentation K n)
    (hclassic : P.IsClassicIntegral) (w : Fin n → P.L) :
    P.L →ₗ[𝓞 K.1] (Fin n → 𝓞 K.1) :=
  (P.classicGramMatrix hclassic w).adjugate.mulVecLin.comp
    (P.classicPairingCoordinates hclassic w)

/-- Determinant-normalized scale-two coordinates. -/
def scaledNormalizedCoordinates
    (P : FixedFieldLatticePresentation K n) (w : Fin n → P.L) :
    P.L →ₗ[𝓞 K.1] (Fin n → 𝓞 K.1) :=
  (P.scaledGramMatrix w).adjugate.mulVecLin.comp
    (P.scaledPairingCoordinates w)

/-- The normalized classic coordinate map is multiplication of ordinary
basis coordinates by the Gram determinant. -/
theorem map_classicNormalizedCoordinates
    (P : FixedFieldLatticePresentation K n)
    (hclassic : P.IsClassicIntegral) (w : Fin n → P.L)
    (b : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (hb : ∀ i, b i = (w i).1) (x : P.L) :
    (fun i ↦ (P.classicNormalizedCoordinates hclassic w x i : K.1)) =
      fun i ↦ ((P.classicGramMatrix hclassic w).det : K.1) *
        b.equivFun x.1 i := by
  let f := algebraMap (𝓞 K.1) K.1
  let G := P.classicGramMatrix hclassic w
  funext i
  change f (G.adjugate.mulVec
      (P.classicPairingCoordinates hclassic w x) i) =
    f G.det * b.equivFun x.1 i
  rw [RingHom.map_mulVec]
  change (f.mapMatrix G.adjugate).mulVec
      (fun j ↦ f (P.classicPairingCoordinates hclassic w x j)) i = _
  rw [f.map_adjugate, P.map_classicPairingCoordinates hclassic w b hb]
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
  rw [← f.map_det]

/-- The normalized scale-two coordinate map is multiplication of ordinary
basis coordinates by the scale-two Gram determinant. -/
theorem map_scaledNormalizedCoordinates
    (P : FixedFieldLatticePresentation K n) (w : Fin n → P.L)
    (b : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (hb : ∀ i, b i = (w i).1) (x : P.L) :
    (fun i ↦ (P.scaledNormalizedCoordinates w x i : K.1)) =
      fun i ↦ ((P.scaledGramMatrix w).det : K.1) *
        b.equivFun x.1 i := by
  let f := algebraMap (𝓞 K.1) K.1
  let G := P.scaledGramMatrix w
  funext i
  change f (G.adjugate.mulVec (P.scaledPairingCoordinates w x) i) =
    f G.det * b.equivFun x.1 i
  rw [RingHom.map_mulVec]
  change (f.mapMatrix G.adjugate).mulVec
      (fun j ↦ f (P.scaledPairingCoordinates w x j)) i = _
  rw [f.map_adjugate, P.map_scaledPairingCoordinates w b hb]
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
  rw [← f.map_det]

/-- The lattice vector with prescribed integral coordinates in the selected
field basis. -/
def integralBasisCombination
    (P : FixedFieldLatticePresentation K n) (w : Fin n → P.L)
    (z : Fin n → 𝓞 K.1) : P.L :=
  ∑ i, z i • w i

/-- The preceding combination has exactly the prescribed coordinates. -/
theorem equivFun_integralBasisCombination
    (P : FixedFieldLatticePresentation K n) (w : Fin n → P.L)
    (b : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (hb : ∀ i, b i = (w i).1) (z : Fin n → 𝓞 K.1) :
    b.equivFun (P.integralBasisCombination w z).1 =
      fun i ↦ (z i : K.1) := by
  apply b.equivFun.symm.injective
  rw [b.equivFun.symm_apply_apply, Basis.equivFun_symm_apply]
  change (↑(∑ i, z i • w i) : Fin n → K.1) =
    ∑ i, (z i : K.1) • b i
  rw [Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Submodule.coe_smul_of_tower, hb i]
  exact (IsScalarTower.algebraMap_smul K.1 (z i) (w i).1).symm

/-- The normalized classic coordinate map is injective. -/
theorem classicNormalizedCoordinates_injective
    (P : FixedFieldLatticePresentation K n)
    (hclassic : P.IsClassicIntegral) (w : Fin n → P.L)
    (b : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (hb : ∀ i, b i = (w i).1) :
    Function.Injective (P.classicNormalizedCoordinates hclassic w) := by
  intro x y hxy
  apply Subtype.ext
  apply b.equivFun.injective
  funext i
  have hcoord := congrArg (fun z : Fin n → 𝓞 K.1 ↦ (z i : K.1)) hxy
  rw [congrFun (P.map_classicNormalizedCoordinates hclassic w b hb x) i,
    congrFun (P.map_classicNormalizedCoordinates hclassic w b hb y) i] at hcoord
  have hdetK : ((P.classicGramMatrix hclassic w).det : K.1) ≠ 0 := by
    intro h
    apply P.classicGramMatrix_det_ne_zero hclassic w b hb
    apply NumberField.RingOfIntegers.coe_injective
    simpa using h
  exact mul_left_cancel₀ hdetK hcoord

/-- The normalized scale-two coordinate map is injective. -/
theorem scaledNormalizedCoordinates_injective
    (P : FixedFieldLatticePresentation K n) (w : Fin n → P.L)
    (b : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (hb : ∀ i, b i = (w i).1) :
    Function.Injective (P.scaledNormalizedCoordinates w) := by
  intro x y hxy
  apply Subtype.ext
  apply b.equivFun.injective
  funext i
  have hcoord := congrArg (fun z : Fin n → 𝓞 K.1 ↦ (z i : K.1)) hxy
  rw [congrFun (P.map_scaledNormalizedCoordinates w b hb x) i,
    congrFun (P.map_scaledNormalizedCoordinates w b hb y) i] at hcoord
  have hdetK : ((P.scaledGramMatrix w).det : K.1) ≠ 0 := by
    intro h
    apply P.scaledGramMatrix_det_ne_zero w b hb
    apply NumberField.RingOfIntegers.coe_injective
    simpa using h
  exact mul_left_cancel₀ hdetK hcoord

/-- The determinant multiple of the standard coordinate module lies in the
range of the normalized classic coordinate map. -/
theorem principalMultiple_le_classicNormalizedRange
    (P : FixedFieldLatticePresentation K n)
    (hclassic : P.IsClassicIntegral) (w : Fin n → P.L)
    (b : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (hb : ∀ i, b i = (w i).1) :
    principalMultipleCoordinateSubmodule K.1 n
        (P.classicGramMatrix hclassic w).det ≤
      LinearMap.range (P.classicNormalizedCoordinates hclassic w) := by
  rw [principalMultipleCoordinateSubmodule]
  rw [Submodule.ideal_span_singleton_smul]
  intro y hy
  rw [Submodule.mem_smul_pointwise_iff_exists] at hy
  rcases hy with ⟨z, _hz, rfl⟩
  let x : P.L := P.integralBasisCombination w z
  refine ⟨x, ?_⟩
  apply funext
  intro i
  apply NumberField.RingOfIntegers.coe_injective
  calc
    (↑((P.classicNormalizedCoordinates hclassic w) x i) : K.1) =
        ((P.classicGramMatrix hclassic w).det : K.1) *
          b.equivFun x.1 i :=
      congrFun (P.map_classicNormalizedCoordinates hclassic w b hb x) i
    _ = ((P.classicGramMatrix hclassic w).det : K.1) * (z i : K.1) := by
      rw [congrFun (P.equivFun_integralBasisCombination w b hb z) i]
    _ = (↑(((P.classicGramMatrix hclassic w).det • z) i) : K.1) := by
      simp

/-- The determinant multiple of the standard coordinate module lies in the
range of the normalized scale-two coordinate map. -/
theorem principalMultiple_le_scaledNormalizedRange
    (P : FixedFieldLatticePresentation K n) (w : Fin n → P.L)
    (b : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (hb : ∀ i, b i = (w i).1) :
    principalMultipleCoordinateSubmodule K.1 n
        (P.scaledGramMatrix w).det ≤
      LinearMap.range (P.scaledNormalizedCoordinates w) := by
  rw [principalMultipleCoordinateSubmodule]
  rw [Submodule.ideal_span_singleton_smul]
  intro y hy
  rw [Submodule.mem_smul_pointwise_iff_exists] at hy
  rcases hy with ⟨z, _hz, rfl⟩
  let x : P.L := P.integralBasisCombination w z
  refine ⟨x, ?_⟩
  apply funext
  intro i
  apply NumberField.RingOfIntegers.coe_injective
  calc
    (↑((P.scaledNormalizedCoordinates w) x i) : K.1) =
        ((P.scaledGramMatrix w).det : K.1) * b.equivFun x.1 i :=
      congrFun (P.map_scaledNormalizedCoordinates w b hb x) i
    _ = ((P.scaledGramMatrix w).det : K.1) * (z i : K.1) := by
      rw [congrFun (P.equivFun_integralBasisCombination w b hb z) i]
    _ = (↑(((P.scaledGramMatrix w).det • z) i) : K.1) := by
      simp

/-- The direct reduction code in the classic branch. -/
def classicReductionCode
    (P : FixedFieldLatticePresentation K n)
    (hclassic : P.IsClassicIntegral) (w : Fin n → P.L) :
    IntegralReductionCode K.1 n :=
  (P.classicGramMatrix hclassic w,
    LinearMap.range (P.classicNormalizedCoordinates hclassic w))

/-- The direct reduction code in the scale-two integral branch. -/
def scaledReductionCode
    (P : FixedFieldLatticePresentation K n) (w : Fin n → P.L) :
    IntegralReductionCode K.1 n :=
  (P.scaledGramMatrix w,
    LinearMap.range (P.scaledNormalizedCoordinates w))

/-- Uniform entry bound furnished by the short-basis argument for fixed
field and rank. -/
def fixedFieldGramBound (K : CodedNumberField) (n : ℕ) (u : ℝ) : ℝ :=
  (((n * Module.finrank ℚ K.1 : ℕ) + 1 : ℝ) * Real.sqrt u + 1) ^ 2

/-- The scale-two integral Gram matrix has twice the classic entry bound. -/
def fixedFieldScaledGramBound
    (K : CodedNumberField) (n : ℕ) (u : ℝ) : ℝ :=
  2 * fixedFieldGramBound K n u

/-- A classic short-basis code satisfies all three finite-code constraints. -/
theorem classicReductionCode_isBounded
    (P : FixedFieldLatticePresentation K n)
    (hclassic : P.IsClassicIntegral) (w : Fin n → P.L)
    (b : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (hb : ∀ i, b i = (w i).1)
    (hcomplex : ∀ (τ : K.1 →ₐ[ℚ] ℂ) i j,
      ‖τ (QuadraticMap.associated P.Q (w i).1 (w j).1)‖ <
        fixedFieldGramBound K n u) :
    IntegralReductionCode.IsBounded (fixedFieldGramBound K n u)
      (P.classicReductionCode hclassic w) := by
  refine ⟨?_, P.classicGramMatrix_det_ne_zero hclassic w b hb,
    P.principalMultiple_le_classicNormalizedRange hclassic w b hb⟩
  intro i j φ
  change ‖φ ((P.classicGramMatrix hclassic w i j : 𝓞 K.1) : K.1)‖ ≤
    fixedFieldGramBound K n u
  rw [show (P.classicGramMatrix hclassic w i j : K.1) =
      QuadraticMap.associated P.Q (w i).1 (w j).1 by
    exact P.toGlobal.coe_classicBilinearInteger hclassic (w i) (w j)]
  exact le_of_lt (hcomplex φ.toRatAlgHom i j)

/-- A scale-two short-basis code satisfies all three finite-code constraints. -/
theorem scaledReductionCode_isBounded
    (P : FixedFieldLatticePresentation K n) (w : Fin n → P.L)
    (b : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (hb : ∀ i, b i = (w i).1)
    (hcomplex : ∀ (τ : K.1 →ₐ[ℚ] ℂ) i j,
      ‖τ (P.toGlobal.scaledBilinearInteger (w i) (w j) : K.1)‖ <
        fixedFieldScaledGramBound K n u) :
    IntegralReductionCode.IsBounded (fixedFieldScaledGramBound K n u)
      (P.scaledReductionCode w) := by
  refine ⟨?_, P.scaledGramMatrix_det_ne_zero w b hb,
    P.principalMultiple_le_scaledNormalizedRange w b hb⟩
  intro i j φ
  change ‖φ ((P.scaledGramMatrix w i j : 𝓞 K.1) : K.1)‖ ≤
    fixedFieldScaledGramBound K n u
  exact le_of_lt (hcomplex φ.toRatAlgHom i j)

/-- Every classic integral trace-Euclidean presentation over a fixed field
and of fixed rank admits a bounded complete reduction code candidate. -/
theorem exists_bounded_classicReductionCode_of_traceEuclidean
    (P : FixedFieldLatticePresentation K n) {t u : ℝ}
    (ht : 0 < t) (htu : t < u) (hE : P.IsTraceEuclidean t)
    (hclassic : P.IsClassicIntegral) :
    ∃ (w : Fin n → P.L)
      (b : Module.Basis (Fin n) K.1 (Fin n → K.1)),
        (∀ i, b i = (w i).1) ∧
        IntegralReductionCode.IsBounded (fixedFieldGramBound K n u)
          (P.classicReductionCode hclassic w) := by
  obtain ⟨w, b, hb, _hw, _hentry, _hreal, hcomplex⟩ :=
    P.toGlobal.exists_short_classicIntegral_fieldBasis ht htu hE hclassic
  refine ⟨w, b, hb, ?_⟩
  apply P.classicReductionCode_isBounded hclassic w b hb
  simpa [fixedFieldGramBound, GlobalLatticePresentation.degree] using hcomplex

/-- Every integral trace-Euclidean presentation over a fixed field and of
fixed rank admits a bounded scale-two reduction code candidate. -/
theorem exists_bounded_scaledReductionCode_of_traceEuclidean
    (P : FixedFieldLatticePresentation K n) {t u : ℝ}
    (ht : 0 < t) (htu : t < u) (hE : P.IsTraceEuclidean t) :
    ∃ (w : Fin n → P.L)
      (b : Module.Basis (Fin n) K.1 (Fin n → K.1)),
        (∀ i, b i = (w i).1) ∧
        IntegralReductionCode.IsBounded (fixedFieldScaledGramBound K n u)
          (P.scaledReductionCode w) := by
  obtain ⟨w, b, hb, _hw, _hentry, _hreal, hcomplex⟩ :=
    P.toGlobal.exists_short_integralScaled_fieldBasis ht htu hE
  refine ⟨w, b, hb, ?_⟩
  apply P.scaledReductionCode_isBounded w b hb
  simpa [fixedFieldScaledGramBound, fixedFieldGramBound,
    GlobalLatticePresentation.degree] using hcomplex

/-- The field-linear change of coordinates carrying one selected basis to
another selected basis. -/
def basisLinearEquiv
    (b b' : Module.Basis (Fin n) K.1 (Fin n → K.1)) :
    (Fin n → K.1) ≃ₗ[K.1] (Fin n → K.1) :=
  b.equivFun.trans b'.equivFun.symm

@[simp]
theorem equivFun_basisLinearEquiv
    (b b' : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (x : Fin n → K.1) :
    b'.equivFun (basisLinearEquiv b b' x) = b.equivFun x := by
  change b'.equivFun (b'.equivFun.symm (b.equivFun x)) = b.equivFun x
  exact b'.equivFun.apply_symm_apply (b.equivFun x)

/-- Equality of determinant-normalized coordinate ranges forces the basis
change to carry one integral lattice onto the other. -/
theorem basisLinearEquiv_mapsLattice_of_normalizedRange_eq
    (P P' : FixedFieldLatticePresentation K n)
    (b b' : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (f : P.L →ₗ[𝓞 K.1] (Fin n → 𝓞 K.1))
    (f' : P'.L →ₗ[𝓞 K.1] (Fin n → 𝓞 K.1))
    (a : 𝓞 K.1) (ha : a ≠ 0)
    (hf : ∀ x, (fun i ↦ (f x i : K.1)) =
      fun i ↦ (a : K.1) * b.equivFun x.1 i)
    (hf' : ∀ x, (fun i ↦ (f' x i : K.1)) =
      fun i ↦ (a : K.1) * b'.equivFun x.1 i)
    (hrange : LinearMap.range f = LinearMap.range f') :
    ∀ x, x ∈ P.L ↔ basisLinearEquiv b b' x ∈ P'.L := by
  have haK : (a : K.1) ≠ 0 := by
    intro h
    apply ha
    apply NumberField.RingOfIntegers.coe_injective
    simpa using h
  intro x
  constructor
  · intro hx
    let lx : P.L := ⟨x, hx⟩
    have hmem : f lx ∈ LinearMap.range f' := by
      rw [← hrange]
      exact ⟨lx, rfl⟩
    rcases hmem with ⟨ly, hly⟩
    have hcoord : b'.equivFun ly.1 = b.equivFun x := by
      funext i
      have hi := congrArg (fun z : Fin n → 𝓞 K.1 ↦ (z i : K.1)) hly
      rw [congrFun (hf' ly) i, congrFun (hf lx) i] at hi
      exact mul_left_cancel₀ haK hi
    have heq : basisLinearEquiv b b' x = ly.1 := by
      apply b'.equivFun.injective
      rw [equivFun_basisLinearEquiv, hcoord]
    rw [heq]
    exact ly.2
  · intro hx
    let lx : P'.L := ⟨basisLinearEquiv b b' x, hx⟩
    have hmem : f' lx ∈ LinearMap.range f := by
      rw [hrange]
      exact ⟨lx, rfl⟩
    rcases hmem with ⟨ly, hly⟩
    have hcoord : b.equivFun ly.1 = b.equivFun x := by
      funext i
      have hi := congrArg (fun z : Fin n → 𝓞 K.1 ↦ (z i : K.1)) hly
      rw [congrFun (hf ly) i, congrFun (hf' lx) i,
        equivFun_basisLinearEquiv] at hi
      exact mul_left_cancel₀ haK hi
    have heq : ly.1 = x := b.equivFun.injective hcoord
    rw [← heq]
    exact ly.2

/-- Equality of associated Gram matrices makes the selected basis change an
isometry of the quadratic spaces. -/
theorem basisLinearEquiv_mapQuadratic_of_matrix_eq
    (P P' : FixedFieldLatticePresentation K n)
    (b b' : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (hmatrix : LinearMap.BilinForm.toMatrix b P.Q.associated =
      LinearMap.BilinForm.toMatrix b' P'.Q.associated) :
    ∀ x, P'.Q (basisLinearEquiv b b' x) = P.Q x := by
  intro x
  rw [← QuadraticMap.associated_eq_self_apply K.1 P'.Q,
    ← QuadraticMap.associated_eq_self_apply K.1 P.Q]
  rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b',
    LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b]
  change b'.equivFun (basisLinearEquiv b b' x) ⬝ᵥ
      (LinearMap.BilinForm.toMatrix b' P'.Q.associated).mulVec
        (b'.equivFun (basisLinearEquiv b b' x)) =
    b.equivFun x ⬝ᵥ
      (LinearMap.BilinForm.toMatrix b P.Q.associated).mulVec (b.equivFun x)
  rw [equivFun_basisLinearEquiv, hmatrix]

/-- Package a same-field basis isometry and its exact lattice image as the
paper's global equivalence data. -/
def equivalenceDataOfBasisLinearEquiv
    (P P' : FixedFieldLatticePresentation K n)
    (b b' : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (hmaps : ∀ x, x ∈ P.L ↔ basisLinearEquiv b b' x ∈ P'.L)
    (hQ : ∀ x, P'.Q (basisLinearEquiv b b' x) = P.Q x) :
    GlobalLatticePresentation.EquivalenceData P.toGlobal P'.toGlobal where
  fieldEquiv := AlgEquiv.refl
  spaceEquiv := (basisLinearEquiv b b').toAddEquiv
  map_smul := by simp
  mapsLattice := hmaps
  mapQuadratic := by simpa using hQ
  rank_eq := rfl
  degree_eq := rfl

/-- In the classic branch, equality of the full Gram matrix and normalized
coordinate module is a complete invariant of the lattice presentation. -/
theorem isEquivalent_of_classicReductionCode_eq
    (P P' : FixedFieldLatticePresentation K n)
    (hclassic : P.IsClassicIntegral) (hclassic' : P'.IsClassicIntegral)
    (w : Fin n → P.L) (w' : Fin n → P'.L)
    (b b' : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (hb : ∀ i, b i = (w i).1) (hb' : ∀ i, b' i = (w' i).1)
    (hcode : P.classicReductionCode hclassic w =
      P'.classicReductionCode hclassic' w') :
    P.toGlobal.IsEquivalent P'.toGlobal := by
  have hG : P.classicGramMatrix hclassic w =
      P'.classicGramMatrix hclassic' w' := by
    simpa [classicReductionCode] using congrArg Prod.fst hcode
  have hrange :
      LinearMap.range (P.classicNormalizedCoordinates hclassic w) =
        LinearMap.range (P'.classicNormalizedCoordinates hclassic' w') := by
    simpa [classicReductionCode] using congrArg Prod.snd hcode
  have hmaps : ∀ x, x ∈ P.L ↔ basisLinearEquiv b b' x ∈ P'.L := by
    apply basisLinearEquiv_mapsLattice_of_normalizedRange_eq P P' b b'
      (P.classicNormalizedCoordinates hclassic w)
      (P'.classicNormalizedCoordinates hclassic' w')
      (P.classicGramMatrix hclassic w).det
      (P.classicGramMatrix_det_ne_zero hclassic w b hb)
    · exact P.map_classicNormalizedCoordinates hclassic w b hb
    · intro x
      simpa [hG] using
        P'.map_classicNormalizedCoordinates hclassic' w' b' hb' x
    · exact hrange
  have hmatrix : LinearMap.BilinForm.toMatrix b P.Q.associated =
      LinearMap.BilinForm.toMatrix b' P'.Q.associated := by
    calc
      LinearMap.BilinForm.toMatrix b P.Q.associated =
          (algebraMap (𝓞 K.1) K.1).mapMatrix
            (P.classicGramMatrix hclassic w) :=
        (P.map_classicGramMatrix hclassic w b hb).symm
      _ = (algebraMap (𝓞 K.1) K.1).mapMatrix
            (P'.classicGramMatrix hclassic' w') := by rw [hG]
      _ = LinearMap.BilinForm.toMatrix b' P'.Q.associated :=
        P'.map_classicGramMatrix hclassic' w' b' hb'
  have hQ := P.basisLinearEquiv_mapQuadratic_of_matrix_eq P' b b' hmatrix
  exact ⟨equivalenceDataOfBasisLinearEquiv P P' b b' hmaps hQ⟩

/-- In the general integral branch, the scale-two Gram matrix and normalized
coordinate module are likewise a complete invariant. -/
theorem isEquivalent_of_scaledReductionCode_eq
    (P P' : FixedFieldLatticePresentation K n)
    (w : Fin n → P.L) (w' : Fin n → P'.L)
    (b b' : Module.Basis (Fin n) K.1 (Fin n → K.1))
    (hb : ∀ i, b i = (w i).1) (hb' : ∀ i, b' i = (w' i).1)
    (hcode : P.scaledReductionCode w = P'.scaledReductionCode w') :
    P.toGlobal.IsEquivalent P'.toGlobal := by
  have hG : P.scaledGramMatrix w = P'.scaledGramMatrix w' := by
    simpa [scaledReductionCode] using congrArg Prod.fst hcode
  have hrange : LinearMap.range (P.scaledNormalizedCoordinates w) =
      LinearMap.range (P'.scaledNormalizedCoordinates w') := by
    simpa [scaledReductionCode] using congrArg Prod.snd hcode
  have hmaps : ∀ x, x ∈ P.L ↔ basisLinearEquiv b b' x ∈ P'.L := by
    apply basisLinearEquiv_mapsLattice_of_normalizedRange_eq P P' b b'
      (P.scaledNormalizedCoordinates w)
      (P'.scaledNormalizedCoordinates w') (P.scaledGramMatrix w).det
      (P.scaledGramMatrix_det_ne_zero w b hb)
    · exact P.map_scaledNormalizedCoordinates w b hb
    · intro x
      simpa [hG] using P'.map_scaledNormalizedCoordinates w' b' hb' x
    · exact hrange
  have htwice :
      (2 : K.1) • LinearMap.BilinForm.toMatrix b P.Q.associated =
        (2 : K.1) • LinearMap.BilinForm.toMatrix b' P'.Q.associated := by
    calc
      (2 : K.1) • LinearMap.BilinForm.toMatrix b P.Q.associated =
          (algebraMap (𝓞 K.1) K.1).mapMatrix (P.scaledGramMatrix w) :=
        (P.map_scaledGramMatrix w b hb).symm
      _ = (algebraMap (𝓞 K.1) K.1).mapMatrix
            (P'.scaledGramMatrix w') := by rw [hG]
      _ = (2 : K.1) • LinearMap.BilinForm.toMatrix b' P'.Q.associated :=
        P'.map_scaledGramMatrix w' b' hb'
  have hmatrix : LinearMap.BilinForm.toMatrix b P.Q.associated =
      LinearMap.BilinForm.toMatrix b' P'.Q.associated := by
    apply Matrix.ext
    intro i j
    have hij := congrFun (congrFun htwice i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hij
    exact mul_left_cancel₀ (by norm_num : (2 : K.1) ≠ 0) hij
  have hQ := P.basisLinearEquiv_mapQuadratic_of_matrix_eq P' b b' hmatrix
  exact ⟨equivalenceDataOfBasisLinearEquiv P P' b b' hmaps hQ⟩

end FixedFieldLatticePresentation

namespace GlobalLatticeClass

variable {K : CodedNumberField} {n : ℕ}

/-- A fixed-field class has a classic reduction code when its selected
representative admits a short field basis producing that code. -/
def HasClassicReductionCode (n : ℕ)
    (c : FieldFiber GlobalLatticeClass.fieldCode K)
    (code : IntegralReductionCode K.1 n) : Prop :=
  ∃ (hn : c.1.representative.rank = n)
    (hclassic :
      (FixedFieldLatticePresentation.ofGlobal c.1.representative c.2 hn).IsClassicIntegral)
    (w : Fin n →
      (FixedFieldLatticePresentation.ofGlobal c.1.representative c.2 hn).L)
    (b : Module.Basis (Fin n) K.1 (Fin n → K.1)),
      (∀ i, b i = (w i).1) ∧
      FixedFieldLatticePresentation.classicReductionCode
        (FixedFieldLatticePresentation.ofGlobal c.1.representative c.2 hn)
        hclassic w = code

/-- The analogous scale-two reduction relation for arbitrary integral
lattices. -/
def HasScaledReductionCode (n : ℕ)
    (c : FieldFiber GlobalLatticeClass.fieldCode K)
    (code : IntegralReductionCode K.1 n) : Prop :=
  ∃ (hn : c.1.representative.rank = n)
    (w : Fin n →
      (FixedFieldLatticePresentation.ofGlobal c.1.representative c.2 hn).L)
    (b : Module.Basis (Fin n) K.1 (Fin n → K.1)),
      (∀ i, b i = (w i).1) ∧
      FixedFieldLatticePresentation.scaledReductionCode
        (FixedFieldLatticePresentation.ofGlobal c.1.representative c.2 hn) w = code

/-- A common classic reduction code identifies the underlying global
field-lattice classes. -/
theorem eq_of_hasClassicReductionCode
    {c c' : FieldFiber GlobalLatticeClass.fieldCode K}
    {code : IntegralReductionCode K.1 n}
    (hc : HasClassicReductionCode n c code)
    (hc' : HasClassicReductionCode n c' code) : c = c' := by
  rcases hc with ⟨hn, hclassic, w, b, hb, hcode⟩
  rcases hc' with ⟨hn', hclassic', w', b', hb', hcode'⟩
  let P := FixedFieldLatticePresentation.ofGlobal c.1.representative c.2 hn
  let P' := FixedFieldLatticePresentation.ofGlobal c'.1.representative c'.2 hn'
  have hequiv : P.toGlobal.IsEquivalent P'.toGlobal :=
    FixedFieldLatticePresentation.isEquivalent_of_classicReductionCode_eq
      P P' hclassic hclassic' w w' b b' hb hb' (hcode.trans hcode'.symm)
  apply Subtype.ext
  calc
    c.1 = Quotient.mk _ c.1.representative := c.1.mk_representative.symm
    _ = Quotient.mk _ P.toGlobal := by
      rw [FixedFieldLatticePresentation.toGlobal_ofGlobal]
    _ = Quotient.mk _ P'.toGlobal := Quotient.sound hequiv
    _ = Quotient.mk _ c'.1.representative := by
      rw [FixedFieldLatticePresentation.toGlobal_ofGlobal]
    _ = c'.1 := c'.1.mk_representative

/-- A common scale-two reduction code identifies the underlying global
field-lattice classes. -/
theorem eq_of_hasScaledReductionCode
    {c c' : FieldFiber GlobalLatticeClass.fieldCode K}
    {code : IntegralReductionCode K.1 n}
    (hc : HasScaledReductionCode n c code)
    (hc' : HasScaledReductionCode n c' code) : c = c' := by
  rcases hc with ⟨hn, w, b, hb, hcode⟩
  rcases hc' with ⟨hn', w', b', hb', hcode'⟩
  let P := FixedFieldLatticePresentation.ofGlobal c.1.representative c.2 hn
  let P' := FixedFieldLatticePresentation.ofGlobal c'.1.representative c'.2 hn'
  have hequiv : P.toGlobal.IsEquivalent P'.toGlobal :=
    FixedFieldLatticePresentation.isEquivalent_of_scaledReductionCode_eq
      P P' w w' b b' hb hb' (hcode.trans hcode'.symm)
  apply Subtype.ext
  calc
    c.1 = Quotient.mk _ c.1.representative := c.1.mk_representative.symm
    _ = Quotient.mk _ P.toGlobal := by
      rw [FixedFieldLatticePresentation.toGlobal_ofGlobal]
    _ = Quotient.mk _ P'.toGlobal := Quotient.sound hequiv
    _ = Quotient.mk _ c'.1.representative := by
      rw [FixedFieldLatticePresentation.toGlobal_ofGlobal]
    _ = c'.1 := c'.1.mk_representative

/-- For a fixed field and rank, the classic-integral trace-Euclidean classes
form a finite set.  This is the direct replacement for the former external
fixed-volume reduction certificate. -/
theorem finite_fixedField_rank_classic_traceEuclidean
    (K : CodedNumberField) (n : ℕ) {t u : ℝ}
    (ht : 0 < t) (htu : t < u) :
    {c : FieldFiber GlobalLatticeClass.fieldCode K |
      c.1.rank = n ∧ c.1.IsTraceEuclidean t ∧
        c.1.IsClassicIntegral}.Finite := by
  let family : FieldFiber GlobalLatticeClass.fieldCode K → Prop :=
    fun c ↦ c.1.rank = n ∧ c.1.IsTraceEuclidean t ∧
      c.1.IsClassicIntegral
  let codes : Set (IntegralReductionCode K.1 n) :=
    {code | IntegralReductionCode.IsBounded
      (FixedFieldLatticePresentation.fixedFieldGramBound K n u) code}
  apply finite_of_finite_complete_relation family codes
    (HasClassicReductionCode n)
  · exact finite_boundedIntegralReductionCodes K.1 n
      (FixedFieldLatticePresentation.fixedFieldGramBound K n u)
  · intro c hc
    have hn : c.1.representative.rank = n := by
      rw [c.1.representative_rank]
      exact hc.1
    let P := FixedFieldLatticePresentation.ofGlobal c.1.representative c.2 hn
    have hPglobal : P.toGlobal = c.1.representative :=
      FixedFieldLatticePresentation.toGlobal_ofGlobal _ _ _
    have hErep : c.1.representative.IsTraceEuclidean t := by
      rw [← GlobalLatticeClass.isTraceEuclidean_mk c.1.representative,
        c.1.mk_representative]
      exact hc.2.1
    have hE : P.IsTraceEuclidean t := by
      change P.toGlobal.IsTraceEuclidean t
      rw [hPglobal]
      exact hErep
    have hclassicRep : c.1.representative.IsClassicIntegral :=
      c.1.representative_isClassicIntegral hc.2.2
    have hclassic : P.IsClassicIntegral := by
      change P.toGlobal.IsClassicIntegral
      rw [hPglobal]
      exact hclassicRep
    obtain ⟨w, b, hb, hbounded⟩ :=
      P.exists_bounded_classicReductionCode_of_traceEuclidean
        ht htu hE hclassic
    refine ⟨P.classicReductionCode hclassic w, hbounded, ?_⟩
    exact ⟨hn, hclassic, w, b, hb, rfl⟩
  · intro c c' code _hc _hc' hcode hcode'
    exact eq_of_hasClassicReductionCode hcode hcode'

/-- For a fixed field and rank, all integral trace-Euclidean classes form a
finite set, using the scale-two integral Gram matrix. -/
theorem finite_fixedField_rank_integral_traceEuclidean
    (K : CodedNumberField) (n : ℕ) {t u : ℝ}
    (ht : 0 < t) (htu : t < u) :
    {c : FieldFiber GlobalLatticeClass.fieldCode K |
      c.1.rank = n ∧ c.1.IsTraceEuclidean t}.Finite := by
  let family : FieldFiber GlobalLatticeClass.fieldCode K → Prop :=
    fun c ↦ c.1.rank = n ∧ c.1.IsTraceEuclidean t
  let codes : Set (IntegralReductionCode K.1 n) :=
    {code | IntegralReductionCode.IsBounded
      (FixedFieldLatticePresentation.fixedFieldScaledGramBound K n u) code}
  apply finite_of_finite_complete_relation family codes
    (HasScaledReductionCode n)
  · exact finite_boundedIntegralReductionCodes K.1 n
      (FixedFieldLatticePresentation.fixedFieldScaledGramBound K n u)
  · intro c hc
    have hn : c.1.representative.rank = n := by
      rw [c.1.representative_rank]
      exact hc.1
    let P := FixedFieldLatticePresentation.ofGlobal c.1.representative c.2 hn
    have hPglobal : P.toGlobal = c.1.representative :=
      FixedFieldLatticePresentation.toGlobal_ofGlobal _ _ _
    have hErep : c.1.representative.IsTraceEuclidean t := by
      rw [← GlobalLatticeClass.isTraceEuclidean_mk c.1.representative,
        c.1.mk_representative]
      exact hc.2
    have hE : P.IsTraceEuclidean t := by
      change P.toGlobal.IsTraceEuclidean t
      rw [hPglobal]
      exact hErep
    obtain ⟨w, b, hb, hbounded⟩ :=
      P.exists_bounded_scaledReductionCode_of_traceEuclidean ht htu hE
    refine ⟨P.scaledReductionCode w, hbounded, ?_⟩
    exact ⟨hn, w, b, hb, rfl⟩
  · intro c c' code _hc _hc' hcode hcode'
    exact eq_of_hasScaledReductionCode hcode hcode'

end GlobalLatticeClass

namespace GlobalLatticePresentation

/-- Strict trace-Euclideanity forces the parameter to be positive. -/
theorem traceEuclidean_parameter_pos
    (P : GlobalLatticePresentation) {t : ℝ}
    (hE : P.IsTraceEuclidean t) : 0 < t := by
  obtain ⟨y, hy⟩ := hE 0
  have hnonnegQ : 0 ≤ P.traceQuadraticForm (0 - y.1) := by
    by_cases hz : 0 - y.1 = 0
    · simp [hz]
    · exact (P.traceQuadraticForm_posDef (0 - y.1) hz).le
  have hnonnegR :
      0 ≤ ((P.traceQuadraticForm (0 - y.1) : ℚ) : ℝ) := by
    exact_mod_cast hnonnegQ
  exact hnonnegR.trans_lt (by
    simpa [traceQuadraticForm_apply] using hy)

end GlobalLatticePresentation

end

end TraceEuclidean
