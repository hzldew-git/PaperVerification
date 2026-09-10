import TraceEuclidean.TraceRationalLattice
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.NhdsWithin
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
Real-coordinate realization of the rational trace form.  A rational
diagonalization gives an explicit positive definite real quadratic form, and
the embedded rational points are dense in that real space.
-/

namespace TraceEuclidean

noncomputable section

namespace GlobalLatticePresentation

/-- Dimension index for the real trace space. -/
abbrev TraceDimensionIndex (P : GlobalLatticePresentation) :=
  Fin (Module.finrank ℚ (Fin P.rank → P.field.1))

/-- The real vector space obtained from rational diagonal coordinates. -/
abbrev RealTraceSpace (P : GlobalLatticePresentation) :=
  P.TraceDimensionIndex → ℝ

/-- Coordinatewise inclusion of rational vectors into the real trace space. -/
def rationalVectorCast (P : GlobalLatticePresentation) :
    (P.TraceDimensionIndex → ℚ) →ₗ[ℚ] P.RealTraceSpace where
  toFun x i := (x i : ℝ)
  map_add' x y := by ext i; simp
  map_smul' q x := by ext i; simp [Rat.smul_def]

/-- The original number-field vector space embedded in real diagonal coordinates. -/
def rationalPointEmbedding (P : GlobalLatticePresentation) :
    (Fin P.rank → P.field.1) →ₗ[ℚ] P.RealTraceSpace :=
  P.rationalVectorCast.comp P.traceDiagonalIsometry.toLinearEquiv.toLinearMap

@[simp]
theorem rationalVectorCast_apply (P : GlobalLatticePresentation)
    (x : P.TraceDimensionIndex → ℚ) (i : P.TraceDimensionIndex) :
    P.rationalVectorCast x i = (x i : ℝ) :=
  rfl

@[simp]
theorem rationalPointEmbedding_apply (P : GlobalLatticePresentation)
    (x : Fin P.rank → P.field.1) (i : P.TraceDimensionIndex) :
    P.rationalPointEmbedding x i = (P.traceDiagonalIsometry x i : ℝ) :=
  rfl

/-- The positive real quadratic form represented by the trace diagonalization. -/
def realTraceQuadraticForm (P : GlobalLatticePresentation) :
    QuadraticForm ℝ P.RealTraceSpace :=
  QuadraticMap.weightedSumSquares ℝ
    (fun i ↦ (P.traceDiagonalWeights i : ℝ))

@[simp]
theorem realTraceQuadraticForm_apply (P : GlobalLatticePresentation)
    (x : P.RealTraceSpace) :
    P.realTraceQuadraticForm x =
      ∑ i : P.TraceDimensionIndex,
        (P.traceDiagonalWeights i : ℝ) * (x i * x i) := by
  simp [realTraceQuadraticForm, QuadraticMap.weightedSumSquares_apply]

/-- The real diagonal form is positive definite. -/
theorem realTraceQuadraticForm_posDef (P : GlobalLatticePresentation) :
    P.realTraceQuadraticForm.PosDef := by
  classical
  intro x hx
  rw [P.realTraceQuadraticForm_apply]
  apply Finset.sum_pos'
  · intro i _hi
    have hw : (0 : ℝ) < (P.traceDiagonalWeights i : ℝ) := by
      exact_mod_cast P.traceDiagonalWeights_pos i
    exact mul_nonneg hw.le (mul_self_nonneg _)
  · simp only [ne_eq, funext_iff, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    refine ⟨i, Finset.mem_univ i, ?_⟩
    have hw : (0 : ℝ) < (P.traceDiagonalWeights i : ℝ) := by
      exact_mod_cast P.traceDiagonalWeights_pos i
    exact mul_pos hw (mul_self_pos.mpr hi)

/-- On embedded rational points, the real form is exactly the rational trace. -/
theorem realTraceQuadraticForm_rationalPointEmbedding
    (P : GlobalLatticePresentation)
    (x : Fin P.rank → P.field.1) :
    P.realTraceQuadraticForm (P.rationalPointEmbedding x) =
      (P.traceQuadraticForm x : ℝ) := by
  rw [P.realTraceQuadraticForm_apply]
  simp only [P.rationalPointEmbedding_apply]
  norm_cast
  have h := P.traceDiagonalIsometry_map x
  rw [QuadraticMap.weightedSumSquares_apply] at h
  simpa only [smul_eq_mul] using h

/-- Coordinatewise rational vectors are dense in the real trace space. -/
theorem rationalVectorCast_denseRange (P : GlobalLatticePresentation) :
    DenseRange P.rationalVectorCast := by
  have hpi : DenseRange
      (Pi.map fun _ : P.TraceDimensionIndex ↦ ((↑) : ℚ → ℝ)) :=
    DenseRange.piMap fun _ ↦ Rat.denseRange_cast
  have heq :
      (P.rationalVectorCast :
        (P.TraceDimensionIndex → ℚ) → P.RealTraceSpace) =
        Pi.map (fun _ : P.TraceDimensionIndex ↦ ((↑) : ℚ → ℝ)) := by
    funext x
    ext i
    simp only [rationalVectorCast_apply, Pi.map_apply]
  rw [heq]
  exact hpi

/-- The embedded number-field vectors are dense in the real trace space. -/
theorem rationalPointEmbedding_denseRange (P : GlobalLatticePresentation) :
    DenseRange P.rationalPointEmbedding := by
  have hsur : Function.Surjective P.traceDiagonalIsometry :=
    P.traceDiagonalIsometry.surjective
  have hcontinuous : Continuous P.rationalVectorCast := by
    apply continuous_pi
    intro i
    exact Rat.continuous_coe_real.comp (continuous_apply i)
  have hcomp := P.rationalVectorCast_denseRange.comp hsur.denseRange
    hcontinuous
  simpa [rationalPointEmbedding, Function.comp_def] using hcomp

/-- The rational basis of the lattice expressed in diagonal coordinates. -/
def diagonalRationalBasis (P : GlobalLatticePresentation) :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ P.integralRestriction)
      ℚ (P.TraceDimensionIndex → ℚ) :=
  P.rationalTraceBasis.map P.traceDiagonalIsometry.toLinearEquiv

/-- The same lattice basis after extending the coordinate field to `ℝ`. -/
def realIntegralBasis (P : GlobalLatticePresentation) :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ P.integralRestriction)
      ℝ P.RealTraceSpace :=
  (P.diagonalRationalBasis.baseChange ℝ).map
    (TensorProduct.piScalarRight ℚ ℝ ℝ P.TraceDimensionIndex)

@[simp]
theorem realIntegralBasis_apply (P : GlobalLatticePresentation)
    (i : Module.Free.ChooseBasisIndex ℤ P.integralRestriction)
    (j : P.TraceDimensionIndex) :
    P.realIntegralBasis i j =
      P.rationalPointEmbedding (P.integralRestrictionBasis i).1 j := by
  simp [realIntegralBasis, diagonalRationalBasis,
    rationalPointEmbedding_apply, rationalTraceBasis_apply,
    TensorProduct.piScalarRightHom_tmul]

/-- The embedded integral lattice in the real trace space. -/
def realIntegralLattice (P : GlobalLatticePresentation) :
    Submodule ℤ P.RealTraceSpace :=
  Submodule.span ℤ (Set.range P.realIntegralBasis)

/-- The real trace lattice is discrete. -/
instance (P : GlobalLatticePresentation) :
    DiscreteTopology P.realIntegralLattice := by
  unfold realIntegralLattice
  infer_instance

/-- The real trace lattice spans the full real trace space. -/
instance (P : GlobalLatticePresentation) :
    IsZLattice ℝ P.realIntegralLattice := by
  unfold realIntegralLattice
  infer_instance

/-- The real embedding of every vector in the original lattice lies in the real lattice. -/
theorem rationalPointEmbedding_mem_realIntegralLattice
    (P : GlobalLatticePresentation)
    (x : Fin P.rank → P.field.1) (hx : x ∈ P.integralRestriction) :
    P.rationalPointEmbedding x ∈ P.realIntegralLattice := by
  classical
  have hspan : x ∈ Submodule.span ℤ
      (Set.range fun i ↦ (P.integralRestrictionBasis i).1) := by
    have hL : P.integralRestriction =
        Submodule.span ℤ
          (Set.range fun i ↦ (P.integralRestrictionBasis i).1) := by
      calc
        P.integralRestriction =
            Submodule.map P.integralRestriction.subtype
              (⊤ : Submodule ℤ P.integralRestriction) := by
                rw [Submodule.map_subtype_top]
        _ = Submodule.map P.integralRestriction.subtype
            (Submodule.span ℤ (Set.range P.integralRestrictionBasis)) := by
              rw [P.integralRestrictionBasis.span_eq]
        _ = Submodule.span ℤ
            (P.integralRestriction.subtype ''
              Set.range P.integralRestrictionBasis) := by
                rw [Submodule.map_span]
        _ = Submodule.span ℤ
            (Set.range fun i ↦ (P.integralRestrictionBasis i).1) := by
              congr 1
              ext y
              simp
    rw [← hL]
    exact hx
  refine Submodule.span_induction
    (p := fun y _hy ↦
      P.rationalPointEmbedding y ∈ P.realIntegralLattice) ?_ (by simp) ?_ ?_ hspan
  · intro y hy
    obtain ⟨i, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨i, ?_⟩
    ext j
    simp
  · intro y z _hy _hz hy hz
    simpa using P.realIntegralLattice.add_mem hy hz
  · intro a y _hy hy
    rw [map_zsmul]
    exact P.realIntegralLattice.smul_mem a hy

/-- Every original lattice vector supplies a point of the embedded real lattice. -/
def realLatticePoint (P : GlobalLatticePresentation) (y : P.L) :
    P.realIntegralLattice := by
  refine ⟨P.rationalPointEmbedding y.1, ?_⟩
  exact P.rationalPointEmbedding_mem_realIntegralLattice y.1 y.2

@[simp]
theorem realLatticePoint_coe (P : GlobalLatticePresentation) (y : P.L) :
    (P.realLatticePoint y : P.RealTraceSpace) =
      P.rationalPointEmbedding y.1 :=
  rfl

end GlobalLatticePresentation

end

end TraceEuclidean
