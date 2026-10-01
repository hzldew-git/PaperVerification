import TraceEuclidean.TraceRealization

/-!
The diagonal real model is explicitly identified with the scalar extension
of the rational number-field vector space.  The natural rational embedding
is the pure-tensor map `x ↦ 1 ⊗ x`.
-/

namespace TraceEuclidean

noncomputable section

namespace GlobalLatticePresentation

/-- The real scalar extension of the underlying rational quadratic space. -/
abbrev TensorRealTraceSpace (P : GlobalLatticePresentation) :=
  TensorProduct ℚ ℝ (Fin P.rank → P.field.1)

/-- The selected rational lattice basis identifies the scalar extension with
the diagonal real trace model. -/
def tensorRealTraceEquiv (P : GlobalLatticePresentation) :
    P.TensorRealTraceSpace ≃ₗ[ℝ] P.RealTraceSpace :=
  (P.rationalTraceBasis.baseChange ℝ).equiv P.realIntegralBasis (Equiv.refl _)

/-- Each chosen lattice-basis vector is carried to its diagonal real image. -/
theorem tensorRealTraceEquiv_basis (P : GlobalLatticePresentation)
    (i : Module.Free.ChooseBasisIndex ℤ P.integralRestriction) :
    P.tensorRealTraceEquiv
      (TensorProduct.tmul ℚ (1 : ℝ) (P.rationalTraceBasis i)) =
      P.realIntegralBasis i := by
  rw [← Module.Basis.baseChange_apply (S := ℝ) P.rationalTraceBasis i]
  simp only [tensorRealTraceEquiv, Module.Basis.equiv_apply, Equiv.refl_apply]

/-- The tensor embedding agrees with the existing rational-point embedding
for every number-field vector, not only for the selected basis vectors. -/
theorem tensorRealTraceEquiv_rationalPoint
    (P : GlobalLatticePresentation) (x : Fin P.rank → P.field.1) :
    P.tensorRealTraceEquiv (TensorProduct.tmul ℚ (1 : ℝ) x) =
      P.rationalPointEmbedding x := by
  let f : (Fin P.rank → P.field.1) →ₗ[ℚ] P.RealTraceSpace :=
    (P.tensorRealTraceEquiv.toLinearMap.restrictScalars ℚ).comp
      (TensorProduct.mk ℚ ℝ (Fin P.rank → P.field.1) 1)
  have hf : f = P.rationalPointEmbedding := by
    apply P.rationalTraceBasis.ext
    intro i
    change P.tensorRealTraceEquiv
        (TensorProduct.tmul ℚ (1 : ℝ) (P.rationalTraceBasis i)) =
      P.rationalPointEmbedding (P.rationalTraceBasis i)
    rw [P.tensorRealTraceEquiv_basis]
    ext j
    simp
  exact congrFun (congrArg DFunLike.coe hf) x

/-- The real trace quadratic form on the scalar extension. -/
def tensorRealTraceQuadraticForm (P : GlobalLatticePresentation) :
    QuadraticForm ℝ P.TensorRealTraceSpace :=
  P.realTraceQuadraticForm.comp P.tensorRealTraceEquiv.toLinearMap

theorem tensorRealTraceQuadraticForm_posDef
    (P : GlobalLatticePresentation) :
    P.tensorRealTraceQuadraticForm.PosDef := by
  intro x hx
  change 0 < P.realTraceQuadraticForm (P.tensorRealTraceEquiv x)
  apply P.realTraceQuadraticForm_posDef
  intro hzero
  apply hx
  exact P.tensorRealTraceEquiv.injective (by simpa using hzero)

/-- On the natural rational embedding, the extended form equals the field
trace of the original quadratic form. -/
theorem tensorRealTraceQuadraticForm_rationalPoint
    (P : GlobalLatticePresentation) (x : Fin P.rank → P.field.1) :
    P.tensorRealTraceQuadraticForm
        (TensorProduct.tmul ℚ (1 : ℝ) x) =
      (P.traceQuadraticForm x : ℝ) := by
  change P.realTraceQuadraticForm
      (P.tensorRealTraceEquiv (TensorProduct.tmul ℚ (1 : ℝ) x)) = _
  rw [P.tensorRealTraceEquiv_rationalPoint]
  exact P.realTraceQuadraticForm_rationalPointEmbedding x

end GlobalLatticePresentation

end

end TraceEuclidean
