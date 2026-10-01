import TraceEuclidean.TraceProductEmbedding
import TraceEuclidean.TraceFormUniqueness
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
The local real quadratic form at each field embedding is obtained by scalar
extension of the original number-field quadratic form. Their sum is the
manuscript's product-space trace cost on rationally embedded vectors.
-/

namespace TraceEuclidean

noncomputable section

namespace GlobalLatticePresentation

/-- Every quadratic form on a finite real coordinate space is continuous. -/
private theorem continuous_quadraticForm_pi {ι : Type*} [Finite ι]
    (Q : QuadraticForm ℝ (ι → ℝ)) : Continuous Q := by
  letI := Fintype.ofFinite ι
  have hc : Continuous (fun x : ι → ℝ => Q.associated x x) :=
    by fun_prop
  exact hc.congr (fun x => by rw [QuadraticMap.associated_eq_self_apply])

/-- Scalar extension of the quadratic form along one real embedding. -/
def localTraceForm (P : GlobalLatticePresentation)
    (σ : P.field.1 →+* ℝ) :
    QuadraticForm ℝ (Fin P.rank → ℝ) := by
  letI : Algebra P.field.1 ℝ := σ.toAlgebra
  exact (P.Q.baseChange ℝ).comp
    (TensorProduct.piScalarRight P.field.1 ℝ ℝ (Fin P.rank)).symm.toLinearMap

/-- The local quadratic form agrees with the embedding of the original
quadratic value on rational points. -/
theorem localTraceForm_rationalPoint (P : GlobalLatticePresentation)
    (σ : P.field.1 →+* ℝ) (x : Fin P.rank → P.field.1) :
    P.localTraceForm σ (fun i => σ (x i)) = σ (P.Q x) := by
  letI : Algebra P.field.1 ℝ := σ.toAlgebra
  have hcoord :
      (TensorProduct.piScalarRight P.field.1 ℝ ℝ (Fin P.rank))
        (TensorProduct.tmul P.field.1 (1 : ℝ) x) =
      (fun i => σ (x i)) := by
    ext i
    simp [TensorProduct.piScalarRightHom_tmul, Algebra.smul_def,
      RingHom.algebraMap_toAlgebra]
  calc
    P.localTraceForm σ (fun i => σ (x i)) =
        P.localTraceForm σ
          ((TensorProduct.piScalarRight P.field.1 ℝ ℝ (Fin P.rank))
            (TensorProduct.tmul P.field.1 (1 : ℝ) x)) := by rw [hcoord]
    _ = (P.Q.baseChange ℝ) (TensorProduct.tmul P.field.1 (1 : ℝ) x) := by
      change (P.Q.baseChange ℝ)
        ((TensorProduct.piScalarRight P.field.1 ℝ ℝ (Fin P.rank)).symm
          ((TensorProduct.piScalarRight P.field.1 ℝ ℝ (Fin P.rank))
            (TensorProduct.tmul P.field.1 (1 : ℝ) x))) = _
      rw [LinearEquiv.symm_apply_apply]
    _ = σ (P.Q x) := by
      rw [QuadraticForm.baseChange_tmul]
      simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]

/-- Each local quadratic form is continuous on its finite-dimensional real space. -/
theorem localTraceForm_continuous (P : GlobalLatticePresentation)
    (σ : P.field.1 →+* ℝ) : Continuous (P.localTraceForm σ) :=
  continuous_quadraticForm_pi (P.localTraceForm σ)

/-- Sum of the local real quadratic forms on the product of real spaces. -/
def productTraceCost (P : GlobalLatticePresentation)
    (z : (P.field.1 →+* ℝ) → Fin P.rank → ℝ) : ℝ :=
  ∑ σ : P.field.1 →+* ℝ, P.localTraceForm σ (z σ)

/-- The finite sum of local forms is continuous on the product space. -/
theorem productTraceCost_continuous (P : GlobalLatticePresentation) :
    Continuous P.productTraceCost := by
  unfold productTraceCost
  apply continuous_finsetSum
  intro σ _
  exact (P.localTraceForm_continuous σ).comp (continuous_apply σ)

/-- The product trace cost equals the rational field trace on the image of
the original quadratic space. -/
theorem productTraceCost_rationalPoint (P : GlobalLatticePresentation)
    (x : Fin P.rank → P.field.1) :
    P.productTraceCost (P.realVectorEmbeddingMap x) =
      (P.traceQuadraticForm x : ℝ) := by
  letI : NumberField.IsTotallyReal P.field.1 := P.totallyReal
  rw [P.traceQuadraticForm_eq_sum_realEmbeddings]
  simp only [productTraceCost, realVectorEmbeddingMap, LinearMap.coe_mk,
    AddHom.coe_mk, P.localTraceForm_rationalPoint]

/-- Once a continuous real comparison map extends the rational product
embedding, the product trace cost agrees everywhere with the constructed
real trace form. -/
theorem productTraceCost_transport (P : GlobalLatticePresentation)
    (e : P.RealTraceSpace →
      (P.field.1 →+* ℝ) → Fin P.rank → ℝ)
    (hcontinuous : Continuous (P.productTraceCost ∘ e))
    (hembedding : ∀ x, e (P.rationalPointEmbedding x) =
      P.realVectorEmbeddingMap x)
    (y : P.RealTraceSpace) :
    P.productTraceCost (e y) = P.realTraceQuadraticForm y := by
  exact P.realTraceQuadraticForm_transport e P.realVectorEmbeddingMap
    P.productTraceCost hcontinuous hembedding
    P.productTraceCost_rationalPoint y

/-- A real-linear identification extending the rational product embedding
automatically transports the trace form; continuity requires no extra input. -/
theorem productTraceCost_transport_linear (P : GlobalLatticePresentation)
    (e : P.RealTraceSpace →ₗ[ℝ]
      (P.field.1 →+* ℝ) → Fin P.rank → ℝ)
    (hembedding : ∀ x, e (P.rationalPointEmbedding x) =
      P.realVectorEmbeddingMap x)
    (y : P.RealTraceSpace) :
    P.productTraceCost (e y) = P.realTraceQuadraticForm y := by
  letI : NumberField.IsTotallyReal P.field.1 := P.totallyReal
  exact P.productTraceCost_transport e
    (P.productTraceCost_continuous.comp e.continuous_of_finiteDimensional)
    hembedding y

end GlobalLatticePresentation

end

end TraceEuclidean
