import TraceEuclidean.TraceRationalLattice
import Mathlib.RingTheory.Trace.Basic

/-!
For a totally real number field, the rational field trace is the sum of the
values of its real embeddings. This identifies the rational values of the
manuscript's sum of local forms with the trace form used elsewhere here.
-/

namespace TraceEuclidean

noncomputable section

/-- Every complex embedding of a totally real field comes from a unique real
embedding. -/
def realComplexEmbeddingsEquiv (F : Type*) [Field F] [NumberField F]
    [NumberField.IsTotallyReal F] :
    (F →+* ℝ) ≃ (F →+* ℂ) where
  toFun σ := Complex.ofRealHom.comp σ
  invFun φ := (NumberField.IsTotallyReal.complexEmbedding_isReal φ).embedding
  left_inv σ := by
    ext x
    simp [NumberField.ComplexEmbedding.IsReal.embedding]
  right_inv φ := by
    ext x
    exact NumberField.ComplexEmbedding.IsReal.coe_embedding_apply
      (NumberField.IsTotallyReal.complexEmbedding_isReal φ) x

/-- A totally real field has exactly `finrank ℚ F` real embeddings. -/
theorem card_realEmbeddings (F : Type*) [Field F] [NumberField F]
    [NumberField.IsTotallyReal F] :
    Fintype.card (F →+* ℝ) = Module.finrank ℚ F := by
  rw [Fintype.card_congr (realComplexEmbeddingsEquiv F)]
  exact NumberField.Embeddings.card F ℂ

/-- The trace of a totally real algebraic number is the sum over its real
embeddings, with no unstated multiplicity factor. -/
theorem trace_eq_sum_realEmbeddings (F : Type*) [Field F] [NumberField F]
    [NumberField.IsTotallyReal F] (a : F) :
    ((Algebra.trace ℚ F a : ℚ) : ℝ) =
      ∑ σ : F →+* ℝ, σ a := by
  let e : (F →+* ℝ) ≃ (F →ₐ[ℚ] ℂ) :=
    (realComplexEmbeddingsEquiv F).trans RingHom.equivRatAlgHom
  have hsum : (∑ σ : F →ₐ[ℚ] ℂ, σ a) =
      ∑ τ : F →+* ℝ, ((τ a : ℝ) : ℂ) := by
    apply (Fintype.sum_equiv e (fun τ : F →+* ℝ => ((τ a : ℝ) : ℂ))
      (fun σ : F →ₐ[ℚ] ℂ => σ a) ?_).symm
    intro τ
    rfl
  have htrace := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := a)
  apply Complex.ofReal_injective
  change (((Algebra.trace ℚ F a : ℚ) : ℝ) : ℂ) =
    ((∑ τ : F →+* ℝ, τ a : ℝ) : ℂ)
  simpa using htrace.trans hsum

namespace GlobalLatticePresentation

/-- On the rational quadratic space, the trace form is the sum of the
quadratic value at all real embeddings. -/
theorem traceQuadraticForm_eq_sum_realEmbeddings
    (P : GlobalLatticePresentation) (x : Fin P.rank → P.field.1) :
    (P.traceQuadraticForm x : ℝ) =
      ∑ σ : P.field.1 →+* ℝ, σ (P.Q x) := by
  letI : NumberField.IsTotallyReal P.field.1 := P.totallyReal
  rw [P.traceQuadraticForm_apply]
  exact trace_eq_sum_realEmbeddings P.field.1 (P.Q x)

end GlobalLatticePresentation

end

end TraceEuclidean
