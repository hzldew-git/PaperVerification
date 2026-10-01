import TraceEuclidean.TraceRealEmbeddings

/-!
The rational Minkowski map into the product of all real embeddings of the
underlying totally real field. This is the rational-point part of the
manuscript's product realization.
-/

namespace TraceEuclidean

noncomputable section

/-- Simultaneous evaluation under every real embedding is rational-linear. -/
def realFieldEmbeddingMap (F : Type*) [Field F] [NumberField F]
    [NumberField.IsTotallyReal F] :
    F →ₗ[ℚ] ((F →+* ℝ) → ℝ) where
  toFun a σ := σ a
  map_add' a b := by funext σ; simp
  map_smul' q a := by funext σ; simp [Algebra.smul_def]

theorem realFieldEmbeddingMap_injective (F : Type*) [Field F]
    [NumberField F] [NumberField.IsTotallyReal F] :
    Function.Injective (realFieldEmbeddingMap F) := by
  let σ : F →+* ℝ := (realComplexEmbeddingsEquiv F).symm (Classical.choice inferInstance)
  intro a b hab
  apply σ.injective
  exact congrFun hab σ

namespace GlobalLatticePresentation

/-- Rational Minkowski embedding of the quadratic space into the product
of its real coordinate spaces. -/
def realVectorEmbeddingMap (P : GlobalLatticePresentation) :
    (Fin P.rank → P.field.1) →ₗ[ℚ]
      ((P.field.1 →+* ℝ) → Fin P.rank → ℝ) where
  toFun x σ i := σ (x i)
  map_add' x y := by funext σ i; simp
  map_smul' q x := by funext σ i; simp [Algebra.smul_def]

theorem realVectorEmbeddingMap_injective (P : GlobalLatticePresentation) :
    Function.Injective P.realVectorEmbeddingMap := by
  letI : NumberField.IsTotallyReal P.field.1 := P.totallyReal
  intro x y h
  funext i
  apply realFieldEmbeddingMap_injective P.field.1
  funext σ
  exact congrFun (congrFun h σ) i

end GlobalLatticePresentation

end

end TraceEuclidean
