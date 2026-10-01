import TraceEuclidean.TraceRealization

/-!
The real trace form is determined by its values on the embedded rational
number-field vectors.  This supplies the uniqueness step needed when comparing
the diagonal real model with a separately constructed Minkowski model.
-/

namespace TraceEuclidean

noncomputable section

namespace GlobalLatticePresentation

/-- The diagonal real trace form is continuous. -/
theorem realTraceQuadraticForm_continuous
    (P : GlobalLatticePresentation) :
    Continuous P.realTraceQuadraticForm := by
  have h : Continuous (fun x : P.RealTraceSpace =>
      ∑ i : P.TraceDimensionIndex,
        (P.traceDiagonalWeights i : ℝ) * (x i * x i)) := by
    fun_prop
  exact h.congr (fun x => (P.realTraceQuadraticForm_apply x).symm)

/-- A continuous real function agreeing with the trace form on all rational
points agrees with the real trace form everywhere. -/
theorem realTraceQuadraticForm_unique
    (P : GlobalLatticePresentation)
    (f : P.RealTraceSpace → ℝ) (hf : Continuous f)
    (htrace : ∀ x : Fin P.rank → P.field.1,
      f (P.rationalPointEmbedding x) = (P.traceQuadraticForm x : ℝ)) :
    f = P.realTraceQuadraticForm := by
  apply P.rationalPointEmbedding_denseRange.equalizer hf
    P.realTraceQuadraticForm_continuous
  funext x
  exact (htrace x).trans (P.realTraceQuadraticForm_rationalPointEmbedding x).symm

/-- Criterion for identifying a real model with the constructed trace form.
The remaining Minkowski comparison must supply a map `e` carrying rational
vectors to their manuscript embeddings and the compatibility of `q` there. -/
theorem realTraceQuadraticForm_transport
    (P : GlobalLatticePresentation) {E : Type*}
    (e : P.RealTraceSpace → E)
    (sigma : (Fin P.rank → P.field.1) → E)
    (q : E → ℝ)
    (hcontinuous : Continuous (q ∘ e))
    (hembedding : ∀ x, e (P.rationalPointEmbedding x) = sigma x)
    (htrace : ∀ x, q (sigma x) = (P.traceQuadraticForm x : ℝ))
    (y : P.RealTraceSpace) :
    q (e y) = P.realTraceQuadraticForm y := by
  have h := P.realTraceQuadraticForm_unique (q ∘ e) hcontinuous (by
    intro x
    exact (congrArg q (hembedding x)).trans (htrace x))
  exact congrFun h y

end GlobalLatticePresentation

end

end TraceEuclidean
