import TraceEuclidean.TraceLocalForms
import TraceEuclidean.TraceTensorCoordinates

/-!
The real-linear product embedding is defined from the rational lattice basis.
Its value on every rational vector is the simultaneous real embedding map.
-/

namespace TraceEuclidean

noncomputable section

namespace GlobalLatticePresentation

/-- Extend the rational product embedding along the chosen real lattice basis. -/
def realProductEmbeddingMap (P : GlobalLatticePresentation) :
    P.RealTraceSpace →ₗ[ℝ]
      ((P.field.1 →+* ℝ) → Fin P.rank → ℝ) :=
  P.realIntegralBasis.constr ℝ
    (fun i => P.realVectorEmbeddingMap (P.rationalTraceBasis i))

theorem realProductEmbeddingMap_basis (P : GlobalLatticePresentation)
    (i : Module.Free.ChooseBasisIndex ℤ P.integralRestriction) :
    P.realProductEmbeddingMap (P.realIntegralBasis i) =
      P.realVectorEmbeddingMap (P.rationalTraceBasis i) := by
  simp [realProductEmbeddingMap]

theorem realProductEmbeddingMap_rationalPoint
    (P : GlobalLatticePresentation) (x : Fin P.rank → P.field.1) :
    P.realProductEmbeddingMap (P.rationalPointEmbedding x) =
      P.realVectorEmbeddingMap x := by
  let f : (Fin P.rank → P.field.1) →ₗ[ℚ]
      ((P.field.1 →+* ℝ) → Fin P.rank → ℝ) :=
    (P.realProductEmbeddingMap.restrictScalars ℚ).comp P.rationalPointEmbedding
  have hf : f = P.realVectorEmbeddingMap := by
    apply P.rationalTraceBasis.ext
    intro i
    change P.realProductEmbeddingMap
        (P.rationalPointEmbedding (P.rationalTraceBasis i)) =
      P.realVectorEmbeddingMap (P.rationalTraceBasis i)
    have hb : P.rationalPointEmbedding (P.rationalTraceBasis i) =
        P.realIntegralBasis i := by
      ext j
      simp
    rw [hb]
    exact P.realProductEmbeddingMap_basis i
  exact congrFun (congrArg DFunLike.coe hf) x

/-- On the entire real trace space, the product sum is the trace form. -/
theorem productTraceCost_realProductEmbeddingMap
    (P : GlobalLatticePresentation) (y : P.RealTraceSpace) :
    P.productTraceCost (P.realProductEmbeddingMap y) =
      P.realTraceQuadraticForm y := by
  exact P.productTraceCost_transport_linear P.realProductEmbeddingMap
    P.realProductEmbeddingMap_rationalPoint y

/-- The real product embedding has trivial kernel. -/
theorem realProductEmbeddingMap_injective
    (P : GlobalLatticePresentation) :
    Function.Injective P.realProductEmbeddingMap := by
  intro x y hxy
  have hzero : P.realProductEmbeddingMap (x - y) = 0 := by
    calc
      P.realProductEmbeddingMap (x - y) =
          P.realProductEmbeddingMap x - P.realProductEmbeddingMap y :=
        P.realProductEmbeddingMap.map_sub x y
      _ = 0 := by rw [hxy, sub_self]
  have hform : P.realTraceQuadraticForm (x - y) = 0 := by
    rw [← P.productTraceCost_realProductEmbeddingMap, hzero]
    simp [productTraceCost]
  apply sub_eq_zero.mp
  by_contra hne
  have hp := P.realTraceQuadraticForm_posDef (x - y) hne
  linarith

/-- The diagonal and product realizations have the same real dimension. -/
theorem realProductSpace_finrank (P : GlobalLatticePresentation) :
    Module.finrank ℝ P.RealTraceSpace =
      Module.finrank ℝ ((P.field.1 →+* ℝ) → Fin P.rank → ℝ) := by
  letI : NumberField.IsTotallyReal P.field.1 := P.totallyReal
  have hsource : Module.finrank ℝ P.RealTraceSpace = P.rank * P.degree := by
    change Module.finrank ℝ
      (Fin (Module.finrank ℚ (Fin P.rank → P.field.1)) → ℝ) = _
    rw [Module.finrank_pi]
    simpa only [Fintype.card_fin] using P.traceSpace_finrank
  have htarget :
      Module.finrank ℝ ((P.field.1 →+* ℝ) → Fin P.rank → ℝ) =
        P.rank * P.degree := by
    rw [Module.finrank_pi_fintype]
    simp [card_realEmbeddings, GlobalLatticePresentation.degree, mul_comm]
  exact hsource.trans htarget.symm

/-- The product realization is an actual real-linear equivalence. -/
def realProductEmbeddingEquiv (P : GlobalLatticePresentation) :
    P.RealTraceSpace ≃ₗ[ℝ]
      ((P.field.1 →+* ℝ) → Fin P.rank → ℝ) :=
  P.realProductEmbeddingMap.linearEquivOfInjective
    P.realProductEmbeddingMap_injective P.realProductSpace_finrank

/-- Minkowski product realization of the manuscript's real scalar extension. -/
def tensorProductEmbeddingEquiv (P : GlobalLatticePresentation) :
    P.TensorRealTraceSpace ≃ₗ[ℝ]
      ((P.field.1 →+* ℝ) → Fin P.rank → ℝ) :=
  P.tensorRealTraceEquiv.trans P.realProductEmbeddingEquiv

/-- The product equivalence sends every natural pure tensor to the
simultaneous real embedding of its original vector. -/
theorem tensorProductEmbeddingEquiv_rationalPoint
    (P : GlobalLatticePresentation) (x : Fin P.rank → P.field.1) :
    P.tensorProductEmbeddingEquiv
        (TensorProduct.tmul ℚ (1 : ℝ) x) =
      P.realVectorEmbeddingMap x := by
  change P.realProductEmbeddingMap
    (P.tensorRealTraceEquiv (TensorProduct.tmul ℚ (1 : ℝ) x)) = _
  rw [P.tensorRealTraceEquiv_rationalPoint,
    P.realProductEmbeddingMap_rationalPoint]

/-- The product-space sum of local forms is the scalar-extended trace form. -/
theorem productTraceCost_tensorProductEmbeddingEquiv
    (P : GlobalLatticePresentation) (y : P.TensorRealTraceSpace) :
    P.productTraceCost (P.tensorProductEmbeddingEquiv y) =
      P.tensorRealTraceQuadraticForm y := by
  exact P.productTraceCost_realProductEmbeddingMap
    (P.tensorRealTraceEquiv y)

/-- The product image of the original integral lattice. -/
def productIntegralLattice (P : GlobalLatticePresentation) :
    Set ((P.field.1 →+* ℝ) → Fin P.rank → ℝ) :=
  Set.range (fun x : P.integralRestriction => P.realVectorEmbeddingMap x.1)

set_option maxRecDepth 2048 in
/-- The product lattice is exactly the image of the tensor lattice. -/
theorem productIntegralLattice_eq_tensorImage
    (P : GlobalLatticePresentation) :
    P.productIntegralLattice =
      P.tensorProductEmbeddingEquiv '' P.tensorIntegralLattice := by
  rw [productIntegralLattice, P.tensorIntegralLattice_eq_range]
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨TensorProduct.tmul ℚ (1 : ℝ) x.1, ⟨x, rfl⟩,
      P.tensorProductEmbeddingEquiv_rationalPoint x.1⟩
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (P.tensorProductEmbeddingEquiv_rationalPoint x.1).symm⟩

end GlobalLatticePresentation

end

end TraceEuclidean
