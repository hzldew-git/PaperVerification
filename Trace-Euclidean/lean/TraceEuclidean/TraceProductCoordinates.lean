import TraceEuclidean.TraceProductRealization

/-!
The manuscript's coordinate proposition on the product of real embedding
spaces, using the real-linear equivalence from the scalar extension.
-/

namespace TraceEuclidean

noncomputable section

set_option maxRecDepth 2048

namespace GlobalLatticePresentation

/-- The sum of local forms as a quadratic form on the product space. -/
def productTraceQuadraticForm (P : GlobalLatticePresentation) :
    QuadraticForm ℝ ((P.field.1 →+* ℝ) → Fin P.rank → ℝ) :=
  P.tensorRealTraceQuadraticForm.comp
    P.tensorProductEmbeddingEquiv.symm.toLinearMap

theorem productTraceQuadraticForm_apply (P : GlobalLatticePresentation)
    (z : (P.field.1 →+* ℝ) → Fin P.rank → ℝ) :
    P.productTraceQuadraticForm z = P.productTraceCost z := by
  change P.tensorRealTraceQuadraticForm
    (P.tensorProductEmbeddingEquiv.symm z) = P.productTraceCost z
  rw [← P.productTraceCost_tensorProductEmbeddingEquiv
    (P.tensorProductEmbeddingEquiv.symm z),
    LinearEquiv.apply_symm_apply]

/-- The associated product bilinear form restricts to the trace of the
original bilinear form on rational vectors. -/
theorem productTraceQuadraticForm_associated_rationalPoint
    (P : GlobalLatticePresentation) (x y : Fin P.rank → P.field.1) :
    QuadraticMap.associated P.productTraceQuadraticForm
        (P.realVectorEmbeddingMap x) (P.realVectorEmbeddingMap y) =
      ((Algebra.trace ℚ P.field.1
        (QuadraticMap.associated P.Q x y) : ℚ) : ℝ) := by
  rw [← P.traceQuadraticForm_associated x y]
  simp only [QuadraticMap.associated_apply, Module.End.smul_def,
    QuadraticMap.half_moduleEnd_apply_eq_half_smul, invOf_eq_inv,
    smul_eq_mul]
  rw [← P.realVectorEmbeddingMap.map_add x y]
  simp only [P.productTraceQuadraticForm_apply,
    P.productTraceCost_rationalPoint]
  norm_num

theorem productTraceQuadraticForm_posDef (P : GlobalLatticePresentation) :
    P.productTraceQuadraticForm.PosDef := by
  intro z hz
  change 0 < P.tensorRealTraceQuadraticForm
    (P.tensorProductEmbeddingEquiv.symm z)
  apply P.tensorRealTraceQuadraticForm_posDef
  intro hzero
  apply hz
  simpa using congrArg P.tensorProductEmbeddingEquiv hzero

/-- Numbered coordinates on the product of real embedding spaces. -/
def productCoordinateEquivFin (P : GlobalLatticePresentation) :
    (Fin (P.rank * P.degree) → ℝ) ≃ₗ[ℝ]
      ((P.field.1 →+* ℝ) → Fin P.rank → ℝ) :=
  P.tensorCoordinateEquivFin.trans P.tensorProductEmbeddingEquiv

theorem productCoordinateFin_int_range (P : GlobalLatticePresentation) :
    Set.range (fun m : Fin (P.rank * P.degree) → ℤ =>
      P.productCoordinateEquivFin (fun j => (m j : ℝ))) =
        P.productIntegralLattice := by
  rw [P.productIntegralLattice_eq_tensorImage,
    ← P.tensorCoordinateFin_int_range]
  ext z
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨P.tensorCoordinateEquivFin (fun j => (m j : ℝ)),
      ⟨m, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨m, rfl⟩, rfl⟩
    exact ⟨m, rfl⟩

theorem productCoordinateFin_rat_range (P : GlobalLatticePresentation) :
    Set.range (fun q : Fin (P.rank * P.degree) → ℚ =>
      P.productCoordinateEquivFin (fun j => (q j : ℝ))) =
        Set.range P.realVectorEmbeddingMap := by
  ext z
  constructor
  · rintro ⟨q, rfl⟩
    have h : P.tensorCoordinateEquivFin (fun j => (q j : ℝ)) ∈
        Set.range (fun x : Fin P.rank → P.field.1 =>
          TensorProduct.tmul ℚ (1 : ℝ) x) := by
      rw [← P.tensorCoordinateFin_rat_range]
      exact ⟨q, rfl⟩
    obtain ⟨x, hx⟩ := h
    refine ⟨x, ?_⟩
    calc
      P.realVectorEmbeddingMap x =
          P.tensorProductEmbeddingEquiv (TensorProduct.tmul ℚ (1 : ℝ) x) :=
        (P.tensorProductEmbeddingEquiv_rationalPoint x).symm
      _ = P.tensorProductEmbeddingEquiv
          (P.tensorCoordinateEquivFin (fun j => (q j : ℝ))) :=
        congrArg P.tensorProductEmbeddingEquiv hx
      _ = P.productCoordinateEquivFin (fun j => (q j : ℝ)) := rfl
  · rintro ⟨x, rfl⟩
    have h : TensorProduct.tmul ℚ (1 : ℝ) x ∈
        Set.range (fun q : Fin (P.rank * P.degree) → ℚ =>
          P.tensorCoordinateEquivFin (fun j => (q j : ℝ))) := by
      rw [P.tensorCoordinateFin_rat_range]
      exact ⟨x, rfl⟩
    obtain ⟨q, hq⟩ := h
    refine ⟨q, ?_⟩
    calc
      P.productCoordinateEquivFin (fun j => (q j : ℝ)) =
          P.tensorProductEmbeddingEquiv
            (P.tensorCoordinateEquivFin (fun j => (q j : ℝ))) := rfl
      _ = P.tensorProductEmbeddingEquiv
          (TensorProduct.tmul ℚ (1 : ℝ) x) :=
        congrArg P.tensorProductEmbeddingEquiv hq
      _ = P.realVectorEmbeddingMap x :=
        P.tensorProductEmbeddingEquiv_rationalPoint x

/-- The integral positive definite coordinate form of the manuscript. -/
def productCoordinateFormFin (P : GlobalLatticePresentation) :
    QuadraticForm ℝ (Fin (P.rank * P.degree) → ℝ) :=
  P.productTraceQuadraticForm.comp P.productCoordinateEquivFin.toLinearMap

theorem productCoordinateFormFin_def (P : GlobalLatticePresentation)
    (u : Fin (P.rank * P.degree) → ℝ) :
    P.productCoordinateFormFin u =
      P.productTraceQuadraticForm (P.productCoordinateEquivFin u) := rfl

theorem productCoordinateFormFin_apply (P : GlobalLatticePresentation)
    (u : Fin (P.rank * P.degree) → ℝ) :
    P.productCoordinateFormFin u = P.tensorCoordinateFormFin u := by
  rw [productCoordinateFormFin, QuadraticMap.comp_apply,
    P.productTraceQuadraticForm_apply]
  exact P.productTraceCost_tensorProductEmbeddingEquiv
    (P.tensorCoordinateEquivFin u)

theorem productCoordinateFormFin_posDef (P : GlobalLatticePresentation) :
    P.productCoordinateFormFin.PosDef := by
  intro u hu
  rw [P.productCoordinateFormFin_apply]
  exact P.tensorCoordinateFormFin_posDef u hu

theorem productCoordinateFormFin_int (P : GlobalLatticePresentation)
    (m : Fin (P.rank * P.degree) → ℤ) :
    ∃ n : ℤ, P.productCoordinateFormFin (fun j => (m j : ℝ)) = (n : ℝ) := by
  simpa only [P.productCoordinateFormFin_apply] using
    P.tensorCoordinateFormFin_int m

/-- Nearest-lattice value in the manuscript's product model. -/
def productTraceNearestValue (P : GlobalLatticePresentation)
    (z : (P.field.1 →+* ℝ) → Fin P.rank → ℝ) : ℝ :=
  sInf (Set.range fun w : P.productIntegralLattice =>
    P.productTraceQuadraticForm (z - w.1))

theorem productTraceNearestValue_domain (P : GlobalLatticePresentation)
    (z : (P.field.1 →+* ℝ) → Fin P.rank → ℝ) :
    (Set.range fun w : P.productIntegralLattice =>
      P.productTraceQuadraticForm (z - w.1)).Nonempty ∧
    BddBelow (Set.range fun w : P.productIntegralLattice =>
      P.productTraceQuadraticForm (z - w.1)) := by
  have hzero : (0 : (P.field.1 →+* ℝ) → Fin P.rank → ℝ) ∈
      P.productIntegralLattice := by
    change 0 ∈ Set.range
      (fun x : P.integralRestriction => P.realVectorEmbeddingMap x.1)
    exact ⟨0, by simp⟩
  constructor
  · exact ⟨_, ⟨⟨0, hzero⟩, rfl⟩⟩
  · refine ⟨0, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact P.productTraceQuadraticForm_posDef.nonneg _

/-- The nearest-lattice formula in numbered real coordinates. -/
theorem productTraceNearestValue_fin_coordinates
    (P : GlobalLatticePresentation)
    (u : Fin (P.rank * P.degree) → ℝ) :
    P.productTraceNearestValue (P.productCoordinateEquivFin u) =
      sInf (Set.range fun m : Fin (P.rank * P.degree) → ℤ =>
        P.productCoordinateFormFin (u - fun j => (m j : ℝ))) := by
  unfold productTraceNearestValue
  congr 1
  ext a
  constructor
  · rintro ⟨w, rfl⟩
    have hw : (w : (P.field.1 →+* ℝ) → Fin P.rank → ℝ) ∈
        Set.range (fun m : Fin (P.rank * P.degree) → ℤ =>
          P.productCoordinateEquivFin (fun j => (m j : ℝ))) := by
      rw [P.productCoordinateFin_int_range]
      exact w.2
    obtain ⟨m, hm⟩ := hw
    refine ⟨m, ?_⟩
    have hsub : P.productCoordinateEquivFin u - w.1 =
        P.productCoordinateEquivFin
          (u - fun j => (m j : ℝ)) := by
      rw [← hm]
      exact (P.productCoordinateEquivFin.map_sub u
        (fun j => (m j : ℝ))).symm
    change P.productCoordinateFormFin (u - fun j => (m j : ℝ)) =
      P.productTraceQuadraticForm (P.productCoordinateEquivFin u - w.1)
    rw [P.productCoordinateFormFin_def]
    exact congrArg P.productTraceQuadraticForm hsub.symm

  · rintro ⟨m, rfl⟩
    have hm : P.productCoordinateEquivFin (fun j => (m j : ℝ)) ∈
        P.productIntegralLattice := by
      rw [← P.productCoordinateFin_int_range]
      exact ⟨m, rfl⟩
    let w : P.productIntegralLattice :=
      ⟨P.productCoordinateEquivFin (fun j => (m j : ℝ)), hm⟩
    refine ⟨w, ?_⟩
    have hsub : P.productCoordinateEquivFin
        (u - fun j => (m j : ℝ)) =
        P.productCoordinateEquivFin u - w.1 := by
      change P.productCoordinateEquivFin
        (u - fun j => (m j : ℝ)) =
          P.productCoordinateEquivFin u -
            P.productCoordinateEquivFin (fun j => (m j : ℝ))
      exact P.productCoordinateEquivFin.map_sub u
        (fun j => (m j : ℝ))
    change P.productTraceQuadraticForm (P.productCoordinateEquivFin u - w.1) =
      P.productCoordinateFormFin (u - fun j => (m j : ℝ))
    rw [P.productCoordinateFormFin_def]
    exact congrArg P.productTraceQuadraticForm hsub.symm

/-- Nearest-lattice trace value on the original rational quadratic space. -/
def rationalTraceNearestValue (P : GlobalLatticePresentation)
    (x : Fin P.rank → P.field.1) : ℝ :=
  sInf (Set.range fun y : P.integralRestriction =>
    (P.traceQuadraticForm (x - y.1) : ℝ))

/-- The real nearest-lattice value agrees with the rational trace value on
embedded rational points. -/
theorem productTraceNearestValue_rationalPoint
    (P : GlobalLatticePresentation) (x : Fin P.rank → P.field.1) :
    P.productTraceNearestValue (P.realVectorEmbeddingMap x) =
      P.rationalTraceNearestValue x := by
  unfold productTraceNearestValue rationalTraceNearestValue
  congr 1
  ext a
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨y, hy⟩ : w.1 ∈
        Set.range (fun y : P.integralRestriction =>
          P.realVectorEmbeddingMap y.1) := w.2
    refine ⟨y, ?_⟩
    change (P.traceQuadraticForm (x - y.1) : ℝ) =
      P.productTraceQuadraticForm
        (P.realVectorEmbeddingMap x - w.1)
    rw [← hy, ← P.realVectorEmbeddingMap.map_sub,
      P.productTraceQuadraticForm_apply,
      P.productTraceCost_rationalPoint]
  · rintro ⟨y, rfl⟩
    let w : P.productIntegralLattice :=
      ⟨P.realVectorEmbeddingMap y.1, ⟨y, rfl⟩⟩
    refine ⟨w, ?_⟩
    change P.productTraceQuadraticForm
        (P.realVectorEmbeddingMap x - P.realVectorEmbeddingMap y.1) =
      (P.traceQuadraticForm (x - y.1) : ℝ)
    rw [← P.realVectorEmbeddingMap.map_sub,
      P.productTraceQuadraticForm_apply,
      P.productTraceCost_rationalPoint]

/-- A rational maximizer of the numbered covering function gives a maximizer
on the original rational vectors. The rational-attainment premise is the
separate geometric input used in the manuscript. -/
theorem productTraceNearestValue_max_of_rational_coordinate_max
    (P : GlobalLatticePresentation)
    (q : Fin (P.rank * P.degree) → ℚ)
    (hmax : ∀ u : Fin (P.rank * P.degree) → ℝ,
      P.productTraceNearestValue (P.productCoordinateEquivFin u) ≤
        P.productTraceNearestValue
          (P.productCoordinateEquivFin (fun j => (q j : ℝ)))) :
    ∃ x : Fin P.rank → P.field.1,
      ∀ z : (P.field.1 →+* ℝ) → Fin P.rank → ℝ,
        P.productTraceNearestValue z ≤
          P.productTraceNearestValue (P.realVectorEmbeddingMap x) := by
  have hq : P.productCoordinateEquivFin (fun j => (q j : ℝ)) ∈
      Set.range P.realVectorEmbeddingMap := by
    rw [← P.productCoordinateFin_rat_range]
    exact ⟨q, rfl⟩
  obtain ⟨x, hx⟩ := hq
  refine ⟨x, ?_⟩
  intro z
  have hz := hmax (P.productCoordinateEquivFin.symm z)
  simpa only [LinearEquiv.apply_symm_apply, ← hx] using hz

/-- Under the rational-attainment input, the original rational trace
nearest-value function also has a global maximum. -/
theorem rationalTraceNearestValue_max_of_rational_coordinate_max
    (P : GlobalLatticePresentation)
    (q : Fin (P.rank * P.degree) → ℚ)
    (hmax : ∀ u : Fin (P.rank * P.degree) → ℝ,
      P.productTraceNearestValue (P.productCoordinateEquivFin u) ≤
        P.productTraceNearestValue
          (P.productCoordinateEquivFin (fun j => (q j : ℝ)))) :
    ∃ x : Fin P.rank → P.field.1,
      ∀ y : Fin P.rank → P.field.1,
        P.rationalTraceNearestValue y ≤ P.rationalTraceNearestValue x := by
  obtain ⟨x, hx⟩ :=
    P.productTraceNearestValue_max_of_rational_coordinate_max q hmax
  refine ⟨x, ?_⟩
  intro y
  simpa only [P.productTraceNearestValue_rationalPoint] using
    hx (P.realVectorEmbeddingMap y)

end GlobalLatticePresentation

end

end TraceEuclidean
