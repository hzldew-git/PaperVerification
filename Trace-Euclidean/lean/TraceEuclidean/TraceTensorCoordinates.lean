import TraceEuclidean.TraceCoordinates
import TraceEuclidean.TraceTensorRealization

/-!
Coordinate form of the trace-lattice proposition directly on the real scalar
extension of the original rational vector space.
-/

namespace TraceEuclidean

noncomputable section

namespace GlobalLatticePresentation

/-- The natural tensor images of integral vectors are precisely the real
trace lattice in the diagonal model. -/
theorem realIntegralLattice_eq_rational_range
    (P : GlobalLatticePresentation) :
    (P.realIntegralLattice : Set P.RealTraceSpace) =
      Set.range (fun x : P.integralRestriction =>
        P.rationalPointEmbedding x.1) := by
  classical
  ext y
  constructor
  · intro hy
    rw [← P.realCoordinate_int_range] at hy
    obtain ⟨z, rfl⟩ := hy
    let x : Fin P.rank → P.field.1 :=
      P.rationalTraceBasis.equivFun.symm (fun i => (z i : ℚ))
    refine ⟨⟨x, P.rationalCoordinate_int_mem z⟩, ?_⟩
    exact (P.realCoordinate_rat_apply (fun i => (z i : ℚ))).symm
  · rintro ⟨x, rfl⟩
    exact P.rationalPointEmbedding_mem_realIntegralLattice x.1 x.2

/-- The integral lattice in the real scalar extension. -/
def tensorIntegralLattice (P : GlobalLatticePresentation) :
    Set P.TensorRealTraceSpace :=
  P.tensorRealTraceEquiv.symm '' (P.realIntegralLattice : Set P.RealTraceSpace)

/-- The tensor lattice is exactly the natural image of the original lattice. -/
theorem tensorIntegralLattice_eq_range (P : GlobalLatticePresentation) :
    P.tensorIntegralLattice =
      Set.range (fun x : P.integralRestriction =>
        TensorProduct.tmul ℚ (1 : ℝ) x.1) := by
  classical
  rw [tensorIntegralLattice, P.realIntegralLattice_eq_rational_range]
  ext y
  constructor
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    refine ⟨x, ?_⟩
    simpa using congrArg P.tensorRealTraceEquiv.symm
      (P.tensorRealTraceEquiv_rationalPoint x.1)
  · rintro ⟨x, rfl⟩
    refine ⟨P.rationalPointEmbedding x.1, ⟨x, rfl⟩, ?_⟩
    simpa using (congrArg P.tensorRealTraceEquiv.symm
      (P.tensorRealTraceEquiv_rationalPoint x.1)).symm

/-- Integer coordinates of the selected basis, now valued in the real
scalar extension. -/
def tensorCoordinateEquivFin (P : GlobalLatticePresentation) :
    (Fin (P.rank * P.degree) → ℝ) ≃ₗ[ℝ] P.TensorRealTraceSpace :=
  P.realCoordinateEquivFin.trans P.tensorRealTraceEquiv.symm

theorem tensorCoordinateFin_int_range (P : GlobalLatticePresentation) :
    Set.range (fun z : Fin (P.rank * P.degree) → ℤ =>
      P.tensorCoordinateEquivFin (fun j => (z j : ℝ))) =
        P.tensorIntegralLattice := by
  classical
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨P.realCoordinateEquivFin (fun j => (z j : ℝ)), ?_, rfl⟩
    rw [← P.realCoordinateFin_int_range]
    exact ⟨z, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rw [← P.realCoordinateFin_int_range] at hy
    obtain ⟨z, rfl⟩ := hy
    exact ⟨z, rfl⟩

theorem tensorCoordinateFin_rat_range (P : GlobalLatticePresentation) :
    Set.range (fun q : Fin (P.rank * P.degree) → ℚ =>
      P.tensorCoordinateEquivFin (fun j => (q j : ℝ))) =
        Set.range (fun x : Fin P.rank → P.field.1 =>
          TensorProduct.tmul ℚ (1 : ℝ) x) := by
  classical
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    have h : P.realCoordinateEquivFin (fun j => (q j : ℝ)) ∈
        Set.range P.rationalPointEmbedding := by
      rw [← P.realCoordinateFin_rat_range]
      exact ⟨q, rfl⟩
    obtain ⟨y, hy⟩ := h
    refine ⟨y, ?_⟩
    rw [← P.tensorRealTraceEquiv_rationalPoint] at hy
    change TensorProduct.tmul ℚ (1 : ℝ) y =
      P.tensorRealTraceEquiv.symm
        (P.realCoordinateEquivFin (fun j => (q j : ℝ)))
    simpa using congrArg P.tensorRealTraceEquiv.symm hy
  · rintro ⟨y, rfl⟩
    have h : P.rationalPointEmbedding y ∈
        Set.range (fun q : Fin (P.rank * P.degree) → ℚ =>
          P.realCoordinateEquivFin (fun j => (q j : ℝ))) := by
      rw [P.realCoordinateFin_rat_range]
      exact ⟨y, rfl⟩
    obtain ⟨q, hq⟩ := h
    refine ⟨q, ?_⟩
    rw [← P.tensorRealTraceEquiv_rationalPoint] at hq
    simp [tensorCoordinateEquivFin, hq]

/-- The trace form on numbered coordinates of the scalar extension. -/
def tensorCoordinateFormFin (P : GlobalLatticePresentation) :
    QuadraticForm ℝ (Fin (P.rank * P.degree) → ℝ) :=
  P.tensorRealTraceQuadraticForm.comp P.tensorCoordinateEquivFin.toLinearMap

theorem tensorCoordinateFormFin_apply (P : GlobalLatticePresentation)
    (u : Fin (P.rank * P.degree) → ℝ) :
    P.tensorCoordinateFormFin u = P.realCoordinateFormFin u := by
  simp [tensorCoordinateFormFin, tensorRealTraceQuadraticForm,
    tensorCoordinateEquivFin, realCoordinateFormFin]

theorem tensorCoordinateFormFin_posDef (P : GlobalLatticePresentation) :
    P.tensorCoordinateFormFin.PosDef := by
  intro u hu
  rw [P.tensorCoordinateFormFin_apply]
  exact P.realCoordinateFormFin_posDef u hu

theorem tensorCoordinateFormFin_int (P : GlobalLatticePresentation)
    (z : Fin (P.rank * P.degree) → ℤ) :
    ∃ n : ℤ, P.tensorCoordinateFormFin (fun j => (z j : ℝ)) = (n : ℝ) := by
  simpa only [P.tensorCoordinateFormFin_apply] using P.realCoordinateFormFin_int z

/-- The nearest-lattice value defined directly in the scalar extension. -/
def tensorTraceNearestValue (P : GlobalLatticePresentation)
    (x : P.TensorRealTraceSpace) : ℝ :=
  sInf (Set.range fun y : P.tensorIntegralLattice =>
    P.tensorRealTraceQuadraticForm (x - y.1))

theorem tensorTraceNearestValue_domain (P : GlobalLatticePresentation)
    (x : P.TensorRealTraceSpace) :
    (Set.range fun y : P.tensorIntegralLattice =>
      P.tensorRealTraceQuadraticForm (x - y.1)).Nonempty ∧
    BddBelow (Set.range fun y : P.tensorIntegralLattice =>
      P.tensorRealTraceQuadraticForm (x - y.1)) := by
  have hzero : (0 : P.TensorRealTraceSpace) ∈ P.tensorIntegralLattice := by
    exact ⟨0, P.realIntegralLattice.zero_mem, by simp⟩
  constructor
  · exact ⟨_, ⟨⟨0, hzero⟩, rfl⟩⟩
  · refine ⟨0, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact P.tensorRealTraceQuadraticForm_posDef.nonneg _

theorem tensorTraceNearestValue_eq_real (P : GlobalLatticePresentation)
    (x : P.TensorRealTraceSpace) :
    P.tensorTraceNearestValue x =
      P.realTraceNearestValue (P.tensorRealTraceEquiv x) := by
  unfold tensorTraceNearestValue realTraceNearestValue
  congr 1
  ext a
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, hz, hy⟩ := y.2
    refine ⟨⟨z, hz⟩, ?_⟩
    have hyez : P.tensorRealTraceEquiv (y : P.TensorRealTraceSpace) = z := by
      rw [← hy]
      simp
    simp [tensorRealTraceQuadraticForm, map_sub, hyez]
  · rintro ⟨z, rfl⟩
    let y : P.tensorIntegralLattice :=
      ⟨P.tensorRealTraceEquiv.symm z.1, ⟨z.1, z.2, rfl⟩⟩
    refine ⟨y, ?_⟩
    simp [tensorRealTraceQuadraticForm, map_sub, y]

/-- Proposition's nearest-lattice infimum formula on the actual real scalar
extension, with `rank * degree` integer coordinates. -/
theorem tensorTraceNearestValue_fin_coordinates
    (P : GlobalLatticePresentation)
    (u : Fin (P.rank * P.degree) → ℝ) :
    P.tensorTraceNearestValue (P.tensorCoordinateEquivFin u) =
      sInf (Set.range fun z : Fin (P.rank * P.degree) → ℤ =>
        P.tensorCoordinateFormFin (u - fun j => (z j : ℝ))) := by
  rw [P.tensorTraceNearestValue_eq_real]
  have h : P.tensorRealTraceEquiv (P.tensorCoordinateEquivFin u) =
      P.realCoordinateEquivFin u := by
    simp [tensorCoordinateEquivFin]
  rw [h, P.realTraceNearestValue_fin_coordinates]
  simp only [P.tensorCoordinateFormFin_apply]

end GlobalLatticePresentation

end

end TraceEuclidean
