import TraceEuclidean.TraceRealization
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Pi

/-!
Integer coordinates for the real trace lattice.  These coordinates are
selected from an actual integer basis of the original number-field lattice.
-/

namespace TraceEuclidean

noncomputable section

namespace GlobalLatticePresentation

/-- The index set of an integer basis of the trace lattice. -/
abbrev TraceCoordinateIndex (P : GlobalLatticePresentation) :=
  Module.Free.ChooseBasisIndex ℤ P.integralRestriction

noncomputable instance (P : GlobalLatticePresentation) :
    Finite P.TraceCoordinateIndex :=
  Module.Finite.finite_basis P.rationalTraceBasis

noncomputable instance (P : GlobalLatticePresentation) :
    Fintype P.TraceCoordinateIndex :=
  Fintype.ofFinite P.TraceCoordinateIndex

/-- The number of integer coordinates is the rank times the field degree. -/
theorem traceCoordinateIndex_card (P : GlobalLatticePresentation) :
    Fintype.card P.TraceCoordinateIndex = P.rank * P.degree := by
  rw [← Module.finrank_eq_card_basis P.rationalTraceBasis]
  exact P.traceSpace_finrank

/-- Number the selected integer basis from `0` to `rank * degree - 1`. -/
def traceCoordinateIndexEquivFin (P : GlobalLatticePresentation) :
    P.TraceCoordinateIndex ≃ Fin (P.rank * P.degree) :=
  Fintype.equivFinOfCardEq P.traceCoordinateIndex_card

/-- The paper's real coordinate map, defined using a chosen integer basis. -/
def realCoordinateEquiv (P : GlobalLatticePresentation) :
    (P.TraceCoordinateIndex → ℝ) ≃ₗ[ℝ] P.RealTraceSpace :=
  P.realIntegralBasis.equivFun.symm

/-- The same coordinate isomorphism on the manuscript's `Fin (rank * degree)` index. -/
def realCoordinateEquivFin (P : GlobalLatticePresentation) :
    (Fin (P.rank * P.degree) → ℝ) ≃ₗ[ℝ] P.RealTraceSpace :=
  (LinearEquiv.piCongrLeft' ℝ (fun _ : P.TraceCoordinateIndex => ℝ)
    P.traceCoordinateIndexEquivFin).symm.trans P.realCoordinateEquiv

@[simp]
theorem realCoordinateEquivFin_apply (P : GlobalLatticePresentation)
    (u : Fin (P.rank * P.degree) → ℝ) :
    P.realCoordinateEquivFin u =
      P.realCoordinateEquiv (fun i => u (P.traceCoordinateIndexEquivFin i)) :=
  by
    simp only [realCoordinateEquivFin, LinearEquiv.trans_apply]
    congr 1
    funext i
    simp [LinearEquiv.piCongrLeft', Equiv.piCongrLeft']

/-- The coordinate map sends all integer tuples onto the real trace lattice. -/
theorem realCoordinate_int_range (P : GlobalLatticePresentation) :
    Set.range (fun z : P.TraceCoordinateIndex → ℤ =>
      P.realCoordinateEquiv (fun i => (z i : ℝ))) =
        (P.realIntegralLattice : Set P.RealTraceSpace) := by
  classical
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    refine (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨z, ?_⟩
    simp [realCoordinateEquiv, Module.Basis.equivFun_symm_apply,
      Int.cast_smul_eq_zsmul]
  · intro hx
    obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
    refine ⟨z, ?_⟩
    simpa [realCoordinateEquiv, Module.Basis.equivFun_symm_apply,
      Int.cast_smul_eq_zsmul] using hz

/-- The integer-coordinate image, using exactly `rank * degree` numbered coordinates. -/
theorem realCoordinateFin_int_range (P : GlobalLatticePresentation) :
    Set.range (fun z : Fin (P.rank * P.degree) → ℤ =>
      P.realCoordinateEquivFin (fun j => (z j : ℝ))) =
        (P.realIntegralLattice : Set P.RealTraceSpace) := by
  classical
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    change P.realCoordinateEquivFin (fun j => (z j : ℝ)) ∈
      (P.realIntegralLattice : Set P.RealTraceSpace)
    rw [P.realCoordinateEquivFin_apply, ← P.realCoordinate_int_range]
    exact ⟨fun i => z (P.traceCoordinateIndexEquivFin i), rfl⟩
  · intro hx
    rw [← P.realCoordinate_int_range] at hx
    obtain ⟨w, rfl⟩ := hx
    refine ⟨fun j => w (P.traceCoordinateIndexEquivFin.symm j), ?_⟩
    change P.realCoordinateEquivFin
        (fun j => (w (P.traceCoordinateIndexEquivFin.symm j) : ℝ)) =
      P.realCoordinateEquiv (fun i => (w i : ℝ))
    rw [P.realCoordinateEquivFin_apply]
    simp only [Equiv.symm_apply_apply]

/-- Rational coordinate tuples are exactly the embedded number-field vectors. -/
theorem realCoordinate_rat_apply (P : GlobalLatticePresentation)
    (q : P.TraceCoordinateIndex → ℚ) :
    P.realCoordinateEquiv (fun i => (q i : ℝ)) =
      P.rationalPointEmbedding (P.rationalTraceBasis.equivFun.symm q) := by
  classical
  have hb (i : P.TraceCoordinateIndex) :
      P.rationalPointEmbedding (P.rationalTraceBasis i) = P.realIntegralBasis i := by
    ext j
    simp
  simp only [realCoordinateEquiv, Module.Basis.equivFun_symm_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul, hb i]
  rfl

theorem realCoordinate_rat_range (P : GlobalLatticePresentation) :
    Set.range (fun q : P.TraceCoordinateIndex → ℚ =>
      P.realCoordinateEquiv (fun i => (q i : ℝ))) =
        Set.range P.rationalPointEmbedding := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨P.rationalTraceBasis.equivFun.symm q, (P.realCoordinate_rat_apply q).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨P.rationalTraceBasis.equivFun y, ?_⟩
    simpa only [LinearEquiv.symm_apply_apply] using
      P.realCoordinate_rat_apply (P.rationalTraceBasis.equivFun y)

/-- The rational-coordinate image, using exactly `rank * degree` coordinates. -/
theorem realCoordinateFin_rat_range (P : GlobalLatticePresentation) :
    Set.range (fun q : Fin (P.rank * P.degree) → ℚ =>
      P.realCoordinateEquivFin (fun j => (q j : ℝ))) =
        Set.range P.rationalPointEmbedding := by
  classical
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    change P.realCoordinateEquivFin (fun j => (q j : ℝ)) ∈
      Set.range P.rationalPointEmbedding
    rw [P.realCoordinateEquivFin_apply, ← P.realCoordinate_rat_range]
    exact ⟨fun i => q (P.traceCoordinateIndexEquivFin i), rfl⟩
  · intro hx
    rw [← P.realCoordinate_rat_range] at hx
    obtain ⟨q, rfl⟩ := hx
    refine ⟨fun j => q (P.traceCoordinateIndexEquivFin.symm j), ?_⟩
    change P.realCoordinateEquivFin
        (fun j => (q (P.traceCoordinateIndexEquivFin.symm j) : ℝ)) =
      P.realCoordinateEquiv (fun i => (q i : ℝ))
    rw [P.realCoordinateEquivFin_apply]
    simp only [Equiv.symm_apply_apply]

/-- The trace quadratic form expressed in real coordinates. -/
def realCoordinateForm (P : GlobalLatticePresentation) :
    QuadraticForm ℝ (P.TraceCoordinateIndex → ℝ) :=
  P.realTraceQuadraticForm.comp P.realCoordinateEquiv.toLinearMap

/-- The same trace form on `rank * degree` explicitly numbered coordinates. -/
def realCoordinateFormFin (P : GlobalLatticePresentation) :
    QuadraticForm ℝ (Fin (P.rank * P.degree) → ℝ) :=
  P.realTraceQuadraticForm.comp P.realCoordinateEquivFin.toLinearMap

/-- The coordinate trace form is positive definite. -/
theorem realCoordinateForm_posDef (P : GlobalLatticePresentation) :
    P.realCoordinateForm.PosDef := by
  intro x hx
  change 0 < P.realTraceQuadraticForm (P.realCoordinateEquiv x)
  apply P.realTraceQuadraticForm_posDef
  intro hzero
  apply hx
  exact P.realCoordinateEquiv.injective (by simpa using hzero)

theorem realCoordinateFormFin_posDef (P : GlobalLatticePresentation) :
    P.realCoordinateFormFin.PosDef := by
  intro x hx
  change 0 < P.realTraceQuadraticForm (P.realCoordinateEquivFin x)
  apply P.realTraceQuadraticForm_posDef
  intro hzero
  apply hx
  apply P.realCoordinateEquivFin.injective
  simpa only [map_zero] using hzero

/-- On rational coordinates, the new real form is exactly the field trace. -/
theorem realCoordinateForm_rat_apply (P : GlobalLatticePresentation)
    (q : P.TraceCoordinateIndex → ℚ) :
    P.realCoordinateForm (fun i => (q i : ℝ)) =
      (P.traceQuadraticForm (P.rationalTraceBasis.equivFun.symm q) : ℝ) := by
  change P.realTraceQuadraticForm
      (P.realCoordinateEquiv (fun i => (q i : ℝ))) = _
  rw [P.realCoordinate_rat_apply]
  exact P.realTraceQuadraticForm_rationalPointEmbedding _

/-- The numbered-coordinate form agrees with the field trace on rational tuples. -/
theorem realCoordinateFormFin_rat_apply (P : GlobalLatticePresentation)
    (q : Fin (P.rank * P.degree) → ℚ) :
    P.realCoordinateFormFin (fun j => (q j : ℝ)) =
      (P.traceQuadraticForm
        (P.rationalTraceBasis.equivFun.symm
          (fun i => q (P.traceCoordinateIndexEquivFin i))) : ℝ) := by
  simpa [realCoordinateFormFin, realCoordinateForm,
    P.realCoordinateEquivFin_apply] using
      P.realCoordinateForm_rat_apply
        (fun i => q (P.traceCoordinateIndexEquivFin i))

/-- Integer coordinate tuples come from the original integer lattice. -/
theorem rationalCoordinate_int_mem (P : GlobalLatticePresentation)
    (z : P.TraceCoordinateIndex → ℤ) :
    P.rationalTraceBasis.equivFun.symm (fun i => (z i : ℚ)) ∈
      P.integralRestriction := by
  classical
  rw [Module.Basis.equivFun_symm_apply]
  apply P.integralRestriction.sum_mem
  intro i _hi
  rw [P.rationalTraceBasis_apply, Int.cast_smul_eq_zsmul]
  exact P.integralRestriction.smul_mem (z i) (P.integralRestrictionBasis i).2

/-- The positive definite real coordinate form takes integer values on integer tuples. -/
theorem realCoordinateForm_int (P : GlobalLatticePresentation)
    (z : P.TraceCoordinateIndex → ℤ) :
    ∃ n : ℤ, P.realCoordinateForm (fun i => (z i : ℝ)) = (n : ℝ) := by
  let q : P.TraceCoordinateIndex → ℚ := fun i => (z i : ℚ)
  let y : Fin P.rank → P.field.1 := P.rationalTraceBasis.equivFun.symm q
  have hy : y ∈ P.integralRestriction := P.rationalCoordinate_int_mem z
  have hyL : y ∈ P.L := (P.mem_integralRestriction_iff y).mp hy
  have htrace : IsIntegral ℤ (Algebra.trace ℚ P.field.1 (P.Q y)) :=
    Algebra.isIntegral_trace (P.integral ⟨y, hyL⟩)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp htrace
  refine ⟨n, ?_⟩
  calc
    P.realCoordinateForm (fun i => (z i : ℝ)) =
        (P.traceQuadraticForm y : ℝ) := by
          simpa [q, y] using P.realCoordinateForm_rat_apply q
    _ = ((Algebra.trace ℚ P.field.1 (P.Q y) : ℚ) : ℝ) := rfl
    _ = (n : ℝ) := by exact_mod_cast hn.symm

/-- The numbered-coordinate form takes integer values on every integer tuple. -/
theorem realCoordinateFormFin_int (P : GlobalLatticePresentation)
    (z : Fin (P.rank * P.degree) → ℤ) :
    ∃ n : ℤ, P.realCoordinateFormFin (fun j => (z j : ℝ)) = (n : ℝ) := by
  obtain ⟨n, hn⟩ := P.realCoordinateForm_int
    (fun i => z (P.traceCoordinateIndexEquivFin i))
  refine ⟨n, ?_⟩
  simpa [realCoordinateFormFin, realCoordinateForm,
    P.realCoordinateEquivFin_apply] using hn

/-- The nearest-lattice-value function in the real trace space. -/
def realTraceNearestValue (P : GlobalLatticePresentation)
    (x : P.RealTraceSpace) : ℝ :=
  sInf (Set.range fun y : P.realIntegralLattice =>
    P.realTraceQuadraticForm (x - y.1))

/-- The set in the nearest-value definition is nonempty and bounded below. -/
theorem realTraceNearestValue_domain (P : GlobalLatticePresentation)
    (x : P.RealTraceSpace) :
    (Set.range fun y : P.realIntegralLattice =>
      P.realTraceQuadraticForm (x - y.1)).Nonempty ∧
      BddBelow (Set.range fun y : P.realIntegralLattice =>
        P.realTraceQuadraticForm (x - y.1)) := by
  constructor
  · exact ⟨_, ⟨0, rfl⟩⟩
  · refine ⟨0, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact P.realTraceQuadraticForm_posDef.nonneg _

/-- The nearest-lattice-value formula in integer basis coordinates. -/
theorem realTraceNearestValue_coordinates (P : GlobalLatticePresentation)
    (u : P.TraceCoordinateIndex → ℝ) :
    P.realTraceNearestValue (P.realCoordinateEquiv u) =
      sInf (Set.range fun z : P.TraceCoordinateIndex → ℤ =>
        P.realCoordinateForm (u - fun i => (z i : ℝ))) := by
  unfold realTraceNearestValue
  congr 1
  ext a
  constructor
  · rintro ⟨y, rfl⟩
    have hy : (y : P.RealTraceSpace) ∈
        (P.realIntegralLattice : Set P.RealTraceSpace) := y.2
    rw [← P.realCoordinate_int_range] at hy
    obtain ⟨z, hz⟩ := hy
    refine ⟨z, ?_⟩
    simp [realCoordinateForm, map_sub, hz]
  · rintro ⟨z, rfl⟩
    have hz : P.realCoordinateEquiv (fun i => (z i : ℝ)) ∈
        P.realIntegralLattice := by
      change P.realCoordinateEquiv (fun i => (z i : ℝ)) ∈
        (P.realIntegralLattice : Set P.RealTraceSpace)
      rw [← P.realCoordinate_int_range]
      exact ⟨z, rfl⟩
    refine ⟨⟨P.realCoordinateEquiv (fun i => (z i : ℝ)), hz⟩, ?_⟩
    simp [realCoordinateForm, map_sub]

/-- The nearest-lattice formula on exactly `rank * degree` real coordinates. -/
theorem realTraceNearestValue_fin_coordinates (P : GlobalLatticePresentation)
    (u : Fin (P.rank * P.degree) → ℝ) :
    P.realTraceNearestValue (P.realCoordinateEquivFin u) =
      sInf (Set.range fun z : Fin (P.rank * P.degree) → ℤ =>
        P.realCoordinateFormFin (u - fun j => (z j : ℝ))) := by
  unfold realTraceNearestValue
  congr 1
  ext a
  constructor
  · rintro ⟨y, rfl⟩
    have hy : (y : P.RealTraceSpace) ∈
        (P.realIntegralLattice : Set P.RealTraceSpace) := y.2
    rw [← P.realCoordinateFin_int_range] at hy
    obtain ⟨z, hz⟩ := hy
    refine ⟨z, ?_⟩
    simp [realCoordinateFormFin, map_sub, hz]
  · rintro ⟨z, rfl⟩
    have hz : P.realCoordinateEquivFin (fun j => (z j : ℝ)) ∈
        P.realIntegralLattice := by
      change P.realCoordinateEquivFin (fun j => (z j : ℝ)) ∈
        (P.realIntegralLattice : Set P.RealTraceSpace)
      rw [← P.realCoordinateFin_int_range]
      exact ⟨z, rfl⟩
    refine ⟨⟨P.realCoordinateEquivFin (fun j => (z j : ℝ)), hz⟩, ?_⟩
    simp [realCoordinateFormFin, map_sub]

end GlobalLatticePresentation

end

end TraceEuclidean
