import TraceEuclidean.TraceRealization
import TraceEuclidean.CoveringVolume
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
Euclidean realization and covering consequences of strict trace-Euclideanity.
The positive diagonal trace form is converted exactly to the standard
Euclidean norm by multiplying each coordinate by the square root of its
positive weight.
-/

namespace TraceEuclidean

noncomputable section

open Set Filter Topology
open scoped Pointwise
open scoped InnerProductSpace

namespace GlobalLatticePresentation

/-- The standard Euclidean space underlying the trace form. -/
abbrev EuclideanTraceSpace (P : GlobalLatticePresentation) :=
  EuclideanSpace ℝ P.TraceDimensionIndex

/-- The positive square root of a diagonal trace weight, bundled as a unit. -/
def traceWeightRootUnit (P : GlobalLatticePresentation)
    (i : P.TraceDimensionIndex) : ℝˣ :=
  Units.mk0 (Real.sqrt (P.traceDiagonalWeights i : ℝ))
    (Real.sqrt_ne_zero'.2 (by
      exact_mod_cast P.traceDiagonalWeights_pos i))

@[simp]
theorem traceWeightRootUnit_coe (P : GlobalLatticePresentation)
    (i : P.TraceDimensionIndex) :
    (P.traceWeightRootUnit i : ℝ) =
      Real.sqrt (P.traceDiagonalWeights i : ℝ) :=
  rfl

/-- Coordinate scaling that turns the trace form into a Euclidean norm. -/
def euclideanTraceScalingEquiv (P : GlobalLatticePresentation) :
    P.RealTraceSpace ≃ₗ[ℝ] P.EuclideanTraceSpace :=
  (LinearEquiv.piCongrRight fun i ↦
      (P.traceWeightRootUnit i).mulLeftLinearEquiv ℝ ℝ).trans
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : P.TraceDimensionIndex ↦ ℝ)).symm.toLinearEquiv

@[simp]
theorem euclideanTraceScalingEquiv_apply
    (P : GlobalLatticePresentation) (x : P.RealTraceSpace)
    (i : P.TraceDimensionIndex) :
    P.euclideanTraceScalingEquiv x i =
      Real.sqrt (P.traceDiagonalWeights i : ℝ) * x i :=
  rfl

/-- The scaled Euclidean norm squared is exactly the real trace form. -/
theorem euclideanTraceScalingEquiv_norm_sq
    (P : GlobalLatticePresentation) (x : P.RealTraceSpace) :
    ‖P.euclideanTraceScalingEquiv x‖ ^ (2 : ℕ) =
      P.realTraceQuadraticForm x := by
  classical
  rw [EuclideanSpace.real_norm_sq_eq,
    P.realTraceQuadraticForm_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [P.euclideanTraceScalingEquiv_apply, mul_pow,
    Real.sq_sqrt]
  · ring
  · exact_mod_cast (P.traceDiagonalWeights_pos i).le

/-- Polarization identifies the Euclidean inner product with the bilinear
form associated to the real trace quadratic form. -/
theorem inner_euclideanTraceScalingEquiv
    (P : GlobalLatticePresentation) (x y : P.RealTraceSpace) :
    ⟪P.euclideanTraceScalingEquiv x,
        P.euclideanTraceScalingEquiv y⟫_ℝ =
      QuadraticMap.associated P.realTraceQuadraticForm x y := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
  simp only [← pow_two, ← map_add]
  rw [P.euclideanTraceScalingEquiv_norm_sq,
    P.euclideanTraceScalingEquiv_norm_sq,
    P.euclideanTraceScalingEquiv_norm_sq,
    QuadraticMap.associated_apply]
  simp only [Module.End.smul_def,
    QuadraticMap.half_moduleEnd_apply_eq_half_smul, invOf_eq_inv,
    smul_eq_mul]
  ring

/-- The number-field rational point mapped into the Euclidean trace space. -/
def euclideanPointEmbedding (P : GlobalLatticePresentation)
    (x : Fin P.rank → P.field.1) : P.EuclideanTraceSpace :=
  P.euclideanTraceScalingEquiv (P.rationalPointEmbedding x)

@[simp]
theorem euclideanPointEmbedding_apply (P : GlobalLatticePresentation)
    (x : Fin P.rank → P.field.1) (i : P.TraceDimensionIndex) :
    P.euclideanPointEmbedding x i =
      Real.sqrt (P.traceDiagonalWeights i : ℝ) *
        (P.traceDiagonalIsometry x i : ℝ) :=
  rfl

/-- The Euclidean embedding is additive. -/
theorem euclideanPointEmbedding_sub (P : GlobalLatticePresentation)
    (x y : Fin P.rank → P.field.1) :
    P.euclideanPointEmbedding (x - y) =
      P.euclideanPointEmbedding x - P.euclideanPointEmbedding y := by
  simp [euclideanPointEmbedding]

/-- The embedded rational number-field vectors remain dense after scaling. -/
theorem euclideanPointEmbedding_denseRange
    (P : GlobalLatticePresentation) :
    DenseRange P.euclideanPointEmbedding := by
  have hcont : Continuous P.euclideanTraceScalingEquiv :=
    P.euclideanTraceScalingEquiv.toContinuousLinearEquiv.continuous
  have hcomp := P.euclideanTraceScalingEquiv.surjective.denseRange.comp
    P.rationalPointEmbedding_denseRange hcont
  change DenseRange (fun x ↦
    P.euclideanTraceScalingEquiv (P.rationalPointEmbedding x))
  exact hcomp

/-- The integral basis after the trace form has been made Euclidean. -/
def euclideanIntegralBasis (P : GlobalLatticePresentation) :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ P.integralRestriction)
      ℝ P.EuclideanTraceSpace :=
  P.realIntegralBasis.map P.euclideanTraceScalingEquiv

@[simp]
theorem euclideanIntegralBasis_apply (P : GlobalLatticePresentation)
    (i : Module.Free.ChooseBasisIndex ℤ P.integralRestriction) :
    P.euclideanIntegralBasis i =
      P.euclideanPointEmbedding (P.integralRestrictionBasis i).1 := by
  ext j
  simp [euclideanIntegralBasis, euclideanPointEmbedding]

/-- The full Euclidean lattice associated with the number-field lattice. -/
def euclideanIntegralLattice (P : GlobalLatticePresentation) :
    Submodule ℤ P.EuclideanTraceSpace :=
  Submodule.span ℤ (Set.range P.euclideanIntegralBasis)

instance (P : GlobalLatticePresentation) :
    DiscreteTopology P.euclideanIntegralLattice := by
  unfold euclideanIntegralLattice
  infer_instance

instance (P : GlobalLatticePresentation) :
    IsZLattice ℝ P.euclideanIntegralLattice := by
  unfold euclideanIntegralLattice
  infer_instance

/-- The displayed ambient basis, regarded as an integral basis of its span. -/
def euclideanIntegralLatticeBasis (P : GlobalLatticePresentation) :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ P.integralRestriction)
      ℤ P.euclideanIntegralLattice := by
  unfold euclideanIntegralLattice
  exact P.euclideanIntegralBasis.restrictScalars ℤ

@[simp]
theorem euclideanIntegralLatticeBasis_coe
    (P : GlobalLatticePresentation)
    (i : Module.Free.ChooseBasisIndex ℤ P.integralRestriction) :
    (P.euclideanIntegralLatticeBasis i : P.EuclideanTraceSpace) =
      P.euclideanIntegralBasis i := by
  exact P.euclideanIntegralBasis.restrictScalars_apply ℤ i

/-- The rational trace Gram matrix on the chosen integral basis. -/
def integralTraceGramMatrix (P : GlobalLatticePresentation) :
    Matrix (Module.Free.ChooseBasisIndex ℤ P.integralRestriction)
      (Module.Free.ChooseBasisIndex ℤ P.integralRestriction) ℚ :=
  Matrix.of fun i j ↦
    Algebra.trace ℚ P.field.1
      (QuadraticMap.associated P.Q
        (P.integralRestrictionBasis i).1
        (P.integralRestrictionBasis j).1)

/-- Every vector of the original lattice maps into the Euclidean lattice. -/
theorem euclideanPointEmbedding_mem_euclideanIntegralLattice
    (P : GlobalLatticePresentation)
    (x : Fin P.rank → P.field.1) (hx : x ∈ P.integralRestriction) :
    P.euclideanPointEmbedding x ∈ P.euclideanIntegralLattice := by
  have hxReal := P.rationalPointEmbedding_mem_realIntegralLattice x hx
  unfold realIntegralLattice at hxReal
  refine Submodule.span_induction
    (p := fun z _hz ↦
      P.euclideanTraceScalingEquiv z ∈ P.euclideanIntegralLattice)
      ?_ (by simp) ?_ ?_ hxReal
  · intro z hz
    obtain ⟨i, rfl⟩ := hz
    apply Submodule.subset_span
    exact ⟨i, rfl⟩
  · intro y z _hy _hz hy hz
    simpa using P.euclideanIntegralLattice.add_mem hy hz
  · intro a y _hy hy
    rw [map_zsmul]
    exact P.euclideanIntegralLattice.smul_mem a hy

/-- Every original lattice vector supplies a point of the Euclidean lattice. -/
def euclideanLatticePoint (P : GlobalLatticePresentation) (y : P.L) :
    P.euclideanIntegralLattice := by
  refine ⟨P.euclideanPointEmbedding y.1, ?_⟩
  exact P.euclideanPointEmbedding_mem_euclideanIntegralLattice y.1 y.2

@[simp]
theorem euclideanLatticePoint_coe
    (P : GlobalLatticePresentation) (y : P.L) :
    (P.euclideanLatticePoint y : P.EuclideanTraceSpace) =
      P.euclideanPointEmbedding y.1 :=
  rfl

/-- The Euclidean distance formula is exactly the original rational trace. -/
theorem norm_sq_euclideanPointEmbedding
    (P : GlobalLatticePresentation)
    (x : Fin P.rank → P.field.1) :
    ‖P.euclideanPointEmbedding x‖ ^ (2 : ℕ) =
      (P.traceQuadraticForm x : ℝ) := by
  rw [euclideanPointEmbedding,
    P.euclideanTraceScalingEquiv_norm_sq,
    P.realTraceQuadraticForm_rationalPointEmbedding]

/-- The Euclidean inner product on embedded rational points is the real cast
of the field trace of the original associated bilinear form. -/
theorem inner_euclideanPointEmbedding
    (P : GlobalLatticePresentation)
    (x y : Fin P.rank → P.field.1) :
    ⟪P.euclideanPointEmbedding x, P.euclideanPointEmbedding y⟫_ℝ =
      ((Algebra.trace ℚ P.field.1
        (QuadraticMap.associated P.Q x y) : ℚ) : ℝ) := by
  calc
    ⟪P.euclideanPointEmbedding x, P.euclideanPointEmbedding y⟫_ℝ =
        QuadraticMap.associated P.realTraceQuadraticForm
          (P.rationalPointEmbedding x) (P.rationalPointEmbedding y) := by
      exact P.inner_euclideanTraceScalingEquiv _ _
    _ = ((QuadraticMap.associated P.traceQuadraticForm x y : ℚ) : ℝ) := by
      rw [QuadraticMap.associated_apply, QuadraticMap.associated_apply]
      simp only [Module.End.smul_def,
        QuadraticMap.half_moduleEnd_apply_eq_half_smul, invOf_eq_inv,
        smul_eq_mul, ← map_add]
      rw [P.realTraceQuadraticForm_rationalPointEmbedding,
        P.realTraceQuadraticForm_rationalPointEmbedding,
        P.realTraceQuadraticForm_rationalPointEmbedding]
      norm_num
    _ = ((Algebra.trace ℚ P.field.1
        (QuadraticMap.associated P.Q x y) : ℚ) : ℝ) := by
      rw [P.traceQuadraticForm_associated]

/-- The Euclidean Gram matrix is the real cast of the rational trace Gram
matrix of the original lattice basis. -/
theorem gram_euclideanIntegralBasis_eq_map_integralTraceGramMatrix
    (P : GlobalLatticePresentation) :
    Matrix.gram ℝ P.euclideanIntegralBasis =
      (P.integralTraceGramMatrix.map (Rat.castHom ℝ)) := by
  ext i j
  rw [Matrix.gram_apply, P.euclideanIntegralBasis_apply,
    P.euclideanIntegralBasis_apply,
    P.inner_euclideanPointEmbedding]
  rfl

/-- Strict trace-Euclideanity gives the exact strict squared-distance bound
on every embedded rational point. -/
theorem exists_euclideanLatticePoint_norm_sq_lt
    (P : GlobalLatticePresentation) {t : ℝ}
    (hE : P.IsTraceEuclidean t)
    (x : Fin P.rank → P.field.1) :
    ∃ l : P.euclideanIntegralLattice,
      ‖P.euclideanPointEmbedding x - (l : P.EuclideanTraceSpace)‖ ^
          (2 : ℕ) < t := by
  obtain ⟨y, hy⟩ := hE x
  refine ⟨P.euclideanLatticePoint y, ?_⟩
  rw [P.euclideanLatticePoint_coe,
    ← P.euclideanPointEmbedding_sub,
    P.norm_sq_euclideanPointEmbedding,
    P.traceQuadraticForm_apply]
  exact hy

/-- Every radius strictly larger than a positive trace-Euclidean bound covers
the complete real trace space by lattice translates. -/
theorem euclidean_ball_cover_of_traceEuclidean
    (P : GlobalLatticePresentation) {t u : ℝ}
    (ht : 0 < t) (htu : t < u)
    (hE : P.IsTraceEuclidean t) :
    ∀ x : P.EuclideanTraceSpace,
      ∃ l : P.euclideanIntegralLattice,
        x ∈ l +ᵥ Metric.ball (0 : P.EuclideanTraceSpace) (Real.sqrt u) := by
  intro x
  have hsqrt : Real.sqrt t < Real.sqrt u :=
    Real.sqrt_lt_sqrt ht.le htu
  have hdelta : 0 < Real.sqrt u - Real.sqrt t := sub_pos.2 hsqrt
  obtain ⟨q, hq⟩ :=
    P.euclideanPointEmbedding_denseRange.exists_dist_lt x hdelta
  obtain ⟨l, hl⟩ := P.exists_euclideanLatticePoint_norm_sq_lt hE q
  have hnorm :
      ‖P.euclideanPointEmbedding q - (l : P.EuclideanTraceSpace)‖ <
        Real.sqrt t := by
    nlinarith [Real.sq_sqrt ht.le,
      norm_nonneg (P.euclideanPointEmbedding q -
        (l : P.EuclideanTraceSpace)), Real.sqrt_nonneg t]
  have htriangle :
      ‖x - (l : P.EuclideanTraceSpace)‖ ≤
        dist x (P.euclideanPointEmbedding q) +
          ‖P.euclideanPointEmbedding q -
            (l : P.EuclideanTraceSpace)‖ := by
    simpa only [dist_eq_norm] using
      dist_triangle x (P.euclideanPointEmbedding q)
        (l : P.EuclideanTraceSpace)
  have hfinal :
      ‖x - (l : P.EuclideanTraceSpace)‖ < Real.sqrt u := by
    nlinarith
  refine ⟨l, ?_⟩
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, Metric.mem_ball]
  simp only [dist_eq_norm, sub_zero]
  change ‖-(l : P.EuclideanTraceSpace) + x‖ < Real.sqrt u
  simpa [sub_eq_add_neg, add_comm] using hfinal

/-- The real Euclidean trace space has dimension rank times field degree. -/
theorem euclideanTraceSpace_finrank (P : GlobalLatticePresentation) :
    Module.finrank ℝ P.EuclideanTraceSpace = P.rank * P.degree := by
  rw [finrank_euclideanSpace_fin]
  exact P.traceSpace_finrank

/-- The covolume squared is the Gram determinant of the displayed integral
basis in the Euclidean trace realization. -/
theorem euclideanCovolume_sq_eq_det_gram
    (P : GlobalLatticePresentation) :
    ZLattice.covolume P.euclideanIntegralLattice ^ (2 : ℕ) =
      (Matrix.gram ℝ P.euclideanIntegralBasis).det := by
  classical
  let bstd : OrthonormalBasis P.TraceDimensionIndex ℝ
      P.EuclideanTraceSpace :=
    EuclideanSpace.basisFun P.TraceDimensionIndex ℝ
  let e : P.TraceDimensionIndex ≃
      Module.Free.ChooseBasisIndex ℤ P.integralRestriction :=
    bstd.toBasis.indexEquiv P.euclideanIntegralBasis
  let b₀o : OrthonormalBasis
      (Module.Free.ChooseBasisIndex ℤ P.integralRestriction) ℝ
      P.EuclideanTraceSpace := bstd.reindex e
  let b₀ : Module.Basis
      (Module.Free.ChooseBasisIndex ℤ P.integralRestriction) ℝ
      P.EuclideanTraceSpace := b₀o.toBasis
  let bℤ := P.euclideanIntegralLatticeBasis
  have hvol :
      MeasureTheory.volume.real (ZSpan.fundamentalDomain b₀) = 1 := by
    calc
      MeasureTheory.volume.real (ZSpan.fundamentalDomain b₀) =
          MeasureTheory.volume.real (Module.Basis.parallelepiped b₀) :=
        MeasureTheory.measureReal_congr
          (ZSpan.fundamentalDomain_ae_parallelepiped b₀
            MeasureTheory.volume)
      _ = 1 := by
        simpa [MeasureTheory.Measure.real, b₀] using
          congrArg ENNReal.toReal b₀o.volume_parallelepiped
  let m : Matrix
      (Module.Free.ChooseBasisIndex ℤ P.integralRestriction)
      (Module.Free.ChooseBasisIndex ℤ P.integralRestriction) ℝ :=
    Matrix.of fun i j ↦ b₀o.repr (P.euclideanIntegralBasis j) i
  have hm : b₀.toMatrix ((↑) ∘ bℤ) = m := by
    ext i j
    change b₀.repr (bℤ j : P.EuclideanTraceSpace) i =
      b₀o.repr (P.euclideanIntegralBasis j) i
    rw [P.euclideanIntegralLatticeBasis_coe]
    rfl
  rw [ZLattice.covolume_eq_det_mul_measureReal
      P.euclideanIntegralLattice (μ := MeasureTheory.volume) bℤ b₀,
    hvol, mul_one, sq_abs, Module.Basis.det_apply, hm]
  rw [Matrix.gram_eq_conjTranspose_mul b₀o
      P.euclideanIntegralBasis,
    Matrix.det_mul, Matrix.det_conjTranspose]
  simp [m, pow_two]

/-- Algebraic form of the covolume identity: the squared real covolume is the
real cast of the rational trace Gram determinant. -/
theorem euclideanCovolume_sq_eq_integralTraceGramDet
    (P : GlobalLatticePresentation) :
    ZLattice.covolume P.euclideanIntegralLattice ^ (2 : ℕ) =
      ((P.integralTraceGramMatrix.det : ℚ) : ℝ) := by
  rw [P.euclideanCovolume_sq_eq_det_gram,
    P.gram_euclideanIntegralBasis_eq_map_integralTraceGramMatrix]
  exact (Rat.cast_det P.integralTraceGramMatrix).symm

/-- The sharp covering-volume inequality attached directly to a positive
strict trace-Euclidean presentation. -/
theorem euclideanCovolume_sq_le_of_traceEuclidean
    (P : GlobalLatticePresentation) {t : ℝ}
    (ht : 0 < t) (hE : P.IsTraceEuclidean t) :
    ZLattice.covolume P.euclideanIntegralLattice ^ (2 : ℕ) ≤
      euclideanUnitBallVolume (P.rank * P.degree) ^ (2 : ℕ) *
        t ^ (P.rank * P.degree) := by
  have hdim : 0 < Module.finrank ℝ P.EuclideanTraceSpace := by
    rw [P.euclideanTraceSpace_finrank]
    exact Nat.mul_pos P.rankPositive (by
      unfold GlobalLatticePresentation.degree
      exact Module.finrank_pos)
  letI : Nontrivial P.EuclideanTraceSpace :=
    Module.nontrivial_of_finrank_pos hdim
  have h := covolume_sq_le_of_sqrt_cover_above
    P.euclideanIntegralLattice t ht
    (fun u htu ↦ P.euclidean_ball_cover_of_traceEuclidean ht htu hE)
  rw [P.euclideanTraceSpace_finrank] at h
  exact h

end GlobalLatticePresentation

end

end TraceEuclidean
