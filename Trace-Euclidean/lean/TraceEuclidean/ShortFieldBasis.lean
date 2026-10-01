import TraceEuclidean.CoveringShortBasis
import TraceEuclidean.VolumeIdeals

/-!
# A short field basis extracted from the Euclidean trace lattice

This file pulls the short real-linearly-independent family supplied by the
covering argument back to the original integral lattice.  It then selects a
field basis from that family, so every selected basis vector retains the same
explicit Euclidean trace-norm bound.
-/

namespace TraceEuclidean

open scoped NumberField

noncomputable section

namespace GlobalLatticePresentation

/-- The integral restriction and its Euclidean realization have the bases
with the same index set, hence are canonically equivalent as `ℤ`-modules. -/
def integralRestrictionEquivEuclideanLattice
    (P : GlobalLatticePresentation) :
    P.integralRestriction ≃ₗ[ℤ] P.euclideanIntegralLattice :=
  P.integralRestrictionBasis.equiv P.euclideanIntegralLatticeBasis (Equiv.refl _)

/-- The preceding basis equivalence is the concrete Euclidean point embedding. -/
@[simp]
theorem coe_integralRestrictionEquivEuclideanLattice
    (P : GlobalLatticePresentation) (x : P.integralRestriction) :
    (P.integralRestrictionEquivEuclideanLattice x : P.EuclideanTraceSpace) =
      P.euclideanPointEmbedding x.1 := by
  let lhs : P.integralRestriction →ₗ[ℤ] P.EuclideanTraceSpace :=
    P.euclideanIntegralLattice.subtype.comp
      P.integralRestrictionEquivEuclideanLattice.toLinearMap
  let rhs : P.integralRestriction →ₗ[ℤ] P.EuclideanTraceSpace :=
    { toFun := fun y ↦ P.euclideanPointEmbedding y.1
      map_add' := by
        intro y z
        simp [euclideanPointEmbedding]
      map_smul' := by
        intro a y
        change P.euclideanTraceScalingEquiv
            (P.rationalPointEmbedding (a • y.1)) =
          a • P.euclideanTraceScalingEquiv (P.rationalPointEmbedding y.1)
        rw [map_zsmul, map_zsmul] }
  have hmaps : lhs = rhs := by
    apply P.integralRestrictionBasis.ext
    intro i
    simp [lhs, rhs, integralRestrictionEquivEuclideanLattice,
      euclideanIntegralBasis_apply]
  exact LinearMap.congr_fun hmaps x

/-- Pull a Euclidean trace-lattice point back to the original lattice. -/
def euclideanLatticePreimage (P : GlobalLatticePresentation)
    (v : P.euclideanIntegralLattice) : P.L := by
  let x : P.integralRestriction :=
    P.integralRestrictionEquivEuclideanLattice.symm v
  exact ⟨x.1, x.2⟩

@[simp]
theorem euclideanPointEmbedding_euclideanLatticePreimage
    (P : GlobalLatticePresentation) (v : P.euclideanIntegralLattice) :
    P.euclideanPointEmbedding (P.euclideanLatticePreimage v).1 =
      (v : P.EuclideanTraceSpace) := by
  have h := P.coe_integralRestrictionEquivEuclideanLattice
    (P.integralRestrictionEquivEuclideanLattice.symm v)
  simpa [euclideanLatticePreimage] using h.symm

/-- The rational-linear map underlying the Euclidean point embedding. -/
def euclideanPointEmbeddingLinear (P : GlobalLatticePresentation) :
    (Fin P.rank → P.field.1) →ₗ[ℚ] P.EuclideanTraceSpace :=
  (P.euclideanTraceScalingEquiv.toLinearMap.restrictScalars ℚ).comp
    P.rationalPointEmbedding

@[simp]
theorem euclideanPointEmbeddingLinear_apply
    (P : GlobalLatticePresentation) (x : Fin P.rank → P.field.1) :
    P.euclideanPointEmbeddingLinear x = P.euclideanPointEmbedding x :=
  rfl

/-- Over the totally real ground field, the real trace is the sum of the
real values of all complex embeddings. -/
theorem real_trace_eq_sum_embeddings (P : GlobalLatticePresentation)
    (a : P.field.1) :
    ((Algebra.trace ℚ P.field.1 a : ℚ) : ℝ) =
      ∑ τ : P.field.1 →ₐ[ℚ] ℂ, (τ a).re := by
  letI : NumberField.IsTotallyReal P.field.1 := P.totallyReal
  have htrace := trace_eq_sum_embeddings ℂ
    (K := ℚ) (L := P.field.1) (x := a)
  have hre := congrArg Complex.re htrace
  let q : ℚ := Algebra.trace ℚ P.field.1 a
  calc
    (q : ℝ) = (Complex.ofReal (q : ℝ)).re := by simp
    _ = ((q : ℂ)).re := by rw [Complex.ofReal_ratCast]
    _ = (∑ τ : P.field.1 →ₐ[ℚ] ℂ, τ a).re := hre
    _ = ∑ τ : P.field.1 →ₐ[ℚ] ℂ, (τ a).re := by
      rw [Complex.re_sum]

/-- Every real conjugate of a represented quadratic value is at most its
trace.  Total positivity is essential here: all other summands in the trace
are nonnegative. -/
theorem realEmbedding_quadratic_le_trace
    (P : GlobalLatticePresentation) (σ : P.field.1 →+* ℝ)
    (x : Fin P.rank → P.field.1) :
    σ (P.Q x) ≤ ((P.traceQuadraticForm x : ℚ) : ℝ) := by
  classical
  letI : NumberField.IsTotallyReal P.field.1 := P.totallyReal
  let τ : P.field.1 →ₐ[ℚ] ℂ :=
    (Complex.ofRealHom.comp σ).toRatAlgHom
  have hnonneg (φ : P.field.1 →ₐ[ℚ] ℂ) :
      0 ≤ (φ (P.Q x)).re := by
    by_cases hx : x = 0
    · simp [hx]
    · let hreal : NumberField.ComplexEmbedding.IsReal φ.toRingHom :=
        NumberField.IsTotallyReal.complexEmbedding_isReal φ.toRingHom
      exact (P.positiveDefinite x hx hreal.embedding).le
  have hterm :
      (τ (P.Q x)).re ≤ ∑ φ : P.field.1 →ₐ[ℚ] ℂ, (φ (P.Q x)).re := by
    exact Finset.single_le_sum (fun φ _hφ ↦ hnonneg φ) (Finset.mem_univ τ)
  calc
    σ (P.Q x) = (τ (P.Q x)).re := by rfl
    _ ≤ ∑ φ : P.field.1 →ₐ[ℚ] ℂ, (φ (P.Q x)).re := hterm
    _ = ((P.traceQuadraticForm x : ℚ) : ℝ) := by
      symm
      simpa [traceQuadraticForm_apply] using
        P.real_trace_eq_sum_embeddings (P.Q x)

/-- Polarization in the normalization used by the manuscript. -/
theorem quadratic_add_eq_add_two_associated
    (P : GlobalLatticePresentation)
    (x y : Fin P.rank → P.field.1) :
    P.Q (x + y) = P.Q x +
      2 * QuadraticMap.associated P.Q x y + P.Q y := by
  calc
    P.Q (x + y) = QuadraticMap.associated P.Q (x + y) (x + y) := by
      symm
      exact QuadraticMap.associated_eq_self_apply P.field.1 P.Q (x + y)
    _ = QuadraticMap.associated P.Q x x +
          QuadraticMap.associated P.Q x y +
          (QuadraticMap.associated P.Q y x +
            QuadraticMap.associated P.Q y y) := by
      simp only [map_add, LinearMap.add_apply]
      abel
    _ = P.Q x + 2 * QuadraticMap.associated P.Q x y + P.Q y := by
      rw [QuadraticMap.associated_eq_self_apply P.field.1 P.Q x,
        QuadraticMap.associated_eq_self_apply P.field.1 P.Q y,
        QuadraticMap.associated_isSymm P.field.1 P.Q y x]
      ring

/-- Expansion of a translated quadratic value in the same polarization
normalization. -/
theorem quadratic_sub_smul_eq
    (P : GlobalLatticePresentation)
    (x y : Fin P.rank → P.field.1) (a : P.field.1) :
    P.Q (x - a • y) = P.Q x -
      2 * a * QuadraticMap.associated P.Q x y + a ^ 2 * P.Q y := by
  rw [sub_eq_add_neg, P.quadratic_add_eq_add_two_associated]
  simp only [map_neg, map_smul,
    QuadraticMap.map_neg, QuadraticMap.map_smul, smul_eq_mul]
  ring

/-- Cauchy--Schwarz for every real embedding of the totally positive
quadratic form. -/
theorem realEmbedding_associated_sq_le
    (P : GlobalLatticePresentation) (σ : P.field.1 →+* ℝ)
    (x y : Fin P.rank → P.field.1) :
    (σ (QuadraticMap.associated P.Q x y)) ^ 2 ≤
      σ (P.Q x) * σ (P.Q y) := by
  by_cases hy : y = 0
  · subst y
    simp
  let b : P.field.1 := QuadraticMap.associated P.Q x y
  let qy : P.field.1 := P.Q y
  have hqy : 0 < σ qy := by
    exact P.positiveDefinite y hy σ
  let z : Fin P.rank → P.field.1 := x - (b / qy) • y
  have hz : 0 ≤ σ (P.Q z) := by
    by_cases hz0 : z = 0
    · simp [hz0]
    · exact (P.positiveDefinite z hz0 σ).le
  have hzExpanded :
      0 ≤ σ (P.Q x) - 2 * (σ b / σ qy) * σ b +
        (σ b / σ qy) ^ 2 * σ qy := by
    rw [show P.Q z = P.Q x - 2 * (b / qy) * b +
        (b / qy) ^ 2 * qy by
      simpa [z, b, qy] using P.quadratic_sub_smul_eq x y (b / qy)] at hz
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat] at hz
    rw [map_div₀] at hz
    exact hz
  have hidentity :
      σ (P.Q x) - 2 * (σ b / σ qy) * σ b +
          (σ b / σ qy) ^ 2 * σ qy =
        (σ (P.Q x) * σ qy - (σ b) ^ 2) / σ qy := by
    field_simp [ne_of_gt hqy]
    ring
  rw [hidentity] at hzExpanded
  have hnumerator :
      0 ≤ σ (P.Q x) * σ qy - (σ b) ^ 2 := by
    have hmul := mul_nonneg hzExpanded hqy.le
    simpa [ne_of_gt hqy] using hmul
  simpa [b, qy] using (sub_nonneg.mp hnumerator)

/-- A trace-Euclidean presentation has a field basis made of lattice vectors,
all selected from the short independent family supplied by the covering
argument. -/
theorem exists_short_lattice_fieldBasis_of_traceEuclidean
    (P : GlobalLatticePresentation) {t u : ℝ}
    (ht : 0 < t) (htu : t < u) (hE : P.IsTraceEuclidean t) :
    ∃ (w : Fin P.rank → P.L)
      (b : Module.Basis (Fin P.rank) P.field.1 (Fin P.rank → P.field.1)),
        (∀ i, b i = (w i).1) ∧
        ∀ i, ‖P.euclideanPointEmbedding (w i).1‖ <
          ((P.rank * P.degree : ℕ) + 1 : ℝ) * Real.sqrt u + 1 := by
  classical
  obtain ⟨v, hvIndependent, hvBound⟩ :=
    P.exists_short_linearIndependent_euclideanLattice_of_traceEuclidean ht htu hE
  let x : P.TraceDimensionIndex → (Fin P.rank → P.field.1) :=
    fun i ↦ (P.euclideanLatticePreimage (v i)).1
  have hxImage :
      P.euclideanPointEmbeddingLinear ∘ x =
        fun i ↦ (v i : P.EuclideanTraceSpace) := by
    funext i
    simp [x]
  have hxIndependent : LinearIndependent ℚ x := by
    apply LinearIndependent.of_comp P.euclideanPointEmbeddingLinear
    rw [hxImage]
    exact hvIndependent.restrict_scalars' ℚ
  have hxSpanQ : Submodule.span ℚ (Set.range x) = ⊤ := by
    apply hxIndependent.span_eq_top_of_card_eq_finrank'
    simp
  have hxSpanF : Submodule.span P.field.1 (Set.range x) = ⊤ :=
    Submodule.span_eq_top_of_span_eq_top (R := ℚ) (S := P.field.1)
      (Set.range x) hxSpanQ
  let S : Set (Fin P.rank → P.field.1) :=
    (linearIndepOn_empty P.field.1
      (id : (Fin P.rank → P.field.1) → (Fin P.rank → P.field.1))).extend
        (Set.empty_subset (Set.range x))
  let bS : Module.Basis S P.field.1 (Fin P.rank → P.field.1) :=
    Module.Basis.ofSpan hxSpanF.ge
  letI : Finite S := Module.Finite.finite_basis bS
  letI : Fintype S := Fintype.ofFinite S
  have hcardS : Fintype.card S = P.rank := by
    rw [← Module.finrank_eq_card_basis bS]
    simp
  let e : S ≃ Fin P.rank := Fintype.equivFinOfCardEq hcardS
  let b : Module.Basis (Fin P.rank) P.field.1 (Fin P.rank → P.field.1) :=
    bS.reindex e
  have hbMem (i : Fin P.rank) : b i ∈ Set.range x := by
    have hvalue : bS (e.symm i) = (e.symm i).1 := by
      exact Module.Basis.ofSpan_apply_self hxSpanF.ge (e.symm i)
    rw [show b i = bS (e.symm i) by simp [b]]
    rw [hvalue]
    exact (linearIndepOn_empty P.field.1
      (id : (Fin P.rank → P.field.1) → (Fin P.rank → P.field.1))).extend_subset
        (Set.empty_subset (Set.range x)) (e.symm i).2
  choose source hsource using hbMem
  let w : Fin P.rank → P.L :=
    fun i ↦ P.euclideanLatticePreimage (v (source i))
  refine ⟨w, b, ?_, ?_⟩
  · intro i
    exact (hsource i).symm
  · intro i
    simpa [w] using hvBound (source i)

/-- The short field basis also has a uniform bound for every real conjugate
of every Gram entry. -/
theorem exists_short_lattice_fieldBasis_with_conjugate_bound
    (P : GlobalLatticePresentation) {t u : ℝ}
    (ht : 0 < t) (htu : t < u) (hE : P.IsTraceEuclidean t) :
    ∃ (w : Fin P.rank → P.L)
      (b : Module.Basis (Fin P.rank) P.field.1 (Fin P.rank → P.field.1)),
        (∀ i, b i = (w i).1) ∧
        (∀ i, ‖P.euclideanPointEmbedding (w i).1‖ <
          ((P.rank * P.degree : ℕ) + 1 : ℝ) * Real.sqrt u + 1) ∧
        ∀ (σ : P.field.1 →+* ℝ) i j,
          |σ (QuadraticMap.associated P.Q (w i).1 (w j).1)| <
            (((P.rank * P.degree : ℕ) + 1 : ℝ) * Real.sqrt u + 1) ^ 2 := by
  classical
  obtain ⟨w, b, hb, hwBound⟩ :=
    P.exists_short_lattice_fieldBasis_of_traceEuclidean ht htu hE
  let C : ℝ := ((P.rank * P.degree : ℕ) + 1 : ℝ) * Real.sqrt u + 1
  refine ⟨w, b, hb, hwBound, ?_⟩
  intro σ i j
  have hwi : (w i).1 ≠ 0 := by
    rw [← hb i]
    exact b.ne_zero i
  have hwj : (w j).1 ≠ 0 := by
    rw [← hb j]
    exact b.ne_zero j
  have hqiPos : 0 < σ (P.Q (w i).1) :=
    P.positiveDefinite (w i).1 hwi σ
  have hqjPos : 0 < σ (P.Q (w j).1) :=
    P.positiveDefinite (w j).1 hwj σ
  have hCPos : 0 < C := by
    exact lt_of_le_of_lt
      (norm_nonneg (P.euclideanPointEmbedding (w i).1)) (by
        simpa [C] using hwBound i)
  have htraceI :
      ((P.traceQuadraticForm (w i).1 : ℚ) : ℝ) < C ^ 2 := by
    rw [← P.norm_sq_euclideanPointEmbedding]
    nlinarith [norm_nonneg (P.euclideanPointEmbedding (w i).1),
      show ‖P.euclideanPointEmbedding (w i).1‖ < C by
        simpa [C] using hwBound i]
  have htraceJ :
      ((P.traceQuadraticForm (w j).1 : ℚ) : ℝ) < C ^ 2 := by
    rw [← P.norm_sq_euclideanPointEmbedding]
    nlinarith [norm_nonneg (P.euclideanPointEmbedding (w j).1),
      show ‖P.euclideanPointEmbedding (w j).1‖ < C by
        simpa [C] using hwBound j]
  have hqiUpper : σ (P.Q (w i).1) < C ^ 2 :=
    (P.realEmbedding_quadratic_le_trace σ (w i).1).trans_lt htraceI
  have hqjUpper : σ (P.Q (w j).1) < C ^ 2 :=
    (P.realEmbedding_quadratic_le_trace σ (w j).1).trans_lt htraceJ
  have hC2Pos : 0 < C ^ 2 := sq_pos_of_pos hCPos
  have hproduct :
      σ (P.Q (w i).1) * σ (P.Q (w j).1) < (C ^ 2) ^ 2 := by
    calc
      σ (P.Q (w i).1) * σ (P.Q (w j).1) <
          σ (P.Q (w i).1) * C ^ 2 :=
        mul_lt_mul_of_pos_left hqjUpper hqiPos
      _ < (C ^ 2) * (C ^ 2) :=
        mul_lt_mul_of_pos_right hqiUpper hC2Pos
      _ = (C ^ 2) ^ 2 := by ring
  have hsq :
      (σ (QuadraticMap.associated P.Q (w i).1 (w j).1)) ^ 2 <
        (C ^ 2) ^ 2 :=
    (P.realEmbedding_associated_sq_le σ (w i).1 (w j).1).trans_lt hproduct
  have habsSq :
      |σ (QuadraticMap.associated P.Q (w i).1 (w j).1)| ^ 2 =
        (σ (QuadraticMap.associated P.Q (w i).1 (w j).1)) ^ 2 := by
    exact sq_abs _
  have habsNonneg :
      0 ≤ |σ (QuadraticMap.associated P.Q (w i).1 (w j).1)| := abs_nonneg _
  have hresult :
      |σ (QuadraticMap.associated P.Q (w i).1 (w j).1)| < C ^ 2 := by
    nlinarith
  simpa [C] using hresult

/-- The real embedding underlying a complex embedding of the totally real
ground field. -/
def realEmbeddingOfComplexEmbedding (P : GlobalLatticePresentation)
    (τ : P.field.1 →ₐ[ℚ] ℂ) : P.field.1 →+* ℝ := by
  letI : NumberField.IsTotallyReal P.field.1 := P.totallyReal
  exact (NumberField.IsTotallyReal.complexEmbedding_isReal τ.toRingHom).embedding

/-- In a totally real field the norm of a complex conjugate is the absolute
value of the corresponding real conjugate. -/
theorem norm_complexEmbedding_eq_abs_realEmbedding
    (P : GlobalLatticePresentation) (τ : P.field.1 →ₐ[ℚ] ℂ)
    (a : P.field.1) :
    ‖τ a‖ = |P.realEmbeddingOfComplexEmbedding τ a| := by
  letI : NumberField.IsTotallyReal P.field.1 := P.totallyReal
  let hreal : NumberField.ComplexEmbedding.IsReal τ.toRingHom :=
    NumberField.IsTotallyReal.complexEmbedding_isReal τ.toRingHom
  change ‖τ a‖ = |hreal.embedding a|
  have heq : (hreal.embedding a : ℂ) = τ a := hreal.coe_embedding_apply a
  rw [← heq, Complex.norm_real, Real.norm_eq_abs]

/-- The same short basis bound, stated simultaneously for real embeddings and
for all complex embeddings. -/
theorem exists_short_lattice_fieldBasis_with_all_embedding_bounds
    (P : GlobalLatticePresentation) {t u : ℝ}
    (ht : 0 < t) (htu : t < u) (hE : P.IsTraceEuclidean t) :
    ∃ (w : Fin P.rank → P.L)
      (b : Module.Basis (Fin P.rank) P.field.1 (Fin P.rank → P.field.1)),
        (∀ i, b i = (w i).1) ∧
        (∀ i, ‖P.euclideanPointEmbedding (w i).1‖ <
          ((P.rank * P.degree : ℕ) + 1 : ℝ) * Real.sqrt u + 1) ∧
        (∀ (σ : P.field.1 →+* ℝ) i j,
          |σ (QuadraticMap.associated P.Q (w i).1 (w j).1)| <
            (((P.rank * P.degree : ℕ) + 1 : ℝ) * Real.sqrt u + 1) ^ 2) ∧
        ∀ (τ : P.field.1 →ₐ[ℚ] ℂ) i j,
          ‖τ (QuadraticMap.associated P.Q (w i).1 (w j).1)‖ <
            (((P.rank * P.degree : ℕ) + 1 : ℝ) * Real.sqrt u + 1) ^ 2 := by
  letI : NumberField.IsTotallyReal P.field.1 := P.totallyReal
  obtain ⟨w, b, hb, hwBound, hrealBound⟩ :=
    P.exists_short_lattice_fieldBasis_with_conjugate_bound ht htu hE
  refine ⟨w, b, hb, hwBound, hrealBound, ?_⟩
  intro τ i j
  rw [P.norm_complexEmbedding_eq_abs_realEmbedding τ]
  exact hrealBound (P.realEmbeddingOfComplexEmbedding τ) i j

/-- In the classic-integral case, every Gram entry of the short field basis
has a canonical representative in `𝓞_F`; its real and complex conjugates obey
the same uniform squared bound. -/
theorem exists_short_classicIntegral_fieldBasis
    (P : GlobalLatticePresentation) {t u : ℝ}
    (ht : 0 < t) (htu : t < u) (hE : P.IsTraceEuclidean t)
    (hclassic : P.IsClassicIntegral) :
    ∃ (w : Fin P.rank → P.L)
      (b : Module.Basis (Fin P.rank) P.field.1 (Fin P.rank → P.field.1)),
        (∀ i, b i = (w i).1) ∧
        (∀ i, ‖P.euclideanPointEmbedding (w i).1‖ <
          ((P.rank * P.degree : ℕ) + 1 : ℝ) * Real.sqrt u + 1) ∧
        (∀ i j,
          (P.classicBilinearInteger hclassic (w i) (w j) : P.field.1) =
            QuadraticMap.associated P.Q (w i).1 (w j).1) ∧
        (∀ (σ : P.field.1 →+* ℝ) i j,
          |σ (QuadraticMap.associated P.Q (w i).1 (w j).1)| <
            (((P.rank * P.degree : ℕ) + 1 : ℝ) * Real.sqrt u + 1) ^ 2) ∧
        ∀ (τ : P.field.1 →ₐ[ℚ] ℂ) i j,
          ‖τ (QuadraticMap.associated P.Q (w i).1 (w j).1)‖ <
            (((P.rank * P.degree : ℕ) + 1 : ℝ) * Real.sqrt u + 1) ^ 2 := by
  obtain ⟨w, b, hb, hwBound, hrealBound, hcomplexBound⟩ :=
    P.exists_short_lattice_fieldBasis_with_all_embedding_bounds ht htu hE
  exact ⟨w, b, hb, hwBound,
    fun i j ↦ P.coe_classicBilinearInteger hclassic (w i) (w j),
    hrealBound, hcomplexBound⟩

/-- Without classic integrality, the Gram matrix of the scaled form `2Q`
still has entries in `𝓞_F`.  Every real or complex conjugate of such an entry
is bounded by twice the squared short-vector bound. -/
theorem exists_short_integralScaled_fieldBasis
    (P : GlobalLatticePresentation) {t u : ℝ}
    (ht : 0 < t) (htu : t < u) (hE : P.IsTraceEuclidean t) :
    ∃ (w : Fin P.rank → P.L)
      (b : Module.Basis (Fin P.rank) P.field.1 (Fin P.rank → P.field.1)),
        (∀ i, b i = (w i).1) ∧
        (∀ i, ‖P.euclideanPointEmbedding (w i).1‖ <
          ((P.rank * P.degree : ℕ) + 1 : ℝ) * Real.sqrt u + 1) ∧
        (∀ i j,
          (P.scaledBilinearInteger (w i) (w j) : P.field.1) =
            2 * QuadraticMap.associated P.Q (w i).1 (w j).1) ∧
        (∀ (σ : P.field.1 →+* ℝ) i j,
          |σ (P.scaledBilinearInteger (w i) (w j) : P.field.1)| <
            2 *
              ((((P.rank * P.degree : ℕ) + 1 : ℝ) * Real.sqrt u + 1) ^ 2)) ∧
        ∀ (τ : P.field.1 →ₐ[ℚ] ℂ) i j,
          ‖τ (P.scaledBilinearInteger (w i) (w j) : P.field.1)‖ <
            2 *
              ((((P.rank * P.degree : ℕ) + 1 : ℝ) * Real.sqrt u + 1) ^ 2) := by
  obtain ⟨w, b, hb, hwBound, hrealBound, hcomplexBound⟩ :=
    P.exists_short_lattice_fieldBasis_with_all_embedding_bounds ht htu hE
  refine ⟨w, b, hb, hwBound, ?_, ?_, ?_⟩
  · intro i j
    exact P.scaledBilinearInteger_eq_two_associated (w i) (w j)
  · intro σ i j
    rw [P.scaledBilinearInteger_eq_two_associated,
      map_mul, map_ofNat, abs_mul]
    norm_num
    simpa only [Nat.cast_mul] using hrealBound σ i j
  · intro τ i j
    rw [P.scaledBilinearInteger_eq_two_associated,
      map_mul, map_ofNat, norm_mul]
    norm_num
    simpa only [Nat.cast_mul] using hcomplexBound τ i j

end GlobalLatticePresentation

end

end TraceEuclidean
