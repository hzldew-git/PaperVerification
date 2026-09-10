import TraceEuclidean.GlobalLatticeClass
import Mathlib.RingTheory.Trace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
The rational trace form and the underlying integral lattice of a global
field--lattice presentation.  This is the algebraic input for the real
Minkowski-space construction: the form is obtained by restricting scalars
from the number field to `ℚ` and applying the field trace, while the lattice
is obtained by restricting scalars from `𝓞_F` to `ℤ`.
-/

namespace TraceEuclidean

open scoped NumberField

noncomputable section

namespace GlobalLatticePresentation

/-- The rational quadratic form obtained from the manuscript's trace form. -/
def traceQuadraticForm (P : GlobalLatticePresentation) :
    QuadraticForm ℚ (Fin P.rank → P.field.1) :=
  (Algebra.trace ℚ P.field.1).compQuadraticMap'
    (P.Q : QuadraticForm P.field.1 (Fin P.rank → P.field.1))

@[simp]
theorem traceQuadraticForm_apply (P : GlobalLatticePresentation)
    (x : Fin P.rank → P.field.1) :
    P.traceQuadraticForm x = Algebra.trace ℚ P.field.1 (P.Q x) :=
  rfl

/-- The associated trace bilinear form is the field trace of the original
associated bilinear form. -/
theorem traceQuadraticForm_associated (P : GlobalLatticePresentation)
    (x y : Fin P.rank → P.field.1) :
    QuadraticMap.associated P.traceQuadraticForm x y =
      Algebra.trace ℚ P.field.1 (QuadraticMap.associated P.Q x y) := by
  simp only [QuadraticMap.associated_apply, traceQuadraticForm_apply,
    Module.End.smul_def,
    QuadraticMap.half_moduleEnd_apply_eq_half_smul, invOf_eq_inv,
    smul_eq_mul, map_sub]
  rw [show (2 : P.field.1)⁻¹ = algebraMap ℚ P.field.1 (2 : ℚ)⁻¹ by
    rw [map_inv₀]
    norm_num]
  simp_rw [← Algebra.smul_def, map_smul]
  simp only [Rat.smul_def]
  ring

/-- The same lattice, regarded as a `ℤ`-submodule of the rational space. -/
def integralRestriction (P : GlobalLatticePresentation) :
    Submodule ℤ (Fin P.rank → P.field.1) :=
  P.L.restrictScalars ℤ

@[simp]
theorem mem_integralRestriction_iff (P : GlobalLatticePresentation)
    (x : Fin P.rank → P.field.1) :
    x ∈ P.integralRestriction ↔ x ∈ P.L :=
  Iff.rfl

/-- The restricted lattice is finitely generated over `ℤ`. -/
theorem integralRestriction_fg (P : GlobalLatticePresentation) :
    P.integralRestriction.FG := by
  exact P.full.fg.restrictScalars

/-- The `ℚ`-span of the restricted lattice is the full rational space. -/
theorem span_integralRestriction_eq_top (P : GlobalLatticePresentation) :
    Submodule.span ℚ (P.integralRestriction :
      Set (Fin P.rank → P.field.1)) = ⊤ := by
  let S : Submodule ℚ (Fin P.rank → P.field.1) :=
    Submodule.span ℚ (P.integralRestriction :
      Set (Fin P.rank → P.field.1))
  have hL : (P.L : Set (Fin P.rank → P.field.1)) ⊆ S := by
    intro x hx
    exact Submodule.subset_span hx
  have hsmul : ∀ (a : P.field.1) (x : Fin P.rank → P.field.1),
      x ∈ S → a • x ∈ S := by
    intro a x hx
    refine Submodule.span_induction
      (p := fun y _hy ↦ a • y ∈ S) ?_ (by simp) ?_ ?_ hx
    · intro z hz
      have ha : a ∈ Submodule.span ℚ
          (Set.range (NumberField.integralBasis P.field.1)) := by
        rw [(NumberField.integralBasis P.field.1).span_eq]
        trivial
      refine Submodule.span_induction
        (p := fun b _hb ↦ b • z ∈ S) ?_ (by simp) ?_ ?_ ha
      · intro b hb
        obtain ⟨i, rfl⟩ := hb
        apply hL
        rw [NumberField.integralBasis_apply]
        exact P.L.smul_mem (NumberField.RingOfIntegers.basis P.field.1 i) hz
      · intro b c _hb _hc hb hc
        simpa [add_smul] using S.add_mem hb hc
      · intro q b _hb hb
        simpa [smul_smul, mul_comm] using S.smul_mem q hb
    · intro y z _hy _hz hy hz
      simpa [smul_add] using S.add_mem hy hz
    · intro q y _hy hy
      simpa only [smul_comm q a] using S.smul_mem q hy
  let T : Submodule P.field.1 (Fin P.rank → P.field.1) :=
    { carrier := S
      zero_mem' := S.zero_mem
      add_mem' := S.add_mem
      smul_mem' := fun a x hx ↦ hsmul a x hx }
  have hT : T = ⊤ := by
    apply top_unique
    rw [← P.full.span_eq_top]
    exact Submodule.span_le.mpr hL
  apply top_unique
  intro x _hx
  change x ∈ S
  change x ∈ T
  rw [hT]
  trivial

/-- The restricted module is a full lattice over the fraction field `ℚ`. -/
theorem integralRestriction_isLattice (P : GlobalLatticePresentation) :
    P.integralRestriction.IsLattice ℚ where
  fg := P.integralRestriction_fg
  span_eq_top := P.span_integralRestriction_eq_top

instance (P : GlobalLatticePresentation) :
    P.integralRestriction.IsLattice ℚ :=
  P.integralRestriction_isLattice

instance (P : GlobalLatticePresentation) :
    Module.Free ℤ P.integralRestriction := inferInstance

/-- Total positivity at every real embedding makes the rational trace form positive definite. -/
theorem traceQuadraticForm_posDef (P : GlobalLatticePresentation) :
    P.traceQuadraticForm.PosDef := by
  letI : NumberField.IsTotallyReal P.field.1 := P.totallyReal
  intro x hx
  have hsum : 0 < ∑ σ : P.field.1 →ₐ[ℚ] ℂ, (σ (P.Q x)).re := by
    apply Finset.sum_pos
    · intro σ _hσ
      let hreal : NumberField.ComplexEmbedding.IsReal σ.toRingHom :=
        NumberField.IsTotallyReal.complexEmbedding_isReal σ.toRingHom
      exact P.positiveDefinite x hx hreal.embedding
    · exact ⟨(IsAlgClosed.lift : P.field.1 →ₐ[ℚ] ℂ), Finset.mem_univ _⟩
  have htrace := trace_eq_sum_embeddings ℂ
    (K := ℚ) (L := P.field.1) (x := P.Q x)
  have hre := congrArg Complex.re htrace
  have hre' :
      ((Algebra.trace ℚ P.field.1 (P.Q x) : ℚ) : ℝ) =
        ∑ σ : P.field.1 →ₐ[ℚ] ℂ, (σ (P.Q x)).re := by
    let q : ℚ := Algebra.trace ℚ P.field.1 (P.Q x)
    calc
      (q : ℝ) = (Complex.ofReal (q : ℝ)).re := by simp
      _ = ((q : ℂ)).re := by rw [Complex.ofReal_ratCast]
      _ = (∑ σ : P.field.1 →ₐ[ℚ] ℂ, σ (P.Q x)).re := hre
      _ = ∑ σ : P.field.1 →ₐ[ℚ] ℂ, (σ (P.Q x)).re := by
        rw [Complex.re_sum]
  have hreal :
      (0 : ℝ) < ((Algebra.trace ℚ P.field.1 (P.Q x) : ℚ) : ℝ) := by
    rw [hre']
    exact hsum
  rw [traceQuadraticForm_apply]
  exact_mod_cast hreal

/-- Rational dimension of the trace space: rank times field degree. -/
theorem traceSpace_finrank (P : GlobalLatticePresentation) :
    Module.finrank ℚ (Fin P.rank → P.field.1) = P.rank * P.degree := by
  rw [← Module.finrank_mul_finrank ℚ P.field.1
    (Fin P.rank → P.field.1)]
  simp [GlobalLatticePresentation.degree, mul_comm]

/-- Install the proved lattice and freeness facts locally when choosing a basis. -/
noncomputable def integralRestrictionBasis (P : GlobalLatticePresentation) :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ P.integralRestriction)
      ℤ P.integralRestriction := by
  exact Module.Free.chooseBasis ℤ P.integralRestriction

/-- The integral basis extended to a rational basis of the full trace space. -/
noncomputable def rationalTraceBasis (P : GlobalLatticePresentation) :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ P.integralRestriction)
      ℚ (Fin P.rank → P.field.1) := by
  exact P.integralRestrictionBasis.extendOfIsLattice ℚ

@[simp]
theorem rationalTraceBasis_apply (P : GlobalLatticePresentation)
    (i : Module.Free.ChooseBasisIndex ℤ P.integralRestriction) :
    P.rationalTraceBasis i = (P.integralRestrictionBasis i).1 := by
  simp [rationalTraceBasis]

/-- Chosen diagonal coefficients for the positive rational trace form. -/
noncomputable def traceDiagonalWeights (P : GlobalLatticePresentation) :
    Fin (Module.finrank ℚ (Fin P.rank → P.field.1)) → ℚ :=
  Classical.choose P.traceQuadraticForm.equivalent_weightedSumSquares

/-- The selected diagonalization is equivalent to the rational trace form. -/
theorem traceDiagonalEquivalent (P : GlobalLatticePresentation) :
    QuadraticMap.Equivalent P.traceQuadraticForm
      (QuadraticMap.weightedSumSquares ℚ P.traceDiagonalWeights) :=
  Classical.choose_spec P.traceQuadraticForm.equivalent_weightedSumSquares

/-- A selected rational isometry from the trace form to its diagonal form. -/
noncomputable def traceDiagonalIsometry (P : GlobalLatticePresentation) :
    P.traceQuadraticForm.IsometryEquiv
      (QuadraticMap.weightedSumSquares ℚ P.traceDiagonalWeights) :=
  Classical.choice P.traceDiagonalEquivalent

@[simp]
theorem traceDiagonalIsometry_map (P : GlobalLatticePresentation)
    (x : Fin P.rank → P.field.1) :
    QuadraticMap.weightedSumSquares ℚ P.traceDiagonalWeights
        (P.traceDiagonalIsometry x) =
      P.traceQuadraticForm x :=
  P.traceDiagonalIsometry.map_app x

/-- Every selected diagonal coefficient is strictly positive. -/
theorem traceDiagonalWeights_pos (P : GlobalLatticePresentation)
    (i : Fin (Module.finrank ℚ (Fin P.rank → P.field.1))) :
    0 < P.traceDiagonalWeights i := by
  classical
  let u : Fin (Module.finrank ℚ (Fin P.rank → P.field.1)) → ℚ :=
    Pi.single i 1
  have hu : u ≠ 0 := by
    intro h
    have hi := congrFun h i
    simp [u] at hi
  have hx : P.traceDiagonalIsometry.symm u ≠ 0 := by
    intro h
    apply hu
    simpa using congrArg P.traceDiagonalIsometry h
  have hpos := P.traceQuadraticForm_posDef
    (P.traceDiagonalIsometry.symm u) hx
  rw [← P.traceDiagonalIsometry_map
    (P.traceDiagonalIsometry.symm u)] at hpos
  simpa [u, QuadraticMap.weightedSumSquares_apply, Pi.single_apply] using hpos

end GlobalLatticePresentation

end

end TraceEuclidean
