import NormEuclidean.ChapterX.CompletedTopology
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Bong.QuadraticSpace.IsometryDeterminant

/-!
# The integral matrix criterion in O'Meara 101:4(i)

For determinant-one or determinant-minus-one transformations, entrywise
integrality of the forward matrix implies integrality of its inverse. It is
therefore equivalent to preserving the integral model spanned by a field
basis. The full orthogonal-group result derives the determinant alternatives
from regularity in characteristic zero. No integral inverse of two is used.
-/

noncomputable section

open scoped TensorProduct

namespace NormEuclidean.IntegralMatrix

open ProperSpinor AdelicOrthogonal

variable {F E ι : Type*} [Field F] [AddCommGroup E] [Module F E]
  [Fintype ι] [DecidableEq ι]

/-- The integral model spanned by a chosen field basis. -/
def model (R : Subring F) (b : Module.Basis ι F E) : Submodule R E :=
  Submodule.span R (Set.range b)

omit [Fintype ι] [DecidableEq ι] in
theorem mem_model_iff (R : Subring F) (b : Module.Basis ι F E) (x : E) :
    x ∈ model R b ↔ ∀ i, b.repr x i ∈ R := by
  have hr : Set.range (algebraMap R F) = (R : Set F) := by
    ext a
    change (∃ r : R, (r : F) = a) ↔ a ∈ R
    exact ⟨by rintro ⟨r, rfl⟩; exact r.2, fun h ↦ ⟨⟨a, h⟩, rfl⟩⟩
  simpa only [model, hr, SetLike.mem_coe] using b.mem_span_iff_repr_mem R x

/-- The adjugate is an integral polynomial in the matrix entries. -/
theorem adjugate_entries_mem (R : Subring F) (A : Matrix ι ι F)
    (hA : ∀ i j, A i j ∈ R) : ∀ i j, A.adjugate i j ∈ R := by
  let B : Matrix ι ι R := fun i j ↦ ⟨A i j, hA i j⟩
  intro i j
  have h : (B.adjugate i j : F) = A.adjugate i j :=
    congrArg (fun M : Matrix ι ι F ↦ M i j) (R.subtype.map_adjugate B)
  exact h ▸ (B.adjugate i j).2

/-- Determinant one makes inverse integrality a consequence of forward integrality. -/
theorem inverse_entries_mem_of_det_one (R : Subring F) (A : Matrix ι ι F)
    (hA : ∀ i j, A i j ∈ R) (hdet : A.det = 1) : ∀ i j, A⁻¹ i j ∈ R := by
  have heq : A⁻¹ = A.adjugate := by
    rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  rw [heq]
  exact adjugate_entries_mem R A hA

theorem inverse_entries_mem_of_det_sign (R : Subring F) (A : Matrix ι ι F)
    (hA : ∀ i j, A i j ∈ R) (hdet : A.det = 1 ∨ A.det = -1) :
    ∀ i j, A⁻¹ i j ∈ R := by
  rcases hdet with hdet | hdet
  · exact inverse_entries_mem_of_det_one R A hA hdet
  · have heq : A⁻¹ = -A.adjugate := by
      simp [Matrix.inv_def, hdet, Ring.inverse_eq_inv]
    rw [heq]
    exact fun i j ↦ R.neg_mem (adjugate_entries_mem R A hA i j)

theorem matrix_symm (b : Module.Basis ι F E) (g : E ≃ₗ[F] E) :
    LinearMap.toMatrixAlgEquiv b g.symm.toLinearMap =
      (LinearMap.toMatrixAlgEquiv b g.toLinearMap)⁻¹ := by
  let u := Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom
    (LinearMap.GeneralLinearGroup.ofLinearEquiv g)
  exact Matrix.coe_units_inv u

theorem matrix_apply (b : Module.Basis ι F E) (g : E ≃ₗ[F] E) (i j : ι) :
    LinearMap.toMatrixAlgEquiv b g.toLinearMap i j = b.repr (g (b j)) i := by
  rw [LinearMap.toMatrixAlgEquiv_apply]
  rfl

omit [Fintype ι] [DecidableEq ι] in
private theorem model_mapsTo (R : Subring F) (b : Module.Basis ι F E)
    (g : E ≃ₗ[F] E) (h : ∀ i, g (b i) ∈ model R b) :
    ∀ x ∈ model R b, g x ∈ model R b := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
  | zero => simpa only [map_zero] using (model R b).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using (model R b).add_mem hx hy
  | smul a x _ hx =>
      simpa only [Subring.smul_def, map_smul] using (model R b).smul_mem a hx

/-- Forward integral entries and determinant one preserve the integral model in both directions. -/
theorem model_preserved_of_integral_matrix (R : Subring F) (b : Module.Basis ι F E)
    (g : E ≃ₗ[F] E)
    (hA : ∀ i j, LinearMap.toMatrixAlgEquiv b g.toLinearMap i j ∈ R)
    (hdet : (LinearMap.toMatrixAlgEquiv b g.toLinearMap).det = 1) :
    ∀ x, g x ∈ model R b ↔ x ∈ model R b := by
  have hf := model_mapsTo R b g (fun j ↦ (mem_model_iff R b _).mpr (by
    intro i
    have h := hA i j
    rw [matrix_apply] at h
    exact h))
  have hiA := inverse_entries_mem_of_det_one R _ hA hdet
  have hi := model_mapsTo R b g.symm (fun j ↦ (mem_model_iff R b _).mpr (by
    intro i
    have h := hiA i j
    rw [← matrix_symm b g] at h
    rw [matrix_apply] at h
    exact h))
  intro x
  exact ⟨fun hx ↦ by simpa only [LinearEquiv.symm_apply_apply] using hi (g x) hx, hf x⟩

theorem model_preserved_of_integral_matrix_of_det_sign
    (R : Subring F) (b : Module.Basis ι F E) (g : E ≃ₗ[F] E)
    (hA : ∀ i j, LinearMap.toMatrixAlgEquiv b g.toLinearMap i j ∈ R)
    (hdet : (LinearMap.toMatrixAlgEquiv b g.toLinearMap).det = 1 ∨
      (LinearMap.toMatrixAlgEquiv b g.toLinearMap).det = -1) :
    ∀ x, g x ∈ model R b ↔ x ∈ model R b := by
  have hf := model_mapsTo R b g (fun j ↦ (mem_model_iff R b _).mpr (by
    intro i
    have h := hA i j
    rw [matrix_apply] at h
    exact h))
  have hiA := inverse_entries_mem_of_det_sign R _ hA hdet
  have hi := model_mapsTo R b g.symm (fun j ↦ (mem_model_iff R b _).mpr (by
    intro i
    have h := hiA i j
    rw [← matrix_symm b g, matrix_apply] at h
    exact h))
  intro x
  exact ⟨fun hx ↦ by simpa only [LinearEquiv.symm_apply_apply] using hi (g x) hx, hf x⟩

variable (Q : QuadraticForm F E)

theorem proper_matrix_det (b : Module.Basis ι F E) (g : properGroup Q) :
    (LinearMap.toMatrixAlgEquiv b g.1.1.toLinearMap).det = 1 := by
  change (LinearMap.toMatrix b b g.1.1.toLinearMap).det = 1
  rw [LinearMap.det_toMatrix]
  have h := congrArg Units.val g.2
  simpa only [determinantHom_apply, LinearEquiv.coe_det, Units.val_one] using h

/-- O'Meara 101:4(i), in the proper group: entrywise integrality is exactly
preservation of the standard integral basis model. -/
theorem mem_properStabilizer_model_iff (R : Subring F) (b : Module.Basis ι F E)
    (g : properGroup Q) :
    g ∈ properStabilizerWithin Q (model R b) ↔
      ∀ i j, LinearMap.toMatrixAlgEquiv b g.1.1.toLinearMap i j ∈ R := by
  constructor
  · intro hg i j
    have hj : b j ∈ model R b := Submodule.subset_span (Set.mem_range_self j)
    have hgj := (hg (b j)).mpr hj
    change g.1.1 (b j) ∈ model R b at hgj
    rw [matrix_apply]
    exact (mem_model_iff R b _).mp hgj i
  · intro hA
    exact model_preserved_of_integral_matrix R b g.1.1 hA (proper_matrix_det Q b g)

section Ambient

variable [CharZero F] [FiniteDimensional F E]

theorem ambient_matrix_det_sign (hQ : Q.polarBilin.Nondegenerate)
    (b : Module.Basis ι F E) (g : ambientGroup Q) :
    (LinearMap.toMatrixAlgEquiv b g.1.toLinearMap).det = 1 ∨
      (LinearMap.toMatrixAlgEquiv b g.1.toLinearMap).det = -1 := by
  have hmat : (LinearMap.toMatrixAlgEquiv b g.1.toLinearMap).det =
      (LinearEquiv.det g.1 : F) := by
    change (LinearMap.toMatrix b b g.1.toLinearMap).det = _
    rw [LinearMap.det_toMatrix, LinearEquiv.coe_det]
  have h := (ambientToBong Q hQ g).det_eq_one_or_neg_one
  change LinearEquiv.det g.1 = 1 ∨ LinearEquiv.det g.1 = (-1 : Fˣ) at h
  rcases h with h | h
  · exact Or.inl (hmat.trans (congrArg Units.val h))
  · exact Or.inr (hmat.trans (congrArg Units.val h))

/-- O'Meara 101:4(i) for the full regular orthogonal group in characteristic
zero. Both proper and improper isometries are included. -/
theorem mem_integralStabilizer_model_iff (hQ : Q.polarBilin.Nondegenerate)
    (R : Subring F) (b : Module.Basis ι F E) (g : ambientGroup Q) :
    g ∈ integralStabilizer Q (model R b) ↔
      ∀ i j, LinearMap.toMatrixAlgEquiv b g.1.toLinearMap i j ∈ R := by
  constructor
  · intro hg i j
    have hj : b j ∈ model R b := Submodule.subset_span (Set.mem_range_self j)
    have hgj : g.1 (b j) ∈ model R b := (hg (b j)).mpr hj
    rw [matrix_apply]
    exact (mem_model_iff R b _).mp hgj i
  · intro hA
    exact model_preserved_of_integral_matrix_of_det_sign R b g.1 hA
      (ambient_matrix_det_sign Q hQ b g)

end Ambient

section Completions

open CompletedIntegralLattice IsDedekindDomain

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

omit [Fintype ι] [DecidableEq ι] in
/-- The completed standard model is exactly the span of the base-changed
field basis over the actual completed integer ring. -/
theorem carrier_model_eq (b : Module.Basis ι K V) :
    carrier R v (model R b) = model (LocalRing R v) (b.baseChange (LocalField R v)) := by
  let P : Submodule (LocalRing R v) (Space (V := V) R v) :=
    model (LocalRing R v) (b.baseChange (LocalField R v))
  change carrier R v (model R b) = P
  have hb (i : ι) : inclusion R v (b i) = b.baseChange (LocalField R v) i := by
    simp only [Module.Basis.baseChange_apply, inclusion, TensorProduct.mk_apply]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        rw [hb]
        exact Submodule.subset_span (Set.mem_range_self i)
    | zero => rw [map_zero]; exact P.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact P.add_mem hx hy
    | smul a x _ hx =>
        rw [inclusion_smul]
        exact P.smul_mem _ hx
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [← hb]
    exact inclusion_mem R v (model R b) (Submodule.subset_span (Set.mem_range_self i))

variable [Invertible (2 : K)]

/-- The matrix integrality criterion applies to the actual completed global model. -/
theorem mem_completedModel_iff_integralEntries (P : QuadraticForm K V)
    (b : Module.Basis ι K V) (g : properGroup (form R v P)) :
    g ∈ properStabilizerWithin (form R v P) (carrier R v (model R b)) ↔
      ∀ i j, LinearMap.toMatrixAlgEquiv (b.baseChange (LocalField R v))
        g.1.1.toLinearMap i j ∈ LocalRing R v := by
  rw [carrier_model_eq R v b]
  exact mem_properStabilizer_model_iff (form R v P) (LocalRing R v)
    (b.baseChange (LocalField R v)) g

/-- At an actual finite place, integral entries mean that each entry has
valuation at most one. The statement includes dyadic places. -/
theorem mem_completedModel_iff_valuation_le_one (P : QuadraticForm K V)
    (b : Module.Basis ι K V) (g : properGroup (form R v P)) :
    g ∈ properStabilizerWithin (form R v P) (carrier R v (model R b)) ↔
      ∀ i j, Valued.v (LinearMap.toMatrixAlgEquiv (b.baseChange (LocalField R v))
        g.1.1.toLinearMap i j) ≤ 1 := by
  rw [mem_completedModel_iff_integralEntries R v P b g]
  rfl

variable [CharZero K] [FiniteDimensional K V]

/-- The same completed criterion for the full regular orthogonal group. -/
theorem mem_completedModel_ambient_iff_integralEntries (P : QuadraticForm K V)
    (hP : P.polarBilin.Nondegenerate) (b : Module.Basis ι K V)
    (g : ambientGroup (form R v P)) :
    g ∈ integralStabilizer (form R v P) (carrier R v (model R b)) ↔
      ∀ i j, LinearMap.toMatrixAlgEquiv (b.baseChange (LocalField R v))
        g.1.toLinearMap i j ∈ LocalRing R v := by
  rw [carrier_model_eq R v b]
  exact mem_integralStabilizer_model_iff (form R v P)
    (form_polarBilin_nondegenerate R v P hP) (LocalRing R v)
    (b.baseChange (LocalField R v)) g

end Completions

end NormEuclidean.IntegralMatrix
