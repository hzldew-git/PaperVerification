import NormEuclidean.ChapterX.IntegralDual
import NormEuclidean.ChapterX.WittExtension

/-!
# The projected-complement step in O'Meara 103:4

For a lattice of integral half-polar scale containing a nonzero-value vector,
the scaled orthogonal projection gives an actual lattice on its complement.
Its sum with the original vector bounds the source between two finite modules.
The scalar quotient bound is proved without a basis of the integral lattice.
-/

noncomputable section

namespace NormEuclidean.ProjectedComplement

open Module QuadraticMap

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

/-- The orthogonal complement in the literal half-polar convention. -/
def complement (y : V) : Submodule K V := (halfPolar Q).orthogonal (K ∙ y)

/-- The numerator of orthogonal projection is in the actual complement. -/
theorem projection_mem_complement (y x : V) :
    Q y • x - halfPolar Q x y • y ∈ complement Q y := by
  rw [complement, LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker]
  change halfPolar Q y (Q y • x - halfPolar Q x y • y) = 0
  simp only [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right,
    halfPolar_self, halfPolar_comm Q y x]
  ring

/-- Scaled orthogonal projection as an actual field-linear map. -/
def projection (y : V) : V →ₗ[K] complement Q y :=
  ((Q y) • (LinearMap.id : V →ₗ[K] V) - ((halfPolar Q).flip y).smulRight y).codRestrict
    (complement Q y) (projection_mem_complement Q y)

@[simp] theorem projection_apply (y x : V) :
    (projection Q y x : V) = Q y • x - halfPolar Q x y • y := rfl

/-- On the orthogonal complement the numerator is multiplication by the value. -/
theorem projection_on_complement (y : V) (x : complement Q y) :
    (projection Q y (x : V) : V) = Q y • (x : V) := by
  have hx : halfPolar Q y (x : V) = 0 :=
    x.property y (Submodule.subset_span (Set.mem_singleton y))
  rw [projection_apply, halfPolar_comm Q (x : V) y, hx, zero_smul, sub_zero]

/-- A nonzero value makes the scaled projection surjective. -/
theorem projection_surjective (y : V) (hy : Q y ≠ 0) :
    Function.Surjective (projection Q y) := by
  intro x
  refine ⟨(Q y)⁻¹ • (x : V), ?_⟩
  apply Subtype.ext
  simp only [map_smul, Submodule.coe_smul, projection_on_complement,
    smul_smul, inv_mul_cancel₀ hy, one_smul]

/-- Integral scale is the exact premise making the projected vectors integral. -/
theorem projection_mem_lattice (L : Lattice (integerSubring K) Q) (y : V)
    (hy : y ∈ L.carrier) (hscale : L.scaleIdeal ≤ 1) (x : V) (hx : x ∈ L.carrier) :
    (projection Q y x : V) ∈ L.carrier := by
  have hxy : halfPolar Q x y ∈ integerSubring K :=
    (IntegralDual.mem_dual Q L.carrier x).mp
      ((IntegralDual.le_dual_iff_scale_integral Q L).mpr hscale hx) y hy
  rw [projection_apply]
  exact L.carrier.sub_mem
    (L.carrier.smul_mem (⟨Q y, L.integral y hy⟩ : integerSubring K) hx)
    (L.carrier.smul_mem (⟨halfPolar Q x y, hxy⟩ : integerSubring K) hy)

/-- The actual projected integral module on the complement. -/
def projectedCarrier (L : Lattice (integerSubring K) Q) (y : V) :
    Submodule (integerSubring K) (complement Q y) :=
  L.carrier.map ((projection Q y).restrictScalars (integerSubring K))

/-- The projected module is a finite full norm-integral lattice on the complement. -/
def projectedLattice (L : Lattice (integerSubring K) Q) (y : V)
    (hy : y ∈ L.carrier) (hscale : L.scaleIdeal ≤ 1) (hy0 : Q y ≠ 0) :
    Lattice (integerSubring K) (Q.comp (complement Q y).subtype) where
  carrier := projectedCarrier Q L y
  finite := L.finite.map _
  full := by
    rw [projectedCarrier, Submodule.map_coe]
    change Submodule.span K (projection Q y '' (L.carrier : Set V)) = ⊤
    rw [Submodule.span_image, L.full, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (projection_surjective Q y hy0)
  integral := by
    rintro _ ⟨x, hx, rfl⟩
    exact L.integral _ (projection_mem_lattice Q L y hy hscale x hx)

/-- Add the fixed original line to the projected module inside the original space. -/
def splitCarrier (L : Lattice (integerSubring K) Q) (y : V) :
    Submodule (integerSubring K) V :=
  Submodule.span (integerSubring K) {y} ⊔
    (projectedCarrier Q L y).map ((complement Q y).subtype.restrictScalars (integerSubring K))

/-- The constructed split submodule is contained in the source lattice. -/
theorem splitCarrier_le (L : Lattice (integerSubring K) Q) (y : V)
    (hy : y ∈ L.carrier) (hscale : L.scaleIdeal ≤ 1) : splitCarrier Q L y ≤ L.carrier := by
  apply sup_le
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hy)
  · rintro _ ⟨u, ⟨x, hx, rfl⟩, rfl⟩
    exact projection_mem_lattice Q L y hy hscale x hx

/-- Multiplication by the represented value sends the entire source into the split module. -/
theorem value_smul_mem_splitCarrier (L : Lattice (integerSubring K) Q) (y : V)
    (hy : y ∈ L.carrier) (hscale : L.scaleIdeal ≤ 1) (x : V) (hx : x ∈ L.carrier) :
    Q y • x ∈ splitCarrier Q L y := by
  have hxy : halfPolar Q x y ∈ integerSubring K :=
    (IntegralDual.mem_dual Q L.carrier x).mp
      ((IntegralDual.le_dual_iff_scale_integral Q L).mpr hscale hx) y hy
  have hline : halfPolar Q x y • y ∈ Submodule.span (integerSubring K) {y} :=
    (Submodule.span (integerSubring K) {y}).smul_mem
      (⟨halfPolar Q x y, hxy⟩ : integerSubring K) (Submodule.subset_span (Set.mem_singleton y))
  have hperp : (projection Q y x : V) ∈
      (projectedCarrier Q L y).map
        ((complement Q y).subtype.restrictScalars (integerSubring K)) :=
    ⟨projection Q y x, ⟨x, hx, rfl⟩, rfl⟩
  have hsum : Q y • x = halfPolar Q x y • y + (projection Q y x : V) := by
    rw [projection_apply]
    module
  rw [hsum]
  exact Submodule.mem_sup.mpr ⟨_, hline, _, hperp, rfl⟩

/-- The split module is full because it contains a nonzero scalar multiple of the source. -/
theorem splitCarrier_full (L : Lattice (integerSubring K) Q) (y : V)
    (hy : y ∈ L.carrier) (hscale : L.scaleIdeal ≤ 1) (hy0 : Q y ≠ 0) :
    Submodule.span K (splitCarrier Q L y : Set V) = ⊤ := by
  apply top_unique
  rw [← L.full]
  apply Submodule.span_le.mpr
  intro x hx
  change x ∈ Submodule.span K (splitCarrier Q L y : Set V)
  have h := (Submodule.span K (splitCarrier Q L y : Set V)).smul_mem (Q y)⁻¹
    (Submodule.subset_span (value_smul_mem_splitCarrier Q L y hy hscale x hx))
  simpa only [smul_smul, inv_mul_cancel₀ hy0, one_smul] using h

/-- The intermediate split object is itself an actual lattice. -/
def splitLattice (L : Lattice (integerSubring K) Q) (y : V)
    (hy : y ∈ L.carrier) (hscale : L.scaleIdeal ≤ 1) (hy0 : Q y ≠ 0) :
    Lattice (integerSubring K) Q where
  carrier := splitCarrier Q L y
  finite := (Submodule.fg_span (Set.finite_singleton y)).sup ((L.finite.map _).map _)
  full := splitCarrier_full Q L y hy hscale hy0
  integral := fun x hx ↦ L.integral x (splitCarrier_le Q L y hy hscale hx)

/-- The projection quotient is finite, with annihilator the actual represented value. -/
theorem finite_projection_quotient (L : Lattice (integerSubring K) Q) (y : V)
    (hy : y ∈ L.carrier) (hscale : L.scaleIdeal ≤ 1) (hy0 : Q y ≠ 0) :
    Finite (L.carrier ⧸ (splitCarrier Q L y).comap L.carrier.subtype) := by
  let a : integerSubring K := ⟨Q y, L.integral y hy⟩
  have ha : a ≠ 0 := fun h ↦ hy0 (congrArg Subtype.val h)
  letI : Ring.HasFiniteQuotients (integerSubring K) :=
    inferInstanceAs (Ring.HasFiniteQuotients (NumberField.RingOfIntegers K))
  letI : Finite ((integerSubring K) ⧸ Ideal.span {a}) :=
    Ring.HasFiniteQuotients.finiteQuotient (by simpa using ha)
  exact LatticeInterval.finite_quotient_of_scalar_bound (splitCarrier Q L y) L.carrier
    L.finite a (fun x hx ↦ value_smul_mem_splitCarrier Q L y hy hscale x hx)

variable [FiniteDimensional K V]

/-- The regular complement has dimension one less than the original space. -/
theorem complement_finrank (y : V) (hy0 : Q y ≠ 0) :
    Module.finrank K (complement Q y) + 1 = Module.finrank K V := by
  have hy : y ≠ 0 := by intro h; exact hy0 (h ▸ Q.map_zero)
  have hyy : halfPolar Q y y ≠ 0 := by simpa only [halfPolar_self] using hy0
  have h := Submodule.finrank_add_eq_of_isCompl
    (LinearMap.BilinForm.isCompl_span_singleton_orthogonal hyy)
  rw [finrank_span_singleton hy] at h
  exact (add_comm _ _).trans h

/-- The complement used for descent is regular for a nonzero represented value. -/
theorem complement_regular (hQ : Q.polarBilin.Nondegenerate) (y : V) (hy0 : Q y ≠ 0) :
    (Q.comp (complement Q y).subtype).polarBilin.Nondegenerate := by
  have hB := (SpinorBridge.quadraticSpace Q hQ).nondegenerate
  have hrefl := (SpinorBridge.quadraticSpace Q hQ).isSymm.isRefl
  have hyy : halfPolar Q y y ≠ 0 := by simpa only [halfPolar_self] using hy0
  have hcompl := LinearMap.BilinForm.isCompl_span_singleton_orthogonal hyy
  have hBU : ((halfPolar Q).restrict (complement Q y)).Nondegenerate := by
    apply (halfPolar Q).nondegenerate_restrict_of_disjoint_orthogonal hrefl
    change Disjoint ((halfPolar Q).orthogonal (K ∙ y))
      ((halfPolar Q).orthogonal ((halfPolar Q).orthogonal (K ∙ y)))
    rw [(halfPolar Q).orthogonal_orthogonal hB hrefl]
    exact hcompl.disjoint.symm
  constructor
  · intro x hx
    apply hBU.1 x
    intro z
    change (2 : K)⁻¹ * (Q.comp (complement Q y).subtype).polarBilin x z = 0
    rw [hx z, mul_zero]
  · intro z hz
    apply hBU.2 z
    intro x
    change (2 : K)⁻¹ * (Q.comp (complement Q y).subtype).polarBilin x z = 0
    rw [hz x, mul_zero]

end NormEuclidean.ProjectedComplement
