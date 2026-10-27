import NormEuclidean.ChapterX.CompletedTopology

/-!
# Scalar multiples of full modules and their actual completed carriers

The scalar may be fractional and the module need not have a basis over
the integral ring. A local unit scalar leaves the completed carrier fixed.
-/

noncomputable section

namespace NormEuclidean.ScalarMultipleModule

open IsDedekindDomain CompletedIntegralLattice
open scoped TensorProduct

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (R : Subring K)

/-- Multiplication by a field scalar, restricted to the coefficient subring. -/
def map (a : K) : V →ₗ[R] V := (a • (LinearMap.id : V →ₗ[K] V)).restrictScalars R

@[simp] theorem map_apply (a : K) (x : V) : map (V := V) R a x = a • x := rfl

/-- The actual scalar multiple of a global module. -/
def scale (a : K) (L : Submodule R V) : Submodule R V := L.map (map R a)

@[simp] theorem scale_one (L : Submodule R V) : scale R 1 L = L := by
  have hmap : map (V := V) R 1 = LinearMap.id := by
    ext x
    exact one_smul K x
  rw [scale, hmap, Submodule.map_id]

/-- Successive scalar multiples compose by multiplication in the field. -/
theorem scale_mul (a b : K) (L : Submodule R V) :
    scale R a (scale R b L) = scale R (a * b) L := by
  rw [scale, scale, ← Submodule.map_comp, scale]
  congr 1
  ext x
  exact (mul_smul a b x).symm

/-- Finite generation is preserved even for a fractional scalar. -/
theorem scale_fg (a : K) (L : Submodule R V) (hL : L.FG) : (scale R a L).FG :=
  hL.map _

/-- A nonzero scalar preserves fullness over the fraction field. -/
theorem scale_full (a : K) (ha : a ≠ 0) (L : Submodule R V)
    (hL : Submodule.span K (L : Set V) = ⊤) :
    Submodule.span K (scale R a L : Set V) = ⊤ := by
  rw [scale, Submodule.map_coe]
  change Submodule.span K ((a • (LinearMap.id : V →ₗ[K] V)) '' (L : Set V)) = ⊤
  rw [Submodule.span_image, hL, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (LinearEquiv.smulOfNeZero K V a ha).surjective

variable [IsDedekindDomain R] [IsFractionRing R K] (p : HeightOneSpectrum R)

/-- Every completed module vector scales into the corresponding completed scalar multiple. -/
theorem smul_mem_carrier (a : K) (L : Submodule R V)
    {x : Space (V := V) R p} (hx : x ∈ carrier R p L) :
    algebraMap K (LocalField R p) a • x ∈ carrier R p (scale R a L) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨y, hy, rfl⟩ := hy
      have h := inclusion_mem R p (scale R a L) (show a • y ∈ scale R a L from
        ⟨y, hy, rfl⟩)
      rw [(inclusion R p).map_smul, ← IsScalarTower.algebraMap_smul
        (R := K) (A := LocalField R p)] at h
      exact h
  | zero => simpa only [smul_zero] using (carrier R p (scale R a L)).zero_mem
  | add x y _ _ hx hy =>
      simpa only [smul_add] using (carrier R p (scale R a L)).add_mem hx hy
  | smul c x _ hx =>
      change algebraMap K (LocalField R p) a • ((c : LocalField R p) • x) ∈ _
      rw [smul_comm]
      exact (carrier R p (scale R a L)).smul_mem c hx

/-- A completed vector belongs to the divided module exactly when its multiple is integral. -/
theorem mem_carrier_divide_iff (d : K) (hd : d ≠ 0) (L : Submodule R V)
    (x : Space (V := V) R p) :
    x ∈ carrier R p (scale R d⁻¹ L) ↔
      algebraMap K (LocalField R p) d • x ∈ carrier R p L := by
  have hdF : algebraMap K (LocalField R p) d ≠ 0 := (map_ne_zero _).mpr hd
  constructor
  · intro hx
    have h := smul_mem_carrier R p d (scale R d⁻¹ L) hx
    simpa only [scale_mul, mul_inv_cancel₀ hd, scale_one] using h
  · intro hx
    have h := smul_mem_carrier R p d⁻¹ L hx
    simpa only [map_inv₀, smul_smul, inv_mul_cancel₀ hdF, one_smul] using h

/-- A scalar integral at this place gives containment of completed carriers. -/
theorem carrier_scale_le (a : K) (ha : algebraMap K (LocalField R p) a ∈ LocalRing R p)
    (L : Submodule R V) : carrier R p (scale R a L) ≤ carrier R p L := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
  have h := (carrier R p L).smul_mem
    (⟨algebraMap K (LocalField R p) a, ha⟩ : LocalRing R p) (inclusion_mem R p L hy)
  change algebraMap K (LocalField R p) a • inclusion R p y ∈ carrier R p L at h
  change inclusion R p (a • y) ∈ carrier R p L
  rw [(inclusion R p).map_smul, ← IsScalarTower.algebraMap_smul
    (R := K) (A := LocalField R p)]
  exact h

/-- A local unit scalar leaves the actual completed module unchanged. -/
theorem carrier_scale_eq (a : K) (ha : a ≠ 0)
    (hint : algebraMap K (LocalField R p) a ∈ LocalRing R p)
    (hinv : algebraMap K (LocalField R p) a⁻¹ ∈ LocalRing R p) (L : Submodule R V) :
    carrier R p (scale R a L) = carrier R p L := by
  apply le_antisymm (carrier_scale_le R p a hint L)
  have h := carrier_scale_le R p a⁻¹ hinv (scale R a L)
  simpa only [scale_mul, inv_mul_cancel₀ ha, scale_one] using h

end NormEuclidean.ScalarMultipleModule
