import NormEuclidean.GeneralContent
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Functoriality, homogeneity, and direct sums of intrinsic content

These are Proposition 2.1(iii) and (iv), for arbitrary finitely generated
submodules of vector spaces over a fraction field. No free basis is chosen.
-/

namespace NormEuclidean.GeneralContent

open scoped nonZeroDivisors

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable {R : Subring K} (L : Submodule R V) (L' : Submodule R W)

/-- Coefficients are preserved by every lattice-preserving ambient equivalence. -/
theorem coefficientSubmodule_equiv (g : V ≃ₗ[K] W)
    (hg : ∀ x, g x ∈ L' ↔ x ∈ L) (x : V) :
    coefficientSubmodule L' (g x) = coefficientSubmodule L x := by
  ext a
  change a • g x ∈ L' ↔ a • x ∈ L
  rw [← g.map_smul]
  exact hg (a • x)

/-- The coefficient of a pair is the intersection of its component coefficients. -/
theorem coefficientSubmodule_prod (x : V) (y : W) :
    coefficientSubmodule (L.prod L') (x, y) =
      coefficientSubmodule L x ⊓ coefficientSubmodule L' y := by
  ext a
  rfl

variable [IsFractionRing R K]

/-- Genuine coefficient ideals, rather than a choice of representatives, are invariant. -/
theorem coefficientIdeal_equiv (hL : L.FG) (hL' : L'.FG)
    (g : V ≃ₗ[K] W) (hg : ∀ x, g x ∈ L' ↔ x ∈ L)
    (x : V) (hx : x ≠ 0) :
    coefficientIdeal L' hL' (g x) (g.map_ne_zero_iff.mpr hx) =
      coefficientIdeal L hL x hx := by
  apply FractionalIdeal.coeToSubmodule_injective
  exact coefficientSubmodule_equiv L L' g hg x

/-- Proposition 2.1(iv), including the zero vector, for ambient equivalences. -/
theorem contentIdeal_equiv (hL : L.FG) (hL' : L'.FG)
    (g : V ≃ₗ[K] W) (hg : ∀ x, g x ∈ L' ↔ x ∈ L) (x : V) :
    contentIdeal L' hL' (g x) = contentIdeal L hL x := by
  by_cases hx : x = 0
  · subst x
    simp
  · rw [contentIdeal_of_ne_zero L hL x hx,
      contentIdeal_of_ne_zero L' hL' (g x) (g.map_ne_zero_iff.mpr hx),
      coefficientIdeal_equiv L L' hL hL' g hg x hx]

/-- The localization extension carries the lattice onto its target lattice. -/
theorem ambientEquiv_mem_iff
    (hfull : Submodule.span K (L : Set V) = ⊤)
    (hfull' : Submodule.span K (L' : Set W) = ⊤)
    (φ : L ≃ₗ[R] L') (x : V) :
    ScalarExtension.ambientEquiv L L' hfull hfull' φ x ∈ L' ↔ x ∈ L := by
  let g := ScalarExtension.ambientEquiv L L' hfull hfull' φ
  constructor
  · intro hx
    let y : L' := ⟨g x, hx⟩
    have h : g (φ.symm y : V) = g x := by
      change ScalarExtension.ambientEquiv L L' hfull hfull' φ (φ.symm y : V) = g x
      rw [ScalarExtension.ambientEquiv_apply, φ.apply_symm_apply]
    have heq : (φ.symm y : V) = x := g.injective h
    rw [← heq]
    exact (φ.symm y).property
  · intro hx
    have h := ScalarExtension.ambientEquiv_apply L L' hfull hfull' φ ⟨x, hx⟩
    rw [h]
    exact (φ ⟨x, hx⟩).property

/-- Proposition 2.1(iv) in its original module-isomorphism formulation. -/
theorem contentIdeal_moduleEquiv (hL : L.FG) (hL' : L'.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤)
    (hfull' : Submodule.span K (L' : Set W) = ⊤)
    (φ : L ≃ₗ[R] L') (x : V) :
    contentIdeal L' hL' (ScalarExtension.ambientEquiv L L' hfull hfull' φ x) =
      contentIdeal L hL x :=
  contentIdeal_equiv L L' hL hL' _ (ambientEquiv_mem_iff L L' hfull hfull' φ) x

/-- Nonzero scaling divides the coefficient ideal by the principal scalar ideal. -/
theorem coefficientIdeal_smul (hL : L.FG) (a : K) (ha : a ≠ 0)
    (x : V) (hx : x ≠ 0) :
    coefficientIdeal L hL (a • x) (smul_ne_zero ha hx) =
      FractionalIdeal.spanSingleton R⁰ a⁻¹ * coefficientIdeal L hL x hx := by
  apply FractionalIdeal.eq_spanSingleton_mul.mpr
  constructor
  · intro b hb
    refine ⟨a * b, ?_, ?_⟩
    · change (a * b) • x ∈ L
      rw [mul_comm a b, mul_smul]
      exact hb
    · rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  · intro b hb
    change (a⁻¹ * b) • (a • x) ∈ L
    have heq : (a⁻¹ * b) * a = b := by
      rw [mul_right_comm, inv_mul_cancel₀ ha, one_mul]
    rw [smul_smul, heq]
    exact hb

/-- Proposition 2.1(iii): content is homogeneous, including zero scalars and vectors. -/
theorem contentIdeal_smul [IsDedekindDomain R] (hL : L.FG) (a : K) (x : V) :
    contentIdeal L hL (a • x) =
      FractionalIdeal.spanSingleton R⁰ a * contentIdeal L hL x := by
  by_cases ha : a = 0
  · subst a
    simp
  by_cases hx : x = 0
  · subst x
    simp
  rw [contentIdeal_of_ne_zero L hL (a • x) (smul_ne_zero ha hx),
    coefficientIdeal_smul L hL a ha x hx,
    mul_inv, FractionalIdeal.spanSingleton_inv, inv_inv,
    contentIdeal_of_ne_zero L hL x hx]

/-- Inverting a sum is intersection of inverses, with nonzero summands. -/
theorem fractionalIdeal_inv_add (I J : FractionalIdeal R⁰ K)
    (hI : I ≠ 0) (hJ : J ≠ 0) : (I + J)⁻¹ = I⁻¹ ⊓ J⁻¹ := by
  have hIJ : I + J ≠ 0 := by
    intro h
    apply hI
    apply le_antisymm _ (FractionalIdeal.zero_le _)
    exact (show I ≤ I + J from le_sup_left).trans (le_of_eq h)
  apply le_antisymm
  · exact le_inf (FractionalIdeal.inv_anti_mono hI hIJ le_sup_left)
      (FractionalIdeal.inv_anti_mono hJ hIJ le_sup_right)
  · intro a ha
    apply (FractionalIdeal.mem_inv_iff hIJ).mpr
    intro b hb
    obtain ⟨i, hi, j, hj, rfl⟩ := (FractionalIdeal.mem_add I J b).mp hb
    rw [mul_add]
    exact (1 : FractionalIdeal R⁰ K).1.add_mem
      ((FractionalIdeal.mem_inv_iff hI).mp ha.1 i hi)
      ((FractionalIdeal.mem_inv_iff hJ).mp ha.2 j hj)

/-- In a Dedekind domain, inverse interchanges nonzero intersection and sum. -/
theorem fractionalIdeal_inv_inf [IsDedekindDomain R]
    (I J : FractionalIdeal R⁰ K) (hI : I ≠ 0) (hJ : J ≠ 0) :
    (I ⊓ J)⁻¹ = I⁻¹ + J⁻¹ := by
  have h := fractionalIdeal_inv_add I⁻¹ J⁻¹ (inv_ne_zero hI) (inv_ne_zero hJ)
  simpa only [inv_inv] using congrArg Inv.inv h.symm

/-- Content of a pair with a zero first component. -/
@[simp] theorem contentIdeal_zero_prod (hL : L.FG) (hL' : L'.FG) (y : W) :
    contentIdeal (L.prod L') (hL.prod hL') (0, y) = contentIdeal L' hL' y := by
  by_cases hy : y = 0
  · subst y
    change contentIdeal (L.prod L') (hL.prod hL') (0 : V × W) = _
    rw [contentIdeal_zero, contentIdeal_zero]
  have hpair : ((0 : V), y) ≠ 0 := fun h => hy (congrArg Prod.snd h)
  rw [contentIdeal_of_ne_zero _ _ _ hpair, contentIdeal_of_ne_zero _ _ _ hy]
  congr 1
  apply FractionalIdeal.coeToSubmodule_injective
  change coefficientSubmodule (L.prod L') (0, y) = coefficientSubmodule L' y
  rw [coefficientSubmodule_prod, coefficientSubmodule_zero, top_inf_eq]

/-- Content of a pair with a zero second component. -/
@[simp] theorem contentIdeal_prod_zero (hL : L.FG) (hL' : L'.FG) (x : V) :
    contentIdeal (L.prod L') (hL.prod hL') (x, 0) = contentIdeal L hL x := by
  by_cases hx : x = 0
  · subst x
    change contentIdeal (L.prod L') (hL.prod hL') (0 : V × W) = _
    rw [contentIdeal_zero, contentIdeal_zero]
  have hpair : (x, (0 : W)) ≠ 0 := fun h => hx (congrArg Prod.fst h)
  rw [contentIdeal_of_ne_zero _ _ _ hpair, contentIdeal_of_ne_zero _ _ _ hx]
  congr 1
  apply FractionalIdeal.coeToSubmodule_injective
  change coefficientSubmodule (L.prod L') (x, 0) = coefficientSubmodule L x
  rw [coefficientSubmodule_prod, coefficientSubmodule_zero, inf_top_eq]

/-- Proposition 2.1(iii): the content of a direct-sum vector is the sum of contents. -/
theorem contentIdeal_prod [IsDedekindDomain R]
    (hL : L.FG) (hL' : L'.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤)
    (hfull' : Submodule.span K (L' : Set W) = ⊤)
    (x : V) (y : W) :
    contentIdeal (L.prod L') (hL.prod hL') (x, y) =
      contentIdeal L hL x + contentIdeal L' hL' y := by
  by_cases hx : x = 0
  · subst x
    rw [contentIdeal_zero, zero_add]
    exact contentIdeal_zero_prod L L' hL hL' y
  by_cases hy : y = 0
  · subst y
    rw [contentIdeal_zero, add_zero]
    exact contentIdeal_prod_zero L L' hL hL' x
  have hpair : (x, y) ≠ 0 := fun h => hx (congrArg Prod.fst h)
  have hcoeff : coefficientIdeal (L.prod L') (hL.prod hL') (x, y) hpair =
      coefficientIdeal L hL x hx ⊓ coefficientIdeal L' hL' y hy := by
    apply FractionalIdeal.coeToSubmodule_injective
    exact coefficientSubmodule_prod L L' x y
  rw [contentIdeal_of_ne_zero _ _ _ hpair, hcoeff,
    fractionalIdeal_inv_inf _ _ (coefficientIdeal_ne_zero L hL hfull x hx)
      (coefficientIdeal_ne_zero L' hL' hfull' y hy),
    contentIdeal_of_ne_zero L hL x hx, contentIdeal_of_ne_zero L' hL' y hy]

end NormEuclidean.GeneralContent
