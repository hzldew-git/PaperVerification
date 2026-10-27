import NormEuclidean.ChapterX.ModulePseudoBasis
import NormEuclidean.ChapterX.ModuleGenusPatching
import NormEuclidean.ChapterX.IntegralDual
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Biduality for finite full number-field modules

The pairing with a regular bilinear form identifies the actual integral dual
with the module dual. Extension of linear functionals is constructed by
localization. Projectivity and reflexivity then give integral biduality,
including nonfree modules and fractional quadratic values.
-/

noncomputable section

namespace NormEuclidean.IntegralBiduality

open Module LinearMap.BilinForm
open scoped nonZeroDivisors

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
variable (B : LinearMap.BilinForm K V)

omit [NumberField K] in
/-- The unit coefficient module is full over the fraction field. -/
theorem coefficient_module_full :
    Submodule.span K ((1 : Submodule (integerSubring K) K) : Set K) = ⊤ := by
  apply top_unique
  intro x _
  have hone : (1 : K) ∈ (1 : Submodule (integerSubring K) K) :=
    Submodule.mem_one.mpr ⟨1, map_one (algebraMap (integerSubring K) K)⟩
  have h := (Submodule.span K ((1 : Submodule (integerSubring K) K) : Set K)).smul_mem x
    (Submodule.subset_span hone)
  simpa only [smul_eq_mul, mul_one] using h

/-- Any finite source has a full integral dual, even if the source's
quadratic or bilinear values are fractional. -/
theorem dual_full (L : Submodule (integerSubring K) V) (hLfg : L.FG) :
    Submodule.span K (B.dualSubmodule L : Set V) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨d, hd0, hd⟩ := exists_lattice_denominator
    (L.map ((B x).restrictScalars (integerSubring K)))
    (1 : Submodule (integerSubring K) K) (hLfg.map _) (coefficient_module_full (K := K))
  have hdx : (d : K) • x ∈ B.dualSubmodule L := by
    intro y hy
    rw [LinearMap.BilinForm.smul_left]
    exact hd _ ⟨y, hy, rfl⟩
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd0
  have h := (Submodule.span K (B.dualSubmodule L : Set V)).smul_mem (d : K)⁻¹
    (Submodule.subset_span hdx)
  simpa only [smul_smul, inv_mul_cancel₀ hdK, one_smul] using h

/-- The integral dual of a finite full module is finitely generated.
A field basis is cleared into the source; no integral basis is assumed. -/
theorem dual_fg (hB : B.Nondegenerate) (L : Submodule (integerSubring K) V)
    (hLfg : L.FG) (hL : Submodule.span K (L : Set V) = ⊤) : (B.dualSubmodule L).FG := by
  classical
  letI := ModuleGenusPatching.finiteDimensional_of_fg_full (integerSubring K) L hLfg hL
  let b := Module.finBasis K V
  obtain ⟨d, hd0, hd⟩ := exists_common_denominator L hL (Finset.univ.image b)
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd0
  let b' := b.unitsSMul (fun _ ↦ Units.mk0 (d : K) hdK)
  have hb' (i : Fin (Module.finrank K V)) : b' i ∈ L := by
    simpa only [b', Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0] using
      hd (b i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hle : Submodule.span (integerSubring K) (Set.range b') ≤ L :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hb' i)
  have hdual : B.dualSubmodule L ≤
      B.dualSubmodule (Submodule.span (integerSubring K) (Set.range b')) :=
    fun _ hx y hy ↦ hx y (hle hy)
  rw [B.dualSubmodule_span_of_basis hB b'] at hdual
  exact (Submodule.fg_span (Set.finite_range (B.dualBasis hB b'))).of_le hdual

/-- Every integral functional on a full module is represented by an actual
vector in its bilinear integral dual. -/
theorem dual_pairing_surjective (hB : B.Nondegenerate)
    (L : Submodule (integerSubring K) V) (hLfg : L.FG)
    (hL : Submodule.span K (L : Set V) = ⊤) :
    Function.Surjective (B.dualSubmoduleToDual L) := by
  letI := ModuleGenusPatching.finiteDimensional_of_fg_full (integerSubring K) L hLfg hL
  letI := ScalarExtension.localizedSubtype L hL
  letI : IsLocalizedModule (integerSubring K)⁰
      (LinearMap.id : K →ₗ[integerSubring K] K) :=
    isLocalizedModule_id (integerSubring K)⁰ K K
  intro f
  let fK : L →ₗ[integerSubring K] K :=
    (Algebra.linearMap (integerSubring K) K).comp f
  let g : V →ₗ[K] K := IsLocalizedModule.mapExtendScalars (integerSubring K)⁰ L.subtype
    (LinearMap.id : K →ₗ[integerSubring K] K) K fK
  let x := (B.toDual hB).symm g
  have hx (y : L) : B x y.1 = algebraMap (integerSubring K) K (f y) := by
    have h : B x = g := (B.toDual hB).apply_symm_apply g
    rw [LinearMap.congr_fun h]
    exact IsLocalizedModule.map_apply (integerSubring K)⁰ L.subtype
      (LinearMap.id : K →ₗ[integerSubring K] K) fK y
  have hint : x ∈ B.dualSubmodule L := by
    intro y hy
    exact Submodule.mem_one.mpr ⟨f ⟨y, hy⟩, (hx ⟨y, hy⟩).symm⟩
  refine ⟨⟨x, hint⟩, ?_⟩
  apply LinearMap.ext
  intro y
  apply Subtype.val_injective
  exact (B.dualSubmoduleParing_spec ⟨x, hint⟩ y).trans (hx y)

/-- The actual integral pairing gives an equivalence with the module dual. -/
def dualPairingEquiv (hB : B.Nondegenerate) (L : Submodule (integerSubring K) V)
    (hLfg : L.FG) (hL : Submodule.span K (L : Set V) = ⊤) :
    B.dualSubmodule L ≃ₗ[integerSubring K] Module.Dual (integerSubring K) L :=
  LinearEquiv.ofBijective (B.dualSubmoduleToDual L)
    ⟨B.dualSubmoduleToDual_injective hB L hL, dual_pairing_surjective B hB L hLfg hL⟩

/-- Integral biduality for an actual finite full module on a regular symmetric
number-field bilinear space. Fractional quadratic values and nonfree modules are allowed. -/
theorem bidual_eq (hB : B.Nondegenerate) (hsym : B.IsSymm)
    (L : Submodule (integerSubring K) V) (hLfg : L.FG)
    (hL : Submodule.span K (L : Set V) = ⊤) : B.dualSubmodule (B.dualSubmodule L) = L := by
  letI := ModuleGenusPatching.finiteDimensional_of_fg_full (integerSubring K) L hLfg hL
  letI : L.IsLattice K := ⟨hLfg, hL⟩
  letI : Module.Finite (integerSubring K) L := Module.Finite.of_fg hLfg
  letI := Module.IsTorsionFree.trans_faithfulSMul (integerSubring K) K V
  letI : Module.FinitePresentation (integerSubring K) L :=
    Module.finitePresentation_of_finite (integerSubring K) L
  letI : Module.Projective (integerSubring K) L :=
    Module.Flat.projective_of_finitePresentation
  let e := dualPairingEquiv B hB L hLfg hL
  apply le_antisymm
  · intro x hx
    let d : Module.Dual (integerSubring K) (B.dualSubmodule L) :=
      B.dualSubmoduleToDual (B.dualSubmodule L) ⟨x, hx⟩
    let t : Module.Dual (integerSubring K) (Module.Dual (integerSubring K) L) :=
      d.comp e.symm.toLinearMap
    let y : L := (Module.evalEquiv (integerSubring K) L).symm t
    have heq : B x = B y.1 := by
      apply LinearMap.ext_on (dual_full B L hLfg)
      intro z hz
      let z' : B.dualSubmodule L := ⟨z, hz⟩
      have h := Module.apply_evalEquiv_symm_apply (integerSubring K) L (e z') t
      have hK := congrArg (algebraMap (integerSubring K) K) h
      have hleft : algebraMap (integerSubring K) K ((e z') y) = B z y.1 :=
        B.dualSubmoduleParing_spec z' y
      have hright : algebraMap (integerSubring K) K (t (e z')) = B x z := by
        change algebraMap (integerSubring K) K (d (e.symm (e z'))) = _
        rw [LinearEquiv.symm_apply_apply]
        exact B.dualSubmoduleParing_spec ⟨x, hx⟩ z'
      rw [hleft, hright, hsym.eq] at hK
      exact hK.symm
    have hxy : x = y.1 := (B.toDual hB).injective heq
    rw [hxy]
    exact y.2
  · intro x hx z hz
    rw [hsym.eq]
    exact hz x hx

/-- The literal half-polar dual is involutive on every finite full number-field module. -/
theorem quadratic_bidual_eq (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (L : Submodule (integerSubring K) V) (hLfg : L.FG)
    (hL : Submodule.span K (L : Set V) = ⊤) :
    IntegralDual.dual Q (IntegralDual.dual Q L) = L :=
  bidual_eq (halfPolar Q) (SpinorBridge.quadraticSpace Q hQ).nondegenerate
    ⟨halfPolar_comm Q⟩ L hLfg hL

end NormEuclidean.IntegralBiduality
