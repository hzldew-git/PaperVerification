import NormEuclidean.ChapterX.ComplementIntersection
import NormEuclidean.ChapterX.RegularSublatticePatching
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Completion of the actual intersection with a field subspace

Flatness of the completed integer ring preserves the kernel of the quotient
map restricted to the original module. An injective tensor comparison puts
this equality in the actual field-completed space. Neither a free global
lattice nor an inverse of two in the local integer ring is required.
-/

noncomputable section

open scoped TensorProduct nonZeroDivisors

namespace NormEuclidean.CompletedSubspaceIntersection

open IsDedekindDomain CompletedIntegralLattice

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]

/-- Integral scalar extension over the global ring maps into the actual
completed space, without choosing a lattice basis. -/
def tensorComparison (v : HeightOneSpectrum R) :
    v.adicCompletionIntegers K ⊗[R] V →ₗ[v.adicCompletionIntegers K] Space (V := V) R v := by
  let O := v.adicCompletionIntegers K
  let F := LocalField R v
  letI : TensorProduct.CompatibleSMul R K F V :=
    IsLocalization.tensorProduct_compatibleSMul R⁰ K F V
  exact (TensorProduct.equivOfCompatibleSMul R K O F V).symm.toLinearMap ∘ₗ
    TensorProduct.AlgebraTensorModule.rTensor R V (Algebra.linearMap O F)

@[simp] theorem tensorComparison_tmul (v : HeightOneSpectrum R)
    (a : LocalRing R v) (x : V) :
    tensorComparison R v (a ⊗ₜ[R] x) = (a : LocalField R v) ⊗ₜ[K] x := rfl

/-- The comparison is injective: the field vector space is torsion-free,
and hence flat, over the Dedekind domain. -/
theorem tensorComparison_injective (v : HeightOneSpectrum R) :
    Function.Injective (tensorComparison (V := V) R v) := by
  haveI : Module.IsTorsionFree R V := .of_smul_eq_zero <| by
    intro a x hx
    change (a : K) • x = 0 at hx
    rcases smul_eq_zero.mp hx with ha | hx
    · exact Or.inl (Subtype.ext ha)
    · exact Or.inr hx
  dsimp only [tensorComparison, LinearMap.coe_comp, LinearEquiv.coe_coe]
  apply Function.Injective.comp (LinearEquiv.injective _)
  exact Module.Flat.rTensor_preserves_injective_linearMap
    ((Algebra.linearMap (v.adicCompletionIntegers K) (LocalField R v)).restrictScalars R)
    (FaithfulSMul.algebraMap_injective (v.adicCompletionIntegers K) (LocalField R v))

/-- The tensor comparison commutes with every field-linear map. -/
theorem tensorComparison_natural (v : HeightOneSpectrum R) (f : V →ₗ[K] W) :
    (tensorComparison (V := W) R v).comp
        ((f.restrictScalars R).baseChange (v.adicCompletionIntegers K)) =
      ((f.baseChange (LocalField R v)).restrictScalars (v.adicCompletionIntegers K)).comp
        (tensorComparison (V := V) R v) := by
  ext a
  rfl

/-- The image of integral base change is precisely the defined completed carrier. -/
theorem map_baseChange_eq_carrier (v : HeightOneSpectrum R) (L : Submodule R V) :
    (L.baseChange (v.adicCompletionIntegers K)).map (tensorComparison R v) = carrier R v L := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span]
  apply congrArg (Submodule.span (v.adicCompletionIntegers K))
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

/-- Completing an intersection with a field-linear kernel gives the
intersection of the actual completed carrier and the completed kernel. -/
theorem carrier_inf_ker (v : HeightOneSpectrum R) (L : Submodule R V) (f : V →ₗ[K] W) :
    carrier R v (L ⊓ f.ker.restrictScalars R) = carrier R v L ⊓
      (f.baseChange (LocalField R v)).ker.restrictScalars (LocalRing R v) := by
  let O := v.adicCompletionIntegers K
  let F := LocalField R v
  haveI : Module.IsTorsionFree R O := .of_smul_eq_zero <| by simp
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨inclusion_mem R v L hx.1, by
      change f.baseChange F (inclusion R v x) = 0
      rw [RegularSublatticePatching.baseChange_inclusion]
      exact congrArg (inclusion R v) hx.2 |>.trans (map_zero _)⟩
  · intro y hy
    rw [← map_baseChange_eq_carrier R v L] at hy
    obtain ⟨t, ⟨s, rfl⟩, hsy⟩ := hy.1
    let g := (f.restrictScalars R).comp L.subtype
    have hzero : g.baseChange O s = 0 := by
      apply tensorComparison_injective R v
      rw [map_zero]
      have hg : g.baseChange O s =
          (f.restrictScalars R).baseChange O (L.subtype.baseChange O s) := by
        dsimp only [g]
        rw [LinearMap.baseChange_comp]
        rfl
      rw [hg]
      have hnat := LinearMap.congr_fun (tensorComparison_natural R v f)
        (L.subtype.baseChange O s)
      simp only [LinearMap.comp_apply] at hnat
      rw [hnat, hsy]
      exact hy.2
    have hker : (g.baseChange O).ker = LinearMap.range (g.ker.subtype.baseChange O) :=
      Module.Flat.ker_lTensor_eq O O g
    have hs : s ∈ LinearMap.range (g.ker.subtype.baseChange O) := by
      rw [← hker]
      exact hzero
    obtain ⟨z, hz⟩ := hs
    let j : g.ker →ₗ[R] ↥(L ⊓ f.ker.restrictScalars R) :=
      { toFun := fun x ↦ ⟨(x : L), (x : L).property, x.property⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    rw [← map_baseChange_eq_carrier R v]
    refine ⟨(L ⊓ f.ker.restrictScalars R).subtype.baseChange O (j.baseChange O z),
      ⟨j.baseChange O z, rfl⟩, ?_⟩
    have hmaps : (L ⊓ f.ker.restrictScalars R).subtype.comp j =
        L.subtype.comp g.ker.subtype := rfl
    have hinner : (L ⊓ f.ker.restrictScalars R).subtype.baseChange O
        (j.baseChange O z) = L.subtype.baseChange O s := by
      calc
        _ = ((L ⊓ f.ker.restrictScalars R).subtype.comp j).baseChange O z := by
          rw [LinearMap.baseChange_comp]
          rfl
        _ = L.subtype.baseChange O s := by
          rw [hmaps, LinearMap.baseChange_comp, LinearMap.comp_apply, hz]
    rw [hinner]
    exact hsy

/-- O'Meara 81:3 in the actual completed ambient space: completion of the
global intersection is exactly the intersection with the completed subspace. -/
theorem map_carrier_onSubspace (v : HeightOneSpectrum R)
    (L : Submodule R V) (U : Submodule K V) :
    (carrier R v (ComplementIntersection.onSubspace R L U)).map
        ((U.subtype.baseChange (LocalField R v)).restrictScalars (LocalRing R v)) =
      carrier R v L ⊓
        (LinearMap.range (U.subtype.baseChange (LocalField R v))).restrictScalars
          (LocalRing R v) := by
  have hker : (U.mkQ.baseChange (LocalField R v)).ker =
      LinearMap.range (U.subtype.baseChange (LocalField R v)) := by
    calc
      _ = U.mkQ.ker.baseChange (LocalField R v) :=
        Module.Flat.ker_lTensor_eq (LocalField R v) (LocalField R v) U.mkQ
      _ = U.baseChange (LocalField R v) := by rw [Submodule.ker_mkQ]
  rw [RegularSublatticePatching.carrier_map, ComplementIntersection.map_onSubspace]
  simpa only [Submodule.ker_mkQ, hker] using carrier_inf_ker R v L U.mkQ

/-- Equivalently, the completed module on the subspace is the literal
preimage of the original completed carrier under the completed inclusion. -/
theorem carrier_onSubspace (v : HeightOneSpectrum R)
    (L : Submodule R V) (U : Submodule K V) :
    carrier R v (ComplementIntersection.onSubspace R L U) =
      (carrier R v L).comap
        ((U.subtype.baseChange (LocalField R v)).restrictScalars (LocalRing R v)) := by
  let f := (U.subtype.baseChange (LocalField R v)).restrictScalars (LocalRing R v)
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap U.subtype U.subtype_injective
  apply Submodule.map_injective_of_injective hf
  rw [map_carrier_onSubspace]
  ext y
  constructor
  · rintro ⟨hyL, x, rfl⟩
    exact ⟨x, hyL, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, x, rfl⟩

end NormEuclidean.CompletedSubspaceIntersection
