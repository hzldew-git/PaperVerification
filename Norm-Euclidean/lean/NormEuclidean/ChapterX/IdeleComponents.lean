/-
Copyright (c) 2026 BONG Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BONG Theory contributors
-/

import NormEuclidean.IdeleClassGroup
import Mathlib.NumberTheory.NumberField.AdeleRing

/-!
# Actual number-field idèles and their components

The finite and infinite evaluation maps and the finite exceptional support
are adapted from HeADC's idèle constructions, without any Hasse or index input.
-/

namespace NormEuclidean.ExtensionIdeleNorm

open scoped NumberField

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- The norm on an infinite completion is nontrivial.  Kept as a local
construction because mathlib does not expose this instance globally. -/
@[implicit_reducible]
noncomputable def infiniteCompletionNontriviallyNormedField
    (w : NumberField.InfinitePlace K) :
    NontriviallyNormedField w.Completion where
  toNormedField := inferInstance
  non_trivial := by
    refine ⟨algebraMap K w.Completion (2 : K), ?_⟩
    have hnorm : ‖algebraMap K w.Completion (2 : K)‖ = 2 := by
      rw [NumberField.InfinitePlace.Completion.algebraMap_apply]
      rw [NumberField.InfinitePlace.Completion.norm_coe]
      exact NumberField.InfinitePlace.map_natCast w 2
    rw [hnorm]
    norm_num

/-- The idèle group of a number field, realized as the units of its full
Adele ring. -/
abbrev NumberFieldIdele (K : Type u) [Field K] [NumberField K] :=
  (NumberField.AdeleRing (𝓞 K) K)ˣ

/-- The principal-idèle embedding. -/
noncomputable def idelePrincipalEmbedding : Kˣ →* NumberFieldIdele K :=
  Units.map (algebraMap K (NumberField.AdeleRing (𝓞 K) K))

/-- Evaluation of an idèle at an actual finite completion. -/
noncomputable def ideleFiniteComponent
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    NumberFieldIdele K →* (p.adicCompletion K)ˣ := by
  change ((NumberField.InfiniteAdeleRing K ×
    IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ) →* _
  exact Units.map <|
    (RestrictedProduct.evalRingHom
      (fun q : IsDedekindDomain.HeightOneSpectrum (𝓞 K) ↦
        q.adicCompletion K) p).comp
      (RingHom.snd (NumberField.InfiniteAdeleRing K)
        (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))

/-- Evaluation of an idèle at an actual infinite completion. -/
noncomputable def ideleInfiniteComponent
    (p : NumberField.InfinitePlace K) :
    NumberFieldIdele K →* p.Completionˣ := by
  change ((NumberField.InfiniteAdeleRing K ×
    IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ) →* _
  exact Units.map <|
    (Pi.evalRingHom (fun q : NumberField.InfinitePlace K ↦ q.Completion) p).comp
      (RingHom.fst (NumberField.InfiniteAdeleRing K)
        (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))

/-- Every full idèle has valuation-unit finite components at all but
finitely many actual finite places. -/
theorem ideleFiniteComponent_eventually_valuation_one
    (i : NumberFieldIdele K) :
    ∀ᶠ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Valued.v ((ideleFiniteComponent p i : (p.adicCompletion K)ˣ) :
        p.adicCompletion K) = 1 := by
  let fi : (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ :=
    Units.map (RingHom.snd (NumberField.InfiniteAdeleRing K)
      (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)).toMonoidHom i
  have h := IsDedekindDomain.FiniteAdeleRing.unitsEquiv_finite_valued_eq_one fi
  filter_upwards [h] with p hp
  exact hp

end NormEuclidean.ExtensionIdeleNorm
