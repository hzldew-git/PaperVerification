import NormEuclidean.IsotropicRayTerminal

/-!
# Open scalar-content neighborhoods in completed hyperbolic lattices
-/

noncomputable section

namespace NormEuclidean.CompletedRayNeighborhoods

open IsDedekindDomain CompletedIntegralLattice Filter Topology
open scoped NumberField NormEuclidean.OrthogonalTopology

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- A neighborhood of a multiple of the primitive hyperbolic vector has fixed scalar content. -/
theorem eventually_hasContent (L : Submodule (integerSubring K) V)
    (hfull : Submodule.span K (L : Set V) = ⊤)
    (p : HeightOneSpectrum (integerSubring K)) (a : (LocalField (integerSubring K) p)ˣ) :
    ∀ᶠ x in 𝓝 ((a : LocalField (integerSubring K) p) •
        inclusion _ p (Hyperbolic.e : Hyperbolic K V)),
      ValuationRayContent.HasContent (carrier (integerSubring K) p (Hyperbolic.submodule L))
        x a := by
  let F := LocalField (integerSubring K) p
  let W := Space (V := Hyperbolic K V) (integerSubring K) p
  let N := carrier (integerSubring K) p (Hyperbolic.submodule L)
  letI := IsModuleTopology.topologicalAddGroup F W
  let phi : W →ₗ[F] F := (LinearMap.fst F F F).comp
    ((LinearMap.snd F (Space (V := V) (integerSubring K) p) (F × F)).comp
      (hyperbolicEquiv (V := V) (integerSubring K) p).toLinearMap)
  apply ValuationRayContent.eventually_hasContent N
    (OrthogonalTopology.isOpen_of_full (LocalRing (integerSubring K) p)
      (OrthogonalTopology.isOpen_localRing _ p) N
      (carrier_full _ p _ (Hyperbolic.submodule_full L hfull))) phi
    (IsModuleTopology.continuous_of_linearMap phi)
  · intro r hr x hx
    exact N.smul_mem (⟨r, hr⟩ : LocalRing (integerSubring K) p) hx
  · intro x hx
    exact ((hyperbolicEquiv_carrier _ p L x).mpr hx).2.1
  · exact inclusion_mem _ p (Hyperbolic.submodule L) (by simp [Hyperbolic.Mem, Hyperbolic.e])
  · change (hyperbolicEquiv (integerSubring K) p
      (inclusion _ p (Hyperbolic.e : Hyperbolic K V))).2.1 = 1
    have h := congrArg
      (fun z : Hyperbolic (LocalField (integerSubring K) p)
        (Space (V := V) (integerSubring K) p) ↦ z.2.1)
      (hyperbolicEquiv_inclusion (integerSubring K) p (Hyperbolic.e : Hyperbolic K V))
    simpa only [Hyperbolic.e, map_one] using h

end NormEuclidean.CompletedRayNeighborhoods
