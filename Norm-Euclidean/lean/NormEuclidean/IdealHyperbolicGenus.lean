import NormEuclidean.IdealCompletion
import NormEuclidean.IdealHyperbolicCancellation

/-!
# Ideal hyperbolic stabilizations belong to the ordinary genus

Completion commutes with the full product module, including arbitrary
fractional coordinate ideals. Each completed ideal is principal, so reciprocal
diagonal scaling supplies the actual local integral isometry at every finite
place. The two lattices have the same ambient quadratic space at infinity.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.IdealHyperbolicGenus

open IsDedekindDomain CompletedIntegralLattice
open scoped nonZeroDivisors

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

local instance : IsFractionRing (LocalRing R v) (LocalField R v) :=
  inferInstanceAs (IsFractionRing (v.adicCompletionIntegers K) (LocalField R v))
local instance : IsPrincipalIdealRing (LocalRing R v) :=
  inferInstanceAs (IsPrincipalIdealRing (v.adicCompletionIntegers K))

/-- The actual completed carrier of a product is the product of its completed scalar spans. -/
theorem map_product_carrier (L : Submodule R V) (A B : Submodule R K) :
    (carrier R v (L.prod (A.prod B))).map
        ((hyperbolicEquiv R v).toLinearMap.restrictScalars (LocalRing R v)) =
      (carrier R v L).prod
        ((VolumeLocalization.scalarSpan R v A).prod (VolumeLocalization.scalarSpan R v B)) := by
  rw [carrier, Submodule.map_span]
  change Submodule.span (LocalRing R v)
    ((hyperbolicEquiv R v) '' (inclusion R v '' (L.prod (A.prod B) : Set (Hyperbolic K V)))) = _
  have hset :
      (hyperbolicEquiv R v) '' (inclusion R v '' (L.prod (A.prod B) : Set (Hyperbolic K V))) =
      (inclusion R v '' (L : Set V)) ×ˢ
        ((algebraMap K (LocalField R v) '' (A : Set K)) ×ˢ
          (algebraMap K (LocalField R v) '' (B : Set K))) := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [hyperbolicEquiv_inclusion]
      exact ⟨⟨x.1, hx.1, rfl⟩, ⟨x.2.1, hx.2.1, rfl⟩, ⟨x.2.2, hx.2.2, rfl⟩⟩
    · rintro ⟨⟨x, hx, hxe⟩, ⟨a, ha, hae⟩, ⟨b, hb, hbe⟩⟩
      refine ⟨inclusion R v (x, a, b), ⟨(x, a, b), ⟨hx, ha, hb⟩, rfl⟩, ?_⟩
      rw [hyperbolicEquiv_inclusion]
      exact Prod.ext hxe (Prod.ext hae hbe)
  have hL0 : (0 : Space (V := V) R v) ∈ inclusion R v '' (L : Set V) :=
    ⟨0, L.zero_mem, (inclusion R v).map_zero⟩
  have hA0 : (0 : LocalField R v) ∈ algebraMap K (LocalField R v) '' (A : Set K) :=
    ⟨0, A.zero_mem, map_zero _⟩
  have hB0 : (0 : LocalField R v) ∈ algebraMap K (LocalField R v) '' (B : Set K) :=
    ⟨0, B.zero_mem, map_zero _⟩
  have hAB0 : (0 : LocalField R v × LocalField R v) ∈
      (algebraMap K (LocalField R v) '' (A : Set K)) ×ˢ
        (algebraMap K (LocalField R v) '' (B : Set K)) := ⟨hA0, hB0⟩
  rw [hset, Submodule.span_prod_eq (LocalRing R v) hL0 hAB0,
    Submodule.span_prod_eq (LocalRing R v) hA0 hB0]
  rfl

/-- Tensor/product coordinates carry the entire completed ideal hyperbolic module. -/
theorem carrier_iff (L : Submodule R V) (I : FractionalIdeal R⁰ K)
    (z : Space (V := Hyperbolic K V) R v) :
    hyperbolicEquiv R v z ∈ IdealHyperbolic.submodule (carrier R v L) (IdealCompletion.map R v I) ↔
      z ∈ carrier R v (IdealHyperbolic.submodule L I) := by
  have h := map_product_carrier R v L (I : Submodule R K)
    ((I⁻¹ : FractionalIdeal R⁰ K) : Submodule R K)
  have heq : IdealHyperbolic.submodule (carrier R v L) (IdealCompletion.map R v I) =
      (carrier R v (IdealHyperbolic.submodule L I)).map
        ((hyperbolicEquiv R v).toLinearMap.restrictScalars (LocalRing R v)) := by
    change (carrier R v L).prod
      ((IdealCompletion.map R v I : Submodule (LocalRing R v) (LocalField R v)).prod
        (((IdealCompletion.map R v I)⁻¹ :
          FractionalIdeal (LocalRing R v)⁰ (LocalField R v)) :
            Submodule (LocalRing R v) (LocalField R v))) = _
    change _ = (carrier R v (L.prod
      ((I : Submodule R K).prod ((I⁻¹ : FractionalIdeal R⁰ K) : Submodule R K)))).map _
    rw [h]
    rw [← map_inv₀, IdealCompletion.coe_map, IdealCompletion.coe_map]
  rw [heq]
  constructor
  · rintro ⟨x, hx, he⟩
    exact (hyperbolicEquiv R v).injective he ▸ hx
  · intro hz
    exact ⟨z, hz, rfl⟩

variable [Invertible (2 : K)]

/-- Actual finite-completion isometry from the ideal stabilization to the standard one. -/
theorem exists_completed_isometry (Q : QuadraticForm K V) (L : Lattice R Q)
    (I : FractionalIdeal R⁰ K) (hI : I ≠ 0) :
    Nonempty (LatticeIsometry (form R v (Hyperbolic.form Q)) (form R v (Hyperbolic.form Q))
      (carrier R v (IdealHyperbolic.lattice L I hI).carrier)
      (carrier R v L.hyperbolic.carrier)) := by
  let J := IdealCompletion.map R v I
  obtain ⟨a, ha⟩ := (FractionalIdeal.isPrincipal_iff J).mp inferInstance
  have hJ : J ≠ 0 := IdealCompletion.map_ne_zero R v I hI
  have ha0 : a ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.mp (ha ▸ hJ)
  let E : LatticeIsometry (form R v (Hyperbolic.form Q)) (Hyperbolic.form (form R v Q))
      (carrier R v (IdealHyperbolic.lattice L I hI).carrier)
      (IdealHyperbolic.submodule (carrier R v L.carrier) J) := {
    toLinearEquiv := hyperbolicEquiv R v
    q_eq := hyperbolicEquiv_form R v Q
    mem_iff := carrier_iff R v L.carrier I }
  have S : LatticeIsometry (Hyperbolic.form (form R v Q)) (Hyperbolic.form (form R v Q))
      (IdealHyperbolic.submodule (carrier R v L.carrier) J)
      (Hyperbolic.submodule (carrier R v L.carrier)) := by
    simpa only [ha, Lattice.hyperbolic, CompletedIntegralLattice.lattice] using
      IdealHyperbolic.principalIsometry (lattice R v Q L) a ha0
  exact ⟨(E.compose S).compose (hyperbolicIsometry R v Q L.carrier).inverse⟩

variable [NumberField K]

/-- Every ideal hyperbolic stabilization is in the ordinary genus of the standard stabilization. -/
theorem sameGenus (Q : QuadraticForm K V) (L : Lattice (integerSubring K) Q)
    (I : FractionalIdeal (integerSubring K)⁰ K) (hI : I ≠ 0) :
    SameGenus (Hyperbolic.form Q) L.hyperbolic (IdealHyperbolic.lattice L I hI) := by
  apply (sameGenus_iff_finite _ _ _).mpr
  intro p
  obtain ⟨e⟩ := exists_completed_isometry (integerSubring K) p Q L I hI
  exact ⟨e.inverse⟩

end NormEuclidean.IdealHyperbolicGenus
