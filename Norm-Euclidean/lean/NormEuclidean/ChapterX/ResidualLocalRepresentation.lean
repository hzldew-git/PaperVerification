import NormEuclidean.ChapterX.FractionalValueMultiplier

/-!
# Almost-everywhere representation for the actual complementary module

The norm-integral local universality theorem extends to every finite full
integer-ring module with possibly fractional quadratic values. This controls
the residual in 104:3 outside an actual finite exceptional set, without a
supplied local representation law. The remaining exceptional places are not
asserted to be covered here.
-/

noncomputable section

namespace NormEuclidean.ResidualLocalRepresentation

open IsDedekindDomain CompletedIntegralLattice Filter

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V]

/-- Every integral completed value is represented at almost all finite places
by the actual completion of a finite full module of rank at least three.
The original quadratic values on that global module may be fractional. -/
theorem eventually_integrally_represents (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (L : Submodule (integerSubring K) V)
    (hfg : L.FG) (hfull : Submodule.span K (L : Set V) = ⊤)
    (hdim : 3 ≤ Module.finrank K V) :
    ∀ᶠ v : HeightOneSpectrum (integerSubring K) in cofinite,
      ∀ t : LocalField (integerSubring K) v, t ∈ LocalRing (integerSubring K) v →
        ∃ z ∈ carrier (integerSubring K) v L, form (integerSubring K) v Q z = t := by
  obtain ⟨d, hd, hdint⟩ := FractionalValueMultiplier.exists_integral_form_scalar Q L hfg
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd
  let M : Lattice (integerSubring K) ((d : K) • Q) :=
    { carrier := L, finite := hfg, full := hfull, integral := hdint }
  have hscaled := LocalIntegralUniversality.eventually_integrally_represents
    ((d : K) • Q) (GenusVolumeFiniteness.polarBilin_smul_nondegenerate Q hQ d hdK) M hdim
  filter_upwards [hscaled] with v hv
  intro t ht
  let dv := algebraMap K (LocalField (integerSubring K) v) (d : K)
  have hdv : dv ≠ 0 := by
    intro h
    exact hdK ((algebraMap K (LocalField (integerSubring K) v)).injective
      (h.trans (map_zero _).symm))
  have hdintv : dv ∈ LocalRing (integerSubring K) v :=
    algebraMap_mem (integerSubring K) v d.property
  obtain ⟨z, hz, hQz⟩ := hv (dv * t)
    ((LocalRing (integerSubring K) v).mul_mem hdintv ht)
  rw [form_rescale, QuadraticMap.smul_apply, smul_eq_mul] at hQz
  exact ⟨z, hz, mul_left_cancel₀ hdv hQz⟩

/-- A genuine finite exceptional set controls all local representations of
every integral residual, simultaneously in the scalar beta. -/
theorem exists_finite_exceptional_set (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (L : Submodule (integerSubring K) V)
    (hfg : L.FG) (hfull : Submodule.span K (L : Set V) = ⊤)
    (hdim : 3 ≤ Module.finrank K V) :
    ∃ S : Finset (HeightOneSpectrum (integerSubring K)),
      ∀ v ∉ S, ∀ a c β : integerSubring K,
        ∃ z ∈ carrier (integerSubring K) v L, form (integerSubring K) v Q z =
          algebraMap K (LocalField (integerSubring K) v)
            ((a : K) * (1 - (c : K) ^ 2 * (β : K) ^ 2)) := by
  classical
  let P (v : HeightOneSpectrum (integerSubring K)) :=
    ∀ t : LocalField (integerSubring K) v, t ∈ LocalRing (integerSubring K) v →
      ∃ z ∈ carrier (integerSubring K) v L, form (integerSubring K) v Q z = t
  have hfinite : {v | ¬ P v}.Finite := eventually_cofinite.mp
    (eventually_integrally_represents Q hQ L hfg hfull hdim)
  refine ⟨hfinite.toFinset, ?_⟩
  intro v hv a c β
  have hPv : P v := by
    by_contra h
    exact hv (hfinite.mem_toFinset.mpr h)
  apply hPv
  exact algebraMap_mem (integerSubring K) v
    (show (a : K) * (1 - (c : K) ^ 2 * (β : K) ^ 2) ∈ integerSubring K from
      (integerSubring K).mul_mem a.property ((integerSubring K).sub_mem
        (integerSubring K).one_mem ((integerSubring K).mul_mem
          ((integerSubring K).pow_mem c.property 2)
          ((integerSubring K).pow_mem β.property 2))))

end NormEuclidean.ResidualLocalRepresentation
