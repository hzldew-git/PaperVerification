import NormEuclidean.ChapterX.ExtensionPlaces
import Mathlib.RingTheory.Multiplicity

/-!
# Transport of actual finite completions by number-field automorphisms

The prime is pulled back along the induced integer-ring automorphism.
Ideal multiplicities prove equality of the normalized valuations. This
gives a uniformly continuous map on the valued copies and a ring map on
the actual completed fields, with its global-element formula.
-/

noncomputable section

namespace NormEuclidean.AdicAutomorphism

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped NumberField WithZero Topology

variable {E : Type*} [Field E] [NumberField E]

/-- Transport of ideals as a multiplicative equivalence. -/
def idealEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Ideal R ≃* Ideal S where
  toFun I := I.map e
  invFun J := J.map e.symm
  left_inv _ := Ideal.map_of_equiv e
  right_inv _ := Ideal.map_of_equiv e.symm
  map_mul' I J := Ideal.map_mul e I J

/-- The prime from which the automorphism maps into `w`. -/
def prime (e : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  HeightOneSpectrum.comap (NumberField.RingOfIntegers.mapRingEquiv e).toRingHom
    (NumberField.RingOfIntegers.mapRingEquiv e).surjective w

/-- Integer valuations are preserved with the pulled-back prime. -/
theorem intValuation_map (e : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) :
    w.intValuation (NumberField.RingOfIntegers.mapRingEquiv e x) =
      (prime e w).intValuation x := by
  by_cases hx : x = 0
  · simp [hx]
  let t := NumberField.RingOfIntegers.mapRingEquiv e
  have hm := multiplicity_map_eq (idealEquiv t)
    (a := (prime e w).asIdeal) (b := Ideal.span {x})
  have hp : (prime e w).asIdeal.map t = w.asIdeal :=
    Ideal.map_comap_eq_self_of_equiv t w.asIdeal
  have hs : (Ideal.span {x}).map t = Ideal.span {t x} := by simp [Ideal.map_span]
  change multiplicity ((prime e w).asIdeal.map t) ((Ideal.span {x}).map t) = _ at hm
  rw [hp, hs] at hm
  rw [intValuation_eq_exp_neg_multiplicity _ (by simpa using hx),
    intValuation_eq_exp_neg_multiplicity _ hx, hm]

/-- Normalized valuations on the fraction field are preserved. -/
theorem valuation_map (e : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    w.valuation E (e x) = (prime e w).valuation E x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have hcoe (a : 𝓞 E) : e (algebraMap (𝓞 E) E a) =
      algebraMap (𝓞 E) E (NumberField.RingOfIntegers.mapRingEquiv e a) := rfl
  rw [map_div₀, hcoe, hcoe, map_div₀, map_div₀,
    valuation_of_algebraMap, valuation_of_algebraMap,
    valuation_of_algebraMap, valuation_of_algebraMap,
    intValuation_map, intValuation_map]

/-- The field automorphism on the two valued copies. -/
def valuedMap (e : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) :
    WithVal ((prime e w).valuation E) →+* WithVal (w.valuation E) :=
  WithVal.map _ _ e.toRingHom

/-- Preservation of the normalized valuation gives uniform continuity. -/
theorem valuedMap_uniformContinuous (e : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) :
    UniformContinuous (valuedMap e w) := by
  let v := (prime e w).valuation E
  let z := w.valuation E
  let sv := (WithVal.valueGroupOrderIso₀ v).trans
    (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v)
  let sz := (WithVal.valueGroupOrderIso₀ z).trans
    (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt z)
  have hv (x : WithVal v) : sv (Valued.v.restrict x) = v x.ofVal := by
    change (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v)
      (WithVal.valueGroupOrderIso₀ v ((WithVal.valuation v).restrict x)) = _
    rw [WithVal.valueGroupOrderIso₀_restrict]
    exact Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
      ((prime e w).valuation_surjective E) _
  have hz (x : WithVal z) : sz (Valued.v.restrict x) = z x.ofVal := by
    change (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt z)
      (WithVal.valueGroupOrderIso₀ z ((WithVal.valuation z).restrict x)) = _
    rw [WithVal.valueGroupOrderIso₀_restrict]
    exact Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
      (w.valuation_surjective E) _
  apply uniformContinuous_of_continuousAt_zero (valuedMap e w)
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _)]
  intro gamma _
  let delta := sv.symm (sz (gamma : _))
  have hd : delta ≠ 0 := by simp [delta]
  refine ⟨Units.mk0 delta hd, trivial, ?_⟩
  intro x hx
  change Valued.v.restrict (valuedMap e w x) < (gamma : _)
  rw [← sz.strictMono.lt_iff_lt, hz]
  change z (e x.ofVal) < sz (gamma : _)
  rw [valuation_map]
  have h := sv.strictMono hx
  simpa only [hv, Units.val_mk0, delta, sv.apply_symm_apply] using h

/-- The automorphism extended to the actual adic completions. -/
def completionMap (e : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) :
    (prime e w).adicCompletion E →+* w.adicCompletion E :=
  (adicCompletion.equiv E w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom (valuedMap e w)
      (valuedMap_uniformContinuous e w).continuous).comp
        (adicCompletion.equiv E (prime e w)).toRingHom)

/-- The completed automorphism agrees with the given automorphism on global elements. -/
theorem completionMap_global (e : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    completionMap e w (algebraMap E ((prime e w).adicCompletion E) x) =
      algebraMap E (w.adicCompletion E) (e x) := by
  apply adicCompletion.ext E w
  change UniformSpace.Completion.map (valuedMap e w)
    (↑(WithVal.toVal ((prime e w).valuation E) x)) =
      ↑(WithVal.toVal (w.valuation E) (e x))
  rw [UniformSpace.Completion.map_coe (valuedMap_uniformContinuous e w)]
  rfl

/-- Continuity is retained on the actual completed fields. -/
theorem completionMap_continuous (e : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) :
    Continuous (completionMap e w) :=
  (adicCompletion.continuous_ofCompletion E w).comp
    (UniformSpace.Completion.continuous_map.comp
      (adicCompletion.continuous_toCompletion E (prime e w)))

end NormEuclidean.AdicAutomorphism
