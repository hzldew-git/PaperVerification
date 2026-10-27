import NormEuclidean.ChapterX.BalancedQuadraticValuations

/-!
# S-unit adjustment of the quadratic Hilbert 90 preimage

Actual base idele principalization realizes the envelope of the two base
coordinates of a balanced quadratic element. Dividing by this base scalar
preserves the Hilbert 90 difference and makes every required valuation one.
-/

noncomputable section

namespace NormEuclidean.SUnitHilbert90

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm SUnitNormArithmetic
open BalancedQuadraticValuations
open scoped NumberField WithZero QuadraticAlgebra

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- A nonzero coordinate selected to attain the actual base valuation envelope. -/
def coordinateUnit (z : K × K) (hz : z ≠ 0) (p : HeightOneSpectrum (𝓞 K)) : Kˣ :=
  (exists_coordinate_envelope z hz p).choose

/-- The chosen coordinate has precisely the envelope valuation. -/
theorem coordinateUnit_value (z : K × K) (hz : z ≠ 0) (p : HeightOneSpectrum (𝓞 K)) :
    p.valuation K (coordinateUnit z hz p).val =
      max (p.valuation K z.1) (p.valuation K z.2) :=
  (exists_coordinate_envelope z hz p).choose_spec

/-- The coordinate envelope is a valuation unit at almost every finite prime. -/
theorem coordinateUnit_eventually (z : K × K) (hz : z ≠ 0) :
    ∀ᶠ (p : HeightOneSpectrum (𝓞 K)) in Filter.cofinite,
      p.valuation K (coordinateUnit z hz p).val = 1 := by
  have hev (a : K) (ha : a ≠ 0) :
      ∀ᶠ (p : HeightOneSpectrum (𝓞 K)) in Filter.cofinite, p.valuation K a = 1 :=
    Filter.eventually_cofinite.mpr (CofiniteLocalIsotropy.finite_nonunit_valuations a ha)
  by_cases hx : z.1 = 0
  · have hy : z.2 ≠ 0 := fun h ↦ hz (Prod.ext hx h)
    filter_upwards [hev z.2 hy] with p hp
    rw [coordinateUnit_value, hx, map_zero, hp]
    exact max_eq_right bot_le
  · by_cases hy : z.2 = 0
    · filter_upwards [hev z.1 hx] with p hp
      rw [coordinateUnit_value, hy, map_zero, hp]
      exact max_eq_left bot_le
    · filter_upwards [hev z.1 hx, hev z.2 hy] with p hp hq
      rw [coordinateUnit_value, hp, hq, max_self]

/-- Principalization gives a global base scalar attaining the coordinate
envelope on every constrained prime. -/
theorem exists_scalar_envelope (S : Set (HeightOneSpectrum (𝓞 K)))
    (hprincipal : idelePrincipalEmbedding.range ⊔ finitePlaceSIdeleSubgroup S = ⊤)
    (z : K × K) (hz : z ≠ 0) :
    ∃ a : Kˣ, ∀ p ∈ S,
      p.valuation K a.val = max (p.valuation K z.1) (p.valuation K z.2) := by
  let f (p : HeightOneSpectrum (𝓞 K)) :=
    Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom (coordinateUnit z hz p)
  have hf : ∀ᶠ p in Filter.cofinite, Valued.v (f p).val = 1 := by
    filter_upwards [coordinateUnit_eventually z hz] with p hp
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p _).trans hp
  let i := NormFiberAssembly.ofComponents f hf (fun _ ↦ 1)
  have hi : i ∈ idelePrincipalEmbedding.range ⊔ finitePlaceSIdeleSubgroup S := by
    rw [hprincipal]
    trivial
  obtain ⟨j, ⟨a, rfl⟩, u, hu, hju⟩ := Subgroup.mem_sup.mp hi
  refine ⟨a, fun p hp ↦ ?_⟩
  have hv := congrArg (fun t ↦ Valued.v (ideleFiniteComponent p t).val) hju
  rw [map_mul, Units.val_mul, map_mul, hu p hp, mul_one] at hv
  have hi_val : Valued.v (ideleFiniteComponent p i).val =
      max (p.valuation K z.1) (p.valuation K z.2) := by
    rw [NormFiberAssembly.finiteComponent_ofComponents]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p _).trans
      (coordinateUnit_value z hz p)
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' p a.val).symm.trans
    (hv.trans hi_val)

/-- Equal conjugate valuations are attained by the same selected base
coordinate at every prime above a good constrained base prime. -/
theorem balanced_value_envelope (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K)) (htwo : (2 : 𝓞 K) ∉ p.asIdeal)
    (hunit : p.valuation K theta.val = 1) :
    letI := quadraticExtensionField theta htheta
    letI := quadraticExtensionNumberField theta htheta
    ∀ w : HeightOneSpectrum (𝓞 (QuadraticAlgebra K theta.val 0)),
      w.under (𝓞 K) = p → ∀ z : QuadraticAlgebra K theta.val 0,
      w.valuation _ z = w.valuation _ (star z) →
      w.valuation _ z =
        (max (p.valuation K z.re) (p.valuation K z.im)) ^
          p.asIdeal.ramificationIdx' w.asIdeal := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  intro w hw z hbal
  letI : w.asIdeal.LiesOver p.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩
  have hval (a : K) : w.valuation (QuadraticAlgebra K theta.val 0)
      (algebraMap K (QuadraticAlgebra K theta.val 0) a) =
      (p.valuation K a) ^ p.asIdeal.ramificationIdx' w.asIdeal :=
    (HeightOneSpectrum.valuation_liesOver _ p w a).symm
  have hp2 : p.valuation K (2 : K) = 1 := by
    calc
      _ = p.valuation K (algebraMap (𝓞 K) K (2 : 𝓞 K)) :=
        congrArg (p.valuation K) (map_ofNat (algebraMap (𝓞 K) K) 2).symm
      _ = p.intValuation (2 : 𝓞 K) := p.valuation_of_algebraMap _
      _ = 1 := (p.intValuation_eq_one_iff_mem_primeCompl _).mpr htwo
  have hw2 : w.valuation _ (2 : QuadraticAlgebra K theta.val 0) = 1 := by
    simpa only [map_ofNat, hp2, one_pow] using hval 2
  have hs : (ω : QuadraticAlgebra K theta.val 0) ^ 2 = algebraMap K _ theta.val := by
    ext <;> simp [pow_two]
  have ho : w.valuation _ (ω : QuadraticAlgebra K theta.val 0) = 1 := by
    apply (pow_eq_one_iff_of_nonneg bot_le (by decide : 2 ≠ 0)).mp
    rw [← map_pow, hs, hval, hunit, one_pow]
  rw [value_eq_max theta.val (w.valuation _) hw2 ho z hbal, hval, hval]
  rcases le_total (p.valuation K z.re) (p.valuation K z.im) with h | h
  · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ bot_le h _)]
  · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ bot_le h _)]

end NormEuclidean.SUnitHilbert90
