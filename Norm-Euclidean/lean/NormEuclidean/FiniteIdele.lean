import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# Finite ideles, fractional ideals, and local units

Finite ideles are units of mathlib's actual restricted product of finite
completions. Their component valuations define a finitely supported divisor
and hence a nonzero fractional ideal. Over a principal ideal domain, every
finite idele is a diagonal field element times local integral units.
-/

noncomputable section

namespace NormEuclidean.FiniteIdele

open IsDedekindDomain
open scoped nonZeroDivisors WithZero

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Evaluation of a finite idele in the unit group of an actual finite completion. -/
def componentUnit (v : HeightOneSpectrum R) :
    (FiniteAdeleRing R K)ˣ →* (v.adicCompletion K)ˣ where
  toFun a :=
    { val := a.1 v
      inv := a.inv v
      val_inv := congrArg (fun b : FiniteAdeleRing R K ↦ b v) a.val_inv
      inv_val := congrArg (fun b : FiniteAdeleRing R K ↦ b v) a.inv_val }
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext rfl

@[simp] theorem componentUnit_val (a : (FiniteAdeleRing R K)ˣ)
    (v : HeightOneSpectrum R) : (componentUnit v a : v.adicCompletion K) = a.1 v := rfl

@[simp] theorem componentUnit_diagonal (k : Kˣ) (v : HeightOneSpectrum R) :
    componentUnit v (FiniteAdeleRing.unitEmbedding R K k) =
      Units.map (algebraMap K (v.adicCompletion K)) k := by
  apply Units.ext
  rfl

/-- The additive order of an actual finite-idele component. -/
def order (a : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) : ℤ :=
  -WithZero.log (Valued.v (a.1 v) : ℤᵐ⁰)

theorem component_ne_zero (a : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) :
    a.1 v ≠ 0 :=
  (FiniteAdeleRing.isUnit_iff.mp a.isUnit).1 v

theorem component_valuation_ne_zero (a : (FiniteAdeleRing R K)ˣ)
    (v : HeightOneSpectrum R) : (Valued.v (a.1 v) : ℤᵐ⁰) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr (component_ne_zero a v)

@[simp] theorem order_one (v : HeightOneSpectrum R) :
    order (1 : (FiniteAdeleRing R K)ˣ) v = 0 := by
  change -WithZero.log (Valued.v (1 : v.adicCompletion K)) = 0
  simp

@[simp] theorem order_mul (a b : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) :
    order (a * b) v = order a v + order b v := by
  change -WithZero.log (Valued.v (a.1 v * b.1 v)) = _
  rw [map_mul, WithZero.log_mul (component_valuation_ne_zero a v)
    (component_valuation_ne_zero b v), neg_add]
  rfl

@[simp] theorem order_inv (a : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) :
    order a⁻¹ v = -order a v := by
  have h := order_mul a a⁻¹ v
  rw [mul_inv_cancel, order_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem order_eq_zero_iff (a : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) :
    order a v = 0 ↔ (Valued.v (a.1 v) : ℤᵐ⁰) = 1 := by
  constructor
  · intro h
    have he := WithZero.exp_log (component_valuation_ne_zero a v)
    rw [show WithZero.log (Valued.v (a.1 v) : ℤᵐ⁰) = 0 from neg_eq_zero.mp h,
      WithZero.exp_zero] at he
    exact he.symm
  · intro h
    simp [order, h]

/-- Restrictedness of an idele and its inverse makes its divisor finite. -/
theorem finite_support_order (a : (FiniteAdeleRing R K)ˣ) :
    (Function.support (order a)).Finite := by
  have h := (FiniteAdeleRing.isUnit_iff.mp a.isUnit).2
  have hz : ∀ᶠ v in Filter.cofinite, order a v = 0 :=
    h.mono fun v hv ↦ (order_eq_zero_iff a v).mpr hv
  exact hz

/-- The finitely supported divisor of a finite idele. -/
def divisor (a : (FiniteAdeleRing R K)ˣ) : HeightOneSpectrum R →₀ ℤ :=
  Finsupp.ofSupportFinite (order a) (finite_support_order a)

@[simp] theorem divisor_apply (a : (FiniteAdeleRing R K)ˣ) (v : HeightOneSpectrum R) :
    divisor a v = order a v := rfl

@[simp] theorem divisor_one : divisor (1 : (FiniteAdeleRing R K)ˣ) = 0 := by
  ext v
  exact order_one v

@[simp] theorem divisor_mul (a b : (FiniteAdeleRing R K)ˣ) :
    divisor (a * b) = divisor a + divisor b := by
  ext v
  exact order_mul a b v

/-- The fractional ideal associated to the genuine finite-idele valuations. -/
def fractionalIdeal (a : (FiniteAdeleRing R K)ˣ) : FractionalIdeal R⁰ K :=
  (divisor a).prod fun v n ↦ (v.asIdeal : FractionalIdeal R⁰ K) ^ n

theorem fractionalIdeal_ne_zero (a : (FiniteAdeleRing R K)ˣ) :
    fractionalIdeal a ≠ 0 := by
  apply Finsupp.prod_ne_zero_iff.mpr
  intro v _
  exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

@[simp] theorem count_fractionalIdeal (a : (FiniteAdeleRing R K)ˣ)
    (v : HeightOneSpectrum R) :
    FractionalIdeal.count K v (fractionalIdeal a) = order a v :=
  FractionalIdeal.count_finsuppProd K v (divisor a)

/-- Equality of all prime exponents determines a nonzero fractional ideal. -/
theorem fractionalIdeal_ext {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R,
      FractionalIdeal.count K v I = FractionalIdeal.count K v J) : I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  apply finprod_congr
  intro v
  rw [h v]

@[simp] theorem fractionalIdeal_one :
    fractionalIdeal (1 : (FiniteAdeleRing R K)ˣ) = 1 := by
  simp [fractionalIdeal]

@[simp] theorem fractionalIdeal_mul (a b : (FiniteAdeleRing R K)ˣ) :
    fractionalIdeal (a * b) = fractionalIdeal a * fractionalIdeal b := by
  apply fractionalIdeal_ext (fractionalIdeal_ne_zero (a * b))
    (mul_ne_zero (fractionalIdeal_ne_zero a) (fractionalIdeal_ne_zero b))
  intro v
  rw [count_fractionalIdeal, FractionalIdeal.count_mul K v
    (fractionalIdeal_ne_zero _) (fractionalIdeal_ne_zero _),
    count_fractionalIdeal, count_fractionalIdeal, order_mul]

/-- The valuation-to-fractional-ideal map, bundled as a homomorphism. -/
def idealHom : (FiniteAdeleRing R K)ˣ →* FractionalIdeal R⁰ K where
  toFun := fractionalIdeal
  map_one' := fractionalIdeal_one
  map_mul' := fractionalIdeal_mul

/-- The prime exponent of a principal fractional ideal is the additive valuation. -/
theorem count_spanSingleton (v : HeightOneSpectrum R) (k : K) (hk : k ≠ 0) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ k) =
      -WithZero.log (v.valuation K k) := by
  obtain ⟨n, d, rfl⟩ := IsLocalization.exists_mk'_eq R⁰ k
  have hn : n ≠ 0 := by
    intro h
    apply hk
    simp [h]
  have hI : FractionalIdeal.spanSingleton R⁰ (IsLocalization.mk' K n d) =
      FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) d)⁻¹ *
        (Ideal.span {n} : Ideal R) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  rw [FractionalIdeal.count_well_defined K v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hk) hI,
    v.valuation_of_mk', WithZero.log_div
      (v.intValuation_ne_zero n hn) (v.intValuation_ne_zero' d),
    v.intValuation_if_neg hn, v.intValuation_if_neg (nonZeroDivisors.coe_ne_zero d),
    WithZero.log_exp, WithZero.log_exp]
  omega

@[simp] theorem order_diagonal (k : Kˣ) (v : HeightOneSpectrum R) :
    order (FiniteAdeleRing.unitEmbedding R K k) v =
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (k : K)) := by
  rw [count_spanSingleton v (k : K) k.ne_zero]
  change -WithZero.log (Valued.v ((k : K) : v.adicCompletion K)) = _
  rw [v.valuedAdicCompletion_eq_valuation']

/-- A diagonal finite idele maps to its principal fractional ideal. -/
@[simp] theorem fractionalIdeal_diagonal (k : Kˣ) :
    fractionalIdeal (FiniteAdeleRing.unitEmbedding R K k) =
      FractionalIdeal.spanSingleton R⁰ (k : K) := by
  apply fractionalIdeal_ext (fractionalIdeal_ne_zero _)
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr k.ne_zero)
  intro v
  rw [count_fractionalIdeal, order_diagonal]

/-- The subgroup of finite ideles that are integral units at every finite place. -/
def localUnitSubgroup : Subgroup (FiniteAdeleRing R K)ˣ where
  carrier := {a | ∀ v, order a v = 0}
  one_mem' := order_one
  mul_mem' := by intro a b ha hb v; simp [ha v, hb v]
  inv_mem' := by intro a ha v; simp [ha v]

theorem mem_localUnitSubgroup_iff (a : (FiniteAdeleRing R K)ˣ) :
    a ∈ localUnitSubgroup ↔ ∀ v : HeightOneSpectrum R,
      (Valued.v (a.1 v) : ℤᵐ⁰) = 1 := by
  exact forall_congr' (order_eq_zero_iff a)

theorem mem_localUnitSubgroup_component_iff (a : (FiniteAdeleRing R K)ˣ) :
    a ∈ localUnitSubgroup ↔ ∀ v : HeightOneSpectrum R,
      (Valued.v (componentUnit v a : v.adicCompletion K) : ℤᵐ⁰) = 1 :=
  mem_localUnitSubgroup_iff a

/-- Each component of a local-unit idele comes from an actual unit of the
completed integer subring used by the lattice-completion modules. -/
theorem exists_localIntegerUnit {a : (FiniteAdeleRing R K)ˣ}
    (ha : a ∈ localUnitSubgroup) (v : HeightOneSpectrum R) :
    ∃ u : ((v.adicCompletionIntegers K).toSubring)ˣ,
      Units.map (v.adicCompletionIntegers K).toSubring.subtype u = componentUnit v a := by
  have hv := (mem_localUnitSubgroup_iff a).mp ha v
  let r : v.adicCompletionIntegers K :=
    ⟨a.1 v, (HeightOneSpectrum.mem_adicCompletionIntegers R K v).mpr hv.le⟩
  have hu : IsUnit r :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hv
  refine ⟨hu.unit, ?_⟩
  apply Units.ext
  exact congrArg (fun x : v.adicCompletionIntegers K ↦ (x : v.adicCompletion K)) hu.unit_spec

/-- This is an equality of actual groups, with local integrality measured in the completions. -/
theorem idealHom_ker : (idealHom (R := R) (K := K)).ker = localUnitSubgroup := by
  ext a
  change fractionalIdeal a = 1 ↔ ∀ v, order a v = 0
  constructor
  · intro h v
    rw [← count_fractionalIdeal a v, h, FractionalIdeal.count_one]
  · intro h
    apply fractionalIdeal_ext (fractionalIdeal_ne_zero a)
      (one_ne_zero : (1 : FractionalIdeal R⁰ K) ≠ 0)
    intro v
    rw [count_fractionalIdeal, h v, FractionalIdeal.count_one]

/-- Under the PID hypothesis an arbitrary finite idele is a diagonal field unit
times an idele whose components are units of all the local integer rings. -/
theorem exists_diagonal_mul_localUnit [IsPrincipalIdealRing R]
    (a : (FiniteAdeleRing R K)ˣ) :
    ∃ k : Kˣ, ∃ u : localUnitSubgroup (R := R) (K := K),
      a = FiniteAdeleRing.unitEmbedding R K k * u.1 := by
  obtain ⟨k, hk⟩ := (FractionalIdeal.isPrincipal_iff (fractionalIdeal a)).mp inferInstance
  have hk0 : k ≠ 0 := by
    intro h
    apply fractionalIdeal_ne_zero a
    simpa [h] using hk
  let k' : Kˣ := Units.mk0 k hk0
  let d := FiniteAdeleRing.unitEmbedding R K k'
  let u := d⁻¹ * a
  have hu : u ∈ localUnitSubgroup := by
    intro v
    change order (d⁻¹ * a) v = 0
    rw [order_mul, order_inv]
    have hd : order d v = order a v := by
      rw [order_diagonal, ← count_fractionalIdeal a v]
      exact congrArg (FractionalIdeal.count K v) hk.symm
    rw [hd, neg_add_cancel]
  exact ⟨k', ⟨u, hu⟩, by dsimp [u, d]; simp⟩

/-- A componentwise form of the PID decomposition, using the genuine evaluation homomorphism. -/
theorem exists_diagonal_mul_valuation_one [IsPrincipalIdealRing R]
    (a : (FiniteAdeleRing R K)ˣ) :
    ∃ k : Kˣ, ∃ b : (FiniteAdeleRing R K)ˣ,
      a = FiniteAdeleRing.unitEmbedding R K k * b ∧
      ∀ v : HeightOneSpectrum R,
        (Valued.v (componentUnit v b : v.adicCompletion K) : ℤᵐ⁰) = 1 := by
  obtain ⟨k, b, h⟩ := exists_diagonal_mul_localUnit a
  exact ⟨k, b.1, h, (mem_localUnitSubgroup_component_iff b.1).mp b.2⟩

end NormEuclidean.FiniteIdele
