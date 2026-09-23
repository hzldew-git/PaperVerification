import TraceEuclidean.V15DedekindZetaConjugation
import Mathlib.Data.Set.FiniteExhaustion
import Mathlib.Order.Preorder.Finite

/-!
# Heights of multiplicity-aware Dedekind-zeta zero occurrences

Hasanalizade--Shen--Wong work first at heights away from zeros, then pass to
boundary heights by right continuity of the finite zero count. These lemmas
formalize that passage for any entire regularization, without assuming the
published quantitative estimate or the existence of the regularization.
-/

namespace TraceEuclidean

noncomputable section

open Filter Set
open scoped Topology

private theorem finite_sublevel_right_gap {α : Type*} (height : α → ℝ) (T : ℝ)
    (hfinite : {a : α | height a ≤ T + 1}.Finite) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ a : α, height a ≤ T + ε ↔ height a ≤ T := by
  let S : Set α := {a | T < height a ∧ height a ≤ T + 1}
  have hS : S.Finite := hfinite.subset (by intro a ha; exact ha.2)
  by_cases hne : S.Nonempty
  · obtain ⟨a, hmin⟩ := hS.exists_minimalFor height S hne
    have ha : T < height a ∧ height a ≤ T + 1 := hmin.1
    refine ⟨(height a - T) / 2, by linarith [ha.1], by linarith [ha.2], ?_⟩
    intro b
    constructor
    · intro hb
      by_contra hnot
      have hT : T < height b := lt_of_not_ge hnot
      have hbS : b ∈ S := ⟨hT, by linarith [ha.2]⟩
      have hminle : height a ≤ height b := hmin.le hbS
      linarith
    · intro hb
      linarith [ha.1]
  · refine ⟨1, by norm_num, by norm_num, ?_⟩
    intro b
    constructor
    · intro hb
      by_contra hnot
      exact hne ⟨b, lt_of_not_ge hnot, hb⟩
    · intro hb
      linarith

variable {K : Type*} [Field K] [NumberField K]

/-- The actual zero occurrences of any entire regularization are exhausted
by the finite sets of heights at most `n`. This includes every multiplicity
slot without asserting that the set of zeros is infinite. -/
def V15DedekindZetaZeroOccurrence.heightExhaustion
    (Z : V15DedekindZetaRegularization K) :
    Set.FiniteExhaustion (Set.univ : Set (V15DedekindZetaZeroOccurrence Z)) where
  toFun n := V15DedekindZetaZeroOccurrence.boundedSet Z n
  finite' n := V15DedekindZetaZeroOccurrence.boundedSet_finite Z n
  subset_succ' n := by
    intro o ho
    change |o.value.im| ≤ (n + 1 : ℕ)
    exact le_trans ho (by exact_mod_cast Nat.le_succ n)
  iUnion_eq' := by
    ext o
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_ge |o.value.im|
    exact ⟨n, hn⟩

/-- The multiplicity-aware occurrence type is countable, even before any
quantitative zero theorem or infinitude theorem is available. -/
theorem V15DedekindZetaZeroOccurrence.countable
    (Z : V15DedekindZetaRegularization K) :
    Countable (V15DedekindZetaZeroOccurrence Z) := by
  apply Set.countable_univ_iff.mp
  rw [← (V15DedekindZetaZeroOccurrence.heightExhaustion Z).iUnion_eq]
  exact Set.countable_iUnion fun n ↦
    ((V15DedekindZetaZeroOccurrence.heightExhaustion Z).finite n).countable

/-- Above every height there is a short interval with no new strip-zero
occurrences, including multiplicity and zeros at the initial height. -/
theorem V15DedekindZetaZeroOccurrence.exists_right_height_gap
    (Z : V15DedekindZetaRegularization K) (T : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ U : ℝ, T < U → U ≤ T + ε →
        V15DedekindZetaZeroOccurrence.boundedSet Z U =
          V15DedekindZetaZeroOccurrence.boundedSet Z T := by
  obtain ⟨ε, hε, hεone, hgap⟩ := finite_sublevel_right_gap
    (fun o : V15DedekindZetaZeroOccurrence Z ↦ |o.value.im|) T
    (V15DedekindZetaZeroOccurrence.boundedSet_finite Z (T + 1))
  refine ⟨ε, hε, hεone, ?_⟩
  intro U hTU hU
  ext o
  change |o.value.im| ≤ U ↔ |o.value.im| ≤ T
  constructor
  · intro ho
    exact (hgap o).mp (le_trans ho hU)
  · intro ho
    exact le_trans ho hTU.le

/-- The interval of locally constant counts has no occurrence at any
strictly larger height in it. -/
theorem V15DedekindZetaZeroOccurrence.exists_right_regular_interval
    (Z : V15DedekindZetaRegularization K) (T : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ U : ℝ, T < U → U ≤ T + ε →
        (V15DedekindZetaZeroOccurrence.boundedSet Z U).ncard =
          (V15DedekindZetaZeroOccurrence.boundedSet Z T).ncard ∧
        ∀ o : V15DedekindZetaZeroOccurrence Z, |o.value.im| ≠ U := by
  obtain ⟨ε, hε, _, hgap⟩ :=
    V15DedekindZetaZeroOccurrence.exists_right_height_gap Z T
  refine ⟨ε, hε, ?_⟩
  intro U hTU hU
  have heq := hgap U hTU hU
  refine ⟨by rw [heq], ?_⟩
  intro o ho
  have hm : o ∈ V15DedekindZetaZeroOccurrence.boundedSet Z T := by
    rw [← heq]
    change |o.value.im| ≤ U
    exact ho.le
  have hUT : U ≤ T := by
    simpa [V15DedekindZetaZeroOccurrence.boundedSet, ho] using hm
  exact (not_le_of_gt hTU) hUT

/-- A continuous numerical bound proved away from zero heights holds also
at zero heights. This is the boundary-height step in HSW's count argument;
it does not prove the numerical bound itself. -/
theorem V15DedekindZetaZeroOccurrence.bound_of_regular_heights
    (Z : V15DedekindZetaRegularization K) (T : ℝ) (hT : 1 ≤ T)
    (main error : ℝ → ℝ) (hMain : ContinuousAt main T)
    (hError : ContinuousAt error T)
    (hBound : ∀ U : ℝ, 1 ≤ U →
      (∀ o : V15DedekindZetaZeroOccurrence Z, |o.value.im| ≠ U) →
      |((V15DedekindZetaZeroOccurrence.boundedSet Z U).ncard : ℝ) - main U| ≤
        error U) :
    |((V15DedekindZetaZeroOccurrence.boundedSet Z T).ncard : ℝ) - main T| ≤
      error T := by
  obtain ⟨ε, hε, hgap⟩ :=
    V15DedekindZetaZeroOccurrence.exists_right_regular_interval Z T
  have hNear : Iio (T + ε) ∈ 𝓝[>] T :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
  have hEventual : ∀ᶠ U : ℝ in 𝓝[>] T,
      |((V15DedekindZetaZeroOccurrence.boundedSet Z T).ncard : ℝ) - main U| ≤
        error U := by
    filter_upwards [hNear, self_mem_nhdsWithin] with U hU hTU
    obtain ⟨heq, hAway⟩ := hgap U hTU hU.le
    simpa only [heq] using hBound U (hT.trans hTU.le) hAway
  have hLeft : ContinuousAt
      (fun U : ℝ ↦ |((V15DedekindZetaZeroOccurrence.boundedSet Z T).ncard : ℝ) -
        main U|) T :=
    (continuousAt_const.sub hMain).abs
  exact le_of_tendsto_of_tendsto
    (hLeft.tendsto.mono_left nhdsWithin_le_nhds)
    (hError.tendsto.mono_left nhdsWithin_le_nhds) hEventual

/-- The exact HSW Corollary 1.2 bound restricted to heights with no
strip-zero occurrence. Its proof from the argument principle remains a
separate analytic task. -/
def V15DedekindZetaZeroOccurrence.HSWRegularHeightInput
    (Z : V15DedekindZetaRegularization K) (d : ℝ) (n : ℕ) : Prop :=
    ∀ T : ℝ, 1 ≤ T →
      (∀ o : V15DedekindZetaZeroOccurrence Z, |o.value.im| ≠ T) →
      |((V15DedekindZetaZeroOccurrence.boundedSet Z T).ncard : ℝ) -
        T / Real.pi * Real.log (d * (T / (2 * Real.pi * Real.exp 1)) ^ n)| ≤
        (228 / 1000 : ℝ) * (Real.log d + (n : ℝ) * Real.log T) +
          (23108 / 1000 : ℝ) * n + 4520 / 1000

/-- For the exact HSW Corollary 1.2 normalization, it suffices to prove the
numerical inequality at heights containing no strip-zero occurrence. The
right-height gap and continuity supply all remaining boundary heights. -/
theorem V15DedekindZetaZeroOccurrence.HSWNumericInput_of_regular_heights
    (Z : V15DedekindZetaRegularization K) (d : ℝ) (n : ℕ) (hd : 0 < d)
    (hRegular : V15DedekindZetaZeroOccurrence.HSWRegularHeightInput Z d n) :
    V15DedekindZetaZeroOccurrence.HSWNumericInput Z d n := by
  intro T hT
  let main : ℝ → ℝ := fun U ↦
    U / Real.pi * Real.log (d * (U / (2 * Real.pi * Real.exp 1)) ^ n)
  let error : ℝ → ℝ := fun U ↦
    (228 / 1000 : ℝ) * (Real.log d + (n : ℝ) * Real.log U) +
      (23108 / 1000 : ℝ) * n + 4520 / 1000
  have hArg : 0 < d * (T / (2 * Real.pi * Real.exp 1)) ^ n := by
    positivity
  have hArgCont : ContinuousAt
      (fun U : ℝ ↦ d * (U / (2 * Real.pi * Real.exp 1)) ^ n) T := by
    fun_prop
  have hLogArg : ContinuousAt
      (fun U : ℝ ↦ Real.log (d * (U / (2 * Real.pi * Real.exp 1)) ^ n)) T :=
    ContinuousAt.comp' (f := fun U : ℝ ↦ d * (U / (2 * Real.pi * Real.exp 1)) ^ n)
      (g := Real.log) (Real.continuousAt_log hArg.ne') hArgCont
  have hMain : ContinuousAt main T := by
    dsimp [main]
    exact (continuousAt_id.div_const _).mul hLogArg
  have hError : ContinuousAt error T := by
    dsimp [error]
    have hLogT : ContinuousAt Real.log T :=
      Real.continuousAt_log (by linarith : T ≠ 0)
    fun_prop
  exact V15DedekindZetaZeroOccurrence.bound_of_regular_heights
    Z T hT main error hMain hError (by
      intro U hU hAway
      exact hRegular U hU hAway)

/-- Field-normalized version of the boundary-height transfer. -/
theorem V15DedekindZetaZeroOccurrence.HSWFieldInput_of_regular_heights
    (Z : V15DedekindZetaRegularization K)
    (hRegular : V15DedekindZetaZeroOccurrence.HSWRegularHeightInput Z
      |(NumberField.discr K : ℝ)| (Module.finrank ℚ K)) :
    V15DedekindZetaZeroOccurrence.HSWFieldInput Z := by
  exact V15DedekindZetaZeroOccurrence.HSWNumericInput_of_regular_heights Z
    |(NumberField.discr K : ℝ)| (Module.finrank ℚ K)
    (lt_of_lt_of_le (by norm_num) (v15_abs_discr_ge_one K)) hRegular

end
end TraceEuclidean
