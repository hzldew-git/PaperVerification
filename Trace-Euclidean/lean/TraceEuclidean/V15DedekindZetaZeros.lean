import TraceEuclidean.V15OdlyzkoZeroCountLiterature
import TraceEuclidean.V15OdlyzkoFourthDecayCriterion
import Mathlib.Analysis.Analytic.Order
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Zero occurrences for a regularized Dedekind zeta continuation

An entire continuation of `(s - 1) * ζ_K(s)` is recorded as explicit data.
Its existence is not supplied by the pinned mathlib. The class-number-formula
residue, which *is* in mathlib, forces any such continuation to be nonzero.
The remaining theorems prove uniqueness, discrete zeros, and an occurrence
type whose finite fibres have exactly the analytic zero multiplicity.
-/

namespace TraceEuclidean

noncomputable section

open Filter Set
open scoped Topology ComplexConjugate

/-- An entire continuation of the pole-removed Dedekind zeta function.
The existence of this object is a separate analytic theorem. -/
structure V15DedekindZetaRegularization (K : Type*) [Field K] [NumberField K] where
  value : ℂ → ℂ
  analytic : AnalyticOnNhd ℂ value Set.univ
  agrees_right : ∀ s : ℂ, 1 < s.re →
    value s = (s - 1) * NumberField.dedekindZeta K s

variable {K : Type*} [Field K] [NumberField K]

/-- The existing class-number-formula residue prevents an entire
regularization from vanishing identically. -/
theorem V15DedekindZetaRegularization.exists_nonzero
    (Z : V15DedekindZetaRegularization K) : ∃ s : ℂ, Z.value s ≠ 0 := by
  have hlimit := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hres : (NumberField.dedekindZeta_residue K : ℂ) ≠ 0 := by
    exact_mod_cast NumberField.dedekindZeta_residue_ne_zero K
  have hne : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ),
      ((t : ℂ) - 1) * NumberField.dedekindZeta K t ≠ 0 :=
    hlimit.eventually_ne hres
  obtain ⟨t, htne, ht⟩ := (hne.and self_mem_nhdsWithin).exists
  refine ⟨(t : ℂ), ?_⟩
  rw [Z.agrees_right (t : ℂ) (by simpa using ht)]
  exact htne

/-- Any two entire continuations agreeing with the right-half-plane
Dirichlet series are identical. -/
theorem V15DedekindZetaRegularization.value_unique
    (Z W : V15DedekindZetaRegularization K) : Z.value = W.value := by
  apply AnalyticOnNhd.eq_of_eventuallyEq Z.analytic W.analytic (z₀ := (2 : ℂ))
  filter_upwards [
    (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
      (by norm_num : (2 : ℂ) ∈ {s : ℂ | 1 < s.re})] with s hs
  rw [Z.agrees_right s hs, W.agrees_right s hs]

/-- The analytic order is finite at every point: the regularization is
not locally the zero function. -/
theorem V15DedekindZetaRegularization.order_ne_top
    (Z : V15DedekindZetaRegularization K) (s : ℂ) :
    analyticOrderAt Z.value s ≠ ⊤ := by
  intro htop
  have hzero := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s
    (fun z ↦ Z.analytic z (mem_univ z))).mp htop
  obtain ⟨z, hz⟩ := Z.exists_nonzero
  exact hz (congrFun hzero z)

/-- Zeros of the entire regularization. -/
def V15DedekindZetaRegularization.zeroSet
    (Z : V15DedekindZetaRegularization K) : Set ℂ :=
  {s | Z.value s = 0}

theorem V15DedekindZetaRegularization.zeroSet_closed
    (Z : V15DedekindZetaRegularization K) : IsClosed Z.zeroSet := by
  obtain ⟨z, hz⟩ := Z.exists_nonzero
  have hcod : Z.value ⁻¹' ({0} : Set ℂ)ᶜ ∈ codiscrete ℂ :=
    Z.analytic.preimage_zero_mem_codiscrete hz
  change IsClosed (Z.value ⁻¹' ({0} : Set ℂ))
  simpa only [Set.preimage_compl, compl_compl] using
    (mem_codiscrete'.mp hcod).1.isClosed_compl

theorem V15DedekindZetaRegularization.zeroSet_discrete
    (Z : V15DedekindZetaRegularization K) : IsDiscrete Z.zeroSet := by
  obtain ⟨z, hz⟩ := Z.exists_nonzero
  have hcod : Z.value ⁻¹' ({0} : Set ℂ)ᶜ ∈ codiscrete ℂ :=
    Z.analytic.preimage_zero_mem_codiscrete hz
  change IsDiscrete (Z.value ⁻¹' ({0} : Set ℂ))
  simpa only [Set.preimage_compl, compl_compl] using
    (mem_codiscrete'.mp hcod).2

/-- Every compact region contains finitely many distinct zero positions. -/
theorem V15DedekindZetaRegularization.finite_zeros_in_compact
    (Z : V15DedekindZetaRegularization K) {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ Z.zeroSet).Finite := by
  apply (hS.inter_right Z.zeroSet_closed).finite
  exact Z.zeroSet_discrete.mono Set.inter_subset_right

/-- Each point in the open critical strip contributes one occurrence for
each unit of its analytic zero order. -/
def V15DedekindZetaZeroOccurrence (Z : V15DedekindZetaRegularization K) :=
  Σ s : {z : ℂ // 0 < z.re ∧ z.re < 1}, Fin (analyticOrderNatAt Z.value s.1)

def V15DedekindZetaZeroOccurrence.value {Z : V15DedekindZetaRegularization K}
    (o : V15DedekindZetaZeroOccurrence Z) : ℂ := o.1.1

/-- Every occurrence has a genuine zero as its underlying complex value. -/
theorem V15DedekindZetaZeroOccurrence.is_zero
    {Z : V15DedekindZetaRegularization K} (o : V15DedekindZetaZeroOccurrence Z) :
    Z.value o.value = 0 := by
  have hpositive : 0 < analyticOrderNatAt Z.value o.1.1 := by
    exact lt_of_le_of_lt (Nat.zero_le (o.2 : ℕ)) o.2.isLt
  have horder : analyticOrderAt Z.value o.1.1 ≠ 0 := by
    intro hzero
    have hnat : analyticOrderNatAt Z.value o.1.1 = 0 := by
      simp [analyticOrderNatAt, hzero]
    omega
  exact apply_eq_zero_of_analyticOrderAt_ne_zero horder

theorem V15DedekindZetaZeroOccurrence.in_strip
    {Z : V15DedekindZetaRegularization K} (o : V15DedekindZetaZeroOccurrence Z) :
    0 < o.value.re ∧ o.value.re < 1 := o.1.2

/-- Conjugates of occurrences are genuine zeros when the continuation has
the expected real-coefficient symmetry. -/
theorem V15DedekindZetaZeroOccurrence.conj_is_zero
    {Z : V15DedekindZetaRegularization K}
    (hConj : ∀ s : ℂ, Z.value (conj s) = conj (Z.value s))
    (o : V15DedekindZetaZeroOccurrence Z) :
    Z.value (conj o.value) = 0 := by
  rw [hConj, o.is_zero, map_zero]

/-- The occurrence fibre over a strip point has exactly its analytic
zero order as cardinality. -/
theorem V15DedekindZetaZeroOccurrence.fibre_card
    (Z : V15DedekindZetaRegularization K)
    (s : {z : ℂ // 0 < z.re ∧ z.re < 1}) :
    Nat.card (Fin (analyticOrderNatAt Z.value s.1)) =
      analyticOrderNatAt Z.value s.1 := by simp

/-- A genuine strip zero has at least one occurrence. -/
theorem V15DedekindZetaZeroOccurrence.exists_of_zero
    (Z : V15DedekindZetaRegularization K) (s : ℂ)
    (hstrip : 0 < s.re ∧ s.re < 1) (hzero : Z.value s = 0) :
    ∃ o : V15DedekindZetaZeroOccurrence Z, o.value = s := by
  have horder : analyticOrderAt Z.value s ≠ 0 :=
    ((Z.analytic s (mem_univ s)).analyticOrderAt_ne_zero).2 hzero
  have hpos : 0 < analyticOrderNatAt Z.value s := by
    exact ENat.toNat_pos horder (Z.order_ne_top s)
  exact ⟨⟨⟨s, hstrip⟩, ⟨0, hpos⟩⟩, rfl⟩

/-- The finite-height set of zero occurrences, retaining multiplicity. -/
def V15DedekindZetaZeroOccurrence.boundedSet
    (Z : V15DedekindZetaRegularization K) (T : ℝ) :
    Set (V15DedekindZetaZeroOccurrence Z) :=
  {o | |o.value.im| ≤ T}

/-- Analyticity makes the occurrence set finite at each finite height,
independently of any published quantitative zero-count estimate. -/
theorem V15DedekindZetaZeroOccurrence.boundedSet_finite
    (Z : V15DedekindZetaRegularization K) (T : ℝ) :
    (V15DedekindZetaZeroOccurrence.boundedSet Z T).Finite := by
  let R : Set ℂ := (Icc (0 : ℝ) 1) ×ℂ Icc (-T) T
  have hR : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  let S : Set ℂ := R ∩ Z.zeroSet
  have hS : S.Finite := Z.finite_zeros_in_compact hR
  letI : Finite S := hS.to_subtype
  let f : (V15DedekindZetaZeroOccurrence.boundedSet Z T) →
      Σ s : S, Fin (analyticOrderNatAt Z.value s.1) := fun o ↦
    ⟨⟨o.1.value, by
      constructor
      · change o.1.value.re ∈ Icc (0 : ℝ) 1 ∧ o.1.value.im ∈ Icc (-T) T
        have hstrip := o.1.in_strip
        have him := abs_le.mp (show |o.1.value.im| ≤ T from o.2)
        exact ⟨⟨le_of_lt hstrip.1, le_of_lt hstrip.2⟩, him⟩
      · exact o.1.is_zero⟩, o.1.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hpoint : a.1.1 = b.1.1 := Subtype.ext
      (congrArg (fun x : Σ s : S, Fin (analyticOrderNatAt Z.value s.1) ↦ x.1.1) hab)
    have hslot : HEq a.1.2 b.1.2 := (Sigma.mk.inj_iff.mp hab).2
    exact Subtype.ext (Sigma.ext hpoint hslot)
  exact Finite.of_injective f hf

/-- The numerical HSW inequality stated for the actual finite occurrence
set of a proposed continuation. Its proof from the argument principle is
still external to this file. -/
def V15DedekindZetaZeroOccurrence.HSWNumericInput
    (Z : V15DedekindZetaRegularization K) (d : ℝ) (n : ℕ) : Prop :=
  ∀ T : ℝ, 1 ≤ T →
    |((V15DedekindZetaZeroOccurrence.boundedSet Z T).ncard : ℝ) -
      T / Real.pi * Real.log (d * (T / (2 * Real.pi * Real.exp 1)) ^ n)| ≤
      (228 / 1000 : ℝ) * (Real.log d + (n : ℝ) * Real.log T) +
        (23108 / 1000 : ℝ) * n + 4520 / 1000

/-- The literature estimate with its two number-field parameters fixed to
the actual absolute discriminant and degree. -/
def V15DedekindZetaZeroOccurrence.HSWFieldInput
    (Z : V15DedekindZetaRegularization K) : Prop :=
  V15DedekindZetaZeroOccurrence.HSWNumericInput Z
    |(NumberField.discr K : ℝ)| (Module.finrank ℚ K)

theorem v15_abs_discr_ge_one (K : Type*) [Field K] [NumberField K] :
    (1 : ℝ) ≤ |(NumberField.discr K : ℝ)| := by
  exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero K)

/-- Finiteness of genuine zero occurrences supplies the finite index set
required by the earlier source-count interface. Only the inequality itself
remains the HSW literature premise. -/
theorem V15DedekindZetaZeroOccurrence.corollary12_of_numeric
    (Z : V15DedekindZetaRegularization K) (d : ℝ) (n : ℕ)
    (hNumeric : V15DedekindZetaZeroOccurrence.HSWNumericInput Z d n) :
    V15HasanalizadeShenWongCorollary12Input d n
      (V15DedekindZetaZeroOccurrence.value (Z := Z)) := by
  classical
  intro T hT
  have hfinite := V15DedekindZetaZeroOccurrence.boundedSet_finite Z T
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · intro o
    exact hfinite.mem_toFinset (a := o)
  · simpa only [Set.ncard_eq_toFinset_card _ hfinite] using hNumeric T hT

/-- The source's numerical count yields the required quadratic count for
any injective enumeration of genuine zero occurrences. -/
theorem V15DedekindZetaZeroOccurrence.countBound_of_HSW
    (Z : V15DedekindZetaRegularization K) (d : ℝ) (n : ℕ)
    (representative : ℕ → V15DedekindZetaZeroOccurrence Z)
    (hd : 1 ≤ d) (hInjective : Function.Injective representative)
    (hNumeric : V15DedekindZetaZeroOccurrence.HSWNumericInput Z d n) :
    V15OdlyzkoZeroCountBound
      ((24 * (n : ℝ) + 5) + 3 * (Real.log d + n) * Real.log 3 +
        3 * (Real.log d + n))
      (V15DedekindZetaZeroOccurrence.value ∘ representative) := by
  exact v15OdlyzkoZeroCountBound_of_HSW_published d n
    V15DedekindZetaZeroOccurrence.value representative hd hInjective
    (V15DedekindZetaZeroOccurrence.corollary12_of_numeric Z d n hNumeric)

/-- A height-ordered enumeration of genuine occurrences has a convergent
conjugate-paired zero transform. The decay is proved internally; the HSW
inequality and the enumeration remain explicit inputs. -/
theorem V15DedekindZetaZeroOccurrence.paired_sum_summable
    (Z : V15DedekindZetaRegularization K) (d : ℝ) (n : ℕ)
    (representative : ℕ → V15DedekindZetaZeroOccurrence Z)
    (hd : 1 ≤ d) (hInjective : Function.Injective representative)
    (hOrdered : ∀ i j : ℕ, i ≤ j →
      |(representative i).value.im| ≤ |(representative j).value.im|)
    (hNumeric : V15DedekindZetaZeroOccurrence.HSWNumericInput Z d n) :
    Summable (fun i ↦
      v15OdlyzkoPhi (representative i).value +
        v15OdlyzkoPhi (conj (representative i).value)) := by
  let C : ℝ := (24 * (n : ℝ) + 5) +
    3 * (Real.log d + n) * Real.log 3 + 3 * (Real.log d + n)
  have hC : 0 ≤ C := by
    dsimp [C]
    have hlog : 0 ≤ Real.log d := Real.log_nonneg hd
    have hlogThree : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  have hCount : V15OdlyzkoZeroCountBound C
      (V15DedekindZetaZeroOccurrence.value ∘ representative) :=
    V15DedekindZetaZeroOccurrence.countBound_of_HSW Z d n
      representative hd hInjective hNumeric
  have hGrowth : V15OdlyzkoZeroOrdinalBound C
      (V15DedekindZetaZeroOccurrence.value ∘ representative) :=
    v15OdlyzkoZeroOrdinalBound_of_countBound _ C hOrdered hCount
  exact v15OdlyzkoPhi_conj_pair_summable_of_ordinalBound _ C hC
    (fun i ↦ ⟨le_of_lt (representative i).in_strip.1,
      le_of_lt (representative i).in_strip.2⟩) hGrowth

/-- Field-normalized version: no free discriminant or degree parameters
remain in the summability theorem. -/
theorem V15DedekindZetaZeroOccurrence.paired_sum_summable_of_field_HSW
    (Z : V15DedekindZetaRegularization K)
    (representative : ℕ → V15DedekindZetaZeroOccurrence Z)
    (hInjective : Function.Injective representative)
    (hConj : ∀ s : ℂ, Z.value (conj s) = conj (Z.value s))
    (hOrdered : ∀ i j : ℕ, i ≤ j →
      |(representative i).value.im| ≤ |(representative j).value.im|)
    (hNumeric : V15DedekindZetaZeroOccurrence.HSWFieldInput Z) :
    (∀ i, Z.value (conj (representative i).value) = 0) ∧
      Summable (fun i ↦
        v15OdlyzkoPhi (representative i).value +
          v15OdlyzkoPhi (conj (representative i).value)) := by
  refine ⟨fun i ↦ (representative i).conj_is_zero hConj, ?_⟩
  exact V15DedekindZetaZeroOccurrence.paired_sum_summable Z
    |(NumberField.discr K : ℝ)| (Module.finrank ℚ K) representative
    (v15_abs_discr_ge_one K) hInjective hOrdered hNumeric

end
end TraceEuclidean
