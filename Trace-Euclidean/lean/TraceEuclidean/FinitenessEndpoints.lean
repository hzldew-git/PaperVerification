import TraceEuclidean.AnalyticFiniteness
import TraceEuclidean.ArithmeticFiniteness

/-!
Logical assembly of the eight clauses in Theorems 1.2 and 1.3. The type `α`
represents equivalence classes of field-lattice pairs under the equivalence
defined before Theorem 1.2. The fixed positive real parameter `t` and the
restriction `t ≤ degree` occur explicitly in every applicable endpoint.
-/

namespace TraceEuclidean

theorem finite_admissible_pairs_of_envelope
    (h : ℕ → ℕ → ℝ) (n₀ : ℕ)
    (hdegree : {d | 0 < h n₀ d}.Finite)
    (hrank : ∀ d, {n | 0 < h n d}.Finite)
    (henvelope : ∀ n d, n₀ ≤ n → h n d ≤ h n₀ d) :
    {p : ℕ × ℕ | n₀ ≤ p.1 ∧ 0 < h p.1 p.2}.Finite := by
  apply finite_of_finite_keys_and_fibers
    (fun p : ℕ × ℕ ↦ n₀ ≤ p.1 ∧ 0 < h p.1 p.2)
    Prod.snd {d | 0 < h n₀ d} hdegree
  · intro p hp
    exact lt_of_lt_of_le hp.2 (henvelope p.1 p.2 hp.1)
  · intro d
    apply ((hrank d).prod (Set.finite_singleton d)).subset
    intro p hp
    constructor
    · simpa [hp.2] using hp.1.2
    · simpa using hp.2

/--
A uniform degree envelope together with the fixed-degree rank tails leaves only
finitely many admissible rank-degree pairs.  This is the form used by the
global clauses of Theorems 1.2 and 1.3.
-/
theorem finite_admissible_pairs_of_uniform_envelope
    (h : ℕ → ℕ → ℝ) (envelope : ℕ → ℝ) (n₀ : ℕ)
    (henvelopeFinite : {d | 0 < envelope d}.Finite)
    (hrank : ∀ d, 1 ≤ d → {n | 0 < h n d}.Finite)
    (hupper : ∀ n d, n₀ ≤ n → 1 ≤ d → h n d ≤ envelope d) :
    {p : ℕ × ℕ |
      n₀ ≤ p.1 ∧ 1 ≤ p.2 ∧ 0 < h p.1 p.2}.Finite := by
  apply finite_of_finite_keys_and_fibers
    (fun p : ℕ × ℕ ↦ n₀ ≤ p.1 ∧ 1 ≤ p.2 ∧ 0 < h p.1 p.2)
    Prod.snd {d | 0 < envelope d} henvelopeFinite
  · intro p hp
    exact lt_of_lt_of_le hp.2.2 (hupper p.1 p.2 hp.1 hp.2.1)
  · intro d
    by_cases hd : 1 ≤ d
    · exact ((hrank d hd).prod (Set.finite_singleton d)).subset fun p hp ↦
        ⟨by simpa [hp.2] using hp.1.2.2, hp.2⟩
    · have hempty :
          {p | (n₀ ≤ p.1 ∧ 1 ≤ p.2 ∧ 0 < h p.1 p.2) ∧ p.2 = d} =
            (∅ : Set (ℕ × ℕ)) := by
        ext p
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro hp
        apply hd
        simpa [hp.2] using hp.1.2.1
      rw [hempty]
      exact Set.finite_empty

/--
The geometric and arithmetic inputs used after the definitions in the proof
of Theorems 1.2 and 1.3. The analytic functions and all of their tail bounds
are proved in `AnalyticFiniteness`. The predicates `classic t a` and
`integral t a` encode positive definiteness, the stated integrality condition,
and strict `t`-trace Euclideanity. The degree restriction remains separate.
-/
structure MainFinitenessFramework (A α : Type*) [Field A] [CharZero A] where
  rank : α → ℕ
  degree : α → ℕ
  classic : ℝ → α → Prop
  integral : ℝ → α → Prop
  fieldCode : α → NumberFieldCode A
  classicVolumeIdeal : ∀ K, FieldFiber fieldCode K →
    Ideal (NumberField.RingOfIntegers K)
  integralScaledVolumeIdeal : ∀ K, FieldFiber fieldCode K →
    Ideal (NumberField.RingOfIntegers K)
  classicDiscriminantBound : ℝ → ℕ → ℕ → ℕ
  integralDiscriminantBound : ℝ → ℕ → ℕ → ℕ
  classicVolumeBound : ℝ → ℕ → ℕ → ℕ
  integralScaledVolumeBound : ℝ → ℕ → ℕ → ℕ
  classic_positive : ∀ (t : ℝ) (a : α), 0 < t → t ≤ degree a →
    classic t a → 0 < gClassicNat (rank a) (degree a)
  integral_positive : ∀ (t : ℝ) (a : α), 0 < t → t ≤ degree a →
    integral t a → 0 < gIntegralNat (rank a) (degree a)
  classic_discriminant_le : ∀ (t : ℝ) (n d : ℕ) (a : α),
    classic t a ∧ rank a = n ∧ degree a = d →
      |(fieldCode a).discriminant| ≤ classicDiscriminantBound t n d
  integral_discriminant_le : ∀ (t : ℝ) (n d : ℕ) (a : α),
    integral t a ∧ rank a = n ∧ degree a = d →
      |(fieldCode a).discriminant| ≤ integralDiscriminantBound t n d
  classic_volume_le : ∀ (t : ℝ) (n d : ℕ) (K)
      (a : FieldFiber fieldCode K),
    classic t a.1 ∧ rank a.1 = n ∧ degree a.1 = d →
      Ideal.absNorm (classicVolumeIdeal K a) ≤ classicVolumeBound t n d
  integral_scaled_volume_le : ∀ (t : ℝ) (n d : ℕ) (K)
      (a : FieldFiber fieldCode K),
    integral t a.1 ∧ rank a.1 = n ∧ degree a.1 = d →
      Ideal.absNorm (integralScaledVolumeIdeal K a) ≤
        integralScaledVolumeBound t n d
  classic_fixed_volume : ∀ (t : ℝ) (n d : ℕ) (K I),
    {a : FieldFiber fieldCode K |
      classic t a.1 ∧ rank a.1 = n ∧ degree a.1 = d ∧
        classicVolumeIdeal K a = I}.Finite
  integral_fixed_scaled_volume : ∀ (t : ℝ) (n d : ℕ) (K I),
    {a : FieldFiber fieldCode K |
      integral t a.1 ∧ rank a.1 = n ∧ degree a.1 = d ∧
        integralScaledVolumeIdeal K a = I}.Finite

namespace MainFinitenessFramework

variable {A α : Type*} [Field A] [CharZero A]
variable (M : MainFinitenessFramework A α)

/-- Lemma 5.1 specialized to a classic-integral fixed parameter fiber. -/
theorem classic_fixed_pair (t : ℝ) (n d : ℕ) :
    {a | M.classic t a ∧ M.rank a = n ∧ M.degree a = d}.Finite := by
  let P : α → Prop := fun a ↦
    M.classic t a ∧ M.rank a = n ∧ M.degree a = d
  apply bounded_discriminant_volume_finiteness P M.fieldCode
    (M.classicDiscriminantBound t n d) (M.classicVolumeBound t n d)
    M.classicVolumeIdeal
  · intro a ha
    exact M.classic_discriminant_le t n d a ha
  · intro K a ha
    exact M.classic_volume_le t n d K a ha
  · intro K I
    simpa only [P, and_assoc] using M.classic_fixed_volume t n d K I

/-- Lemma 5.1 specialized to an integral fixed parameter fiber after scaling. -/
theorem integral_fixed_pair (t : ℝ) (n d : ℕ) :
    {a | M.integral t a ∧ M.rank a = n ∧ M.degree a = d}.Finite := by
  let P : α → Prop := fun a ↦
    M.integral t a ∧ M.rank a = n ∧ M.degree a = d
  apply bounded_discriminant_volume_finiteness P M.fieldCode
    (M.integralDiscriminantBound t n d)
    (M.integralScaledVolumeBound t n d) M.integralScaledVolumeIdeal
  · intro a ha
    exact M.integral_discriminant_le t n d a ha
  · intro K a ha
    exact M.integral_scaled_volume_le t n d K a ha
  · intro K I
    simpa only [P, and_assoc] using
      M.integral_fixed_scaled_volume t n d K I

/-- Theorem 1.2(i), for either fixed rank `1` or fixed rank `2`. -/
theorem finiteness_classic_fixed_degree_low_rank
    (t : ℝ) (_ht : 0 < t) (n d : ℕ) (_htd : t ≤ d)
    (_hn : n = 1 ∨ n = 2) :
    {a | M.classic t a ∧ M.rank a = n ∧ M.degree a = d}.Finite :=
  M.classic_fixed_pair t n d

/-- Theorem 1.2(ii): fixed rank at least three and varying degree. -/
theorem finiteness_classic_fixed_high_rank
    (t : ℝ) (ht : 0 < t) (n : ℕ) (hn : 3 ≤ n) :
    {a | M.classic t a ∧ M.rank a = n ∧ t ≤ M.degree a}.Finite := by
  apply finite_of_finite_keys_and_fibers
    (fun a ↦ M.classic t a ∧ M.rank a = n ∧ t ≤ M.degree a)
    M.degree {d | 0 < gClassicNat n d}
    (finite_positive_of_tendsto_atTop_atBot (gClassicNat_degree_tail n hn))
  · intro a ha
    simpa [ha.2.1] using M.classic_positive t a ht ha.2.2 ha.1
  · intro d
    by_cases htd : t ≤ d
    · exact (M.classic_fixed_pair t n d).subset fun a ha ↦
        ⟨ha.1.1, ha.1.2.1, ha.2⟩
    · have hempty :
          {a | (M.classic t a ∧ M.rank a = n ∧ t ≤ M.degree a) ∧
            M.degree a = d} = (∅ : Set α) := by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro ha
        apply htd
        simpa [ha.2] using ha.1.2.2
      rw [hempty]
      exact Set.finite_empty

/-- Theorem 1.2(iii): fixed degree and arbitrary rank. -/
theorem finiteness_classic_fixed_degree
    (t : ℝ) (ht : 0 < t) (d : ℕ) (htd : t ≤ d) :
    {a | M.classic t a ∧ M.degree a = d}.Finite := by
  have hd : 1 ≤ d := by
    have hdreal : (0 : ℝ) < d := ht.trans_le htd
    exact_mod_cast (show 0 < d by exact_mod_cast hdreal)
  apply finite_of_finite_keys_and_fibers
    (fun a ↦ M.classic t a ∧ M.degree a = d)
    M.rank {n | 0 < gClassicNat n d}
    (finite_positive_of_tendsto_atTop_atBot (gClassicNat_rank_tail d hd))
  · intro a ha
    simpa [ha.2] using M.classic_positive t a ht (by simpa [ha.2]) ha.1
  · intro n
    exact (M.classic_fixed_pair t n d).subset fun a ha ↦
      ⟨ha.1.1, ha.2, ha.1.2⟩

/-- Theorem 1.2(iv): all ranks at least three and all allowed degrees. -/
theorem finiteness_classic_global (t : ℝ) (ht : 0 < t) :
    {a | M.classic t a ∧ t ≤ M.degree a ∧ 3 ≤ M.rank a}.Finite := by
  have hpairs :
      {p : ℕ × ℕ |
        3 ≤ p.1 ∧ 1 ≤ p.2 ∧ 0 < gClassicNat p.1 p.2}.Finite :=
    finite_admissible_pairs_of_uniform_envelope
      gClassicNat gClassicEnvelopeNat 3
      (finite_positive_of_tendsto_atTop_atBot
        gClassicEnvelopeNat_tail)
      (fun d hd ↦ finite_positive_of_tendsto_atTop_atBot
        (gClassicNat_rank_tail d hd))
      (fun n d hn hd ↦ gClassicNat_le_envelope hn hd)
  apply finite_of_finite_keys_and_fibers
    (fun a ↦ M.classic t a ∧ t ≤ M.degree a ∧ 3 ≤ M.rank a)
    (fun a ↦ (M.rank a, M.degree a))
    {p | 3 ≤ p.1 ∧ 1 ≤ p.2 ∧ 0 < gClassicNat p.1 p.2} hpairs
  · intro a ha
    have hdreal : (0 : ℝ) < M.degree a := ht.trans_le ha.2.1
    have hd : 1 ≤ M.degree a := by
      have : 0 < M.degree a := by exact_mod_cast hdreal
      omega
    exact ⟨ha.2.2, hd, M.classic_positive t a ht ha.2.1 ha.1⟩
  · intro p
    by_cases htd : t ≤ p.2
    · exact (M.classic_fixed_pair t p.1 p.2).subset fun a ha ↦ by
        have hr := congrArg Prod.fst ha.2
        have hd := congrArg Prod.snd ha.2
        exact ⟨ha.1.1, hr, hd⟩
    · have hempty :
          {a | (M.classic t a ∧ t ≤ M.degree a ∧ 3 ≤ M.rank a) ∧
            (M.rank a, M.degree a) = p} = (∅ : Set α) := by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro ha
        apply htd
        have hd := congrArg Prod.snd ha.2
        change M.degree a = p.2 at hd
        rw [← hd]
        exact ha.1.2.1
      rw [hempty]
      exact Set.finite_empty

/-- Theorem 1.3(i), for a fixed rank from one through four. -/
theorem finiteness_integral_fixed_degree_low_rank
    (t : ℝ) (_ht : 0 < t) (n d : ℕ) (_htd : t ≤ d)
    (_hn : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4) :
    {a | M.integral t a ∧ M.rank a = n ∧ M.degree a = d}.Finite :=
  M.integral_fixed_pair t n d

/-- Theorem 1.3(ii): fixed rank at least five and varying degree. -/
theorem finiteness_integral_fixed_high_rank
    (t : ℝ) (ht : 0 < t) (n : ℕ) (hn : 5 ≤ n) :
    {a | M.integral t a ∧ M.rank a = n ∧ t ≤ M.degree a}.Finite := by
  apply finite_of_finite_keys_and_fibers
    (fun a ↦ M.integral t a ∧ M.rank a = n ∧ t ≤ M.degree a)
    M.degree {d | 0 < gIntegralNat n d}
    (finite_positive_of_tendsto_atTop_atBot (gIntegralNat_degree_tail n hn))
  · intro a ha
    simpa [ha.2.1] using M.integral_positive t a ht ha.2.2 ha.1
  · intro d
    by_cases htd : t ≤ d
    · exact (M.integral_fixed_pair t n d).subset fun a ha ↦
        ⟨ha.1.1, ha.1.2.1, ha.2⟩
    · have hempty :
          {a | (M.integral t a ∧ M.rank a = n ∧ t ≤ M.degree a) ∧
            M.degree a = d} = (∅ : Set α) := by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro ha
        apply htd
        simpa [ha.2] using ha.1.2.2
      rw [hempty]
      exact Set.finite_empty

/-- Theorem 1.3(iii): fixed degree and arbitrary rank. -/
theorem finiteness_integral_fixed_degree
    (t : ℝ) (ht : 0 < t) (d : ℕ) (htd : t ≤ d) :
    {a | M.integral t a ∧ M.degree a = d}.Finite := by
  have hd : 1 ≤ d := by
    have hdreal : (0 : ℝ) < d := ht.trans_le htd
    have : 0 < d := by exact_mod_cast hdreal
    omega
  apply finite_of_finite_keys_and_fibers
    (fun a ↦ M.integral t a ∧ M.degree a = d)
    M.rank {n | 0 < gIntegralNat n d}
    (finite_positive_of_tendsto_atTop_atBot (gIntegralNat_rank_tail d hd))
  · intro a ha
    simpa [ha.2] using M.integral_positive t a ht (by simpa [ha.2]) ha.1
  · intro n
    exact (M.integral_fixed_pair t n d).subset fun a ha ↦
      ⟨ha.1.1, ha.2, ha.1.2⟩

/-- Theorem 1.3(iv): all ranks at least five and all allowed degrees. -/
theorem finiteness_integral_global (t : ℝ) (ht : 0 < t) :
    {a | M.integral t a ∧ t ≤ M.degree a ∧ 5 ≤ M.rank a}.Finite := by
  have hpairs :
      {p : ℕ × ℕ |
        5 ≤ p.1 ∧ 1 ≤ p.2 ∧ 0 < gIntegralNat p.1 p.2}.Finite :=
    finite_admissible_pairs_of_uniform_envelope
      gIntegralNat gIntegralEnvelopeNat 5
      (finite_positive_of_tendsto_atTop_atBot
        gIntegralEnvelopeNat_tail)
      (fun d hd ↦ finite_positive_of_tendsto_atTop_atBot
        (gIntegralNat_rank_tail d hd))
      (fun n d hn hd ↦ gIntegralNat_le_envelope hn hd)
  apply finite_of_finite_keys_and_fibers
    (fun a ↦ M.integral t a ∧ t ≤ M.degree a ∧ 5 ≤ M.rank a)
    (fun a ↦ (M.rank a, M.degree a))
    {p | 5 ≤ p.1 ∧ 1 ≤ p.2 ∧ 0 < gIntegralNat p.1 p.2} hpairs
  · intro a ha
    have hdreal : (0 : ℝ) < M.degree a := ht.trans_le ha.2.1
    have hd : 1 ≤ M.degree a := by
      have : 0 < M.degree a := by exact_mod_cast hdreal
      omega
    exact ⟨ha.2.2, hd, M.integral_positive t a ht ha.2.1 ha.1⟩
  · intro p
    by_cases htd : t ≤ p.2
    · exact (M.integral_fixed_pair t p.1 p.2).subset fun a ha ↦ by
        have hr := congrArg Prod.fst ha.2
        have hd := congrArg Prod.snd ha.2
        exact ⟨ha.1.1, hr, hd⟩
    · have hempty :
          {a | (M.integral t a ∧ t ≤ M.degree a ∧ 5 ≤ M.rank a) ∧
            (M.rank a, M.degree a) = p} = (∅ : Set α) := by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro ha
        apply htd
        have hd := congrArg Prod.snd ha.2
        change M.degree a = p.2 at hd
        rw [← hd]
        exact ha.1.2.1
      rw [hempty]
      exact Set.finite_empty

end MainFinitenessFramework

end TraceEuclidean
