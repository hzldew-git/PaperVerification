import TraceEuclidean.HunterGeneralNumberFieldProjection
import TraceEuclidean.CubicGeneratorSpread

/-!
# Trace form of the general Hunter bound

This module rewrites the squared norm of a centered Minkowski embedding as
the usual quadratic trace expression and packages the arbitrary-dimensional
Minkowski ball theorem as an algebraic-integer existence theorem.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Module
open scoped NumberField

/-- Every integer has, up to sign and translation by a positive modulus, a
representative in the first half of a complete residue interval. -/
theorem exists_signed_integer_normalization
    (t : ℤ) (d : ℕ) (hd : 0 < d) :
    ∃ k : ℤ,
      (0 ≤ t - k * (d : ℤ) ∧ 2 * (t - k * (d : ℤ)) ≤ d) ∨
      (0 ≤ -t - k * (d : ℤ) ∧ 2 * (-t - k * (d : ℤ)) ≤ d) := by
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  have hremNonneg : 0 ≤ t % (d : ℤ) :=
    Int.emod_nonneg t (ne_of_gt hdZ)
  have hremLt : t % (d : ℤ) < d :=
    Int.emod_lt_of_pos t hdZ
  have hdecomp : t / (d : ℤ) * d + t % (d : ℤ) = t :=
    Int.ediv_mul_add_emod t d
  by_cases hhalf : 2 * (t % (d : ℤ)) ≤ d
  · refine ⟨t / (d : ℤ), Or.inl ⟨?_, ?_⟩⟩ <;> omega
  · let k : ℤ := -(t / (d : ℤ)) - 1
    have hcalc : -t - k * (d : ℤ) = (d : ℤ) - t % (d : ℤ) := by
      dsimp only [k]
      calc
        -t - (-(t / (d : ℤ)) - 1) * (d : ℤ) =
            (d : ℤ) - (t - t / (d : ℤ) * d) := by ring
        _ = (d : ℤ) - t % (d : ℤ) := by omega
    refine ⟨k, Or.inr ?_⟩
    rw [hcalc]
    omega

/-- Translation by a rational scalar preserves generation of the ambient
field by one element. -/
theorem adjoin_sub_algebraMap_eq_top
    (K : Type*) [Field K] [NumberField K] (a : K) (q : ℚ)
    (hgen : IntermediateField.adjoin ℚ {a} = ⊤) :
    IntermediateField.adjoin ℚ {a - algebraMap ℚ K q} = ⊤ := by
  let b := a - algebraMap ℚ K q
  have hb : b ∈ IntermediateField.adjoin ℚ {b} :=
    IntermediateField.mem_adjoin_simple_self ℚ b
  have hq : algebraMap ℚ K q ∈ IntermediateField.adjoin ℚ {b} :=
    (IntermediateField.adjoin ℚ {b}).algebraMap_mem q
  have ha : a ∈ IntermediateField.adjoin ℚ {b} := by
    rw [show a = b + algebraMap ℚ K q by simp [b]]
    exact (IntermediateField.adjoin ℚ {b}).add_mem hb hq
  have hle :
      IntermediateField.adjoin ℚ {a} ≤ IntermediateField.adjoin ℚ {b} :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ha)
  change IntermediateField.adjoin ℚ {b} = ⊤
  exact top_unique (hgen ▸ hle)

/-- Negation followed by rational translation preserves generation of the
ambient field by one element. -/
theorem adjoin_neg_sub_algebraMap_eq_top
    (K : Type*) [Field K] [NumberField K] (a : K) (q : ℚ)
    (hgen : IntermediateField.adjoin ℚ {a} = ⊤) :
    IntermediateField.adjoin ℚ {-a - algebraMap ℚ K q} = ⊤ := by
  let b := -a - algebraMap ℚ K q
  have hb : b ∈ IntermediateField.adjoin ℚ {b} :=
    IntermediateField.mem_adjoin_simple_self ℚ b
  have hq : algebraMap ℚ K q ∈ IntermediateField.adjoin ℚ {b} :=
    (IntermediateField.adjoin ℚ {b}).algebraMap_mem q
  have ha : a ∈ IntermediateField.adjoin ℚ {b} := by
    rw [show a = -(b + algebraMap ℚ K q) by simp [b]]
    exact (IntermediateField.adjoin ℚ {b}).neg_mem
      ((IntermediateField.adjoin ℚ {b}).add_mem hb hq)
  have hle :
      IntermediateField.adjoin ℚ {a} ≤ IntermediateField.adjoin ℚ {b} :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ha)
  change IntermediateField.adjoin ℚ {b} = ⊤
  exact top_unique (hgen ▸ hle)

/-- The quadratic trace expression is invariant under rational translation. -/
theorem trace_expression_sub_algebraMap
    (K : Type*) [Field K] [NumberField K] (d : ℕ)
    (hdegree : Module.finrank ℚ K = d) (a : K) (q : ℚ) :
    (d : ℚ) * Algebra.trace ℚ K ((a - algebraMap ℚ K q) ^ 2) -
        Algebra.trace ℚ K (a - algebraMap ℚ K q) ^ 2 =
      (d : ℚ) * Algebra.trace ℚ K (a ^ 2) -
        Algebra.trace ℚ K a ^ 2 := by
  have hsq : (a - algebraMap ℚ K q) ^ 2 =
      a ^ 2 - (2 * q) • a + algebraMap ℚ K (q ^ 2) := by
    simp only [Algebra.smul_def, map_mul, map_pow, map_ofNat]
    ring
  rw [hsq]
  simp only [map_sub, map_add, map_smul, Algebra.trace_algebraMap, hdegree]
  ring

/-- The quadratic trace expression is invariant under negation. -/
theorem trace_expression_neg
    (K : Type*) [Field K] [NumberField K] (d : ℕ) (a : K) :
    (d : ℚ) * Algebra.trace ℚ K ((-a) ^ 2) -
        Algebra.trace ℚ K (-a) ^ 2 =
      (d : ℚ) * Algebra.trace ℚ K (a ^ 2) -
        Algebra.trace ℚ K a ^ 2 := by
  simp

/-- Integral trace after translating an algebraic integer. -/
theorem intTrace_sub_integer
    (K : Type*) [Field K] [NumberField K] (d : ℕ)
    (hdegree : Module.finrank ℚ K = d) (a : 𝓞 K) (k : ℤ) :
    Algebra.intTrace ℤ (𝓞 K) (a - algebraMap ℤ (𝓞 K) k) =
      Algebra.intTrace ℤ (𝓞 K) a - k * (d : ℤ) := by
  rw [map_sub, Algebra.intTrace_eq_trace, Algebra.trace_algebraMap]
  rw [NumberField.RingOfIntegers.rank K, hdegree]
  ring

/-- Integral trace after negating and translating an algebraic integer. -/
theorem intTrace_neg_sub_integer
    (K : Type*) [Field K] [NumberField K] (d : ℕ)
    (hdegree : Module.finrank ℚ K = d) (a : 𝓞 K) (k : ℤ) :
    Algebra.intTrace ℤ (𝓞 K) (-a - algebraMap ℤ (𝓞 K) k) =
      -Algebra.intTrace ℤ (𝓞 K) a - k * (d : ℤ) := by
  rw [map_sub, map_neg, Algebra.intTrace_eq_trace,
    Algebra.trace_algebraMap]
  rw [NumberField.RingOfIntegers.rank K, hdegree]
  ring

/-- Every primitive algebraic integer can be signed and translated so that
its integral trace lies between `0` and half the field degree, without changing
the quadratic trace expression. -/
theorem exists_trace_normalized_generator
    (K : Type*) [Field K] [NumberField K] (d : ℕ)
    (hdegree : Module.finrank ℚ K = d) (hd : 0 < d)
    (a : 𝓞 K) (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    ∃ b : 𝓞 K,
      IntermediateField.adjoin ℚ {(b : K)} = ⊤ ∧
      0 ≤ Algebra.intTrace ℤ (𝓞 K) b ∧
      2 * Algebra.intTrace ℤ (𝓞 K) b ≤ d ∧
      (d : ℚ) * Algebra.trace ℚ K ((b : K) ^ 2) -
          Algebra.trace ℚ K (b : K) ^ 2 =
        (d : ℚ) * Algebra.trace ℚ K ((a : K) ^ 2) -
          Algebra.trace ℚ K (a : K) ^ 2 := by
  let t := Algebra.intTrace ℤ (𝓞 K) a
  obtain ⟨k, hpos | hneg⟩ :=
    exists_signed_integer_normalization t d hd
  · let b : 𝓞 K := a - algebraMap ℤ (𝓞 K) k
    have hbcoe : (b : K) = (a : K) - algebraMap ℚ K (k : ℚ) := by
      simp [b]
    refine ⟨b, ?_, ?_, ?_, ?_⟩
    · rw [hbcoe]
      exact adjoin_sub_algebraMap_eq_top K (a : K) (k : ℚ) hgen
    · rw [intTrace_sub_integer K d hdegree a k]
      exact hpos.1
    · rw [intTrace_sub_integer K d hdegree a k]
      exact hpos.2
    · rw [hbcoe]
      exact trace_expression_sub_algebraMap K d hdegree (a : K) (k : ℚ)
  · let b : 𝓞 K := -a - algebraMap ℤ (𝓞 K) k
    have hbcoe : (b : K) = -(a : K) - algebraMap ℚ K (k : ℚ) := by
      simp [b]
    refine ⟨b, ?_, ?_, ?_, ?_⟩
    · rw [hbcoe]
      exact adjoin_neg_sub_algebraMap_eq_top K (a : K) (k : ℚ) hgen
    · rw [intTrace_neg_sub_integer K d hdegree a k]
      exact hneg.1
    · rw [intTrace_neg_sub_integer K d hdegree a k]
      exact hneg.2
    · rw [hbcoe, trace_expression_sub_algebraMap K d hdegree
          (-(a : K)) (k : ℚ)]
      exact trace_expression_neg K d (a : K)

/-- In a prime-degree field, every nonrational element generates the field. -/
theorem adjoin_eq_top_of_finrank_prime_of_not_rat
    (K : Type*) [Field K] [NumberField K]
    (hprime : Nat.Prime (Module.finrank ℚ K)) (a : K)
    (hnotrat : ¬ ∃ q : ℚ, a = algebraMap ℚ K q) :
    IntermediateField.adjoin ℚ {a} = ⊤ := by
  letI : IsSimpleOrder (IntermediateField ℚ K) :=
    IntermediateField.isSimpleOrder_of_finrank_prime ℚ K hprime
  rcases eq_bot_or_eq_top (IntermediateField.adjoin ℚ {a}) with hbot | htop
  · exfalso
    have ha : a ∈ (⊥ : IntermediateField ℚ K) := by
      rw [← hbot]
      exact IntermediateField.mem_adjoin_simple_self ℚ a
    obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp ha
    exact hnotrat ⟨q, hq.symm⟩
  · exact htop

open scoped Classical in
/-- In degree `n + 1`, the centered Euclidean norm is the standard quadratic
trace expression. -/
theorem hunterGeneral_center_norm_eq_trace_expression
    (K : Type*) [Field K] [NumberField K] {n : ℕ}
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = n + 1) (a : K) :
    let e := euclideanOne K
    let he : inner ℝ e e ≠ 0 := by
      rw [inner_euclideanOne_self_eq_degree K hreal, hdegree]
      positivity
    (n + 1 : ℝ) *
        ‖hunterCenterLinearMap e he (euclideanEmbedding K a)‖ ^ 2 =
      (n + 1 : ℝ) *
          ((Algebra.trace ℚ K (a ^ 2) : ℚ) : ℝ) -
        ((Algebra.trace ℚ K a : ℚ) : ℝ) ^ 2 := by
  letI : NumberField.IsTotallyReal K := hreal
  dsimp only
  let he : inner ℝ (euclideanOne K) (euclideanOne K) ≠ 0 := by
    rw [inner_euclideanOne_self_eq_degree K hreal, hdegree]
    positivity
  rw [← real_inner_self_eq_norm_sq]
  change (n + 1 : ℝ) * inner ℝ
      (hunterCenter (euclideanOne K) (euclideanEmbedding K a))
      (hunterCenter (euclideanOne K) (euclideanEmbedding K a)) = _
  rw [inner_center_center (euclideanOne K)
    (euclideanEmbedding K a) (euclideanEmbedding K a) he]
  rw [inner_euclideanOne_self_eq_degree K hreal, hdegree]
  rw [inner_euclideanOne_euclideanEmbedding K a]
  rw [inner_euclideanEmbedding_self K a]
  push_cast
  field_simp

open scoped Classical in
/-- The general Minkowski ball condition produces a nonrational algebraic
integer satisfying the corresponding strict quadratic trace bound. -/
theorem exists_nonrational_integer_of_hunterBall
    (K : Type*) [Field K] [NumberField K] {n : ℕ}
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = n + 1)
    (hn : 0 < n) (r : ℝ) (hr : 0 < r)
    (hball :
      ((|NumberField.discr K| : ℤ) : ℝ) *
          (((2 : ℝ) ^ n) ^ 2) <
        (n + 1 : ℝ) *
          (euclideanUnitBallVolume n * r ^ n) ^ 2) :
    ∃ a : 𝓞 K,
      (¬ ∃ q : ℚ, (a : K) = algebraMap ℚ K q) ∧
      (n + 1 : ℝ) *
          ((Algebra.trace ℚ K ((a : K) ^ 2) : ℚ) : ℝ) -
        ((Algebra.trace ℚ K (a : K) : ℚ) : ℝ) ^ 2 <
          (n + 1 : ℝ) * r ^ 2 := by
  obtain ⟨bz, hbzero⟩ :=
    exists_euclidean_integerLattice_basis_one_general K hdegree
  obtain ⟨x, hx, hxnorm⟩ :=
    hunterGeneral_projected_shortVector_of_ball
      K hreal hdegree hn bz hbzero r hr hball
  let a : 𝓞 K := hunterGeneralAlgebraicIntegerLift K bz x
  refine ⟨a, hunterGeneralAlgebraicIntegerLift_not_rat
    K bz hbzero x hx, ?_⟩
  let b := bz.ofZLatticeBasis ℝ
  have hbzero' : b 0 = euclideanOne K := by
    rw [show b 0 =
        (((bz 0 : NumberField.mixedEmbedding.euclidean.integerLattice K) :
          NumberField.mixedEmbedding.euclidean.mixedSpace K)) by
      exact bz.ofZLatticeBasis_apply ℝ
        (NumberField.mixedEmbedding.euclidean.integerLattice K) 0]
    exact hbzero
  have hcenter := hunterGeneralAlgebraicIntegerLift_center K bz x
  have heone :
      inner ℝ (euclideanOne K) (euclideanOne K) ≠ 0 := by
    rw [inner_euclideanOne_self_eq_degree K hreal, hdegree]
    positivity
  have hcenterVal :
      hunterCenter (euclideanOne K)
          (euclideanEmbedding K (a : K)) =
        (((x : hunterGeneralProjectedLattice
            (bz.ofZLatticeBasis ℝ)) :
          (ℝ ∙ (bz.ofZLatticeBasis ℝ) 0)ᗮ) :
          NumberField.mixedEmbedding.euclidean.mixedSpace K) := by
    have hv := congrArg Subtype.val hcenter
    change hunterCenter ((bz.ofZLatticeBasis ℝ) 0)
        (euclideanEmbedding K (a : K)) = _ at hv
    have hzero : (bz.ofZLatticeBasis ℝ) 0 = euclideanOne K := by
      simpa [b] using hbzero'
    conv_lhs at hv => rw [hzero]
    exact hv
  have hcenterNorm :
      ‖hunterCenterLinearMap (euclideanOne K)
          heone
          (euclideanEmbedding K (a : K))‖ < r := by
    change ‖hunterCenter (euclideanOne K)
      (euclideanEmbedding K (a : K))‖ < r
    rw [hcenterVal]
    simpa using hxnorm
  have hsquare :
      ‖hunterCenterLinearMap (euclideanOne K)
          heone
          (euclideanEmbedding K (a : K))‖ ^ 2 < r ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg _) hr.le).2 hcenterNorm
  have htrace :=
    hunterGeneral_center_norm_eq_trace_expression
      K hreal hdegree (a : K)
  dsimp only at htrace
  rw [← htrace]
  exact mul_lt_mul_of_pos_left hsquare (by positivity)

open scoped Classical in
/-- In prime degree, the general Hunter ball condition produces a primitive
algebraic integer satisfying the strict quadratic trace bound. -/
theorem exists_primitive_integer_of_hunterBall
    (K : Type*) [Field K] [NumberField K] {n : ℕ}
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = n + 1)
    (hprime : Nat.Prime (n + 1))
    (hn : 0 < n) (r : ℝ) (hr : 0 < r)
    (hball :
      ((|NumberField.discr K| : ℤ) : ℝ) *
          (((2 : ℝ) ^ n) ^ 2) <
        (n + 1 : ℝ) *
          (euclideanUnitBallVolume n * r ^ n) ^ 2) :
    ∃ a : 𝓞 K,
      IntermediateField.adjoin ℚ {(a : K)} = ⊤ ∧
      (n + 1 : ℝ) *
          ((Algebra.trace ℚ K ((a : K) ^ 2) : ℚ) : ℝ) -
        ((Algebra.trace ℚ K (a : K) : ℚ) : ℝ) ^ 2 <
          (n + 1 : ℝ) * r ^ 2 := by
  obtain ⟨a, hnotrat, htrace⟩ :=
    exists_nonrational_integer_of_hunterBall
      K hreal hdegree hn r hr hball
  refine ⟨a, ?_, htrace⟩
  apply adjoin_eq_top_of_finrank_prime_of_not_rat K
  · rwa [hdegree]
  · exact hnotrat

open scoped Classical in
/-- In prime degree, the Hunter element can also be normalized to have integral
trace between `0` and half the degree, while retaining the strict trace bound. -/
theorem exists_trace_normalized_primitive_integer_of_hunterBall
    (K : Type*) [Field K] [NumberField K] {n : ℕ}
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = n + 1)
    (hprime : Nat.Prime (n + 1))
    (hn : 0 < n) (r : ℝ) (hr : 0 < r)
    (hball :
      ((|NumberField.discr K| : ℤ) : ℝ) *
          (((2 : ℝ) ^ n) ^ 2) <
        (n + 1 : ℝ) *
          (euclideanUnitBallVolume n * r ^ n) ^ 2) :
    ∃ a : 𝓞 K,
      IntermediateField.adjoin ℚ {(a : K)} = ⊤ ∧
      0 ≤ Algebra.intTrace ℤ (𝓞 K) a ∧
      2 * Algebra.intTrace ℤ (𝓞 K) a ≤ n + 1 ∧
      (n + 1 : ℝ) *
          ((Algebra.trace ℚ K ((a : K) ^ 2) : ℚ) : ℝ) -
        ((Algebra.trace ℚ K (a : K) : ℚ) : ℝ) ^ 2 <
          (n + 1 : ℝ) * r ^ 2 := by
  obtain ⟨a, hgen, htrace⟩ :=
    exists_primitive_integer_of_hunterBall
      K hreal hdegree hprime hn r hr hball
  obtain ⟨b, hgenb, htraceNonneg, htraceHalf, hinvariant⟩ :=
    exists_trace_normalized_generator
      K (n + 1) hdegree (by omega) a hgen
  refine ⟨b, hgenb, htraceNonneg, htraceHalf, ?_⟩
  have hinvariantReal :
      (n + 1 : ℝ) *
          ((Algebra.trace ℚ K ((b : K) ^ 2) : ℚ) : ℝ) -
        ((Algebra.trace ℚ K (b : K) : ℚ) : ℝ) ^ 2 =
      (n + 1 : ℝ) *
          ((Algebra.trace ℚ K ((a : K) ^ 2) : ℚ) : ℝ) -
        ((Algebra.trace ℚ K (a : K) : ℚ) : ℝ) ^ 2 := by
    exact_mod_cast hinvariant
  rw [hinvariantReal]
  exact htrace

end

end TraceEuclidean
