import TraceEuclidean.V15HunterGeneralTraceBound
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Coefficient bridge for the general Hunter generator

This module proves Newton's first two identities in arbitrary degree and
applies them to a primitive algebraic integer.  It converts the quadratic
trace expression produced by the general Hunter argument into the first two
coefficients of the integral minimal polynomial.
-/

namespace TraceEuclidean

noncomputable section

open Algebra NumberField Polynomial

/-- Adding one entry to a multiset adds the expected cross term to its second
elementary symmetric function. -/
theorem v15_esymm_two_cons {R : Type*} [CommRing R]
    (a : R) (s : Multiset R) :
    (a ::ₘ s).esymm 2 = s.esymm 2 + a * s.sum := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons,
    Multiset.powersetCard_one, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_apply, Multiset.prod_cons]
  simpa using
    (Multiset.sum_map_mul_left (s := s) (a := a)
      (f := fun x : R => x))

/-- Newton's second identity for an arbitrary multiset over a commutative
ring. -/
theorem v15_multiset_sum_sq_eq_sum_sq_sub_two_esymm
    {R : Type*} [CommRing R] (s : Multiset R) :
    (s.map fun x => x ^ 2).sum = s.sum ^ 2 - 2 * s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm]
  | @cons a s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, ih,
        v15_esymm_two_cons]
      ring

/-- The trace of the square of a power-basis generator is the sum of the
squares of the roots of its minimal polynomial. -/
theorem v15_powerBasis_map_trace_gen_sq_eq_sum_roots_sq
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [Algebra.IsSeparable F L]
    (pb : PowerBasis F L) :
    algebraMap F (AlgebraicClosure F)
        (Algebra.trace F L (pb.gen ^ 2)) =
      (((minpoly F pb.gen).aroots (AlgebraicClosure F)).map
        (fun x => x ^ 2)).sum := by
  letI := Classical.decEq (AlgebraicClosure F)
  rw [trace_eq_sum_embeddings (E := AlgebraicClosure F)]
  simp only [map_pow]
  have hsum :
      (∑ σ : L →ₐ[F] AlgebraicClosure F, (σ pb.gen) ^ 2) =
        ∑ x : {y : AlgebraicClosure F //
          y ∈ (minpoly F pb.gen).aroots (AlgebraicClosure F)},
            x.1 ^ 2 :=
    Fintype.sum_equiv pb.liftEquiv'
      (fun σ : L →ₐ[F] AlgebraicClosure F => (σ pb.gen) ^ 2)
      (fun x : {y : AlgebraicClosure F //
        y ∈ (minpoly F pb.gen).aroots (AlgebraicClosure F)} =>
          x.1 ^ 2)
      (by intro σ; simp)
  rw [hsum]
  rw [Finset.sum_mem_multiset, Finset.sum_eq_multiset_sum,
    Multiset.toFinset_val, Multiset.dedup_eq_self.mpr]
  · exact nodup_roots
      ((separable_map (algebraMap F (AlgebraicClosure F))).mpr
        (Algebra.IsSeparable.isSeparable F pb.gen))
  · intro x
    rfl

/-- Vieta's formula identifies the coefficient two places below the leading
coefficient with the second elementary symmetric function of the roots. -/
theorem v15_powerBasis_map_secondCoeff_eq_esymm_roots
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (pb : PowerBasis F L) (hdim : 2 ≤ pb.dim) :
    algebraMap F (AlgebraicClosure F)
        (pb.minpolyGen.coeff (pb.dim - 2)) =
      ((minpoly F pb.gen).aroots (AlgebraicClosure F)).esymm 2 := by
  let p := (minpoly F pb.gen).map
    (algebraMap F (AlgebraicClosure F))
  have hpdeg : p.natDegree = pb.dim := by
    simp [p]
  have hk : pb.dim - 2 ≤ p.natDegree := by omega
  have hv := Polynomial.coeff_eq_esymm_roots_of_splits
    (IsAlgClosed.splits p) hk
  have hsub : pb.dim - (pb.dim - 2) = 2 := by omega
  rw [hpdeg, hsub] at hv
  have hpmonic : p.Monic := (minpoly.monic pb.isIntegral_gen).map _
  rw [hpmonic.leadingCoeff] at hv
  norm_num at hv
  simpa [p, Polynomial.aroots_def, PowerBasis.minpolyGen_eq] using hv

/-- Newton's second trace identity for a power-basis generator in arbitrary
degree at least two. -/
theorem v15_powerBasis_trace_gen_sq
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [Algebra.IsSeparable F L]
    (pb : PowerBasis F L) (hdim : 2 ≤ pb.dim) :
    Algebra.trace F L (pb.gen ^ 2) =
      pb.minpolyGen.coeff (pb.dim - 1) ^ 2 -
        2 * pb.minpolyGen.coeff (pb.dim - 2) := by
  apply (algebraMap F (AlgebraicClosure F)).injective
  rw [v15_powerBasis_map_trace_gen_sq_eq_sum_roots_sq pb,
    map_sub, map_pow, map_mul, map_ofNat]
  rw [v15_multiset_sum_sq_eq_sum_sq_sub_two_esymm]
  rw [v15_powerBasis_map_secondCoeff_eq_esymm_roots pb hdim]
  have htrace := PowerBasis.trace_gen_eq_nextCoeff_minpoly pb
  have hnext :
      (minpoly F pb.gen).nextCoeff =
        pb.minpolyGen.coeff (pb.dim - 1) := by
    simp [Polynomial.nextCoeff, pb.dim_pos.ne',
      PowerBasis.minpolyGen_eq]
  rw [hnext] at htrace
  have hsum := PowerBasis.trace_gen_eq_sum_roots pb
    (IsAlgClosed.splits ((minpoly F pb.gen).map
      (algebraMap F (AlgebraicClosure F))))
  rw [htrace, map_neg] at hsum
  rw [← hsum]
  ring

/-- The first signed coefficient of the degree-`d` integral minimal
polynomial. -/
def v15GeneralS1 (K : Type*) [Field K] [NumberField K]
    (d : ℕ) (a : 𝓞 K) : ℤ :=
  -(minpoly ℤ (a : K)).coeff (d - 1)

/-- The second signed coefficient of the degree-`d` integral minimal
polynomial. -/
def v15GeneralS2 (K : Type*) [Field K] [NumberField K]
    (d : ℕ) (a : 𝓞 K) : ℤ :=
  (minpoly ℤ (a : K)).coeff (d - 2)

/-- Coefficient form of the Hunter quadratic trace expression. -/
def v15GeneralSpread (d : ℕ) (s1 s2 : ℤ) : ℤ :=
  (d : ℤ) * (s1 ^ 2 - 2 * s2) - s1 ^ 2

/-- The field trace of a primitive algebraic integer is its first signed
integral coefficient. -/
theorem v15_general_trace_eq_s1
    (K : Type*) [Field K] [NumberField K]
    (d : ℕ) (hdegree : Module.finrank ℚ K = d) (hd : 0 < d)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    Algebra.trace ℚ K (a : K) = (v15GeneralS1 K d a : ℚ) := by
  let hint : IsIntegral ℚ (a : K) := IsIntegral.of_finite ℚ (a : K)
  let hsub : Algebra.adjoin ℚ {(a : K)} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hint.isAlgebraic hgen
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hint hsub
  have hdim : pb.dim = d := by
    rw [PowerBasis.ofAdjoinEqTop_dim]
    have h := hgen
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
    exact h.trans hdegree
  have ht := PowerBasis.trace_gen_eq_nextCoeff_minpoly pb
  have hnext : pb.minpolyGen.nextCoeff =
      pb.minpolyGen.coeff (d - 1) := by
    simp [Polynomial.nextCoeff, hdim, hd.ne']
  rw [← pb.minpolyGen_eq, hnext] at ht
  have hmin : pb.minpolyGen =
      (minpoly ℤ (a : K)).map (algebraMap ℤ ℚ) := by
    rw [pb.minpolyGen_eq]
    exact minpoly.isIntegrallyClosed_eq_field_fractions'
      ℚ a.isIntegral_coe
  rw [hmin] at ht
  simpa [pb, v15GeneralS1, Polynomial.coeff_map] using ht

/-- Newton's second identity for a primitive algebraic integer of arbitrary
degree at least two. -/
theorem v15_general_trace_sq_eq_s1_sq_sub_two_s2
    (K : Type*) [Field K] [NumberField K]
    (d : ℕ) (hdegree : Module.finrank ℚ K = d) (hd : 2 ≤ d)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    Algebra.trace ℚ K ((a : K) ^ 2) =
      (v15GeneralS1 K d a : ℚ) ^ 2 -
        2 * (v15GeneralS2 K d a : ℚ) := by
  let hint : IsIntegral ℚ (a : K) := IsIntegral.of_finite ℚ (a : K)
  let hsub : Algebra.adjoin ℚ {(a : K)} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hint.isAlgebraic hgen
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hint hsub
  have hdim : pb.dim = d := by
    rw [PowerBasis.ofAdjoinEqTop_dim]
    have h := hgen
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
    exact h.trans hdegree
  have ht := v15_powerBasis_trace_gen_sq pb (hdim.trans_ge hd)
  have hmin : pb.minpolyGen =
      (minpoly ℤ (a : K)).map (algebraMap ℤ ℚ) := by
    rw [pb.minpolyGen_eq]
    exact minpoly.isIntegrallyClosed_eq_field_fractions'
      ℚ a.isIntegral_coe
  rw [hmin, hdim] at ht
  simpa [pb, v15GeneralS1, v15GeneralS2,
    Polynomial.coeff_map] using ht

/-- The integral trace of a primitive algebraic integer is its first signed
integral coefficient. -/
theorem v15_general_intTrace_eq_s1
    (K : Type*) [Field K] [NumberField K]
    (d : ℕ) (hdegree : Module.finrank ℚ K = d) (hd : 0 < d)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    Algebra.intTrace ℤ (𝓞 K) a = v15GeneralS1 K d a := by
  apply (Int.cast_injective :
    Function.Injective (fun z : ℤ => (z : ℚ)))
  change algebraMap ℤ ℚ (Algebra.intTrace ℤ (𝓞 K) a) =
    algebraMap ℤ ℚ (v15GeneralS1 K d a)
  rw [Algebra.algebraMap_intTrace
    (A := ℤ) (K := ℚ) (L := K) (B := 𝓞 K)]
  exact v15_general_trace_eq_s1 K d hdegree hd a hgen

/-- The Hunter trace expression is exactly the integral coefficient spread
for a primitive algebraic integer. -/
theorem v15_general_trace_expression_eq_spread
    (K : Type*) [Field K] [NumberField K]
    (d : ℕ) (hdegree : Module.finrank ℚ K = d) (hd : 2 ≤ d)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    (d : ℚ) * Algebra.trace ℚ K ((a : K) ^ 2) -
        Algebra.trace ℚ K (a : K) ^ 2 =
      (v15GeneralSpread d (v15GeneralS1 K d a)
        (v15GeneralS2 K d a) : ℚ) := by
  rw [v15_general_trace_eq_s1 K d hdegree (by omega) a hgen]
  rw [v15_general_trace_sq_eq_s1_sq_sub_two_s2
    K d hdegree hd a hgen]
  simp only [v15GeneralSpread]
  push_cast
  ring

open scoped Classical in
/-- The rational minimal polynomial of a primitive element of a totally real
number field splits over the real numbers. -/
theorem v15_primitive_minpoly_splits_real
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    ((minpoly ℚ (a : K)).map (algebraMap ℚ ℝ)).Splits := by
  letI : NumberField.IsTotallyReal K := hreal
  let hint : IsIntegral ℚ (a : K) := IsIntegral.of_finite ℚ (a : K)
  let hsub : Algebra.adjoin ℚ {(a : K)} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hint.isAlgebraic hgen
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hint hsub
  let p := (minpoly ℚ (a : K)).map (algebraMap ℚ ℝ)
  have hcomplex : (p.map (algebraMap ℝ ℂ)).Splits :=
    IsAlgClosed.splits _
  apply hcomplex.of_splits_map (algebraMap ℝ ℂ)
  intro z hz
  have hcomp :
      (algebraMap ℝ ℂ).comp (algebraMap ℚ ℝ) = algebraMap ℚ ℂ := by
    ext q
    simp
  have hz' : z ∈ (minpoly ℚ (a : K)).aroots ℂ := by
    simpa [p, Polynomial.aroots_def, Polynomial.map_map, hcomp] using hz
  let σ : K →ₐ[ℚ] ℂ := (pb.liftEquiv').symm ⟨z, hz'⟩
  have hsigma : σ pb.gen = z := by
    calc
      σ pb.gen = (pb.liftEquiv' σ).1 :=
        (PowerBasis.liftEquiv'_apply_coe pb σ).symm
      _ = z := congrArg Subtype.val
        (pb.liftEquiv'.apply_symm_apply ⟨z, hz'⟩)
  let hσreal :=
    NumberField.IsTotallyReal.complexEmbedding_isReal σ.toRingHom
  refine ⟨hσreal.embedding (a : K), ?_⟩
  change ((hσreal.embedding (a : K) : ℝ) : ℂ) = z
  rw [NumberField.ComplexEmbedding.IsReal.coe_embedding_apply hσreal]
  simpa [pb] using hsigma

/-- The integral minimal polynomial of a primitive element of a totally real
number field splits over the real numbers. -/
theorem v15_primitive_integral_minpoly_splits_real
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤) :
    ((minpoly ℤ (a : K)).map (algebraMap ℤ ℝ)).Splits := by
  have hq := v15_primitive_minpoly_splits_real K hreal a hgen
  have hmin :
      (minpoly ℤ (a : K)).map (algebraMap ℤ ℚ) =
        minpoly ℚ (a : K) :=
    (minpoly.isIntegrallyClosed_eq_field_fractions'
      ℚ a.isIntegral_coe).symm
  have hmap :
      (((minpoly ℤ (a : K)).map (algebraMap ℤ ℚ)).map
        (algebraMap ℚ ℝ)).Splits := by
    rw [hmin]
    exact hq
  have hcomp :
      (algebraMap ℚ ℝ).comp (algebraMap ℤ ℚ) =
        algebraMap ℤ ℝ := by
    ext z
    simp
  have hpoly :
      ((minpoly ℤ (a : K)).map (algebraMap ℤ ℚ)).map
          (algebraMap ℚ ℝ) =
        (minpoly ℤ (a : K)).map (algebraMap ℤ ℝ) := by
    rw [Polynomial.map_map, hcomp]
  rw [hpoly] at hmap
  exact hmap

open scoped Classical in
/-- In prime degree, the general Hunter construction produces a primitive
integral generator whose first two coefficients satisfy the normalized trace
conditions and the strict coefficient-spread bound. -/
theorem v15_exists_trace_normalized_primitive_coefficients_of_hunterBall
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
      0 ≤ v15GeneralS1 K (n + 1) a ∧
      2 * v15GeneralS1 K (n + 1) a ≤ n + 1 ∧
      ((v15GeneralSpread (n + 1)
        (v15GeneralS1 K (n + 1) a)
        (v15GeneralS2 K (n + 1) a) : ℤ) : ℝ) <
          (n + 1 : ℝ) * r ^ 2 := by
  obtain ⟨a, hgen, htraceNonneg, htraceHalf, hbound⟩ :=
    v15_exists_trace_normalized_primitive_integer_of_hunterBall
      K hreal hdegree hprime hn r hr hball
  have hs1 := v15_general_intTrace_eq_s1
    K (n + 1) hdegree (by omega) a hgen
  refine ⟨a, hgen, ?_, ?_, ?_⟩
  · rwa [hs1] at htraceNonneg
  · rwa [hs1] at htraceHalf
  · have hq := v15_general_trace_expression_eq_spread
      K (n + 1) hdegree (by omega) a hgen
    have hrealEq := congrArg (fun q : ℚ => (q : ℝ)) hq
    push_cast at hrealEq
    rw [hrealEq] at hbound
    exact hbound

/-- A monic irreducible integral polynomial satisfying the exact front-end
conditions supplied by the Hunter argument: its roots are real, its trace is
normalized, and its first two coefficients satisfy the strict spread bound. -/
def V15HunterPolynomialCandidate (d : ℕ) (B : ℝ)
    (f : ℤ[X]) : Prop :=
  f.Monic ∧
  Irreducible f ∧
  f.natDegree = d ∧
  (f.map (algebraMap ℤ ℝ)).Splits ∧
  0 ≤ -f.coeff (d - 1) ∧
  2 * (-f.coeff (d - 1)) ≤ d ∧
  ((v15GeneralSpread d (-f.coeff (d - 1))
    (f.coeff (d - 2)) : ℤ) : ℝ) < B

/-- In degree five, the normalized trace coefficient has exactly the three
values used to start the finite Hunter search. -/
theorem v15_hunterPolynomialCandidate_degreeFive_trace_cases
    {B : ℝ} {f : ℤ[X]}
    (h : V15HunterPolynomialCandidate 5 B f) :
    -f.coeff 4 = 0 ∨ -f.coeff 4 = 1 ∨ -f.coeff 4 = 2 := by
  rcases h with ⟨_, _, _, _, hnonneg, hhalf, _⟩
  norm_num at hnonneg hhalf
  omega

/-- In degree seven, the normalized trace coefficient has exactly the four
values used to start the finite Hunter search. -/
theorem v15_hunterPolynomialCandidate_degreeSeven_trace_cases
    {B : ℝ} {f : ℤ[X]}
    (h : V15HunterPolynomialCandidate 7 B f) :
    -f.coeff 6 = 0 ∨ -f.coeff 6 = 1 ∨
      -f.coeff 6 = 2 ∨ -f.coeff 6 = 3 := by
  rcases h with ⟨_, _, _, _, hnonneg, hhalf, _⟩
  norm_num at hnonneg hhalf
  omega

open scoped Classical in
/-- The general Hunter ball theorem produces an integral polynomial satisfying
all front-end conditions required by the later finite enumeration. -/
theorem v15_exists_hunterPolynomialCandidate_of_hunterBall
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
    ∃ f : ℤ[X],
      V15HunterPolynomialCandidate (n + 1)
        ((n + 1 : ℝ) * r ^ 2) f := by
  obtain ⟨a, hgen, hs1Nonneg, hs1Half, hspread⟩ :=
    v15_exists_trace_normalized_primitive_coefficients_of_hunterBall
      K hreal hdegree hprime hn r hr hball
  let f : ℤ[X] := minpoly ℤ (a : K)
  have hdegQ : (minpoly ℚ (a : K)).natDegree = n + 1 := by
    have h := hgen
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
    exact h.trans hdegree
  have hmin :
      f.map (algebraMap ℤ ℚ) = minpoly ℚ (a : K) := by
    simpa [f] using
      (minpoly.isIntegrallyClosed_eq_field_fractions'
        ℚ a.isIntegral_coe).symm
  have hdeg : f.natDegree = n + 1 := by
    have hmap := (minpoly.monic a.isIntegral_coe).natDegree_map
      (algebraMap ℤ ℚ)
    change (f.map (algebraMap ℤ ℚ)).natDegree = f.natDegree at hmap
    rw [hmin, hdegQ] at hmap
    exact hmap.symm
  refine ⟨f, ?_, minpoly.irreducible a.isIntegral_coe, hdeg,
    v15_primitive_integral_minpoly_splits_real K hreal a hgen,
    ?_, ?_, ?_⟩
  · exact minpoly.monic a.isIntegral_coe
  · simpa [f, v15GeneralS1] using hs1Nonneg
  · simpa [f, v15GeneralS1] using hs1Half
  · simpa [f, v15GeneralS1, v15GeneralS2] using hspread

end

end TraceEuclidean
