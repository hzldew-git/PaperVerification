import TraceEuclidean.TraceCovering

/-!
# Short independent lattice vectors from a covering bound

This file isolates the finite-dimensional perturbation argument needed for a reduction-theoretic
finiteness proof.  A family that stays uniformly close to a sufficiently large multiple of the
standard orthonormal basis remains linearly independent.  Applying a lattice covering hypothesis
at those scaled basis points therefore produces a uniformly bounded independent lattice family.
-/

namespace TraceEuclidean

noncomputable section

open scoped InnerProductSpace

/--
If every vector `v i` is within `R` of `T` times the standard orthonormal basis vector and
`card ι * R < T`, then the vectors `v i` are linearly independent.
-/
theorem linearIndependent_of_norm_sub_smul_basis_lt
    {ι : Type*} [Fintype ι]
    (v : ι → EuclideanSpace ℝ ι) (R T : ℝ)
    (hR : 0 ≤ R) (hT : (Fintype.card ι : ℝ) * R < T)
    (hclose : ∀ i, ‖v i - T • EuclideanSpace.basisFun ι ℝ i‖ < R) :
    LinearIndependent ℝ v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  let e : ι → EuclideanSpace ℝ ι :=
    fun i ↦ v i - T • EuclideanSpace.basisFun ι ℝ i
  have he (i : ι) : ‖e i‖ ≤ R := (hclose i).le
  have hv (i : ι) : v i = T • EuclideanSpace.basisFun ι ℝ i + e i := by
    simp [e]
  have hcoord (k : ι) :
      T * g k + ∑ i, g i * e i k = 0 := by
    have hk := congrArg (fun x : EuclideanSpace ℝ ι ↦ x k) hg
    simp_rw [hv] at hk
    simpa [EuclideanSpace.basisFun_apply, Pi.single_apply,
      Finset.sum_add_distrib, Finset.mul_sum, mul_ite, eq_comm, mul_assoc, mul_comm] using hk
  have hcoordBound (k : ι) :
      T * |g k| ≤ R * ∑ i, |g i| := by
    have hTnonneg : 0 ≤ T := by
      exact le_trans (mul_nonneg (Nat.cast_nonneg _) hR) hT.le
    calc
      T * |g k| = |T * g k| := by rw [abs_mul, abs_of_nonneg hTnonneg]
      _ = |∑ i, g i * e i k| := by
        rw [eq_neg_of_add_eq_zero_left (hcoord k), abs_neg]
      _ ≤ ∑ i, |g i * e i k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |g i| * R := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (PiLp.norm_apply_le (p := 2) (e i) k).trans (he i)
      _ = R * ∑ i, |g i| := by simp [Finset.mul_sum, mul_comm]
  have hsumBound :
      T * ∑ k, |g k| ≤
        (Fintype.card ι : ℝ) * R * ∑ i, |g i| := by
    calc
      T * ∑ k, |g k| = ∑ k, T * |g k| := by rw [Finset.mul_sum]
      _ ≤ ∑ _k : ι, R * ∑ i, |g i| :=
        Finset.sum_le_sum fun k _hk ↦ hcoordBound k
      _ = (Fintype.card ι : ℝ) * R * ∑ i, |g i| := by
        simp [mul_assoc]
  have hsumZero : ∑ i, |g i| = 0 := by
    have hsumNonneg : 0 ≤ ∑ i, |g i| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    nlinarith
  have habs : |g j| = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg fun i _hi ↦ abs_nonneg (g i)).mp hsumZero j
      (Finset.mem_univ j)
  exact abs_eq_zero.mp habs

/-
A covering bound produces one lattice point near each suitably scaled standard basis vector.
These lattice points are linearly independent and have a bound depending only on the covering
radius and the dimension.
-/
theorem exists_short_linearIndependent_of_cover
    {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (EuclideanSpace ℝ ι)) (R : ℝ) (hR : 0 ≤ R)
    (hcover : ∀ x : EuclideanSpace ℝ ι, ∃ l : L, ‖x - (l : EuclideanSpace ℝ ι)‖ < R) :
    ∃ v : ι → L,
      LinearIndependent ℝ (fun i ↦ (v i : EuclideanSpace ℝ ι)) ∧
        ∀ i, ‖(v i : EuclideanSpace ℝ ι)‖ <
          ((Fintype.card ι : ℝ) + 1) * R + 1 := by
  classical
  let T : ℝ := (Fintype.card ι : ℝ) * R + 1
  choose v hv using fun i ↦ hcover (T • EuclideanSpace.basisFun ι ℝ i)
  have hT : (Fintype.card ι : ℝ) * R < T := by
    simp [T]
  have hTnonneg : 0 ≤ T := by
    dsimp [T]
    positivity
  have hclose (i : ι) :
      ‖(v i : EuclideanSpace ℝ ι) - T • EuclideanSpace.basisFun ι ℝ i‖ < R := by
    simpa only [norm_sub_rev] using hv i
  refine ⟨v, linearIndependent_of_norm_sub_smul_basis_lt
    (fun i ↦ (v i : EuclideanSpace ℝ ι)) R T hR hT hclose, ?_⟩
  intro i
  have hbasis : ‖EuclideanSpace.basisFun ι ℝ i‖ = 1 := by
    simp [EuclideanSpace.basisFun_apply]
  have hscaled : ‖T • EuclideanSpace.basisFun ι ℝ i‖ = T := by
    rw [norm_smul, hbasis, mul_one, Real.norm_eq_abs, abs_of_nonneg hTnonneg]
  calc
    ‖(v i : EuclideanSpace ℝ ι)‖ =
        ‖((v i : EuclideanSpace ℝ ι) - T • EuclideanSpace.basisFun ι ℝ i) +
          T • EuclideanSpace.basisFun ι ℝ i‖ := by
            congr 1
            abel
    _ ≤ ‖(v i : EuclideanSpace ℝ ι) - T • EuclideanSpace.basisFun ι ℝ i‖ +
          ‖T • EuclideanSpace.basisFun ι ℝ i‖ := norm_add_le _ _
    _ < R + T := by rw [hscaled]; linarith [hclose i]
    _ = ((Fintype.card ι : ℝ) + 1) * R + 1 := by
      dsimp [T]
      ring

namespace GlobalLatticePresentation

/-
Strict trace Euclideanity therefore supplies `rank * degree` linearly independent points of the
Euclidean trace lattice with a completely explicit norm bound.  The auxiliary squared radius `u`
can be chosen arbitrarily close to `t` from above.
-/
theorem exists_short_linearIndependent_euclideanLattice_of_traceEuclidean
    (P : GlobalLatticePresentation) {t u : ℝ}
    (ht : 0 < t) (htu : t < u) (hE : P.IsTraceEuclidean t) :
    ∃ v : P.TraceDimensionIndex → P.euclideanIntegralLattice,
      LinearIndependent ℝ (fun i ↦ (v i : P.EuclideanTraceSpace)) ∧
        ∀ i, ‖(v i : P.EuclideanTraceSpace)‖ <
          ((P.rank * P.degree : ℕ) + 1 : ℝ) * Real.sqrt u + 1 := by
  have hcover : ∀ x : P.EuclideanTraceSpace,
      ∃ l : P.euclideanIntegralLattice,
        ‖x - (l : P.EuclideanTraceSpace)‖ < Real.sqrt u := by
    intro x
    obtain ⟨l, hl⟩ := P.euclidean_ball_cover_of_traceEuclidean ht htu hE x
    refine ⟨l, ?_⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, Metric.mem_ball] at hl
    simp only [dist_eq_norm, sub_zero] at hl
    change ‖-(l : P.EuclideanTraceSpace) + x‖ < Real.sqrt u at hl
    simpa [sub_eq_add_neg, add_comm] using hl
  obtain ⟨v, hvind, hvnorm⟩ :=
    exists_short_linearIndependent_of_cover P.euclideanIntegralLattice
      (Real.sqrt u) (Real.sqrt_nonneg u) hcover
  refine ⟨v, hvind, ?_⟩
  intro i
  simpa [P.traceSpace_finrank] using hvnorm i

end GlobalLatticePresentation

end

end TraceEuclidean
