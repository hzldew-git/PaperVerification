import NormEuclidean.LatticeGaussian

/-!
# The actual zero term and exponential theta decay

Discreteness supplies a positive length gap. Separating the actual zero
vector then gives an exponential estimate for the remaining series.
The gap and all constants are allowed to depend on the lattice.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace NormEuclidean.LatticeThetaDecay

open Filter Topology LatticeGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]

/-- The actual Gaussian series over the nonzero vectors. -/
def tail (t : ℝ) : ℝ := ∑' x : {x : L // x ≠ 0}, Real.exp (-t * ‖(x.1 : E)‖ ^ 2)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A positive length gap follows from discreteness, including the zero lattice. -/
theorem exists_gap : ∃ ε : ℝ, 0 < ε ∧ ∀ x : L, x ≠ 0 → ε ≤ ‖(x : E)‖ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_discrete ({0} : Set L)) 0 (by simp)
  refine ⟨ε, hε, fun x hx ↦ le_of_not_gt fun h ↦ hx ?_⟩
  exact Set.mem_singleton_iff.mp (hball (by simpa [Metric.mem_ball] using h))

/-- Removing the zero vector preserves the proved summability. -/
theorem summable_tail (t : ℝ) (ht : 0 < t) :
    Summable (fun x : {x : L // x ≠ 0} ↦ Real.exp (-t * ‖(x.1 : E)‖ ^ 2)) :=
  (LatticeGaussian.summable L t ht).subtype _

/-- The full series is one plus its actual punctured series. -/
theorem theta_eq_one_add_tail (t : ℝ) (ht : 0 < t) :
    theta L t = 1 + tail L t := by
  classical
  have h := (LatticeGaussian.summable L t ht).sum_add_tsum_subtype_compl {0}
  have he := (Equiv.subtypeEquivRight (fun x : L ↦
    show x ∉ ({0} : Finset L) ↔ x ≠ 0 by simp)).tsum_eq
      (fun x : {x : L // x ≠ 0} ↦ Real.exp (-t * ‖(x.1 : E)‖ ^ 2))
  simp only [Equiv.subtypeEquivRight_apply] at he
  simpa only [theta, tail, he, Finset.sum_singleton, Submodule.coe_zero, norm_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, neg_zero,
    Real.exp_zero] using h.symm

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DiscreteTopology L] in
/-- All summands of the punctured series are nonnegative. -/
theorem tail_nonneg (t : ℝ) : 0 ≤ tail L t := tsum_nonneg fun _ ↦ (Real.exp_pos _).le

/-- In particular the actual theta function has its zero-term lower bound. -/
theorem one_le_theta (t : ℝ) (ht : 0 < t) : 1 ≤ theta L t := by
  rw [theta_eq_one_add_tail L t ht]
  exact le_add_of_nonneg_right (tail_nonneg L t)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Pointwise factoring uses a genuine lower bound for the nonzero vector length. -/
theorem term_le (ε a t : ℝ) (hε : 0 ≤ ε) (hat : a ≤ t)
    (x : E) (hx : ε ≤ ‖x‖) :
    Real.exp (-t * ‖x‖ ^ 2) ≤
      Real.exp (-(t - a) * ε ^ 2) * Real.exp (-a * ‖x‖ ^ 2) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have hh : ε ^ 2 ≤ ‖x‖ ^ 2 := (sq_le_sq₀ hε (norm_nonneg x)).mpr hx
  nlinarith [mul_nonneg (sub_nonneg.mpr hat) (sub_nonneg.mpr hh)]

/-- The punctured theta series decays exponentially with the actual lattice gap. -/
theorem tail_le (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ x : L, x ≠ 0 → ε ≤ ‖(x : E)‖)
    (a t : ℝ) (ha : 0 < a) (hat : a ≤ t) :
    tail L t ≤ Real.exp (-(t - a) * ε ^ 2) * tail L a := by
  have h := (summable_tail L t (ha.trans_le hat)).tsum_le_tsum
    (fun x : {x : L // x ≠ 0} ↦ term_le ε a t hε.le hat (x.1 : E) (hgap x.1 x.2))
    ((summable_tail L a ha).mul_left (Real.exp (-(t - a) * ε ^ 2)))
  simpa only [tsum_mul_left, tail] using h

/-- The actual punctured series tends to zero at large positive parameters. -/
theorem tendsto_tail : Tendsto (tail L) atTop (𝓝 0) := by
  obtain ⟨ε, hε, hgap⟩ := exists_gap L
  have hexp : Tendsto (fun t : ℝ ↦ Real.exp (-(t - 1) * ε ^ 2)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have ht : Tendsto (fun t : ℝ ↦ t - 1) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1) tendsto_id
    simpa only [Function.comp_def, neg_mul] using
      tendsto_neg_atTop_atBot.comp (ht.atTop_mul_const (sq_pos_of_pos hε))
  apply squeeze_zero' (Eventually.of_forall (tail_nonneg L))
    ((eventually_ge_atTop (1 : ℝ)).mono fun t ht ↦ tail_le L ε hε hgap 1 t zero_lt_one ht)
  simpa using hexp.mul_const (tail L 1)

/-- The actual theta function tends to one, with its zero vector accounted for. -/
theorem tendsto_theta : Tendsto (theta L) atTop (𝓝 1) := by
  have h := (tendsto_tail L).const_add 1
  apply (show Tendsto (fun t ↦ 1 + tail L t) atTop (𝓝 1) by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (theta_eq_one_add_tail L t ht).symm

end NormEuclidean.LatticeThetaDecay
