import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
Measure-theoretic covering bounds for full real lattices.  The proof avoids a
formal Voronoi construction: a fixed fundamental domain is covered by the
translates of the covering set, and the fundamental-domain decomposition says
that the sum of the intersection measures is exactly the measure of that set.
-/

namespace TraceEuclidean

open MeasureTheory Set Module Filter Topology
open scoped Pointwise

noncomputable section

/-- The Euclidean unit-ball volume `U_m = π^(m/2) / Γ(m/2+1)`. -/
def euclideanUnitBallVolume (m : ℕ) : ℝ :=
  Real.pi ^ ((m : ℝ) / 2) / Real.Gamma ((m : ℝ) / 2 + 1)

/-- Every Euclidean unit ball has positive volume. -/
theorem euclideanUnitBallVolume_pos (m : ℕ) :
    0 < euclideanUnitBallVolume m := by
  unfold euclideanUnitBallVolume
  exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    (Real.Gamma_pos_of_pos (by positivity))

/-- Mathlib's square-root formula for the unit ball equals `U_m`. -/
theorem sqrtPiPow_div_gamma_eq_euclideanUnitBallVolume (m : ℕ) :
    Real.sqrt Real.pi ^ m /
        Real.Gamma ((m : ℝ) / 2 + 1) =
      euclideanUnitBallVolume m := by
  unfold euclideanUnitBallVolume
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast]
  rw [← Real.rpow_mul (le_of_lt Real.pi_pos)]
  congr 1
  ring

/--
If all lattice translates of a finite-measure set cover the ambient real
vector space, then the lattice covolume is at most the measure of the set.
-/
theorem covolume_le_measureReal_of_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (s : Set E) (hsTop : μ s ≠ ⊤)
    (hcover : ∀ x : E, ∃ l : L, x ∈ l +ᵥ s) :
    ZLattice.covolume L μ ≤ μ.real s := by
  let b : Basis (Free.ChooseBasisIndex ℤ L) ℝ E :=
    (Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  let F : Set E := ZSpan.fundamentalDomain b
  have hb : Submodule.span ℤ (Set.range b) = L := by
    simpa only [b] using (Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ L
  have hfund : IsAddFundamentalDomain L F μ :=
    hb ▸ ZSpan.isAddFundamentalDomain b μ
  have : MeasurableVAdd L E :=
    (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E μ :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup E μ)
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L μ hfund]
  apply ENNReal.toReal_mono hsTop
  calc
    μ F ≤ μ (⋃ l : L, (l +ᵥ s) ∩ F) := by
      apply measure_mono
      intro x hx
      obtain ⟨l, hl⟩ := hcover x
      exact mem_iUnion.2 ⟨l, hl, hx⟩
    _ ≤ ∑' l : L, μ ((l +ᵥ s) ∩ F) := measure_iUnion_le _
    _ = μ s := (hfund.measure_eq_tsum s).symm

/--
The covering bound specialized to a Euclidean ball, with mathlib's exact
Gamma-function formula for its volume.
-/
theorem covolume_le_ball_formula_of_cover
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (r : ℝ) (hr : 0 < r)
    (hcover : ∀ x : E, ∃ l : L,
      x ∈ l +ᵥ Metric.ball (0 : E) r) :
    ZLattice.covolume L ≤
      euclideanUnitBallVolume (Module.finrank ℝ E) *
        r ^ Module.finrank ℝ E := by
  have h := covolume_le_measureReal_of_cover L volume
    (Metric.ball (0 : E) r) measure_ball_lt_top.ne hcover
  rw [Measure.real, InnerProductSpace.volume_ball] at h
  have hunit :
      0 ≤ Real.sqrt Real.pi ^ Module.finrank ℝ E /
        Real.Gamma ((Module.finrank ℝ E : ℝ) / 2 + 1) := by
    positivity
  rw [sqrtPiPow_div_gamma_eq_euclideanUnitBallVolume] at h
  have hU : 0 ≤ euclideanUnitBallVolume (Module.finrank ℝ E) :=
    (euclideanUnitBallVolume_pos _).le
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hunit,
    ENNReal.toReal_ofReal hU, hr.le, mul_comm] using h

/--
Combine the covering-volume inequality with a Gram/covolume identity.  This is
the abstract form of the calculation shared by the classic and scale-two
branches of the manuscript.
-/
theorem gramVolume_le_of_ball_cover
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (D V r : ℝ) (n d : ℕ) (hr : 0 < r)
    (hdim : Module.finrank ℝ E = n * d)
    (hGram : D ^ n * V = ZLattice.covolume L ^ (2 : ℕ))
    (hcover : ∀ x : E, ∃ l : L,
      x ∈ l +ᵥ Metric.ball (0 : E) r) :
    D ^ n * V ≤
      euclideanUnitBallVolume (n * d) ^ (2 : ℕ) *
        (r ^ (2 : ℕ)) ^ (n * d) := by
  have hcov := covolume_le_ball_formula_of_cover L r hr hcover
  rw [hdim] at hcov
  have hrpow :
      (r ^ (n * d)) ^ (2 : ℕ) = (r ^ (2 : ℕ)) ^ (n * d) := by
    calc
      (r ^ (n * d)) ^ (2 : ℕ) = r ^ ((n * d) * 2) :=
        (pow_mul r (n * d) 2).symm
      _ = r ^ (2 * (n * d)) := by rw [Nat.mul_comm]
      _ = (r ^ (2 : ℕ)) ^ (n * d) := pow_mul r 2 (n * d)
  calc
    D ^ n * V = ZLattice.covolume L ^ (2 : ℕ) := hGram
    _ ≤ (euclideanUnitBallVolume (n * d) * r ^ (n * d)) ^
          (2 : ℕ) :=
      pow_le_pow_left₀ (ZLattice.covolume_pos L volume).le hcov 2
    _ = euclideanUnitBallVolume (n * d) ^ (2 : ℕ) *
          (r ^ (2 : ℕ)) ^ (n * d) := by
      rw [mul_pow, hrpow]

/-- The Gram/covolume consequence for a squared covering radius `t`. -/
theorem gramVolume_le_of_sqrt_cover
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (D V t : ℝ) (n d : ℕ) (ht : 0 < t)
    (hdim : Module.finrank ℝ E = n * d)
    (hGram : D ^ n * V = ZLattice.covolume L ^ (2 : ℕ))
    (hcover : ∀ x : E, ∃ l : L,
      x ∈ l +ᵥ Metric.ball (0 : E) (Real.sqrt t)) :
    D ^ n * V ≤
      euclideanUnitBallVolume (n * d) ^ (2 : ℕ) * t ^ (n * d) := by
  simpa [Real.sq_sqrt ht.le] using
    gramVolume_le_of_ball_cover L D V (Real.sqrt t) n d
      (Real.sqrt_pos.2 ht) hdim hGram hcover

/--
If every squared radius strictly larger than `t` gives a lattice covering,
then passage to the limit gives the sharp squared covolume bound at `t`.
This is the form needed when a strict Euclidean condition is extended from a
dense rational subspace to the complete real space.
-/
theorem covolume_sq_le_of_sqrt_cover_above
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (t : ℝ) (ht : 0 < t)
    (hcover : ∀ u : ℝ, t < u → ∀ x : E, ∃ l : L,
      x ∈ l +ᵥ Metric.ball (0 : E) (Real.sqrt u)) :
    ZLattice.covolume L ^ (2 : ℕ) ≤
      euclideanUnitBallVolume (Module.finrank ℝ E) ^ (2 : ℕ) *
        t ^ Module.finrank ℝ E := by
  let u : ℕ → ℝ := fun k ↦ t + 1 / ((k : ℝ) + 1)
  have htu (k : ℕ) : t < u k := by
    dsimp [u]
    have hk : 0 < (k : ℝ) + 1 := by positivity
    exact lt_add_of_pos_right _ (one_div_pos.mpr hk)
  have hu (k : ℕ) : 0 < u k := ht.trans (htu k)
  have hbound (k : ℕ) :
      ZLattice.covolume L ^ (2 : ℕ) ≤
        euclideanUnitBallVolume (Module.finrank ℝ E) ^ (2 : ℕ) *
          (u k) ^ Module.finrank ℝ E := by
    have h := gramVolume_le_of_sqrt_cover L
      (1 : ℝ) (ZLattice.covolume L ^ (2 : ℕ)) (u k)
      (Module.finrank ℝ E) 1 (hu k) (by simp) (by simp)
      (hcover (u k) (htu k))
    simpa using h
  have hu_tend : Tendsto u atTop (𝓝 t) := by
    dsimp [u]
    simpa only [add_zero] using
      (tendsto_const_nhds (x := t)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim :
      Tendsto
        (fun k ↦
          euclideanUnitBallVolume (Module.finrank ℝ E) ^ (2 : ℕ) *
            (u k) ^ Module.finrank ℝ E)
        atTop
        (𝓝 (euclideanUnitBallVolume (Module.finrank ℝ E) ^ (2 : ℕ) *
          t ^ Module.finrank ℝ E)) :=
    tendsto_const_nhds.mul (hu_tend.pow _)
  exact ge_of_tendsto' hlim hbound

end

end TraceEuclidean
