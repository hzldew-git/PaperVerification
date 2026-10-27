import NormEuclidean.ChapterX.OrthogonalVolume

/-!
# The projected-complement volume bound in 103:4

The actual scalar sandwich and orthogonal volume formula prove
`alpha^(2n) volume(L) <= volume(K')`. Integral half-polar scale remains
explicit. No bound or volume identity is supplied as a premise.
-/

noncomputable section

namespace NormEuclidean.ProjectedVolume

open IntegralVolume ProjectedComplement
open scoped Pointwise nonZeroDivisors

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

/-- The projected module has integral scale because its actual image is inside the source. -/
theorem projected_scale_integral (L : Lattice (integerSubring K) Q) (y : V)
    (hy : y ∈ L.carrier) (hs : L.scaleIdeal ≤ 1) (hy0 : Q y ≠ 0) :
    (projectedLattice Q L y hy hs hy0).scaleIdeal ≤ 1 := by
  apply (IntegralDual.le_dual_iff_scale_integral _ _).mp
  intro x hx
  apply (IntegralDual.mem_dual _ _ _).mpr
  intro z hz
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hz
  have ha' := projection_mem_lattice Q L y hy hs a ha
  have hb' := projection_mem_lattice Q L y hy hs b hb
  have h := (IntegralDual.mem_dual Q L.carrier _).mp
    ((IntegralDual.le_dual_iff_scale_integral Q L).mpr hs ha') _ hb'
  exact h

/-- The exact split volume equals the represented scalar times projected volume. -/
theorem split_volume_eq (L : Lattice (integerSubring K) Q) (y : V)
    (hy0 : Q y ≠ 0) :
    volumeSubmodule (halfPolar Q) (Module.finrank K V) (splitCarrier Q L y) =
      Q y • volumeSubmodule (halfPolar (Q.comp (complement Q y).subtype))
        (Module.finrank K (complement Q y)) (projectedCarrier Q L y) := by
  letI := L.finiteDimensional
  rw [← complement_finrank Q y hy0]
  exact volumeSubmodule_orthogonal_line Q y _ rfl (projectedCarrier Q L y)

/-- Source volume after scalar multiplication lies in the projected volume.
This is O'Meara's `alpha^(2n) c` bound on the actual projected lattice. -/
theorem scaled_volume_submodule_le (L : Lattice (integerSubring K) Q) (y : V)
    (hy : y ∈ L.carrier) (hs : L.scaleIdeal ≤ 1) (hy0 : Q y ≠ 0) :
    Q y ^ (2 * Module.finrank K V) •
      volumeSubmodule (halfPolar Q) (Module.finrank K V) L.carrier ≤
        volumeSubmodule (halfPolar (Q.comp (complement Q y).subtype))
          (Module.finrank K (complement Q y)) (projectedCarrier Q L y) := by
  have hle : L.carrier.map
      ((LinearMap.lsmul K V (Q y)).restrictScalars (integerSubring K)) ≤
        splitCarrier Q L y := by
    rintro _ ⟨x, hx, rfl⟩
    exact value_smul_mem_splitCarrier Q L y hy hs x hx
  have hvol := volumeSubmodule_mono (halfPolar Q) (Module.finrank K V) hle
  rw [volumeSubmodule_map_scalar, split_volume_eq Q L y hy0] at hvol
  apply hvol.trans
  intro t ht
  obtain ⟨z, hz, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp ht
  simpa only [Subring.smul_def] using
    (volumeSubmodule (halfPolar (Q.comp (complement Q y).subtype))
      (Module.finrank K (complement Q y)) (projectedCarrier Q L y)).smul_mem
        (⟨Q y, L.integral y hy⟩ : integerSubring K) hz

/-- The intrinsic fractional volume ideals satisfy the actual projected bound. -/
theorem scaled_volumeIdeal_le_projected (L : Lattice (integerSubring K) Q) (y : V)
    (hy : y ∈ L.carrier) (hs : L.scaleIdeal ≤ 1) (hy0 : Q y ≠ 0) :
    FractionalIdeal.spanSingleton (integerSubring K)⁰
        (Q y ^ (2 * Module.finrank K V)) * L.volumeIdeal ≤
      (projectedLattice Q L y hy hs hy0).volumeIdeal := by
  apply FractionalIdeal.coe_le_coe.mp
  rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton,
    Submodule.span_singleton_mul]
  exact scaled_volume_submodule_le Q L y hy hs hy0

/-- Any given lower volume ideal is carried to the source's required lower
bound on the actual lower-rank projected complement. -/
theorem projected_volume_lower_bound (L : Lattice (integerSubring K) Q) (y : V)
    (hy : y ∈ L.carrier) (hs : L.scaleIdeal ≤ 1) (hy0 : Q y ≠ 0)
    (c : FractionalIdeal (integerSubring K)⁰ K) (hc : c ≤ L.volumeIdeal) :
    FractionalIdeal.spanSingleton (integerSubring K)⁰
        (Q y ^ (2 * Module.finrank K V)) * c ≤
      (projectedLattice Q L y hy hs hy0).volumeIdeal := by
  apply FractionalIdeal.coe_le_coe.mp
  rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton,
    Submodule.span_singleton_mul]
  have hc' : (c : Submodule (integerSubring K) K) ≤
      volumeSubmodule (halfPolar Q) (Module.finrank K V) L.carrier := hc
  exact (smul_mono_right (Q y ^ (2 * Module.finrank K V)) hc').trans
    (scaled_volume_submodule_le Q L y hy hs hy0)

end NormEuclidean.ProjectedVolume
