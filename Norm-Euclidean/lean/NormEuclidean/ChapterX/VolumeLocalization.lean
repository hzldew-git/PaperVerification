import NormEuclidean.ChapterX.MixedVolume
import NormEuclidean.ChapterX.LocalIntegralUniversality
import NormEuclidean.CompletionDescent

/-!
# Volume at the actual finite completions

Two multilinear span inductions identify the mixed determinant volume of the
completed carrier with the completed scalar span of the global volume. Actual
completed integral isometries therefore recover equality of global volumes.
Neither finite generation nor an integral basis is needed for this equality.
-/

noncomputable section

namespace NormEuclidean.VolumeLocalization

open IntegralVolume CompletedIntegralLattice IsDedekindDomain
open scoped TensorProduct

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]

/-- The actual completed scalar span of a global coefficient module. -/
def scalarSpan (v : HeightOneSpectrum R) (I : Submodule R K) :
    Submodule (LocalRing R v) (LocalField R v) :=
  Submodule.span (LocalRing R v) (algebraMap K (LocalField R v) '' (I : Set K))

/-- Tensor scalar extension of the coefficient field is its completion itself. -/
def scalarEquiv (v : HeightOneSpectrum R) :
    Space (V := K) R v ≃ₗ[LocalField R v] LocalField R v :=
  TensorProduct.AlgebraTensorModule.rid K (LocalField R v) (LocalField R v)

@[simp]
theorem scalarEquiv_inclusion (v : HeightOneSpectrum R) (x : K) :
    scalarEquiv R v (inclusion R v x) = algebraMap K (LocalField R v) x := by
  simp only [scalarEquiv, inclusion, TensorProduct.mk_apply,
    TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one]

/-- The completed coefficient carrier is identified with its scalar span. -/
theorem map_coefficient_carrier (v : HeightOneSpectrum R) (I : Submodule R K) :
    (carrier R v I).map ((scalarEquiv R v).toLinearMap.restrictScalars (LocalRing R v)) =
      scalarSpan R v I := by
  rw [carrier, Submodule.map_span, Set.image_image]
  simp only [scalarSpan, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe, scalarEquiv_inclusion]

/-- Equality of scalar spans at every finite completion determines the coefficient module. -/
theorem eq_of_scalarSpans_eq (hR : ¬ IsField R) {I J : Submodule R K}
    (h : ∀ v : HeightOneSpectrum R, scalarSpan R v I = scalarSpan R v J) : I = J := by
  apply CompletionDescent.submodule_eq_of_completed_carriers_eq R hR
  intro v
  apply Submodule.map_injective_of_injective
    (f := (scalarEquiv R v).toLinearMap.restrictScalars (LocalRing R v))
    (scalarEquiv R v).injective
  rw [map_coefficient_carrier, map_coefficient_carrier, h v]

/-- Completed scalar spans commute with spans of arbitrary global generators. -/
theorem scalarSpan_span (v : HeightOneSpectrum R) (S : Set K) :
    scalarSpan R v (Submodule.span R S) =
      Submodule.span (LocalRing R v) (algebraMap K (LocalField R v) '' S) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨t, ht, rfl⟩
    induction ht using Submodule.span_induction with
    | mem t ht => exact Submodule.subset_span ⟨t, ht, rfl⟩
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      rw [map_add]
      exact Submodule.add_mem _ ha hb
    | smul a t _ ht =>
      let av : LocalRing R v := ⟨algebraMap K (LocalField R v) (a : K),
        algebraMap_mem R v a.property⟩
      change algebraMap K (LocalField R v) ((a : K) * t) ∈ _
      rw [map_mul]
      exact Submodule.smul_mem _ av ht
  · apply Submodule.span_mono
    exact Set.image_mono Submodule.subset_span

/-- The scalar completion of a principal coefficient span is the actual local principal span. -/
theorem scalarSpan_span_singleton (v : HeightOneSpectrum R) (a : K) :
    scalarSpan R v (Submodule.span R {a}) =
      Submodule.span (LocalRing R v) {algebraMap K (LocalField R v) a} := by
  rw [scalarSpan_span, Set.image_singleton]

variable [Invertible (2 : K)]

/-- The literal half-polar pairing commutes with the actual field inclusion. -/
theorem halfPolar_inclusion (v : HeightOneSpectrum R) (Q : QuadraticForm K V) (x y : V) :
    halfPolar (form R v Q) (inclusion R v x) (inclusion R v y) =
      algebraMap K (LocalField R v) (halfPolar Q x y) := by
  change (2 : LocalField R v)⁻¹ * (form R v Q).polarBilin
    (inclusion R v x) (inclusion R v y) =
      algebraMap K (LocalField R v) ((2 : K)⁻¹ * Q.polarBilin x y)
  rw [LocalIntegralUniversality.polar_inclusion, map_mul, map_inv₀, map_ofNat]

/-- Mapping the actual mixed matrix maps its determinant. -/
theorem det_inclusion (v : HeightOneSpectrum R) (Q : QuadraticForm K V) (n : ℕ)
    (x y : Fin n → V) :
    (pairingMatrix (halfPolar (form R v Q))
      (fun i ↦ inclusion R v (x i)) (fun j ↦ inclusion R v (y j))).det =
      algebraMap K (LocalField R v) (pairingMatrix (halfPolar Q) x y).det := by
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  exact halfPolar_inclusion R v Q (x i) (y j)

/-- Completed volume is the actual scalar extension of global mixed volume.
This includes degree zero and dyadic places and needs no free integral basis. -/
theorem completed_volume (v : HeightOneSpectrum R) (Q : QuadraticForm K V) (n : ℕ)
    (L : Submodule R V) :
    MixedVolume.submodule (LocalRing R v) (halfPolar (form R v Q)) n (carrier R v L) =
      scalarSpan R v (MixedVolume.submodule R (halfPolar Q) n L) := by
  apply le_antisymm
  · apply MixedVolume.le_of_generators
    intro x y hx hy
    choose a ha hxa using hx
    choose b hb hyb using hy
    have hx' : x = fun i ↦ inclusion R v (a i) := funext fun i ↦ (hxa i).symm
    have hy' : y = fun j ↦ inclusion R v (b j) := funext fun j ↦ (hyb j).symm
    rw [hx', hy', det_inclusion]
    exact Submodule.subset_span
      ⟨_, MixedVolume.det_mem R (halfPolar Q) n L a b ha hb, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨t, ht, rfl⟩
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨p, rfl⟩ := ht
      rw [← det_inclusion]
      exact MixedVolume.det_mem (LocalRing R v) _ n _ _ _
        (fun i ↦ inclusion_mem R v L (p.1 i).2)
        (fun j ↦ inclusion_mem R v L (p.2 j).2)
    | zero =>
      change algebraMap K (LocalField R v) 0 ∈
        MixedVolume.submodule (LocalRing R v) (halfPolar (form R v Q)) n (carrier R v L)
      rw [map_zero]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      rw [map_add]
      exact Submodule.add_mem _ ha hb
    | smul a t _ ht =>
      let av : LocalRing R v := ⟨algebraMap K (LocalField R v) (a : K),
        algebraMap_mem R v a.property⟩
      have h := Submodule.smul_mem
        (MixedVolume.submodule (LocalRing R v) (halfPolar (form R v Q)) n
          (carrier R v L)) av ht
      change algebraMap K (LocalField R v) ((a : K) * t) ∈
        MixedVolume.submodule (LocalRing R v) (halfPolar (form R v Q)) n (carrier R v L)
      rw [map_mul]
      exact h

/-- Actual completed integral isometry preserves mixed volume in any degree. -/
theorem scalarSpan_eq_of_local_isometry (v : HeightOneSpectrum R)
    (Q : QuadraticForm K V) (Q' : QuadraticForm K W) (n : ℕ)
    (L : Submodule R V) (M : Submodule R W)
    (e : LatticeIsometry (form R v Q) (form R v Q') (carrier R v L) (carrier R v M)) :
    scalarSpan R v (MixedVolume.submodule R (halfPolar Q) n L) =
      scalarSpan R v (MixedVolume.submodule R (halfPolar Q') n M) := by
  have hmap : (carrier R v L).map
      (e.toLinearEquiv.toLinearMap.restrictScalars (LocalRing R v)) = carrier R v M := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (e.mem_iff x).mpr hx
    · intro hz
      refine ⟨e.toLinearEquiv.symm z, ?_, e.toLinearEquiv.apply_symm_apply z⟩
      apply (e.mem_iff _).mp
      rw [e.toLinearEquiv.apply_symm_apply]
      exact hz
  have hB (x y : Space (V := V) R v) :
      halfPolar (form R v Q') (e.toLinearEquiv x) (e.toLinearEquiv y) =
        halfPolar (form R v Q) x y := by
    simp only [halfPolar_apply, QuadraticMap.polar]
    rw [← e.toLinearEquiv.map_add, e.q_eq, e.q_eq, e.q_eq]
  rw [← completed_volume, ← completed_volume, ← hmap]
  exact (MixedVolume.map_isometry (LocalRing R v) _ _ n _ _ hB).symm

/-- All actual finite-place integral isometries recover equality of global mixed volumes. -/
theorem mixed_volume_eq_of_finiteLocallyIsometric (hR : ¬ IsField R)
    (Q : QuadraticForm K V) (Q' : QuadraticForm K W) (n : ℕ)
    (L : Submodule R V) (M : Submodule R W) (h : FiniteLocallyIsometric R Q Q' L M) :
    MixedVolume.submodule R (halfPolar Q) n L =
      MixedVolume.submodule R (halfPolar Q') n M := by
  apply eq_of_scalarSpans_eq R hR
  intro v
  obtain ⟨e⟩ := h v
  exact scalarSpan_eq_of_local_isometry R v Q Q' n L M e

end NormEuclidean.VolumeLocalization

namespace NormEuclidean.Lattice

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

/-- The actual volume ideal is constant on the ordinary genus, as on p. 299. -/
theorem volumeIdeal_eq_of_sameGenus (L M : Lattice (integerSubring K) Q)
    (h : SameGenus Q L M) : L.volumeIdeal = M.volumeIdeal := by
  apply FractionalIdeal.coeToSubmodule_injective
  change IntegralVolume.volumeSubmodule (halfPolar Q) (Module.finrank K V) L.carrier =
    IntegralVolume.volumeSubmodule (halfPolar Q) (Module.finrank K V) M.carrier
  exact VolumeLocalization.mixed_volume_eq_of_finiteLocallyIsometric (integerSubring K)
    (NumberField.RingOfIntegers.not_isField K) Q Q (Module.finrank K V)
    L.carrier M.carrier h.1

omit [Invertible (2 : K)] in
/-- Degree-one mixed volume is precisely the actual half-polar scale span. -/
theorem scaleSubmodule_eq_volume_degree_one (L : Lattice (integerSubring K) Q) :
    L.scaleSubmodule = MixedVolume.submodule (integerSubring K) (halfPolar Q) 1 L.carrier := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    have h := MixedVolume.det_mem (integerSubring K) (halfPolar Q) 1 L.carrier
      (fun _ ↦ (p.1 : V)) (fun _ ↦ (p.2 : V)) (fun _ ↦ p.1.2) (fun _ ↦ p.2.2)
    change halfPolar Q p.1 p.2 ∈
      MixedVolume.submodule (integerSubring K) (halfPolar Q) 1 L.carrier
    rw [Matrix.det_fin_one] at h
    exact h
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    dsimp only
    rw [Matrix.det_fin_one]
    exact L.halfPolar_mem_scaleIdeal (p.1 0) (p.2 0)

/-- Actual scale ideals, including their integrality, are constant on a genus. -/
theorem scaleIdeal_eq_of_sameGenus (L M : Lattice (integerSubring K) Q)
    (h : SameGenus Q L M) : L.scaleIdeal = M.scaleIdeal := by
  apply FractionalIdeal.coeToSubmodule_injective
  change L.scaleSubmodule = M.scaleSubmodule
  rw [scaleSubmodule_eq_volume_degree_one, scaleSubmodule_eq_volume_degree_one]
  exact VolumeLocalization.mixed_volume_eq_of_finiteLocallyIsometric (integerSubring K)
    (NumberField.RingOfIntegers.not_isField K) Q Q 1 L.carrier M.carrier h.1

end NormEuclidean.Lattice
