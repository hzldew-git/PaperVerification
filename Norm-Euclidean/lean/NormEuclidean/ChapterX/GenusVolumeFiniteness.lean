import NormEuclidean.ChapterX.VolumeLocalization
import NormEuclidean.ChapterX.ClassFinitenessInduction
import NormEuclidean.GenusRescaling
import NormEuclidean.ChapterX.ProperClassFiniteness

/-!
# From bounded-volume class representatives to finite genus classes

The actual genus-volume and scale equalities supply the inclusion in the
bounded-volume family. The remaining arithmetic coverage of 103:3 is explicit;
it is not replaced by an axiom or asserted as already proved.
-/

noncomputable section

namespace NormEuclidean.GenusVolumeFiniteness

open ClassFinitenessInduction
open scoped nonZeroDivisors

universe u v

variable {K : Type v} {V : Type u} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V]

/-- Finite representatives of the actual bounded-volume family give finite
ordinary genus classes. Genus volume and scale agreement are proved internally. -/
theorem finite_genus_classes_of_volume_representatives (Q : QuadraticForm K V)
    (L : Lattice (integerSubring K) Q) (hs : L.scaleIdeal ≤ 1)
    (hclasses : HasFiniteVolumeClassRepresentatives Q L.volumeIdeal) :
    Finite (GenusClassSet Q L) := by
  classical
  obtain ⟨A, hA, hcover⟩ := hclasses
  letI : Finite A := hA.to_subtype
  let f : A → GenusClassSet Q L := fun N ↦
    if h : SameGenus Q L N.1 then Quotient.mk (genusClassSetoid Q L) ⟨N.1, h⟩
    else Quotient.mk (genusClassSetoid Q L) (selfGenusMember Q L)
  apply Finite.of_surjective f
  intro k
  have hvol : L.volumeIdeal ≤ k.out.1.volumeIdeal :=
    le_of_eq (L.volumeIdeal_eq_of_sameGenus k.out.1 k.out.2)
  have hscale : k.out.1.scaleIdeal ≤ 1 := by
    rw [← L.scaleIdeal_eq_of_sameGenus k.out.1 k.out.2]
    exact hs
  obtain ⟨N, hNA, hMN⟩ := hcover k.out.1 hscale hvol
  have hLN : SameGenus Q L N := by
    obtain ⟨e⟩ := hMN
    exact allPlaceLocallyIsometric_trans k.out.2 (allPlaceLocallyIsometric_of_isometry e)
  refine ⟨⟨N, hNA⟩, ?_⟩
  change (if h : SameGenus Q L N then _ else _) = k
  rw [dif_pos hLN]
  have heq : Quotient.mk (genusClassSetoid Q L)
      (⟨N, hLN⟩ : GenusMember Q L) = Quotient.mk (genusClassSetoid Q L) k.out :=
    Quotient.sound (GloballyIsometric.symm Q hMN)
  exact heq.trans (Quotient.out_eq k)

/-- A regular integral-scale rank-one genus is unconditionally finite. -/
theorem finite_genus_classes_rank_one (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (L : Lattice (integerSubring K) Q)
    (hs : L.scaleIdeal ≤ 1) (hdim : Module.finrank K V = 1) :
    Finite (GenusClassSet Q L) := by
  letI := L.finiteDimensional
  apply finite_genus_classes_of_volume_representatives Q L hs
  exact finite_volume_classes_rank_one Q hQ hdim L.volumeIdeal (L.volumeIdeal_ne_zero hQ)

/-- The completed geometric chain of 103:4 produces finite ordinary genus
classes once the high-rank arithmetic statement of 103:3 is available. -/
theorem finite_genus_classes_of_bounded_value_coverage
    (hvalues : ∀ (W : Type u) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
      (Q : QuadraticForm K W), Q.polarBilin.Nondegenerate → 2 ≤ Module.finrank K W →
        ∀ c : FractionalIdeal (integerSubring K)⁰ K, c ≠ 0 → BoundedValueCoverage Q c)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice (integerSubring K) Q) (hs : L.scaleIdeal ≤ 1) :
    Finite (GenusClassSet Q L) := by
  letI := L.finiteDimensional
  apply finite_genus_classes_of_volume_representatives Q L hs
  exact finite_volume_classes_of_bounded_value_coverage hvalues V Q hQ
    L.volumeIdeal (L.volumeIdeal_ne_zero hQ)

omit [NumberField K] [Invertible (2 : K)] in
/-- Nonzero scalar rescaling preserves regularity of the actual polar pairing. -/
theorem polarBilin_smul_nondegenerate (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (a : K) (ha : a ≠ 0) :
    (a • Q).polarBilin.Nondegenerate := by
  have hscale (x y : V) : (a • Q).polarBilin x y = a * Q.polarBilin x y := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      QuadraticMap.smul_apply, smul_eq_mul]
    ring
  constructor
  · intro x hx
    apply hQ.1 x
    intro y
    have h := hx y
    rw [hscale] at h
    exact (mul_eq_zero.mp h).resolve_left ha
  · intro y hy
    apply hQ.2 y
    intro x
    have h := hy x
    rw [hscale] at h
    exact (mul_eq_zero.mp h).resolve_left ha

/-- Doubling and the proved full genus-class bijection remove an integral-scale
restriction on the base lattice. The only remaining arithmetic input is 103:3. -/
theorem finite_integral_genus_classes_of_bounded_value_coverage
    (hvalues : ∀ (W : Type u) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
      (Q : QuadraticForm K W), Q.polarBilin.Nondegenerate → 2 ≤ Module.finrank K W →
        ∀ c : FractionalIdeal (integerSubring K)⁰ K, c ≠ 0 → BoundedValueCoverage Q c)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice (integerSubring K) Q) : Finite (GenusClassSet Q L) := by
  apply (finite_genusClassSet_rescale_iff L 2 (by norm_num)).mp
  exact finite_genus_classes_of_bounded_value_coverage hvalues ((2 : K) • Q)
    (polarBilin_smul_nondegenerate Q hQ 2 (by norm_num)) (L.rescale 2)
    L.doubled_scaleIdeal_le_one

/-- The same explicit 103:3 input gives finite proper genus classes by the
proved two-sign fibers. No separate proper-class finiteness premise is supplied. -/
theorem finite_integral_proper_genus_classes_of_bounded_value_coverage
    (hvalues : ∀ (W : Type u) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
      (Q : QuadraticForm K W), Q.polarBilin.Nondegenerate → 2 ≤ Module.finrank K W →
        ∀ c : FractionalIdeal (integerSubring K)⁰ K, c ≠ 0 → BoundedValueCoverage Q c)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice (integerSubring K) Q) : Finite (ProperGenusClassSet Q L) := by
  letI := L.finiteDimensional
  exact ProperClassFiniteness.finite_proper_classes_of_finite_classes Q hQ L
    (finite_integral_genus_classes_of_bounded_value_coverage hvalues Q hQ L)

/-- The class-finiteness premise of the 104:1 endpoint follows from the exact
remaining 103:3 input. This theorem retains that unproved arithmetic premise. -/
theorem exists_divided_value_multiplier_of_bounded_value_coverage
    (hvalues : ∀ (W : Type u) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
      (Q : QuadraticForm K W), Q.polarBilin.Nondegenerate → 2 ≤ Module.finrank K W →
        ∀ c : FractionalIdeal (integerSubring K)⁰ K, c ≠ 0 → BoundedValueCoverage Q c)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice (integerSubring K) Q) (hs : L.scaleIdeal ≤ 1)
    (hdim : 3 ≤ Module.finrank K V)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (integerSubring K))) :
    ∃ γ : integerSubring K, γ ≠ 0 ∧
      (∀ v ∈ T, IsUnit (⟨algebraMap K (CompletedIntegralLattice.LocalField
        (integerSubring K) v) (γ : K),
        CompletedIntegralLattice.algebraMap_mem (integerSubring K) v γ.property⟩ :
          CompletedIntegralLattice.LocalRing (integerSubring K) v)) ∧
      ∀ a : K, (∃ b : integerSubring K, a = (γ : K) * (b : K)) →
        (∃ x : V, Q x = a) →
        (∀ v : IsDedekindDomain.HeightOneSpectrum (integerSubring K),
          ∃ z ∈ CompletedIntegralLattice.carrier (integerSubring K) v L.carrier,
            CompletedIntegralLattice.form (integerSubring K) v Q z =
              algebraMap K (CompletedIntegralLattice.LocalField (integerSubring K) v) a) →
        ∃ x ∈ L.carrier, Q x = a := by
  exact LocalIntegralUniversality.exists_divided_value_multiplier_of_finite_classes Q hQ L
    hdim (finite_genus_classes_of_bounded_value_coverage hvalues Q hQ L hs) T

/-- The exact norm-integral 104:1 conclusion follows from the remaining high-rank
103:3 input, without a supplied class-finiteness or integral-scale premise. -/
theorem exists_integral_divided_value_multiplier_of_bounded_value_coverage
    (hvalues : ∀ (W : Type u) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
      (Q : QuadraticForm K W), Q.polarBilin.Nondegenerate → 2 ≤ Module.finrank K W →
        ∀ c : FractionalIdeal (integerSubring K)⁰ K, c ≠ 0 → BoundedValueCoverage Q c)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (L : Lattice (integerSubring K) Q) (hdim : 3 ≤ Module.finrank K V)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (integerSubring K))) :
    ∃ γ : integerSubring K, γ ≠ 0 ∧
      (∀ v ∈ T, IsUnit (⟨algebraMap K (CompletedIntegralLattice.LocalField
        (integerSubring K) v) (γ : K),
        CompletedIntegralLattice.algebraMap_mem (integerSubring K) v γ.property⟩ :
          CompletedIntegralLattice.LocalRing (integerSubring K) v)) ∧
      ∀ a : K, (∃ b : integerSubring K, a = (γ : K) * (b : K)) →
        (∃ x : V, Q x = a) →
        (∀ v : IsDedekindDomain.HeightOneSpectrum (integerSubring K),
          ∃ z ∈ CompletedIntegralLattice.carrier (integerSubring K) v L.carrier,
            CompletedIntegralLattice.form (integerSubring K) v Q z =
              algebraMap K (CompletedIntegralLattice.LocalField (integerSubring K) v) a) →
        ∃ x ∈ L.carrier, Q x = a := by
  exact LocalIntegralUniversality.exists_divided_value_multiplier_of_finite_classes Q hQ L
    hdim (finite_integral_genus_classes_of_bounded_value_coverage hvalues Q hQ L) T

end NormEuclidean.GenusVolumeFiniteness
