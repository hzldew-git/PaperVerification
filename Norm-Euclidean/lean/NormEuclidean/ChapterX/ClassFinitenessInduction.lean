import NormEuclidean.ChapterX.ProjectedVolume
import NormEuclidean.ChapterX.RankOneVolumeFiniteness
import NormEuclidean.ChapterX.ClassFinitenessFiber
import NormEuclidean.ChapterX.FixedValueTransitivity

/-!
# The geometric induction step of 103:4

Actual projected-volume bounds and finite class fibers assemble finite
ordinary class representatives from finite represented-value coverage and
lower-rank class coverage. These two dependencies remain explicit here;
this module does not assert the full 103:3 theorem or unconditional 103:4.
-/

noncomputable section

namespace NormEuclidean.ClassFinitenessInduction

open ProjectedComplement ProjectedVolume ProperSpinor AdelicApproximation
open scoped nonZeroDivisors

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Actual ordinary class coverage of the integral-scale bounded-volume family. -/
def HasFiniteVolumeClassRepresentatives (Q : QuadraticForm K V)
    (c : FractionalIdeal (integerSubring K)⁰ K) : Prop :=
  ∃ A : Set (Lattice (integerSubring K) Q), A.Finite ∧
    ∀ L : Lattice (integerSubring K) Q, L.scaleIdeal ≤ 1 → c ≤ L.volumeIdeal →
      ∃ N ∈ A, GloballyIsometric Q L N

/-- The finite nonzero represented-value coverage required from 103:3.
This is a transparent statement of the remaining arithmetic dependency. -/
def BoundedValueCoverage (Q : QuadraticForm K V)
    (c : FractionalIdeal (integerSubring K)⁰ K) : Prop :=
  ∃ Φ : Set K, Φ.Finite ∧ 0 ∉ Φ ∧
    ∀ L : Lattice (integerSubring K) Q, L.scaleIdeal ≤ 1 → c ≤ L.volumeIdeal →
      ∃ x ∈ L.carrier, Q x ∈ Φ

/-- The rank-one base supplies actual finite ordinary class representatives. -/
theorem finite_volume_classes_rank_one (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 1)
    (c : FractionalIdeal (integerSubring K)⁰ K) (hc : c ≠ 0) :
    HasFiniteVolumeClassRepresentatives Q c := by
  refine ⟨{L : Lattice (integerSubring K) Q | c ≤ L.volumeIdeal},
    RankOneVolumeFiniteness.finite_rank_one_lattices Q hQ hdim c hc, ?_⟩
  intro L _ hL
  exact ⟨L, hL, GloballyIsometric.refl Q L⟩

/-- In rank one, finite represented-value coverage itself is unconditional. -/
theorem bounded_value_coverage_rank_one (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K V = 1)
    (c : FractionalIdeal (integerSubring K)⁰ K) (hc : c ≠ 0) :
    BoundedValueCoverage Q c := by
  classical
  let E : Set (Lattice (integerSubring K) Q) := {L | c ≤ L.volumeIdeal}
  have hE : E.Finite := RankOneVolumeFiniteness.finite_rank_one_lattices Q hQ hdim c hc
  letI : Fintype E := hE.fintype
  choose x hx hQx using fun L : E ↦
    RankOneVolumeFiniteness.exists_nonzero_integral_value Q hQ (by omega) L.1
  refine ⟨Set.range (fun L : E ↦ Q (x L)), Set.finite_range _, ?_, ?_⟩
  · rintro ⟨L, hL⟩
    exact hQx L hL
  · intro L _ hL
    let L' : E := ⟨L, hL⟩
    exact ⟨x L', hx L', Set.mem_range_self L'⟩

/-- The zero-rank class base is also finite; the value-coverage statement
is intentionally not asserted for this boundary case. -/
theorem finite_volume_classes_rank_zero (Q : QuadraticForm K V)
    (hdim : Module.finrank K V = 0) (c : FractionalIdeal (integerSubring K)⁰ K) :
    HasFiniteVolumeClassRepresentatives Q c := by
  letI : Subsingleton V := (Module.finrank_zero_iff).mp hdim
  have heq (L M : Lattice (integerSubring K) Q) : L = M := by
    have h : L.carrier = M.carrier := Subsingleton.elim _ _
    cases L
    cases M
    cases h
    rfl
  letI : Subsingleton (Lattice (integerSubring K) Q) := ⟨heq⟩
  refine ⟨Set.univ, Set.toFinite _, ?_⟩
  intro L _ _
  exact ⟨L, Set.mem_univ _, GloballyIsometric.refl Q L⟩

/-- Integral scale is preserved by actual orthogonal transport. -/
theorem scale_integral_transport (Q : QuadraticForm K V) (g : ambientGroup Q)
    (L : Lattice (integerSubring K) Q) (hs : L.scaleIdeal ≤ 1) :
    (transportLattice Q g L).scaleIdeal ≤ 1 := by
  apply (IntegralDual.le_dual_iff_scale_integral _ _).mp
  intro x hx
  apply (IntegralDual.mem_dual _ _ _).mpr
  intro y hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have hB : halfPolar Q (g.1 a) (g.1 b) = halfPolar Q a b := by
    simp only [halfPolar_apply, QuadraticMap.polar]
    rw [← g.1.map_add, g.2, g.2, g.2]
  change halfPolar Q (g.1 a) (g.1 b) ∈ integerSubring K
  rw [hB]
  exact (IntegralDual.mem_dual Q L.carrier _).mp
    ((IntegralDual.le_dual_iff_scale_integral Q L).mpr hs ha) _ hb

/-- Finite lower-rank class coverage and the proved projected volume bound
cover all bounded-volume lattices containing one fixed nonzero-value vector. -/
theorem finite_classes_with_fixed_vector (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (c : FractionalIdeal (integerSubring K)⁰ K)
    (y : V) (hy0 : Q y ≠ 0)
    (hcomp : HasFiniteVolumeClassRepresentatives (Q.comp (complement Q y).subtype)
      (FractionalIdeal.spanSingleton (integerSubring K)⁰
        (Q y ^ (2 * Module.finrank K V)) * c)) :
    ∃ A : Set (Lattice (integerSubring K) Q), A.Finite ∧
      ∀ (L : Lattice (integerSubring K) Q) (hy : y ∈ L.carrier) (hs : L.scaleIdeal ≤ 1),
        c ≤ L.volumeIdeal → ∃ N ∈ A, GloballyIsometric Q L N := by
  classical
  let C := Q.comp (complement Q y).subtype
  obtain ⟨B, hB, hcover⟩ := hcomp
  have hfiber (N : Lattice (integerSubring K) C) :
      ∃ A : Set (Lattice (integerSubring K) Q), A.Finite ∧
        ∀ (L : Lattice (integerSubring K) Q) (hy : y ∈ L.carrier) (hs : L.scaleIdeal ≤ 1),
          c ≤ L.volumeIdeal → GloballyIsometric C (projectedLattice Q L y hy hs hy0) N →
            ∃ M ∈ A, GloballyIsometric Q L M := by
    let F : Set (Lattice (integerSubring K) Q) :=
      {L | ∃ (hy : y ∈ L.carrier) (hs : L.scaleIdeal ≤ 1), c ≤ L.volumeIdeal ∧
        GloballyIsometric C (projectedLattice Q L y hy hs hy0) N}
    by_cases hF : F.Nonempty
    · obtain ⟨L₀, hy₀, hs₀, _, hN₀⟩ := hF
      obtain ⟨A, hA, hclasses⟩ :=
        ClassFinitenessFiber.exists_finite_representatives_of_projected_class
          Q hQ L₀ y hy₀ hs₀ hy0
      refine ⟨A, hA, ?_⟩
      intro L hy hs _ hN
      exact hclasses L hy hs (GloballyIsometric.trans C hN (GloballyIsometric.symm C hN₀))
    · refine ⟨∅, Set.finite_empty, ?_⟩
      intro L hy hs hvol hN
      exact (hF ⟨L, hy, hs, hvol, hN⟩).elim
  choose A hA hclasses using hfiber
  refine ⟨⋃ N ∈ B, A N, hB.biUnion (fun N _ ↦ hA N), ?_⟩
  intro L hy hs hvol
  obtain ⟨N, hN, hiso⟩ := hcover (projectedLattice Q L y hy hs hy0)
    (projected_scale_integral Q L y hy hs hy0)
    (projected_volume_lower_bound Q L y hy hs hy0 c hvol)
  obtain ⟨M, hM, hLM⟩ := hclasses N L hy hs hvol hiso
  exact ⟨M, Set.mem_iUnion.mpr ⟨N, Set.mem_iUnion.mpr ⟨hN, hM⟩⟩, hLM⟩

/-- Equal nonzero values are normalized by actual global isometries. This
removes the fixed-vector restriction in the geometric induction step. -/
theorem finite_classes_representing_value (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : 2 ≤ Module.finrank K V)
    (c : FractionalIdeal (integerSubring K)⁰ K) (y : V) (hy0 : Q y ≠ 0)
    (hcomp : HasFiniteVolumeClassRepresentatives (Q.comp (complement Q y).subtype)
      (FractionalIdeal.spanSingleton (integerSubring K)⁰
        (Q y ^ (2 * Module.finrank K V)) * c)) :
    ∃ A : Set (Lattice (integerSubring K) Q), A.Finite ∧
      ∀ L : Lattice (integerSubring K) Q, L.scaleIdeal ≤ 1 → c ≤ L.volumeIdeal →
        (∃ x ∈ L.carrier, Q x = Q y) → ∃ N ∈ A, GloballyIsometric Q L N := by
  obtain ⟨A, hA, hclasses⟩ := finite_classes_with_fixed_vector Q hQ c y hy0 hcomp
  refine ⟨A, hA, ?_⟩
  rintro L hs hvol ⟨x, hx, hxy⟩
  have hx0 := hxy.trans_ne hy0
  obtain ⟨u, hu, hxu⟩ := FixedValueTransitivity.exists_anisotropic_orthogonal
    Q hQ hdim x hx0
  have hux : QuadraticMap.polar Q u x = 0 :=
    (QuadraticMap.polar_comm Q u x).trans hxu
  obtain ⟨v, hv, w, hw, hmap⟩ := FixedValueTransitivity.exists_doubleReflection_map
    Q hQ x y u hx0 hxy hu hux
  let g : ambientGroup Q := (SpinorBaseChange.doubleReflection Q hQ v hv w hw).1
  let M := transportLattice Q g L
  have hLM : GloballyIsometric Q L M :=
    ⟨{ toLinearEquiv := g.1, q_eq := g.2, mem_iff := mem_transportLattice Q g L }⟩
  have hy : y ∈ M.carrier := by
    rw [← hmap]
    exact (mem_transportLattice Q g L x).mpr hx
  have hsM : M.scaleIdeal ≤ 1 := scale_integral_transport Q g L hs
  have hvolM : c ≤ M.volumeIdeal := by
    rw [← L.volumeIdeal_eq_of_globallyIsometric M hLM]
    exact hvol
  obtain ⟨N, hN, hMN⟩ := hclasses M hy hsM hvolM
  exact ⟨N, hN, GloballyIsometric.trans Q hLM hMN⟩

/-- The full geometric induction step of 103:4 is proved from its exact
finite-value input and lower-rank induction hypotheses. The complete
arithmetic proof of 103:3 is still required to apply it unconditionally. -/
theorem finite_volume_classes_step (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : 2 ≤ Module.finrank K V)
    (c : FractionalIdeal (integerSubring K)⁰ K) (hvalues : BoundedValueCoverage Q c)
    (hcomp : ∀ y : V, Q y ≠ 0 →
      HasFiniteVolumeClassRepresentatives (Q.comp (complement Q y).subtype)
        (FractionalIdeal.spanSingleton (integerSubring K)⁰
          (Q y ^ (2 * Module.finrank K V)) * c)) :
    HasFiniteVolumeClassRepresentatives Q c := by
  classical
  obtain ⟨Φ, hΦ, hzero, hvalue⟩ := hvalues
  letI : Fintype Φ := hΦ.fintype
  have hfixed (a : Φ) : ∃ A : Set (Lattice (integerSubring K) Q), A.Finite ∧
      ∀ L : Lattice (integerSubring K) Q, L.scaleIdeal ≤ 1 → c ≤ L.volumeIdeal →
        (∃ x ∈ L.carrier, Q x = (a : K)) → ∃ N ∈ A, GloballyIsometric Q L N := by
    have ha0 : (a : K) ≠ 0 := fun h ↦ hzero (h ▸ a.property)
    by_cases hrep : ∃ y : V, Q y = (a : K)
    · obtain ⟨y, hy⟩ := hrep
      have hy0 := hy.trans_ne ha0
      obtain ⟨A, hA, hclasses⟩ :=
        finite_classes_representing_value Q hQ hdim c y hy0 (hcomp y hy0)
      refine ⟨A, hA, ?_⟩
      intro L hs hvol hx
      exact hclasses L hs hvol (by simpa only [hy] using hx)
    · refine ⟨∅, Set.finite_empty, ?_⟩
      rintro L _ _ ⟨x, _, hx⟩
      exact (hrep ⟨x, hx⟩).elim
  choose A hA hclasses using hfixed
  refine ⟨⋃ a : Φ, A a, Set.finite_iUnion hA, ?_⟩
  intro L hs hvol
  obtain ⟨x, hx, hQx⟩ := hvalue L hs hvol
  obtain ⟨N, hN, hLN⟩ := hclasses ⟨Q x, hQx⟩ L hs hvol ⟨x, hx, rfl⟩
  exact ⟨N, Set.mem_iUnion.mpr ⟨⟨Q x, hQx⟩, hN⟩, hLN⟩

end NormEuclidean.ClassFinitenessInduction

namespace NormEuclidean.ClassFinitenessInduction

open ProjectedComplement
open scoped nonZeroDivisors

universe u v

/-- Complete rank induction reduces 103:4 to the exact arithmetic 103:3
coverage in ranks at least two. There is no separate lower-rank class-finiteness
premise. The coverage parameter is explicit and is still unproved in general. -/
theorem finite_volume_classes_of_bounded_value_coverage
    {F : Type v} [Field F] [NumberField F] [Invertible (2 : F)]
    (hvalues : ∀ (W : Type u) [AddCommGroup W] [Module F W] [FiniteDimensional F W]
      (Q : QuadraticForm F W), Q.polarBilin.Nondegenerate → 2 ≤ Module.finrank F W →
        ∀ c : FractionalIdeal (integerSubring F)⁰ F, c ≠ 0 → BoundedValueCoverage Q c)
    (W : Type u) [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (Q : QuadraticForm F W) (hQ : Q.polarBilin.Nondegenerate)
    (c : FractionalIdeal (integerSubring F)⁰ F) (hc : c ≠ 0) :
    HasFiniteVolumeClassRepresentatives Q c := by
  have h (n : ℕ) : ∀ (W : Type u) [AddCommGroup W] [Module F W] [FiniteDimensional F W]
      (Q : QuadraticForm F W), Q.polarBilin.Nondegenerate → Module.finrank F W = n →
        ∀ c : FractionalIdeal (integerSubring F)⁰ F, c ≠ 0 →
          HasFiniteVolumeClassRepresentatives Q c := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ _ Q hQ hdim c hc
      by_cases hn0 : n = 0
      · exact finite_volume_classes_rank_zero Q (hdim.trans hn0) c
      by_cases hn1 : n = 1
      · exact finite_volume_classes_rank_one Q hQ (hdim.trans hn1) c hc
      have htwo : 2 ≤ Module.finrank F W := by omega
      apply finite_volume_classes_step Q hQ htwo c (hvalues W Q hQ htwo c hc)
      intro y hy0
      let U := complement Q y
      have hdimU := complement_finrank Q y hy0
      have hlt : Module.finrank F U < n := by
        change Module.finrank F (complement Q y) < n
        omega
      have hregular := complement_regular Q hQ y hy0
      have hnonzero : FractionalIdeal.spanSingleton (integerSubring F)⁰
          (Q y ^ (2 * Module.finrank F W)) * c ≠ 0 :=
        mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (pow_ne_zero _ hy0)) hc
      exact ih (Module.finrank F U) hlt U (Q.comp U.subtype) hregular rfl _ hnonzero
  exact h (Module.finrank F W) W Q hQ rfl c hc

end NormEuclidean.ClassFinitenessInduction
