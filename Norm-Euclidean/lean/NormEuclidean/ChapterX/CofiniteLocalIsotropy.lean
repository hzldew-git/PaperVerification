import NormEuclidean.ChapterX.BinaryUnitRepresentation
import NormEuclidean.ChapterX.LocalIntegralUniversality
import NormEuclidean.ChapterX.ScalarIntegralApproximation
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# The cofinite local-isotropy input in O'Meara 66:1

This ports the coordinate-support argument inspected in the author's
HeADC development to the project's quadratic forms and actual completions.
The ternary isotropic vector is constructed by the proved binary Hensel
lifting, with a fixed nonzero third coordinate. This is Example 63:14;
it does not assert global Hasse--Minkowski.
-/

noncomputable section

namespace NormEuclidean.CofiniteLocalIsotropy

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation Filter

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]

/-- A nonzero field scalar has only finitely many finite zeros and poles. -/
theorem finite_nonunit_valuations (a : K) (ha : a ≠ 0) :
    {p : HeightOneSpectrum (integerSubring K) | p.valuation K a ≠ 1}.Finite := by
  apply ((HeightOneSpectrum.Support.finite (integerSubring K) a).union
    (HeightOneSpectrum.Support.finite (integerSubring K) a⁻¹)).subset
  intro p hp
  by_cases hhigh : 1 < p.valuation K a
  · exact Or.inl hhigh
  · apply Or.inr
    change 1 < p.valuation K a⁻¹
    rw [map_inv₀]
    exact one_lt_inv_iff₀.mpr
      ⟨(Valuation.pos_iff (p.valuation K)).mpr ha, lt_of_le_of_ne (le_of_not_gt hhigh) hp⟩

variable [Invertible (2 : K)] [FiniteDimensional K V]

/-- Every regular number-field form of rank at least three is isotropic
at almost every actual finite completion. No global local-to-global law,
integral lattice, dyadic context or isotropy premise is supplied. -/
theorem eventually_isotropic (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : 3 ≤ Module.finrank K V) :
    ∀ᶠ p : HeightOneSpectrum (integerSubring K) in cofinite,
      ¬ (form (integerSubring K) p Q).Anisotropic := by
  classical
  let q := SpinorBridge.quadraticSpace Q hQ
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.mp q.isSymm)
  let ix : Fin 3 → Fin (Module.finrank K V) := fun i ↦ ⟨i.1, lt_of_lt_of_le i.2 hdim⟩
  let w := fun i : Fin 3 ↦ b (ix i)
  have hval (i : Fin 3) : Q (w i) ≠ 0 := by
    have h : q.quadratic (w i) ≠ 0 :=
      LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate
      hb q.nondegenerate (ix i)
    simpa only [q, w, SpinorBridge.quadraticSpace_quadratic] using h
  have horth (i j : Fin 3) (hij : i ≠ j) : Q.polarBilin (w i) (w j) = 0 := by
    have hix : ix i ≠ ix j := fun h ↦ hij
      (Fin.ext (congrArg (fun k : Fin (Module.finrank K V) ↦ k.val) h))
    have h : q.bilin (w i) (w j) = 0 := hb hix
    change (2 : K)⁻¹ * Q.polarBilin (w i) (w j) = 0 at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (by norm_num))
  have hev : ∀ᶠ p : HeightOneSpectrum (integerSubring K) in cofinite,
      ∀ i : Fin 3, p.valuation K (Q (w i)) = 1 := by
    apply eventually_all.mpr
    intro i
    exact eventually_cofinite.mpr (finite_nonunit_valuations _ (hval i))
  have htwoev : ∀ᶠ p : HeightOneSpectrum (integerSubring K) in cofinite,
      (2 : integerSubring K) ∉ p.asIdeal := by
    apply eventually_cofinite.mpr
    simpa only [not_not] using
      finite_primes_containing (K := K) (integerSubring K) 2 (by norm_num)
  filter_upwards [hev, htwoev] with p hp hp2
  let F := LocalField (integerSubring K) p
  let S := LocalRing (integerSubring K) p
  let P := form (integerSubring K) p Q
  let e := fun i : Fin 3 ↦ inclusion (integerSubring K) p (w i)
  letI := CompletionHensel.finite_residue_field p
  letI := CompletionHensel.henselian_completed_integers p
  have hci (i : Fin 3) : algebraMap K F (Q (w i)) ∈ S := by
    change Valued.v (algebraMap K F (Q (w i))) ≤ 1
    rw [valuation_algebraMap, hp i]
  let ci : Fin 3 → S := fun i ↦ ⟨algebraMap K F (Q (w i)), hci i⟩
  have hunit (i : Fin 3) : IsUnit (ci i) := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact (valuation_algebraMap _ _ _).trans (hp i)
  choose u hu using hunit
  have htwo : IsUnit (2 : S) := by
    have h := isUnit_algebraMap_localRing (integerSubring K) p hp2
    convert h using 1
    apply Subtype.ext
    change (2 : F) = algebraMap K F (2 : K)
    exact (map_ofNat _ 2).symm
  obtain ⟨s, t, hst⟩ := BinaryUnitRepresentation.henselian_binary_represents_unit
    htwo (u 0) (u 1) (-(u 2))
  have hfield := congrArg (fun a : S ↦ (a : F)) hst
  have hPQ (i : Fin 3) : P (e i) = algebraMap K F (Q (w i)) := form_inclusion _ p Q _
  have heorth (i j : Fin 3) (hij : i ≠ j) : P.polarBilin (e i) (e j) = 0 := by
    rw [LocalIntegralUniversality.polar_inclusion, horth i j hij, map_zero]
  let z := (s : F) • e 0 + (t : F) • e 1 + e 2
  have hzQ : P z = 0 := by
    have hz := LocalIntegralUniversality.ternary_value P (e 0) (e 1) (e 2)
      (heorth 0 1 (by decide)) (heorth 0 2 (by decide)) (heorth 1 2 (by decide))
      (s : F) (t : F) 1
    simp only [one_smul, one_pow, mul_one, hPQ] at hz
    simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_pow, Units.val_neg, hu] at hfield
    change algebraMap K F (Q (w 0)) * (s : F) ^ 2 +
      algebraMap K F (Q (w 1)) * (t : F) ^ 2 = -algebraMap K F (Q (w 2)) at hfield
    change P z = _ at hz
    rw [hz]
    change _ + algebraMap K F (Q (w 2)) = 0
    linear_combination hfield
  have hzg : P.polarBilin (e 2) z = 2 * P (e 2) := by
    simp only [z, LinearMap.map_add, map_smul, smul_eq_mul,
      heorth 2 0 (by decide), heorth 2 1 (by decide), mul_zero, zero_add,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul]
    norm_num
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hzg
    have hQe : P (e 2) ≠ 0 := by rw [hPQ]; exact (map_ne_zero _).mpr (hval 2)
    exact mul_ne_zero (by norm_num) hQe hzg.symm
  exact P.not_anisotropic_iff_exists.mpr ⟨z, hz0, hzQ⟩

end NormEuclidean.CofiniteLocalIsotropy
