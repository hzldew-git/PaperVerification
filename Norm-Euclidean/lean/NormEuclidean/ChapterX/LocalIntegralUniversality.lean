import NormEuclidean.ChapterX.FiniteResidueRepresentation
import NormEuclidean.ChapterX.CompletionHensel
import NormEuclidean.ChapterX.DividedValueMultiplier
import NormEuclidean.IntegralDiagonalFrame
import NormEuclidean.ScaleIdeal

/-!
# Almost-everywhere integral representation

In dimension at least three, choose three orthogonal nonzero-value vectors
inside the global lattice. Their integral values and two are units away from
finitely many primes. Finite-residue-field representation and actual Hensel
lifting then construct a completed lattice vector of every integral value.
-/

noncomputable section

namespace NormEuclidean.LocalIntegralUniversality

open IsDedekindDomain CompletedIntegralLattice QuadraticMap Filter

/-- The value on three mutually orthogonal scaled vectors is the diagonal sum. -/
theorem ternary_value {F E : Type*} [Field F] [AddCommGroup E] [Module F E]
    (Q : QuadraticForm F E) (u v w : E)
    (huv : Q.polarBilin u v = 0) (huw : Q.polarBilin u w = 0)
    (hvw : Q.polarBilin v w = 0) (x y z : F) :
    Q (x • u + y • v + z • w) = Q u * x ^ 2 + Q v * y ^ 2 + Q w * z ^ 2 := by
  have hxy : Q.polarBilin (x • u) (y • v) = 0 := by
    simp [huv]
  have hxyz : Q.polarBilin (x • u + y • v) (z • w) = 0 := by
    simp [huw, hvw]
  have hxyQ := (Q.isOrtho_polarBilin).mp hxy
  have hxyzQ := (Q.isOrtho_polarBilin).mp hxyz
  rw [isOrtho_def] at hxyQ hxyzQ
  rw [hxyzQ, hxyQ, Q.map_smul, Q.map_smul, Q.map_smul]
  simp only [smul_eq_mul]
  ring

section Places

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K] [Invertible (2 : K)]

/-- The polar pairing of two included global vectors is its actual field image. -/
theorem polar_inclusion (v : HeightOneSpectrum R) (Q : QuadraticForm K V) (x y : V) :
    (form R v Q).polarBilin (inclusion R v x) (inclusion R v y) =
      algebraMap K (LocalField R v) (Q.polarBilin x y) := by
  simp only [polarBilin_apply_apply, polar, ← inclusion_add, form_inclusion, map_sub]

end Places

section NumberField

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V]

/-- A regular lattice of rank at least three contains three mutually orthogonal
vectors of nonzero integral quadratic value, without an integral basis premise. -/
theorem exists_integral_orthogonal_triple (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (L : Lattice (integerSubring K) Q)
    (hdim : 3 ≤ Module.finrank K V) :
    ∃ w : Fin 3 → V, (∀ i, w i ∈ L.carrier ∧ Q (w i) ≠ 0) ∧
      ∀ i j, i ≠ j → Q.polarBilin (w i) (w j) = 0 := by
  classical
  letI := L.finiteDimensional
  let q := SpinorBridge.quadraticSpace Q hQ
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.mp q.isSymm)
  let ix : Fin 3 → Fin (Module.finrank K V) := fun i ↦ ⟨i.1, lt_of_lt_of_le i.2 hdim⟩
  choose d hd0 hd using fun i : Fin 3 ↦
    ScalarExtension.exists_denominator L.carrier L.full (b (ix i))
  have hdK (i : Fin 3) : (d i : K) ≠ 0 := by exact_mod_cast hd0 i
  let w := fun i : Fin 3 ↦ (d i : K) • b (ix i)
  refine ⟨w, ?_, ?_⟩
  · intro i
    have hb0 : q.quadratic (b (ix i)) ≠ 0 :=
      LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate
        hb q.nondegenerate (ix i)
    have hQb : Q (b (ix i)) ≠ 0 := by
      simpa only [q, SpinorBridge.quadraticSpace_quadratic] using hb0
    refine ⟨hd i, ?_⟩
    change Q ((d i : K) • b (ix i)) ≠ 0
    rw [Q.map_smul, smul_eq_mul]
    exact mul_ne_zero (mul_ne_zero (hdK i) (hdK i)) hQb
  · intro i j hij
    have hij' : ix i ≠ ix j := by
      intro h
      apply hij
      apply Fin.ext
      exact congrArg (fun k : Fin (Module.finrank K V) ↦ k.1) h
    have hB : q.bilin (w i) (w j) = 0 := by
      simp only [w, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
        hb hij', mul_zero]
    change (2 : K)⁻¹ * Q.polarBilin (w i) (w j) = 0 at hB
    exact (mul_eq_zero.mp hB).resolve_left (inv_ne_zero (by norm_num))

/-- Almost every actual finite completed lattice represents every integral
local value. This discharges the local universality premise of 104:1. -/
theorem eventually_integrally_represents (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (L : Lattice (integerSubring K) Q)
    (hdim : 3 ≤ Module.finrank K V) :
    ∀ᶠ v : HeightOneSpectrum (integerSubring K) in cofinite,
      ∀ t : LocalField (integerSubring K) v, t ∈ LocalRing (integerSubring K) v →
        ∃ z ∈ carrier (integerSubring K) v L.carrier, form (integerSubring K) v Q z = t := by
  classical
  obtain ⟨w, hw, horth⟩ := exists_integral_orthogonal_triple Q hQ L hdim
  let c : Fin 3 → integerSubring K := fun i ↦ ⟨Q (w i), L.integral _ (hw i).1⟩
  have hc0 (i : Fin 3) : c i ≠ 0 := by
    intro h
    exact (hw i).2 (congrArg Subtype.val h)
  have htwone : (2 : integerSubring K) ≠ 0 := by
    exact_mod_cast (by norm_num : (2 : K) ≠ 0)
  have htwoev : ∀ᶠ v : HeightOneSpectrum (integerSubring K) in cofinite,
      (2 : integerSubring K) ∉ v.asIdeal := by
    apply eventually_cofinite.mpr
    simpa only [not_not] using
      finite_primes_containing (K := K) (integerSubring K) 2 htwone
  have hcev : ∀ᶠ v : HeightOneSpectrum (integerSubring K) in cofinite,
      ∀ i : Fin 3, c i ∉ v.asIdeal := by
    apply eventually_all.mpr
    intro i
    apply eventually_cofinite.mpr
    simpa only [not_not] using
      finite_primes_containing (K := K) (integerSubring K) (c i) (hc0 i)
  filter_upwards [htwoev, hcev] with v htwo hc
  let S := LocalRing (integerSubring K) v
  let A := LocalField (integerSubring K) v
  letI := CompletionHensel.finite_residue_field v
  letI := CompletionHensel.henselian_completed_integers v
  let ci : Fin 3 → S := fun i ↦
    ⟨algebraMap K A (c i : K), algebraMap_mem (integerSubring K) v (c i).property⟩
  have hunit (i : Fin 3) : IsUnit (ci i) :=
    isUnit_algebraMap_localRing (integerSubring K) v (hc i)
  choose u hu using hunit
  have htwoS : IsUnit (2 : S) := by
    have h : IsUnit (⟨algebraMap K A ((2 : integerSubring K) : K),
      algebraMap_mem (integerSubring K) v (2 : integerSubring K).property⟩ : S) :=
        isUnit_algebraMap_localRing (integerSubring K) v htwo
    convert h using 1
    apply Subtype.ext
    change (2 : A) = algebraMap K A (2 : K)
    exact (map_ofNat (algebraMap K A) 2).symm
  have horthlocal (i j : Fin 3) (hij : i ≠ j) :
      (form (integerSubring K) v Q).polarBilin
        (inclusion (integerSubring K) v (w i)) (inclusion (integerSubring K) v (w j)) = 0 := by
    rw [polar_inclusion, horth i j hij, map_zero]
  intro t ht
  obtain ⟨x, y, z, hrep⟩ := FiniteResidueRepresentation.henselian_ternary_represents
    htwoS (u 0) (u 1) (u 2) (⟨t, ht⟩ : S)
  let e := fun i : Fin 3 ↦ inclusion (integerSubring K) v (w i)
  let M := carrier (integerSubring K) v L.carrier
  have he (i : Fin 3) : e i ∈ M := inclusion_mem (integerSubring K) v L.carrier (hw i).1
  refine ⟨x • e 0 + y • e 1 + z • e 2,
    M.add_mem (M.add_mem (M.smul_mem x (he 0)) (M.smul_mem y (he 1)))
      (M.smul_mem z (he 2)), ?_⟩
  have hfield := congrArg (fun r : S ↦ (r : A)) hrep
  simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_pow, hu] at hfield
  change form (integerSubring K) v Q
    ((x : A) • e 0 + (y : A) • e 1 + (z : A) • e 2) = t
  rw [ternary_value _ _ _ _ (horthlocal 0 1 (by decide))
    (horthlocal 0 2 (by decide)) (horthlocal 1 2 (by decide))]
  simpa only [e, form_inclusion, ci, c] using hfield

/-- Almost every completed quadratic value set is exactly the completed integer ring. -/
theorem eventually_value_set_eq_integer_ring (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (L : Lattice (integerSubring K) Q)
    (hdim : 3 ≤ Module.finrank K V) :
    ∀ᶠ v : HeightOneSpectrum (integerSubring K) in cofinite,
      form (integerSubring K) v Q ''
        (carrier (integerSubring K) v L.carrier : Set (Space (V := V) (integerSubring K) v)) =
          (LocalRing (integerSubring K) v : Set (LocalField (integerSubring K) v)) := by
  filter_upwards [eventually_integrally_represents Q hQ L hdim] with v hv
  ext t
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact carrier_integral (integerSubring K) v Q L.carrier L.integral z hz
  · intro ht
    obtain ⟨z, hz, hzt⟩ := hv t ht
    exact ⟨z, hz, hzt⟩

/-- The divided-value conclusion of 104:1 now needs only actual class
finiteness: almost-everywhere integral universality is proved internally. -/
theorem exists_divided_value_multiplier_of_finite_classes (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (L : Lattice (integerSubring K) Q)
    (hdim : 3 ≤ Module.finrank K V) (hfinite : Finite (GenusClassSet Q L))
    (T : Finset (HeightOneSpectrum (integerSubring K))) :
    ∃ γ : integerSubring K, γ ≠ 0 ∧
      (∀ v ∈ T, IsUnit (⟨algebraMap K (LocalField (integerSubring K) v) (γ : K),
        algebraMap_mem (integerSubring K) v γ.property⟩ : LocalRing (integerSubring K) v)) ∧
      ∀ a : K, (∃ b : integerSubring K, a = (γ : K) * (b : K)) →
        (∃ x : V, Q x = a) →
        (∀ v : HeightOneSpectrum (integerSubring K),
          ∃ z ∈ carrier (integerSubring K) v L.carrier,
            form (integerSubring K) v Q z =
              algebraMap K (LocalField (integerSubring K) v) a) →
        ∃ x ∈ L.carrier, Q x = a := by
  letI := L.finiteDimensional
  exact DividedValueMultiplier.exists_divided_value_multiplier_of_eventual_universality
    Q hQ (by omega) L hfinite T (eventually_integrally_represents Q hQ L hdim)

end NumberField

end NormEuclidean.LocalIntegralUniversality
