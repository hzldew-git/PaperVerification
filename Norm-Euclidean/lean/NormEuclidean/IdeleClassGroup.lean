import NormEuclidean.FiniteIdele
import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Finite ideles and the ordinary ideal class group

The map is defined from actual finite ideles to actual fractional ideals and
then to mathlib's ideal class group. Its kernel consists of the diagonal field
units times the product of local integral units; no PID hypothesis is used.
-/

noncomputable section

namespace NormEuclidean.FiniteIdele

open IsDedekindDomain
open scoped nonZeroDivisors WithZero

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The finite-idele ideal map, valued in the group of invertible fractional ideals. -/
def idealUnitHom : (FiniteAdeleRing R K)ˣ →* (FractionalIdeal R⁰ K)ˣ where
  toFun a := Units.mk0 (fractionalIdeal a) (fractionalIdeal_ne_zero a)
  map_one' := Units.ext fractionalIdeal_one
  map_mul' a b := Units.ext (fractionalIdeal_mul a b)

@[simp] theorem idealUnitHom_val (a : (FiniteAdeleRing R K)ˣ) :
    (idealUnitHom a : FractionalIdeal R⁰ K) = fractionalIdeal a := rfl

/-- The ordinary ideal class of a finite idele. -/
def classHom : (FiniteAdeleRing R K)ˣ →* ClassGroup R :=
  (ClassGroup.mk K).comp idealUnitHom

theorem classHom_eq_one_iff_principal (a : (FiniteAdeleRing R K)ˣ) :
    classHom a = 1 ↔ (fractionalIdeal a : Submodule R K).IsPrincipal :=
  ClassGroup.mk_eq_one_iff

@[simp] theorem classHom_diagonal (k : Kˣ) :
    classHom (FiniteAdeleRing.unitEmbedding R K k) = 1 := by
  rw [classHom_eq_one_iff_principal, FractionalIdeal.isPrincipal_iff]
  exact ⟨k, fractionalIdeal_diagonal k⟩

theorem classHom_eq_one_of_localUnit {a : (FiniteAdeleRing R K)ˣ}
    (ha : a ∈ localUnitSubgroup) : classHom a = 1 := by
  have hi : fractionalIdeal a = 1 := by
    change a ∈ (idealHom (R := R) (K := K)).ker
    rwa [idealHom_ker]
  have hu : idealUnitHom a = 1 := Units.ext hi
  change ClassGroup.mk K (idealUnitHom a) = 1
  rw [hu, map_one]

/-- Principal ideal class is exactly the condition for a diagonal/local-unit decomposition. -/
theorem exists_diagonal_mul_localUnit_of_classHom_eq_one
    (a : (FiniteAdeleRing R K)ˣ) (ha : classHom a = 1) :
    ∃ k : Kˣ, ∃ u : localUnitSubgroup (R := R) (K := K),
      a = FiniteAdeleRing.unitEmbedding R K k * u.1 := by
  obtain ⟨k, hk⟩ := (FractionalIdeal.isPrincipal_iff (fractionalIdeal a)).mp
    ((classHom_eq_one_iff_principal a).mp ha)
  have hk0 : k ≠ 0 := by
    intro h
    apply fractionalIdeal_ne_zero a
    simpa [h] using hk
  let k' : Kˣ := Units.mk0 k hk0
  let d := FiniteAdeleRing.unitEmbedding R K k'
  let u := d⁻¹ * a
  have hu : u ∈ localUnitSubgroup := by
    intro v
    change order (d⁻¹ * a) v = 0
    rw [order_mul, order_inv]
    have hd : order d v = order a v := by
      rw [order_diagonal, ← count_fractionalIdeal a v]
      exact congrArg (FractionalIdeal.count K v) hk.symm
    rw [hd, neg_add_cancel]
  exact ⟨k', ⟨u, hu⟩, by dsimp [u, d]; simp⟩

/-- The finite-idele ordinary class kernel: diagonal field units times all local units. -/
theorem classHom_ker : (classHom (R := R) (K := K)).ker =
    (FiniteAdeleRing.unitEmbedding R K).range ⊔ localUnitSubgroup := by
  apply le_antisymm
  · intro a ha
    obtain ⟨k, u, h⟩ := exists_diagonal_mul_localUnit_of_classHom_eq_one a ha
    rw [h]
    exact Subgroup.mul_mem_sup ⟨k, rfl⟩ u.2
  · apply sup_le
    · rintro a ⟨k, rfl⟩
      exact classHom_diagonal k
    · intro a ha
      exact classHom_eq_one_of_localUnit ha

/-- The genuine ordinary finite idelic class quotient. -/
abbrev ClassQuotient := (FiniteAdeleRing R K)ˣ ⧸
  ((FiniteAdeleRing.unitEmbedding R K).range ⊔ localUnitSubgroup)

/-- First-isomorphism equivalence, without assuming surjectivity onto the class group. -/
def classQuotientEquivRange : ClassQuotient (R := R) (K := K) ≃*
    (classHom (R := R) (K := K)).range :=
  (QuotientGroup.quotientMulEquivOfEq classHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivRange classHom)

/-- A unit of the local field with valuation `exp (-1)`, chosen from the global fraction field. -/
def localUniformizer (v : HeightOneSpectrum R) : (v.adicCompletion K)ˣ := by
  let π : K := (v.valuation_exists_uniformizer K).choose
  have hπ : (Valued.v (π : v.adicCompletion K) : ℤᵐ⁰) = WithZero.exp (-1 : ℤ) := by
    rw [v.valuedAdicCompletion_eq_valuation']
    exact (v.valuation_exists_uniformizer K).choose_spec
  refine Units.mk0 (π : v.adicCompletion K) ?_
  intro h
  rw [h, map_zero] at hπ
  exact WithZero.exp_ne_zero hπ.symm

@[simp] theorem localUniformizer_valuation (v : HeightOneSpectrum R) :
    (Valued.v (localUniformizer (K := K) v : v.adicCompletion K) : ℤᵐ⁰) =
      WithZero.exp (-1 : ℤ) := by
  change (Valued.v (((v.valuation_exists_uniformizer K).choose : K) : v.adicCompletion K) :
    ℤᵐ⁰) = _
  rw [v.valuedAdicCompletion_eq_valuation']
  exact (v.valuation_exists_uniformizer K).choose_spec

/-- An actual restricted-product unit realizing any finitely supported divisor. -/
def ideleOfDivisor (d : HeightOneSpectrum R →₀ ℤ) : (FiniteAdeleRing R K)ˣ :=
  RestrictedProduct.mkUnit (B := fun v : HeightOneSpectrum R ↦ v.adicCompletionIntegers K)
    (fun v ↦ localUniformizer v ^ d v) (by
      have hd : ∀ᶠ v in Filter.cofinite, d v = 0 := d.hasFiniteSupport
      filter_upwards [hd] with v hv
      rw [hv, zpow_zero]
      exact one_mem _)

@[simp] theorem componentUnit_ideleOfDivisor (d : HeightOneSpectrum R →₀ ℤ)
    (v : HeightOneSpectrum R) :
    componentUnit v (ideleOfDivisor (K := K) d) = localUniformizer v ^ d v :=
  Units.ext rfl

@[simp] theorem order_ideleOfDivisor (d : HeightOneSpectrum R →₀ ℤ)
    (v : HeightOneSpectrum R) : order (ideleOfDivisor (K := K) d) v = d v := by
  change -WithZero.log (Valued.v ((localUniformizer v ^ d v :
    (v.adicCompletion K)ˣ) : v.adicCompletion K)) = _
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, localUniformizer_valuation,
    WithZero.log_zpow, WithZero.log_exp]
  simp

@[simp] theorem divisor_ideleOfDivisor (d : HeightOneSpectrum R →₀ ℤ) :
    divisor (ideleOfDivisor (K := K) d) = d := by
  ext v
  exact order_ideleOfDivisor d v

/-- Every invertible fractional ideal is represented by an actual finite idele. -/
theorem idealUnitHom_surjective :
    Function.Surjective (idealUnitHom (R := R) (K := K)) := by
  intro I
  let d : HeightOneSpectrum R →₀ ℤ := Finsupp.ofSupportFinite
    (fun v ↦ FractionalIdeal.count K v I) (FractionalIdeal.finite_factors I.1)
  refine ⟨ideleOfDivisor d, Units.ext ?_⟩
  change fractionalIdeal (ideleOfDivisor d) = I.1
  apply fractionalIdeal_ext (fractionalIdeal_ne_zero _) I.ne_zero
  intro v
  rw [count_fractionalIdeal, order_ideleOfDivisor]
  rfl

/-- The finite idelic class map is onto the full ordinary ideal class group. -/
theorem classHom_surjective : Function.Surjective (classHom (R := R) (K := K)) := by
  intro c
  refine ClassGroup.induction K (fun I ↦ ?_) c
  obtain ⟨a, ha⟩ := idealUnitHom_surjective I
  exact ⟨a, congrArg (ClassGroup.mk K) ha⟩

/-- The ordinary finite idelic class quotient is the actual ordinary ideal class group. -/
def classQuotientEquivClassGroup : ClassQuotient (R := R) (K := K) ≃* ClassGroup R :=
  (QuotientGroup.quotientMulEquivOfEq classHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective classHom classHom_surjective)

@[simp] theorem classQuotientEquivClassGroup_mk (a : (FiniteAdeleRing R K)ˣ) :
    classQuotientEquivClassGroup (QuotientGroup.mk a) = classHom a := by
  change QuotientGroup.quotientKerEquivOfSurjective classHom classHom_surjective
    (QuotientGroup.quotientMulEquivOfEq classHom_ker.symm (QuotientGroup.mk a)) = _
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

end NormEuclidean.FiniteIdele
