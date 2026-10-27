import NormEuclidean.IntegralSpan
import NormEuclidean.ScalarExtension
import NormEuclidean.HyperbolicModule
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct

/-!
# Integral lattices over actual finite completions

For a height-one prime of the integral Dedekind subring `R ⊆ K`, the ambient
space is `K_v ⊗[K] V`, where `K_v` is mathlib's valuation completion. The
integral lattice is the `O_v`-span of the image of `L`, where `O_v` is the actual
valuation subring of that completion. Finite generation, fullness, quadratic
integrality, and transport of actual integral isometries are proved below.

Quadratic scalar extension is performed over the field `K`. Invertibility of
two is never required in `R` or in `O_v`, so this construction includes dyadic
places. This file does not assert local classification, a topological universal
property for the lattice, or a local-to-global theorem.
-/

open scoped TensorProduct
open IsDedekindDomain
namespace NormEuclidean.CompletedIntegralLattice
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
variable (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)
abbrev LocalField := v.adicCompletion K
noncomputable abbrev LocalRing : Subring (LocalField R v) := (v.adicCompletionIntegers K).toSubring
abbrev Space := LocalField R v ⊗[K] V
noncomputable def inclusion : V →ₗ[K] Space (V := V) R v :=
  TensorProduct.mk K (LocalField R v) V 1
noncomputable def carrier (L : Submodule R V) : Submodule (LocalRing R v) (Space (V := V) R v) :=
  Submodule.span (LocalRing R v) (inclusion R v '' (L : Set V))
@[simp] theorem inclusion_add (x y : V) : inclusion R v (x+y) = inclusion R v x + inclusion R v y :=
  (inclusion R v).map_add x y

/-- Global integers land in the completed valuation ring. -/
theorem algebraMap_mem {a : K} (ha : a ∈ R) :
    algebraMap K (LocalField R v) a ∈ LocalRing R v := by
  exact HeightOneSpectrum.coe_algebraMap_mem R K v ⟨a, ha⟩

theorem inclusion_smul (a : R) (x : V) :
    inclusion R v (a • x) =
      (⟨algebraMap K (LocalField R v) (a : K), algebraMap_mem R v a.property⟩ : LocalRing R v) •
        inclusion R v x := by
  change inclusion R v ((a : K) • x) = _
  rw [(inclusion R v).map_smul]
  conv_lhs =>
    rw [← IsScalarTower.algebraMap_smul
      (R := K) (A := LocalField R v)]
  conv_rhs =>
    rw [← IsScalarTower.algebraMap_smul
      (R := LocalRing R v) (A := LocalField R v)]
  rw [Algebra.algebraMap_ofSubsemiring_apply]

/-- Every global lattice vector gives an integral generator locally. -/
theorem inclusion_mem (L : Submodule R V) {x : V} (hx : x ∈ L) :
    inclusion R v x ∈ carrier R v L := Submodule.subset_span ⟨x, hx, rfl⟩

/-- Finite generation is preserved without choosing a lattice basis. -/
theorem carrier_fg (L : Submodule R V) (hL : L.FG) : (carrier R v L).FG := by
  obtain ⟨s, hs⟩ := hL
  have heq : carrier R v L = Submodule.span (LocalRing R v)
      (inclusion R v '' (s : Set V)) := by
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro _ ⟨x, hx, rfl⟩
      rw [← hs] at hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero =>
          rw [map_zero]
          exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
          rw [map_add]
          exact Submodule.add_mem _ hx hy
      | smul a x _ hx => rw [inclusion_smul]; exact Submodule.smul_mem _ _ hx
    · apply Submodule.span_mono
      exact Set.image_mono (by rw [← hs]; exact Submodule.subset_span)
  rw [heq]
  exact Submodule.fg_span (s.finite_toSet.image _)

/-- Fullness is preserved in the completed ambient vector space. -/
theorem carrier_full (L : Submodule R V)
    (hL : Submodule.span K (L : Set V) = ⊤) :
    Submodule.span (LocalField R v) (carrier R v L : Set (Space (V := V) R v)) = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  have hgen : ∀ x : V, inclusion R v x ∈
      Submodule.span (LocalField R v) (carrier R v L : Set (Space (V := V) R v)) := by
    intro x
    have hx : x ∈ Submodule.span K (L : Set V) := by rw [hL]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (inclusion_mem R v L hx)
    | zero => simp
    | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [map_smul]
      simpa only [algebraMap_smul] using
        Submodule.smul_mem _ (algebraMap K (LocalField R v) a) hx
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a x =>
    have h := Submodule.smul_mem _ a (hgen x)
    simpa only [inclusion, LinearMap.flip_apply, TensorProduct.mk_apply,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h
  | add x y hx hy => exact Submodule.add_mem _ hx hy

/-- Extend an ambient linear equivalence to the actual completed fields. -/
noncomputable def equiv (e : V ≃ₗ[K] W) :
    Space (V := V) R v ≃ₗ[LocalField R v] Space (V := W) R v :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (LocalField R v) (LocalField R v)) e

@[simp] theorem equiv_inclusion (e : V ≃ₗ[K] W) (x : V) :
    equiv R v e (inclusion R v x) = inclusion R v (e x) := rfl

theorem equiv_carrier_forward (L : Submodule R V) (L' : Submodule R W)
    (e : V ≃ₗ[K] W) (he : ∀ x ∈ L, e x ∈ L')
    {z : Space (V := V) R v} (hz : z ∈ carrier R v L) :
    equiv R v e z ∈ carrier R v L' := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    rw [equiv_inclusion]
    exact inclusion_mem R v L' (he x hx)
  | zero => simpa only [map_zero] using (carrier R v L').zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using (carrier R v L').add_mem hx hy
  | smul a x _ hx =>
    change equiv R v e ((a : LocalField R v) • x) ∈ _
    rw [map_smul]
    exact (carrier R v L').smul_mem a hx

/-- Completed spans preserve every actual lattice-preserving ambient equivalence. -/
theorem equiv_carrier (L : Submodule R V) (L' : Submodule R W)
    (e : V ≃ₗ[K] W) (he : ∀ x, e x ∈ L' ↔ x ∈ L)
    (z : Space (V := V) R v) :
    equiv R v e z ∈ carrier R v L' ↔ z ∈ carrier R v L := by
  constructor
  · intro hz
    have h := equiv_carrier_forward R v L' L e.symm
      (fun x hx => (he (e.symm x)).1 (by simpa using hx)) hz
    change (equiv R v e).symm ((equiv R v e) z) ∈ carrier R v L at h
    simpa using h
  · exact equiv_carrier_forward R v L L' e (fun x hx => (he x).2 hx)

variable [Invertible (2 : K)]
noncomputable def form (Q : QuadraticForm K V) : QuadraticForm (LocalField R v) (Space (V := V) R v) :=
  Q.baseChange (LocalField R v)
@[simp] theorem form_inclusion (Q : QuadraticForm K V) (x : V) :
  form R v Q (inclusion R v x) = algebraMap K (LocalField R v) (Q x) := by
  simp [form, inclusion, Algebra.smul_def]
/-- Integrality persists in the completed lattice, including dyadic places.
The proof uses the full polar form rather than dividing integral values by two. -/
theorem carrier_integral (Q : QuadraticForm K V) (L : Submodule R V)
    (hQ : ∀ x ∈ L, Q x ∈ R) :
    ∀ z ∈ carrier R v L, form R v Q z ∈ LocalRing R v := by
  intro z hz
  apply quadratic_mem_subring_of_mem_span (form R v Q)
    (inclusion R v '' (L : Set V)) ?_ ?_ hz
  · rintro _ ⟨x, hx, rfl⟩
    rw [form_inclusion]
    exact algebraMap_mem R v (hQ x hx)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [QuadraticMap.polar, ← inclusion_add, form_inclusion]
    exact (LocalRing R v).sub_mem
      ((LocalRing R v).sub_mem (algebraMap_mem R v (hQ _ (L.add_mem hx hy)))
        (algebraMap_mem R v (hQ x hx))) (algebraMap_mem R v (hQ y hy))

/-- The actual completed full integral lattice, with finite generation proved. -/
noncomputable def lattice (Q : QuadraticForm K V) (L : Lattice R Q) :
    Lattice (LocalRing R v) (form R v Q) where
  carrier := carrier R v L.carrier
  finite := carrier_fg R v L.carrier L.finite
  full := carrier_full R v L.carrier L.full
  integral := carrier_integral R v Q L.carrier L.integral

/-- Scalar extension respects the quadratic values of actual isometries. -/
theorem equiv_form (Q : QuadraticForm K V) (Q' : QuadraticForm K W)
    (e : V ≃ₗ[K] W) (he : ∀ x, Q' (e x) = Q x)
    (z : Space (V := V) R v) :
    form R v Q' (equiv R v e z) = form R v Q z := by
  have h : (form R v Q').comp (equiv R v e).toLinearMap = form R v Q := by
    apply baseChange_ext
    intro x
    change form R v Q' (equiv R v e (inclusion R v x)) = form R v Q (inclusion R v x)
    rw [equiv_inclusion, form_inclusion, form_inclusion, he]
  exact DFunLike.congr_fun h z

/-- An actual global lattice isometry induces an actual integral local isometry. -/
noncomputable def isometry {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    {L : Submodule R V} {L' : Submodule R W} (e : LatticeIsometry Q Q' L L') :
    LatticeIsometry (form R v Q) (form R v Q') (carrier R v L) (carrier R v L') where
  toLinearEquiv := equiv R v e.toLinearEquiv
  q_eq := equiv_form R v Q Q' e.toLinearEquiv e.q_eq
  mem_iff := equiv_carrier R v L L' e.toLinearEquiv e.mem_iff

end NormEuclidean.CompletedIntegralLattice
