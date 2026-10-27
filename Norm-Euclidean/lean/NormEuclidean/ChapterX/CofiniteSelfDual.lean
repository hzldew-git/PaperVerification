import NormEuclidean.ChapterX.IntegralMatrix
import NormEuclidean.ChapterX.QuadraticValueNormalization
import NormEuclidean.ChapterX.CofiniteLocalIsotropy

/-!
# Almost-everywhere self-duality of completed full modules

A field orthogonal basis has unit diagonal values at almost every prime.
Its integral span is then self-dual. Every finite full module has the
same completed carrier as that span away from finitely many primes.
No global integral basis of the given module is required.
-/

noncomputable section

namespace NormEuclidean.CofiniteSelfDual

open IsDedekindDomain CompletedIntegralLattice ScalarIntegralApproximation LocalPrimitivePairing
  Filter
open scoped TensorProduct

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]

/-- Any two finite full modules have equal completed carriers at almost every finite place. -/
theorem carrier_eventually_eq (L M : Submodule (integerSubring K) V)
    (hLfg : L.FG) (hMfg : M.FG) (hL : Submodule.span K (L : Set V) = ⊤)
    (hM : Submodule.span K (M : Set V) = ⊤) :
    ∀ᶠ p : HeightOneSpectrum (integerSubring K) in cofinite,
      carrier (integerSubring K) p L = carrier (integerSubring K) p M := by
  obtain ⟨a, ha0, ha⟩ := exists_lattice_denominator L M hLfg hM
  obtain ⟨b, hb0, hb⟩ := exists_lattice_denominator M L hMfg hL
  have haev : ∀ᶠ p : HeightOneSpectrum (integerSubring K) in cofinite, a ∉ p.asIdeal := by
    apply eventually_cofinite.mpr
    simpa only [not_not] using finite_primes_containing (K := K) (integerSubring K) a ha0
  have hbev : ∀ᶠ p : HeightOneSpectrum (integerSubring K) in cofinite, b ∉ p.asIdeal := by
    apply eventually_cofinite.mpr
    simpa only [not_not] using finite_primes_containing (K := K) (integerSubring K) b hb0
  filter_upwards [haev, hbev] with p hap hbp
  exact le_antisymm
    (carrier_le_of_scaled_le_of_not_mem (integerSubring K) p L M a ha hap)
    (carrier_le_of_scaled_le_of_not_mem (integerSubring K) p M L b hb hbp)

/-- Every global vector belongs to the actual completed carrier almost everywhere. -/
theorem eventually_mem_carrier (L : Submodule (integerSubring K) V) (hfg : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤) (x : V) :
    ∀ᶠ p : HeightOneSpectrum (integerSubring K) in cofinite,
      inclusion (integerSubring K) p x ∈ carrier (integerSubring K) p L := by
  let M := L ⊔ Submodule.span (integerSubring K) {x}
  have hMfg : M.FG := hfg.sup (Submodule.fg_span_singleton x)
  have hMfull : Submodule.span K (M : Set V) = ⊤ :=
    top_unique (hfull ▸ Submodule.span_mono (show L ≤ M from le_sup_left))
  filter_upwards [carrier_eventually_eq M L hMfg hfg hMfull hfull] with p hp
  rw [← hp]
  exact inclusion_mem (integerSubring K) p M
    ((show Submodule.span (integerSubring K) {x} ≤ M from le_sup_right)
      (Submodule.subset_span (Set.mem_singleton x)))

section Model

variable {F E ι : Type*} [Field F] [AddCommGroup E] [Module F E]
  [Fintype ι] [DecidableEq ι]

/-- Pairing with one member of an orthogonal basis reads its corresponding coordinate. -/
theorem pairing_basis (B : LinearMap.BilinForm F E) (b : Module.Basis ι F E)
    (horth : ∀ i j, i ≠ j → B (b i) (b j) = 0) (x : E) (i : ι) :
    B x (b i) = b.repr x i * B (b i) (b i) := by
  calc
    B x (b i) = B (∑ j, b.repr x j • b j) (b i) := by rw [b.sum_repr]
    _ = ∑ j, b.repr x j * B (b j) (b i) := by
      simp only [LinearMap.BilinForm.sum_left, LinearMap.BilinForm.smul_left]
    _ = b.repr x i * B (b i) (b i) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [horth j i hji, mul_zero]
      · simp

/-- Unit diagonal coefficients make the full integral basis model self-dual. -/
theorem model_selfDual (S : Subring F) (B : LinearMap.BilinForm F E)
    (b : Module.Basis ι F E) (horth : ∀ i j, i ≠ j → B (b i) (b j) = 0)
    (hne : ∀ i, B (b i) (b i) ≠ 0) (hint : ∀ i, B (b i) (b i) ∈ S)
    (hinv : ∀ i, (B (b i) (b i))⁻¹ ∈ S) :
    SelfDual S B (IntegralMatrix.model S b) := by
  intro x
  constructor
  · intro hx y hy
    have hxi := (IntegralMatrix.mem_model_iff S b x).mp hx
    have hbase (i : ι) : B x (b i) ∈ S := by
      rw [pairing_basis B b horth]
      exact S.mul_mem (hxi i) (hint i)
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hbase i
    | zero => simpa only [map_zero] using S.zero_mem
    | add y z _ _ hy hz => simpa only [map_add] using S.add_mem hy hz
    | smul a y _ hy =>
        change B x ((a : F) • y) ∈ S
        rw [map_smul, smul_eq_mul]
        exact S.mul_mem a.property hy
  · intro hx
    apply (IntegralMatrix.mem_model_iff S b x).mpr
    intro i
    have h := hx (b i) (Submodule.subset_span (Set.mem_range_self i))
    rw [pairing_basis B b horth, mul_comm] at h
    exact (QuadraticValueNormalization.mul_mem_iff S _ (hne i) (hint i) (hinv i) _).mp h

end Model

variable [Invertible (2 : K)] [FiniteDimensional K V]

/-- The half-polar pairing of included vectors is the actual completed scalar image. -/
theorem halfPolar_inclusion (p : HeightOneSpectrum (integerSubring K))
    (Q : QuadraticForm K V) (x y : V) :
    halfPolar (form (integerSubring K) p Q)
      (inclusion (integerSubring K) p x) (inclusion (integerSubring K) p y) =
      algebraMap K (LocalField (integerSubring K) p) (halfPolar Q x y) := by
  change (2 : LocalField (integerSubring K) p)⁻¹ *
      (form (integerSubring K) p Q).polarBilin
        (inclusion (integerSubring K) p x) (inclusion (integerSubring K) p y) =
    algebraMap K (LocalField (integerSubring K) p) ((2 : K)⁻¹ * Q.polarBilin x y)
  rw [LocalIntegralUniversality.polar_inclusion]
  simp only [map_mul, map_inv₀, map_ofNat]

set_option backward.isDefEq.respectTransparency false in
/-- Every regular finite full number-field module is self-dual at almost every completion. -/
theorem eventually_selfDual (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (L : Submodule (integerSubring K) V) (hfg : L.FG)
    (hfull : Submodule.span K (L : Set V) = ⊤) :
    ∀ᶠ p : HeightOneSpectrum (integerSubring K) in cofinite,
      SelfDual (LocalRing (integerSubring K) p) (halfPolar (form (integerSubring K) p Q))
        (carrier (integerSubring K) p L) := by
  classical
  let q := SpinorBridge.quadraticSpace Q hQ
  let b := q.fieldOrthogonalFinBasis
  let A := IntegralMatrix.model (integerSubring K) b
  have hAfg : A.FG := Submodule.fg_span (Set.finite_range b)
  have hAfull : Submodule.span K (A : Set V) = ⊤ := by
    change Submodule.span K (Submodule.span (integerSubring K) (Set.range b) : Set V) = ⊤
    rw [Submodule.span_span_of_tower, b.span_eq]
  have hne (i : Fin (Module.finrank K V)) : Q (b i) ≠ 0 := by
    simpa only [Bong.QuadraticSpace.fieldDiagonalCoefficients, q,
      SpinorBridge.quadraticSpace_quadratic] using q.fieldDiagonalCoefficients_ne_zero i
  have hu : ∀ᶠ p : HeightOneSpectrum (integerSubring K) in cofinite,
      ∀ i, p.valuation K (Q (b i)) = 1 := by
    apply eventually_all.mpr
    intro i
    exact eventually_cofinite.mpr (CofiniteLocalIsotropy.finite_nonunit_valuations _ (hne i))
  filter_upwards [carrier_eventually_eq L A hfg hAfg hfull hAfull, hu] with p hp hpu
  rw [hp, IntegralMatrix.carrier_model_eq]
  let F := LocalField (integerSubring K) p
  let S := LocalRing (integerSubring K) p
  let P := form (integerSubring K) p Q
  let bF := b.baseChange F
  have hbF (i : Fin (Module.finrank K V)) : bF i = inclusion (integerSubring K) p (b i) := by
    simp only [bF, Module.Basis.baseChange_apply, inclusion, TensorProduct.mk_apply]
  have hdiag (i : Fin (Module.finrank K V)) : halfPolar P (bF i) (bF i) =
      algebraMap K F (Q (b i)) := by
    rw [hbF, halfPolar_inclusion, halfPolar_self]
  apply model_selfDual S (halfPolar P) bF
  · intro i j hij
    rw [hbF, hbF, halfPolar_inclusion]
    have h := q.fieldOrthogonalFinBasis_isOrtho hij
    change halfPolar Q (b i) (b j) = 0 at h
    rw [h, map_zero]
  · intro i
    rw [hdiag]
    exact (map_ne_zero _).mpr (hne i)
  · intro i
    rw [hdiag]
    exact (QuadraticValueNormalization.local_unit_membership _ p (hpu i)).1
  · intro i
    rw [hdiag, ← map_inv₀]
    exact (QuadraticValueNormalization.local_unit_membership _ p (hpu i)).2

end NormEuclidean.CofiniteSelfDual
