import NormEuclidean.ChapterX.IntegralBiduality
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Basis.SMul

/-!
# Intrinsic volume ideals

The full-rank mixed pairing determinants generate the volume ideal. Using
two independent families avoids division by two in the integer ring and
does not require an integral basis. The quadratic normalization is the
half-polar pairing, with `B(x,x) = Q(x)`.
-/

noncomputable section

namespace NormEuclidean.IntegralVolume

open Matrix Module
open scoped Pointwise nonZeroDivisors

variable {K V W : Type*} [Field K] [NumberField K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The mixed pairing matrix of two independent vector families. -/
def pairingMatrix (B : LinearMap.BilinForm K V) {n : ℕ} (x y : Fin n → V) :
    Matrix (Fin n) (Fin n) K := fun i j ↦ B (x i) (y j)

/-- Intrinsic determinant generators; the degree is the ambient rank in
the lattice volume application. No integral basis is selected. -/
def volumeSubmodule (B : LinearMap.BilinForm K V) (n : ℕ)
    (L : Submodule (integerSubring K) V) : Submodule (integerSubring K) K :=
  Submodule.span (integerSubring K) (Set.range fun p : (Fin n → L) × (Fin n → L) ↦
    (pairingMatrix B (fun i ↦ (p.1 i : V)) (fun j ↦ (p.2 j : V))).det)

/-- Every actual mixed pairing determinant is a volume generator. -/
theorem det_mem_volumeSubmodule (B : LinearMap.BilinForm K V) (n : ℕ)
    (L : Submodule (integerSubring K) V) (x y : Fin n → V)
    (hx : ∀ i, x i ∈ L) (hy : ∀ j, y j ∈ L) :
    (pairingMatrix B x y).det ∈ volumeSubmodule B n L :=
  Submodule.subset_span ⟨(fun i ↦ ⟨x i, hx i⟩, fun j ↦ ⟨y j, hy j⟩), rfl⟩

/-- Inclusion of modules gives inclusion of their intrinsic volume ideals. -/
theorem volumeSubmodule_mono (B : LinearMap.BilinForm K V) (n : ℕ)
    {L M : Submodule (integerSubring K) V} (h : L ≤ M) :
    volumeSubmodule B n L ≤ volumeSubmodule B n M := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  exact det_mem_volumeSubmodule B n M _ _ (fun i ↦ h (p.1 i).2) (fun j ↦ h (p.2 j).2)

/-- The empty determinant has volume one, including on the zero-rank boundary. -/
theorem volumeSubmodule_degree_zero (B : LinearMap.BilinForm K V)
    (L : Submodule (integerSubring K) V) :
    volumeSubmodule B 0 L = Submodule.span (integerSubring K) {(1 : K)} := by
  simp only [volumeSubmodule, Matrix.det_isEmpty, Set.range_const]

/-- Finite generation supplies one denominator for all pairing determinants.
Fullness and regularity are not needed for fractionality. -/
theorem volumeSubmodule_isFractional (B : LinearMap.BilinForm K V) (n : ℕ)
    (L : Submodule (integerSubring K) V) (hLfg : L.FG) :
    IsFractional (integerSubring K)⁰ (volumeSubmodule B n L) := by
  obtain ⟨d, hd0, hd⟩ := exists_lattice_denominator L (B.dualSubmodule L) hLfg
    (IntegralBiduality.dual_full B L hLfg)
  rw [volumeSubmodule, FractionalIdeal.isFractional_span_iff]
  refine ⟨d ^ n, mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ hd0), ?_⟩
  rintro _ ⟨p, rfl⟩
  have hint (i j : Fin n) : ∃ a : integerSubring K,
      algebraMap (integerSubring K) K a = (d : K) * B (p.1 i) (p.2 j) := by
    have h := hd (p.1 i) (p.1 i).2 (p.2 j) (p.2 j).2
    rw [LinearMap.BilinForm.smul_left] at h
    exact Submodule.mem_one.mp h
  choose a ha using hint
  let A : Matrix (Fin n) (Fin n) (integerSubring K) := a
  refine ⟨Matrix.det A, ?_⟩
  have hmap : Matrix.map A (algebraMap (integerSubring K) K) =
      (d : K) • pairingMatrix B (fun i ↦ (p.1 i : V)) (fun j ↦ (p.2 j : V)) := by
    ext i j
    exact ha i j
  change algebraMap (integerSubring K) K A.det =
    d ^ n • (pairingMatrix B (fun i ↦ (p.1 i : V)) (fun j ↦ (p.2 j : V))).det
  rw [RingHom.map_det]
  change (Matrix.map A (algebraMap (integerSubring K) K)).det = _
  rw [hmap, Matrix.det_smul]
  simp only [Fintype.card_fin, Subring.smul_def, Subring.coe_pow, smul_eq_mul]

/-- The actual fractional volume ideal of a finite module, in degree `n`. -/
def volumeIdeal (B : LinearMap.BilinForm K V) (n : ℕ)
    (L : Submodule (integerSubring K) V) (hLfg : L.FG) :
    FractionalIdeal (integerSubring K)⁰ K :=
  ⟨volumeSubmodule B n L, volumeSubmodule_isFractional B n L hLfg⟩

@[simp]
theorem coe_volumeIdeal (B : LinearMap.BilinForm K V) (n : ℕ)
    (L : Submodule (integerSubring K) V) (hLfg : L.FG) :
    (volumeIdeal B n L hLfg : Submodule (integerSubring K) K) = volumeSubmodule B n L := rfl

/-- Volume ideal comparison for finite modules. -/
theorem volumeIdeal_mono (B : LinearMap.BilinForm K V) (n : ℕ)
    {L M : Submodule (integerSubring K) V} (hLfg : L.FG) (hMfg : M.FG) (h : L ≤ M) :
    volumeIdeal B n L hLfg ≤ volumeIdeal B n M hMfg :=
  volumeSubmodule_mono B n h

/-- An integral bilinear pairing gives an integral volume ideal in every degree. -/
theorem volumeIdeal_le_one (B : LinearMap.BilinForm K V) (n : ℕ)
    (L : Submodule (integerSubring K) V) (hLfg : L.FG)
    (hB : ∀ x ∈ L, ∀ y ∈ L, B x y ∈ (1 : Submodule (integerSubring K) K)) :
    volumeIdeal B n L hLfg ≤ 1 := by
  change volumeSubmodule B n L ≤
    ((1 : FractionalIdeal (integerSubring K)⁰ K) : Submodule (integerSubring K) K)
  rw [FractionalIdeal.coe_one]
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  choose a ha using fun i j : Fin n ↦ Submodule.mem_one.mp
    (hB (p.1 i) (p.1 i).2 (p.2 j) (p.2 j).2)
  let A : Matrix (Fin n) (Fin n) (integerSubring K) := a
  apply Submodule.mem_one.mpr
  refine ⟨Matrix.det A, ?_⟩
  change algebraMap (integerSubring K) K A.det =
    (pairingMatrix B (fun i ↦ (p.1 i : V)) (fun j ↦ (p.2 j : V))).det
  rw [RingHom.map_det]
  congr 1
  ext i j
  exact ha i j

/-- A linear transport scaling the pairing by `c` scales volume by `c^n`.
All families in the image module are lifted to actual source families. -/
theorem volumeSubmodule_map (B : LinearMap.BilinForm K V)
    (C : LinearMap.BilinForm K W) (n : ℕ) (L : Submodule (integerSubring K) V)
    (f : V →ₗ[K] W) (c : K) (hf : ∀ x y, C (f x) (f y) = c * B x y) :
    volumeSubmodule C n (L.map (f.restrictScalars (integerSubring K))) =
      c ^ n • volumeSubmodule B n L := by
  classical
  rw [volumeSubmodule, volumeSubmodule, Submodule.smul_span, Set.smul_set_range]
  congr 1
  ext t
  constructor
  · rintro ⟨p, rfl⟩
    choose x hx hfx using fun i ↦ (p.1 i).2
    choose y hy hfy using fun j ↦ (p.2 j).2
    refine ⟨(fun i ↦ ⟨x i, hx i⟩, fun j ↦ ⟨y j, hy j⟩), ?_⟩
    have hmat : pairingMatrix C (fun i ↦ (p.1 i : W)) (fun j ↦ (p.2 j : W)) =
        c • pairingMatrix B x y := by
      ext i j
      change C (p.1 i) (p.2 j) = c * B (x i) (y j)
      rw [← hfx i, ← hfy j]
      exact hf _ _
    change c ^ n • (pairingMatrix B x y).det =
      (pairingMatrix C (fun i ↦ (p.1 i : W)) (fun j ↦ (p.2 j : W))).det
    rw [hmat, Matrix.det_smul]
    simp only [Fintype.card_fin, smul_eq_mul]
  · rintro ⟨p, rfl⟩
    let x : Fin n → L.map (f.restrictScalars (integerSubring K)) :=
      fun i ↦ ⟨f (p.1 i), ⟨p.1 i, (p.1 i).2, rfl⟩⟩
    let y : Fin n → L.map (f.restrictScalars (integerSubring K)) :=
      fun j ↦ ⟨f (p.2 j), ⟨p.2 j, (p.2 j).2, rfl⟩⟩
    refine ⟨(x, y), ?_⟩
    have hmat : pairingMatrix C (fun i ↦ (x i : W)) (fun j ↦ (y j : W)) =
        c • pairingMatrix B (fun i ↦ (p.1 i : V)) (fun j ↦ (p.2 j : V)) := by
      ext i j
      exact hf _ _
    change (pairingMatrix C (fun i ↦ (x i : W)) (fun j ↦ (y j : W))).det =
      c ^ n • (pairingMatrix B (fun i ↦ (p.1 i : V)) (fun j ↦ (p.2 j : V))).det
    rw [hmat, Matrix.det_smul]
    simp only [Fintype.card_fin, smul_eq_mul]

/-- Ambient pairing-preserving transport leaves the intrinsic volume unchanged. -/
theorem volumeSubmodule_map_isometry (B : LinearMap.BilinForm K V)
    (C : LinearMap.BilinForm K W) (n : ℕ) (L : Submodule (integerSubring K) V)
    (f : V →ₗ[K] W) (hf : ∀ x y, C (f x) (f y) = B x y) :
    volumeSubmodule C n (L.map (f.restrictScalars (integerSubring K))) =
      volumeSubmodule B n L := by
  simpa using volumeSubmodule_map B C n L f 1 (by simpa using hf)

/-- Scalar enlargement of a module scales its volume by the square power. -/
theorem volumeSubmodule_map_scalar (B : LinearMap.BilinForm K V) (n : ℕ)
    (L : Submodule (integerSubring K) V) (a : K) :
    volumeSubmodule B n (L.map ((LinearMap.lsmul K V a).restrictScalars (integerSubring K))) =
      a ^ (2 * n) • volumeSubmodule B n L := by
  have h := volumeSubmodule_map B B n L (LinearMap.lsmul K V a) (a ^ 2) (by
    intro x y
    simp only [LinearMap.lsmul_apply, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right, pow_two]
    ring)
  simpa only [← pow_mul] using h

/-- Multiplying the bilinear form scales the volume by the ambient-rank power. -/
theorem volumeSubmodule_smul_form (B : LinearMap.BilinForm K V) (n : ℕ)
    (L : Submodule (integerSubring K) V) (a : K) :
    volumeSubmodule (a • B) n L = a ^ n • volumeSubmodule B n L := by
  have h := volumeSubmodule_map B (a • B) n L (LinearMap.id : V →ₗ[K] V) a (by
    intro x y
    rfl)
  simpa only [LinearMap.restrictScalars_id, Submodule.map_id] using h

/-- A finite full module on a regular space has nonzero full-rank volume.
Only a field basis is used, and it is cleared into the actual module. -/
theorem volumeSubmodule_ne_bot (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (L : Submodule (integerSubring K) V) (hLfg : L.FG)
    (hL : Submodule.span K (L : Set V) = ⊤) :
    volumeSubmodule B (Module.finrank K V) L ≠ ⊥ := by
  classical
  letI := ModuleGenusPatching.finiteDimensional_of_fg_full (integerSubring K) L hLfg hL
  let b := Module.finBasis K V
  obtain ⟨d, hd0, hd⟩ := exists_common_denominator L hL (Finset.univ.image b)
  have hdK : (d : K) ≠ 0 := by exact_mod_cast hd0
  let b' := b.unitsSMul (fun _ ↦ Units.mk0 (d : K) hdK)
  have hb' (i : Fin (Module.finrank K V)) : b' i ∈ L := by
    simpa only [b', Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0] using
      hd (b i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hmat : pairingMatrix B b' b' = LinearMap.BilinForm.toMatrix b' B := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  have hdet : (pairingMatrix B b' b').det ≠ 0 := by
    rw [hmat]
    exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b').mp hB
  intro hzero
  have hmem := det_mem_volumeSubmodule B (Module.finrank K V) L b' b' hb' hb'
  rw [hzero] at hmem
  exact hdet hmem

/-- The intrinsic full-rank volume is a nonzero fractional ideal. -/
theorem volumeIdeal_ne_zero (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (L : Submodule (integerSubring K) V) (hLfg : L.FG)
    (hL : Submodule.span K (L : Set V) = ⊤) :
    volumeIdeal B (Module.finrank K V) L hLfg ≠ 0 :=
  FractionalIdeal.coeToSubmodule_ne_bot.mp (volumeSubmodule_ne_bot B hB L hLfg hL)

end NormEuclidean.IntegralVolume

namespace NormEuclidean.Lattice

open scoped nonZeroDivisors Pointwise

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V}

/-- O'Meara volume in the half-polar normalization, defined intrinsically on
the actual finite full lattice rather than an integral basis. -/
def volumeIdeal (L : Lattice (integerSubring K) Q) :
    FractionalIdeal (integerSubring K)⁰ K :=
  IntegralVolume.volumeIdeal (halfPolar Q) (Module.finrank K V) L.carrier L.finite

/-- Integral scale implies integral volume, also for nonfree lattices. -/
theorem volumeIdeal_le_one (L : Lattice (integerSubring K) Q) (hs : L.scaleIdeal ≤ 1) :
    L.volumeIdeal ≤ 1 := by
  apply IntegralVolume.volumeIdeal_le_one
  intro x hx y hy
  have h := hs (L.halfPolar_mem_scaleIdeal ⟨x, hx⟩ ⟨y, hy⟩)
  change halfPolar Q x y ∈
    ((1 : FractionalIdeal (integerSubring K)⁰ K) : Submodule (integerSubring K) K) at h
  simpa only [FractionalIdeal.coe_one] using h

/-- The full-rank volume of a regular lattice is nonzero. -/
theorem volumeIdeal_ne_zero [Invertible (2 : K)] (L : Lattice (integerSubring K) Q)
    (hQ : Q.polarBilin.Nondegenerate) : L.volumeIdeal ≠ 0 :=
  IntegralVolume.volumeIdeal_ne_zero (halfPolar Q)
    (SpinorBridge.quadraticSpace Q hQ).nondegenerate L.carrier L.finite L.full

/-- Rescaling the quadratic form multiplies its actual volume by the rank power. -/
theorem volumeIdeal_rescale (L : Lattice (integerSubring K) Q) (a : integerSubring K) :
    (L.rescale a).volumeIdeal = FractionalIdeal.spanSingleton (integerSubring K)⁰
      ((a : K) ^ Module.finrank K V) * L.volumeIdeal := by
  apply FractionalIdeal.coeToSubmodule_injective
  dsimp only
  have hB : halfPolar ((a : K) • Q) = (a : K) • halfPolar Q := by
    ext x y
    exact halfPolar_smul (a : K) Q x y
  change IntegralVolume.volumeSubmodule (halfPolar ((a : K) • Q))
    (Module.finrank K V) L.carrier = _
  rw [hB, IntegralVolume.volumeSubmodule_smul_form, FractionalIdeal.coe_mul,
    FractionalIdeal.coe_spanSingleton, Submodule.span_singleton_mul]
  rfl

/-- Ordinary integral isometry preserves the actual volume ideal. -/
theorem volumeIdeal_eq_of_globallyIsometric (L M : Lattice (integerSubring K) Q)
    (h : GloballyIsometric Q L M) : L.volumeIdeal = M.volumeIdeal := by
  obtain ⟨e⟩ := h
  have hmap : L.carrier.map
      (e.toLinearEquiv.toLinearMap.restrictScalars (integerSubring K)) = M.carrier := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (e.mem_iff x).mpr hx
    · intro hz
      refine ⟨e.toLinearEquiv.symm z, ?_, e.toLinearEquiv.apply_symm_apply z⟩
      apply (e.mem_iff _).mp
      simpa only [LinearEquiv.apply_symm_apply] using hz
  have hB (x y : V) : halfPolar Q (e.toLinearEquiv x) (e.toLinearEquiv y) =
      halfPolar Q x y := by
    simp only [halfPolar_apply, QuadraticMap.polar]
    rw [← e.toLinearEquiv.map_add, e.q_eq, e.q_eq, e.q_eq]
  apply FractionalIdeal.coeToSubmodule_injective
  change IntegralVolume.volumeSubmodule (halfPolar Q) (Module.finrank K V) L.carrier =
    IntegralVolume.volumeSubmodule (halfPolar Q) (Module.finrank K V) M.carrier
  rw [← hmap, IntegralVolume.volumeSubmodule_map_isometry _ _ _ _ _ hB]

end NormEuclidean.Lattice
