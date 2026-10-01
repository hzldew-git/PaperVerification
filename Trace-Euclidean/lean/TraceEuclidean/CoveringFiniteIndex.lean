import TraceEuclidean.CoveringShortBasis
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# Finite-index consequences of short lattice bases

This file supplies the group-theoretic and Euclidean determinant steps used in the direct
fixed-field finiteness reduction.  A bounded real basis contained in a full integer lattice
generates a sublattice whose relative index is explicitly bounded.  A factorial of any natural
index bound annihilates the quotient, and only finitely many submodules can contain the resulting
multiple of a fixed free finite module.

The determinant estimate below is the elementary entrywise bound
`|det A| ≤ (card ι)! * B^(card ι)`.  This is weaker than Hadamard's sharp inequality, but its
constants are completely explicit and it requires no additional analytic input.
-/

namespace TraceEuclidean

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

/-! ## Finite residue-module codes -/

/-- The integer submodule consisting of the `m`-fold multiples of an additive group. -/
def nsmulRange (M : Type*) [AddCommGroup M] (m : ℕ) : Submodule ℤ M :=
  (nsmulAddMonoidHom (α := M) m).range.toIntSubmodule

@[simp]
theorem mem_nsmulRange_iff {M : Type*} [AddCommGroup M] (m : ℕ) (x : M) :
    x ∈ nsmulRange M m ↔ ∃ y : M, m • y = x := by
  rfl

/-- The image of an ambient integer submodule under multiplication by `m`. -/
def nsmulImage {E : Type*} [AddCommGroup E] (m : ℕ)
    (S : Submodule ℤ E) : Submodule ℤ E :=
  S.map (DistribSMul.toLinearMap ℤ E m)

@[simp]
theorem mem_nsmulImage_iff {E : Type*} [AddCommGroup E]
    (m : ℕ) (S : Submodule ℤ E) (x : E) :
    x ∈ nsmulImage m S ↔ ∃ y ∈ S, m • y = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

/--
For a fixed free finite `ℤ`-module, there are only finitely many submodules containing all
`m`-fold multiples, provided `m` is positive.  Equivalently, these submodules are pulled back
from submodules of the finite quotient `M / mM`.
-/
theorem finite_submodules_containing_nsmulRange
    (M : Type*) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (m : ℕ) (hm : 0 < m) :
    (Set.Ici (nsmulRange M m)).Finite := by
  let H : AddSubgroup M := (nsmulAddMonoidHom (α := M) m).range
  have hindex : H.index = m ^ Module.finrank ℤ M := by
    simpa [H] using AddSubgroup.index_range_nsmul M m
  have hindex0 : H.index ≠ 0 := by
    rw [hindex]
    exact pow_ne_zero _ (Nat.ne_of_gt hm)
  letI : H.FiniteIndex := AddSubgroup.finiteIndex_iff.mpr hindex0
  haveI hquot : Finite (M ⧸ H) :=
    AddSubgroup.finite_quotient_of_finiteIndex
  let p : Submodule ℤ M := nsmulRange M m
  haveI : Finite (M ⧸ p) := by
    rw [show p = H.toIntSubmodule by rfl]
    exact hquot
  haveI : Finite (Submodule ℤ (M ⧸ p)) := by infer_instance
  haveI : Finite (Set.Ici p) :=
    Finite.of_equiv (Submodule ℤ (M ⧸ p))
      (Submodule.comapMkQRelIso p).toEquiv
  change (Set.Ici p).Finite
  exact Set.toFinite (Set.Ici p)

/-! ## Relative index and quotient annihilation -/

/-- Two full real lattices related by inclusion have strictly positive relative index. -/
theorem relIndex_pos_of_zlattice_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (S L : Submodule ℤ E) [DiscreteTopology S] [IsZLattice ℝ S]
    [DiscreteTopology L] [IsZLattice ℝ L] (hSL : S ≤ L) :
    0 < S.toAddSubgroup.relIndex L.toAddSubgroup := by
  have hr := ZLattice.covolume_div_covolume_eq_relIndex' S L hSL
  have hreal :
      (0 : ℝ) < (S.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) := by
    rw [← hr]
    exact div_pos (ZLattice.covolume_pos S volume)
      (ZLattice.covolume_pos L volume)
  exact_mod_cast hreal

/--
If the relative index is positive and at most `N`, then `N!` annihilates the quotient: every
`N!`-fold multiple of an element of the larger subgroup belongs to the smaller subgroup.
-/
theorem factorial_nsmul_mem_of_relIndex_le
    {E : Type*} [AddCommGroup E] (S L : Submodule ℤ E) (N : ℕ)
    (hpos : 0 < S.toAddSubgroup.relIndex L.toAddSubgroup)
    (hindex : S.toAddSubgroup.relIndex L.toAddSubgroup ≤ N)
    {x : E} (hx : x ∈ L) :
    N.factorial • x ∈ S := by
  let k := S.toAddSubgroup.relIndex L.toAddSubgroup
  have hkdiv : k ∣ N.factorial := Nat.dvd_factorial hpos hindex
  obtain ⟨q, hq⟩ := hkdiv
  have hkx : k • x ∈ S :=
    S.toAddSubgroup.nsmul_relIndex_mem (K := L.toAddSubgroup) hx
  rw [hq, mul_nsmul]
  exact S.toAddSubgroup.nsmul_mem hkx q

/-- The preceding annihilation result specialized to an inclusion of full real lattices. -/
theorem factorial_nsmul_mem_of_zlattice_relIndex_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (S L : Submodule ℤ E) [DiscreteTopology S] [IsZLattice ℝ S]
    [DiscreteTopology L] [IsZLattice ℝ L] (hSL : S ≤ L) (N : ℕ)
    (hindex : S.toAddSubgroup.relIndex L.toAddSubgroup ≤ N)
    {x : E} (hx : x ∈ L) :
    N.factorial • x ∈ S :=
  factorial_nsmul_mem_of_relIndex_le S L N
    (relIndex_pos_of_zlattice_le S L hSL) hindex hx

/--
Inside an ambient group, the interval of submodules between `mS` and a fixed free finite
submodule `S` is finite.  Pulling an intermediate submodule back to the subtype `S` reduces this
to `finite_submodules_containing_nsmulRange`.
-/
theorem finite_submodules_between_nsmulImage_and_self
    {E : Type*} [AddCommGroup E] (S : Submodule ℤ E)
    [Module.Free ℤ S] [Module.Finite ℤ S]
    (m : ℕ) (hm : 0 < m) :
    {U : Submodule ℤ E | nsmulImage m S ≤ U ∧ U ≤ S}.Finite := by
  let A : Set (Submodule ℤ E) :=
    {U : Submodule ℤ E | nsmulImage m S ≤ U ∧ U ≤ S}
  let f : Submodule ℤ E → Submodule ℤ S :=
    fun U ↦ U.comap S.subtype
  have htarget : f '' A ⊆ Set.Ici (nsmulRange S m) := by
    rintro V ⟨U, hU, rfl⟩
    intro s hs
    rw [mem_nsmulRange_iff] at hs
    obtain ⟨y, rfl⟩ := hs
    change m • (y : E) ∈ U
    exact hU.1 (by
      rw [mem_nsmulImage_iff]
      exact ⟨y, y.property, rfl⟩)
  have himage : (f '' A).Finite :=
    (finite_submodules_containing_nsmulRange S m hm).subset htarget
  have hinj : Set.InjOn f A := by
    intro U hU V hV hEq
    have hmap := congrArg (Submodule.map S.subtype) hEq
    simpa [f, Submodule.map_comap_subtype, inf_eq_right.mpr hU.2,
      inf_eq_right.mpr hV.2] using hmap
  exact Set.Finite.of_finite_image himage hinj

/--
For a fixed free finite submodule `S` of a torsion-free abelian group, there are only finitely
many overmodules containing `S` with positive relative index at most `N`.  The injective code is
`L ↦ N! L`, which lies in the finite interval `[N! S, S]`.
-/
theorem finite_overlattices_of_relIndex_le
    {E : Type*} [AddCommGroup E] [Module.IsTorsionFree ℤ E]
    (S : Submodule ℤ E) [Module.Free ℤ S] [Module.Finite ℤ S]
    (N : ℕ) :
    {L : Submodule ℤ E |
      S ≤ L ∧ 0 < S.toAddSubgroup.relIndex L.toAddSubgroup ∧
        S.toAddSubgroup.relIndex L.toAddSubgroup ≤ N}.Finite := by
  let A : Set (Submodule ℤ E) :=
    {L : Submodule ℤ E |
      S ≤ L ∧ 0 < S.toAddSubgroup.relIndex L.toAddSubgroup ∧
        S.toAddSubgroup.relIndex L.toAddSubgroup ≤ N}
  let B : Set (Submodule ℤ E) :=
    {U : Submodule ℤ E |
      nsmulImage N.factorial S ≤ U ∧ U ≤ S}
  let f : Submodule ℤ E → Submodule ℤ E :=
    fun L ↦ nsmulImage N.factorial L
  have htarget : f '' A ⊆ B := by
    rintro U ⟨L, hL, rfl⟩
    refine ⟨Submodule.map_mono hL.1, ?_⟩
    intro x hx
    rw [mem_nsmulImage_iff] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact factorial_nsmul_mem_of_relIndex_le S L N hL.2.1 hL.2.2 hy
  have himage : (f '' A).Finite :=
    (finite_submodules_between_nsmulImage_and_self S N.factorial
      (Nat.factorial_pos N)).subset htarget
  have hinjective : Function.Injective f := by
    exact Submodule.map_injective_of_injective
      (AddSubgroup.distribSMulToLinearMap_injective_of_isTorsionFree
        (Nat.factorial_ne_zero N))
  exact Set.Finite.of_finite_image himage hinjective.injOn

/-! ## The determinant and covolume estimate -/

/--
A real basis contained in a full lattice and bounded by `B` generates a sublattice of index at
most `(card ι)! * B^(card ι) / δ`, whenever `δ` is a positive lower bound for the covolume
of the original lattice.
-/
theorem relIndex_span_basis_le_of_covolume_lower
    {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℝ (EuclideanSpace ℝ ι))
    (B δ : ℝ) (hB0 : 0 ≤ B) (hδ : 0 < δ)
    (hbmem : ∀ i, b i ∈ L) (hbnorm : ∀ i, ‖b i‖ ≤ B)
    (hcovLower : δ ≤ ZLattice.covolume L) :
    (((Submodule.span ℤ (Set.range b)).toAddSubgroup.relIndex
      L.toAddSubgroup : ℕ) : ℝ) ≤
      (Nat.factorial (Fintype.card ι) : ℝ) * B ^ Fintype.card ι / δ := by
  classical
  let S : Submodule ℤ (EuclideanSpace ℝ ι) :=
    Submodule.span ℤ (Set.range b)
  letI : DiscreteTopology S := by
    dsimp [S]
    infer_instance
  letI : IsZLattice ℝ S := by
    dsimp [S]
    infer_instance
  have hSL : S ≤ L := by
    dsimp [S]
    exact Submodule.span_le.mpr (by
      rintro x ⟨i, rfl⟩
      exact hbmem i)
  let b0 : Module.Basis ι ℝ (EuclideanSpace ℝ ι) :=
    (EuclideanSpace.basisFun ι ℝ).toBasis
  have hfund : volume.real (ZSpan.fundamentalDomain b0) = 1 := by
    calc
      volume.real (ZSpan.fundamentalDomain b0) =
          volume.real (parallelepiped b0) :=
        MeasureTheory.measureReal_congr
          (ZSpan.fundamentalDomain_ae_parallelepiped b0 volume)
      _ = ENNReal.toReal (volume (parallelepiped b0)) := rfl
      _ = ENNReal.toReal 1 := by
        rw [show volume (parallelepiped b0) = 1 by
          simpa [b0] using (EuclideanSpace.basisFun ι ℝ).volume_parallelepiped]
      _ = 1 := ENNReal.toReal_one
  have hdet : |b0.det b| ≤
      (Nat.factorial (Fintype.card ι) : ℝ) * B ^ Fintype.card ι := by
    rw [Module.Basis.det_apply]
    have hm := Matrix.det_le (abv := AbsoluteValue.abs)
      (A := b0.toMatrix b) (x := B) (fun i j ↦
        (PiLp.norm_apply_le (p := 2) (b j) i).trans (hbnorm j))
    simpa [b0, Module.Basis.toMatrix_apply,
      EuclideanSpace.basisFun_repr, nsmul_eq_mul] using hm
  have hcovS : ZLattice.covolume S ≤
      (Nat.factorial (Fintype.card ι) : ℝ) * B ^ Fintype.card ι := by
    rw [ZLattice.covolume_eq_det_mul_measureReal S volume
      (b.restrictScalars ℤ) b0, hfund, mul_one]
    have hfamily : (Subtype.val ∘ ⇑(b.restrictScalars ℤ)) = b := by
      funext i
      exact Module.Basis.restrictScalars_apply ℤ b i
    rw [hfamily]
    exact hdet
  have hC :
      0 ≤ (Nat.factorial (Fintype.card ι) : ℝ) * B ^ Fintype.card ι := by
    positivity
  change ((S.toAddSubgroup.relIndex L.toAddSubgroup : ℕ) : ℝ) ≤ _
  rw [← ZLattice.covolume_div_covolume_eq_relIndex' S L hSL]
  calc
    ZLattice.covolume S / ZLattice.covolume L ≤
        ((Nat.factorial (Fintype.card ι) : ℝ) * B ^ Fintype.card ι) /
          ZLattice.covolume L :=
      (div_le_div_iff_of_pos_right (ZLattice.covolume_pos L volume)).2 hcovS
    _ ≤ (Nat.factorial (Fintype.card ι) : ℝ) * B ^ Fintype.card ι / δ :=
      div_le_div_of_nonneg_left hC hδ hcovLower

/-- The determinant bound stated for a full-size linearly independent family in `L`. -/
theorem relIndex_span_linearIndependent_le_of_covolume_lower
    {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (v : ι → L) (B δ : ℝ) (hB0 : 0 ≤ B) (hδ : 0 < δ)
    (hvind : LinearIndependent ℝ
      (fun i ↦ (v i : EuclideanSpace ℝ ι)))
    (hvnorm : ∀ i, ‖(v i : EuclideanSpace ℝ ι)‖ ≤ B)
    (hcovLower : δ ≤ ZLattice.covolume L) :
    (((Submodule.span ℤ
      (Set.range fun i ↦ (v i : EuclideanSpace ℝ ι))).toAddSubgroup.relIndex
        L.toAddSubgroup : ℕ) : ℝ) ≤
      (Nat.factorial (Fintype.card ι) : ℝ) * B ^ Fintype.card ι / δ := by
  classical
  let w : ι → EuclideanSpace ℝ ι :=
    fun i ↦ (v i : EuclideanSpace ℝ ι)
  let b : Module.Basis ι ℝ (EuclideanSpace ℝ ι) :=
    basisOfLinearIndependentOfCardEqFinrank' w hvind
      (finrank_euclideanSpace (𝕜 := ℝ) (ι := ι)).symm
  have hb : (b : ι → EuclideanSpace ℝ ι) = w := by
    exact coe_basisOfLinearIndependentOfCardEqFinrank' w hvind _
  change (((Submodule.span ℤ (Set.range w)).toAddSubgroup.relIndex
      L.toAddSubgroup : ℕ) : ℝ) ≤ _
  rw [← hb]
  apply relIndex_span_basis_le_of_covolume_lower L b B δ hB0 hδ
  · intro i
    rw [hb]
    exact (v i).property
  · intro i
    rw [hb]
    exact hvnorm i
  · exact hcovLower

/--
Squared form of the index bound, convenient when arithmetic supplies a lower bound for the Gram
determinant, hence for the square of the covolume.
-/
theorem relIndex_span_linearIndependent_sq_le_of_covolume_sq_lower
    {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (v : ι → L) (B D : ℝ) (hB0 : 0 ≤ B) (hD : 0 < D)
    (hvind : LinearIndependent ℝ
      (fun i ↦ (v i : EuclideanSpace ℝ ι)))
    (hvnorm : ∀ i, ‖(v i : EuclideanSpace ℝ ι)‖ ≤ B)
    (hcovSqLower : D ≤ ZLattice.covolume L ^ (2 : ℕ)) :
    (((Submodule.span ℤ
      (Set.range fun i ↦ (v i : EuclideanSpace ℝ ι))).toAddSubgroup.relIndex
        L.toAddSubgroup : ℕ) : ℝ) ^ (2 : ℕ) ≤
      ((Nat.factorial (Fintype.card ι) : ℝ) *
          B ^ Fintype.card ι) ^ (2 : ℕ) / D := by
  let C : ℝ :=
    (Nat.factorial (Fintype.card ι) : ℝ) * B ^ Fintype.card ι
  have hroot : Real.sqrt D ≤ ZLattice.covolume L :=
    Real.sqrt_le_iff.mpr
      ⟨(ZLattice.covolume_pos L volume).le, hcovSqLower⟩
  have hindex := relIndex_span_linearIndependent_le_of_covolume_lower
    L v B (Real.sqrt D) hB0 (Real.sqrt_pos.mpr hD) hvind hvnorm hroot
  have hindex0 :
      0 ≤ (((Submodule.span ℤ
        (Set.range fun i ↦ (v i : EuclideanSpace ℝ ι))).toAddSubgroup.relIndex
          L.toAddSubgroup : ℕ) : ℝ) := by positivity
  have hsquare := pow_le_pow_left₀ hindex0 hindex 2
  change _ ≤ C ^ (2 : ℕ) / D
  calc
    _ ≤ (C / Real.sqrt D) ^ (2 : ℕ) := by
      simpa [C] using hsquare
    _ = C ^ (2 : ℕ) / D := by
      rw [div_pow, Real.sq_sqrt hD.le]

/-! ## Arithmetic lower bounds for the classic and scale-two branches -/

/-- An integer-valued covolume square forces the sharp lower bound `covolume ≥ 1`. -/
theorem one_le_covolume_of_covolume_sq_eq_int
    {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (z : ℤ) (hInt : ZLattice.covolume L ^ (2 : ℕ) = (z : ℝ)) :
    1 ≤ ZLattice.covolume L := by
  have hc : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
  have hzposR : (0 : ℝ) < (z : ℝ) := by
    rw [← hInt]
    positivity
  have hzpos : (0 : ℤ) < z := by exact_mod_cast hzposR
  have hzone : (1 : ℝ) ≤ (z : ℝ) := by
    exact_mod_cast (Int.add_one_le_iff.mpr hzpos)
  rw [← hInt] at hzone
  nlinarith

/--
If the scale-two Gram determinant in dimension `N` is an integer, then the original covolume
square is at least `2⁻ᴺ`, written as the inverse of `2^N`.
-/
theorem inv_two_pow_le_covolume_sq_of_scaled_covolume_sq_eq_int
    {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (N : ℕ) (z : ℤ)
    (hInt : (2 : ℝ) ^ N * ZLattice.covolume L ^ (2 : ℕ) = (z : ℝ)) :
    ((2 : ℝ) ^ N)⁻¹ ≤ ZLattice.covolume L ^ (2 : ℕ) := by
  have hp : 0 < (2 : ℝ) ^ N := by positivity
  have hc : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
  have hzposR : (0 : ℝ) < (z : ℝ) := by
    rw [← hInt]
    exact mul_pos hp (pow_pos hc 2)
  have hzpos : (0 : ℤ) < z := by exact_mod_cast hzposR
  have hzone : (1 : ℝ) ≤ (z : ℝ) := by
    exact_mod_cast (Int.add_one_le_iff.mpr hzpos)
  rw [← hInt] at hzone
  rw [← one_div]
  exact (div_le_iff₀ hp).2 (by simpa [mul_comm] using hzone)

/-- Classic-integral specialization of the relative-index estimate. -/
theorem relIndex_span_linearIndependent_le_of_covolume_sq_eq_int
    {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (v : ι → L) (B : ℝ) (hB0 : 0 ≤ B)
    (hvind : LinearIndependent ℝ
      (fun i ↦ (v i : EuclideanSpace ℝ ι)))
    (hvnorm : ∀ i, ‖(v i : EuclideanSpace ℝ ι)‖ ≤ B)
    (z : ℤ) (hInt : ZLattice.covolume L ^ (2 : ℕ) = (z : ℝ)) :
    (((Submodule.span ℤ
      (Set.range fun i ↦ (v i : EuclideanSpace ℝ ι))).toAddSubgroup.relIndex
        L.toAddSubgroup : ℕ) : ℝ) ≤
      (Nat.factorial (Fintype.card ι) : ℝ) * B ^ Fintype.card ι := by
  simpa using relIndex_span_linearIndependent_le_of_covolume_lower
    L v B 1 hB0 zero_lt_one hvind hvnorm
      (one_le_covolume_of_covolume_sq_eq_int L z hInt)

/--
Scale-two specialization.  The squared relative index is bounded by the square of the elementary
determinant bound times `2^N`.
-/
theorem relIndex_span_linearIndependent_sq_le_of_scaled_covolume_sq_eq_int
    {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (v : ι → L) (B : ℝ) (hB0 : 0 ≤ B)
    (hvind : LinearIndependent ℝ
      (fun i ↦ (v i : EuclideanSpace ℝ ι)))
    (hvnorm : ∀ i, ‖(v i : EuclideanSpace ℝ ι)‖ ≤ B)
    (N : ℕ) (z : ℤ)
    (hInt : (2 : ℝ) ^ N * ZLattice.covolume L ^ (2 : ℕ) = (z : ℝ)) :
    (((Submodule.span ℤ
      (Set.range fun i ↦ (v i : EuclideanSpace ℝ ι))).toAddSubgroup.relIndex
        L.toAddSubgroup : ℕ) : ℝ) ^ (2 : ℕ) ≤
      ((Nat.factorial (Fintype.card ι) : ℝ) *
          B ^ Fintype.card ι) ^ (2 : ℕ) * (2 : ℝ) ^ N := by
  have h := relIndex_span_linearIndependent_sq_le_of_covolume_sq_lower
    L v B (((2 : ℝ) ^ N)⁻¹) hB0 (by positivity) hvind hvnorm
      (inv_two_pow_le_covolume_sq_of_scaled_covolume_sq_eq_int L N z hInt)
  simpa [div_inv_eq_mul] using h

/-! ## Covering-to-index composition -/

/--
A covering bound and a covolume lower bound produce a bounded independent lattice family and an
explicit index estimate for the sublattice that it spans.
-/
theorem exists_short_span_relIndex_le_of_cover
    {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (EuclideanSpace ℝ ι))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hcover : ∀ x : EuclideanSpace ℝ ι,
      ∃ l : L, ‖x - (l : EuclideanSpace ℝ ι)‖ < R)
    (hcovLower : δ ≤ ZLattice.covolume L) :
    ∃ v : ι → L,
      LinearIndependent ℝ (fun i ↦ (v i : EuclideanSpace ℝ ι)) ∧
      (∀ i, ‖(v i : EuclideanSpace ℝ ι)‖ <
        ((Fintype.card ι : ℝ) + 1) * R + 1) ∧
      (((Submodule.span ℤ
        (Set.range fun i ↦ (v i : EuclideanSpace ℝ ι))).toAddSubgroup.relIndex
          L.toAddSubgroup : ℕ) : ℝ) ≤
        (Nat.factorial (Fintype.card ι) : ℝ) *
          (((Fintype.card ι : ℝ) + 1) * R + 1) ^ Fintype.card ι / δ := by
  obtain ⟨v, hvind, hvnorm⟩ :=
    exists_short_linearIndependent_of_cover L R hR hcover
  refine ⟨v, hvind, hvnorm, ?_⟩
  apply relIndex_span_linearIndependent_le_of_covolume_lower
    L v (((Fintype.card ι : ℝ) + 1) * R + 1) δ
  · positivity
  · exact hδ
  · exact hvind
  · intro i
    exact (hvnorm i).le
  · exact hcovLower

end

end TraceEuclidean
