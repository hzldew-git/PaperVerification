import NormEuclidean.ChapterX.DeterminantContent
import NormEuclidean.ChapterX.ModulePseudoBasis

/-!
# The actual pseudobasis volume formula

The ambient extension of the module pseudobasis supplies its field basis.
Transporting determinant content proves the book's volume formula for arbitrary
coefficient fractional ideals, without total reality or positive definiteness.
-/

noncomputable section

namespace NormEuclidean.PseudoBasisVolume

open IntegralVolume NumberFieldLatticeModule Module
open scoped NumberField nonZeroDivisors Pointwise

variable {K : Type*} [Field K] [NumberField K]

local instance : Module.Free ℤ (integerSubring K) :=
  inferInstanceAs (Module.Free ℤ (𝓞 K))

local instance : Module.Finite ℤ (integerSubring K) :=
  inferInstanceAs (Module.Finite ℤ (𝓞 K))

/-- Products of fractional ideals have the actual product as their coefficient module. -/
theorem coe_product (n : ℕ) (I : Fin n → FractionalIdeal (𝓞 K)⁰ K) :
    ((∏ i, I i : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) =
      ∏ i, (I i : Submodule (𝓞 K) K) :=
  map_prod (FractionalIdeal.coeSubmoduleHom (S := (𝓞 K)⁰) (P := K)) I Finset.univ

/-- The actual field basis obtained from the pseudobasis by localization. -/
def fieldBasis {n : ℕ} {L : Submodule (𝓞 K) (Fin n → K)}
    (pb : PseudoBasis n L) (hL : L.IsLattice K) : Basis (Fin n) K (Fin n → K) :=
  (Pi.basisFun K (Fin n)).map (pb.ambientEquiv hL)

/-- The ambient extension maps the actual coefficient module onto the original module. -/
theorem map_coordinateModule {n : ℕ} {L : Submodule (𝓞 K) (Fin n → K)}
    (pb : PseudoBasis n L) (hL : L.IsLattice K) :
    (NumberFieldLatticeModule.coordinateModule n pb.ideals).map
      ((pb.ambientEquiv hL).toLinearMap.restrictScalars (𝓞 K)) = L := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change pb.ambientEquiv hL x ∈ L
    rw [pb.ambientEquiv_apply_mem hL ⟨x, hx⟩]
    exact (pb.equiv ⟨x, hx⟩).2
  · intro hz
    obtain ⟨x, hx⟩ := pb.equiv.surjective ⟨z, hz⟩
    refine ⟨x, x.2, ?_⟩
    change pb.ambientEquiv hL x.1 = z
    rw [pb.ambientEquiv_apply_mem]
    exact congrArg Subtype.val hx

/-- In a pseudobasis the intrinsic mixed volume is Gram determinant times
the square of the coefficient product. No principal coefficient ideals are assumed. -/
theorem volumeIdeal_formula {n : ℕ} {L : Submodule (𝓞 K) (Fin n → K)}
    (B : LinearMap.BilinForm K (Fin n → K)) (pb : PseudoBasis n L)
    (hL : L.IsLattice K) :
    IntegralVolume.volumeIdeal B n L hL.fg =
      FractionalIdeal.spanSingleton (𝓞 K)⁰
        (pairingMatrix B (fieldBasis pb hL) (fieldBasis pb hL)).det *
          (∏ i, pb.ideals i) ^ 2 := by
  let f := pb.ambientEquiv hL
  let C := B.comp f.toLinearMap f.toLinearMap
  have hGram : LinearMap.BilinForm.toMatrix (Pi.basisFun K (Fin n)) C =
      pairingMatrix B (fieldBasis pb hL) (fieldBasis pb hL) := by
    apply Matrix.ext
    intro i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  apply FractionalIdeal.coeToSubmodule_injective
  dsimp only
  change MixedVolume.submodule (integerSubring K) B n L =
    ((FractionalIdeal.spanSingleton (𝓞 K)⁰
      (pairingMatrix B (fieldBasis pb hL) (fieldBasis pb hL)).det *
        (∏ i, pb.ideals i) ^ 2 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
  rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton,
    Submodule.span_singleton_mul, FractionalIdeal.coe_pow, coe_product]
  conv_lhs => rw [← map_coordinateModule pb hL]
  change MixedVolume.submodule (integerSubring K) B n
    ((NumberFieldLatticeModule.coordinateModule n pb.ideals).map
      (f.toLinearMap.restrictScalars (integerSubring K))) = _
  rw [MixedVolume.map_isometry (integerSubring K) C B n _ f.toLinearMap (by intros; rfl)]
  change MixedVolume.submodule (integerSubring K) C n
    (DeterminantContent.coordinateModule (integerSubring K) n
      (fun i ↦ (pb.ideals i : Submodule (𝓞 K) K))) = _
  rw [DeterminantContent.coordinate_volume, hGram]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Taking the actual fractional-ideal norm gives the exact numerical volume formula. -/
theorem absNorm_volumeIdeal_formula {n : ℕ} {L : Submodule (𝓞 K) (Fin n → K)}
    (B : LinearMap.BilinForm K (Fin n → K)) (pb : PseudoBasis n L)
    (hL : L.IsLattice K) :
    FractionalIdeal.absNorm (IntegralVolume.volumeIdeal B n L hL.fg) =
      fieldAbsNorm K (pairingMatrix B (fieldBasis pb hL) (fieldBasis pb hL)).det *
        (∏ i, FractionalIdeal.absNorm (pb.ideals i)) ^ 2 := by
  rw [volumeIdeal_formula B pb hL]
  change FractionalIdeal.absNorm (R := 𝓞 K)
    (FractionalIdeal.spanSingleton (𝓞 K)⁰
      (pairingMatrix B (fieldBasis pb hL) (fieldBasis pb hL)).det *
        (∏ i, pb.ideals i) ^ 2) = _
  rw [map_mul, map_pow, map_prod, FractionalIdeal.absNorm_span_singleton]
  rfl

section Ambient

variable {V : Type*} [AddCommGroup V] [Module K V]

set_option backward.isDefEq.respectTransparency false in
/-- A finite full module has an actual pseudobasis with its intrinsic volume
formula. Membership is given by its fractional-ideal coordinates. -/
theorem exists_volume_formula (B : LinearMap.BilinForm K V)
    (L : Submodule (integerSubring K) V) (hLfg : L.FG)
    (hL : Submodule.span K (L : Set V) = ⊤) :
    ∃ b : Basis (Fin (Module.finrank K V)) K V,
      ∃ I : Fin (Module.finrank K V) → FractionalIdeal (integerSubring K)⁰ K,
        (∀ i, I i ≠ 0) ∧ (∀ x : V, x ∈ L ↔ ∀ i, b.repr x i ∈ I i) ∧
          IntegralVolume.volumeIdeal B (Module.finrank K V) L hLfg =
            FractionalIdeal.spanSingleton (integerSubring K)⁰ (pairingMatrix B b b).det *
              (∏ i, I i) ^ 2 := by
  letI := ModuleGenusPatching.finiteDimensional_of_fg_full (integerSubring K) L hLfg hL
  let n := Module.finrank K V
  let e := (Module.finBasis K V).equivFun
  let Lc := L.map (e.toLinearMap.restrictScalars (integerSubring K))
  have hLc : Lc.IsLattice K := by
    constructor
    · exact hLfg.map _
    · change Submodule.span K (e.toLinearMap '' (L : Set V)) = ⊤
      rw [Submodule.span_image, hL, Submodule.map_top]
      exact LinearMap.range_eq_top.mpr e.surjective
  obtain ⟨pb⟩ := NumberFieldLatticeModule.exists_pseudoBasis n Lc hLc
  let f := (pb.ambientEquiv hLc).trans e.symm
  let b := (Pi.basisFun K (Fin n)).map f
  have hmap : (NumberFieldLatticeModule.coordinateModule n pb.ideals).map
      (f.toLinearMap.restrictScalars (integerSubring K)) = L := by
    have hcomp : f.toLinearMap.restrictScalars (integerSubring K) =
        (e.symm.toLinearMap.restrictScalars (integerSubring K)).comp
          ((pb.ambientEquiv hLc).toLinearMap.restrictScalars (integerSubring K)) := rfl
    have hcoord : (NumberFieldLatticeModule.coordinateModule n pb.ideals).map
        ((pb.ambientEquiv hLc).toLinearMap.restrictScalars (integerSubring K)) = Lc := by
      exact map_coordinateModule pb hLc
    rw [hcomp, Submodule.map_comp, hcoord]
    change (L.map (e.toLinearMap.restrictScalars (integerSubring K))).map
      (e.symm.toLinearMap.restrictScalars (integerSubring K)) = L
    rw [← Submodule.map_comp]
    have hid : (e.symm.toLinearMap.restrictScalars (integerSubring K)).comp
        (e.toLinearMap.restrictScalars (integerSubring K)) = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact e.symm_apply_apply x
    rw [hid, Submodule.map_id]
  refine ⟨b, pb.ideals, pb.ideals_ne, ?_, ?_⟩
  · intro x
    rw [← hmap]
    change x ∈ (NumberFieldLatticeModule.coordinateModule n pb.ideals).map
      ((f.restrictScalars (integerSubring K)).toLinearMap) ↔ _
    rw [Submodule.mem_map_equiv]
    change (∀ i ∈ Set.univ, f.symm x i ∈ pb.ideals i) ↔
      ∀ i, b.repr x i ∈ pb.ideals i
    have hrepr (i : Fin n) : b.repr x i = f.symm x i := by
      change (Pi.basisFun K (Fin n)).repr (f.symm x) i = _
      exact Pi.basisFun_repr K (Fin n) (f.symm x) i
    simp only [Set.mem_univ, forall_const, hrepr]
  · let C := B.comp e.symm.toLinearMap e.symm.toLinearMap
    have hback : Lc.map (e.symm.toLinearMap.restrictScalars (integerSubring K)) = L := by
      change (L.map (e.toLinearMap.restrictScalars (integerSubring K))).map
        (e.symm.toLinearMap.restrictScalars (integerSubring K)) = L
      ext x
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        change e.symm (e y) ∈ L
        rw [e.symm_apply_apply]
        exact hy
      · intro hx
        exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
    have hvol : IntegralVolume.volumeIdeal B n L hLfg =
        IntegralVolume.volumeIdeal C n Lc hLc.fg := by
      apply FractionalIdeal.coeToSubmodule_injective
      change MixedVolume.submodule (integerSubring K) B n L =
        MixedVolume.submodule (integerSubring K) C n Lc
      rw [← hback]
      exact MixedVolume.map_isometry (integerSubring K) C B n Lc e.symm.toLinearMap
        (by intros; rfl)
    rw [hvol, volumeIdeal_formula C pb hLc]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The same actual pseudobasis supplies both the ideal and absolute norm formulas. -/
theorem exists_volume_formula_with_norm (B : LinearMap.BilinForm K V)
    (L : Submodule (integerSubring K) V) (hLfg : L.FG)
    (hL : Submodule.span K (L : Set V) = ⊤) :
    ∃ b : Basis (Fin (Module.finrank K V)) K V,
      ∃ I : Fin (Module.finrank K V) → FractionalIdeal (integerSubring K)⁰ K,
        (∀ i, I i ≠ 0) ∧ (∀ x : V, x ∈ L ↔ ∀ i, b.repr x i ∈ I i) ∧
          IntegralVolume.volumeIdeal B (Module.finrank K V) L hLfg =
            FractionalIdeal.spanSingleton (integerSubring K)⁰ (pairingMatrix B b b).det *
              (∏ i, I i) ^ 2 ∧
          FractionalIdeal.absNorm (IntegralVolume.volumeIdeal B (Module.finrank K V) L hLfg) =
            fieldAbsNorm K (pairingMatrix B b b).det *
              (∏ i, FractionalIdeal.absNorm (I i)) ^ 2 := by
  obtain ⟨b, I, hI, hmem, hvol⟩ := exists_volume_formula B L hLfg hL
  refine ⟨b, I, hI, hmem, hvol, ?_⟩
  rw [hvol, map_mul, map_pow, map_prod, FractionalIdeal.absNorm_span_singleton]
  rfl

end Ambient

end NormEuclidean.PseudoBasisVolume
