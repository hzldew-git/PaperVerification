import TraceEuclidean.GlobalLatticeClass
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.Algebra.Exact.Basic

/-!
# Pseudobases for number-field lattices

This file develops the Dedekind-module input needed for the determinant and
covolume formula of a general, possibly nonfree, ring-of-integers lattice.
The first step is completely intrinsic: a full lattice over the ring of
integers is finite, torsion-free, hence flat and finitely presented, and
therefore projective.
-/

namespace TraceEuclidean

open scoped NumberField

noncomputable section

namespace NumberFieldLatticeModule

variable {K V : Type*} [Field K] [NumberField K]
variable [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
variable [IsScalarTower (𝓞 K) K V]

/-- Scalar extension of any full ring-of-integers lattice along the fraction
field recovers its ambient number-field vector space. -/
theorem isLocalizedModule_subtype (L : Submodule (𝓞 K) V)
    (hL : L.IsLattice K) :
    IsLocalizedModule (nonZeroDivisors (𝓞 K)) L.subtype := by
  letI : L.IsLattice K := hL
  letI : IsLocalizedModule (nonZeroDivisors (𝓞 K))
      (.id : V →ₗ[𝓞 K] V) :=
    isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K
  refine
    { map_units := ?_
      surj := ?_
      exists_of_eq := ?_ }
  · intro s
    exact IsLocalizedModule.map_units
      (S := nonZeroDivisors (𝓞 K)) (f := (.id : V →ₗ[𝓞 K] V)) s
  · intro x
    have hx : x ∈ Submodule.span K (L : Set V) := by
      rw [hL.span_eq_top]
      trivial
    obtain ⟨s, hs⟩ :=
      multiple_mem_span_of_mem_localization_span
        (nonZeroDivisors (𝓞 K)) K (L : Set V) x hx
    have hsL : s • x ∈ L := by
      simpa only [Submodule.span_eq] using hs
    exact ⟨⟨⟨s • x, hsL⟩, s⟩, rfl⟩
  · intro x y hxy
    exact ⟨1, by
      apply Subtype.ext
      simpa using hxy⟩

/-- A full lattice over a number-field integer ring is a finitely generated
projective module. -/
theorem projective (L : Submodule (𝓞 K) V) (hL : L.IsLattice K) :
    Module.Projective (𝓞 K) L := by
  letI : L.IsLattice K := hL
  letI := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  letI : Module.FinitePresentation (𝓞 K) L :=
    Module.finitePresentation_of_finite (𝓞 K) L
  exact Module.Flat.projective_of_finitePresentation

/-- The coordinate lattice associated with a family of fractional ideals. -/
def coordinateModule (n : ℕ)
    (ideals : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
    Submodule (𝓞 K) (Fin n → K) :=
  Submodule.pi Set.univ fun i ↦ (ideals i).coeToSubmodule

/-- A finite product of nonzero fractional ideals is a full lattice in the
ambient coordinate space. -/
theorem coordinateModule_isLattice (n : ℕ)
    (ideals : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (hne : ∀ i, ideals i ≠ 0) :
    (coordinateModule n ideals).IsLattice K := by
  classical
  constructor
  · unfold coordinateModule
    exact Submodule.fg_pi fun i ↦
      FractionalIdeal.fg_of_isUnit (ideals i)
        (isUnit_iff_ne_zero.mpr (hne i))
  · apply top_unique
    rw [← (Pi.basisFun K (Fin n)).span_eq]
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (FractionalIdeal.coeToSubmodule_ne_bot.mpr (hne i))
    have hv : Pi.single i a ∈ coordinateModule n ideals := by
      rw [coordinateModule, Submodule.mem_pi]
      intro j _
      by_cases hji : j = i
      · subst j
        simpa using haI
      · simp [hji]
    have hscaled : a⁻¹ • Pi.single i a ∈
        Submodule.span K (coordinateModule n ideals : Set (Fin n → K)) :=
      Submodule.smul_mem _ a⁻¹ (Submodule.subset_span hv)
    rw [Pi.basisFun_apply]
    have heq : a⁻¹ • Pi.single i a = Pi.single i (1 : K) := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [ha0]
      · simp [hji]
    rw [← heq]
    exact hscaled

instance coordinateModule.instIsLattice (n : ℕ)
    (ideals : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    [∀ i, NeZero (ideals i)] :
    (coordinateModule n ideals).IsLattice K :=
  coordinateModule_isLattice n ideals fun _i ↦ NeZero.ne _

/-- A nonzero fractional ideal is a full one-dimensional lattice. -/
theorem fractionalIdeal_isLattice
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI : I ≠ 0) :
    I.coeToSubmodule.IsLattice K := by
  classical
  constructor
  · exact FractionalIdeal.fg_of_isUnit I (isUnit_iff_ne_zero.mpr hI)
  · obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (FractionalIdeal.coeToSubmodule_ne_bot.mpr hI)
    apply top_unique
    intro x _
    have ha : a ∈ Submodule.span K (I.coeToSubmodule : Set K) :=
      Submodule.subset_span haI
    have hscaled := Submodule.smul_mem
      (Submodule.span K (I.coeToSubmodule : Set K)) (x * a⁻¹) ha
    simpa [smul_eq_mul, ha0] using hscaled

/-- Split the first coordinate from a coordinate lattice. -/
def coordinateModuleSuccEquiv (n : ℕ)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (ideals : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
    coordinateModule (n + 1) (Fin.cases I ideals) ≃ₗ[𝓞 K]
      I.coeToSubmodule × coordinateModule n ideals where
  toFun x :=
    (⟨x.1 0, by
        exact (Submodule.mem_pi.mp x.2 0 (Set.mem_univ 0))⟩,
      ⟨Fin.tail x.1, by
        rw [coordinateModule, Submodule.mem_pi]
        intro i _
        exact Submodule.mem_pi.mp x.2 i.succ (Set.mem_univ i.succ)⟩)
  invFun x :=
    ⟨Fin.cons x.1.1 x.2.1, by
      rw [coordinateModule, Submodule.mem_pi]
      intro i _
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact x.1.2
      · simpa using x.2.2 j (Set.mem_univ j)⟩
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext
    · rfl
    · funext i
      rfl
  map_smul' r x := by
    apply Prod.ext <;> apply Subtype.ext
    · rfl
    · funext i
      rfl
  left_inv x := by
    apply Subtype.ext
    exact Fin.cons_self_tail x.1
  right_inv x := by
    apply Prod.ext <;> apply Subtype.ext
    · rfl
    · rfl

/-- A pseudobasis at the module level: the lattice is equivalent to the
coordinate lattice cut out by nonzero fractional ideals.  Scalar extension
of `equiv` recovers the usual field basis and its embedding in the ambient
coordinate space. -/
structure PseudoBasis (n : ℕ) (L : Submodule (𝓞 K) (Fin n → K)) where
  ideals : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 K)) K
  ideals_ne : ∀ i, ideals i ≠ 0
  equiv : coordinateModule n ideals ≃ₗ[𝓞 K] L

namespace PseudoBasis

/-- Scalar extension of a pseudobasis equivalence to the ambient coordinate
space. -/
def ambientEquiv {n : ℕ} {L : Submodule (𝓞 K) (Fin n → K)}
    (pb : PseudoBasis n L) (hL : L.IsLattice K) :
    (Fin n → K) ≃ₗ[K] (Fin n → K) := by
  let hcoord := coordinateModule_isLattice n pb.ideals pb.ideals_ne
  letI : (coordinateModule n pb.ideals).IsLattice K := hcoord
  letI : L.IsLattice K := hL
  letI : IsLocalizedModule (nonZeroDivisors (𝓞 K))
      (coordinateModule n pb.ideals).subtype :=
    isLocalizedModule_subtype _ hcoord
  letI : IsLocalizedModule (nonZeroDivisors (𝓞 K)) L.subtype :=
    isLocalizedModule_subtype _ hL
  exact IsLocalizedModule.mapEquiv (nonZeroDivisors (𝓞 K))
    (coordinateModule n pb.ideals).subtype L.subtype K pb.equiv

@[simp]
theorem ambientEquiv_apply_mem {n : ℕ}
    {L : Submodule (𝓞 K) (Fin n → K)}
    (pb : PseudoBasis n L) (hL : L.IsLattice K)
    (x : coordinateModule n pb.ideals) :
    pb.ambientEquiv hL x.1 = (pb.equiv x).1 := by
  let hcoord := coordinateModule_isLattice n pb.ideals pb.ideals_ne
  letI : (coordinateModule n pb.ideals).IsLattice K := hcoord
  letI : L.IsLattice K := hL
  letI : IsLocalizedModule (nonZeroDivisors (𝓞 K))
      (coordinateModule n pb.ideals).subtype :=
    isLocalizedModule_subtype _ hcoord
  letI : IsLocalizedModule (nonZeroDivisors (𝓞 K)) L.subtype :=
    isLocalizedModule_subtype _ hL
  change (IsLocalizedModule.mapEquiv (nonZeroDivisors (𝓞 K))
      (coordinateModule n pb.ideals).subtype L.subtype K pb.equiv) x.1 = _
  rw [IsLocalizedModule.mapEquiv_apply]
  exact IsLocalizedModule.map_apply (nonZeroDivisors (𝓞 K))
    (coordinateModule n pb.ideals).subtype L.subtype pb.equiv x

end PseudoBasis

/-- The zero-dimensional lattice has the empty pseudobasis. -/
def pseudoBasisZero (L : Submodule (𝓞 K) (Fin 0 → K)) :
    PseudoBasis 0 L where
  ideals := Fin.elim0
  ideals_ne := fun i ↦ Fin.elim0 i
  equiv := LinearEquiv.ofSubsingleton _ _

/-- Restriction of the first-coordinate projection to a lattice. -/
def headMap {n : ℕ} (L : Submodule (𝓞 K) (Fin (n + 1) → K)) :
    L →ₗ[𝓞 K] K :=
  (LinearMap.proj (R := 𝓞 K) (φ := fun _ : Fin (n + 1) ↦ K) 0).comp
    L.subtype

/-- Fullness forces the first-coordinate image of a lattice to be nonzero. -/
theorem headMap_range_ne_bot {n : ℕ}
    (L : Submodule (𝓞 K) (Fin (n + 1) → K))
    (hL : L.IsLattice K) :
    (headMap L).range ≠ ⊥ := by
  classical
  intro hrange
  have hzero : ∀ x : L, headMap L x = 0 := by
    intro x
    have hx : headMap L x ∈ (headMap L).range :=
      LinearMap.mem_range_self (headMap L) x
    rw [hrange] at hx
    simpa using hx
  let p : (Fin (n + 1) → K) →ₗ[K] K :=
    LinearMap.proj (R := K) (φ := fun _ : Fin (n + 1) ↦ K) 0
  have hle : Submodule.span K (L : Set (Fin (n + 1) → K)) ≤ p.ker := by
    apply Submodule.span_le.2
    intro x hx
    change p x = 0
    exact hzero ⟨x, hx⟩
  have htop : (⊤ : Submodule K (Fin (n + 1) → K)) ≤ p.ker := by
    simpa only [hL.span_eq_top] using hle
  have hbasis : Pi.basisFun K (Fin (n + 1)) 0 ∈ p.ker :=
    htop Submodule.mem_top
  simp [p, Pi.basisFun_apply] at hbasis

/-- The first-coordinate image, bundled as a fractional ideal. -/
def headFractionalIdeal {n : ℕ}
    (L : Submodule (𝓞 K) (Fin (n + 1) → K))
    (hL : L.IsLattice K) :
    FractionalIdeal (nonZeroDivisors (𝓞 K)) K := by
  letI : L.IsLattice K := hL
  exact ⟨(headMap L).range,
    FractionalIdeal.isFractional_of_fg (Submodule.fg_range (headMap L))⟩

@[simp]
theorem headFractionalIdeal_coe {n : ℕ}
    (L : Submodule (𝓞 K) (Fin (n + 1) → K))
    (hL : L.IsLattice K) :
    (headFractionalIdeal L hL).coeToSubmodule = (headMap L).range :=
  rfl

theorem headFractionalIdeal_ne_zero {n : ℕ}
    (L : Submodule (𝓞 K) (Fin (n + 1) → K))
    (hL : L.IsLattice K) :
    headFractionalIdeal L hL ≠ 0 := by
  rw [← FractionalIdeal.coeToSubmodule_ne_bot,
    headFractionalIdeal_coe]
  exact headMap_range_ne_bot L hL

/-- Delete the forced zero first coordinate on the kernel of `headMap`. -/
def kernelTail {n : ℕ}
    (L : Submodule (𝓞 K) (Fin (n + 1) → K)) :
    (headMap L).ker →ₗ[𝓞 K] (Fin n → K) where
  toFun x := Fin.tail x.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NumberField K] in
/-- Deleting the first coordinate is injective on the projection kernel. -/
theorem kernelTail_injective {n : ℕ}
    (L : Submodule (𝓞 K) (Fin (n + 1) → K)) :
    Function.Injective (kernelTail L) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · have hx := x.2
    have hy := y.2
    change x.1.1 0 = 0 at hx
    change y.1.1 0 = 0 at hy
    exact hx.trans hy.symm
  · exact congrFun hxy j

/-- The tail of the first-coordinate kernel is again a full lattice. -/
theorem kernelTail_range_isLattice {n : ℕ}
    (L : Submodule (𝓞 K) (Fin (n + 1) → K))
    (hL : L.IsLattice K) :
    (kernelTail L).range.IsLattice K := by
  classical
  letI : L.IsLattice K := hL
  constructor
  · exact Submodule.fg_range (kernelTail L)
  · apply top_unique
    rw [← (Pi.basisFun K (Fin n)).span_eq]
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    let x : Fin (n + 1) → K :=
      Fin.cons 0 (Pi.basisFun K (Fin n) i)
    have hx : x ∈ Submodule.span K (L : Set (Fin (n + 1) → K)) := by
      rw [hL.span_eq_top]
      trivial
    obtain ⟨s, hs⟩ :=
      multiple_mem_span_of_mem_localization_span
        (nonZeroDivisors (𝓞 K)) K (L : Set (Fin (n + 1) → K)) x hx
    have hsL : s • x ∈ L := by
      simpa only [Submodule.span_eq] using hs
    let l : L := ⟨s • x, hsL⟩
    have hlker : l ∈ (headMap L).ker := by
      change (s • x) 0 = 0
      simp [x]
    let k : (headMap L).ker := ⟨l, hlker⟩
    have hrange : kernelTail L k ∈ (kernelTail L).range :=
      LinearMap.mem_range_self (kernelTail L) k
    have hspan : kernelTail L k ∈
        Submodule.span K ((kernelTail L).range : Set (Fin n → K)) :=
      Submodule.subset_span hrange
    let a : K := algebraMap (𝓞 K) K (s : 𝓞 K)
    have ha0 : a ≠ 0 := by
      intro ha
      apply nonZeroDivisors.ne_zero s.2
      apply IsFractionRing.injective (𝓞 K) K
      simp [a] at ha
    have hscaled : a⁻¹ • kernelTail L k ∈
        Submodule.span K ((kernelTail L).range : Set (Fin n → K)) :=
      Submodule.smul_mem _ a⁻¹ hspan
    have heq : a⁻¹ • kernelTail L k = Pi.single i (1 : K) := by
      ext j
      simp [kernelTail, k, l, x, a, Pi.basisFun_apply, Fin.tail]
      change a⁻¹ * (a * (Pi.single i (1 : K) : Fin n → K) j) =
        (Pi.single i (1 : K) : Fin n → K) j
      simp [ha0]
    rw [Pi.basisFun_apply, ← heq]
    exact hscaled

/-- Every full lattice in `K^n` admits a pseudobasis by nonzero fractional
ideals.  The proof is the usual Dedekind-module induction: project to the
first coordinate, split the resulting projective rank-one quotient, and
recurse on the full tail lattice of the kernel. -/
theorem exists_pseudoBasis :
    ∀ (n : ℕ) (L : Submodule (𝓞 K) (Fin n → K)),
      L.IsLattice K → Nonempty (PseudoBasis n L)
  | 0, L, _ => ⟨pseudoBasisZero L⟩
  | n + 1, L, hL => by
      let I := headFractionalIdeal L hL
      have hI : I ≠ 0 := headFractionalIdeal_ne_zero L hL
      have htail : (kernelTail L).range.IsLattice K :=
        kernelTail_range_isLattice L hL
      obtain ⟨pb⟩ := exists_pseudoBasis n (kernelTail L).range htail
      have hhead : (headMap L).range.IsLattice K := by
        rw [← headFractionalIdeal_coe L hL]
        exact fractionalIdeal_isLattice I hI
      letI : (headMap L).range.IsLattice K := hhead
      letI : Module.Projective (𝓞 K) (headMap L).range :=
        projective (headMap L).range hhead
      obtain ⟨sec, hsec⟩ :=
        (headMap L).rangeRestrict.exists_rightInverse_of_surjective
          (headMap L).range_rangeRestrict
      have hexact : Function.Exact
          (headMap L).rangeRestrict.ker.subtype
          (headMap L).rangeRestrict :=
        LinearMap.exact_subtype_ker_map (headMap L).rangeRestrict
      have hinj : Function.Injective
          ((headMap L).rangeRestrict.ker.subtype :
            (headMap L).rangeRestrict.ker →ₗ[𝓞 K] L) :=
        (headMap L).rangeRestrict.ker.injective_subtype
      let splitData :=
        (Function.Exact.splitSurjectiveEquiv
          (R := 𝓞 K)
          (M := (headMap L).rangeRestrict.ker)
          (N := L)
          (P := (headMap L).range)
          (f := (headMap L).rangeRestrict.ker.subtype)
          (g := (headMap L).rangeRestrict) hexact hinj)
          ⟨sec, hsec⟩
      have hker : (headMap L).rangeRestrict.ker = (headMap L).ker := by
        ext x
        simp
      let splitEquiv0 :
          L ≃ₗ[𝓞 K]
            (headMap L).rangeRestrict.ker × (headMap L).range :=
        splitData.1
      let splitEquiv :
          L ≃ₗ[𝓞 K] (headMap L).ker × (headMap L).range :=
        splitEquiv0.trans
          (LinearEquiv.prodCongr
            (LinearEquiv.ofEq _ _ hker) (LinearEquiv.refl _ _))
      let tailEquiv :
          (headMap L).ker ≃ₗ[𝓞 K] (kernelTail L).range :=
        LinearEquiv.ofInjective (kernelTail L) (kernelTail_injective L)
      let headEquiv : I.coeToSubmodule ≃ₗ[𝓞 K] (headMap L).range :=
        LinearEquiv.ofEq _ _ (headFractionalIdeal_coe L hL)
      let allIdeals : Fin (n + 1) →
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
        Fin.cases I pb.ideals
      refine ⟨{
        ideals := allIdeals
        ideals_ne := ?_
        equiv := ?_ }⟩
      · intro i
        exact Fin.cases hI (fun j ↦ pb.ideals_ne j) i
      · exact
          (coordinateModuleSuccEquiv n I pb.ideals).trans <|
            (LinearEquiv.prodCongr headEquiv pb.equiv).trans <|
              (LinearEquiv.prodCongr (LinearEquiv.refl _ _)
                tailEquiv.symm).trans <|
                (LinearEquiv.prodComm (𝓞 K) _ _).trans splitEquiv.symm

end NumberFieldLatticeModule

namespace GlobalLatticePresentation

/-- Scalar extension of a full ring-of-integers lattice along the fraction
field recovers the ambient number-field vector space. -/
theorem lattice_isLocalizedModule (P : GlobalLatticePresentation) :
    IsLocalizedModule (nonZeroDivisors (𝓞 P.field.1)) P.L.subtype := by
  exact NumberFieldLatticeModule.isLocalizedModule_subtype P.L P.full

/-- A full ring-of-integers lattice in a number-field vector space is a
finitely generated projective module. -/
theorem lattice_projective (P : GlobalLatticePresentation) :
    Module.Projective (𝓞 P.field.1) P.L := by
  exact NumberFieldLatticeModule.projective P.L P.full

end GlobalLatticePresentation

end

end TraceEuclidean
