import NormEuclidean.ChapterX.MultilinearSpan

/-!
# Mixed determinant volume over a subring

The determinant-span construction is available over an arbitrary field subring.
It applies in particular to completed valuation rings, without requiring two to
be a unit in those rings. The number-field volume is the same construction.
-/

noncomputable section

namespace NormEuclidean.MixedVolume

open IntegralVolume

variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

/-- The subring span of all mixed pairing determinants in degree `n`. -/
def submodule (R : Subring F) (B : LinearMap.BilinForm F V) (n : ℕ)
    (L : Submodule R V) : Submodule R F :=
  Submodule.span R (Set.range fun p : (Fin n → L) × (Fin n → L) ↦
    (pairingMatrix B (fun i ↦ (p.1 i : V)) (fun j ↦ (p.2 j : V))).det)

/-- Every actual determinant belongs to the mixed volume. -/
theorem det_mem (R : Subring F) (B : LinearMap.BilinForm F V) (n : ℕ)
    (L : Submodule R V) (x y : Fin n → V) (hx : ∀ i, x i ∈ L) (hy : ∀ j, y j ∈ L) :
    (pairingMatrix B x y).det ∈ submodule R B n L :=
  Submodule.subset_span ⟨(fun i ↦ ⟨x i, hx i⟩, fun j ↦ ⟨y j, hy j⟩), rfl⟩

/-- Interchanging the families and reversing the pairing transposes the matrix. -/
theorem det_flip (B : LinearMap.BilinForm F V) (n : ℕ) (x y : Fin n → V) :
    (pairingMatrix B.flip y x).det = (pairingMatrix B x y).det :=
  Matrix.det_transpose (pairingMatrix B x y)

/-- A determinant bound on generators extends to their entire subring span. -/
theorem le_of_generators (R : Subring F) (B : LinearMap.BilinForm F V) (n : ℕ)
    (S : Set V) (P : Submodule R F)
    (h : ∀ x y : Fin n → V, (∀ i, x i ∈ S) → (∀ j, y j ∈ S) →
      (pairingMatrix B x y).det ∈ P) :
    submodule R B n (Submodule.span R S) ≤ P := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  apply multilinear_mem_of_mem_span
    ((determinantLeft B n (fun j ↦ (p.2 j : V))).toMultilinearMap.restrictScalars R) S P
  · intro x hx
    have hright := multilinear_mem_of_mem_span
      ((determinantLeft B.flip n x).toMultilinearMap.restrictScalars R)
      S P (fun y hy ↦ by
        change (pairingMatrix B.flip y x).det ∈ P
        rw [det_flip]
        exact h x y hx hy)
      (fun j ↦ (p.2 j : V)) (fun j ↦ (p.2 j).2)
    change (pairingMatrix B.flip (fun j ↦ (p.2 j : V)) x).det ∈ P at hright
    rw [det_flip] at hright
    exact hright
  · exact fun i ↦ (p.1 i).2

/-- Actual linear transport preserving a pairing preserves its mixed volume. -/
theorem map_isometry (R : Subring F) (B : LinearMap.BilinForm F V)
    (C : LinearMap.BilinForm F W) (n : ℕ) (L : Submodule R V) (f : V →ₗ[F] W)
    (hf : ∀ x y, C (f x) (f y) = B x y) :
    submodule R C n (L.map (f.restrictScalars R)) = submodule R B n L := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    choose x hx hfx using fun i ↦ (p.1 i).2
    choose y hy hfy using fun j ↦ (p.2 j).2
    dsimp only
    have hmat : pairingMatrix C (fun i ↦ (p.1 i : W)) (fun j ↦ (p.2 j : W)) =
        pairingMatrix B x y := by
      ext i j
      change C (p.1 i) (p.2 j) = B (x i) (y j)
      rw [← hfx i, ← hfy j]
      exact hf _ _
    rw [hmat]
    exact det_mem R B n L x y hx hy
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    dsimp only
    have hmat : pairingMatrix C (fun i ↦ f (p.1 i)) (fun j ↦ f (p.2 j)) =
        pairingMatrix B (fun i ↦ (p.1 i : V)) (fun j ↦ (p.2 j : V)) := by
      ext i j
      exact hf _ _
    rw [← hmat]
    exact det_mem R C n _ _ _
      (fun i ↦ ⟨p.1 i, (p.1 i).2, rfl⟩) (fun j ↦ ⟨p.2 j, (p.2 j).2, rfl⟩)

/-- The global intrinsic volume is this subring construction, definitionally. -/
theorem integer_submodule (B : LinearMap.BilinForm F V) (n : ℕ)
    (L : Submodule (integerSubring F) V) :
    submodule (integerSubring F) B n L = IntegralVolume.volumeSubmodule B n L := rfl

end NormEuclidean.MixedVolume
