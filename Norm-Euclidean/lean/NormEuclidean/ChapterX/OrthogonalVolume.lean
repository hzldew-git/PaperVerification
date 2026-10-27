import NormEuclidean.ChapterX.MultilinearSpan
import NormEuclidean.ChapterX.ProjectedComplement

/-!
# Volume of an orthogonal line and complement

Mixed determinants on `Ry + M` reduce to the line value times complementary
determinants. Span induction handles nonfree integral modules. No ideal
class, determinant identity, or volume comparison is assumed as a law.
-/

noncomputable section

namespace NormEuclidean.IntegralVolume

open Matrix Module ProjectedComplement
open scoped Pointwise

variable {K V : Type*} [Field K] [NumberField K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A mixed determinant with too many vectors in one field subspace vanishes. -/
theorem det_pairing_lower_dimension (B : LinearMap.BilinForm K V) (n : ℕ)
    (U : Submodule K V) (hdim : Module.finrank K U < n) (x y : Fin n → V)
    (hx : ∀ i, x i ∈ U) : (pairingMatrix B x y).det = 0 := by
  let u : Fin n → U := fun i ↦ ⟨x i, hx i⟩
  have hdep : ¬ LinearIndependent K u := by
    intro h
    have hcard := h.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hcard
    exact (not_le_of_gt hdim) hcard
  exact ((determinantLeft B n y).compLinearMap U.subtype).map_linearDependent u hdep

/-- Half-polar pairings commute with the actual complementary subtype. -/
theorem halfPolar_complement_apply (Q : QuadraticForm K V) (y : V)
    (u v : complement Q y) :
    halfPolar (Q.comp (complement Q y).subtype) u v = halfPolar Q (u : V) (v : V) := rfl

/-- Complement vectors are orthogonal to the distinguished line in both orders. -/
theorem halfPolar_line_complement (Q : QuadraticForm K V) (y : V)
    (u : complement Q y) : halfPolar Q y (u : V) = 0 ∧ halfPolar Q (u : V) y = 0 := by
  have h := u.property y (Submodule.subset_span (Set.mem_singleton y))
  exact ⟨h, (halfPolar_comm Q (u : V) y).trans h⟩

/-- The actual split submodule formed from an integral line and a complement module. -/
def orthogonalLineModule (Q : QuadraticForm K V) (y : V)
    (M : Submodule (integerSubring K) (complement Q y)) :
    Submodule (integerSubring K) V :=
  Submodule.span (integerSubring K) {y} ⊔
    M.map ((complement Q y).subtype.restrictScalars (integerSubring K))

/-- A union of line and complementary generators spans the actual split module. -/
theorem span_line_generators (Q : QuadraticForm K V) (y : V)
    (M : Submodule (integerSubring K) (complement Q y)) :
    Submodule.span (integerSubring K)
      ({y} ∪ ((fun u : complement Q y ↦ (u : V)) '' (M : Set (complement Q y)))) =
      orthogonalLineModule Q y M := by
  rw [Submodule.span_union]
  change _ ⊔ Submodule.span (integerSubring K)
    (((complement Q y).subtype.restrictScalars (integerSubring K)) ''
      (M : Set (complement Q y))) = _
  rw [Submodule.span_image, Submodule.span_eq]
  rfl

/-- Appending the orthogonal line multiplies each complementary mixed determinant by its value. -/
theorem det_pairing_cons_line (Q : QuadraticForm K V) (y : V) (n : ℕ)
    (x z : Fin n → complement Q y) :
    (pairingMatrix (halfPolar Q) (Fin.cons y (fun i ↦ (x i : V)))
      (Fin.cons y (fun j ↦ (z j : V)))).det =
      Q y * (pairingMatrix (halfPolar (Q.comp (complement Q y).subtype)) x z).det := by
  rw [Matrix.det_succ_row_zero, Finset.sum_eq_single 0]
  · simp only [Fin.val_zero, pow_zero, one_mul, pairingMatrix, Fin.cons_zero, halfPolar_self]
    congr 1
  · intro j _ hj
    cases j using Fin.cases with
    | zero => exact (hj rfl).elim
    | succ j =>
      simp only [pairingMatrix, Fin.cons_zero, Fin.cons_succ,
        (halfPolar_line_complement Q y (z j)).1, mul_zero, zero_mul]
  · simp

/-- Orthogonal line decomposition gives the exact intrinsic volume formula.
The complementary module need not be free or finitely generated. -/
theorem volumeSubmodule_orthogonal_line (Q : QuadraticForm K V) (y : V) (n : ℕ)
    (hn : Module.finrank K (complement Q y) = n)
    (M : Submodule (integerSubring K) (complement Q y)) :
    volumeSubmodule (halfPolar Q) (n + 1) (orthogonalLineModule Q y M) =
      Q y • volumeSubmodule (halfPolar (Q.comp (complement Q y).subtype)) n M := by
  classical
  let U := complement Q y
  let C := halfPolar (Q.comp U.subtype)
  let S : Set V := {y} ∪ ((fun u : U ↦ (u : V)) '' (M : Set U))
  let P := Q y • volumeSubmodule C n M
  apply le_antisymm
  · rw [← span_line_generators]
    apply volumeSubmodule_le_of_generators
    intro x z hx hz
    have extract (v : V) (hv : v ∈ S) (hvy : v ≠ y) : ∃ u ∈ M, (u : V) = v := by
      rcases hv with h | h
      · exact (hvy h).elim
      · exact h
    by_cases hline : ∃ i : Fin (n + 1), x i = y
    · obtain ⟨i, hi⟩ := hline
      by_cases hdup : ∃ k : Fin (n + 1), k ≠ i ∧ x k = y
      · obtain ⟨k, hki, hk⟩ := hdup
        have hzero : (pairingMatrix (halfPolar Q) x z).det = 0 :=
          Matrix.det_zero_of_row_eq hki (by ext j; simp only [pairingMatrix, hi, hk])
        rw [hzero]
        exact P.zero_mem
      have hnot (k : Fin (n + 1)) (hki : k ≠ i) : x k ≠ y :=
        fun hk ↦ hdup ⟨k, hki, hk⟩
      choose u hu hux using fun k : Fin n ↦
        extract (x (i.succAbove k)) (hx _) (hnot _ (Fin.succAbove_ne i k))
      rw [Matrix.det_succ_row _ i]
      apply P.sum_mem
      intro j _
      by_cases hj : z j = y
      · by_cases hdupz : ∃ k : Fin (n + 1), k ≠ j ∧ z k = y
        · obtain ⟨k, hkj, hk⟩ := hdupz
          obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hkj
          have hzero : ((pairingMatrix (halfPolar Q) x z).submatrix
              i.succAbove j.succAbove).det = 0 := by
            apply Matrix.det_eq_zero_of_column_eq_zero l
            intro a
            change halfPolar Q (x (i.succAbove a)) (z (j.succAbove l)) = 0
            rw [hl, hk, ← hux a]
            exact (halfPolar_line_complement Q y (u a)).2
          rw [hzero, mul_zero]
          exact P.zero_mem
        have hnotz (k : Fin (n + 1)) (hkj : k ≠ j) : z k ≠ y :=
          fun hk ↦ hdupz ⟨k, hkj, hk⟩
        choose v hv hvz using fun k : Fin n ↦
          extract (z (j.succAbove k)) (hz _) (hnotz _ (Fin.succAbove_ne j k))
        have hmat : (pairingMatrix (halfPolar Q) x z).submatrix
            i.succAbove j.succAbove = pairingMatrix C u v := by
          ext a b
          change halfPolar Q (x (i.succAbove a)) (z (j.succAbove b)) = C (u a) (v b)
          rw [← hux a, ← hvz b]
          rfl
        have hminor := det_mem_volumeSubmodule C n M u v hu hv
        have hmem : Q y * (pairingMatrix C u v).det ∈ P := by
          exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
            ⟨(pairingMatrix C u v).det, hminor, rfl⟩
        have hsign := P.smul_mem ((-1 : integerSubring K) ^ (i + j : ℕ)) hmem
        rw [pairingMatrix, hi, hj, halfPolar_self, hmat]
        simpa only [Subring.smul_def, Subring.coe_pow, Subring.coe_neg, Subring.coe_one,
          smul_eq_mul, mul_assoc] using hsign
      · obtain ⟨v, _, hv⟩ := extract (z j) (hz j) hj
        change (-1 : K) ^ (i + j : ℕ) * halfPolar Q (x i) (z j) * _ ∈ P
        rw [hi, ← hv, (halfPolar_line_complement Q y v).1, mul_zero, zero_mul]
        exact P.zero_mem
    · choose u hu hux using fun i ↦ extract (x i) (hx i) (fun hi ↦ hline ⟨i, hi⟩)
      have hzero := det_pairing_lower_dimension (halfPolar Q) (n + 1) U
        (by rw [hn]; exact Nat.lt_succ_self n) x z
        (fun i ↦ by rw [← hux i]; exact (u i).2)
      rw [hzero]
      exact P.zero_mem
  · rw [volumeSubmodule, Submodule.smul_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ⟨p, rfl⟩, rfl⟩
    let x : Fin (n + 1) → V := Fin.cons y (fun i ↦ (p.1 i : V))
    let z : Fin (n + 1) → V := Fin.cons y (fun j ↦ (p.2 j : V))
    have hmem (p : Fin n → M) :
        ∀ i : Fin (n + 1), (Fin.cons y (fun j ↦ (p j : V)) : Fin (n + 1) → V) i ∈
          orthogonalLineModule Q y M := by
      intro i
      cases i using Fin.cases with
      | zero =>
        exact Submodule.mem_sup.mpr
          ⟨y, Submodule.subset_span (Set.mem_singleton y), 0, by simp, by simp⟩
      | succ i =>
        exact Submodule.mem_sup.mpr ⟨0, by simp, p i,
          ⟨p i, (p i).2, rfl⟩, by simp⟩
    have hdet := det_mem_volumeSubmodule (halfPolar Q) (n + 1)
      (orthogonalLineModule Q y M) x z (hmem p.1) (hmem p.2)
    rw [det_pairing_cons_line] at hdet
    exact hdet

end NormEuclidean.IntegralVolume
