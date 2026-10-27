import NormEuclidean.TernaryUnipotentReduction
import NormEuclidean.ChapterX.GeneratedWords

/-!
# Generation of the genuine ternary Wall kernel by opposite unipotents
-/

noncomputable section

namespace NormEuclidean.TernaryKernelGeneration

open ProperSpinor SpinorBaseChange HyperbolicUnipotentGroup

variable {F E : Type*} [Field F] [CharZero F] [AddCommGroup E] [Module F E]
  [FiniteDimensional F E] (Q : QuadraticForm F E) (hQ : Q.polarBilin.Nondegenerate)
  (hA : Q.Anisotropic)

/-- The two opposite families generate the entire proper Wall kernel in dimension three. -/
theorem generated_eq_kernel (hdim : Module.finrank F E = 1) :
    generated Q hQ hA = (properAmbientSpinorNormHom (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ)).ker := by
  apply le_antisymm (generated_le_kernel Q hQ hA)
  intro g hg
  obtain ⟨u, hu⟩ := (SpinorBridge.quadraticSpace Q hQ).exists_isAnisotropic_of_finrank_pos
    (by omega : 0 < Module.finrank F E)
  have hu0 : Q u ≠ 0 := by simpa [Bong.QuadraticSpace.IsAnisotropic] using hu
  obtain ⟨r, hr, a, ha⟩ :=
    TernaryUnipotentReduction.exists_reduction Q hQ hA hdim u hu0 g
  let theta := properAmbientSpinorNormHom (Hyperbolic.form Q)
    (Hyperbolic.form_polarBilin_nondegenerate Q hQ)
  have hclass : Bong.Dyadic.squareClass F a = 1 := by
    have hh := congrArg theta ha
    rw [map_mul, show theta r = 1 from generated_le_kernel Q hQ hA hr,
      show theta g = 1 from hg, one_mul] at hh
    exact (hyperbolicCorrection_spinorNorm Q hQ a).symm.trans hh.symm
  have hasq : a ∈ Subgroup.square Fˣ := (QuotientGroup.eq_one_iff _).mp hclass
  obtain ⟨s, hs⟩ := hasq
  have hd : hyperbolicCorrection Q hQ a ∈ generated Q hQ hA := by
    rw [hs]
    simpa only [pow_two] using
      TernaryUnipotentDilation.square_correction_mem Q hQ hA hdim u hu0 s
  have hrg : r * g ∈ generated Q hQ hA := ha ▸ hd
  exact (generated Q hQ hA).mul_mem_cancel_left hr |>.mp hrg

/-- One Boolean selects which of the two actual unipotent families is used. -/
def family (b : Bool) (u : E) : properGroup (Hyperbolic.form Q) :=
  if b then lower Q hQ hA u else upper Q hQ hA u

theorem family_zero (b : Bool) : family Q hQ hA b 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  cases b <;> simp [family, upper, lower, HyperbolicUnipotent.element_apply,
    OppositeHyperbolicUnipotent.element_apply]

theorem family_add (b : Bool) (u v : E) :
    family Q hQ hA b (u + v) = family Q hQ hA b u * family Q hQ hA b v := by
  cases b
  · exact HyperbolicUnipotent.element_add Q hQ hA u v
  · apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    change Hyperbolic.swap
      ((upper Q hQ hA (u + v)).1.1 (Hyperbolic.swap z)) =
      Hyperbolic.swap ((upper Q hQ hA u).1.1
        (Hyperbolic.swap (Hyperbolic.swap
          ((upper Q hQ hA v).1.1 (Hyperbolic.swap z)))))
    rw [Hyperbolic.swap_swap]
    rw [show upper Q hQ hA (u + v) = upper Q hQ hA u * upper Q hQ hA v from
      HyperbolicUnipotent.element_add Q hQ hA u v]
    rfl

theorem family_inv (b : Bool) (u : E) :
    (family Q hQ hA b u)⁻¹ = family Q hQ hA b (-u) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← family_add, add_neg_cancel, family_zero]

/-- Every actual ternary kernel element is a literal finite scalar-parameter unipotent word. -/
theorem exists_scalar_word (hdim : Module.finrank F E = 1) (u : E) (hu : u ≠ 0)
    (g : properGroup (Hyperbolic.form Q))
    (hg : properAmbientSpinorNormHom (Hyperbolic.form Q)
      (Hyperbolic.form_polarBilin_nondegenerate Q hQ) g = 1) :
    ∃ l : List (Bool × F),
      (l.map (fun p ↦ family Q hQ hA p.1 (p.2 • u))).prod = g := by
  let f : Bool × F → properGroup (Hyperbolic.form Q) :=
    fun p ↦ family Q hQ hA p.1 (p.2 • u)
  have hle : generated Q hQ hA ≤ Subgroup.closure (Set.range f) := by
    apply (Subgroup.closure_le _).2
    rintro x (⟨v, rfl⟩ | ⟨v, rfl⟩)
    · obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one hdim hu v
      exact Subgroup.subset_closure ⟨(false, c), rfl⟩
    · obtain ⟨c, rfl⟩ := exists_smul_eq_of_finrank_eq_one hdim hu v
      exact Subgroup.subset_closure ⟨(true, c), rfl⟩
  have hmem : g ∈ Subgroup.closure (Set.range f) := by
    apply hle
    rw [generated_eq_kernel Q hQ hA hdim]
    exact hg
  exact GeneratedWords.exists_word f (fun p ↦ (p.1, -p.2))
    (fun p ↦ by simp only [f, family_inv, neg_smul]) hmem

end NormEuclidean.TernaryKernelGeneration
