import NormEuclidean.ScalarExtension

/-!
# Clearing a common lattice denominator

This is the lattice sandwich ingredient in Step 1 of Theorem 1.2 (reference manuscript). It uses
finite generation of the source and fullness of the target, not a free
basis of either integral lattice.
-/

namespace NormEuclidean

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {R : Subring K} [IsFractionRing R K]

/-- A finite set of ambient vectors has a common nonzero integral denominator
putting all of them in a full submodule. -/
theorem exists_common_denominator (M : Submodule R V)
    (hM : Submodule.span K (M : Set V) = ⊤) (s : Finset V) :
    ∃ a : R, a ≠ 0 ∧ ∀ x ∈ s, (a : K) • x ∈ M := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | @insert x s hx ih =>
    obtain ⟨a, ha, hax⟩ := ScalarExtension.exists_denominator M hM x
    obtain ⟨b, hb, hbs⟩ := ih
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · have h := M.smul_mem b hax
      convert h using 1
      simp only [Subring.coe_mul, Subring.smul_def, smul_smul]
      rw [mul_comm]
    · have h := M.smul_mem a (hbs y hy)
      simpa only [Subring.coe_mul, Subring.smul_def, smul_smul] using h

/-- Any finite submodule can be scaled into any full submodule by a nonzero
integral scalar. This gives the sandwich `a L ⊆ L₀ ⊆ L` when a full finite
submodule `L₀ ⊆ L` has been chosen. -/
theorem exists_lattice_denominator (L M : Submodule R V) (hL : L.FG)
    (hM : Submodule.span K (M : Set V) = ⊤) :
    ∃ a : R, a ≠ 0 ∧ ∀ x ∈ L, (a : K) • x ∈ M := by
  obtain ⟨s, hs⟩ := hL
  obtain ⟨a, ha, has⟩ := exists_common_denominator M hM s
  refine ⟨a, ha, ?_⟩
  intro x hx
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact has y hy
  | zero => simp
  | add x y _ _ hx hy => simpa only [smul_add] using M.add_mem hx hy
  | smul r y _ hy =>
    have h := M.smul_mem r hy
    simpa only [smul_comm (a : K) r y] using h

end NormEuclidean
