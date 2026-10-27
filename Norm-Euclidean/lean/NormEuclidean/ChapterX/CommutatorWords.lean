import NormEuclidean.ChapterX.CommutatorGeneration

/-!
# Literal short-commutator words for the actual derived group

Subgroup closure is converted into finite products. Inversion reverses
the word and interchanges its two reflecting vectors in each factor.
-/

noncomputable section

namespace NormEuclidean.CommutatorWords

open ProperSpinor SpinorBaseChange CommutatorGeneration

variable {F E : Type*} [Field F] [CharZero F] [AddCommGroup E] [Module F E]
  [FiniteDimensional F E] (Q : QuadraticForm F E) (hQ : Q.polarBilin.Nondegenerate)

/-- Regard a short commutator as an actual proper transformation. -/
def shortProper (p : ReflectingPair Q) : properGroup Q :=
  doubleReflection Q hQ p.1.1 p.1.2 p.2.1 p.2.2 ^ 2

@[simp] theorem shortProper_coe (p : ReflectingPair Q) :
    (shortProper Q hQ p).1 = shortAmbient Q p := rfl

include hQ in
/-- Membership in the actual ambient derived group supplies a literal finite short word. -/
theorem exists_ambient_word (g : ambientGroup Q) (hg : g ∈ commutator (ambientGroup Q)) :
    ∃ l : List (ReflectingPair Q), (l.map (shortAmbient Q)).prod = g := by
  rw [← shortSubgroup_eq_commutator Q hQ] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      exact ⟨[p], by simp⟩
  | one => exact ⟨[], rfl⟩
  | mul g h _ _ hg hh =>
      obtain ⟨l, hl⟩ := hg
      obtain ⟨m, hm⟩ := hh
      exact ⟨l ++ m, by simp [hl, hm]⟩
  | inv g _ hg =>
      obtain ⟨l, hl⟩ := hg
      refine ⟨l.reverse.map Prod.swap, ?_⟩
      rw [← hl, List.prod_inv_reverse]
      simp only [List.map_map, List.map_reverse, Function.comp_def, short_inv]

/-- A proper member of the ambient commutator group is a product of actual proper shorts. -/
theorem exists_proper_word (g : properGroup Q)
    (hg : g.1 ∈ commutator (ambientGroup Q)) :
    ∃ l : List (ReflectingPair Q), (l.map (shortProper Q hQ)).prod = g := by
  obtain ⟨l, hl⟩ := exists_ambient_word Q hQ g.1 hg
  refine ⟨l, Subtype.ext ?_⟩
  have hmap := (properGroup Q).subtype.map_list_prod (l.map (shortProper Q hQ))
  simp only [List.map_map, Function.comp_def, shortProper_coe] at hmap
  exact hmap.trans hl

end NormEuclidean.CommutatorWords
