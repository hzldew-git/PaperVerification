import NormEuclidean.ChapterX.GeneratedWords
import NormEuclidean.ChapterX.CommutatorWords
import NormEuclidean.ChapterX.ShortCommutatorWords

/-!
# Finite local commutator targets as simultaneous short-commutator words

The coordinates may have different original word lengths. Single-coordinate
words and subgroup closure assemble a common finite word without assuming
any local group-generation principle.
-/

noncomputable section

namespace NormEuclidean.FiniteCommutatorWords

open IsDedekindDomain CompletedIntegralLattice ProperSpinor SpinorBaseChange
  CommutatorGeneration CommutatorWords ProperWeakApproximation ReflectionApproximation

variable {K V : Type*} [Field K] [NumberField K] [Invertible (2 : K)]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

local instance finiteCharZero (p : HeightOneSpectrum (integerSubring K)) :
    CharZero (LocalField (integerSubring K) p) := Algebra.charZero_of_charZero K _

/-- A tuple of actual local short commutators. -/
def tupleShort (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (T : Finset (HeightOneSpectrum (integerSubring K))) (p : pairDomain Q T) :
    (v : T) → properGroup (form (integerSubring K) v.1 Q) := pairImage Q hQ T p ^ 2

def swapTarget (Q : QuadraticForm K V) (T : Finset (HeightOneSpectrum (integerSubring K)))
    (p : pairDomain Q T) : pairDomain Q T :=
  ⟨fun v ↦ (p.1 v).swap, fun v ↦ ⟨(p.2 v).2, (p.2 v).1⟩⟩

theorem tupleShort_inv (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (T : Finset (HeightOneSpectrum (integerSubring K))) (p : pairDomain Q T) :
    (tupleShort Q hQ T p)⁻¹ = tupleShort Q hQ T (swapTarget Q T p) := by
  funext v
  apply Subtype.ext
  exact short_inv (form (integerSubring K) v.1 Q)
    (⟨(p.1 v).1, (p.2 v).1⟩, ⟨(p.1 v).2, (p.2 v).2⟩)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- The actual local ambient commutator condition supplies a common finite short word. -/
theorem exists_word (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hpos : 0 < Module.finrank K V) (T : Finset (HeightOneSpectrum (integerSubring K)))
    (a : (v : T) → properGroup (form (integerSubring K) v.1 Q))
    (ha : ∀ v, (a v).1 ∈ commutator (ambientGroup (form (integerSubring K) v.1 Q))) :
    ∃ l : List (pairDomain Q T), ShortCommutatorWords.wordImage Q hQ T l = a := by
  classical
  let G : T → Type _ := fun v ↦ ↥(properGroup (form (integerSubring K) v.1 Q))
  let H := Subgroup.closure (Set.range (tupleShort Q hQ T))
  obtain ⟨u, hu⟩ := (SpinorBridge.quadraticSpace Q hQ).exists_isAnisotropic_of_finrank_pos hpos
  have hu0 : Q u ≠ 0 := by simpa [Bong.QuadraticSpace.IsAnisotropic] using hu
  have hs (v : T) (g : G v)
      (hg : g.1 ∈ commutator (ambientGroup (form (integerSubring K) v.1 Q))) :
      MonoidHom.mulSingle G v g ∈ H := by
    obtain ⟨l, hl⟩ := exists_proper_word (form (integerSubring K) v.1 Q)
      (form_polarBilin_nondegenerate (integerSubring K) v.1 Q hQ) g hg
    rw [← hl, MonoidHom.map_list_prod, List.map_map]
    apply H.list_prod_mem
    intro b hb
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hb
    let p0 : PairData Q T := fun w ↦
      (inclusion (integerSubring K) w.1 u, inclusion (integerSubring K) w.1 u)
    let p := Function.update p0 v (r.1.1, r.2.1)
    have hp : p ∈ pairDomain Q T := by
      intro w
      by_cases hw : w = v
      · subst w
        simpa [p] using And.intro r.1.2 r.2.2
      · simpa [p, p0, hw] using And.intro
          (form_inclusion_ne_zero (integerSubring K) w.1 Q u hu0)
          (form_inclusion_ne_zero (integerSubring K) w.1 Q u hu0)
    have heq : tupleShort Q hQ T ⟨p, hp⟩ =
        MonoidHom.mulSingle G v (shortProper (form (integerSubring K) v.1 Q)
          (form_polarBilin_nondegenerate (integerSubring K) v.1 Q hQ) r) := by
      funext w
      by_cases hw : w = v
      · subst w
        simp [tupleShort, pairImage, p, shortProper]
      · simp [tupleShort, pairImage, p, p0, hw, doubleReflection_self]
    dsimp only [Function.comp_apply]
    rw [← heq]
    exact Subgroup.subset_closure (Set.mem_range_self _)
  let A (v : T) : Subgroup (G v) :=
    (commutator (ambientGroup (form (integerSubring K) v.1 Q))).comap
      (properGroup (form (integerSubring K) v.1 Q)).subtype
  have haH : a ∈ H := GeneratedWords.mem_of_singles H A hs a ha
  obtain ⟨l, hl⟩ := GeneratedWords.exists_word (tupleShort Q hQ T) (swapTarget Q T)
    (tupleShort_inv Q hQ T) haH
  refine ⟨l, ?_⟩
  funext v
  have he := (Pi.evalMonoidHom G v).map_list_prod (l.map (tupleShort Q hQ T))
  have hh := congrFun hl v
  simp only [List.map_map] at he
  exact he.symm.trans hh

end NormEuclidean.FiniteCommutatorWords
