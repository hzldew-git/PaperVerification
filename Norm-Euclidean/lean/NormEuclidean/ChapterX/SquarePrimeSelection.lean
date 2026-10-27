import NormEuclidean.ChapterX.SquarePrimeTransfer
import Mathlib.Data.List.Sublists

/-!
# Simultaneous square and nonsquare prime selection

O'Meara 65:16-17 can be implemented by adjoining one square root at a
time. The distinguished class must avoid every product of the classes
to be made square. Global square detection in each successive number
field and odd local unit square classes then give a prime in the base.
-/

noncomputable section

namespace NormEuclidean.SquarePrimeSelection

open IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm SUnitNormArithmetic
open QuadraticSquareDescent SquarePrimeTransfer
open scoped NumberField

/-- The distinguished square class is outside the span of the given finite family. -/
def AvoidsSquares {F : Type*} [CommGroup F] (a : F) (B : List F) : Prop :=
  ∀ C : List F, C.Sublist B → ¬ IsSquare (a * C.prod)

universe u

/-- A distinguished nonsquare class can be separated from finitely many other classes
at an actual odd prime in any cofinite good set. No prime-selection input is assumed. -/
theorem exists_pattern (n : ℕ) :
    ∀ {K : Type u} [Field K] [NumberField K] (a : Kˣ) (B : List Kˣ), B.length ≤ n →
      AvoidsSquares a B → ∀ (S : Set (HeightOneSpectrum (𝓞 K))), Sᶜ.Finite →
        (∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal) → a ∈ sUnitSubgroup S →
        (∀ b ∈ B, b ∈ sUnitSubgroup S) →
        ∃ p ∈ S, ¬ IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom a) ∧
          ∀ b ∈ B, IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom b) := by
  induction n with
  | zero =>
    intro K _ _ a B hlen hav S hS _ _ _
    have hB : B = [] := List.length_eq_zero_iff.mp (by omega)
    subst B
    have hans : ¬ IsSquare a := by simpa using hav [] (List.Sublist.refl [])
    have haF : ¬ IsSquare a.val := fun h ↦ hans ((GlobalSquare.unit_square_iff a).mpr h)
    obtain ⟨p, hp, hns⟩ := GlobalSquare.exists_nonsquare_place a.val haF Sᶜ hS
    exact ⟨p, not_not.mp hp, fun h ↦ hns ((GlobalSquare.unit_square_iff _).mp h),
      fun b hb ↦ False.elim (List.not_mem_nil hb)⟩
  | succ n ih =>
    intro K _ _ a B hlen hav S hS htwo hau hbu
    cases B with
    | nil =>
      exact ih a [] (by simp) hav S hS htwo hau hbu
    | cons b B =>
      have hlenB : B.length ≤ n := by simpa using Nat.le_of_succ_le_succ hlen
      have havB : AvoidsSquares a B := fun C hC ↦ hav C (hC.cons b)
      have hbuB : ∀ c ∈ B, c ∈ sUnitSubgroup S := fun c hc ↦ hbu c (by simp [hc])
      by_cases hb : IsSquare b
      · obtain ⟨p, hp, ha, hB⟩ := ih a B hlenB havB S hS htwo hau hbuB
        refine ⟨p, hp, ha, ?_⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hb.map _
        · exact hB c hc
      · letI := quadraticExtensionField b hb
        letI := quadraticExtensionNumberField b hb
        let E := QuadraticAlgebra K b.val 0
        let f : Kˣ →* Eˣ := Units.map (algebraMap K E).toMonoidHom
        let SE := finitePlacesOverSet (E := E) S
        have hSE : SEᶜ.Finite := NormFiberAssembly.finite_preimage_under Sᶜ hS
        have havE : AvoidsSquares (f a) (B.map f) := by
          intro C hC hsq
          obtain ⟨D, hD, rfl⟩ := List.sublist_map_iff.mp hC
          have hh : IsSquare (f (a * D.prod)) := by
            simpa only [map_mul, map_list_prod] using hsq
          rcases (square_base_iff b hb (a * D.prod)).mp hh with h | h
          · exact hav D (hD.cons b) h
          · apply hav (b :: D) (hD.cons_cons b)
            simpa only [List.prod_cons, mul_assoc, mul_comm, mul_left_comm] using h
        have h2E : ∀ w ∈ SE, (2 : 𝓞 E) ∉ w.asIdeal :=
          fun w hw ↦ odd_above w (htwo (w.under (𝓞 K)) hw)
        have haE : f a ∈ sUnitSubgroup SE := SUnitNormFiniteness.base_embedding_mem S a hau
        have hBE : ∀ c ∈ B.map f, c ∈ sUnitSubgroup SE := by
          intro c hc
          obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
          exact SUnitNormFiniteness.base_embedding_mem S d (hbuB d hd)
        obtain ⟨w, hw, han, hBs⟩ := ih (f a) (B.map f) (by simpa using hlenB)
          havE SE hSE h2E haE hBE
        let p := w.under (𝓞 K)
        have haF : ¬ IsSquare (algebraMap E (w.adicCompletion E) (algebraMap K E a.val)) := by
          intro h
          exact han ((GlobalSquare.unit_square_iff _).mpr h)
        have hanp : ¬ IsSquare
            (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom a) := by
          intro h
          exact nonsquare_under w a.val haF ((GlobalSquare.unit_square_iff _).mp h)
        refine ⟨p, hw, hanp, ?_⟩
        intro c hc
        apply square_under_of_nonsquare w a c (htwo p hw) (hau p hw) (hbu c hc p hw) haF
        rcases List.mem_cons.mp hc with hcb | hc
        · subst c
          have hs : IsSquare (algebraMap K E b.val) := by
            refine ⟨(QuadraticAlgebra.omega : E), ?_⟩
            apply QuadraticAlgebra.ext
            · change b.val = 0 * 0 + b.val * 1 * 1
              ring
            · change (0 : K) = 0 * 1 + 1 * 0 + 0 * 1 * 1
              ring
          exact hs.map (algebraMap E (w.adicCompletion E)).toMonoidHom
        · have hlocal := hBs (f c) (List.mem_map.mpr ⟨c, hc, rfl⟩)
          exact (GlobalSquare.unit_square_iff _).mp hlocal

end NormEuclidean.SquarePrimeSelection
