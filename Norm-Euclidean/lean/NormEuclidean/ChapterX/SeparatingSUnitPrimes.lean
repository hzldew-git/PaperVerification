import NormEuclidean.ChapterX.SquareClassBasis
import NormEuclidean.ChapterX.PrimeSquareDetection

/-!
# O'Meara 65:18 with a prescribed quadratic parameter

An actual S-unit square-class basis containing the given nonsquare
parameter supplies the independence conditions of simultaneous prime
selection. The selected primes are distinct and lie in S.
-/

noncomputable section

namespace NormEuclidean.SeparatingSUnitPrimes

open IsDedekindDomain ExtensionIdeleNorm SUnitNormArithmetic PrimeSquareDetection
open SquarePrimeSelection
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- A square root of an actual S-unit is itself an S-unit. -/
theorem square_root_mem (S : Set (HeightOneSpectrum (𝓞 K)))
    (x : sUnitSubgroup S) (hs : IsSquare x.val) : IsSquare x := by
  obtain ⟨r, hr⟩ := hs
  have hu : r ∈ sUnitSubgroup S := by
    intro p hp
    have hx := x.property p hp
    have he := congrArg Units.val hr
    change x.val.val = r.val * r.val at he
    rw [he, map_mul] at hx
    apply (pow_eq_one_iff_of_nonneg bot_le (by decide : 2 ≠ 0)).mp
    simpa only [pow_two] using hx
  exact ⟨⟨r, hu⟩, Subtype.ext hr⟩

/-- Distinct actual primes separate a full S-unit square-class family containing theta. -/
theorem exists_separating_family (S : Set (HeightOneSpectrum (𝓞 K))) (hS : Sᶜ.Finite)
    (htwo : ∀ p ∈ S, (2 : 𝓞 K) ∉ p.asIdeal)
    (theta : Kˣ) (htheta : ¬ IsSquare theta) (hunit : theta ∈ sUnitSubgroup S) :
    ∃ (e : Fin (Module.finrank ℤ (Additive (sUnitSubgroup S)) + 1) → sUnitSubgroup S)
      (i₀ : Fin (Module.finrank ℤ (Additive (sUnitSubgroup S)) + 1))
      (p : Fin (Module.finrank ℤ (Additive (sUnitSubgroup S)) + 1) →
        HeightOneSpectrum (𝓞 K)),
      (e i₀).val = theta ∧ Separates S e p ∧ Function.Injective p := by
  classical
  let A := sUnitSubgroup S
  let M := Additive A
  let s := Module.finrank ℤ M + 1
  letI : Module.Finite ℤ M := SUnitFiniteness.moduleFinite_sUnits S hS
  let minus : A := ⟨-1, fun p _ ↦ by simp⟩
  have hcard : (SquareIndex.doubles M).index = 2 ^ s := by
    rw [FinitelyGeneratedSquareIndex.doubles_index,
      FieldSquareIndex.twoTorsion_card A.subtype A.subtype_injective minus rfl]
    exact (pow_succ 2 _).symm
  let x : M := Additive.ofMul ⟨theta, hunit⟩
  have hx : x ∉ SquareIndex.doubles M := by
    rintro ⟨y, hy⟩
    apply htheta
    refine ⟨y.toMul.val, ?_⟩
    change (2 : ℕ) • y = Additive.ofMul (⟨theta, hunit⟩ : A) at hy
    rw [two_nsmul] at hy
    have he : y.toMul * y.toMul = (⟨theta, hunit⟩ : A) := congrArg Additive.toMul hy
    exact (congrArg Subtype.val he).symm
  obtain ⟨eA, i₀, c, he₀, hc, hc2⟩ := SquareClassBasis.exists_coordinates M s hcard x hx
  let e (i : Fin s) : A := (eA i).toMul
  let B (i : Fin s) : List (Fin s) := (Finset.univ.erase i).toList
  have hnot (i : Fin s) :
      AvoidsSquares (e i).val ((B i).map (fun j ↦ (e j).val)) := by
    intro C hC hsq
    obtain ⟨D, hD, rfl⟩ := List.sublist_map_iff.mp hC
    let z : A := e i * (D.map e).prod
    have hzval : z.val = (e i).val * (D.map (fun j ↦ (e j).val)).prod := by
      change A.subtype (e i * (D.map e).prod) = _
      rw [map_mul, map_list_prod, List.map_map]
      rfl
    have hzsq : IsSquare z := square_root_mem S z (hzval.symm ▸ hsq)
    have hDne : ∀ j ∈ D, j ≠ i := by
      intro j hj
      exact (Finset.mem_erase.mp (Finset.mem_toList.mp (hD.subset hj))).1
    have hzero : ∀ L : List (Fin s), (∀ j ∈ L, j ≠ i) →
        c i (Additive.ofMul (L.map e).prod) = 0 := by
      intro L hL
      induction L with
      | nil => exact map_zero _
      | cons j L ih =>
        change c i (eA j + Additive.ofMul (L.map e).prod) = 0
        rw [map_add, hc i j, if_neg (hL j (by simp)).symm,
          ih (fun k hk ↦ hL k (by simp [hk])), add_zero]
    have hz1 : c i (Additive.ofMul z) = 1 := by
      change c i (eA i + Additive.ofMul (D.map e).prod) = 1
      rw [map_add, hc i i, if_pos rfl, hzero D hDne, add_zero]
    obtain ⟨r, hr⟩ := hzsq
    have hd : Additive.ofMul z = (2 : ℕ) • Additive.ofMul r := by
      rw [two_nsmul]
      exact congrArg Additive.ofMul hr
    have hz0 : c i (Additive.ofMul z) = 0 := by rw [hd]; exact hc2 i _
    rw [hz1] at hz0
    exact one_ne_zero hz0
  have hchoice (i : Fin s) : ∃ p ∈ S,
      ¬ IsSquare (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom (e i).val) ∧
      ∀ j ∈ B i, IsSquare
        (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom (e j).val) := by
    obtain ⟨p, hp, hn, hs⟩ := exists_pattern (B i).length (e i).val
      ((B i).map (fun j ↦ (e j).val)) (by simp) (hnot i) S hS htwo (e i).property
      (by intro b hb; obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb; exact (e j).property)
    exact ⟨p, hp, hn, fun j hj ↦ hs _ (List.mem_map.mpr ⟨j, hj, rfl⟩)⟩
  choose p hp hn hs using hchoice
  have hsep : Separates S e p := ⟨hp, hn, fun i j hij ↦
    hs i j (Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩))⟩
  refine ⟨e, i₀, p, congrArg (fun z : M ↦ z.toMul.val) he₀, hsep, ?_⟩
  intro i j hij
  by_contra hne
  have hlocal := hsep.2.2 i j hne
  rw [hij] at hlocal
  exact hn j hlocal

end NormEuclidean.SeparatingSUnitPrimes
