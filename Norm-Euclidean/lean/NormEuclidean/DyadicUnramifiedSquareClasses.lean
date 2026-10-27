import NormEuclidean.UnramifiedCompletionValuation
import NormEuclidean.Reuse.Bong.Bong.MaximalDefectClassProof
import Bong.Bong.ResidueDefectProductProof

/-!
# The dyadic unramified defect bound

O'Meara 63:3: a square root in an extension preserving normalized order
forces relative quadratic defect at least `2e`. The proof transports an
exact principal-unit representative to the extension and contradicts the
oddness of a defect strictly below `2e` using the square-difference lemma.
The number-field endpoint uses the actual unramified completion map.
-/

noncomputable section

namespace NormEuclidean.DyadicUnramifiedSquareClasses

open Bong Bong.Dyadic IsDedekindDomain ExtensionIdeleNorm QuadraticExtensionNorm
open scoped NumberField QuadraticAlgebra

section Local

variable {F B : Type*} [Field F] [CharZero F] [ValuativeRel F]
  [TopologicalSpace F] [DyadicContext F]
  [Field B] [CharZero B] [ValuativeRel B] [TopologicalSpace B] [DyadicContext B]

/-- The ramification index of two agrees under an order-preserving embedding. -/
theorem ramificationIndex_eq (f : F →+* B) (hord : ∀ a, ord B (f a) = ord F a) :
    ramificationIndex B = ramificationIndex F := by
  have h := hord 2
  rw [map_ofNat, ← ramificationIndex_spec, ← ramificationIndex_spec] at h
  exact_mod_cast h

/-- An order-preserving square root forces the unramified relative defect bound. -/
theorem defect_ge_twoE_of_root (f : F →+* B) (hord : ∀ a, ord B (f a) = ord F a)
    (q : Fˣ) (x : B) (hx : x ^ 2 = f (q : F)) :
    ((2 * ramificationIndex F : ℕ) : ℕ∞) ≤ quadraticDefect F q := by
  letI : QuadraticDefectLaws F := quadraticDefectLawsOfHensel F
  letI : UnitQuadraticDefectParityLaws F := unitQuadraticDefectParityLawsProved
  by_contra! hlt
  have hfinite : quadraticDefect F q ≠ ⊤ := ne_top_of_lt (hlt.trans (ENat.coe_lt_top _))
  have hx0 : x ≠ 0 := by
    intro hz
    exact (f.injective.ne q.ne_zero) (by simpa [hz] using hx.symm)
  let xu : Bˣ := Units.mk0 x hx0
  have hqEven : Even (ordUnit F q) := by
    have horder : ordUnit F q = 2 * ordUnit B xu := by
      apply WithTop.coe_injective
      rw [two_mul, WithTop.coe_add, coe_ordUnit, coe_ordUnit]
      change ord F (q : F) = ord B x + ord B x
      rw [← hord, ← hx, AddValuation.map_pow, two_smul]
    rw [horder]
    exact even_two_mul _
  have hnonzero : quadraticDefect F q ≠ 0 := by
    intro hz
    exact Int.not_odd_iff_even.mpr hqEven (odd_ordUnit_of_quadraticDefect_eq_zero q hz)
  obtain ⟨v, r, t, hvUnit, hvDefect, hfactor, hvField, htOrder⟩ :=
    BONG.exists_exact_principal_representation q hfinite hnonzero
  have hvLt : quadraticDefect F v < ((2 * ramificationIndex F : ℕ) : ℕ∞) := by
    rwa [hvDefect]
  have hdOdd : Odd (quadraticDefect F q).toNat := by
    simpa only [hvDefect] using
      quadraticDefect_toNat_odd_of_unit_of_lt_two_mul_e (K := F) v hvUnit hvLt
  let d := (quadraticDefect F q).toNat
  have hdPos : 0 < d := by
    obtain ⟨m, hm⟩ := hdOdd
    dsimp only [d]
    omega
  have hdLt : (d : ℤ) < 2 * (ramificationIndex B : ℤ) := by
    rw [ramificationIndex_eq f hord]
    have hcast : quadraticDefect F q = (d : ℕ∞) := (ENat.coe_toNat hfinite).symm
    rw [hcast] at hlt
    exact_mod_cast hlt
  let y : B := x / f (r : F)
  have hy2 : y ^ 2 = f (v : F) := by
    have hq : (q : F) = (v : F) * (r : F) ^ 2 := by
      exact congrArg Units.val hfactor
    dsimp only [y]
    rw [div_pow, hx, hq, map_mul, map_pow]
    exact mul_div_cancel_right₀ _
      (pow_ne_zero _ (by simpa only [map_zero] using f.injective.ne r.ne_zero))
  have horder : ord B (1 - y ^ 2) = ((d : ℤ) : WithTop ℤ) := by
    rw [hy2, ← map_one f, ← map_sub, hord]
    have heq : (1 : F) - (v : F) = -t := by rw [hvField]; ring
    rw [heq, ord_neg]
    exact htOrder
  have hdEven := even_order_one_sub_sq_of_lt_two_mul_e_proved y (d : ℤ)
    horder (by exact_mod_cast hdPos) hdLt
  have hdOddInt : Odd (d : ℤ) := by exact_mod_cast hdOdd
  exact Int.not_odd_iff_even.mpr hdEven hdOddInt

end Local

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- Actual nonramification above a dyadic prime gives the completed `2e` defect bound. -/
theorem quadratic_defect_ge_twoE (theta : Kˣ) (htheta : ¬ IsSquare theta)
    (p : HeightOneSpectrum (𝓞 K)) (hp : (2 : 𝓞 K) ∈ p.asIdeal)
    (hunram : letI := quadraticExtensionField theta htheta
      letI := quadraticExtensionNumberField theta htheta
      ∀ w : FinitePlacesAbove (E := QuadraticAlgebra K (theta : K) 0) p,
        Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal) :
    letI := Bong.NumberFieldCompletion.dyadicContext p hp
    ((2 * ramificationIndex (p.adicCompletion K) : ℕ) : ℕ∞) ≤
      quadraticDefect (p.adicCompletion K)
        (Units.map (algebraMap K (p.adicCompletion K)).toMonoidHom theta) := by
  letI := quadraticExtensionField theta htheta
  letI := quadraticExtensionNumberField theta htheta
  letI := Bong.NumberFieldCompletion.dyadicContext p hp
  obtain ⟨w⟩ := finitePlacesAbove_nonempty (E := QuadraticAlgebra K (theta : K) 0) p
  letI : w.1.asIdeal.LiesOver p.asIdeal :=
    ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩
  have hwp : (2 : 𝓞 (QuadraticAlgebra K (theta : K) 0)) ∈ w.1.asIdeal := by
    have hm : algebraMap (𝓞 K) (𝓞 (QuadraticAlgebra K (theta : K) 0)) 2 ∈
        w.1.asIdeal := by
      change (2 : 𝓞 K) ∈ w.1.asIdeal.under (𝓞 K)
      rw [← Ideal.over_def w.1.asIdeal p.asIdeal]
      exact hp
    simpa only [map_ofNat] using hm
  letI := Bong.NumberFieldCompletion.dyadicContext w.1 hwp
  letI : CharZero (p.adicCompletion K) := Algebra.charZero_of_charZero K _
  letI : CharZero (w.1.adicCompletion (QuadraticAlgebra K (theta : K) 0)) :=
    Algebra.charZero_of_charZero (QuadraticAlgebra K (theta : K) 0) _
  apply defect_ge_twoE_of_root (finitePlaceAboveCompletionMap p w)
    (fun a ↦ UnramifiedCompletionValuation.adicOrder_map p w (hunram w) a)
    _ (algebraMap (QuadraticAlgebra K (theta : K) 0) _ ω)
  change (algebraMap (QuadraticAlgebra K (theta : K) 0) _ ω) ^ 2 =
    finitePlaceAboveCompletionMap p w (algebraMap K (p.adicCompletion K) (theta : K))
  calc
    _ = algebraMap (QuadraticAlgebra K (theta : K) 0) _
        ((ω : QuadraticAlgebra K (theta : K) 0) ^ 2) := (map_pow _ _ _).symm
    _ = algebraMap (QuadraticAlgebra K (theta : K) 0) _
        (algebraMap K (QuadraticAlgebra K (theta : K) 0) (theta : K)) := by
      congr 1
      ext <;> simp [pow_two]
    _ = _ := (finitePlaceAboveCompletionMap_global p w (theta : K)).symm

end NormEuclidean.DyadicUnramifiedSquareClasses
