import TraceEuclidean.V15QuarticOrderMaximality

/-!
# Maximality of the quartic order in the `2304` branch

For the polynomial `X^4 - 4 X^2 + 1`, the preceding module removes every
`2`-primary denominator and shows that multiplication by `9` sends each
algebraic integer into the power order.  This module proves `3`-saturation.

The proof writes `3 z = A + B a + C a^2 + D a^3` and uses integrality of
the traces of `z`, `z^2`, and `z^4`.  Their exact trace identities force
`3` to divide all four coefficients.  Applying the saturation theorem twice
shows that the power order is the full ring of integers and hence that the
field discriminant is exactly `2304`.
-/

namespace TraceEuclidean

noncomputable section

open NumberField Module Polynomial
open scoped NumberField

private def v15Quartic2304T1 (A _B C _D : ℤ) : ℤ := A + 2 * C

private def v15Quartic2304T2 (A B C D : ℤ) : ℤ :=
  A ^ 2 + 4 * A * C + 2 * B ^ 2 + 14 * B * D +
    7 * C ^ 2 + 26 * D ^ 2

private def v15Quartic2304T4 (A B C D : ℤ) : ℤ :=
  A ^ 4 + 8 * A ^ 3 * C + 12 * A ^ 2 * B ^ 2 +
    84 * A ^ 2 * B * D + 42 * A ^ 2 * C ^ 2 +
    156 * A ^ 2 * D ^ 2 + 84 * A * B ^ 2 * C +
    624 * A * B * C * D + 104 * A * C ^ 3 +
    1164 * A * C * D ^ 2 + 7 * B ^ 4 + 104 * B ^ 3 * D +
    156 * B ^ 2 * C ^ 2 + 582 * B ^ 2 * D ^ 2 +
    1164 * B * C ^ 2 * D + 1448 * B * D ^ 3 + 97 * C ^ 4 +
    2172 * C ^ 2 * D ^ 2 + 1351 * D ^ 4

private def v15Quartic2304U2 (A B c d : ℤ) : ℤ :=
  4 * A ^ 2 + 18 * A * c + 14 * B ^ 2 + 66 * B * d +
    21 * c ^ 2 + 78 * d ^ 2

private def v15Quartic2304U4 (A B c d : ℤ) : ℤ :=
  28 * A ^ 4 + 264 * A ^ 3 * c + 624 * A ^ 2 * B ^ 2 +
    2952 * A ^ 2 * B * d + 936 * A ^ 2 * c ^ 2 +
    3492 * A ^ 2 * d ^ 2 + 2952 * A * B ^ 2 * c +
    13968 * A * B * c * d + 1476 * A * c ^ 3 +
    16524 * A * c * d ^ 2 + 388 * B ^ 4 + 3672 * B ^ 3 * d +
    3492 * B ^ 2 * c ^ 2 + 13032 * B ^ 2 * d ^ 2 +
    16524 * B * c ^ 2 * d + 20556 * B * d ^ 3 + 873 * c ^ 4 +
    19548 * c ^ 2 * d ^ 2 + 12159 * d ^ 4

private def v15Quartic2304U4Quot (A B c d : ℤ) : ℤ :=
  9 * A ^ 4 + 88 * A ^ 3 * c + 208 * A ^ 2 * B ^ 2 +
    984 * A ^ 2 * B * d + 312 * A ^ 2 * c ^ 2 +
    1164 * A ^ 2 * d ^ 2 + 984 * A * B ^ 2 * c +
    4656 * A * B * c * d + 492 * A * c ^ 3 +
    5508 * A * c * d ^ 2 + 129 * B ^ 4 + 1224 * B ^ 3 * d +
    1164 * B ^ 2 * c ^ 2 + 4344 * B ^ 2 * d ^ 2 +
    5508 * B * c ^ 2 * d + 6852 * B * d ^ 3 + 291 * c ^ 4 +
    6516 * c ^ 2 * d ^ 2 + 4053 * d ^ 4

/-- The three trace divisibilities required by the `2304` row force every
coefficient of a reduced power-basis expression to be divisible by `3`. -/
theorem v15_quartic_2304_coefficients_divisible_by_three (A B C D : ℤ)
    (h1 : (3 : ℤ) ∣ v15Quartic2304T1 A B C D)
    (h2 : (9 : ℤ) ∣ v15Quartic2304T2 A B C D)
    (h4 : (81 : ℤ) ∣ v15Quartic2304T4 A B C D) :
    (3 : ℤ) ∣ A ∧ (3 : ℤ) ∣ B ∧
      (3 : ℤ) ∣ C ∧ (3 : ℤ) ∣ D := by
  rcases h1 with ⟨r, hr⟩
  have hAC : (3 : ℤ) ∣ C - A := by
    refine ⟨C - r, ?_⟩
    dsimp [v15Quartic2304T1] at hr
    omega
  rcases hAC with ⟨c, hc⟩
  have hC : C = A + 3 * c := by omega
  have h2three : (3 : ℤ) ∣ v15Quartic2304T2 A B C D :=
    dvd_trans (by norm_num) h2
  have hsq : (3 : ℤ) ∣ (B - D) ^ 2 := by
    have haux : (3 : ℤ) ∣ v15Quartic2304T2 A B C D + (B - D) ^ 2 := by
      refine ⟨4 * A ^ 2 + 18 * A * c + B ^ 2 + 4 * B * D +
        9 * D ^ 2 + 21 * c ^ 2, ?_⟩
      rw [hC]
      simp only [v15Quartic2304T2]
      ring
    have hsub := dvd_sub haux h2three
    simpa only [add_sub_cancel_left] using hsub
  have hBD : (3 : ℤ) ∣ B - D :=
    (show Prime (3 : ℤ) by norm_num).dvd_of_dvd_pow hsq
  rcases hBD with ⟨d, hd⟩
  have hD : D = B - 3 * d := by omega
  have hfactor2 : v15Quartic2304T2 A B C D = 3 * v15Quartic2304U2 A B c (-d) := by
    rw [hC, hD]
    simp only [v15Quartic2304T2, v15Quartic2304U2]
    ring
  rcases h2 with ⟨q, hq⟩
  have hv15Quartic2304U2 : (3 : ℤ) ∣ v15Quartic2304U2 A B c (-d) := by
    refine ⟨q, ?_⟩
    omega
  have hsqdiff : (3 : ℤ) ∣ A ^ 2 - B ^ 2 := by
    have haux : (3 : ℤ) ∣
        v15Quartic2304U2 A B c (-d) - (A ^ 2 - B ^ 2) := by
      refine ⟨A ^ 2 + 6 * A * c + 5 * B ^ 2 - 22 * B * d +
        7 * c ^ 2 + 26 * d ^ 2, ?_⟩
      simp only [v15Quartic2304U2]
      ring
    have hsub := dvd_sub hv15Quartic2304U2 haux
    simpa only [sub_sub_cancel] using hsub
  by_cases hA : (3 : ℤ) ∣ A
  · have hBsq : (3 : ℤ) ∣ B ^ 2 := by
      have hA2 : (3 : ℤ) ∣ A ^ 2 := dvd_pow hA (by norm_num)
      have hsub := dvd_sub hA2 hsqdiff
      simpa only [sub_sub_cancel] using hsub
    have hB : (3 : ℤ) ∣ B :=
      (show Prime (3 : ℤ) by norm_num).dvd_of_dvd_pow hBsq
    have hCdiv : (3 : ℤ) ∣ C := by
      rw [hC]
      exact dvd_add hA (dvd_mul_right 3 c)
    have hDdiv : (3 : ℤ) ∣ D := by
      rw [hD]
      exact dvd_sub hB (dvd_mul_right 3 d)
    exact ⟨hA, hB, hCdiv, hDdiv⟩
  · have hfactor4 : v15Quartic2304T4 A B C D = 9 * v15Quartic2304U4 A B c (-d) := by
      rw [hC, hD]
      simp only [v15Quartic2304T4, v15Quartic2304U4]
      ring
    rcases h4 with ⟨q4, hq4⟩
    have hu4nine : (9 : ℤ) ∣ v15Quartic2304U4 A B c (-d) := by
      refine ⟨q4, ?_⟩
      omega
    have hu4three : (3 : ℤ) ∣ v15Quartic2304U4 A B c (-d) :=
      dvd_trans (by norm_num) hu4nine
    have hu4mod : (3 : ℤ) ∣
        v15Quartic2304U4 A B c (-d) - (A ^ 4 + B ^ 4) := by
      refine ⟨v15Quartic2304U4Quot A B c (-d), ?_⟩
      simp only [v15Quartic2304U4, v15Quartic2304U4Quot]
      ring
    have hsumDiv : (3 : ℤ) ∣ A ^ 4 + B ^ 4 := by
      have hsub := dvd_sub hu4three hu4mod
      simpa only [sub_sub_cancel] using hsub
    have hdiffz : ((A ^ 2 - B ^ 2 : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 hsqdiff
    have hABz : ((A : ZMod 3) ^ 2) = (B : ZMod 3) ^ 2 := by
      push_cast at hdiffz
      exact sub_eq_zero.mp hdiffz
    have hAz : (A : ZMod 3) ≠ 0 := by
      intro hz
      exact hA ((ZMod.intCast_zmod_eq_zero_iff_dvd A 3).1 hz)
    have hU : (A : ZMod 3) ^ 4 + (B : ZMod 3) ^ 4 = 0 := by
      have hsumz : (((A ^ 4 + B ^ 4 : ℤ) : ZMod 3)) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 hsumDiv
      push_cast at hsumz
      exact hsumz
    have htwice : (2 : ZMod 3) * (((A : ZMod 3) ^ 2) ^ 2) = 0 := by
      calc
        (2 : ZMod 3) * (((A : ZMod 3) ^ 2) ^ 2) =
            ((A : ZMod 3) ^ 2) ^ 2 +
              ((A : ZMod 3) ^ 2) ^ 2 := by ring
        _ = (A : ZMod 3) ^ 4 + (B : ZMod 3) ^ 4 := by
          congr 1
          · ring
          · rw [hABz]
            ring
        _ = 0 := hU
    rcases mul_eq_zero.mp htwice with htwo | hzero
    · exact ((by decide : (2 : ZMod 3) ≠ 0) htwo).elim
    · exact ((pow_ne_zero 2 (pow_ne_zero 2 hAz)) hzero).elim

set_option maxHeartbeats 4000000 in
-- Expanding the fourth power of the symbolic multiplication matrix is costly.
/-- Exact first, second, and fourth power-trace identities for the `2304`
quartic row. -/
theorem v15_quartic_2304_trace_identities
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤)
    (hs1 : v15QuarticS1 K a = 0)
    (hs2 : v15QuarticS2 K a = -4)
    (hs3 : v15QuarticS3 K a = 0)
    (hs4 : v15QuarticS4 K a = 1)
    (A B C D : ℤ) :
    let y : K := algebraMap ℤ K A + algebraMap ℤ K B * (a : K) +
      algebraMap ℤ K C * (a : K) ^ 2 +
      algebraMap ℤ K D * (a : K) ^ 3
    Algebra.trace ℚ K y = ((4 * v15Quartic2304T1 A B C D : ℤ) : ℚ) ∧
      Algebra.trace ℚ K (y ^ 2) = ((4 * v15Quartic2304T2 A B C D : ℤ) : ℚ) ∧
      Algebra.trace ℚ K (y ^ 4) = ((4 * v15Quartic2304T4 A B C D : ℤ) : ℚ) := by
  dsimp only
  let hint : IsIntegral ℚ (a : K) := IsIntegral.of_finite ℚ (a : K)
  let hsub : Algebra.adjoin ℚ {(a : K)} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hint.isAlgebraic hgen
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hint hsub
  have hgenpb : pb.gen = (a : K) := by
    simp [pb, PowerBasis.ofAdjoinEqTop]
  have hdim : pb.dim = 4 := by
    rw [PowerBasis.ofAdjoinEqTop_dim]
    exact (PowerBasis.finrank pb).symm.trans hdegree
  have hpbint : IsIntegral ℤ pb.gen := by
    rw [hgenpb]
    exact a.isIntegral_coe
  have hmin : minpoly ℤ pb.gen = v15QuarticPolynomial 0 (-4) 0 1 := by
    rw [hgenpb, ← v15_quarticPolynomial_eq_minpoly
      K hdegree a hgen, hs1, hs2, hs3, hs4]
  have hminMap : pb.minpolyGen =
      (minpoly ℤ pb.gen).map (algebraMap ℤ ℚ) := by
    rw [pb.minpolyGen_eq]
    exact minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hpbint
  let e : Fin pb.dim ≃ Fin 4 := finCongr hdim
  let M := Matrix.reindexAlgEquiv ℚ ℚ e
    (Algebra.leftMulMatrix pb.basis pb.gen)
  have hM : M =
      !![0, 0, 0, -1;
         1, 0, 0, 0;
         0, 1, 0, 4;
         0, 0, 1, 0] := by
    change Matrix.reindexAlgEquiv ℚ ℚ e
      (Algebra.leftMulMatrix pb.basis pb.gen) = _
    rw [v15_powerBasis_companionMatrix_dim_four pb hdim,
      hminMap, hmin]
    simp [v15QuarticPolynomial, Polynomial.coeff_one]
  let y : K := algebraMap ℤ K A + algebraMap ℤ K B * (a : K) +
    algebraMap ℤ K C * (a : K) ^ 2 +
    algebraMap ℤ K D * (a : K) ^ 3
  let MY := Matrix.reindexAlgEquiv ℚ ℚ e
    (Algebra.leftMulMatrix pb.basis y)
  have hy : y = algebraMap ℚ K (A : ℚ) +
      algebraMap ℚ K (B : ℚ) * pb.gen +
      algebraMap ℚ K (C : ℚ) * pb.gen ^ 2 +
      algebraMap ℚ K (D : ℚ) * pb.gen ^ 3 := by
    simp [y, hgenpb]
  have hMY : MY =
      (A : ℚ) • 1 + (B : ℚ) • M +
        (C : ℚ) • M ^ 2 + (D : ℚ) • M ^ 3 := by
    change Matrix.reindexAlgEquiv ℚ ℚ e
      (Algebra.leftMulMatrix pb.basis y) = _
    rw [hy]
    simp only [map_add, map_mul, map_pow, AlgHom.commutes]
    simp [M, Algebra.smul_def]
  have htracePow (n : ℕ) :
      Algebra.trace ℚ K (y ^ n) = Matrix.trace (MY ^ n) := by
    rw [Algebra.trace_eq_matrix_trace pb.basis]
    calc
      Matrix.trace (Algebra.leftMulMatrix pb.basis (y ^ n)) =
          Matrix.trace (Matrix.reindexAlgEquiv ℚ ℚ e
            (Algebra.leftMulMatrix pb.basis (y ^ n))) :=
        (v15_matrix_trace_reindex e _).symm
      _ = Matrix.trace (MY ^ n) := by
        simp only [MY, map_pow]
  have h1 := htracePow 1
  have h2 := htracePow 2
  have h4 := htracePow 4
  rw [hMY, hM] at h1 h2 h4
  refine ⟨?_, ?_, ?_⟩
  · have ht : Algebra.trace ℚ K y = ((4 * v15Quartic2304T1 A B C D : ℤ) : ℚ) := by
      rw [show y = y ^ 1 by simp, h1]
      simp [Matrix.trace, Matrix.diag_apply,
        Fin.sum_univ_succ, v15Quartic2304T1, pow_succ]
      ring
    simpa only [y] using ht
  · have ht : Algebra.trace ℚ K (y ^ 2) =
        ((4 * v15Quartic2304T2 A B C D : ℤ) : ℚ) := by
      rw [h2]
      simp [Matrix.trace, Matrix.mul_apply, Matrix.diag_apply,
        Fin.sum_univ_succ, v15Quartic2304T2, pow_succ]
      ring
    simpa only [y] using ht
  · have ht : Algebra.trace ℚ K (y ^ 4) =
        ((4 * v15Quartic2304T4 A B C D : ℤ) : ℚ) := by
      rw [h4]
      simp [Matrix.trace, Matrix.mul_apply, Matrix.diag_apply,
        Fin.sum_univ_succ, v15Quartic2304T4, pow_succ]
      ring
    simpa only [y] using ht

private theorem v15_quartic_2304_trace_divisibility
    (K : Type*) [Field K] [NumberField K]
    (z y : K) (hzint : IsIntegral ℤ z)
    (hy : y = (3 : ℤ) • z) (k : ℕ) (T : ℤ)
    (htrace : Algebra.trace ℚ K (y ^ k) = ((4 * T : ℤ) : ℚ))
    (hcop : Int.gcd ((3 : ℤ) ^ k) 4 = 1) :
    (3 : ℤ) ^ k ∣ T := by
  have hztraceInt : IsIntegral ℤ (Algebra.trace ℚ K (z ^ k)) :=
    Algebra.isIntegral_trace (hzint.pow k)
  obtain ⟨n, hn⟩ :=
    (IsIntegrallyClosed.isIntegral_iff.mp hztraceInt)
  have hscale : Algebra.trace ℚ K (y ^ k) =
      (3 : ℚ) ^ k * Algebra.trace ℚ K (z ^ k) := by
    rw [hy]
    rw [← Int.cast_smul_eq_zsmul ℚ]
    change Algebra.trace ℚ K
        (((3 : ℚ) • z) ^ k) = _
    rw [Algebra.smul_def]
    rw [mul_pow, ← map_pow, ← Algebra.smul_def,
      LinearMap.map_smul, smul_eq_mul]
  have heqQ : ((4 * T : ℤ) : ℚ) =
      (((3 : ℤ) ^ k * n : ℤ) : ℚ) := by
    rw [← htrace, hscale, ← hn]
    norm_num
  have heqZ : (4 : ℤ) * T = (3 : ℤ) ^ k * n := by
    exact_mod_cast heqQ
  have hd : (3 : ℤ) ^ k ∣ (4 : ℤ) * T := ⟨n, heqZ⟩
  exact Int.dvd_of_dvd_mul_right_of_gcd_one hd hcop

set_option maxHeartbeats 6000000 in
-- This combines the symbolic trace identities with polynomial reduction.
/-- The power order in the `2304` row is saturated at `3`: an integral
element whose triple belongs to the power order already belongs to it. -/
theorem v15_quartic_2304_three_saturated
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤)
    (hs1 : v15QuarticS1 K a = 0)
    (hs2 : v15QuarticS2 K a = -4)
    (hs3 : v15QuarticS3 K a = 0)
    (hs4 : v15QuarticS4 K a = 1)
    (z : K) (hzint : IsIntegral ℤ z)
    (hz : (3 : ℤ) • z ∈ Algebra.adjoin ℤ {(a : K)}) :
    z ∈ Algebra.adjoin ℤ {(a : K)} := by
  have hmin : minpoly ℤ (a : K) =
      v15QuarticPolynomial 0 (-4) 0 1 := by
    rw [← v15_quarticPolynomial_eq_minpoly K hdegree a hgen,
      hs1, hs2, hs3, hs4]
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
  obtain ⟨Q₁, hQ⟩ := hz
  set P := minpoly ℤ (a : K) with hP
  set Q := Q₁ %ₘ P with hQ₁
  replace hQ : aeval (a : K) Q = (3 : ℤ) • z := by
    simpa [hQ₁, hP] using hQ
  have hPmonic : P.Monic := by
    rw [hP]
    exact minpoly.monic a.isIntegral_coe
  have hPnat : P.natDegree = 4 := by
    have hpoly : v15QuarticPolynomial 0 (-4) 0 1 =
        X ^ 4 + (-(4 * X ^ 2) + 1) := by
      simp [v15QuarticPolynomial]
      ring
    rw [hmin, hpoly, natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · compute_degree
      norm_num
  have hPne : P ≠ 1 := by
    intro heq
    rw [heq] at hPnat
    norm_num at hPnat
  have hQdeg : Q.natDegree < 4 := by
    rw [hQ₁, ← hPnat]
    exact natDegree_modByMonic_lt Q₁ hPmonic hPne
  let A := Q.coeff 0
  let B := Q.coeff 1
  let C := Q.coeff 2
  let D := Q.coeff 3
  let y : K := algebraMap ℤ K A + algebraMap ℤ K B * (a : K) +
    algebraMap ℤ K C * (a : K) ^ 2 +
    algebraMap ℤ K D * (a : K) ^ 3
  have hQeval : aeval (a : K) Q = y := by
    rw [aeval_eq_sum_range' hQdeg]
    simp [y, A, B, C, D, Finset.sum_range_succ,
      Algebra.smul_def]
  have hy : y = (3 : ℤ) • z := by
    rw [← hQ, hQeval]
  have htraces :
      Algebra.trace ℚ K y = ((4 * v15Quartic2304T1 A B C D : ℤ) : ℚ) ∧
      Algebra.trace ℚ K (y ^ 2) = ((4 * v15Quartic2304T2 A B C D : ℤ) : ℚ) ∧
      Algebra.trace ℚ K (y ^ 4) = ((4 * v15Quartic2304T4 A B C D : ℤ) : ℚ) := by
    simpa only [y] using
      (v15_quartic_2304_trace_identities K hdegree a hgen hs1 hs2 hs3 hs4 A B C D)
  have hd1 : (3 : ℤ) ∣ v15Quartic2304T1 A B C D := by
    have hv15Quartic2304T1 : Algebra.trace ℚ K (y ^ 1) =
        ((4 * v15Quartic2304T1 A B C D : ℤ) : ℚ) := by
      simpa using htraces.1
    simpa using v15_quartic_2304_trace_divisibility K z y hzint hy 1 (v15Quartic2304T1 A B C D)
      hv15Quartic2304T1 (by norm_num)
  have hd2 : (9 : ℤ) ∣ v15Quartic2304T2 A B C D := by
    simpa using v15_quartic_2304_trace_divisibility K z y hzint hy 2 (v15Quartic2304T2 A B C D)
      htraces.2.1 (by norm_num)
  have hd4 : (81 : ℤ) ∣ v15Quartic2304T4 A B C D := by
    simpa using v15_quartic_2304_trace_divisibility K z y hzint hy 4 (v15Quartic2304T4 A B C D)
      htraces.2.2 (by norm_num)
  obtain ⟨hA, hB, hC, hD⟩ := v15_quartic_2304_coefficients_divisible_by_three A B C D hd1 hd2 hd4
  refine mem_adjoin_of_dvd_coeff_of_dvd_aeval (by norm_num) ?_ hQ
  intro i hi
  have hi4 : i < 4 := by
    have hiQ : i < Q.natDegree + 1 := Finset.mem_range.mp hi
    omega
  interval_cases i
  · simpa only [A] using hA
  · simpa only [B] using hB
  · simpa only [C] using hC
  · simpa only [D] using hD

/-- Every algebraic integer in the `2304` row belongs to the power order. -/
theorem v15_quartic_2304_all_integral_mem_adjoin
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤)
    (hs1 : v15QuarticS1 K a = 0)
    (hs2 : v15QuarticS2 K a = -4)
    (hs3 : v15QuarticS3 K a = 0)
    (hs4 : v15QuarticS4 K a = 1) :
    ∀ x : K, IsIntegral ℤ x →
      x ∈ Algebra.adjoin ℤ {(a : K)} := by
  intro x hx
  have h9 := v15_quartic_2304_nine_smul_integral_mem_adjoin
    K hdegree a hgen hs1 hs2 hs3 hs4 x hx
  have h3xInt : IsIntegral ℤ ((3 : ℤ) • x) := hx.smul 3
  have h3 : (3 : ℤ) • x ∈ Algebra.adjoin ℤ {(a : K)} := by
    apply v15_quartic_2304_three_saturated K hdegree a hgen hs1 hs2 hs3 hs4
      ((3 : ℤ) • x) h3xInt
    convert h9 using 1
    simp [zsmul_eq_mul]
    ring
  exact v15_quartic_2304_three_saturated K hdegree a hgen hs1 hs2 hs3 hs4 x hx h3

/-- The `2304` generator generates the full ring of integers as a
`ℤ`-algebra. -/
theorem v15_quartic_2304_adjoin_ringOfIntegers_eq_top
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤)
    (hs1 : v15QuarticS1 K a = 0)
    (hs2 : v15QuarticS2 K a = -4)
    (hs3 : v15QuarticS3 K a = 0)
    (hs4 : v15QuarticS4 K a = 1) :
    Algebra.adjoin ℤ ({a} : Set (𝓞 K)) = ⊤ := by
  apply top_unique
  intro z _
  let f : 𝓞 K →ₐ[ℤ] K := IsScalarTower.toAlgHom ℤ (𝓞 K) K
  have hz : (z : K) ∈ Algebra.adjoin ℤ ({(a : K)} : Set K) :=
    v15_quartic_2304_all_integral_mem_adjoin K hdegree a hgen hs1 hs2 hs3 hs4
      z z.isIntegral_coe
  have hmap :
      Subalgebra.map f (Algebra.adjoin ℤ ({a} : Set (𝓞 K))) =
        Algebra.adjoin ℤ ({(a : K)} : Set K) := by
    rw [AlgHom.map_adjoin_singleton]
    rfl
  rw [← hmap] at hz
  obtain ⟨y, hy, hyz⟩ := hz
  have : y = z := by
    apply Subtype.ext
    exact hyz
  rwa [this] at hy

/-- A quartic field generated by the `2304` row has field discriminant
exactly `2304`. -/
theorem v15_quartic_field_discriminant_eq_2304
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤)
    (hs1 : v15QuarticS1 K a = 0)
    (hs2 : v15QuarticS2 K a = -4)
    (hs3 : v15QuarticS3 K a = 0)
    (hs4 : v15QuarticS4 K a = 1) :
    NumberField.discr K = 2304 := by
  classical
  let htop : Algebra.adjoin ℤ ({a} : Set (𝓞 K)) = ⊤ :=
    v15_quartic_2304_adjoin_ringOfIntegers_eq_top K hdegree a hgen hs1 hs2 hs3 hs4
  let pb : PowerBasis ℤ (𝓞 K) :=
    PowerBasis.ofAdjoinEqTop' (RingOfIntegers.isIntegral a) htop
  have hdim : pb.dim = 4 := by
    rw [← PowerBasis.finrank, RingOfIntegers.rank, hdegree]
  let e : Fin pb.dim ≃ Fin 4 := finCongr hdim
  have hfamily : Algebra.discr ℤ (v15QuarticPowerFamily K a) =
      Algebra.discr ℤ pb.basis := by
    rw [← Algebra.discr_reindex ℤ pb.basis e]
    congr 1
    ext i
    simp only [Function.comp_apply]
    apply congrArg (fun z : 𝓞 K ↦ (z : K))
    change v15QuarticPowerFamily K a i = pb.basis (e.symm i)
    rw [pb.basis_eq_pow]
    have he : ((e.symm i : Fin pb.dim) : ℕ) = (i : ℕ) := rfl
    rw [he]
    fin_cases i <;> simp [v15QuarticPowerFamily, pb]
  calc
    NumberField.discr K = Algebra.discr ℤ pb.basis :=
      (NumberField.discr_eq_discr K pb.basis).symm
    _ = Algebra.discr ℤ (v15QuarticPowerFamily K a) := hfamily.symm
    _ = v15QuarticDiscriminant (v15QuarticS1 K a)
        (v15QuarticS2 K a) (v15QuarticS3 K a)
        (v15QuarticS4 K a) :=
      v15_quarticPowerFamily_discr_eq_quarticDiscriminant
        K hdegree a hgen
    _ = 2304 := by
      rw [hs1, hs2, hs3, hs4]
      norm_num [v15QuarticDiscriminant]

/-- Under the field-discriminant interval used in the weak Minkowski route,
no primitive quartic generator can satisfy the spread bound.  The preceding
module reduces such a generator to the `2304` row, whose order is now known
to be maximal and therefore has discriminant `2304`, contradicting the
upper bound `725`. -/
theorem v15_quartic_weak_minkowski_contradiction
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 4)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤)
    (hspreadLt : v15QuarticSpread (v15QuarticS1 K a)
      (v15QuarticS2 K a) < 35)
    (hfieldLower : 29 < NumberField.discr K)
    (hfieldUpper : NumberField.discr K < 725) : False := by
  rcases v15_quartic_weak_minkowski_normalized_row_2304
      K hreal hdegree a hgen hspreadLt hfieldLower hfieldUpper with
    ⟨b, hgenb, hs1, hs2, hs3, hs4⟩
  have hfield := v15_quartic_field_discriminant_eq_2304
    K hdegree b hgenb hs1 hs2 hs3 hs4
  omega

end
end TraceEuclidean

