import TraceEuclidean.QuadraticFieldBridge
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.RingTheory.Trace.Basic

namespace TraceEuclidean

noncomputable section

abbrev RealQuadraticAlgebra (m : ℕ) := QuadraticAlgebra ℚ (m : ℚ) 0

theorem squarefreeNat_not_isSquare {m : ℕ}
    (hm : 1 < m) (hsq : IsSquarefreeNat m) : ¬ IsSquare m := by
  rintro ⟨k, hk⟩
  have hdiv : k * k ∣ m := ⟨1, by simpa [pow_two] using hk⟩
  have hk1 := hsq k hdiv
  have : m = 1 := by simpa [hk1] using hk
  omega

theorem realQuadratic_nonsquare {m : ℕ}
    (hm : 1 < m) (hsq : IsSquarefreeNat m) :
    ∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r := by
  intro r hr
  apply squarefreeNat_not_isSquare hm hsq
  simp only [zero_mul, add_zero] at hr
  rw [← Rat.isSquare_natCast_iff]
  exact ⟨r, by simpa [pow_two] using hr.symm⟩

theorem rat_den_sq_dvd_of_nat_mul_sq_isInt {m : ℕ} (q : ℚ)
    (h : ∃ c : ℤ, (c : ℚ) = (m : ℚ) * q ^ 2) :
    q.den * q.den ∣ m := by
  obtain ⟨c, hc⟩ := h
  have hdenq : (q.den : ℚ) ≠ 0 := by positivity
  have hrepr : q * (q.den : ℚ) = (q.num : ℚ) := by
    exact ((div_eq_iff hdenq).mp q.num_div_den).symm
  have heqQ :
      (m : ℚ) * (q.num : ℚ) ^ 2 =
        (c : ℚ) * (q.den : ℚ) ^ 2 := by
    rw [← hrepr]
    rw [hc]
    ring
  have heqZ :
      (m : ℤ) * q.num ^ 2 = c * (q.den : ℤ) ^ 2 := by
    exact_mod_cast heqQ
  have hdvdZ : (q.den : ℤ) ^ 2 ∣ (m : ℤ) * q.num ^ 2 := by
    refine ⟨c, ?_⟩
    rw [heqZ]
    ring
  have hdvdNat := Int.natAbs_dvd_natAbs.mpr hdvdZ
  simp only [Int.natAbs_pow, Int.natAbs_natCast, Int.natAbs_mul] at hdvdNat
  have hcop : (q.den ^ 2).Coprime (q.num.natAbs ^ 2) :=
    Nat.Coprime.pow 2 2 q.reduced.symm
  have hdvdM : q.den ^ 2 ∣ m := by
    apply hcop.dvd_of_dvd_mul_left
    simpa [mul_comm] using hdvdNat
  simpa [pow_two] using hdvdM

theorem rat_isInt_of_squarefree_mul_sq_isInt {m : ℕ}
    (hsq : IsSquarefreeNat m) (q : ℚ)
    (h : IsIntegral ℤ ((m : ℚ) * q ^ 2)) :
    ∃ c : ℤ, (c : ℚ) = q := by
  have hmq : ∃ c : ℤ, (c : ℚ) = (m : ℚ) * q ^ 2 :=
    IsIntegrallyClosed.isIntegral_iff.mp h
  have hden := rat_den_sq_dvd_of_nat_mul_sq_isInt q hmq
  have hden1 := hsq q.den hden
  exact ⟨q.num, by simpa [hden1] using (Rat.coe_int_num_of_den_eq_one hden1)⟩

theorem caseI_integer_parity {m : ℕ} {A B N : ℤ}
    (hmod : m % 4 = 2 ∨ m % 4 = 3)
    (hEq : A ^ 2 - (m : ℤ) * B ^ 2 = 4 * N) :
    ∃ a b : ℤ, A = 2 * a ∧ B = 2 * b := by
  rcases hmod with hm2 | hm3
  · have hmNat : m = 4 * (m / 4) + 2 := by omega
    have hm : (m : ℤ) = 4 * (m / 4 : ℕ) + 2 := by exact_mod_cast hmNat
    rcases Int.even_or_odd A with ⟨a, ha⟩ | ⟨a, ha⟩ <;>
      rcases Int.even_or_odd B with ⟨b, hb⟩ | ⟨b, hb⟩
    · exact ⟨a, b, by simpa [two_mul] using ha, by simpa [two_mul] using hb⟩
    all_goals exfalso; rw [ha, hb, hm] at hEq; ring_nf at hEq; omega
  · have hmNat : m = 4 * (m / 4) + 3 := by omega
    have hm : (m : ℤ) = 4 * (m / 4 : ℕ) + 3 := by exact_mod_cast hmNat
    rcases Int.even_or_odd A with ⟨a, ha⟩ | ⟨a, ha⟩ <;>
      rcases Int.even_or_odd B with ⟨b, hb⟩ | ⟨b, hb⟩
    · exact ⟨a, b, by simpa [two_mul] using ha, by simpa [two_mul] using hb⟩
    all_goals exfalso; rw [ha, hb, hm] at hEq; ring_nf at hEq; omega

theorem caseII_integer_parity {m : ℕ} {A B N : ℤ}
    (hmod : m % 4 = 1)
    (hEq : A ^ 2 - (m : ℤ) * B ^ 2 = 4 * N) :
    ∃ a b : ℤ, A = 2 * a + b ∧ B = b := by
  have hmNat : m = 4 * (m / 4) + 1 := by omega
  have hm : (m : ℤ) = 4 * (m / 4 : ℕ) + 1 := by exact_mod_cast hmNat
  rcases Int.even_or_odd A with ⟨a, ha⟩ | ⟨a, ha⟩ <;>
    rcases Int.even_or_odd B with ⟨b, hb⟩ | ⟨b, hb⟩
  · refine ⟨a - b, 2 * b, ?_, by simpa [two_mul] using hb⟩
    rw [ha]
    ring
  · exfalso
    rw [ha, hb, hm] at hEq
    ring_nf at hEq
    omega
  · exfalso
    rw [ha, hb, hm] at hEq
    ring_nf at hEq
    omega
  · refine ⟨a - b, 2 * b + 1, ?_, by simpa [two_mul] using hb⟩
    rw [ha]
    ring

section Model

variable {m : ℕ} [Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r)]

instance : NumberField (RealQuadraticAlgebra m) where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

theorem realQuadratic_trace (z : RealQuadraticAlgebra m) :
    Algebra.trace ℚ (RealQuadraticAlgebra m) z = 2 * z.re := by
  let b := QuadraticAlgebra.basis (m : ℚ) 0
  rw [Algebra.trace_eq_matrix_trace b]
  have hmatrix :
      Algebra.leftMulMatrix b z =
        !![z.re, (m : ℚ) * z.im; z.im, z.re] := by
    change LinearMap.toMatrix b b (Algebra.lmul ℚ (RealQuadraticAlgebra m) z) = _
    apply LinearEquiv.eq_symm_apply _ |>.mp
    ext1 w
    apply b.repr.injective
    apply DFunLike.coe_injective
    rw [LinearMap.toMatrix_symm, Matrix.repr_toLin]
    ext i
    fin_cases i <;> simp [b] <;> ring
  rw [hmatrix]
  simp [Matrix.trace]
  ring

theorem realQuadratic_norm (z : RealQuadraticAlgebra m) :
    Algebra.norm ℚ z = z.re ^ 2 - m * z.im ^ 2 := by
  rw [Algebra.norm_apply]
  change LinearMap.det
    (DistribSMul.toLinearMap ℚ (RealQuadraticAlgebra m) z) = _
  rw [QuadraticAlgebra.det_toLinearMap_eq_norm]
  simp [QuadraticAlgebra.norm_def]
  ring

theorem integral_has_doubled_coordinates
    (hsq : IsSquarefreeNat m) {z : RealQuadraticAlgebra m}
    (hz : IsIntegral ℤ z) :
    ∃ A B N : ℤ,
      (A : ℚ) = 2 * z.re ∧ (B : ℚ) = 2 * z.im ∧
        A ^ 2 - (m : ℤ) * B ^ 2 = 4 * N := by
  have htraceInt : IsIntegral ℤ
      (Algebra.trace ℚ (RealQuadraticAlgebra m) z) :=
    Algebra.isIntegral_trace hz
  rw [realQuadratic_trace] at htraceInt
  obtain ⟨A, hA⟩ := IsIntegrallyClosed.isIntegral_iff.mp htraceInt
  change (A : ℚ) = 2 * z.re at hA
  have hnormInt : IsIntegral ℤ
      (Algebra.norm ℚ z) := Algebra.isIntegral_norm ℚ hz
  rw [realQuadratic_norm] at hnormInt
  obtain ⟨N, hN⟩ := IsIntegrallyClosed.isIntegral_iff.mp hnormInt
  change (N : ℚ) = z.re ^ 2 - (m : ℚ) * z.im ^ 2 at hN
  have hmBInt : IsIntegral ℤ ((m : ℚ) * (2 * z.im) ^ 2) := by
    apply IsIntegrallyClosed.isIntegral_iff.mpr
    refine ⟨A ^ 2 - 4 * N, ?_⟩
    have hAsq := congrArg (fun q : ℚ ↦ q ^ 2) hA
    calc
      ((A ^ 2 - 4 * N : ℤ) : ℚ) =
          (A : ℚ) ^ 2 - 4 * (N : ℚ) := by
            simp only [Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat]
      _ = (2 * z.re) ^ 2 -
          4 * (z.re ^ 2 - (m : ℚ) * z.im ^ 2) := by rw [hAsq, hN]
      _ = (m : ℚ) * (2 * z.im) ^ 2 := by ring
  obtain ⟨B, hB⟩ := rat_isInt_of_squarefree_mul_sq_isInt hsq (2 * z.im) hmBInt
  refine ⟨A, B, N, hA, hB, ?_⟩
  have hEqQ :
      (A : ℚ) ^ 2 - (m : ℚ) * (B : ℚ) ^ 2 = 4 * (N : ℚ) := by
    have hAsq := congrArg (fun q : ℚ ↦ q ^ 2) hA
    have hBsq := congrArg (fun q : ℚ ↦ q ^ 2) hB
    calc
      (A : ℚ) ^ 2 - (m : ℚ) * (B : ℚ) ^ 2 =
          (2 * z.re) ^ 2 - (m : ℚ) * (2 * z.im) ^ 2 := by
            rw [hAsq, hBsq]
      _ = 4 * (N : ℚ) := by rw [hN]; ring
  exact_mod_cast hEqQ

theorem integral_coordinates_caseI
    (hsq : IsSquarefreeNat m) (hmod : m % 4 = 2 ∨ m % 4 = 3)
    {z : RealQuadraticAlgebra m} (hz : IsIntegral ℤ z) :
    ∃ a b : ℤ, z.re = a ∧ z.im = b := by
  obtain ⟨A, B, N, hA, hB, hEq⟩ := integral_has_doubled_coordinates hsq hz
  obtain ⟨a, b, ha, hb⟩ := caseI_integer_parity hmod hEq
  refine ⟨a, b, ?_, ?_⟩
  · rw [ha] at hA
    push_cast at hA
    linarith
  · rw [hb] at hB
    push_cast at hB
    linarith

theorem integral_coordinates_caseII
    (hsq : IsSquarefreeNat m) (hmod : m % 4 = 1)
    {z : RealQuadraticAlgebra m} (hz : IsIntegral ℤ z) :
    ∃ a b : ℤ, z.re = a + b / 2 ∧ z.im = b / 2 := by
  obtain ⟨A, B, N, hA, hB, hEq⟩ := integral_has_doubled_coordinates hsq hz
  obtain ⟨a, b, ha, hb⟩ := caseII_integer_parity hmod hEq
  refine ⟨a, b, ?_, ?_⟩
  · rw [ha] at hA
    push_cast at hA
    linarith
  · rw [hb] at hB
    linarith

theorem omega_isIntegral :
    IsIntegral ℤ (QuadraticAlgebra.omega : RealQuadraticAlgebra m) := by
  apply IsIntegral.of_pow (n := 2) (by norm_num)
  have hmInt : IsIntegral ℤ
      (algebraMap ℤ (RealQuadraticAlgebra m) (m : ℤ)) :=
    isIntegral_algebraMap
  convert hmInt using 1
  rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_add]
  ext <;> simp

def quadraticEta : RealQuadraticAlgebra m :=
  ⟨1 / 2, 1 / 2⟩

theorem quadraticEta_isIntegral (hmod : m % 4 = 1) :
    IsIntegral ℤ (quadraticEta (m := m)) := by
  let k : ℤ := (m / 4 : ℕ)
  refine ⟨Polynomial.X ^ 2 - Polynomial.X - Polynomial.C k, ?_, ?_⟩
  · monicity
    norm_num
  · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    have hmNat : m = 4 * (m / 4) + 1 := by omega
    have hm : (m : ℚ) = 4 * (m / 4 : ℕ) + 1 := by exact_mod_cast hmNat
    apply QuadraticAlgebra.ext
    · simp [quadraticEta, k, hm, pow_two]
      ring_nf
      exact sub_eq_zero.mpr (congrArg (fun z : ℤ ↦ (z : ℚ))
        (Int.natCast_div m 4))
    · simp [quadraticEta, k, hm, pow_two]
      ring

def caseIIntegerPointValue (z : IntegralPoint) : RealQuadraticAlgebra m :=
  ⟨(z.1 : ℚ), (z.2 : ℚ)⟩

def caseIIIntegerPointValue (z : IntegralPoint) : RealQuadraticAlgebra m :=
  ⟨(z.1 : ℚ) + z.2 / 2, z.2 / 2⟩

theorem caseIIntegerPointValue_isIntegral (z : IntegralPoint) :
    IsIntegral ℤ (caseIIntegerPointValue (m := m) z) := by
  have ha : IsIntegral ℤ
      (algebraMap ℤ (RealQuadraticAlgebra m) z.1) := isIntegral_algebraMap
  have hb : IsIntegral ℤ
      (algebraMap ℤ (RealQuadraticAlgebra m) z.2) := isIntegral_algebraMap
  have h := ha.add (hb.mul omega_isIntegral)
  have heq : caseIIntegerPointValue (m := m) z =
      algebraMap ℤ (RealQuadraticAlgebra m) z.1 +
        algebraMap ℤ (RealQuadraticAlgebra m) z.2 * QuadraticAlgebra.omega := by
    apply QuadraticAlgebra.ext <;> simp [caseIIntegerPointValue]
  rw [heq]
  exact h

theorem caseIIIntegerPointValue_isIntegral (hmod : m % 4 = 1)
    (z : IntegralPoint) :
    IsIntegral ℤ (caseIIIntegerPointValue (m := m) z) := by
  have ha : IsIntegral ℤ
      (algebraMap ℤ (RealQuadraticAlgebra m) z.1) := isIntegral_algebraMap
  have hb : IsIntegral ℤ
      (algebraMap ℤ (RealQuadraticAlgebra m) z.2) := isIntegral_algebraMap
  have h := ha.add (hb.mul (quadraticEta_isIntegral hmod))
  have heq : caseIIIntegerPointValue (m := m) z =
      algebraMap ℤ (RealQuadraticAlgebra m) z.1 +
        algebraMap ℤ (RealQuadraticAlgebra m) z.2 * quadraticEta := by
    apply QuadraticAlgebra.ext <;>
      simp [caseIIIntegerPointValue, quadraticEta] <;> ring
  rw [heq]
  exact h

abbrev RealQuadraticIntegers :=
  NumberField.RingOfIntegers (RealQuadraticAlgebra m)

def caseIIntegerPointToRing (z : IntegralPoint) :
    RealQuadraticIntegers (m := m) :=
  ⟨caseIIntegerPointValue (m := m) z,
    caseIIntegerPointValue_isIntegral z⟩

def caseIIntegerPointRingHom :
    IntegralPoint →+ RealQuadraticIntegers (m := m) where
  toFun := caseIIntegerPointToRing
  map_zero' := by
    apply Subtype.ext
    change caseIIntegerPointValue (m := m) 0 = 0
    apply QuadraticAlgebra.ext <;> norm_num [caseIIntegerPointValue]
  map_add' z w := by
    apply Subtype.ext
    change caseIIntegerPointValue (m := m) (z + w) =
      caseIIntegerPointValue (m := m) z +
        caseIIntegerPointValue (m := m) w
    apply QuadraticAlgebra.ext <;> simp [caseIIntegerPointValue]

theorem caseIIntegerPointRingHom_bijective
    (hsq : IsSquarefreeNat m)
    (hmod : m % 4 = 2 ∨ m % 4 = 3) :
    Function.Bijective (caseIIntegerPointRingHom (m := m)) := by
  constructor
  · intro z w hzw
    have hre := congrArg
      (fun q : RealQuadraticIntegers (m := m) ↦ q.1.re) hzw
    have him := congrArg
      (fun q : RealQuadraticIntegers (m := m) ↦ q.1.im) hzw
    apply Prod.ext
    · dsimp [caseIIntegerPointRingHom, caseIIntegerPointToRing,
        caseIIntegerPointValue] at hre
      exact_mod_cast hre
    · dsimp [caseIIntegerPointRingHom, caseIIntegerPointToRing,
        caseIIntegerPointValue] at him
      exact_mod_cast him
  · intro y
    obtain ⟨a, b, ha, hb⟩ :=
      integral_coordinates_caseI hsq hmod y.property
    refine ⟨(a, b), ?_⟩
    apply Subtype.ext
    apply QuadraticAlgebra.ext
    · simpa [caseIIntegerPointRingHom, caseIIntegerPointToRing,
        caseIIntegerPointValue] using ha.symm
    · simpa [caseIIntegerPointRingHom, caseIIntegerPointToRing,
        caseIIntegerPointValue] using hb.symm

def caseIIntegerPointRingEquiv
    (hsq : IsSquarefreeNat m)
    (hmod : m % 4 = 2 ∨ m % 4 = 3) :
    IntegralPoint ≃+ RealQuadraticIntegers (m := m) :=
  AddEquiv.ofBijective caseIIntegerPointRingHom
    (caseIIntegerPointRingHom_bijective hsq hmod)

def caseIIIntegerPointToRing (hmod : m % 4 = 1)
    (z : IntegralPoint) : RealQuadraticIntegers (m := m) :=
  ⟨caseIIIntegerPointValue (m := m) z,
    caseIIIntegerPointValue_isIntegral hmod z⟩

def caseIIIntegerPointRingHom (hmod : m % 4 = 1) :
    IntegralPoint →+ RealQuadraticIntegers (m := m) where
  toFun := caseIIIntegerPointToRing hmod
  map_zero' := by
    apply Subtype.ext
    change caseIIIntegerPointValue (m := m) 0 = 0
    apply QuadraticAlgebra.ext <;> norm_num [caseIIIntegerPointValue]
  map_add' z w := by
    apply Subtype.ext
    change caseIIIntegerPointValue (m := m) (z + w) =
      caseIIIntegerPointValue (m := m) z +
        caseIIIntegerPointValue (m := m) w
    apply QuadraticAlgebra.ext <;> simp [caseIIIntegerPointValue] <;> ring

theorem caseIIIntegerPointRingHom_bijective
    (hsq : IsSquarefreeNat m) (hmod : m % 4 = 1) :
    Function.Bijective (caseIIIntegerPointRingHom (m := m) hmod) := by
  constructor
  · intro z w hzw
    have hre := congrArg
      (fun q : RealQuadraticIntegers (m := m) ↦ q.1.re) hzw
    have him := congrArg
      (fun q : RealQuadraticIntegers (m := m) ↦ q.1.im) hzw
    dsimp [caseIIIntegerPointRingHom, caseIIIntegerPointToRing,
      caseIIIntegerPointValue] at hre him
    have hbq : (z.2 : ℚ) = (w.2 : ℚ) := by linarith
    have hb : z.2 = w.2 := by exact_mod_cast hbq
    have haq : (z.1 : ℚ) = (w.1 : ℚ) := by
      rw [hb] at hre
      linarith
    have ha : z.1 = w.1 := by exact_mod_cast haq
    exact Prod.ext ha hb
  · intro y
    obtain ⟨a, b, ha, hb⟩ :=
      integral_coordinates_caseII hsq hmod y.property
    refine ⟨(a, b), ?_⟩
    apply Subtype.ext
    apply QuadraticAlgebra.ext
    · simpa [caseIIIntegerPointRingHom, caseIIIntegerPointToRing,
        caseIIIntegerPointValue] using ha.symm
    · simpa [caseIIIntegerPointRingHom, caseIIIntegerPointToRing,
        caseIIIntegerPointValue] using hb.symm

def caseIIIntegerPointRingEquiv
    (hsq : IsSquarefreeNat m) (hmod : m % 4 = 1) :
    IntegralPoint ≃+ RealQuadraticIntegers (m := m) :=
  AddEquiv.ofBijective (caseIIIntegerPointRingHom hmod)
    (caseIIIntegerPointRingHom_bijective hsq hmod)

def caseICoordinates :
    RealQuadraticAlgebra m ≃ₗ[ℚ] RationalPoint where
  toFun z := (z.re, z.im)
  invFun x := ⟨x.1, x.2⟩
  left_inv z := rfl
  right_inv x := rfl
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

def caseIICoordinates :
    RealQuadraticAlgebra m ≃ₗ[ℚ] RationalPoint where
  toFun z := (z.re - z.im, 2 * z.im)
  invFun x := ⟨x.1 + x.2 / 2, x.2 / 2⟩
  left_inv z := by
    apply QuadraticAlgebra.ext <;> simp
  right_inv x := by
    apply Prod.ext
    · simp
    · simp
      ring
  map_add' x y := by
    apply Prod.ext <;> simp <;> ring
  map_smul' c x := by
    apply Prod.ext <;> simp <;> ring

theorem caseI_trace_formula
    (hmod : m % 4 = 2 ∨ m % 4 = 3)
    (x : RealQuadraticAlgebra m) (z : IntegralPoint) :
    Algebra.trace ℚ (RealQuadraticAlgebra m)
        ((x - caseIIntegerPointValue (m := m) z) ^ 2) =
      realQuadraticCostRat m (caseICoordinates x) z := by
  rw [realQuadratic_trace]
  have hnot : m % 4 ≠ 1 := by omega
  simp [realQuadraticCostRat, hnot, caseICostOver, caseICoordinates,
    caseIIntegerPointValue, pow_two]
  ring

theorem caseII_trace_formula
    (hmod : m % 4 = 1)
    (x : RealQuadraticAlgebra m) (z : IntegralPoint) :
    Algebra.trace ℚ (RealQuadraticAlgebra m)
        ((x - caseIIIntegerPointValue (m := m) z) ^ 2) =
      realQuadraticCostRat m (caseIICoordinates x) z := by
  rw [realQuadratic_trace]
  simp [realQuadraticCostRat, hmod, caseIICostOver, caseIICoordinates,
    caseIIIntegerPointValue, pow_two]
  ring

def realQuadraticCoordinateModel_caseI
    (hsq : IsSquarefreeNat m)
    (hmod : m % 4 = 2 ∨ m % 4 = 3) :
    RealQuadraticCoordinateModel (RealQuadraticAlgebra m) m where
  coordinates := caseICoordinates
  integerCoordinates := (caseIIntegerPointRingEquiv hsq hmod).symm
  trace_formula x y := by
    let e := caseIIntegerPointRingEquiv (m := m) hsq hmod
    let z := e.symm y
    have hy : caseIIntegerPointValue (m := m) z =
        (y : RealQuadraticAlgebra m) := by
      have h := e.apply_symm_apply y
      have hval := congrArg Subtype.val h
      change caseIIntegerPointValue (m := m) (e.symm y) = y.1 at hval
      change caseIIntegerPointValue (m := m) (e.symm y) = y.1
      exact hval
    rw [← hy]
    simpa [z, e] using caseI_trace_formula (m := m) hmod x z

def realQuadraticCoordinateModel_caseII
    (hsq : IsSquarefreeNat m) (hmod : m % 4 = 1) :
    RealQuadraticCoordinateModel (RealQuadraticAlgebra m) m where
  coordinates := caseIICoordinates
  integerCoordinates := (caseIIIntegerPointRingEquiv hsq hmod).symm
  trace_formula x y := by
    let e := caseIIIntegerPointRingEquiv (m := m) hsq hmod
    let z := e.symm y
    have hy : caseIIIntegerPointValue (m := m) z =
        (y : RealQuadraticAlgebra m) := by
      have h := e.apply_symm_apply y
      have hval := congrArg Subtype.val h
      change caseIIIntegerPointValue (m := m) (e.symm y) = y.1 at hval
      change caseIIIntegerPointValue (m := m) (e.symm y) = y.1
      exact hval
    rw [← hy]
    simpa [z, e] using caseII_trace_formula (m := m) hmod x z

end Model

theorem squarefree_mod_four_cases {m : ℕ} (hsq : IsSquarefreeNat m) :
    m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by
  have hnot0 : m % 4 ≠ 0 := by
    intro hzero
    have hdiv4 : 4 ∣ m := Nat.dvd_iff_mod_eq_zero.mpr hzero
    have htwo : 2 = 1 := hsq 2 (by simpa using hdiv4)
    omega
  have hlt : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  omega

/--
Theorem 1.8 for the concrete quadratic algebra `ℚ(√m)`, including the full
algebraic-integer coordinate classification and the exact trace-square bridge.
-/
theorem realQuadratic_two_trace_euclidean_iff {m : ℕ}
    (hm : 1 < m) (hsq : IsSquarefreeNat m) :
    letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
      ⟨realQuadratic_nonsquare hm hsq⟩
    IsFieldTraceEuclidean (F := RealQuadraticAlgebra m) 2 ↔
      m = 2 ∨ m = 5 ∨ m = 13 := by
  letI : Fact (∀ r : ℚ, r ^ 2 ≠ (m : ℚ) + 0 * r) :=
    ⟨realQuadratic_nonsquare hm hsq⟩
  rcases squarefree_mod_four_cases hsq with hmod | hmod
  · exact RealQuadraticCoordinateModel.field_two_trace_euclidean_iff
      (realQuadraticCoordinateModel_caseII hsq hmod) hm hsq
  · exact RealQuadraticCoordinateModel.field_two_trace_euclidean_iff
      (realQuadraticCoordinateModel_caseI hsq hmod) hm hsq

end

end TraceEuclidean
