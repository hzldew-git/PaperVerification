import TraceEuclidean.V15QuadraticDiscriminantRows
import TraceEuclidean.V15CubicGeneratorArithmetic

/-!
# Arithmetic of a quadratic integral generator

This module records the integral power family `1, a` in a quadratic number
field.  Its discriminant is the usual quadratic trace expression, and its
determinant in an integral basis gives the exact square index relating that
expression to the field discriminant.
-/

namespace TraceEuclidean

noncomputable section

open Matrix Module NumberField
open scoped NumberField

/-- The distinguished generator of `ℚ⟮a⟯`, regarded as an algebraic integer
of the adjoin field. -/
noncomputable def v15AdjoinRingOfIntegersGenerator
    (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) :
    𝓞 (IntermediateField.adjoin ℚ {(a : K)}) := by
  let E : IntermediateField ℚ K :=
    IntermediateField.adjoin ℚ {(a : K)}
  let aE : E := IntermediateField.AdjoinSimple.gen ℚ (a : K)
  refine ⟨aE, ?_⟩
  apply (isIntegral_algHom_iff
    (E.val.restrictScalars ℤ) E.val.injective).mp
  simpa [aE, E] using a.isIntegral_coe

/-- The preceding integral element generates its adjoin field. -/
theorem v15AdjoinRingOfIntegersGenerator_adjoin_eq_top
    (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) :
    IntermediateField.adjoin ℚ
      {((v15AdjoinRingOfIntegersGenerator K a :
        𝓞 (IntermediateField.adjoin ℚ {(a : K)})) :
          IntermediateField.adjoin ℚ {(a : K)})} = ⊤ := by
  let hint : IsIntegral ℚ (a : K) := IsIntegral.of_finite ℚ (a : K)
  let pb : PowerBasis ℚ (IntermediateField.adjoin ℚ {(a : K)}) :=
    IntermediateField.adjoin.powerBasis hint
  simpa [v15AdjoinRingOfIntegersGenerator, pb] using
    pb.adjoin_gen_eq_top

/-- The two integral powers `1, a`. -/
def v15QuadraticPowerFamily
    (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) : Fin 2 → 𝓞 K
  | 0 => 1
  | 1 => a

/-- The discriminant of `1, a`, after localization to the number field, is
the standard quadratic trace expression. -/
theorem v15_quadraticPowerFamily_discr_cast_eq_trace
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2) (a : 𝓞 K) :
    ((Algebra.discr ℤ (v15QuadraticPowerFamily K a) : ℤ) : ℚ) =
      2 * Algebra.trace ℚ K ((a : K) ^ 2) -
        (Algebra.trace ℚ K (a : K)) ^ 2 := by
  classical
  rw [v15_discr_ringOfIntegers_cast, Algebra.discr_def,
    Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  have htraceOne : Algebra.trace ℚ K (1 : K) = 2 := by
    rw [show (1 : K) = algebraMap ℚ K 1 by simp,
      Algebra.trace_algebraMap, hdegree]
    norm_num
  simp [v15QuadraticPowerFamily, htraceOne, pow_two]

/-- Scaling the nonconstant member of a quadratic power family by an integer
scales its discriminant by the square of that integer. -/
theorem v15_quadraticPowerFamily_discr_zsmul
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2) (n : ℤ) (a : 𝓞 K) :
    Algebra.discr ℤ (v15QuadraticPowerFamily K (n • a)) =
      n ^ 2 * Algebra.discr ℤ (v15QuadraticPowerFamily K a) := by
  apply Rat.intCast_injective
  push_cast
  rw [v15_quadraticPowerFamily_discr_cast_eq_trace K hdegree,
    v15_quadraticPowerFamily_discr_cast_eq_trace K hdegree]
  simp only [map_mul, Algebra.smul_def]
  have hnK : algebraMap (𝓞 K) K (algebraMap ℤ (𝓞 K) n) =
      algebraMap ℚ K (n : ℚ) := by
    norm_num
  rw [hnK]
  rw [mul_pow]
  rw [show algebraMap ℚ K (n : ℚ) ^ 2 * (a : K) ^ 2 =
      (n : ℚ) ^ 2 • (a : K) ^ 2 by simp [Algebra.smul_def],
    show algebraMap ℚ K (n : ℚ) * (a : K) =
      (n : ℚ) • (a : K) by simp [Algebra.smul_def],
    map_smul, map_smul]
  ring

/-- The determinant of the integral power family in an integral basis gives
the exact square factor between its discriminant and the field
discriminant. -/
theorem v15_quadraticPowerFamily_discr_eq_det_sq_mul_fieldDiscriminant
    (K : Type*) [Field K] [NumberField K]
    (a : 𝓞 K) (bO : Basis (Fin 2) ℤ (𝓞 K)) :
    Algebra.discr ℤ (v15QuadraticPowerFamily K a) =
      (bO.toMatrix (v15QuadraticPowerFamily K a)).det ^ 2 *
        NumberField.discr K := by
  classical
  let P := bO.toMatrix (v15QuadraticPowerFamily K a)
  change Algebra.discr ℤ (v15QuadraticPowerFamily K a) =
    P.det ^ 2 * NumberField.discr K
  calc
    Algebra.discr ℤ (v15QuadraticPowerFamily K a) =
        Algebra.discr ℤ
          (bO ᵥ* P.map (algebraMap ℤ (𝓞 K))) := by
      rw [bO.toMatrix_map_vecMul (v15QuadraticPowerFamily K a)]
    _ = P.det ^ 2 * Algebra.discr ℤ bO :=
      Algebra.discr_of_matrix_vecMul bO P
    _ = P.det ^ 2 * NumberField.discr K := by
      rw [NumberField.discr_eq_discr K bO]

/-- A quadratic algebraic integer generating the field has a strictly
positive natural index, with the exact discriminant relation. -/
theorem v15_quadratic_exists_positive_index
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤)
    (bO : Basis (Fin 2) ℤ (𝓞 K)) :
    ∃ index : ℕ, 0 < index ∧
      Algebra.discr ℤ (v15QuadraticPowerFamily K a) =
        (index : ℤ) ^ 2 * NumberField.discr K := by
  classical
  let P := bO.toMatrix (v15QuadraticPowerFamily K a)
  have hfamily : Algebra.discr ℤ (v15QuadraticPowerFamily K a) =
      P.det ^ 2 * NumberField.discr K :=
    v15_quadraticPowerFamily_discr_eq_det_sq_mul_fieldDiscriminant K a bO
  have hdet : P.det ≠ 0 := by
    intro hzero
    have hzeroDiscr : Algebra.discr ℤ (v15QuadraticPowerFamily K a) = 0 := by
      rw [hfamily, hzero]
      norm_num
    have hcast := congrArg (fun z : ℤ ↦ (z : ℚ)) hzeroDiscr
    rw [v15_discr_ringOfIntegers_cast] at hcast
    simp only [Int.cast_zero] at hcast
    let hint : IsIntegral ℚ (a : K) := IsIntegral.of_finite ℚ (a : K)
    let hsub : Algebra.adjoin ℚ {(a : K)} = ⊤ :=
      Algebra.adjoin_eq_top_of_primitive_element hint.isAlgebraic hgen
    let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hint hsub
    have hdim : pb.dim = 2 := by
      rw [PowerBasis.ofAdjoinEqTop_dim]
      have h := hgen
      rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
      exact h.trans hdegree
    let e : Fin pb.dim ≃ Fin 2 := finCongr hdim
    have hfamilyBasis :
        (fun i ↦ ((v15QuadraticPowerFamily K a i : 𝓞 K) : K)) =
          pb.basis ∘ e.symm := by
      funext i
      change ((v15QuadraticPowerFamily K a i : 𝓞 K) : K) =
        pb.basis (e.symm i)
      rw [pb.basis_eq_pow]
      have he : ((e.symm i : Fin pb.dim) : ℕ) = (i : ℕ) := rfl
      rw [he]
      fin_cases i <;> simp [v15QuadraticPowerFamily, pb]
    rw [hfamilyBasis] at hcast
    exact (Algebra.discr_not_zero_of_basis ℚ (pb.basis.reindex e)) (by
      simpa [Basis.coe_reindex] using hcast)
  refine ⟨P.det.natAbs, Int.natAbs_pos.mpr hdet, ?_⟩
  rw [hfamily]
  simp [sq_abs]

/-- A quadratic integral generator whose power-family discriminant is below
`9` already generates the full ring of integers. -/
theorem v15_quadraticPowerFamily_discr_eq_field_of_lt_nine
    (K : Type*) [Field K] [NumberField K]
    (hreal : NumberField.IsTotallyReal K)
    (hdegree : Module.finrank ℚ K = 2)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤)
    (hlt : ((Algebra.discr ℤ
      (v15QuadraticPowerFamily K a) : ℤ) : ℚ) < 9) :
    Algebra.discr ℤ (v15QuadraticPowerFamily K a) =
      NumberField.discr K := by
  obtain ⟨bO, hbO⟩ := v15_exists_ringOfIntegers_basis_one_dim_two K hdegree
  obtain ⟨index, hindex, hdisc⟩ :=
    v15_quadratic_exists_positive_index K hdegree a hgen bO
  letI : NumberField.IsTotallyReal K := hreal
  have hsign : (NumberField.discr K).sign = 1 := by
    rw [NumberField.sign_discr,
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero]
    norm_num
  have hfieldPos : 0 < NumberField.discr K :=
    Int.sign_eq_one_iff_pos.mp hsign
  have hfieldFive : (5 : ℤ) ≤ NumberField.discr K := by
    have h := v15_degree_two_discriminant_ge_five K hreal hdegree
    rw [abs_of_pos hfieldPos] at h
    exact_mod_cast h
  have hdiscLt : Algebra.discr ℤ
      (v15QuadraticPowerFamily K a) < 9 := by
    exact_mod_cast hlt
  have hindexOne : index = 1 := by
    by_contra hne
    have htwo : 2 ≤ index := by omega
    rw [hdisc] at hdiscLt
    have hindexCast : (2 : ℤ) ≤ index := by exact_mod_cast htwo
    nlinarith
  simpa [hindexOne] using hdisc

/-- A quadratic integral generator whose power-family discriminant is the
field discriminant is primitive in the ring of integers. -/
theorem v15_quadratic_generator_isPrimitive_of_discr_eq_field
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤)
    (hdisc : Algebra.discr ℤ (v15QuadraticPowerFamily K a) =
      NumberField.discr K) :
    V15IsPrimitiveVector a := by
  intro n c hnc
  have hgenC : IntermediateField.adjoin ℚ {(c : K)} = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    have hc : (c : K) ∈ IntermediateField.adjoin ℚ {(c : K)} :=
      IntermediateField.subset_adjoin ℚ {(c : K)} (Set.mem_singleton (c : K))
    have hn : algebraMap ℚ K (n : ℚ) ∈
        IntermediateField.adjoin ℚ {(c : K)} :=
      (IntermediateField.adjoin ℚ {(c : K)}).algebraMap_mem (n : ℚ)
    have hmul := (IntermediateField.adjoin ℚ {(c : K)}).mul_mem hn hc
    have hncK := congrArg (fun x : 𝓞 K ↦ (x : K)) hnc
    have hcoe : ((n • c : 𝓞 K) : K) =
        algebraMap ℚ K (n : ℚ) * (c : K) := by
      simp [Algebra.smul_def]
    rw [← hcoe] at hmul
    exact hncK.symm ▸ hmul
  obtain ⟨bO, hbO⟩ := v15_exists_ringOfIntegers_basis_one_dim_two K hdegree
  obtain ⟨index, hindex, hdiscC⟩ :=
    v15_quadratic_exists_positive_index K hdegree c hgenC bO
  have hscaled := v15_quadraticPowerFamily_discr_zsmul K hdegree n c
  rw [hnc, hdisc, hdiscC] at hscaled
  have hfieldNe : NumberField.discr K ≠ 0 := NumberField.discr_ne_zero K
  have hfactor : n ^ 2 * (index : ℤ) ^ 2 = 1 := by
    apply mul_right_cancel₀ hfieldNe
    simpa [mul_assoc] using hscaled.symm
  apply isUnit_iff_dvd_one.mpr
  refine ⟨n * (index : ℤ) ^ 2, ?_⟩
  nlinarith

/-- For a generator of a quadratic field, the square of twice the generator
minus its trace is the discriminant of the power family `1, a`. -/
theorem v15_quadratic_generator_centered_sq_eq_traceDiscriminant
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2)
    (a : K) (hgen : IntermediateField.adjoin ℚ {a} = ⊤) :
    (2 * a - algebraMap ℚ K (Algebra.trace ℚ K a)) ^ 2 =
      algebraMap ℚ K
        (2 * Algebra.trace ℚ K (a ^ 2) -
          (Algebra.trace ℚ K a) ^ 2) := by
  let hint : IsIntegral ℚ a := IsIntegral.of_finite ℚ a
  let hsub : Algebra.adjoin ℚ {a} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element hint.isAlgebraic hgen
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop hint hsub
  have hdim : pb.dim = 2 := by
    rw [PowerBasis.ofAdjoinEqTop_dim]
    have h := hgen
    rw [Field.primitive_element_iff_minpoly_natDegree_eq] at h
    exact h.trans hdegree
  let B : Basis (Fin 2) ℚ K := pb.basis.reindex (finCongr hdim)
  have hb0 : B 0 = 1 := by
    simp only [B, Module.Basis.reindex_apply]
    rw [pb.basis_eq_pow]
    norm_num
  have hb1 : B 1 = a := by
    simp only [B, Module.Basis.reindex_apply]
    rw [pb.basis_eq_pow]
    change pb.gen ^ 1 = a
    simp [pb, PowerBasis.ofAdjoinEqTop]
  let A : ℚ := B.repr (a * a) 0
  let C : ℚ := B.repr (a * a) 1
  have hrepa0 : B.repr a 0 = 0 := by
    rw [← hb1]
    simp
  have htrace : Algebra.trace ℚ K a = C := by
    rw [Algebra.trace_eq_matrix_trace B]
    simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul,
      hb0, hb1, hrepa0, C]
  have hsum := B.sum_repr (a * a)
  have hrelation : a * a = algebraMap ℚ K A + algebraMap ℚ K C * a := by
    simpa [Fin.sum_univ_two, A, C, hb0, hb1, Algebra.smul_def,
      add_comm] using hsum.symm
  have htraceA : Algebra.trace ℚ K (algebraMap ℚ K A) = 2 * A := by
    rw [Algebra.trace_algebraMap, hdegree]
    ring
  have htraceCa :
      Algebra.trace ℚ K (algebraMap ℚ K C * a) =
        C * Algebra.trace ℚ K a := by
    rw [show algebraMap ℚ K C * a = C • a by rw [Algebra.smul_def],
      map_smul]
    rfl
  have htraceSq : Algebra.trace ℚ K (a ^ 2) = 2 * A + C ^ 2 := by
    rw [pow_two, hrelation, map_add, htraceA, htraceCa, htrace]
    ring
  rw [htrace, htraceSq]
  calc
    (2 * a - algebraMap ℚ K C) ^ 2 =
        4 * (a * a) - 4 * algebraMap ℚ K C * a +
          (algebraMap ℚ K C) ^ 2 := by ring
    _ = 4 * algebraMap ℚ K A + (algebraMap ℚ K C) ^ 2 := by
      rw [hrelation]
      ring
    _ = algebraMap ℚ K (2 * (2 * A + C ^ 2) - C ^ 2) := by
      push_cast
      norm_num
      ring

/-- If the integral power family `1, a` has the field discriminant, the
centered quadratic generator has square equal to that field discriminant. -/
theorem v15_quadratic_generator_centered_sq_eq_fieldDiscriminant
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 2)
    (a : 𝓞 K)
    (hgen : IntermediateField.adjoin ℚ {(a : K)} = ⊤)
    (hdisc : Algebra.discr ℤ (v15QuadraticPowerFamily K a) =
      NumberField.discr K) :
    (2 * (a : K) -
        algebraMap ℚ K (Algebra.trace ℚ K (a : K))) ^ 2 =
      algebraMap ℚ K (NumberField.discr K : ℚ) := by
  rw [v15_quadratic_generator_centered_sq_eq_traceDiscriminant
    K hdegree (a : K) hgen]
  have hdiscQ := congrArg (fun z : ℤ ↦ (z : ℚ)) hdisc
  rw [v15_quadraticPowerFamily_discr_cast_eq_trace K hdegree a] at hdiscQ
  rw [hdiscQ]

/-- Every element of a quadratic simple extension is a rational linear
combination of `1` and the chosen generator. -/
theorem v15_mem_quadratic_adjoin_eq_rat_add_rat_mul
    (L : Type*) [Field L] [NumberField L]
    (a c : L)
    (hdegree : Module.finrank ℚ (IntermediateField.adjoin ℚ {a}) = 2)
    (hc : c ∈ IntermediateField.adjoin ℚ {a}) :
    ∃ r s : ℚ, c = algebraMap ℚ L r + algebraMap ℚ L s * a := by
  let E : IntermediateField ℚ L := IntermediateField.adjoin ℚ {a}
  let hint : IsIntegral ℚ a := IsIntegral.of_finite ℚ a
  let pb : PowerBasis ℚ E := IntermediateField.adjoin.powerBasis hint
  have hdim : pb.dim = 2 := by
    rw [← PowerBasis.finrank pb]
    exact hdegree
  let B : Basis (Fin 2) ℚ E := pb.basis.reindex (finCongr hdim)
  let aE : E := IntermediateField.AdjoinSimple.gen ℚ a
  let cE : E := ⟨c, hc⟩
  have hb0 : B 0 = 1 := by
    simp only [B, Module.Basis.reindex_apply]
    rw [pb.basis_eq_pow]
    norm_num
  have hb1 : B 1 = aE := by
    simp only [B, Module.Basis.reindex_apply]
    rw [pb.basis_eq_pow]
    change pb.gen ^ 1 = aE
    simp [pb, aE]
  refine ⟨B.repr cE 0, B.repr cE 1, ?_⟩
  have hsum := B.sum_repr cE
  have hsumL := congrArg E.val hsum
  simpa [Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, E, aE, cE,
    add_comm] using hsumL.symm

/-- Two quadratic subfields generated by integral elements with the same
field discriminant coincide inside a common number field.  The proof uses
the canonical square roots `2a - Tr(a)` of the common discriminant. -/
theorem v15_quadratic_adjoin_eq_of_powerFamily_discr_eq
    (L : Type*) [Field L] [NumberField L]
    (a c : 𝓞 L) :
    let E := IntermediateField.adjoin ℚ {(a : L)}
    let F := IntermediateField.adjoin ℚ {(c : L)}
    Module.finrank ℚ E = 2 →
    Module.finrank ℚ F = 2 →
    Algebra.discr ℤ
        (v15QuadraticPowerFamily E
          (v15AdjoinRingOfIntegersGenerator L a)) =
      NumberField.discr E →
    Algebra.discr ℤ
        (v15QuadraticPowerFamily F
          (v15AdjoinRingOfIntegersGenerator L c)) =
      NumberField.discr F →
    NumberField.discr E = NumberField.discr F →
    E = F := by
  dsimp only
  intro hdegreeE hdegreeF hdiscA hdiscC hdiscEq
  let E : IntermediateField ℚ L := IntermediateField.adjoin ℚ {(a : L)}
  let F : IntermediateField ℚ L := IntermediateField.adjoin ℚ {(c : L)}
  let aE : 𝓞 E := v15AdjoinRingOfIntegersGenerator L a
  let cF : 𝓞 F := v15AdjoinRingOfIntegersGenerator L c
  have hgenE : IntermediateField.adjoin ℚ {(aE : E)} = ⊤ := by
    simpa [E, aE] using v15AdjoinRingOfIntegersGenerator_adjoin_eq_top L a
  have hgenF : IntermediateField.adjoin ℚ {(cF : F)} = ⊤ := by
    simpa [F, cF] using v15AdjoinRingOfIntegersGenerator_adjoin_eq_top L c
  have hsqE := v15_quadratic_generator_centered_sq_eq_fieldDiscriminant
    E hdegreeE aE hgenE (by simpa [E, aE] using hdiscA)
  have hsqF := v15_quadratic_generator_centered_sq_eq_fieldDiscriminant
    F hdegreeF cF hgenF (by simpa [F, cF] using hdiscC)
  have haMap : algebraMap E L (aE : E) = (a : L) := by rfl
  have hcMap : algebraMap F L (cF : F) = (c : L) := by rfl
  have haCoe : ((aE : E) : L) = (a : L) := by rfl
  have hcCoe : ((cF : F) : L) = (c : L) := by rfl
  let u : L := algebraMap E L (2 : E) * (a : L) -
    algebraMap ℚ L (Algebra.trace ℚ E (aE : E))
  let v : L := algebraMap F L (2 : F) * (c : L) -
    algebraMap ℚ L (Algebra.trace ℚ F (cF : F))
  have hsqEL := congrArg (algebraMap E L) hsqE
  have hsqFL := congrArg (algebraMap F L) hsqF
  have huSq : u ^ 2 = algebraMap ℚ L (NumberField.discr E : ℚ) := by
    simpa [u, haMap, haCoe, IsScalarTower.algebraMap_apply ℚ E L] using hsqEL
  have hvSq : v ^ 2 = algebraMap ℚ L (NumberField.discr F : ℚ) := by
    simpa [v, hcMap, hcCoe, IsScalarTower.algebraMap_apply ℚ F L] using hsqFL
  have huvSq : u ^ 2 = v ^ 2 := by
    rw [huSq, hvSq, hdiscEq]
  have hcMem : (c : L) ∈ F := by
    exact IntermediateField.subset_adjoin ℚ {(c : L)}
      (Set.mem_singleton (c : L))
  have htwoFMem : ((2 : F) : L) ∈ F := (2 : F).property
  have htwoE : ((2 : E) : L) = (2 : L) := by
    change algebraMap E L (2 : E) = (2 : L)
    exact map_ofNat (algebraMap E L) 2
  have hvMem : v ∈ F := by
    dsimp [v]
    exact F.sub_mem
      (F.mul_mem htwoFMem hcMem)
      (F.algebraMap_mem (Algebra.trace ℚ F (cF : F)))
  have huMem : u ∈ F := by
    rcases eq_or_eq_neg_of_sq_eq_sq u v huvSq with huv | huv
    · exact huv.symm ▸ hvMem
    · rw [huv]
      exact F.neg_mem hvMem
  have haEq : (a : L) =
      algebraMap ℚ L (2 : ℚ)⁻¹ *
        (u + algebraMap ℚ L (Algebra.trace ℚ E (aE : E))) := by
    dsimp [u]
    rw [htwoE]
    norm_num
    field_simp
  have haMem : (a : L) ∈ F := by
    rw [haEq]
    exact F.mul_mem (F.algebraMap_mem (2 : ℚ)⁻¹)
      (F.add_mem huMem
        (F.algebraMap_mem (Algebra.trace ℚ E (aE : E))))
  have hle : E ≤ F := by
    dsimp [E]
    apply IntermediateField.adjoin_le_iff.mpr
    simpa using haMem
  exact IntermediateField.eq_of_le_of_finrank_eq hle
    (by simpa [E, F] using hdegreeE.trans hdegreeF.symm)

end

end TraceEuclidean
