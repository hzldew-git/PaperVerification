import TraceEuclidean.VoightMaximalOrderCertificates.Chunk070
import TraceEuclidean.VoightAllIrreducible
import TraceEuclidean.VoightIntegralBasisCertificate
import TraceEuclidean.VoightPolynomialBridge
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.CertifyAdjoinRootCore
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.MaximalAPI
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.CertificateDedekind
import Mathlib.Tactic

set_option linter.all false
set_option maxHeartbeats 5000000

namespace TraceEuclidean

namespace VoightMaximalOrderD6R685

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨14628625, [-5, 5, 24, 2, -10, -1, 1], 4⟩
local notation "l" => [-5, 5, 24, 2, -10, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSix := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSix_irreducible row row_mem
lemma T_monic : Monic T := by
  rw [← T_ofList]
  exact monic_ofList l rfl

abbrev K := AdjoinRoot (map (algebraMap ℤ ℚ) T)
instance hirr : Fact (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map T_monic).1
    T_irreducible
instance KField : Field K := AdjoinRoot.instField
instance : Algebra ℤ K := Ring.toIntAlgebra K
instance : IsScalarTower ℤ ℚ K :=
  IsScalarTower.of_algebraMap_eq' (by ext; simp)
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
  AdjoinRoot.isAdjoinRoot _
local notation "θ" => Adj.root

def basisDenominator : ℤ := 4
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![4, 0, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0], ![0, 0, 4, 0, 0, 0], ![0, 0, 0, 4, 0, 0], ![0, 0, 0, 0, 4, 0], ![1, 0, 0, 2, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-1, 0, 0, -2, 0, 4], ![1, -1, -6, -1, 3, 1]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-1, 0, 0, -2, 0, 4], ![4, -5, -24, -4, 10, 4], ![-2, 0, -7, -13, 2, 13]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-1, 0, 0, -2, 0, 4], ![4, -5, -24, -4, 10, 4], ![-6, 0, -29, -48, 8, 44], ![11, -15, -78, -24, 26, 21]], ![![0, 0, 0, 0, 1, 0], ![-1, 0, 0, -2, 0, 4], ![4, -5, -24, -4, 10, 4], ![-6, 0, -29, -48, 8, 44], ![36, -50, -264, -89, 84, 76], ![-5, -10, -141, -151, 39, 125]], ![![0, 0, 0, 0, 0, 1], ![1, -1, -6, -1, 3, 1], ![-2, 0, -7, -13, 2, 13], ![11, -15, -78, -24, 26, 21], ![-5, -10, -141, -151, 39, 125], ![27, -40, -229, -98, 69, 81]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-4]], ![[], [], [], [], [-16], [-4, -4]], ![[], [], [], [-16], [-16, -16], [-52, -4, -4]], ![[], [], [-16], [-16, -16], [-176, -16, -16], [-84, -52, -4, -4]], ![[], [-4], [-4, -4], [-52, -4, -4], [-84, -52, -4, -4], [-151, -23, -15, -1, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 6 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 6) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 6) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 6) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, 0, 0, -2, 0, 4], [1, -1, -6, -1, 3, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, 0, 0, -2, 0, 4], [4, -5, -24, -4, 10, 4], [-2, 0, -7, -13, 2, 13]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, 0, 0, -2, 0, 4], [4, -5, -24, -4, 10, 4], [-6, 0, -29, -48, 8, 44], [11, -15, -78, -24, 26, 21]], ![[0, 0, 0, 0, 1, 0], [-1, 0, 0, -2, 0, 4], [4, -5, -24, -4, 10, 4], [-6, 0, -29, -48, 8, 44], [36, -50, -264, -89, 84, 76], [-5, -10, -141, -151, 39, 125]], ![[0, 0, 0, 0, 0, 1], [1, -1, -6, -1, 3, 1], [-2, 0, -7, -13, 2, 13], [11, -15, -78, -24, 26, 21], [-5, -10, -141, -151, 39, 125], [27, -40, -229, -98, 69, 81]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp10639 : Fact (Nat.Prime 10639) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1]
  b' := [2, 3]
  k := [1]
  f := [1, -1, -3, 2, 4, 1]
  g := [0, 3, 2, 1]
  h := [0, 3, 2, 1]
  a := [1, 2]
  b := [3, 3, 0, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [5, 8, 2]
  b' := [0, 7, 0, 4]
  k := [8, 1, 0, 5, 1]
  f := [7, 4, -1, 5, 3, 1]
  g := [9, 5, 1, 7, 2, 1]
  h := [8, 1]
  a := [1, 9, 3, 0, 9]
  b := [3, 8, 0, 2, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD10639 : CertificateDedekindCriterionLists l 10639 where
  n := 2
  a' := [1393, 4935, 3891, 3064]
  b' := [4966, 561, 6350, 4776, 1515]
  k := [4357, 1519, 9427, 2334, 1]
  f := [1547, 905, 602, 3148, 2532, 1]
  g := [3964, 2318, 1542, 8066, 6486, 1]
  h := [4152, 1]
  a := [9397, 7029, 5444, 2012, 9175]
  b := [10391, 10179, 5636, 7587, 1464]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 4
  p := ![2, 5, 11, 10639]
  exp := ![3, 1, 1, 1]
  pdgood := [5, 11, 10639]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp5.out
    exact hp11.out
    exact hp10639.out
  a := [-1785977, -8014323, 4310661, 5104775, -2022126]
  b := [-849745, 1929206, 3396990, -1746856, -906966, 337021]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 10639 T_ofList CD10639

noncomputable def M2 : MaximalOrderCertificateOfUnramifiedLists 2 O Om hm where
  n := 6
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0], [1, 1, 0, 1, 1, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 1, 0, 1]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [1, 1, 0, 0, 0, 1]], ![[0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [1, 0, 1, 1, 1, 1]], ![[0, 0, 0, 0, 0, 1], [1, 1, 0, 1, 1, 1], [0, 0, 1, 1, 0, 1], [1, 1, 0, 0, 0, 1], [1, 0, 1, 1, 1, 1], [1, 0, 1, 0, 1, 1]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![1, 0, 1, 0, 1, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [2]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 2 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M2
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 6) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 6 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 6
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 6 := T_degree

noncomputable def bQ : Basis (Fin 6) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 6) :
    bQ i = Adj.root ^ (i : ℕ) := by
  rw [show bQ i = pb.basis ((finCongr pb_dim).symm i) by
    exact Basis.reindex_apply pb.basis (finCongr pb_dim) i]
  rw [pb.basis_eq_pow, pb_gen]
  congr 1

lemma bOm_cast_eq_vecMul :
    (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) =
      Matrix.vecMul bQ (P.map (algebraMap ℚ K)) := by
  funext j
  change (timesTableO.basis j).val = _
  rw [timesTableO_basis_apply]
  rw [ofList_eq_sum']
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X]
  rw [_root_.map_mul, _root_.map_sum]
  rw [← IsAdjoinRoot.algebraMap_apply Adj]
  have hdist :
      (algebraMap ℚ K) ((algebraMap ℤ ℚ) basisDenominator)⁻¹ *
          (∑ x : Fin 6,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 6,
          (algebraMap ℚ K) ((algebraMap ℤ ℚ) basisDenominator)⁻¹ *
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ)) := by
    exact Finset.mul_sum Finset.univ _ _
  rw [hdist]
  rw [Matrix.vecMul_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [_root_.map_mul, ← IsAdjoinRoot.algebraMap_apply Adj,
    _root_.map_pow, IsAdjoinRoot.map_X Adj]
  rw [bQ_apply]
  simp [P, div_eq_mul_inv, mul_comm, mul_left_comm]

lemma bQ_discr : Algebra.discr ℚ bQ = (T.discr : ℚ) := by
  calc
    Algebra.discr ℚ bQ = Algebra.discr ℚ pb.basis := by
      simpa [bQ] using
        Algebra.discr_reindex ℚ pb.basis (finCongr pb_dim)
    _ = (minpoly ℚ pb.gen).discr :=
      powerBasis_discr_eq_minpoly_discr pb
    _ = (map (algebraMap ℤ ℚ) T).discr := by
      have hqmonic : (map (algebraMap ℤ ℚ) T).Monic :=
        T_monic.map (algebraMap ℤ ℚ)
      rw [show minpoly ℚ pb.gen = map (algebraMap ℤ ℚ) T by
        rw [pb_gen]
        calc
          minpoly ℚ Adj.root =
              map (algebraMap ℤ ℚ) T *
                C (map (algebraMap ℤ ℚ) T).leadingCoeff⁻¹ :=
            AdjoinRoot.minpoly_root hirr.out.ne_zero
          _ = map (algebraMap ℤ ℚ) T := by
            rw [hqmonic.leadingCoeff]
            simp]
    _ = (T.discr : ℚ) := by
      exact (intCast_discr_eq_discr_map T T_monic
        (T_degree ▸ by norm_num)).symm

lemma P_det_index_sq :
    P.det ^ 2 * (row.index : ℚ) ^ 2 = 1 := by
  have htriangular : P.BlockTriangular id := by
    have hcheck :
        (List.ofFn fun i : Fin 6 =>
          (List.ofFn fun j : Fin 6 =>
            decide ((j : ℕ) < (i : ℕ) -> P i j = 0)).all id).all id =
          true := by native_decide
    simp only [List.all_eq_true, List.forall_mem_ofFn_iff, id_eq,
      decide_eq_true_eq] at hcheck
    intro i j hji
    exact hcheck i j hji
  rw [Matrix.det_of_upperTriangular htriangular]
  native_decide

theorem field_discriminant_eq_recorded :
    NumberField.discr K = (row.fieldDiscriminant : ℤ) := by
  apply Rat.intCast_injective
  have hbOmCast :
      ((NumberField.discr K : ℤ) : ℚ) =
        Algebra.discr ℚ
          (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) := by
    rw [← bOm_discr]
    exact discr_ringOfIntegers_cast K bOm
  have hrecorded :
      T.discr = (row.index : ℤ) ^ 2 *
        (row.fieldDiscriminant : ℤ) := by
    simpa [T] using
      (voightPolynomialDiscriminantInput 6 row row_mem)
  have hrecordedQ :
      (T.discr : ℚ) = (row.index : ℚ) ^ 2 *
        (row.fieldDiscriminant : ℚ) := by
    exact_mod_cast hrecorded
  calc
    ((NumberField.discr K : ℤ) : ℚ) =
        Algebra.discr ℚ
          (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) :=
      hbOmCast
    _ = Algebra.discr ℚ
        (Matrix.vecMul bQ (P.map (algebraMap ℚ K))) := by
      rw [bOm_cast_eq_vecMul]
    _ = P.det ^ 2 * Algebra.discr ℚ bQ :=
      Algebra.discr_of_matrix_vecMul bQ P
    _ = P.det ^ 2 * (T.discr : ℚ) := by rw [bQ_discr]
    _ = P.det ^ 2 *
        ((row.index : ℚ) ^ 2 *
          (row.fieldDiscriminant : ℚ)) := by rw [hrecordedQ]
    _ = (P.det ^ 2 * (row.index : ℚ) ^ 2) *
        (row.fieldDiscriminant : ℚ) := by ring
    _ = (row.fieldDiscriminant : ℚ) := by
      rw [P_det_index_sq, one_mul]

end

end VoightMaximalOrderD6R685

namespace VoightMaximalOrderD6R687

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨14642000, [29, -64, 17, 26, -11, -2, 1], 8⟩
local notation "l" => [29, -64, 17, 26, -11, -2, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSix := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSix_irreducible row row_mem
lemma T_monic : Monic T := by
  rw [← T_ofList]
  exact monic_ofList l rfl

abbrev K := AdjoinRoot (map (algebraMap ℤ ℚ) T)
instance hirr : Fact (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map T_monic).1
    T_irreducible
instance KField : Field K := AdjoinRoot.instField
instance : Algebra ℤ K := Ring.toIntAlgebra K
instance : IsScalarTower ℤ ℚ K :=
  IsScalarTower.of_algebraMap_eq' (by ext; simp)
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
  AdjoinRoot.isAdjoinRoot _
local notation "θ" => Adj.root

def basisDenominator : ℤ := 2
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![1, 1, 1, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![1, 1, 0, 0, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![-1, -1, -1, 2, 0, 0], ![-1, 0, 0, 1, 1, 0], ![0, 0, 0, 0, -1, 1], ![-7, 44, 5, -26, 8, 3]], ![![0, 0, 1, 0, 0, 0], ![-1, -1, -1, 2, 0, 0], ![-1, 0, 0, 0, 2, 0], ![-1, -1, 0, 1, 0, 1], ![-7, 44, 5, -26, 9, 2], ![0, 120, 54, -94, -10, 17]], ![![0, 0, 0, 1, 0, 0], ![-1, 0, 0, 1, 1, 0], ![-1, -1, 0, 1, 0, 1], ![-5, 21, 2, -11, 5, 2], ![0, 60, 27, -47, -5, 9], ![-43, 429, 105, -274, 25, 31]], ![![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, -1, 1], ![-7, 44, 5, -26, 9, 2], ![0, 60, 27, -47, -5, 9], ![-43, 309, 51, -180, 36, 13], ![-5, 787, 374, -596, -76, 88]], ![![0, 0, 0, 0, 0, 1], ![-7, 44, 5, -26, 8, 3], ![0, 120, 54, -94, -10, 17], ![-43, 429, 105, -274, 25, 31], ![-5, 787, 374, -596, -76, 88], ![-399, 4280, 1227, -2732, 108, 276]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-2]], ![[], [], [], [], [-2], [-6, -2]], ![[], [], [], [-1], [-3, -1], [-21, -4, -1]], ![[], [], [-2], [-3, -1], [-15, -2, -1], [-41, -17, -3, -1]], ![[], [-2], [-6, -2], [-21, -4, -1], [-41, -17, -3, -1], [-217, -58, -20, -4, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 6 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 6) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 6) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 6) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [-1, -1, -1, 2, 0, 0], [-1, 0, 0, 1, 1, 0], [0, 0, 0, 0, -1, 1], [-7, 44, 5, -26, 8, 3]], ![[0, 0, 1, 0, 0, 0], [-1, -1, -1, 2, 0, 0], [-1, 0, 0, 0, 2, 0], [-1, -1, 0, 1, 0, 1], [-7, 44, 5, -26, 9, 2], [0, 120, 54, -94, -10, 17]], ![[0, 0, 0, 1, 0, 0], [-1, 0, 0, 1, 1, 0], [-1, -1, 0, 1, 0, 1], [-5, 21, 2, -11, 5, 2], [0, 60, 27, -47, -5, 9], [-43, 429, 105, -274, 25, 31]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, -1, 1], [-7, 44, 5, -26, 9, 2], [0, 60, 27, -47, -5, 9], [-43, 309, 51, -180, 36, 13], [-5, 787, 374, -596, -76, 88]], ![[0, 0, 0, 0, 0, 1], [-7, 44, 5, -26, 8, 3], [0, 120, 54, -94, -10, 17], [-43, 429, 105, -274, 25, 31], [-5, 787, 374, -596, -76, 88], [-399, 4280, 1227, -2732, 108, 276]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp7321 : Fact (Nat.Prime 7321) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 1]
  b' := [4, 4, 3]
  k := [1]
  f := [-5, 16, 3, 2, 7, 2]
  g := [2, 4, 4, 1]
  h := [2, 4, 4, 1]
  a := [0, 3, 2]
  b := [3, 4, 2, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD7321 : CertificateDedekindCriterionLists l 7321 where
  n := 2
  a' := [2848, 6431, 1499, 4345]
  b' := [4003, 5233, 810, 5562, 6452]
  k := [7135, 4967, 6524, 6590, 1]
  f := [2976, 3112, 2002, 4009, 1812, 1]
  g := [5413, 5659, 3640, 7291, 3294, 1]
  h := [4025, 1]
  a := [2530, 6587, 1152, 4752, 2315]
  b := [3950, 6248, 7266, 7171, 5006]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 3
  p := ![2, 5, 7321]
  exp := ![3, 1, 1]
  pdgood := [5, 7321]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp5.out
    exact hp7321.out
  a := [-605368, -23202, 704934, -39918, -109656]
  b := [-278883, 446698, 79244, -196872, 561, 18276]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7321 T_ofList CD7321

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 4
  n := 2
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0], [1, 0, 0, 1, 1, 0], [0, 0, 0, 0, 1, 1], [1, 0, 1, 0, 0, 1]], ![[0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0], [1, 1, 0, 1, 0, 1], [1, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 1, 0], [1, 1, 0, 1, 0, 1], [1, 1, 0, 1, 1, 0], [0, 0, 1, 1, 1, 1], [1, 1, 1, 0, 1, 1]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 1, 1], [1, 0, 1, 0, 1, 0], [0, 0, 1, 1, 1, 1], [1, 1, 1, 0, 0, 1], [1, 1, 0, 0, 0, 0]], ![[0, 0, 0, 0, 0, 1], [1, 0, 1, 0, 0, 1], [0, 0, 0, 0, 0, 1], [1, 1, 1, 0, 1, 1], [1, 1, 0, 0, 0, 0], [1, 0, 1, 0, 0, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![1, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0]]
  v := ![![1, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 1]]
  v_ind := ![1, 2, 4, 5]
  w_ind := ![0, 3]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 0], ![1, 0, 1, 0, 0, 1], ![1, 0, 1, 0, 1, 1], ![0, 1, 1, 0, 0, 1], ![1, 0, 1, 0, 0, 0]]
  a := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![0, 1, 1, 1], ![43, 5, 12, 3], ![414, 84, 40, 25], ![1380, 538, -53, 139]], ![![44, 5, 8, 4], ![120, 56, -8, 18], ![831, 380, -66, 91], ![4400, 1281, 98, 294]], ![![44, 5, 8, 5], ![164, 61, 2, 20], ![1140, 431, -29, 104], ![5187, 1655, 22, 382]], ![![44, 6, 8, 4], ![120, 54, -8, 18], ![832, 380, -68, 92], ![4444, 1286, 106, 296]], ![![0, 0, 0, 0], ![0, 2, 2, 0], ![44, 6, 10, 2], ![120, 54, -10, 18]]]
  c := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![-2, 2], ![-35, -11], ![-294, -126], ![-960, -495]], ![![-32, -12], ![-84, -47], ![-578, -311], ![-3089, -1413]], ![![-32, -12], ![-117, -60], ![-798, -401], ![-3634, -1711]], ![![-33, -12], ![-84, -46], ![-578, -311], ![-3121, -1426]], ![![0, 1], ![-2, 0], ![-33, -13], ![-82, -47]]]
  d := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2, 2, 2, 0], ![160, 58, 2, 24]], ![![0, 2, 0, 2], ![856, 210, 50, 64]], ![![0, 2, 2, 2], ![976, 264, 40, 82]], ![![2, 2, 0, 2], ![856, 210, 52, 64]], ![![0, 2, 0, 0], ![-2, 0, 0, 2]]]
  e := ![![![1, 0], ![0, 1]], ![![-3, 1], ![-117, -56]], ![![0, 0], ![-602, -272]], ![![-1, 0], ![-684, -319]], ![![-2, 0], ![-604, -272]], ![![0, 0], ![0, 2]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 2, Sum.inl 0), (Sum.inl 3, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 2, Sum.inr 0)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [2]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 2 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M2
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 6) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 6 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 6
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 6 := T_degree

noncomputable def bQ : Basis (Fin 6) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 6) :
    bQ i = Adj.root ^ (i : ℕ) := by
  rw [show bQ i = pb.basis ((finCongr pb_dim).symm i) by
    exact Basis.reindex_apply pb.basis (finCongr pb_dim) i]
  rw [pb.basis_eq_pow, pb_gen]
  congr 1

lemma bOm_cast_eq_vecMul :
    (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) =
      Matrix.vecMul bQ (P.map (algebraMap ℚ K)) := by
  funext j
  change (timesTableO.basis j).val = _
  rw [timesTableO_basis_apply]
  rw [ofList_eq_sum']
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X]
  rw [_root_.map_mul, _root_.map_sum]
  rw [← IsAdjoinRoot.algebraMap_apply Adj]
  have hdist :
      (algebraMap ℚ K) ((algebraMap ℤ ℚ) basisDenominator)⁻¹ *
          (∑ x : Fin 6,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 6,
          (algebraMap ℚ K) ((algebraMap ℤ ℚ) basisDenominator)⁻¹ *
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ)) := by
    exact Finset.mul_sum Finset.univ _ _
  rw [hdist]
  rw [Matrix.vecMul_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [_root_.map_mul, ← IsAdjoinRoot.algebraMap_apply Adj,
    _root_.map_pow, IsAdjoinRoot.map_X Adj]
  rw [bQ_apply]
  simp [P, div_eq_mul_inv, mul_comm, mul_left_comm]

lemma bQ_discr : Algebra.discr ℚ bQ = (T.discr : ℚ) := by
  calc
    Algebra.discr ℚ bQ = Algebra.discr ℚ pb.basis := by
      simpa [bQ] using
        Algebra.discr_reindex ℚ pb.basis (finCongr pb_dim)
    _ = (minpoly ℚ pb.gen).discr :=
      powerBasis_discr_eq_minpoly_discr pb
    _ = (map (algebraMap ℤ ℚ) T).discr := by
      have hqmonic : (map (algebraMap ℤ ℚ) T).Monic :=
        T_monic.map (algebraMap ℤ ℚ)
      rw [show minpoly ℚ pb.gen = map (algebraMap ℤ ℚ) T by
        rw [pb_gen]
        calc
          minpoly ℚ Adj.root =
              map (algebraMap ℤ ℚ) T *
                C (map (algebraMap ℤ ℚ) T).leadingCoeff⁻¹ :=
            AdjoinRoot.minpoly_root hirr.out.ne_zero
          _ = map (algebraMap ℤ ℚ) T := by
            rw [hqmonic.leadingCoeff]
            simp]
    _ = (T.discr : ℚ) := by
      exact (intCast_discr_eq_discr_map T T_monic
        (T_degree ▸ by norm_num)).symm

lemma P_det_index_sq :
    P.det ^ 2 * (row.index : ℚ) ^ 2 = 1 := by
  have htriangular : P.BlockTriangular id := by
    have hcheck :
        (List.ofFn fun i : Fin 6 =>
          (List.ofFn fun j : Fin 6 =>
            decide ((j : ℕ) < (i : ℕ) -> P i j = 0)).all id).all id =
          true := by native_decide
    simp only [List.all_eq_true, List.forall_mem_ofFn_iff, id_eq,
      decide_eq_true_eq] at hcheck
    intro i j hji
    exact hcheck i j hji
  rw [Matrix.det_of_upperTriangular htriangular]
  native_decide

theorem field_discriminant_eq_recorded :
    NumberField.discr K = (row.fieldDiscriminant : ℤ) := by
  apply Rat.intCast_injective
  have hbOmCast :
      ((NumberField.discr K : ℤ) : ℚ) =
        Algebra.discr ℚ
          (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) := by
    rw [← bOm_discr]
    exact discr_ringOfIntegers_cast K bOm
  have hrecorded :
      T.discr = (row.index : ℤ) ^ 2 *
        (row.fieldDiscriminant : ℤ) := by
    simpa [T] using
      (voightPolynomialDiscriminantInput 6 row row_mem)
  have hrecordedQ :
      (T.discr : ℚ) = (row.index : ℚ) ^ 2 *
        (row.fieldDiscriminant : ℚ) := by
    exact_mod_cast hrecorded
  calc
    ((NumberField.discr K : ℤ) : ℚ) =
        Algebra.discr ℚ
          (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) :=
      hbOmCast
    _ = Algebra.discr ℚ
        (Matrix.vecMul bQ (P.map (algebraMap ℚ K))) := by
      rw [bOm_cast_eq_vecMul]
    _ = P.det ^ 2 * Algebra.discr ℚ bQ :=
      Algebra.discr_of_matrix_vecMul bQ P
    _ = P.det ^ 2 * (T.discr : ℚ) := by rw [bQ_discr]
    _ = P.det ^ 2 *
        ((row.index : ℚ) ^ 2 *
          (row.fieldDiscriminant : ℚ)) := by rw [hrecordedQ]
    _ = (P.det ^ 2 * (row.index : ℚ) ^ 2) *
        (row.fieldDiscriminant : ℚ) := by ring
    _ = (row.fieldDiscriminant : ℚ) := by
      rw [P_det_index_sq, one_mul]

end

end VoightMaximalOrderD6R687

namespace VoightMaximalOrderD6R688

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨14662000, [1, -16, 16, 12, -8, -2, 1], 4⟩
local notation "l" => [1, -16, 16, 12, -8, -2, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSix := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSix_irreducible row row_mem
lemma T_monic : Monic T := by
  rw [← T_ofList]
  exact monic_ofList l rfl

abbrev K := AdjoinRoot (map (algebraMap ℤ ℚ) T)
instance hirr : Fact (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map T_monic).1
    T_irreducible
instance KField : Field K := AdjoinRoot.instField
instance : Algebra ℤ K := Ring.toIntAlgebra K
instance : IsScalarTower ℤ ℚ K :=
  IsScalarTower.of_algebraMap_eq' (by ext; simp)
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
  AdjoinRoot.isAdjoinRoot _
local notation "θ" => Adj.root

def basisDenominator : ℤ := 4
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![4, 0, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0], ![0, 0, 4, 0, 0, 0], ![0, 0, 0, 4, 0, 0], ![0, 0, 0, 0, 4, 0], ![1, 3, 1, 3, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-1, -3, -1, -3, -1, 4], ![-1, 2, -4, -5, 2, 3]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-1, -3, -1, -3, -1, 4], ![-3, 10, -18, -18, 6, 8], ![-5, -1, -12, -25, -1, 17]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-1, -3, -1, -3, -1, 4], ![-3, 10, -18, -18, 6, 8], ![-14, -5, -28, -76, -8, 48], ![-16, 32, -68, -94, 10, 47]], ![![0, 0, 0, 0, 1, 0], ![-1, -3, -1, -3, -1, 4], ![-3, 10, -18, -18, 6, 8], ![-14, -5, -28, -76, -8, 48], ![-40, 106, -189, -244, 28, 112], ![-57, 48, -166, -333, -10, 181]], ![![0, 0, 0, 0, 0, 1], ![-1, 2, -4, -5, 2, 3], ![-5, -1, -12, -25, -1, 17], ![-16, 32, -68, -94, 10, 47], ![-57, 48, -166, -333, -10, 181], ![-71, 121, -265, -424, 16, 213]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-4]], ![[], [], [], [], [-16], [-12, -4]], ![[], [], [], [-16], [-32, -16], [-68, -12, -4]], ![[], [], [-16], [-32, -16], [-192, -32, -16], [-188, -68, -12, -4]], ![[], [-4], [-12, -4], [-68, -12, -4], [-188, -68, -12, -4], [-285, -74, -23, -4, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 6 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 6) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 6) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 6) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, -3, -1, -3, -1, 4], [-1, 2, -4, -5, 2, 3]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, -3, -1, -3, -1, 4], [-3, 10, -18, -18, 6, 8], [-5, -1, -12, -25, -1, 17]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, -3, -1, -3, -1, 4], [-3, 10, -18, -18, 6, 8], [-14, -5, -28, -76, -8, 48], [-16, 32, -68, -94, 10, 47]], ![[0, 0, 0, 0, 1, 0], [-1, -3, -1, -3, -1, 4], [-3, 10, -18, -18, 6, 8], [-14, -5, -28, -76, -8, 48], [-40, 106, -189, -244, 28, 112], [-57, 48, -166, -333, -10, 181]], ![[0, 0, 0, 0, 0, 1], [-1, 2, -4, -5, 2, 3], [-5, -1, -12, -25, -1, 17], [-16, 32, -68, -94, 10, 47], [-57, 48, -166, -333, -10, 181], [-71, 121, -265, -424, 16, 213]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp7331 : Fact (Nat.Prime 7331) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 2]
  b' := [0, 0, 1]
  k := [1]
  f := [3, 8, 5, 4, 6, 2]
  g := [4, 3, 4, 1]
  h := [4, 3, 4, 1]
  a := [3, 0, 2]
  b := [3, 3, 2, 4, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD7331 : CertificateDedekindCriterionLists l 7331 where
  n := 2
  a' := [639, 2050, 3796, 4346]
  b' := [1372, 3141, 3882, 646, 597]
  k := [5838, 6157, 4498, 836, 1]
  f := [2293, 6192, 5245, 5754, 394, 1]
  g := [2432, 6567, 5562, 6102, 417, 1]
  h := [6912, 1]
  a := [5638, 3614, 6316, 4660, 5928]
  b := [1337, 1944, 4951, 7057, 1403]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 3
  p := ![2, 5, 7331]
  exp := ![3, 1, 1]
  pdgood := [5, 7331]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp5.out
    exact hp7331.out
  a := [-106168, -107472, 114012, 62140, -32946]
  b := [-24963, 49525, 51313, -33243, -12187, 5491]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7331 T_ofList CD7331

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 2
  n := 4
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 1, 1, 1, 1, 0], [1, 0, 0, 1, 0, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 1, 1, 1, 1, 0], [1, 0, 0, 0, 0, 0], [1, 1, 0, 1, 1, 1]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 1, 1, 1, 1, 0], [1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1]], ![[0, 0, 0, 0, 1, 0], [1, 1, 1, 1, 1, 0], [1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [1, 0, 0, 1, 0, 1]], ![[0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 1], [1, 1, 0, 1, 1, 1], [0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 1], [1, 1, 1, 0, 0, 1]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![1, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0]]
  v := ![![1, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0]]
  w := ![![1, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0]]
  v_ind := ![3, 4]
  w_ind := ![0, 1, 2, 4]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 1, 0, 0, 1, 1], ![0, 1, 1, 1, 1, 1], ![0, 1, 0, 0, 1, 0], ![1, 1, 0, 1, 1, 0], ![0, 1, 0, 0, 1, 1], ![1, 1, 1, 0, 0, 1]]
  a := ![![![-169, 4], ![-588, 19]], ![![-190, 9], ![-681, 17]], ![![-76, -6], ![-250, 26]], ![![-92, 0], ![-326, 20]], ![![-170, 4], ![-588, 18]], ![![-96, 10], ![-358, -2]]]
  c := ![![![22, 48, -36, -48], ![92, 152, -86, -180]], ![![24, 54, -41, -57], ![102, 180, -111, -203]], ![![7, 24, -23, -14], ![44, 60, -23, -95]], ![![10, 28, -25, -23], ![51, 84, -46, -109]], ![![22, 48, -36, -48], ![92, 152, -86, -180]], ![![14, 26, -16, -34], ![50, 98, -68, -94]]]
  d := ![![![0, 2], ![-1540, 20], ![-16, 2], ![-84, 10]], ![![2, 2], ![-1774, 40], ![-14, 4], ![-90, 10]], ![![0, 2], ![-682, -16], ![-6, -2], ![-34, 12]], ![![2, 2], ![-868, 6], ![-6, 0], ![-40, 10]], ![![0, 2], ![-1540, 20], ![-16, 2], ![-84, 10]], ![![0, 0], ![-916, 38], ![-8, 4], ![-48, 0]]]
  e := ![![![0, 1, -1, 0], ![234, 406, -244, -439], ![-1, 7, -8, -4], ![9, 25, -21, -29]], ![![-2, 1, -1, 1], ![266, 469, -287, -518], ![-2, 7, -10, -4], ![7, 29, -28, -31]], ![![0, 0, 0, 0], ![94, 188, -132, -170], ![-2, 4, -6, 0], ![6, 8, -4, -18]], ![![0, 0, 0, 0], ![124, 236, -158, -238], ![-2, 4, -6, 0], ![4, 12, -10, -18]], ![![-1, 1, -1, 0], ![234, 405, -244, -439], ![-1, 7, -9, -4], ![9, 25, -21, -30]], ![![0, 1, 0, 1], ![143, 238, -131, -283], ![0, 3, -2, -3], ![2, 17, -18, -11]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 1, Sum.inr 0), (Sum.inr 0, Sum.inr 0), (Sum.inr 1, Sum.inr 0)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [2]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 2 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M2
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 6) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 6 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 6
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 6 := T_degree

noncomputable def bQ : Basis (Fin 6) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 6) :
    bQ i = Adj.root ^ (i : ℕ) := by
  rw [show bQ i = pb.basis ((finCongr pb_dim).symm i) by
    exact Basis.reindex_apply pb.basis (finCongr pb_dim) i]
  rw [pb.basis_eq_pow, pb_gen]
  congr 1

lemma bOm_cast_eq_vecMul :
    (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) =
      Matrix.vecMul bQ (P.map (algebraMap ℚ K)) := by
  funext j
  change (timesTableO.basis j).val = _
  rw [timesTableO_basis_apply]
  rw [ofList_eq_sum']
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X]
  rw [_root_.map_mul, _root_.map_sum]
  rw [← IsAdjoinRoot.algebraMap_apply Adj]
  have hdist :
      (algebraMap ℚ K) ((algebraMap ℤ ℚ) basisDenominator)⁻¹ *
          (∑ x : Fin 6,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 6,
          (algebraMap ℚ K) ((algebraMap ℤ ℚ) basisDenominator)⁻¹ *
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ)) := by
    exact Finset.mul_sum Finset.univ _ _
  rw [hdist]
  rw [Matrix.vecMul_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [_root_.map_mul, ← IsAdjoinRoot.algebraMap_apply Adj,
    _root_.map_pow, IsAdjoinRoot.map_X Adj]
  rw [bQ_apply]
  simp [P, div_eq_mul_inv, mul_comm, mul_left_comm]

lemma bQ_discr : Algebra.discr ℚ bQ = (T.discr : ℚ) := by
  calc
    Algebra.discr ℚ bQ = Algebra.discr ℚ pb.basis := by
      simpa [bQ] using
        Algebra.discr_reindex ℚ pb.basis (finCongr pb_dim)
    _ = (minpoly ℚ pb.gen).discr :=
      powerBasis_discr_eq_minpoly_discr pb
    _ = (map (algebraMap ℤ ℚ) T).discr := by
      have hqmonic : (map (algebraMap ℤ ℚ) T).Monic :=
        T_monic.map (algebraMap ℤ ℚ)
      rw [show minpoly ℚ pb.gen = map (algebraMap ℤ ℚ) T by
        rw [pb_gen]
        calc
          minpoly ℚ Adj.root =
              map (algebraMap ℤ ℚ) T *
                C (map (algebraMap ℤ ℚ) T).leadingCoeff⁻¹ :=
            AdjoinRoot.minpoly_root hirr.out.ne_zero
          _ = map (algebraMap ℤ ℚ) T := by
            rw [hqmonic.leadingCoeff]
            simp]
    _ = (T.discr : ℚ) := by
      exact (intCast_discr_eq_discr_map T T_monic
        (T_degree ▸ by norm_num)).symm

lemma P_det_index_sq :
    P.det ^ 2 * (row.index : ℚ) ^ 2 = 1 := by
  have htriangular : P.BlockTriangular id := by
    have hcheck :
        (List.ofFn fun i : Fin 6 =>
          (List.ofFn fun j : Fin 6 =>
            decide ((j : ℕ) < (i : ℕ) -> P i j = 0)).all id).all id =
          true := by native_decide
    simp only [List.all_eq_true, List.forall_mem_ofFn_iff, id_eq,
      decide_eq_true_eq] at hcheck
    intro i j hji
    exact hcheck i j hji
  rw [Matrix.det_of_upperTriangular htriangular]
  native_decide

theorem field_discriminant_eq_recorded :
    NumberField.discr K = (row.fieldDiscriminant : ℤ) := by
  apply Rat.intCast_injective
  have hbOmCast :
      ((NumberField.discr K : ℤ) : ℚ) =
        Algebra.discr ℚ
          (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) := by
    rw [← bOm_discr]
    exact discr_ringOfIntegers_cast K bOm
  have hrecorded :
      T.discr = (row.index : ℤ) ^ 2 *
        (row.fieldDiscriminant : ℤ) := by
    simpa [T] using
      (voightPolynomialDiscriminantInput 6 row row_mem)
  have hrecordedQ :
      (T.discr : ℚ) = (row.index : ℚ) ^ 2 *
        (row.fieldDiscriminant : ℚ) := by
    exact_mod_cast hrecorded
  calc
    ((NumberField.discr K : ℤ) : ℚ) =
        Algebra.discr ℚ
          (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) :=
      hbOmCast
    _ = Algebra.discr ℚ
        (Matrix.vecMul bQ (P.map (algebraMap ℚ K))) := by
      rw [bOm_cast_eq_vecMul]
    _ = P.det ^ 2 * Algebra.discr ℚ bQ :=
      Algebra.discr_of_matrix_vecMul bQ P
    _ = P.det ^ 2 * (T.discr : ℚ) := by rw [bQ_discr]
    _ = P.det ^ 2 *
        ((row.index : ℚ) ^ 2 *
          (row.fieldDiscriminant : ℚ)) := by rw [hrecordedQ]
    _ = (P.det ^ 2 * (row.index : ℚ) ^ 2) *
        (row.fieldDiscriminant : ℚ) := by ring
    _ = (row.fieldDiscriminant : ℚ) := by
      rw [P_det_index_sq, one_mul]

end

end VoightMaximalOrderD6R688

namespace VoightMaximalOrderD6R689

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨14680125, [-1, -6, 12, 14, -6, -3, 1], 9⟩
local notation "l" => [-1, -6, 12, 14, -6, -3, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSix := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSix_irreducible row row_mem
lemma T_monic : Monic T := by
  rw [← T_ofList]
  exact monic_ofList l rfl

abbrev K := AdjoinRoot (map (algebraMap ℤ ℚ) T)
instance hirr : Fact (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map T_monic).1
    T_irreducible
instance KField : Field K := AdjoinRoot.instField
instance : Algebra ℤ K := Ring.toIntAlgebra K
instance : IsScalarTower ℤ ℚ K :=
  IsScalarTower.of_algebraMap_eq' (by ext; simp)
noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
  AdjoinRoot.isAdjoinRoot _
local notation "θ" => Adj.root

def basisDenominator : ℤ := 3
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![3, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0], ![0, 0, 0, 3, 0, 0], ![1, 2, 2, 1, 1, 0], ![2, 2, 0, 1, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-1, -2, -2, -1, 3, 0], ![-1, -1, 0, 0, 1, 1], ![-4, -4, -8, -8, 7, 3]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-1, -2, -2, -1, 3, 0], ![-2, -2, 0, -1, 0, 3], ![-5, -6, -9, -8, 8, 4], ![-11, -7, -12, -24, 4, 16]], ![![0, 0, 0, 1, 0, 0], ![-1, -2, -2, -1, 3, 0], ![-2, -2, 0, -1, 0, 3], ![-11, -12, -24, -23, 18, 9], ![-16, -13, -22, -33, 12, 20], ![-44, -31, -87, -116, 44, 52]], ![![0, 0, 0, 0, 1, 0], ![-1, -1, 0, 0, 1, 1], ![-5, -6, -9, -8, 8, 4], ![-16, -13, -22, -33, 12, 20], ![-29, -23, -49, -66, 28, 34], ![-70, -39, -114, -189, 42, 97]], ![![0, 0, 0, 0, 0, 1], ![-4, -4, -8, -8, 7, 3], ![-11, -7, -12, -24, 4, 16], ![-44, -31, -87, -116, 44, 52], ![-70, -39, -114, -189, 42, 97], ![-175, -87, -331, -520, 119, 240]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-3]], ![[], [], [], [], [-3], [-9, -3]], ![[], [], [], [-9], [-12, -3], [-48, -9, -3]], ![[], [], [-3], [-12, -3], [-26, -5, -1], [-76, -21, -4, -1]], ![[], [-3], [-9, -3], [-48, -9, -3], [-76, -21, -4, -1], [-218, -55, -17, -3, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 6 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 6) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 6) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 6) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [-1, -2, -2, -1, 3, 0], [-1, -1, 0, 0, 1, 1], [-4, -4, -8, -8, 7, 3]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [-1, -2, -2, -1, 3, 0], [-2, -2, 0, -1, 0, 3], [-5, -6, -9, -8, 8, 4], [-11, -7, -12, -24, 4, 16]], ![[0, 0, 0, 1, 0, 0], [-1, -2, -2, -1, 3, 0], [-2, -2, 0, -1, 0, 3], [-11, -12, -24, -23, 18, 9], [-16, -13, -22, -33, 12, 20], [-44, -31, -87, -116, 44, 52]], ![[0, 0, 0, 0, 1, 0], [-1, -1, 0, 0, 1, 1], [-5, -6, -9, -8, 8, 4], [-16, -13, -22, -33, 12, 20], [-29, -23, -49, -66, 28, 34], [-70, -39, -114, -189, 42, 97]], ![[0, 0, 0, 0, 0, 1], [-4, -4, -8, -8, 7, 3], [-11, -7, -12, -24, 4, 16], [-44, -31, -87, -116, 44, 52], [-70, -39, -114, -189, 42, 97], [-175, -87, -331, -520, 119, 240]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp13049 : Fact (Nat.Prime 13049) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 1]
  b' := [4, 1, 3]
  k := [1]
  f := [2, 6, 2, 0, 3, 1]
  g := [3, 4, 1, 1]
  h := [3, 4, 1, 1]
  a := [2, 3, 1]
  b := [4, 2, 3, 0, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD13049 : CertificateDedekindCriterionLists l 13049 where
  n := 2
  a' := [3479, 12413, 5339, 9634]
  b' := [837, 6654, 3718, 3837, 683]
  k := [10672, 1374, 5163, 10258, 1]
  f := [97, 836, 919, 333, 1245, 1]
  g := [908, 7825, 8597, 3111, 11652, 1]
  h := [1394, 1]
  a := [2126, 2473, 9020, 8970, 1343]
  b := [2604, 1105, 2667, 5201, 11706]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
  n := 3
  p := ![3, 5, 13049]
  exp := ![1, 1, 1]
  pdgood := [5, 13049]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp5.out
    exact hp13049.out
  a := [-88551, -190224, 104118, 75552, -29544]
  b := [-17864, 48799, 65917, -27060, -15054, 4924]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 13049 T_ofList CD13049

noncomputable def M3 : MaximalOrderCertificateLists 3 O Om hm where
  m := 2
  n := 4
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [2, 1, 1, 2, 0, 0], [2, 2, 0, 0, 1, 1], [2, 2, 1, 1, 1, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [2, 1, 1, 2, 0, 0], [1, 1, 0, 2, 0, 0], [1, 0, 0, 1, 2, 1], [1, 2, 0, 0, 1, 1]], ![[0, 0, 0, 1, 0, 0], [2, 1, 1, 2, 0, 0], [1, 1, 0, 2, 0, 0], [1, 0, 0, 1, 0, 0], [2, 2, 2, 0, 0, 2], [1, 2, 0, 1, 2, 1]], ![[0, 0, 0, 0, 1, 0], [2, 2, 0, 0, 1, 1], [1, 0, 0, 1, 2, 1], [2, 2, 2, 0, 0, 2], [1, 1, 2, 0, 1, 1], [2, 0, 0, 0, 0, 1]], ![[0, 0, 0, 0, 0, 1], [2, 2, 1, 1, 1, 0], [1, 2, 0, 0, 1, 1], [1, 2, 0, 1, 2, 1], [2, 0, 0, 0, 0, 1], [2, 0, 2, 2, 2, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![2, 2, 1, 0, 0, 0], ![2, 1, 0, 1, 0, 0]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 1], ![1, 1, 0, 0, 2, 1], ![1, 2, 0, 0, 0, 0]]
  v := ![![2, 2, 1, 0, 0, 0], ![2, 1, 0, 1, 0, 0]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 1], ![1, 1, 0, 0, 2, 1], ![1, 2, 0, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 1], ![0, 0, 1, 0, 2, 1], ![0, 0, 0, 1, 0, 0]]
  v_ind := ![2, 3]
  w_ind := ![0, 1, 2, 3]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![4, 0, 2, 0, 0, 2], ![0, 4, 2, 0, 0, 2], ![0, 2, 2, 4, 0, 0], ![2, 0, 2, 2, 0, 0], ![2, 0, 2, 0, 0, 2], ![0, 0, 2, 4, 4, 2]]
  a := ![![![-52, -78], ![-186, -244]], ![![-48, -74], ![-190, -252]], ![![-12, 0], ![-102, -90]], ![![-6, 0], ![-48, -42]], ![![-54, -78], ![-186, -246]], ![![-108, -114], ![-378, -468]]]
  c := ![![![51, 9, 7, 18], ![168, 23, 17, 71]], ![![45, 9, 7, 16], ![168, 21, 19, 73]], ![![-1, -1, 5, -2], ![63, -1, 15, 32]], ![![0, -1, 3, -1], ![31, 1, 7, 14]], ![![51, 9, 7, 18], ![168, 23, 17, 71]], ![![75, 9, 19, 26], ![318, 39, 41, 133]]]
  d := ![![![6, 0], ![-2106, -3306], ![-3576, -5670], ![-90, -84]], ![![6, 0], ![-2190, -3402], ![-3660, -5766], ![-66, -84]], ![![6, 12], ![-1182, -1590], ![-1812, -2466], ![-30, 0]], ![![6, 6], ![-606, -840], ![-972, -1326], ![-18, 6]], ![![6, 0], ![-2106, -3306], ![-3576, -5670], ![-90, -84]], ![![6, 12], ![-4542, -6978], ![-7716, -11706], ![-138, -96]]]
  e := ![![![3, 2, 0, -3], ![2202, 392, 130, 896], ![3767, 694, 234, 1487], ![57, 0, 14, 33]], ![![-3, 2, 0, -1], ![2262, 386, 144, 926], ![3821, 696, 248, 1511], ![47, 0, 14, 23]], ![![-9, 0, 0, -3], ![1074, 141, 105, 459], ![1659, 255, 171, 660], ![-3, -12, 12, 3]], ![![-3, 0, 0, -3], ![567, 87, 51, 234], ![894, 141, 93, 351], ![-3, -6, 6, 3]], ![![1, 2, 0, -3], ![2202, 390, 130, 896], ![3767, 694, 232, 1487], ![57, 0, 14, 31]], ![![-9, 0, 2, -5], ![4652, 808, 310, 1874], ![7805, 1384, 572, 3067], ![61, -10, 32, 31]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 1, Sum.inr 0), (Sum.inr 0, Sum.inr 0), (Sum.inr 1, Sum.inr 0)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [3]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 3 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M3
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [3] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 6) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 6 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 6
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 6 := T_degree

noncomputable def bQ : Basis (Fin 6) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 6) :
    bQ i = Adj.root ^ (i : ℕ) := by
  rw [show bQ i = pb.basis ((finCongr pb_dim).symm i) by
    exact Basis.reindex_apply pb.basis (finCongr pb_dim) i]
  rw [pb.basis_eq_pow, pb_gen]
  congr 1

lemma bOm_cast_eq_vecMul :
    (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) =
      Matrix.vecMul bQ (P.map (algebraMap ℚ K)) := by
  funext j
  change (timesTableO.basis j).val = _
  rw [timesTableO_basis_apply]
  rw [ofList_eq_sum']
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X]
  rw [_root_.map_mul, _root_.map_sum]
  rw [← IsAdjoinRoot.algebraMap_apply Adj]
  have hdist :
      (algebraMap ℚ K) ((algebraMap ℤ ℚ) basisDenominator)⁻¹ *
          (∑ x : Fin 6,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 6,
          (algebraMap ℚ K) ((algebraMap ℤ ℚ) basisDenominator)⁻¹ *
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ)) := by
    exact Finset.mul_sum Finset.univ _ _
  rw [hdist]
  rw [Matrix.vecMul_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [_root_.map_mul, ← IsAdjoinRoot.algebraMap_apply Adj,
    _root_.map_pow, IsAdjoinRoot.map_X Adj]
  rw [bQ_apply]
  simp [P, div_eq_mul_inv, mul_comm, mul_left_comm]

lemma bQ_discr : Algebra.discr ℚ bQ = (T.discr : ℚ) := by
  calc
    Algebra.discr ℚ bQ = Algebra.discr ℚ pb.basis := by
      simpa [bQ] using
        Algebra.discr_reindex ℚ pb.basis (finCongr pb_dim)
    _ = (minpoly ℚ pb.gen).discr :=
      powerBasis_discr_eq_minpoly_discr pb
    _ = (map (algebraMap ℤ ℚ) T).discr := by
      have hqmonic : (map (algebraMap ℤ ℚ) T).Monic :=
        T_monic.map (algebraMap ℤ ℚ)
      rw [show minpoly ℚ pb.gen = map (algebraMap ℤ ℚ) T by
        rw [pb_gen]
        calc
          minpoly ℚ Adj.root =
              map (algebraMap ℤ ℚ) T *
                C (map (algebraMap ℤ ℚ) T).leadingCoeff⁻¹ :=
            AdjoinRoot.minpoly_root hirr.out.ne_zero
          _ = map (algebraMap ℤ ℚ) T := by
            rw [hqmonic.leadingCoeff]
            simp]
    _ = (T.discr : ℚ) := by
      exact (intCast_discr_eq_discr_map T T_monic
        (T_degree ▸ by norm_num)).symm

lemma P_det_index_sq :
    P.det ^ 2 * (row.index : ℚ) ^ 2 = 1 := by
  have htriangular : P.BlockTriangular id := by
    have hcheck :
        (List.ofFn fun i : Fin 6 =>
          (List.ofFn fun j : Fin 6 =>
            decide ((j : ℕ) < (i : ℕ) -> P i j = 0)).all id).all id =
          true := by native_decide
    simp only [List.all_eq_true, List.forall_mem_ofFn_iff, id_eq,
      decide_eq_true_eq] at hcheck
    intro i j hji
    exact hcheck i j hji
  rw [Matrix.det_of_upperTriangular htriangular]
  native_decide

theorem field_discriminant_eq_recorded :
    NumberField.discr K = (row.fieldDiscriminant : ℤ) := by
  apply Rat.intCast_injective
  have hbOmCast :
      ((NumberField.discr K : ℤ) : ℚ) =
        Algebra.discr ℚ
          (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) := by
    rw [← bOm_discr]
    exact discr_ringOfIntegers_cast K bOm
  have hrecorded :
      T.discr = (row.index : ℤ) ^ 2 *
        (row.fieldDiscriminant : ℤ) := by
    simpa [T] using
      (voightPolynomialDiscriminantInput 6 row row_mem)
  have hrecordedQ :
      (T.discr : ℚ) = (row.index : ℚ) ^ 2 *
        (row.fieldDiscriminant : ℚ) := by
    exact_mod_cast hrecorded
  calc
    ((NumberField.discr K : ℤ) : ℚ) =
        Algebra.discr ℚ
          (fun i => (((bOm i : NumberField.RingOfIntegers K) : K))) :=
      hbOmCast
    _ = Algebra.discr ℚ
        (Matrix.vecMul bQ (P.map (algebraMap ℚ K))) := by
      rw [bOm_cast_eq_vecMul]
    _ = P.det ^ 2 * Algebra.discr ℚ bQ :=
      Algebra.discr_of_matrix_vecMul bQ P
    _ = P.det ^ 2 * (T.discr : ℚ) := by rw [bQ_discr]
    _ = P.det ^ 2 *
        ((row.index : ℚ) ^ 2 *
          (row.fieldDiscriminant : ℚ)) := by rw [hrecordedQ]
    _ = (P.det ^ 2 * (row.index : ℚ) ^ 2) *
        (row.fieldDiscriminant : ℚ) := by ring
    _ = (row.fieldDiscriminant : ℚ) := by
      rw [P_det_index_sq, one_mul]

end

end VoightMaximalOrderD6R689

end TraceEuclidean
