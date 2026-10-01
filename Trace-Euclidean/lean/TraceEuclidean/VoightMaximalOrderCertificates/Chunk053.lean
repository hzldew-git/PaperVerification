import TraceEuclidean.VoightMaximalOrderCertificates.Chunk049
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

namespace VoightMaximalOrderD6R431

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨10718125, [-9, -18, 14, 16, -6, -3, 1], 3⟩
local notation "l" => [-9, -18, 14, 16, -6, -3, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![3, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0], ![0, 0, 0, 3, 0, 0], ![0, 0, 0, 0, 3, 0], ![0, 2, 1, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, -2, -1, 0, 0, 3], ![3, 4, -5, -5, 2, 3]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, -2, -1, 0, 0, 3], ![9, 12, -17, -16, 6, 9], ![9, 11, -13, -20, 1, 15]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, -2, -1, 0, 0, 3], ![9, 12, -17, -16, 6, 9], ![27, 33, -39, -62, 2, 45], ![45, 67, -65, -88, 10, 48]], ![![0, 0, 0, 0, 1, 0], ![0, -2, -1, 0, 0, 3], ![9, 12, -17, -16, 6, 9], ![27, 33, -39, -62, 2, 45], ![135, 203, -194, -264, 28, 141], ![144, 217, -183, -305, 8, 174]], ![![0, 0, 0, 0, 0, 1], ![3, 4, -5, -5, 2, 3], ![9, 11, -13, -20, 1, 15], ![45, 67, -65, -88, 10, 48], ![144, 217, -183, -305, 8, 174], ![179, 281, -228, -361, 16, 189]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-3]], ![[], [], [], [], [-9], [-9, -3]], ![[], [], [], [-9], [-27, -9], [-45, -9, -3]], ![[], [], [-9], [-27, -9], [-135, -27, -9], [-144, -45, -9, -3]], ![[], [-3], [-9, -3], [-45, -9, -3], [-144, -45, -9, -3], [-179, -49, -15, -3, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, -2, -1, 0, 0, 3], [3, 4, -5, -5, 2, 3]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, -2, -1, 0, 0, 3], [9, 12, -17, -16, 6, 9], [9, 11, -13, -20, 1, 15]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, -2, -1, 0, 0, 3], [9, 12, -17, -16, 6, 9], [27, 33, -39, -62, 2, 45], [45, 67, -65, -88, 10, 48]], ![[0, 0, 0, 0, 1, 0], [0, -2, -1, 0, 0, 3], [9, 12, -17, -16, 6, 9], [27, 33, -39, -62, 2, 45], [135, 203, -194, -264, 28, 141], [144, 217, -183, -305, 8, 174]], ![[0, 0, 0, 0, 0, 1], [3, 4, -5, -5, 2, 3], [9, 11, -13, -20, 1, 15], [45, 67, -65, -88, 10, 48], [144, 217, -183, -305, 8, 174], [179, 281, -228, -361, 16, 189]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp1559 : Fact (Nat.Prime 1559) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 4
  a' := [4]
  b' := [0, 3]
  k := [1, 3, 1]
  f := [5, 6, -2, -1, 2, 1]
  g := [4, 0, 1]
  h := [4, 3, 0, 2, 1]
  a := [0, 1]
  b := [4, 0, 0, 3, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [9, 3, 8, 3]
  b' := [7, 2, 3, 1, 6]
  k := [7, 5, 0, 0, 1]
  f := [3, 4, 1, -1, 2, 1]
  g := [6, 5, 5, 0, 4, 1]
  h := [4, 1]
  a := [5, 4, 1, 8, 1]
  b := [5, 7, 8, 5, 10]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1559 : CertificateDedekindCriterionLists l 1559 where
  n := 2
  a' := [428, 1270, 1500, 411]
  b' := [899, 955, 1181, 328, 1165]
  k := [186, 1423, 674, 818, 1]
  f := [9, 343, 164, 17, 281, 1]
  g := [38, 1449, 689, 70, 1187, 1]
  h := [369, 1]
  a := [243, 403, 126, 992, 622]
  b := [763, 166, 720, 1300, 937]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
  n := 4
  p := ![3, 5, 11, 1559]
  exp := ![2, 1, 1, 1]
  pdgood := [5, 11, 1559]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp5.out
    exact hp11.out
    exact hp1559.out
  a := [59227, -324312, 19272, 228936, -77664]
  b := [-72486, -9827, 152159, -26202, -44628, 12944]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1559 T_ofList CD1559

noncomputable def M3 : MaximalOrderCertificateOfUnramifiedLists 3 O Om hm where
  n := 6
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 1, 2, 0, 0, 0], [0, 1, 1, 1, 2, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 1, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0], [0, 2, 2, 1, 1, 0]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 1, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0], [0, 0, 0, 1, 2, 0], [0, 1, 1, 2, 1, 0]], ![[0, 0, 0, 0, 1, 0], [0, 1, 2, 0, 0, 0], [0, 0, 1, 2, 0, 0], [0, 0, 0, 1, 2, 0], [0, 2, 1, 0, 1, 0], [0, 1, 0, 1, 2, 0]], ![[0, 0, 0, 0, 0, 1], [0, 1, 1, 1, 2, 0], [0, 2, 2, 1, 1, 0], [0, 1, 1, 2, 1, 0], [0, 1, 0, 1, 2, 0], [2, 2, 0, 2, 1, 0]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![0, 1, 1, 1, 0, 0], ![0, 2, 0, 1, 0, 0], ![0, 1, 2, 1, 0, 0], ![0, 0, 2, 2, 1, 0], ![0, 1, 1, 2, 0, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [3]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 3 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M3
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

end VoightMaximalOrderD6R431

namespace VoightMaximalOrderD6R433

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨10758881, [-43, -46, 38, 24, -13, -2, 1], 56⟩
local notation "l" => [-43, -46, 38, 24, -13, -2, 1]
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

def basisDenominator : ℤ := 14
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![14, 0, 0, 0, 0, 0], ![0, 14, 0, 0, 0, 0], ![0, 0, 14, 0, 0, 0], ![7, 0, 7, 7, 0, 0], ![7, 7, 7, 0, 7, 0], ![9, 5, 4, 2, 2, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![-1, 0, -1, 2, 0, 0], ![-1, 0, -1, 1, 1, 0], ![-3, -1, 0, -1, -2, 7], ![2, 2, -2, -4, 1, 4]], ![![0, 0, 1, 0, 0, 0], ![-1, 0, -1, 2, 0, 0], ![-1, -1, -1, 0, 2, 0], ![-3, -2, 0, -2, -1, 7], ![21, 13, -14, -27, 10, 14], ![11, 9, 0, -25, -2, 23]], ![![0, 0, 0, 1, 0, 0], ![-1, 0, -1, 1, 1, 0], ![-3, -2, 0, -2, -1, 7], ![8, 5, -7, -15, 3, 14], ![30, 26, 6, -74, -11, 70], ![44, 34, -6, -70, 0, 51]], ![![0, 0, 0, 0, 1, 0], ![-3, -1, 0, -1, -2, 7], ![21, 13, -14, -27, 10, 14], ![30, 26, 6, -74, -11, 70], ![232, 168, -66, -284, 40, 147], ![145, 121, 14, -241, -21, 177]], ![![0, 0, 0, 0, 0, 1], ![2, 2, -2, -4, 1, 4], ![11, 9, 0, -25, -2, 23], ![44, 34, -6, -70, 0, 51], ![145, 121, 14, -241, -21, 177], ![140, 114, 2, -208, -9, 139]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-14]], ![[], [], [], [], [-98], [-56, -14]], ![[], [], [], [-49], [-147, -49], [-189, -35, -7]], ![[], [], [-98], [-147, -49], [-931, -98, -49], [-581, -168, -28, -7]], ![[], [-14], [-56, -14], [-189, -35, -7], [-581, -168, -28, -7], [-549, -136, -33, -6, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [-1, 0, -1, 2, 0, 0], [-1, 0, -1, 1, 1, 0], [-3, -1, 0, -1, -2, 7], [2, 2, -2, -4, 1, 4]], ![[0, 0, 1, 0, 0, 0], [-1, 0, -1, 2, 0, 0], [-1, -1, -1, 0, 2, 0], [-3, -2, 0, -2, -1, 7], [21, 13, -14, -27, 10, 14], [11, 9, 0, -25, -2, 23]], ![[0, 0, 0, 1, 0, 0], [-1, 0, -1, 1, 1, 0], [-3, -2, 0, -2, -1, 7], [8, 5, -7, -15, 3, 14], [30, 26, 6, -74, -11, 70], [44, 34, -6, -70, 0, 51]], ![[0, 0, 0, 0, 1, 0], [-3, -1, 0, -1, -2, 7], [21, 13, -14, -27, 10, 14], [30, 26, 6, -74, -11, 70], [232, 168, -66, -284, 40, 147], [145, 121, 14, -241, -21, 177]], ![[0, 0, 0, 0, 0, 1], [2, 2, -2, -4, 1, 4], [11, 9, 0, -25, -2, 23], [44, 34, -6, -70, 0, 51], [145, 121, 14, -241, -21, 177], [140, 114, 2, -208, -9, 139]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp4481 : Fact (Nat.Prime 4481) := fact_iff.2 (by norm_num)

def CD4481 : CertificateDedekindCriterionLists l 4481 where
  n := 2
  a' := [1708, 1598, 3072, 2879]
  b' := [451, 2444, 1388, 828, 3009]
  k := [3947, 4286, 1257, 2598, 1]
  f := [2929, 1442, 902, 1797, 922, 1]
  g := [4126, 2030, 1270, 2531, 1298, 1]
  h := [3181, 1]
  a := [3629, 1397, 4322, 4309, 713]
  b := [2046, 4252, 79, 3881, 3768]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 7] where
  n := 3
  p := ![2, 7, 4481]
  exp := ![1, 2, 1]
  pdgood := [4481]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp7.out
    exact hp4481.out
  a := [-63948, 43572, 165816, -3482, -22326]
  b := [50231, 106208, 2696, -46021, -660, 3721]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 4481 T_ofList CD4481

noncomputable def M2 : MaximalOrderCertificateOfUnramifiedLists 2 O Om hm where
  n := 6
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0], [1, 0, 1, 1, 1, 0], [1, 1, 0, 1, 0, 1], [0, 0, 0, 0, 1, 0]], ![[0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0], [1, 0, 0, 0, 1, 1], [1, 1, 0, 1, 0, 0], [1, 1, 0, 1, 0, 1]], ![[0, 0, 0, 1, 0, 0], [1, 0, 1, 1, 1, 0], [1, 0, 0, 0, 1, 1], [0, 1, 1, 1, 1, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 0, 0, 0, 1, 0], [1, 1, 0, 1, 0, 1], [1, 1, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [1, 1, 0, 1, 1, 1]], ![[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0], [1, 1, 0, 1, 0, 1], [0, 0, 0, 0, 0, 1], [1, 1, 0, 1, 1, 1], [0, 0, 0, 0, 1, 1]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hindw := by decide
  hwFrobComp := by decide

noncomputable def M7 : MaximalOrderCertificateLists 7 O Om hm where
  m := 4
  n := 2
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [6, 0, 6, 2, 0, 0], [6, 0, 6, 1, 1, 0], [4, 6, 0, 6, 5, 0], [2, 2, 5, 3, 1, 4]], ![[0, 0, 1, 0, 0, 0], [6, 0, 6, 2, 0, 0], [6, 6, 6, 0, 2, 0], [4, 5, 0, 5, 6, 0], [0, 6, 0, 1, 3, 0], [4, 2, 0, 3, 5, 2]], ![[0, 0, 0, 1, 0, 0], [6, 0, 6, 1, 1, 0], [4, 5, 0, 5, 6, 0], [1, 5, 0, 6, 3, 0], [2, 5, 6, 3, 3, 0], [2, 6, 1, 0, 0, 2]], ![[0, 0, 0, 0, 1, 0], [4, 6, 0, 6, 5, 0], [0, 6, 0, 1, 3, 0], [2, 5, 6, 3, 3, 0], [1, 0, 4, 3, 5, 0], [5, 2, 0, 4, 0, 2]], ![[0, 0, 0, 0, 0, 1], [2, 2, 5, 3, 1, 4], [4, 2, 0, 3, 5, 2], [2, 6, 1, 0, 0, 2], [5, 2, 0, 4, 0, 2], [0, 2, 2, 2, 5, 6]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![3, 4, 1, 0, 0, 0], ![2, 6, 0, 1, 0, 0], ![3, 4, 0, 0, 1, 0], ![2, 4, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![4, 3, 0, 0, 0, 0]]
  v := ![![3, 4, 1, 0, 0, 0], ![2, 6, 0, 1, 0, 0], ![3, 4, 0, 0, 1, 0], ![2, 4, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![4, 3, 0, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 1, 1, 4, 0]]
  v_ind := ![2, 3, 4, 5]
  w_ind := ![0, 1]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![15, 0, 9, 18, 6, 9], ![0, 18, 12, 3, 15, 18], ![6, 18, 18, 18, 18, 15], ![3, 6, 3, 9, 6, 0], ![18, 12, 9, 9, 12, 0]]
  a := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![-231, -393, 120, 756], ![-396, -1347, 81, 1680], ![-441, -5418, 36, 4200], ![-168, -4791, -153, 3783]], ![![-336, -1056, 144, 1407], ![-231, -2775, -174, 3192], ![-984, -9393, 282, 6657], ![84, -8175, -489, 6402]], ![![-420, -903, 210, 1512], ![-378, -2772, -126, 3549], ![-1260, -10605, 399, 7728], ![-18, -9300, -507, 7455]], ![![-105, -105, 63, 315], ![-63, -504, -42, 819], ![-399, -2394, 168, 1764], ![0, -2121, -126, 1785]], ![![-168, -231, 105, 567], ![-21, -903, -168, 1533], ![-861, -4242, 441, 2940], ![84, -3717, -294, 3192]]]
  c := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![-42, 0], ![-512, 158], ![-2830, 958], ![-2478, 831]], ![![-336, 93], ![-1061, 317], ![-5180, 1790], ![-4200, 1395]], ![![-175, 31], ![-946, 268], ![-5774, 1991], ![-4725, 1566]], ![![31, -19], ![-104, 17], ![-1305, 453], ![-1043, 341]], ![![21, -21], ![-168, 21], ![-2401, 847], ![-1803, 585]]]
  d := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![63, 126, 42, 63], ![-693, 378, 483, 1890]], ![![84, 21, 105, 126], ![-357, -1176, 231, 4221]], ![![126, 126, 126, 105], ![-504, 0, 441, 4326]], ![![21, 63, 42, 0], ![-42, 441, 105, 882]], ![![63, 63, 84, 0], ![126, 567, 21, 1764]]]
  e := ![![![1, 0], ![0, 1]], ![![188, -68], ![1025, -401]], ![![117, -60], ![708, -399]], ![![224, -98], ![1715, -770]], ![![70, -28], ![721, -301]], ![![105, -42], ![1197, -504]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 2, Sum.inl 0), (Sum.inl 3, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 3, Sum.inr 0)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [2, 7]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 2 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M2
    exact @pMaximal_of_MaximalOrderCertificateLists K 7 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M7
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 7] D q hq hbad)
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

end VoightMaximalOrderD6R433

namespace VoightMaximalOrderD6R437

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨10784448, [-2, 22, 31, -4, -11, 0, 1], 4⟩
local notation "l" => [-2, 22, 31, -4, -11, 0, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![0, 0, 0, 2, 0, 0], ![0, 0, 1, 1, 1, 0], ![0, 0, 1, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, -1, -1, 2, 0], ![0, 0, -1, 0, 1, 1], ![1, -11, -21, -3, 11, 0]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, -1, -1, 2, 0], ![0, 0, -1, 0, 0, 2], ![1, -11, -22, -4, 12, 1], ![0, 1, -19, -18, 5, 11]], ![![0, 0, 0, 1, 0, 0], ![0, 0, -1, -1, 2, 0], ![0, 0, -1, 0, 0, 2], ![2, -22, -42, -7, 22, 0], ![1, -10, -40, -21, 15, 12], ![11, -121, -217, -34, 90, 5]], ![![0, 0, 0, 0, 1, 0], ![0, 0, -1, 0, 1, 1], ![1, -11, -22, -4, 12, 1], ![1, -10, -40, -21, 15, 12], ![7, -76, -159, -40, 66, 14], ![8, -82, -259, -125, 86, 53]], ![![0, 0, 0, 0, 0, 1], ![1, -11, -21, -3, 11, 0], ![0, 1, -19, -18, 5, 11], ![11, -121, -217, -34, 90, 5], ![8, -82, -259, -125, 86, 53], ![45, -492, -916, -186, 338, 44]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-2]], ![[], [], [], [], [-2], [0, -2]], ![[], [], [], [-4], [-2, -2], [-22, 0, -2]], ![[], [], [-2], [-2, -2], [-14, -2, -1], [-16, -12, -1, -1]], ![[], [-2], [0, -2], [-22, 0, -2], [-16, -12, -1, -1], [-90, -6, -11, 0, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, -1, -1, 2, 0], [0, 0, -1, 0, 1, 1], [1, -11, -21, -3, 11, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, -1, -1, 2, 0], [0, 0, -1, 0, 0, 2], [1, -11, -22, -4, 12, 1], [0, 1, -19, -18, 5, 11]], ![[0, 0, 0, 1, 0, 0], [0, 0, -1, -1, 2, 0], [0, 0, -1, 0, 0, 2], [2, -22, -42, -7, 22, 0], [1, -10, -40, -21, 15, 12], [11, -121, -217, -34, 90, 5]], ![[0, 0, 0, 0, 1, 0], [0, 0, -1, 0, 1, 1], [1, -11, -22, -4, 12, 1], [1, -10, -40, -21, 15, 12], [7, -76, -159, -40, 66, 14], [8, -82, -259, -125, 86, 53]], ![[0, 0, 0, 0, 0, 1], [1, -11, -21, -3, 11, 0], [0, 1, -19, -18, 5, 11], [11, -121, -217, -34, 90, 5], [8, -82, -259, -125, 86, 53], [45, -492, -916, -186, 338, 44]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp79 : Fact (Nat.Prime 79) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 2
  a' := []
  b' := [2]
  k := [1]
  f := [1, -6, -9, 2, 5]
  g := [1, 2, 0, 1]
  h := [1, 2, 0, 1]
  a := [1, 2, 1]
  b := [0, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD79 : CertificateDedekindCriterionLists l 79 where
  n := 2
  a' := [32, 27, 32]
  b' := [33, 31, 46, 71]
  k := [56, 46, 1]
  f := [36, 52, 59, 67, 18, 1]
  g := [58, 18, 74, 23, 1]
  h := [49, 56, 1]
  a := [50, 56, 59, 52]
  b := [33, 60, 74, 43, 27]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 3
  p := ![2, 3, 79]
  exp := ![3, 1, 1]
  pdgood := [3, 79]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp3.out
    exact hp79.out
  a := [-530, -340, 706, 102, -156]
  b := [38, 392, 67, -213, -17, 26]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 79 T_ofList CD79

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 3
  n := 3
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0], [0, 0, 1, 0, 1, 1], [1, 1, 1, 1, 1, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0], [0, 0, 1, 0, 0, 0], [1, 1, 0, 0, 0, 1], [0, 1, 1, 0, 1, 1]], ![[0, 0, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 1, 0], [1, 1, 1, 0, 0, 1]], ![[0, 0, 0, 0, 1, 0], [0, 0, 1, 0, 1, 1], [1, 1, 0, 0, 0, 1], [1, 0, 0, 1, 1, 0], [1, 0, 1, 0, 0, 0], [0, 0, 1, 1, 0, 1]], ![[0, 0, 0, 0, 0, 1], [1, 1, 1, 1, 1, 0], [0, 1, 1, 0, 1, 1], [1, 1, 1, 0, 0, 1], [0, 0, 1, 1, 0, 1], [1, 0, 0, 0, 0, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 1, 1, 1, 0, 0], ![1, 1, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 1, 1, 0, 0, 0]]
  v := ![![0, 1, 1, 1, 0, 0], ![1, 1, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 1, 1, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0]]
  v_ind := ![3, 4, 5]
  w_ind := ![0, 2, 3]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![1, 1, 0, 1, 0, 1], ![0, 0, 1, 1, 0, 0], ![0, 1, 1, 1, 0, 0], ![0, 1, 0, 0, 1, 1], ![1, 0, 1, 1, 1, 0]]
  a := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![-62, 132, 18], ![-149, 116, 67], ![-222, 439, 51]], ![![-8, 26, 4], ![-24, 29, 13], ![-51, 95, 16]], ![![-8, 28, 4], ![-24, 30, 14], ![-54, 106, 16]], ![![-80, 136, 30], ![-168, 166, 70], ![-314, 436, 98]], ![![-32, 54, 18], ![-64, 98, 28], ![-176, 182, 70]]]
  c := ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![-68, 8, -119], ![-86, 52, -86], ![-216, 46, -466]], ![![-14, -1, -19], ![-20, 6, -19], ![-50, 10, -92]], ![![-15, -2, -19], ![-21, 6, -19], ![-55, 10, -101]], ![![-76, 16, -120], ![-110, 53, -136], ![-240, 88, -441]], ![![-34, 6, -38], ![-58, 14, -79], ![-116, 55, -159]]]
  d := ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![2, 0, 2], ![-8, 26, 0], ![-42, 36, 26]], ![![2, 0, 0], ![0, 4, 0], ![-2, 8, 4]], ![![2, 0, 0], ![0, 4, 0], ![0, 8, 4]], ![![0, 2, 2], ![-6, 24, 2], ![-48, 58, 26]], ![![2, 2, 0], ![0, 6, 2], ![-10, 34, 8]]]
  e := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![0, 1, -1], ![-12, -2, -17], ![-30, 13, -19]], ![![0, -1, 0], ![-2, -1, -1], ![-6, -1, -2]], ![![0, 0, 0], ![-2, -2, 0], ![-6, -2, -2]], ![![-2, 0, 0], ![-12, -2, -18], ![-40, 12, -38]], ![![0, -2, 0], ![-4, 0, -2], ![-20, -2, -20]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 2, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 1, Sum.inr 1), (Sum.inl 2, Sum.inr 1)]
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

end VoightMaximalOrderD6R437

namespace VoightMaximalOrderD6R440

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨10826109, [-29, -67, 45, 24, -13, -2, 1], 7⟩
local notation "l" => [-29, -67, 45, 24, -13, -2, 1]
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

def basisDenominator : ℤ := 7
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![7, 0, 0, 0, 0, 0], ![0, 7, 0, 0, 0, 0], ![0, 0, 7, 0, 0, 0], ![0, 0, 0, 7, 0, 0], ![0, 0, 0, 0, 7, 0], ![6, 4, 6, 4, 4, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-6, -4, -6, -4, -4, 7], ![-1, 7, -11, -6, -1, 6]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-6, -4, -6, -4, -4, 7], ![17, 59, -57, -32, 5, 14], ![0, 45, -53, -43, -8, 29]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-6, -4, -6, -4, -4, 7], ![17, 59, -57, -32, 5, 14], ![-44, 95, -125, -161, -66, 119], ![19, 235, -226, -195, -40, 118]], ![![0, 0, 0, 0, 1, 0], ![-6, -4, -6, -4, -4, 7], ![17, 59, -57, -32, 5, 14], ![-44, 95, -125, -161, -66, 119], ![277, 1053, -818, -575, -16, 252], ![122, 1005, -823, -774, -153, 428]], ![![0, 0, 0, 0, 0, 1], ![-1, 7, -11, -6, -1, 6], ![0, 45, -53, -43, -8, 29], ![19, 235, -226, -195, -40, 118], ![122, 1005, -823, -774, -153, 428], ![150, 1284, -1049, -991, -202, 555]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-7]], ![[], [], [], [], [-49], [-42, -7]], ![[], [], [], [-49], [-98, -49], [-203, -42, -7]], ![[], [], [-49], [-98, -49], [-833, -98, -49], [-826, -203, -42, -7]], ![[], [-7], [-42, -7], [-203, -42, -7], [-826, -203, -42, -7], [-1056, -264, -57, -10, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-6, -4, -6, -4, -4, 7], [-1, 7, -11, -6, -1, 6]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-6, -4, -6, -4, -4, 7], [17, 59, -57, -32, 5, 14], [0, 45, -53, -43, -8, 29]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-6, -4, -6, -4, -4, 7], [17, 59, -57, -32, 5, 14], [-44, 95, -125, -161, -66, 119], [19, 235, -226, -195, -40, 118]], ![[0, 0, 0, 0, 1, 0], [-6, -4, -6, -4, -4, 7], [17, 59, -57, -32, 5, 14], [-44, 95, -125, -161, -66, 119], [277, 1053, -818, -575, -16, 252], [122, 1005, -823, -774, -153, 428]], ![[0, 0, 0, 0, 0, 1], [-1, 7, -11, -6, -1, 6], [0, 45, -53, -43, -8, 29], [19, 235, -226, -195, -40, 118], [122, 1005, -823, -774, -153, 428], [150, 1284, -1049, -991, -202, 555]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp167 : Fact (Nat.Prime 167) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 2
  a' := [1]
  b' := [1, 0, 2]
  k := [1]
  f := [11, 25, -11, -4, 7, 2]
  g := [2, 2, 2, 1]
  h := [2, 2, 2, 1]
  a := [2, 1, 1]
  b := [0, 1, 1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD167 : CertificateDedekindCriterionLists l 167 where
  n := 2
  a' := [18, 31, 42, 42]
  b' := [132, 28, 130, 80, 25]
  k := [69, 112, 108, 24, 1]
  f := [97, 108, 41, 120, 11, 1]
  g := [105, 116, 44, 130, 11, 1]
  h := [154, 1]
  a := [154, 81, 10, 71, 62]
  b := [82, 7, 109, 96, 105]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [7] where
  n := 3
  p := ![3, 7, 167]
  exp := ![1, 2, 1]
  pdgood := [3, 167]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp7.out
    exact hp167.out
  a := [-95268, 90872, 137120, -21448, -22404]
  b := [40869, 110834, -21408, -42300, 2330, 3734]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 167 T_ofList CD167

noncomputable def M7 : MaximalOrderCertificateLists 7 O Om hm where
  m := 4
  n := 2
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 3, 1, 3, 3, 0], [6, 0, 3, 1, 6, 6]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 3, 1, 3, 3, 0], [3, 3, 6, 3, 5, 0], [0, 3, 3, 6, 6, 1]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 3, 1, 3, 3, 0], [3, 3, 6, 3, 5, 0], [5, 4, 1, 0, 4, 0], [5, 4, 5, 1, 2, 6]], ![[0, 0, 0, 0, 1, 0], [1, 3, 1, 3, 3, 0], [3, 3, 6, 3, 5, 0], [5, 4, 1, 0, 4, 0], [4, 3, 1, 6, 5, 0], [3, 4, 3, 3, 1, 1]], ![[0, 0, 0, 0, 0, 1], [6, 0, 3, 1, 6, 6], [0, 3, 3, 6, 6, 1], [5, 4, 5, 1, 2, 6], [3, 4, 3, 3, 1, 1], [3, 3, 1, 3, 1, 2]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![3, 4, 1, 0, 0, 0], ![2, 1, 0, 1, 0, 0], ![4, 5, 0, 0, 1, 0], ![5, 6, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![4, 2, 0, 0, 0, 0]]
  v := ![![3, 4, 1, 0, 0, 0], ![2, 1, 0, 1, 0, 0], ![4, 5, 0, 0, 1, 0], ![5, 6, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![4, 2, 0, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 2, 0, 1, 0]]
  v_ind := ![2, 3, 4, 5]
  w_ind := ![0, 1]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![4, 4, 6, 8, 8, 0], ![4, 12, 4, 2, 12, 10], ![0, 10, 4, 6, 0, 12], ![0, 10, 12, 0, 12, 0], ![4, 8, 10, 2, 10, 0]]
  a := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![-658, -364, -58, 392], ![-1524, -1574, -516, 1162], ![-8106, -6194, -726, 3360], ![-8988, -8150, -1700, 4906]], ![![-1890, -1220, -212, 1078], ![-4060, -4058, -1218, 2828], ![-19430, -15650, -2110, 8442], ![-22162, -20446, -4256, 12028]], ![![-1148, -784, -140, 714], ![-3192, -2604, -462, 1624], ![-11508, -10738, -2282, 6384], ![-14978, -13672, -2742, 8036]], ![![-896, -518, -84, 504], ![-1610, -2016, -854, 1596], ![-10822, -7504, -364, 3682], ![-10934, -10080, -2170, 6048]], ![![-756, -434, -70, 434], ![-1456, -1736, -700, 1358], ![-9268, -6566, -420, 3304], ![-9562, -8778, -1876, 5278]]]
  c := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![-238, 91], ![-750, 319], ![-5492, 2249], ![-5726, 2374]], ![![-840, 333], ![-2214, 933], ![-13306, 5465], ![-14476, 6004]], ![![-490, 191], ![-1942, 800], ![-7424, 3083], ![-9786, 4050]], ![![-376, 146], ![-686, 301], ![-7660, 3116], ![-7028, 2915]], ![![-308, 119], ![-644, 280], ![-6496, 2646], ![-6130, 2542]]]
  d := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![42, 56, 56, 0], ![-448, -140, -112, 784]], ![![28, 14, 84, 70], ![-2268, -1400, -448, 2296]], ![![28, 42, 0, 84], ![-1596, -784, -84, 1344]], ![![84, 0, 84, 0], ![-532, -504, -336, 1176]], ![![70, 14, 70, 0], ![-448, -364, -252, 980]]]
  e := ![![![1, 0], ![0, 1]], ![![74, -34], ![368, -178]], ![![142, -63], ![-56, -26]], ![![84, -42], ![-308, 70]], ![![112, -49], ![476, -224]], ![![98, -42], ![420, -196]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 2, Sum.inl 0), (Sum.inl 3, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 3, Sum.inr 0)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [7]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 7 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M7
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [7] D q hq hbad)
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

end VoightMaximalOrderD6R440

end TraceEuclidean
