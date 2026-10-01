import TraceEuclidean.VoightMaximalOrderCertificates.Chunk051
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

namespace VoightMaximalOrderD6R456

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨11053625, [1, -9, 18, 4, -10, -1, 1], 4⟩
local notation "l" => [1, -9, 18, 4, -10, -1, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![4, 0, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0], ![0, 0, 4, 0, 0, 0], ![0, 0, 0, 4, 0, 0], ![0, 0, 0, 0, 4, 0], ![1, 2, 0, 0, 2, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-1, -2, 0, 0, -2, 4], ![-1, 1, -4, -1, 1, 3]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-1, -2, 0, 0, -2, 4], ![-2, 7, -18, -4, 8, 4], ![-4, 0, -11, -7, 0, 13]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-1, -2, 0, 0, -2, 4], ![-2, 7, -18, -4, 8, 4], ![-12, -14, -9, -22, -16, 44], ![-13, 9, -52, -24, 6, 39]], ![![0, 0, 0, 0, 1, 0], ![-1, -2, 0, 0, -2, 4], ![-2, 7, -18, -4, 8, 4], ![-12, -14, -9, -22, -16, 44], ![-28, 64, -190, -53, 54, 68], ![-45, 14, -147, -91, 3, 141]], ![![0, 0, 0, 0, 0, 1], ![-1, 1, -4, -1, 1, 3], ![-4, 0, -11, -7, 0, 13], ![-13, 9, -52, -24, 6, 39], ![-45, 14, -147, -91, 3, 141], ![-59, 30, -213, -118, 13, 181]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-4]], ![[], [], [], [], [-16], [-12, -4]], ![[], [], [], [-16], [-16, -16], [-52, -12, -4]], ![[], [], [-16], [-16, -16], [-176, -16, -16], [-156, -52, -12, -4]], ![[], [-4], [-12, -4], [-52, -12, -4], [-156, -52, -12, -4], [-221, -65, -19, -5, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, -2, 0, 0, -2, 4], [-1, 1, -4, -1, 1, 3]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, -2, 0, 0, -2, 4], [-2, 7, -18, -4, 8, 4], [-4, 0, -11, -7, 0, 13]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, -2, 0, 0, -2, 4], [-2, 7, -18, -4, 8, 4], [-12, -14, -9, -22, -16, 44], [-13, 9, -52, -24, 6, 39]], ![[0, 0, 0, 0, 1, 0], [-1, -2, 0, 0, -2, 4], [-2, 7, -18, -4, 8, 4], [-12, -14, -9, -22, -16, 44], [-28, 64, -190, -53, 54, 68], [-45, 14, -147, -91, 3, 141]], ![[0, 0, 0, 0, 0, 1], [-1, 1, -4, -1, 1, 3], [-4, 0, -11, -7, 0, 13], [-13, 9, -52, -24, 6, 39], [-45, 14, -147, -91, 3, 141], [-59, 30, -213, -118, 13, 181]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp8039 : Fact (Nat.Prime 8039) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3]
  b' := [1, 4]
  k := [1]
  f := [0, 3, -1, 2, 4, 1]
  g := [1, 3, 2, 1]
  h := [1, 3, 2, 1]
  a := [4, 1, 1]
  b := [1, 0, 4, 2, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [2, 8, 4, 2]
  b' := [9, 0, 7, 1, 4]
  k := [4, 2, 9, 0, 1]
  f := [4, 3, 0, 4, 4, 1]
  g := [9, 3, 3, 9, 5, 1]
  h := [5, 1]
  a := [8, 9, 6, 10]
  b := [7, 8, 4, 1]
  c := [1]
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD8039 : CertificateDedekindCriterionLists l 8039 where
  n := 2
  a' := [1226, 2656, 1381, 4395]
  b' := [3515, 6524, 3979, 26, 7160]
  k := [4191, 7583, 3156, 7122, 1]
  f := [353, 249, 343, 69, 432, 1]
  g := [6196, 4357, 6011, 1198, 7580, 1]
  h := [458, 1]
  a := [6743, 6195, 2531, 3955, 5432]
  b := [1466, 6379, 3425, 3650, 2607]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 4
  p := ![2, 5, 11, 8039]
  exp := ![3, 1, 1, 1]
  pdgood := [5, 11, 8039]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp5.out
    exact hp11.out
    exact hp8039.out
  a := [-36686405, -1644165, 41774343, 3601539, -6161022]
  b := [-4469285, 18626580, 1460222, -10427754, -771396, 1026837]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 8039 T_ofList CD8039

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

end VoightMaximalOrderD6R456

namespace VoightMaximalOrderD6R460

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨11125125, [-9, -15, 22, 13, -9, -2, 1], 27⟩
local notation "l" => [-9, -15, 22, 13, -9, -2, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![3, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0], ![0, 1, 2, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, -1, -2, 3, 0, 0], ![0, -1, -1, 2, 1, 0], ![0, 0, 0, 0, 0, 1], ![3, 6, 0, -12, 9, 2]], ![![0, 0, 1, 0, 0, 0], ![0, -1, -2, 3, 0, 0], ![0, -1, 0, 0, 3, 0], ![0, -1, -1, 1, 2, 1], ![3, 6, 0, -12, 9, 2], ![6, 27, 18, -48, 6, 13]], ![![0, 0, 0, 1, 0, 0], ![0, -1, -1, 2, 1, 0], ![0, -1, -1, 1, 2, 1], ![1, 1, -1, -3, 5, 2], ![4, 13, 6, -24, 8, 6], ![18, 58, 25, -102, 30, 20]], ![![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1], ![3, 6, 0, -12, 9, 2], ![4, 13, 6, -24, 8, 6], ![13, 38, 13, -66, 23, 11], ![33, 132, 78, -225, 33, 45]], ![![0, 0, 0, 0, 0, 1], ![3, 6, 0, -12, 9, 2], ![6, 27, 18, -48, 6, 13], ![18, 58, 25, -102, 30, 20], ![33, 132, 78, -225, 33, 45], ![135, 450, 201, -756, 180, 123]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-3]], ![[], [], [], [], [-3], [-6, -3]], ![[], [], [], [-1], [-4, -1], [-18, -4, -1]], ![[], [], [-3], [-4, -1], [-13, -2, -1], [-33, -13, -2, -1]], ![[], [-3], [-6, -3], [-18, -4, -1], [-33, -13, -2, -1], [-135, -33, -13, -2, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, -1, -2, 3, 0, 0], [0, -1, -1, 2, 1, 0], [0, 0, 0, 0, 0, 1], [3, 6, 0, -12, 9, 2]], ![[0, 0, 1, 0, 0, 0], [0, -1, -2, 3, 0, 0], [0, -1, 0, 0, 3, 0], [0, -1, -1, 1, 2, 1], [3, 6, 0, -12, 9, 2], [6, 27, 18, -48, 6, 13]], ![[0, 0, 0, 1, 0, 0], [0, -1, -1, 2, 1, 0], [0, -1, -1, 1, 2, 1], [1, 1, -1, -3, 5, 2], [4, 13, 6, -24, 8, 6], [18, 58, 25, -102, 30, 20]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [3, 6, 0, -12, 9, 2], [4, 13, 6, -24, 8, 6], [13, 38, 13, -66, 23, 11], [33, 132, 78, -225, 33, 45]], ![[0, 0, 0, 0, 0, 1], [3, 6, 0, -12, 9, 2], [6, 27, 18, -48, 6, 13], [18, 58, 25, -102, 30, 20], [33, 132, 78, -225, 33, 45], [135, 450, 201, -756, 180, 123]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp31 : Fact (Nat.Prime 31) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 1]
  b' := [2, 1, 3]
  k := [1]
  f := [5, 3, 2, -1, 5, 2]
  g := [4, 0, 4, 1]
  h := [4, 0, 4, 1]
  a := [1]
  b := [4, 3, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [6, 4, 0, 3]
  b' := [2, 2, 3, 4, 6]
  k := [6, 4, 0, 5, 1]
  f := [1, 2, -1, 1, 3, 1]
  g := [1, 3, 4, 10, 7, 1]
  h := [2, 1]
  a := [9, 3, 7, 2, 6]
  b := [3, 3, 8, 0, 5]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [25, 13, 9, 26]
  b' := [19, 14, 27, 26, 18]
  k := [13, 16, 12, 11, 1]
  f := [5, 8, 7, 4, 6, 1]
  g := [17, 25, 25, 13, 19, 1]
  h := [8, 1]
  a := [12, 28, 12, 28, 15]
  b := [17, 14, 1, 22, 14]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD31 : CertificateDedekindCriterionLists l 31 where
  n := 2
  a' := [13, 1, 30, 4]
  b' := [14, 5, 6, 11, 24]
  k := [29, 17, 3, 22, 1]
  f := [15, 8, 7, 11, 7, 1]
  g := [24, 11, 12, 18, 10, 1]
  h := [19, 1]
  a := [26, 7, 22, 8, 3]
  b := [29, 15, 26, 1, 28]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
  n := 5
  p := ![3, 5, 11, 29, 31]
  exp := ![2, 1, 1, 1, 1]
  pdgood := [5, 11, 29, 31]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp5.out
    exact hp11.out
    exact hp29.out
    exact hp31.out
  a := [-29185, -53866, 57406, 19778, -12864]
  b := [-12156, 25847, 20830, -16092, -4011, 2144]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
    exact satisfiesDedekindCriterion_of_certificate_lists T l 31 T_ofList CD31

noncomputable def M3 : MaximalOrderCertificateLists 3 O Om hm where
  m := 2
  n := 4
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0], [0, 2, 2, 2, 1, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2]], ![[0, 0, 1, 0, 0, 0], [0, 2, 1, 0, 0, 0], [0, 2, 0, 0, 0, 0], [0, 2, 2, 1, 2, 1], [0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1]], ![[0, 0, 0, 1, 0, 0], [0, 2, 2, 2, 1, 0], [0, 2, 2, 1, 2, 1], [1, 1, 2, 0, 2, 2], [1, 1, 0, 0, 2, 0], [0, 1, 1, 0, 0, 2]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2], [1, 1, 0, 0, 2, 0], [1, 2, 1, 0, 2, 2], [0, 0, 0, 0, 0, 0]], ![[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 2], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0]]
  v := ![![0, 1, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 2, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 1]]
  v_ind := ![2, 5]
  w_ind := ![0, 1, 3, 4]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![4, 4, 4, 2, 0, 0], ![2, 2, 0, 0, 2, 4], ![1, 0, 2, 0, 0, 0], ![0, 4, 4, 0, 0, 2], ![0, 2, 2, 0, 0, 0]]
  a := ![![![1, 0], ![0, 1]], ![![-12, 2], ![122, 104]], ![![72, 66], ![960, 588]], ![![-3, 0], ![36, 27]], ![![24, 30], ![474, 306]], ![![-6, 0], ![36, 30]]]
  c := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 10, 6], ![24, 21, -148, 40]], ![![14, 12, -86, 26], ![204, 186, -1166, 268]], ![![0, 0, 2, 2], ![4, 3, -32, 4]], ![![6, 5, -32, 14], ![102, 93, -584, 140]], ![![0, 0, 4, 2], ![6, 5, -40, 10]]]
  d := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![12, 0], ![-36, 0], ![-30, 24], ![36, 72]], ![![0, 12], ![12, 60], ![330, 276], ![1014, 612]], ![![6, 0], ![-24, 0], ![-6, 6], ![0, 12]], ![![12, 6], ![-24, 24], ![126, 132], ![468, 306]], ![![6, 0], ![-12, 0], ![-12, 6], ![0, 18]]]
  e := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![4, 0, 2, 0], ![0, 4, 32, 4], ![2, 2, 10, 22], ![20, 19, -96, 56]], ![![2, 1, 0, 2], ![24, 24, -96, 72], ![80, 73, -450, 138], ![158, 133, -1032, 180]], ![![1, -1, 0, 0], ![0, 3, 12, 0], ![0, 0, 3, 4], ![6, 6, -24, 19]], ![![0, 0, 0, 0], ![12, 12, -24, 36], ![36, 33, -192, 72], ![78, 66, -498, 102]], ![![0, 0, 0, 0], ![0, 0, 12, 0], ![0, 0, 6, 6], ![6, 6, -24, 18]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 1, Sum.inr 0), (Sum.inl 0, Sum.inr 1), (Sum.inl 1, Sum.inr 1)]
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

end VoightMaximalOrderD6R460

namespace VoightMaximalOrderD6R461

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨11149137, [-1, -8, 8, 12, -7, -2, 1], 8⟩
local notation "l" => [-1, -8, 8, 12, -7, -2, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![1, 0, 1, 1, 0, 0], ![1, 1, 1, 0, 1, 0], ![1, 1, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![-1, 0, -1, 2, 0, 0], ![-1, 0, -1, 1, 1, 0], ![-1, 0, 0, 1, 0, 1], ![2, 0, -1, -12, 7, 2]], ![![0, 0, 1, 0, 0, 0], ![-1, 0, -1, 2, 0, 0], ![-1, -1, -1, 0, 2, 0], ![-1, -1, 0, 0, 1, 1], ![1, -1, -2, -11, 8, 2], ![10, 2, 11, -31, 2, 11]], ![![0, 0, 0, 1, 0, 0], ![-1, 0, -1, 1, 1, 0], ![-1, -1, 0, 0, 1, 1], ![0, -1, -1, -5, 4, 2], ![5, 0, 4, -21, 6, 7], ![25, 6, 11, -85, 24, 18]], ![![0, 0, 0, 0, 1, 0], ![-1, 0, 0, 1, 0, 1], ![1, -1, -2, -11, 8, 2], ![5, 0, 4, -21, 6, 7], ![21, 4, 4, -81, 31, 15], ![71, 21, 62, -201, 19, 54]], ![![0, 0, 0, 0, 0, 1], ![2, 0, -1, -12, 7, 2], ![10, 2, 11, -31, 2, 11], ![25, 6, 11, -85, 24, 18], ![71, 21, 62, -201, 19, 54], ![203, 65, 95, -621, 153, 110]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-2]], ![[], [], [], [], [-2], [-4, -2]], ![[], [], [], [-1], [-3, -1], [-13, -3, -1]], ![[], [], [-2], [-3, -1], [-13, -2, -1], [-27, -12, -2, -1]], ![[], [-2], [-4, -2], [-13, -3, -1], [-27, -12, -2, -1], [-95, -24, -11, -2, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [-1, 0, -1, 2, 0, 0], [-1, 0, -1, 1, 1, 0], [-1, 0, 0, 1, 0, 1], [2, 0, -1, -12, 7, 2]], ![[0, 0, 1, 0, 0, 0], [-1, 0, -1, 2, 0, 0], [-1, -1, -1, 0, 2, 0], [-1, -1, 0, 0, 1, 1], [1, -1, -2, -11, 8, 2], [10, 2, 11, -31, 2, 11]], ![[0, 0, 0, 1, 0, 0], [-1, 0, -1, 1, 1, 0], [-1, -1, 0, 0, 1, 1], [0, -1, -1, -5, 4, 2], [5, 0, 4, -21, 6, 7], [25, 6, 11, -85, 24, 18]], ![[0, 0, 0, 0, 1, 0], [-1, 0, 0, 1, 0, 1], [1, -1, -2, -11, 8, 2], [5, 0, 4, -21, 6, 7], [21, 4, 4, -81, 31, 15], [71, 21, 62, -201, 19, 54]], ![[0, 0, 0, 0, 0, 1], [2, 0, -1, -12, 7, 2], [10, 2, 11, -31, 2, 11], [25, 6, 11, -85, 24, 18], [71, 21, 62, -201, 19, 54], [203, 65, 95, -621, 153, 110]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp491 : Fact (Nat.Prime 491) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 3
  a' := [1, 1, 1]
  b' := [1, 0, 2, 2]
  k := [1, 1, 0, 0, 2, 2, 1]
  f := [1, 4, -1, -3, 3, 1]
  g := [2, 2, 1, 0, 1]
  h := [1, 1, 1]
  a := [0, 2]
  b := [2, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 3
  a' := [20, 20, 17]
  b' := [3, 15, 7, 3]
  k := [20, 24, 11, 8, 25, 21, 1]
  f := [4, 22, 30, 23, 8, 1]
  g := [5, 25, 26, 16, 1]
  h := [23, 11, 1]
  a := [16, 27, 26, 18]
  b := [28, 0, 19, 2, 11]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD491 : CertificateDedekindCriterionLists l 491 where
  n := 2
  a' := [223, 412, 116, 371]
  b' := [19, 393, 289, 415, 24]
  k := [394, 173, 272, 471, 1]
  f := [2, 9, 4, 2, 9, 1]
  g := [109, 478, 166, 92, 480, 1]
  h := [9, 1]
  a := [194, 293, 182, 190, 334]
  b := [46, 385, 225, 4, 157]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 4
  p := ![2, 3, 29, 491]
  exp := ![1, 1, 1, 1]
  pdgood := [3, 29, 491]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp3.out
    exact hp29.out
    exact hp491.out
  a := [-23762, -55128, 57244, 17456, -12684]
  b := [-7709, 15235, 19990, -14678, -3614, 2114]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
    exact satisfiesDedekindCriterion_of_certificate_lists T l 491 T_ofList CD491

noncomputable def M2 : MaximalOrderCertificateOfUnramifiedLists 2 O Om hm where
  n := 6
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0], [1, 0, 1, 1, 1, 0], [1, 0, 0, 1, 0, 1], [0, 0, 1, 0, 1, 0]], ![[0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0], [1, 1, 0, 0, 1, 1], [1, 1, 0, 1, 0, 0], [0, 0, 1, 1, 0, 1]], ![[0, 0, 0, 1, 0, 0], [1, 0, 1, 1, 1, 0], [1, 1, 0, 0, 1, 1], [0, 1, 1, 1, 0, 0], [1, 0, 0, 1, 0, 1], [1, 0, 1, 1, 0, 0]], ![[0, 0, 0, 0, 1, 0], [1, 0, 0, 1, 0, 1], [1, 1, 0, 1, 0, 0], [1, 0, 0, 1, 0, 1], [1, 0, 0, 1, 1, 1], [1, 1, 0, 1, 1, 0]], ![[0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 1, 0], [0, 0, 1, 1, 0, 1], [1, 0, 1, 1, 0, 0], [1, 1, 0, 1, 1, 0], [1, 1, 1, 1, 1, 0]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
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

end VoightMaximalOrderD6R461

namespace VoightMaximalOrderD6R464

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨11188748, [-1, 2, 10, -2, -8, 0, 1], 4⟩
local notation "l" => [-1, 2, 10, -2, -8, 0, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![0, 0, 0, 2, 0, 0], ![1, 1, 0, 1, 1, 0], ![1, 0, 1, 1, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-1, -1, 0, -1, 2, 0], ![-1, 0, 0, -1, 1, 1], ![-4, -5, -5, -3, 9, 0]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-1, -1, 0, -1, 2, 0], ![-1, 0, -1, -1, 0, 2], ![-4, -5, -5, -3, 8, 1], ![-6, -1, -5, -11, 3, 9]], ![![0, 0, 0, 1, 0, 0], ![-1, -1, 0, -1, 2, 0], ![-1, 0, -1, -1, 0, 2], ![-7, -10, -10, -6, 16, 0], ![-9, -6, -10, -13, 11, 8], ![-28, -40, -46, -24, 62, 3]], ![![0, 0, 0, 0, 1, 0], ![-1, 0, 0, -1, 1, 1], ![-4, -5, -5, -3, 8, 1], ![-9, -6, -10, -13, 11, 8], ![-20, -21, -28, -23, 35, 10], ![-41, -32, -53, -60, 56, 33]], ![![0, 0, 0, 0, 0, 1], ![-4, -5, -5, -3, 9, 0], ![-6, -1, -5, -11, 3, 9], ![-28, -40, -46, -24, 62, 3], ![-41, -32, -53, -60, 56, 33], ![-115, -154, -190, -112, 239, 27]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-2]], ![[], [], [], [], [-2], [0, -2]], ![[], [], [], [-4], [-2, -2], [-18, 0, -2]], ![[], [], [-2], [-2, -2], [-9, -2, -1], [-13, -9, -1, -1]], ![[], [-2], [0, -2], [-18, 0, -2], [-13, -9, -1, -1], [-71, -4, -10, 0, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [-1, -1, 0, -1, 2, 0], [-1, 0, 0, -1, 1, 1], [-4, -5, -5, -3, 9, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [-1, -1, 0, -1, 2, 0], [-1, 0, -1, -1, 0, 2], [-4, -5, -5, -3, 8, 1], [-6, -1, -5, -11, 3, 9]], ![[0, 0, 0, 1, 0, 0], [-1, -1, 0, -1, 2, 0], [-1, 0, -1, -1, 0, 2], [-7, -10, -10, -6, 16, 0], [-9, -6, -10, -13, 11, 8], [-28, -40, -46, -24, 62, 3]], ![[0, 0, 0, 0, 1, 0], [-1, 0, 0, -1, 1, 1], [-4, -5, -5, -3, 8, 1], [-9, -6, -10, -13, 11, 8], [-20, -21, -28, -23, 35, 10], [-41, -32, -53, -60, 56, 33]], ![[0, 0, 0, 0, 0, 1], [-4, -5, -5, -3, 9, 0], [-6, -1, -5, -11, 3, 9], [-28, -40, -46, -24, 62, 3], [-41, -32, -53, -60, 56, 33], [-115, -154, -190, -112, 239, 27]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp71 : Fact (Nat.Prime 71) := fact_iff.2 (by norm_num)
instance hp39397 : Fact (Nat.Prime 39397) := fact_iff.2 (by norm_num)

def CD71 : CertificateDedekindCriterionLists l 71 where
  n := 2
  a' := [69, 16, 19, 55]
  b' := [9, 49, 2, 21, 60]
  k := [52, 70, 37, 42, 1]
  f := [31, 2, 2, 5, 15, 1]
  g := [44, 2, 3, 7, 21, 1]
  h := [50, 1]
  a := [45, 26, 50, 67, 32]
  b := [49, 0, 5, 54, 39]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD39397 : CertificateDedekindCriterionLists l 39397 where
  n := 2
  a' := [19269, 353, 25273, 28337]
  b' := [11534, 30328, 13133, 37160, 2212]
  k := [31977, 8304, 30899, 6852, 1]
  f := [8998, 24750, 7368, 33380, 3129, 1]
  g := [9855, 27107, 8069, 36559, 3426, 1]
  h := [35971, 1]
  a := [5079, 22070, 24341, 6655, 2263]
  b := [3370, 26824, 29737, 35104, 37134]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 3
  p := ![2, 71, 39397]
  exp := ![1, 1, 1]
  pdgood := [71, 39397]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp71.out
    exact hp39397.out
  a := [-5169056, 375540, 11875164, 451152, -2369898]
  b := [212659, 3230236, -257061, -3032482, -75192, 394983]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 71 T_ofList CD71
    exact satisfiesDedekindCriterion_of_certificate_lists T l 39397 T_ofList CD39397

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 1
  n := 5
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0], [1, 0, 0, 1, 1, 1], [0, 1, 1, 1, 1, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0], [0, 1, 1, 1, 0, 1], [0, 1, 1, 1, 1, 1]], ![[0, 0, 0, 1, 0, 0], [1, 1, 0, 1, 0, 0], [1, 0, 1, 1, 0, 0], [1, 0, 0, 0, 0, 0], [1, 0, 0, 1, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 0, 0, 0, 1, 0], [1, 0, 0, 1, 1, 1], [0, 1, 1, 1, 0, 1], [1, 0, 0, 1, 1, 0], [0, 1, 0, 1, 1, 0], [1, 0, 1, 0, 0, 1]], ![[0, 0, 0, 0, 0, 1], [0, 1, 1, 1, 1, 0], [0, 1, 1, 1, 1, 1], [0, 0, 0, 0, 0, 1], [1, 0, 1, 0, 0, 1], [1, 0, 0, 0, 1, 1]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![1, 0, 0, 1, 0, 0]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![1, 1, 0, 0, 1, 0], ![1, 0, 0, 0, 1, 1]]
  v := ![![1, 0, 0, 1, 0, 0]]
  w := ![![1, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![1, 1, 0, 0, 1, 0], ![1, 0, 0, 0, 1, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  v_ind := ![3]
  w_ind := ![0, 1, 2, 4, 5]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![0, 1, 0, 1, 1, 0], ![1, 0, 1, 1, 1, 0], ![1, 1, 0, 1, 1, 0], ![1, 0, 1, 0, 0, 0], ![0, 0, 1, 1, 0, 1], ![1, 0, 0, 1, 0, 0]]
  a := ![![![-19]], ![![-18]], ![![-18]], ![![0]], ![![-30]], ![![-4]]]
  c := ![![![-4, -10, -19, 11, 4]], ![![-3, -10, -17, 9, 5]], ![![-4, -10, -19, 11, 4]], ![![0, 0, 1, -1, 1]], ![![-14, -28, -61, 36, 3]], ![![-4, -5, -13, 8, 0]]]
  d := ![![![2], ![-4], ![-4], ![-76], ![-246]], ![![2], ![-8], ![-2], ![-78], ![-266]], ![![2], ![-4], ![-4], ![-76], ![-246]], ![![0], ![-2], ![2], ![-4], ![-28]], ![![2], ![-24], ![-6], ![-156], ![-444]], ![![2], ![0], ![-2], ![-26], ![-72]]]
  e := ![![![-2, 0, 0, 1, 0], ![-6, -6, -10, 6, 3], ![-4, 1, -3, 2, 1], ![-8, -37, -58, 31, 20], ![-13, -142, -223, 120, 55]], ![![-2, 1, -1, 1, 0], ![-8, -4, -14, 8, 3], ![-4, 0, -2, 2, 1], ![-12, -42, -71, 39, 20], ![-5, -146, -217, 112, 65]], ![![-1, 0, 0, 1, 0], ![-6, -5, -10, 6, 3], ![-4, 1, -2, 2, 1], ![-8, -37, -58, 32, 20], ![-13, -142, -223, 120, 56]], ![![0, 1, 0, 0, 0], ![-3, 2, -3, 2, 0], ![-1, 0, 1, 0, 0], ![-6, -4, -12, 8, 1], ![2, -9, -7, 1, 11]], ![![-2, 1, 1, -1, 1], ![4, -5, 5, -7, 12], ![-8, -5, -17, 11, 0], ![5, -72, -92, 43, 43], ![-52, -308, -535, 297, 82]], ![![0, 0, 0, 0, 0], ![0, 0, 2, -2, 2], ![-2, 0, -2, 2, 0], ![0, -10, -12, 6, 8], ![-18, -56, -108, 62, 12]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inr 0, Sum.inr 0), (Sum.inr 1, Sum.inr 0), (Sum.inr 3, Sum.inr 0), (Sum.inl 0, Sum.inr 1)]
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

end VoightMaximalOrderD6R464

end TraceEuclidean
