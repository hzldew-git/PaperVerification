import TraceEuclidean.VoightMaximalOrderCertificates.Chunk044
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

namespace VoightMaximalOrderD6R363

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨9462528, [-2, -4, 12, 6, -10, -2, 1], 19⟩
local notation "l" => [-2, -4, 12, 6, -10, -2, 1]
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

def basisDenominator : ℤ := 19
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![19, 0, 0, 0, 0, 0], ![0, 19, 0, 0, 0, 0], ![0, 0, 19, 0, 0, 0], ![0, 0, 0, 19, 0, 0], ![0, 0, 0, 0, 19, 0], ![12, 1, 10, 5, 14, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-12, -1, -10, -5, -14, 19], ![-10, 0, -9, -4, -11, 16]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-12, -1, -10, -5, -14, 19], ![-22, 2, -32, -16, -18, 38], ![-28, 1, -34, -18, -26, 47]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-12, -1, -10, -5, -14, 19], ![-22, 2, -32, -16, -18, 38], ![-164, -4, -160, -94, -182, 266], ![-158, -2, -162, -92, -171, 258]], ![![0, 0, 0, 0, 1, 0], ![-12, -1, -10, -5, -14, 19], ![-22, 2, -32, -16, -18, 38], ![-164, -4, -160, -94, -182, 266], ![-476, 18, -578, -314, -472, 798], ![-528, 13, -614, -339, -536, 879]], ![![0, 0, 0, 0, 0, 1], ![-10, 0, -9, -4, -11, 16], ![-28, 1, -34, -18, -26, 47], ![-158, -2, -162, -92, -171, 258], ![-528, 13, -614, -339, -536, 879], ![-570, 10, -647, -360, -586, 946]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-19]], ![[], [], [], [], [-361], [-304, -19]], ![[], [], [], [-361], [-722, -361], [-893, -304, -19]], ![[], [], [-361], [-722, -361], [-5054, -722, -361], [-4902, -893, -304, -19]], ![[], [-19], [-304, -19], [-893, -304, -19], [-4902, -893, -304, -19], [-4887, -1006, -276, -30, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-12, -1, -10, -5, -14, 19], [-10, 0, -9, -4, -11, 16]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-12, -1, -10, -5, -14, 19], [-22, 2, -32, -16, -18, 38], [-28, 1, -34, -18, -26, 47]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-12, -1, -10, -5, -14, 19], [-22, 2, -32, -16, -18, 38], [-164, -4, -160, -94, -182, 266], [-158, -2, -162, -92, -171, 258]], ![[0, 0, 0, 0, 1, 0], [-12, -1, -10, -5, -14, 19], [-22, 2, -32, -16, -18, 38], [-164, -4, -160, -94, -182, 266], [-476, 18, -578, -314, -472, 798], [-528, 13, -614, -339, -536, 879]], ![[0, 0, 0, 0, 0, 1], [-10, 0, -9, -4, -11, 16], [-28, 1, -34, -18, -26, 47], [-158, -2, -162, -92, -171, 258], [-528, 13, -614, -339, -536, 879], [-570, 10, -647, -360, -586, 946]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp37 : Fact (Nat.Prime 37) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 6
  a' := []
  b' := [1]
  k := [1]
  f := [1, 2, -6, -3, 5, 1]
  g := [0, 1]
  h := [0, 0, 0, 0, 0, 1]
  a := [1]
  b := [0, 0, 1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 2
  a' := [1]
  b' := [1, 0, 2]
  k := [1]
  f := [2, 4, 0, 2, 6, 2]
  g := [2, 2, 2, 1]
  h := [2, 2, 2, 1]
  a := [1, 2]
  b := [1, 1, 0, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD37 : CertificateDedekindCriterionLists l 37 where
  n := 2
  a' := [14, 1, 29]
  b' := [26, 23, 20, 2]
  k := [15, 9, 1]
  f := [2, 5, 9, 15, 9, 1]
  g := [9, 8, 29, 22, 1]
  h := [8, 13, 1]
  a := [26, 10, 10, 15]
  b := [22, 0, 36, 0, 22]
  c := [29]
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [19] where
  n := 4
  p := ![2, 3, 19, 37]
  exp := ![2, 1, 2, 1]
  pdgood := [2, 3, 37]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp3.out
    exact hp19.out
    exact hp37.out
  a := [-70810, -30932, 257598, 55410, -38916]
  b := [-4666, 58280, 18386, -65078, -11397, 6486]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 37 T_ofList CD37

noncomputable def M19 : MaximalOrderCertificateOfUnramifiedLists 19 O Om hm where
  n := 6
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [7, 18, 9, 14, 5, 0], [9, 0, 10, 15, 8, 16]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [7, 18, 9, 14, 5, 0], [16, 2, 6, 3, 1, 0], [10, 1, 4, 1, 12, 9]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [7, 18, 9, 14, 5, 0], [16, 2, 6, 3, 1, 0], [7, 15, 11, 1, 8, 0], [13, 17, 9, 3, 0, 11]], ![[0, 0, 0, 0, 1, 0], [7, 18, 9, 14, 5, 0], [16, 2, 6, 3, 1, 0], [7, 15, 11, 1, 8, 0], [18, 18, 11, 9, 3, 0], [4, 13, 13, 3, 15, 5]], ![[0, 0, 0, 0, 0, 1], [9, 0, 10, 15, 8, 16], [10, 1, 4, 1, 12, 9], [13, 17, 9, 3, 0, 11], [4, 13, 13, 3, 15, 5], [0, 10, 18, 1, 3, 15]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![15, 10, 10, 17, 4, 0], ![11, 1, 10, 16, 4, 0], ![13, 6, 4, 18, 2, 0], ![9, 9, 9, 12, 0, 0], ![1, 3, 2, 0, 1, 18]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [19]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 19 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M19
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [19] D q hq hbad)
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

end VoightMaximalOrderD6R363

namespace VoightMaximalOrderD6R368

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨9543232, [-1, 1, 10, 1, -8, -1, 1], 4⟩
local notation "l" => [-1, 1, 10, 1, -8, -1, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![0, 0, 0, 2, 0, 0], ![1, 0, 1, 0, 1, 0], ![0, 1, 0, 1, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-1, 0, -1, 0, 2, 0], ![0, 0, 0, 0, 0, 1], ![-4, -1, -9, -1, 9, 1]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-1, 0, -1, 0, 2, 0], ![0, -1, 0, -1, 0, 2], ![-4, -1, -9, -1, 9, 1], ![-3, -5, -9, -10, 7, 10]], ![![0, 0, 0, 1, 0, 0], ![-1, 0, -1, 0, 2, 0], ![0, -1, 0, -1, 0, 2], ![-7, -2, -18, -2, 16, 2], ![-3, -5, -9, -10, 7, 10], ![-30, -13, -85, -19, 70, 17]], ![![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1], ![-4, -1, -9, -1, 9, 1], ![-3, -5, -9, -10, 7, 10], ![-17, -7, -47, -10, 40, 9], ![-26, -26, -78, -56, 61, 49]], ![![0, 0, 0, 0, 0, 1], ![-4, -1, -9, -1, 9, 1], ![-3, -5, -9, -10, 7, 10], ![-30, -13, -85, -19, 70, 17], ![-26, -26, -78, -56, 61, 49], ![-140, -75, -411, -127, 329, 110]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-2]], ![[], [], [], [], [-2], [-2, -2]], ![[], [], [], [-4], [-2, -2], [-20, -2, -2]], ![[], [], [-2], [-2, -2], [-11, -1, -1], [-18, -11, -1, -1]], ![[], [-2], [-2, -2], [-20, -2, -2], [-18, -11, -1, -1], [-98, -18, -11, -1, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [-1, 0, -1, 0, 2, 0], [0, 0, 0, 0, 0, 1], [-4, -1, -9, -1, 9, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [-1, 0, -1, 0, 2, 0], [0, -1, 0, -1, 0, 2], [-4, -1, -9, -1, 9, 1], [-3, -5, -9, -10, 7, 10]], ![[0, 0, 0, 1, 0, 0], [-1, 0, -1, 0, 2, 0], [0, -1, 0, -1, 0, 2], [-7, -2, -18, -2, 16, 2], [-3, -5, -9, -10, 7, 10], [-30, -13, -85, -19, 70, 17]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [-4, -1, -9, -1, 9, 1], [-3, -5, -9, -10, 7, 10], [-17, -7, -47, -10, 40, 9], [-26, -26, -78, -56, 61, 49]], ![[0, 0, 0, 0, 0, 1], [-4, -1, -9, -1, 9, 1], [-3, -5, -9, -10, 7, 10], [-30, -13, -85, -19, 70, 17], [-26, -26, -78, -56, 61, 49], [-140, -75, -411, -127, 329, 110]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp149113 : Fact (Nat.Prime 149113) := fact_iff.2 (by norm_num)

def CD149113 : CertificateDedekindCriterionLists l 149113 where
  n := 2
  a' := [83392, 111443, 2445, 2725]
  b' := [2733, 124658, 128891, 115185, 148568]
  k := [53273, 115272, 60777, 66279, 1]
  f := [23877, 50663, 27053, 7161, 25774, 1]
  g := [30700, 65140, 34783, 9207, 33139, 1]
  h := [115973, 1]
  a := [106007, 114244, 39874, 52060, 109827]
  b := [9964, 78634, 111676, 34883, 39286]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 2
  p := ![2, 149113]
  exp := ![3, 1]
  pdgood := [149113]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp149113.out
  a := [-1213954, -847597, 2953501, 670373, -616362]
  b := [-21050, 787357, 256648, -761835, -128850, 102727]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 149113 T_ofList CD149113

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 2
  n := 4
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 1, 1, 1, 1, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0], [0, 1, 1, 1, 1, 1], [1, 1, 1, 0, 1, 0]], ![[0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0], [1, 1, 1, 0, 1, 0], [0, 1, 1, 1, 0, 1]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [0, 1, 1, 1, 1, 1], [1, 1, 1, 0, 1, 0], [1, 1, 1, 0, 0, 1], [0, 0, 0, 0, 1, 1]], ![[0, 0, 0, 0, 0, 1], [0, 1, 1, 1, 1, 1], [1, 1, 1, 0, 1, 0], [0, 1, 1, 1, 0, 1], [0, 0, 0, 0, 1, 1], [0, 1, 1, 1, 1, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![1, 1, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 1, 1]]
  v := ![![1, 1, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0]]
  w := ![![1, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 1, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 1]]
  v_ind := ![2, 3]
  w_ind := ![0, 1, 2, 3]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![0, 0, 1, 0, 1, 0], ![1, 0, 0, 1, 0, 1], ![1, 0, 0, 1, 0, 0], ![0, 1, 1, 1, 0, 0], ![1, 0, 1, 0, 1, 0], ![0, 0, 0, 1, 1, 1]]
  a := ![![![-9, 0], ![-8, -11]], ![![-18, -11], ![-103, -19]], ![![0, 0], ![-18, 0]], ![![0, 2], ![-18, -2]], ![![-8, 0], ![-8, -10]], ![![-28, -12], ![-112, -30]]]
  c := ![![![-4, 5, -1, 1], ![4, -2, 3, 6]], ![![2, 2, 4, 7], ![0, 33, 11, 10]], ![![-1, 0, 0, 1], ![-2, 7, 1, 1]], ![![-4, 1, -1, 1], ![-3, 7, 1, 2]], ![![-4, 5, -1, 1], ![4, -2, 3, 6]], ![![0, 6, 4, 8], ![4, 32, 14, 15]]]
  d := ![![![2, 0], ![-110, -20], ![0, 2], ![-284, -154]], ![![0, 2], ![-194, -132], ![-20, -2], ![-1166, -422]], ![![0, 2], ![-20, -18], ![-2, 0], ![-188, -56]], ![![2, 2], ![-34, -18], ![0, 2], ![-240, -80]], ![![2, 0], ![-110, -20], ![0, 2], ![-284, -154]], ![![0, 2], ![-288, -152], ![-20, -2], ![-1416, -554]]]
  e := ![![![-2, 1, -2, 0], ![-6, 39, 8, 11], ![-1, -1, 1, 1], ![51, 49, 54, 69]], ![![0, -1, 1, 1], ![50, 19, 47, 61], ![-5, 10, 0, 1], ![128, 280, 184, 188]], ![![0, 0, 0, 0], ![6, 0, 6, 10], ![-2, 2, 0, 0], ![12, 50, 26, 28]], ![![-2, 0, 0, 0], ![0, 6, 6, 12], ![-4, 2, -2, 0], ![14, 62, 34, 40]], ![![-1, 1, -2, 0], ![-6, 40, 8, 11], ![-1, -1, 2, 1], ![51, 49, 54, 70]], ![![-2, 0, 0, 1], ![49, 49, 56, 71], ![-5, 9, 0, 2], ![174, 324, 232, 245]]]
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

end VoightMaximalOrderD6R368

namespace VoightMaximalOrderD6R369

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨9548777, [-49, -49, 35, 27, -11, -3, 1], 49⟩
local notation "l" => [-49, -49, 35, 27, -11, -3, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![7, 0, 0, 0, 0, 0], ![0, 7, 0, 0, 0, 0], ![0, 0, 7, 0, 0, 0], ![0, 0, 0, 7, 0, 0], ![0, 0, 1, 5, 1, 0], ![0, 0, 2, 4, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, -1, -5, 7, 0], ![0, 0, -1, -4, 5, 1], ![7, 7, -8, -16, 15, 3]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, -1, -5, 7, 0], ![0, 0, -2, -4, 0, 7], ![7, 7, -9, -17, 12, 8], ![21, 28, -16, -36, 8, 24]], ![![0, 0, 0, 1, 0, 0], ![0, 0, -1, -5, 7, 0], ![0, 0, -2, -4, 0, 7], ![49, 49, -52, -94, 77, 21], ![56, 63, -52, -100, 61, 36], ![168, 189, -136, -252, 148, 80]], ![![0, 0, 0, 0, 1, 0], ![0, 0, -1, -4, 5, 1], ![7, 7, -9, -17, 12, 8], ![56, 63, -52, -100, 61, 36], ![77, 90, -65, -127, 66, 51], ![203, 243, -149, -292, 132, 116]], ![![0, 0, 0, 0, 0, 1], ![7, 7, -8, -16, 15, 3], ![21, 28, -16, -36, 8, 24], ![168, 189, -136, -252, 148, 80], ![203, 243, -149, -292, 132, 116], ![490, 584, -340, -657, 296, 244]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-7]], ![[], [], [], [], [-7], [-21, -7]], ![[], [], [], [-49], [-56, -7], [-168, -21, -7]], ![[], [], [-7], [-56, -7], [-77, -13, -1], [-203, -40, -8, -1]], ![[], [-7], [-21, -7], [-168, -21, -7], [-203, -40, -8, -1], [-490, -94, -28, -3, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, -1, -5, 7, 0], [0, 0, -1, -4, 5, 1], [7, 7, -8, -16, 15, 3]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, -1, -5, 7, 0], [0, 0, -2, -4, 0, 7], [7, 7, -9, -17, 12, 8], [21, 28, -16, -36, 8, 24]], ![[0, 0, 0, 1, 0, 0], [0, 0, -1, -5, 7, 0], [0, 0, -2, -4, 0, 7], [49, 49, -52, -94, 77, 21], [56, 63, -52, -100, 61, 36], [168, 189, -136, -252, 148, 80]], ![[0, 0, 0, 0, 1, 0], [0, 0, -1, -4, 5, 1], [7, 7, -9, -17, 12, 8], [56, 63, -52, -100, 61, 36], [77, 90, -65, -127, 66, 51], [203, 243, -149, -292, 132, 116]], ![[0, 0, 0, 0, 0, 1], [7, 7, -8, -16, 15, 3], [21, 28, -16, -36, 8, 24], [168, 189, -136, -252, 148, 80], [203, 243, -149, -292, 132, 116], [490, 584, -340, -657, 296, 244]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp41 : Fact (Nat.Prime 41) := fact_iff.2 (by norm_num)
instance hp97 : Fact (Nat.Prime 97) := fact_iff.2 (by norm_num)

def CD41 : CertificateDedekindCriterionLists l 41 where
  n := 2
  a' := [31, 22, 35, 4]
  b' := [23, 29, 3, 18, 32]
  k := [9, 4, 38, 39, 1]
  f := [9, 5, 12, 19, 10, 1]
  g := [16, 7, 26, 39, 18, 1]
  h := [20, 1]
  a := [32, 14, 31, 21, 19]
  b := [0, 18, 36, 8, 22]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD97 : CertificateDedekindCriterionLists l 97 where
  n := 2
  a' := [7, 23, 83, 74]
  b' := [95, 94, 27, 49, 24]
  k := [95, 87, 11, 95, 1]
  f := [1, 2, 16, 6, 23, 1]
  g := [1, 3, 33, 12, 46, 1]
  h := [48, 1]
  a := [59, 70, 59, 53, 48]
  b := [39, 83, 37, 81, 49]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [7] where
  n := 3
  p := ![7, 41, 97]
  exp := ![2, 1, 1]
  pdgood := [41, 97]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp7.out
    exact hp41.out
    exact hp97.out
  a := [12921, -61930, 52738, 18384, -9192]
  b := [-16898, 24869, 26015, -14790, -3830, 1532]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 41 T_ofList CD41
    exact satisfiesDedekindCriterion_of_certificate_lists T l 97 T_ofList CD97

noncomputable def M7 : MaximalOrderCertificateLists 7 O Om hm where
  m := 4
  n := 2
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 6, 2, 0, 0], [0, 0, 6, 3, 5, 1], [0, 0, 6, 5, 1, 3]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 6, 2, 0, 0], [0, 0, 5, 3, 0, 0], [0, 0, 5, 4, 5, 1], [0, 0, 5, 6, 1, 3]], ![[0, 0, 0, 1, 0, 0], [0, 0, 6, 2, 0, 0], [0, 0, 5, 3, 0, 0], [0, 0, 4, 4, 0, 0], [0, 0, 4, 5, 5, 1], [0, 0, 4, 0, 1, 3]], ![[0, 0, 0, 0, 1, 0], [0, 0, 6, 3, 5, 1], [0, 0, 5, 4, 5, 1], [0, 0, 4, 5, 5, 1], [0, 6, 5, 6, 3, 2], [0, 5, 5, 2, 6, 4]], ![[0, 0, 0, 0, 0, 1], [0, 0, 6, 5, 1, 3], [0, 0, 5, 6, 1, 3], [0, 0, 4, 0, 1, 3], [0, 5, 5, 2, 6, 4], [0, 3, 3, 1, 2, 6]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 6, 1, 0, 0, 0], ![0, 6, 0, 1, 0, 0], ![0, 6, 0, 0, 1, 0], ![0, 6, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0]]
  v := ![![0, 6, 1, 0, 0, 0], ![0, 6, 0, 1, 0, 0], ![0, 6, 0, 0, 1, 0], ![0, 6, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 4, 0, 0]]
  v_ind := ![2, 3, 4, 5]
  w_ind := ![0, 2]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![15, 0, 30, 25, 30, 0], ![0, 5, 5, 20, 20, 20], ![0, 10, 15, 10, 20, 15], ![0, 30, 5, 0, 0, 0], ![0, 0, 10, 25, 0, 0]]
  a := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![-665, -2050, 2520, 595], ![-3250, -6745, 5705, 1995], ![-3850, -8110, 5830, 2850], ![-8680, -17430, 9850, 6395]], ![![-1715, -4130, 3675, 1260], ![-5985, -11935, 8995, 3255], ![-6540, -13455, 8505, 4585], ![-13790, -27250, 14875, 9415]], ![![-1295, -3115, 2835, 980], ![-4480, -8960, 6650, 2625], ![-5040, -10345, 6510, 3640], ![-10600, -21045, 11200, 7560]], ![![175, 35, 35, 0], ![140, -140, 210, 35], ![105, -175, 210, 70], ![-140, -630, 490, 210]], ![![-210, -840, 1120, 175], ![-1470, -3080, 2975, 595], ![-1540, -3360, 2695, 980], ![-3710, -7350, 4830, 2240]]]
  c := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![30, -60], ![415, 485], ![560, 693], ![1560, 2061]], ![![200, 200], ![900, 1168], ![1085, 1435], ![2600, 3481]], ![![155, 136], ![680, 863], ![840, 1092], ![2015, 2684]], ![![0, -42], ![0, -42], ![5, -35], ![45, 22]], ![![0, -42], ![175, 203], ![210, 257], ![630, 827]]]
  d := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![210, 175, 210, 0], ![-1925, -7525, 11375, 1050]], ![![35, 140, 140, 140], ![-6825, -17325, 18900, 2800]], ![![105, 70, 140, 105], ![-4900, -12425, 13825, 2275]], ![![35, 0, 0, 0], ![1050, 175, 0, 0]], ![![70, 175, 0, 0], ![-875, -4025, 6125, 0]]]
  e := ![![![1, 0], ![0, 1]], ![![15, -102], ![0, -495]], ![![0, -77], ![700, 560]], ![![0, -70], ![525, 315]], ![![0, 0], ![0, -210]], ![![0, -42], ![0, -210]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 2, Sum.inl 0), (Sum.inl 3, Sum.inl 0), (Sum.inl 2, Sum.inr 0), (Sum.inl 2, Sum.inr 1)]
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

end VoightMaximalOrderD6R369

namespace VoightMaximalOrderD6R370

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨9582813, [1, -7, 5, 14, -10, -1, 1], 9⟩
local notation "l" => [1, -7, 5, 14, -10, -1, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![3, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0], ![0, 0, 0, 3, 0, 0], ![1, 0, 1, 0, 1, 0], ![1, 1, 1, 1, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-1, 0, -1, 0, 3, 0], ![0, 0, 0, 0, -1, 1], ![-4, 2, -5, -5, 9, 2]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-1, 0, -1, 0, 3, 0], ![0, -1, 0, -1, -3, 3], ![-4, 2, -5, -5, 10, 1], ![-3, 0, -3, -15, -6, 13]], ![![0, 0, 0, 1, 0, 0], ![-1, 0, -1, 0, 3, 0], ![0, -1, 0, -1, -3, 3], ![-11, 6, -15, -15, 27, 3], ![1, -2, 2, -10, -16, 12], ![-37, 23, -50, -68, 78, 20]], ![![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, -1, 1], ![-4, 2, -5, -5, 10, 1], ![1, -2, 2, -10, -16, 12], ![-14, 9, -19, -21, 35, 3], ![-5, 1, -4, -55, -36, 44]], ![![0, 0, 0, 0, 0, 1], ![-4, 2, -5, -5, 9, 2], ![-3, 0, -3, -15, -6, 13], ![-37, 23, -50, -68, 78, 20], ![-5, 1, -4, -55, -36, 44], ![-126, 84, -168, -279, 231, 96]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-3]], ![[], [], [], [], [-3], [-6, -3]], ![[], [], [], [-9], [-3, -3], [-39, -6, -3]], ![[], [], [-3], [-3, -3], [-13, -1, -1], [-22, -14, -2, -1]], ![[], [-3], [-6, -3], [-39, -6, -3], [-22, -14, -2, -1], [-154, -36, -16, -3, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [-1, 0, -1, 0, 3, 0], [0, 0, 0, 0, -1, 1], [-4, 2, -5, -5, 9, 2]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [-1, 0, -1, 0, 3, 0], [0, -1, 0, -1, -3, 3], [-4, 2, -5, -5, 10, 1], [-3, 0, -3, -15, -6, 13]], ![[0, 0, 0, 1, 0, 0], [-1, 0, -1, 0, 3, 0], [0, -1, 0, -1, -3, 3], [-11, 6, -15, -15, 27, 3], [1, -2, 2, -10, -16, 12], [-37, 23, -50, -68, 78, 20]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, -1, 1], [-4, 2, -5, -5, 10, 1], [1, -2, 2, -10, -16, 12], [-14, 9, -19, -21, 35, 3], [-5, 1, -4, -55, -36, 44]], ![[0, 0, 0, 0, 0, 1], [-4, 2, -5, -5, 9, 2], [-3, 0, -3, -15, -6, 13], [-37, 23, -50, -68, 78, 20], [-5, 1, -4, -55, -36, 44], [-126, 84, -168, -279, 231, 96]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp31 : Fact (Nat.Prime 31) := fact_iff.2 (by norm_num)
instance hp107 : Fact (Nat.Prime 107) := fact_iff.2 (by norm_num)

def CD31 : CertificateDedekindCriterionLists l 31 where
  n := 2
  a' := [23, 15, 21, 20]
  b' := [26, 24, 4, 5, 27]
  k := [5, 29, 24, 9, 1]
  f := [5, 13, 2, 8, 4, 1]
  g := [6, 15, 2, 10, 4, 1]
  h := [26, 1]
  a := [25, 22, 25, 14, 4]
  b := [0, 5, 14, 17, 27]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD107 : CertificateDedekindCriterionLists l 107 where
  n := 2
  a' := [13, 57, 83]
  b' := [7, 35, 28, 6]
  k := [62, 93, 1]
  f := [65, 59, 37, 57, 27, 1]
  g := [94, 9, 45, 46, 1]
  h := [74, 60, 1]
  a := [76, 9, 89, 35]
  b := [26, 54, 97, 41, 72]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
  n := 3
  p := ![3, 31, 107]
  exp := ![2, 1, 1]
  pdgood := [31, 107]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp31.out
    exact hp107.out
  a := [-60531, -95888, 143798, 9780, -21312]
  b := [-12912, 28387, 36275, -36028, -2222, 3552]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 31 T_ofList CD31
    exact satisfiesDedekindCriterion_of_certificate_lists T l 107 T_ofList CD107

noncomputable def M3 : MaximalOrderCertificateLists 3 O Om hm where
  m := 3
  n := 3
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [2, 0, 2, 0, 0, 0], [0, 0, 0, 0, 2, 1], [2, 2, 1, 1, 0, 2]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [2, 0, 2, 0, 0, 0], [0, 2, 0, 2, 0, 0], [2, 2, 1, 1, 1, 1], [0, 0, 0, 0, 0, 1]], ![[0, 0, 0, 1, 0, 0], [2, 0, 2, 0, 0, 0], [0, 2, 0, 2, 0, 0], [1, 0, 0, 0, 0, 0], [1, 1, 2, 2, 2, 0], [2, 2, 1, 1, 0, 2]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 2, 1], [2, 2, 1, 1, 1, 1], [1, 1, 2, 2, 2, 0], [1, 0, 2, 0, 2, 0], [1, 1, 2, 2, 0, 2]], ![[0, 0, 0, 0, 0, 1], [2, 2, 1, 1, 0, 2], [0, 0, 0, 0, 0, 1], [2, 2, 1, 1, 0, 2], [1, 1, 2, 2, 0, 2], [0, 0, 0, 0, 0, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![2, 0, 1, 0, 0, 0], ![0, 2, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 0]]
  v := ![![2, 0, 1, 0, 0, 0], ![0, 2, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 1, 2], ![0, 0, 0, 1, 0, 0]]
  v_ind := ![2, 3, 5]
  w_ind := ![0, 1, 3]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![0, 2, 2, 0, 1, 0], ![1, 1, 0, 1, 2, 2], ![0, 2, 0, 1, 0, 1], ![1, 2, 2, 1, 0, 2], ![2, 2, 1, 1, 0, 1]]
  a := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![-3, -3, 1], ![4, -8, 20], ![-20, -95, 74]], ![![-15, -38, 35], ![-132, -190, 79], ![-399, -741, 303]], ![![-3, -12, 18], ![-75, -93, 27], ![-228, -357, 120]], ![![-3, -27, 33], ![-135, -168, 57], ![-402, -666, 243]], ![![0, -12, 18], ![-75, -90, 30], ![-231, -372, 135]]]
  c := ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 6, -2], ![-3, -6, 10], ![7, -10, 75]], ![![6, 3, 24], ![54, 64, 82], ![165, 159, 400]], ![![1, -3, 12], ![30, 45, 28], ![95, 109, 166]], ![![0, -3, 22], ![55, 75, 57], ![167, 182, 327]], ![![0, -2, 11], ![30, 44, 28], ![96, 107, 178]]]
  d := ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![6, 0, 0], ![-81, -87, 24], ![6, 6, 3]], ![![0, 3, 6], ![-162, -516, 339], ![-30, -30, 18]], ![![0, 3, 3], ![-18, -210, 180], ![-12, -15, 6]], ![![6, 3, 6], ![-75, -414, 324], ![-27, -24, 12]], ![![3, 3, 3], ![-33, -222, 183], ![-12, -12, 6]]]
  e := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![-4, 1, 1], ![32, 52, 19], ![-4, -1, -3]], ![![1, 2, -3], ![62, 1, 366], ![11, 19, 6]], ![![0, 0, 0], ![3, -42, 183], ![3, 12, 0]], ![![-3, 0, 0], ![24, -48, 333], ![9, 21, 0]], ![![0, 0, 0], ![9, -30, 183], ![3, 12, 0]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 0, Sum.inl 1), (Sum.inl 0, Sum.inr 0), (Sum.inl 1, Sum.inr 0), (Sum.inl 0, Sum.inr 1)]
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

end VoightMaximalOrderD6R370

end TraceEuclidean
