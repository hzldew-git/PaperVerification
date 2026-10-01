import TraceEuclidean.VoightMaximalOrderCertificates.Chunk029
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

namespace VoightMaximalOrderD6R179

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5888125, [1, -8, 4, 16, -6, -3, 1], 19⟩
local notation "l" => [1, -8, 4, 16, -6, -3, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![19, 0, 0, 0, 0, 0], ![0, 19, 0, 0, 0, 0], ![0, 0, 19, 0, 0, 0], ![0, 0, 0, 19, 0, 0], ![0, 0, 0, 0, 19, 0], ![7, 9, 3, 15, 5, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-7, -9, -3, -15, -5, 19], ![-3, -3, -1, -7, -1, 8]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-7, -9, -3, -15, -5, 19], ![-22, -19, -13, -61, -9, 57], ![-17, -18, -8, -42, -10, 45]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-7, -9, -3, -15, -5, 19], ![-22, -19, -13, -61, -9, 57], ![-108, -112, -49, -277, -73, 285], ![-65, -62, -33, -173, -37, 170]], ![![0, 0, 0, 0, 1, 0], ![-7, -9, -3, -15, -5, 19], ![-22, -19, -13, -61, -9, 57], ![-108, -112, -49, -277, -73, 285], ![-344, -306, -178, -949, -197, 893], ![-251, -242, -121, -668, -158, 657]], ![![0, 0, 0, 0, 0, 1], ![-3, -3, -1, -7, -1, 8], ![-17, -18, -8, -42, -10, 45], ![-65, -62, -33, -173, -37, 170], ![-251, -242, -121, -668, -158, 657], ![-167, -159, -82, -446, -101, 437]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-19]], ![[], [], [], [], [-361], [-152, -19]], ![[], [], [], [-361], [-1083, -361], [-855, -152, -19]], ![[], [], [-361], [-1083, -361], [-5415, -1083, -361], [-3230, -855, -152, -19]], ![[], [-19], [-152, -19], [-855, -152, -19], [-3230, -855, -152, -19], [-2215, -518, -100, -13, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-7, -9, -3, -15, -5, 19], [-3, -3, -1, -7, -1, 8]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-7, -9, -3, -15, -5, 19], [-22, -19, -13, -61, -9, 57], [-17, -18, -8, -42, -10, 45]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-7, -9, -3, -15, -5, 19], [-22, -19, -13, -61, -9, 57], [-108, -112, -49, -277, -73, 285], [-65, -62, -33, -173, -37, 170]], ![[0, 0, 0, 0, 1, 0], [-7, -9, -3, -15, -5, 19], [-22, -19, -13, -61, -9, 57], [-108, -112, -49, -277, -73, 285], [-344, -306, -178, -949, -197, 893], [-251, -242, -121, -668, -158, 657]], ![[0, 0, 0, 0, 0, 1], [-3, -3, -1, -7, -1, 8], [-17, -18, -8, -42, -10, 45], [-65, -62, -33, -173, -37, 170], [-251, -242, -121, -668, -158, 657], [-167, -159, -82, -446, -101, 437]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp9421 : Fact (Nat.Prime 9421) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 4
  a' := [4]
  b' := [0, 3]
  k := [1, 3, 1]
  f := [3, 4, 0, -1, 2, 1]
  g := [4, 0, 1]
  h := [4, 3, 0, 2, 1]
  a := [0, 4]
  b := [4, 2, 0, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD9421 : CertificateDedekindCriterionLists l 9421 where
  n := 2
  a' := [544, 3732, 3775, 1570]
  b' := [3999, 2262, 3641, 7074, 9107]
  k := [513, 5023, 2547, 2874, 1]
  f := [555, 1926, 425, 1430, 2135, 1]
  g := [1598, 5545, 1222, 4117, 6146, 1]
  h := [3272, 1]
  a := [505, 1602, 6928, 576, 3168]
  b := [2454, 8466, 6045, 6764, 6253]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [19] where
  n := 3
  p := ![5, 19, 9421]
  exp := ![1, 2, 1]
  pdgood := [5, 9421]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp19.out
    exact hp9421.out
  a := [-14589095, -33526320, 23885484, 11551896, -5264304]
  b := [-3949250, 6449055, 11971013, -5869754, -2364008, 877384]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 9421 T_ofList CD9421

noncomputable def M19 : MaximalOrderCertificateOfUnramifiedLists 19 O Om hm where
  n := 6
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [12, 10, 16, 4, 14, 0], [16, 16, 18, 12, 18, 8]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [12, 10, 16, 4, 14, 0], [16, 0, 6, 15, 10, 0], [2, 1, 11, 15, 9, 7]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [12, 10, 16, 4, 14, 0], [16, 0, 6, 15, 10, 0], [6, 2, 8, 8, 3, 0], [11, 14, 5, 17, 1, 18]], ![[0, 0, 0, 0, 1, 0], [12, 10, 16, 4, 14, 0], [16, 0, 6, 15, 10, 0], [6, 2, 8, 8, 3, 0], [17, 17, 12, 1, 12, 0], [15, 5, 12, 16, 13, 11]], ![[0, 0, 0, 0, 0, 1], [16, 16, 18, 12, 18, 8], [2, 1, 11, 15, 9, 7], [11, 14, 5, 17, 1, 18], [15, 5, 12, 16, 13, 11], [4, 12, 13, 10, 13, 0]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![6, 17, 18, 15, 14, 0], ![9, 1, 0, 5, 3, 0], ![5, 12, 12, 14, 12, 0], ![12, 6, 6, 16, 7, 0], ![8, 13, 10, 16, 16, 1]]
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

end VoightMaximalOrderD6R179

namespace VoightMaximalOrderD6R181

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5911461, [-9, -18, 9, 17, -6, -3, 1], 9⟩
local notation "l" => [-9, -18, 9, 17, -6, -3, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![3, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0], ![0, 0, 0, 3, 0, 0], ![0, 0, 1, 1, 1, 0], ![0, 0, 2, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, -1, -1, 3, 0], ![0, 0, -1, 0, 1, 1], ![3, 6, -7, -7, 6, 3]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, -1, -1, 3, 0], ![0, 0, -2, 0, 0, 3], ![3, 6, -8, -8, 7, 4], ![9, 21, -14, -21, 3, 15]], ![![0, 0, 0, 1, 0, 0], ![0, 0, -1, -1, 3, 0], ![0, 0, -2, 0, 0, 3], ![9, 18, -21, -23, 18, 9], ![12, 27, -21, -28, 7, 19], ![45, 99, -66, -98, 30, 48]], ![![0, 0, 0, 0, 1, 0], ![0, 0, -1, 0, 1, 1], ![3, 6, -8, -8, 7, 4], ![12, 27, -21, -28, 7, 19], ![24, 53, -38, -54, 17, 29], ![66, 151, -83, -141, 19, 79]], ![![0, 0, 0, 0, 0, 1], ![3, 6, -7, -7, 6, 3], ![9, 21, -14, -21, 3, 15], ![45, 99, -66, -98, 30, 48], ![66, 151, -83, -141, 19, 79], ![180, 410, -211, -375, 54, 192]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-3]], ![[], [], [], [], [-3], [-9, -3]], ![[], [], [], [-9], [-12, -3], [-45, -9, -3]], ![[], [], [-3], [-12, -3], [-24, -5, -1], [-66, -19, -4, -1]], ![[], [-3], [-9, -3], [-45, -9, -3], [-66, -19, -4, -1], [-180, -50, -15, -3, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, -1, -1, 3, 0], [0, 0, -1, 0, 1, 1], [3, 6, -7, -7, 6, 3]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, -1, -1, 3, 0], [0, 0, -2, 0, 0, 3], [3, 6, -8, -8, 7, 4], [9, 21, -14, -21, 3, 15]], ![[0, 0, 0, 1, 0, 0], [0, 0, -1, -1, 3, 0], [0, 0, -2, 0, 0, 3], [9, 18, -21, -23, 18, 9], [12, 27, -21, -28, 7, 19], [45, 99, -66, -98, 30, 48]], ![[0, 0, 0, 0, 1, 0], [0, 0, -1, 0, 1, 1], [3, 6, -8, -8, 7, 4], [12, 27, -21, -28, 7, 19], [24, 53, -38, -54, 17, 29], [66, 151, -83, -141, 19, 79]], ![[0, 0, 0, 0, 0, 1], [3, 6, -7, -7, 6, 3], [9, 21, -14, -21, 3, 15], [45, 99, -66, -98, 30, 48], [66, 151, -83, -141, 19, 79], [180, 410, -211, -375, 54, 192]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp17 : Fact (Nat.Prime 17) := fact_iff.2 (by norm_num)
instance hp53 : Fact (Nat.Prime 53) := fact_iff.2 (by norm_num)

def CD17 : CertificateDedekindCriterionLists l 17 where
  n := 2
  a' := [0, 14, 9, 11]
  b' := [13, 2, 6, 1, 8]
  k := [15, 5, 13, 15, 1]
  f := [1, 3, 3, 6, 4, 1]
  g := [1, 4, 7, 14, 6, 1]
  h := [8, 1]
  a := [16, 14, 0, 14, 14]
  b := [2, 15, 6, 14, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD53 : CertificateDedekindCriterionLists l 53 where
  n := 2
  a' := [19, 5, 30, 33]
  b' := [49, 7, 50, 45, 4]
  k := [17, 49, 5, 51, 1]
  f := [9, 10, 10, 3, 12, 1]
  g := [18, 19, 20, 6, 24, 1]
  h := [26, 1]
  a := [44, 25, 38, 25, 8]
  b := [34, 42, 49, 18, 45]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
  n := 3
  p := ![3, 17, 53]
  exp := ![3, 1, 1]
  pdgood := [17, 53]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp17.out
    exact hp53.out
  a := [2583, -16338, 12714, 7248, -3624]
  b := [-2643, 2943, 6727, -3478, -1510, 604]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 17 T_ofList CD17
    exact satisfiesDedekindCriterion_of_certificate_lists T l 53 T_ofList CD53

noncomputable def M3 : MaximalOrderCertificateLists 3 O Om hm where
  m := 4
  n := 2
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 2, 2, 0, 0], [0, 0, 2, 0, 1, 1], [0, 0, 2, 2, 0, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 2, 2, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 1, 1, 1, 1], [0, 0, 1, 0, 0, 0]], ![[0, 0, 0, 1, 0, 0], [0, 0, 2, 2, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 2, 1, 1], [0, 0, 0, 1, 0, 0]], ![[0, 0, 0, 0, 1, 0], [0, 0, 2, 0, 1, 1], [0, 0, 1, 1, 1, 1], [0, 0, 0, 2, 1, 1], [0, 2, 1, 0, 2, 2], [0, 1, 1, 0, 1, 1]], ![[0, 0, 0, 0, 0, 1], [0, 0, 2, 2, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 1, 1, 0, 1, 1], [0, 2, 2, 0, 0, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 2, 1, 0, 0, 0], ![0, 2, 0, 1, 0, 0], ![0, 2, 0, 0, 1, 0], ![0, 2, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0]]
  v := ![![0, 2, 1, 0, 0, 0], ![0, 2, 0, 1, 0, 0], ![0, 2, 0, 0, 1, 0], ![0, 2, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0]]
  v_ind := ![2, 3, 4, 5]
  w_ind := ![0, 3]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![1, 0, 2, 0, 2, 0], ![0, 0, 1, 1, 2, 2], ![0, 1, 1, 1, 2, 1], ![0, 2, 1, 0, 0, 0], ![0, 0, 2, 1, 0, 0]]
  a := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![-21, -14, 24, 12], ![-50, -51, 18, 48], ![-96, -120, 53, 70], ![-198, -320, 48, 193]], ![![-81, -87, 57, 57], ![-231, -303, 126, 162], ![-305, -454, 120, 255], ![-702, -1179, 213, 621]], ![![-51, -51, 42, 36], ![-150, -192, 87, 108], ![-207, -299, 90, 171], ![-482, -797, 153, 426]], ![![3, 3, 3, 0], ![0, 0, 6, 3], ![-6, -6, 9, 6], ![-24, -33, 15, 21]], ![![-6, 0, 12, 3], ![-27, -21, 24, 15], ![-39, -42, 27, 27], ![-96, -138, 42, 78]]]
  c := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![2, 4], ![8, 42], ![18, 102], ![50, 300]], ![![12, 62], ![45, 262], ![69, 411], ![186, 1120]], ![![7, 31], ![28, 159], ![45, 264], ![125, 750]], ![![0, -6], ![0, -6], ![1, 0], ![5, 25]], ![![0, -6], ![3, 12], ![6, 31], ![21, 123]]]
  d := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![6, 0, 6, 0], ![-6, 6, 6, 6]], ![![3, 3, 6, 6], ![-51, -42, 51, 24]], ![![3, 3, 6, 3], ![-27, -21, 33, 15]], ![![3, 0, 0, 0], ![6, 3, 0, 0]], ![![6, 3, 0, 0], ![-3, 3, 9, 0]]]
  e := ![![![1, 0], ![0, 1]], ![![1, -8], ![0, -7]], ![![0, -12], ![6, 24]], ![![0, -9], ![3, 6]], ![![0, 0], ![0, -6]], ![![0, -6], ![0, -6]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 2, Sum.inl 0), (Sum.inl 3, Sum.inl 0), (Sum.inl 2, Sum.inr 0), (Sum.inl 2, Sum.inr 1)]
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

end VoightMaximalOrderD6R181

namespace VoightMaximalOrderD6R184

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5953625, [1, 12, 20, 1, -9, -1, 1], 5⟩
local notation "l" => [1, 12, 20, 1, -9, -1, 1]
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

def basisDenominator : ℤ := 5
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![5, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0], ![0, 0, 5, 0, 0, 0], ![0, 0, 0, 5, 0, 0], ![0, 0, 0, 0, 5, 0], ![4, 2, 2, 1, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-4, -2, -2, -1, 0, 5], ![-1, -2, -4, 0, 2, 1]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-4, -2, -2, -1, 0, 5], ![-5, -14, -22, -2, 9, 5], ![-9, -7, -10, -6, 2, 11]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-4, -2, -2, -1, 0, 5], ![-5, -14, -22, -2, 9, 5], ![-41, -33, -52, -31, 8, 50], ![-19, -35, -55, -12, 16, 21]], ![![0, 0, 0, 0, 1, 0], ![-4, -2, -2, -1, 0, 5], ![-5, -14, -22, -2, 9, 5], ![-41, -33, -52, -31, 8, 50], ![-82, -157, -249, -60, 69, 90], ![-85, -93, -151, -71, 30, 101]], ![![0, 0, 0, 0, 0, 1], ![-1, -2, -4, 0, 2, 1], ![-9, -7, -10, -6, 2, 11], ![-19, -35, -55, -12, 16, 21], ![-85, -93, -151, -71, 30, 101], ![-52, -80, -128, -41, 31, 60]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-5]], ![[], [], [], [], [-25], [-5, -5]], ![[], [], [], [-25], [-25, -25], [-55, -5, -5]], ![[], [], [-25], [-25, -25], [-250, -25, -25], [-105, -55, -5, -5]], ![[], [-5], [-5, -5], [-55, -5, -5], [-105, -55, -5, -5], [-116, -24, -12, -1, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-4, -2, -2, -1, 0, 5], [-1, -2, -4, 0, 2, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-4, -2, -2, -1, 0, 5], [-5, -14, -22, -2, 9, 5], [-9, -7, -10, -6, 2, 11]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-4, -2, -2, -1, 0, 5], [-5, -14, -22, -2, 9, 5], [-41, -33, -52, -31, 8, 50], [-19, -35, -55, -12, 16, 21]], ![[0, 0, 0, 0, 1, 0], [-4, -2, -2, -1, 0, 5], [-5, -14, -22, -2, 9, 5], [-41, -33, -52, -31, 8, 50], [-82, -157, -249, -60, 69, 90], [-85, -93, -151, -71, 30, 101]], ![[0, 0, 0, 0, 0, 1], [-1, -2, -4, 0, 2, 1], [-9, -7, -10, -6, 2, 11], [-19, -35, -55, -12, 16, 21], [-85, -93, -151, -71, 30, 101], [-52, -80, -128, -41, 31, 60]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp47629 : Fact (Nat.Prime 47629) := fact_iff.2 (by norm_num)

def CD47629 : CertificateDedekindCriterionLists l 47629 where
  n := 2
  a' := [32952, 41948, 809, 3337]
  b' := [45031, 6135, 45597, 22844, 27910]
  k := [9563, 8138, 17178, 8163, 1]
  f := [17933, 32265, 41198, 33018, 3732, 1]
  g := [19614, 35289, 45059, 36112, 4081, 1]
  h := [43547, 1]
  a := [33982, 14727, 34461, 12978, 34207]
  b := [47552, 9072, 42746, 18015, 13422]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [5] where
  n := 2
  p := ![5, 47629]
  exp := ![3, 1]
  pdgood := [47629]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp47629.out
  a := [-11646631, -10799016, 14672880, 4773048, -3098592]
  b := [1466688, 7657589, 3095359, -3933918, -881580, 516432]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 47629 T_ofList CD47629

noncomputable def M5 : MaximalOrderCertificateLists 5 O Om hm where
  m := 3
  n := 3
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 3, 3, 4, 0, 0], [4, 3, 1, 0, 2, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 3, 3, 4, 0, 0], [0, 1, 3, 3, 4, 0], [1, 3, 0, 4, 2, 1]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 3, 3, 4, 0, 0], [0, 1, 3, 3, 4, 0], [4, 2, 3, 4, 3, 0], [1, 0, 0, 3, 1, 1]], ![[0, 0, 0, 0, 1, 0], [1, 3, 3, 4, 0, 0], [0, 1, 3, 3, 4, 0], [4, 2, 3, 4, 3, 0], [3, 3, 1, 0, 4, 0], [0, 2, 4, 4, 0, 1]], ![[0, 0, 0, 0, 0, 1], [4, 3, 1, 0, 2, 1], [1, 3, 0, 4, 2, 1], [1, 0, 0, 3, 1, 1], [0, 2, 4, 4, 0, 1], [3, 0, 2, 4, 1, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![1, 1, 2, 1, 0, 0], ![3, 4, 2, 0, 1, 0], ![0, 2, 3, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![1, 4, 4, 0, 0, 0], ![1, 4, 1, 0, 0, 0]]
  v := ![![1, 1, 2, 1, 0, 0], ![3, 4, 2, 0, 1, 0], ![0, 2, 3, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![1, 4, 4, 0, 0, 0], ![1, 4, 1, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 3, 0], ![0, 0, 1, 3, 2, 0]]
  v_ind := ![3, 4, 5]
  w_ind := ![0, 1, 2]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![24, 36, 24, 36, 36, 48], ![0, 36, 24, 48, 48, 0], ![24, 36, 0, 48, 12, 0], ![0, 48, 24, 12, 36, 36], ![48, 0, 36, 0, 36, 48]]
  a := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![-2460, 2472, 5160], ![-7428, 5976, 13020], ![-6204, 4860, 10716]], ![![-1800, 1860, 3960], ![-4620, 5160, 8940], ![-4500, 3792, 8076]], ![![-480, 840, 1500], ![-2220, 1680, 4500], ![-1560, 1620, 3300]], ![![-2100, 1980, 4260], ![-5700, 5160, 10080], ![-5100, 3960, 8700]], ![![-2400, 2100, 4680], ![-6360, 5700, 10740], ![-5820, 4200, 9540]]]
  c := ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![-705, -1195, 40], ![-1470, -2946, 120], ![-1185, -2415, 96]], ![![-555, -905, 32], ![-1470, -2274, 12], ![-975, -1849, 64]], ![![-288, -380, 8], ![-435, -949, 76], ![-465, -787, 28]], ![![-555, -969, 36], ![-1338, -2402, 56], ![-960, -1960, 76]], ![![-555, -1045, 40], ![-1425, -2575, 40], ![-963, -2097, 84]]]
  d := ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![180, 180, 240], ![-7260, 11700, 22560], ![-1860, 5040, 9240]], ![![240, 240, 0], ![-2400, 10320, 14400], ![-780, 3480, 7200]], ![![240, 60, 0], ![-720, 3180, 7200], ![-180, 1560, 2700]], ![![60, 180, 180], ![-5220, 10260, 17220], ![-1440, 3960, 7680]], ![![0, 180, 240], ![-7200, 11220, 18960], ![-1800, 4380, 8340]]]
  e := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![-60, -68, 8], ![-4056, -5400, 120], ![-1950, -2274, 72]], ![![-141, -39, -12], ![-3969, -4131, -108], ![-1476, -1704, 48]], ![![-45, -35, 20], ![-1365, -1675, 100], ![-690, -610, -20]], ![![-75, -45, 0], ![-3615, -4425, 0], ![-1545, -1875, 60]], ![![0, -40, -20], ![-3720, -4720, -20], ![-1650, -2110, 160]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 2, Sum.inl 1), (Sum.inl 0, Sum.inr 0), (Sum.inl 1, Sum.inr 0), (Sum.inl 2, Sum.inr 0)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [5]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 5 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M5
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [5] D q hq hbad)
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

end VoightMaximalOrderD6R184

namespace VoightMaximalOrderD6R187

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6025625, [-5, -10, 16, 9, -9, -1, 1], 13⟩
local notation "l" => [-5, -10, 16, 9, -9, -1, 1]
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

def basisDenominator : ℤ := 13
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![13, 0, 0, 0, 0, 0], ![0, 13, 0, 0, 0, 0], ![0, 0, 13, 0, 0, 0], ![0, 0, 0, 13, 0, 0], ![0, 0, 0, 0, 13, 0], ![7, 3, 0, 3, 9, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-7, -3, 0, -3, -9, 13], ![-5, -1, -1, -3, -6, 10]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-7, -3, 0, -3, -9, 13], ![-2, 7, -16, -12, 0, 13], ![-8, 3, -11, -13, -9, 22]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-7, -3, 0, -3, -9, 13], ![-2, 7, -16, -12, 0, 13], ![-65, -15, -6, -55, -90, 130], ![-47, -3, -19, -50, -64, 103]], ![![0, 0, 0, 0, 1, 0], ![-7, -3, 0, -3, -9, 13], ![-2, 7, -16, -12, 0, 13], ![-65, -15, -6, -55, -90, 130], ![-20, 75, -145, -126, -25, 130], ![-67, 42, -106, -136, -92, 198]], ![![0, 0, 0, 0, 0, 1], ![-5, -1, -1, -3, -6, 10], ![-8, 3, -11, -13, -9, 22], ![-47, -3, -19, -50, -64, 103], ![-67, 42, -106, -136, -92, 198], ![-85, 29, -90, -139, -118, 224]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-13]], ![[], [], [], [], [-169], [-130, -13]], ![[], [], [], [-169], [-169, -169], [-286, -130, -13]], ![[], [], [-169], [-169, -169], [-1690, -169, -169], [-1339, -286, -130, -13]], ![[], [-13], [-130, -13], [-286, -130, -13], [-1339, -286, -130, -13], [-1194, -331, -115, -19, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-7, -3, 0, -3, -9, 13], [-5, -1, -1, -3, -6, 10]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-7, -3, 0, -3, -9, 13], [-2, 7, -16, -12, 0, 13], [-8, 3, -11, -13, -9, 22]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-7, -3, 0, -3, -9, 13], [-2, 7, -16, -12, 0, 13], [-65, -15, -6, -55, -90, 130], [-47, -3, -19, -50, -64, 103]], ![[0, 0, 0, 0, 1, 0], [-7, -3, 0, -3, -9, 13], [-2, 7, -16, -12, 0, 13], [-65, -15, -6, -55, -90, 130], [-20, 75, -145, -126, -25, 130], [-67, 42, -106, -136, -92, 198]], ![[0, 0, 0, 0, 0, 1], [-5, -1, -1, -3, -6, 10], [-8, 3, -11, -13, -9, 22], [-47, -3, -19, -50, -64, 103], [-67, 42, -106, -136, -92, 198], [-85, 29, -90, -139, -118, 224]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp13 : Fact (Nat.Prime 13) := fact_iff.2 (by norm_num)
instance hp31 : Fact (Nat.Prime 31) := fact_iff.2 (by norm_num)
instance hp311 : Fact (Nat.Prime 311) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 4
  a' := [1]
  b' := [1, 2]
  k := [0, 0, 1]
  f := [1, 2, -3, -1, 3, 1]
  g := [0, 1, 1]
  h := [0, 1, 3, 3, 1]
  a := [1, 2]
  b := [1, 3, 4, 0, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD31 : CertificateDedekindCriterionLists l 31 where
  n := 2
  a' := [6, 26, 13, 8]
  b' := [17, 9, 11, 22, 17]
  k := [17, 12, 1, 10, 1]
  f := [5, 5, 7, 3, 7, 1]
  g := [15, 13, 22, 8, 20, 1]
  h := [10, 1]
  a := [28, 28, 13, 28]
  b := [30, 7, 10, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD311 : CertificateDedekindCriterionLists l 311 where
  n := 2
  a' := [103, 178, 110, 60]
  b' := [155, 164, 178, 33, 299]
  k := [58, 145, 31, 7, 1]
  f := [78, 99, 21, 3, 3, 1]
  g := [79, 100, 21, 3, 3, 1]
  h := [307, 1]
  a := [231, 291, 310, 309, 310]
  b := [79, 20, 1, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [13] where
  n := 4
  p := ![5, 13, 31, 311]
  exp := ![1, 2, 1, 1]
  pdgood := [5, 31, 311]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp13.out
    exact hp31.out
    exact hp311.out
  a := [-1337209, -689460, 3456666, -5404, -717072]
  b := [-146060, 1214547, 313781, -951396, -19018, 119512]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 31 T_ofList CD31
    exact satisfiesDedekindCriterion_of_certificate_lists T l 311 T_ofList CD311

noncomputable def M13 : MaximalOrderCertificateOfUnramifiedLists 13 O Om hm where
  n := 6
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [6, 10, 0, 10, 4, 0], [8, 12, 12, 10, 7, 10]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [6, 10, 0, 10, 4, 0], [11, 7, 10, 1, 0, 0], [5, 3, 2, 0, 4, 9]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [6, 10, 0, 10, 4, 0], [11, 7, 10, 1, 0, 0], [0, 11, 7, 10, 1, 0], [5, 10, 7, 2, 1, 12]], ![[0, 0, 0, 0, 1, 0], [6, 10, 0, 10, 4, 0], [11, 7, 10, 1, 0, 0], [0, 11, 7, 10, 1, 0], [6, 10, 11, 4, 1, 0], [11, 3, 11, 7, 12, 3]], ![[0, 0, 0, 0, 0, 1], [8, 12, 12, 10, 7, 10], [5, 3, 2, 0, 4, 9], [5, 10, 7, 2, 1, 12], [11, 3, 11, 7, 12, 3], [6, 3, 1, 4, 12, 3]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![7, 8, 10, 9, 8, 0], ![5, 5, 10, 12, 2, 0], ![11, 2, 3, 2, 7, 0], ![6, 8, 5, 3, 6, 0], ![3, 4, 2, 12, 2, 12]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [13]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 13 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M13
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [13] D q hq hbad)
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

end VoightMaximalOrderD6R187

end TraceEuclidean
