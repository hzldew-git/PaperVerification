import TraceEuclidean.VoightMaximalOrderCertificates.Chunk073
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

namespace VoightMaximalOrderD6R716

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨15154256, [-4, -2, 12, 4, -8, -2, 1], 2⟩
local notation "l" => [-4, -2, 12, 4, -8, -2, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 2, 0], ![0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 2], ![2, 1, -6, -2, 4, 2]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 2], ![4, 2, -12, -4, 8, 4], ![4, 4, -11, -10, 6, 12]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 2], ![4, 2, -12, -4, 8, 4], ![8, 8, -22, -20, 12, 24], ![24, 16, -68, -35, 38, 36]], ![![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 2], ![4, 2, -12, -4, 8, 4], ![8, 8, -22, -20, 12, 24], ![48, 32, -136, -70, 76, 72], ![72, 60, -200, -140, 109, 148]], ![![0, 0, 0, 0, 0, 1], ![2, 1, -6, -2, 4, 2], ![4, 4, -11, -10, 6, 12], ![24, 16, -68, -35, 38, 36], ![72, 60, -200, -140, 109, 148], ![148, 110, -414, -248, 226, 257]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-2]], ![[], [], [], [], [-4], [-4, -2]], ![[], [], [], [-4], [-8, -4], [-24, -4, -2]], ![[], [], [-4], [-8, -4], [-48, -8, -4], [-72, -24, -4, -2]], ![[], [-2], [-4, -2], [-24, -4, -2], [-72, -24, -4, -2], [-148, -36, -12, -2, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2], [2, 1, -6, -2, 4, 2]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2], [4, 2, -12, -4, 8, 4], [4, 4, -11, -10, 6, 12]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2], [4, 2, -12, -4, 8, 4], [8, 8, -22, -20, 12, 24], [24, 16, -68, -35, 38, 36]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2], [4, 2, -12, -4, 8, 4], [8, 8, -22, -20, 12, 24], [48, 32, -136, -70, 76, 72], [72, 60, -200, -140, 109, 148]], ![[0, 0, 0, 0, 0, 1], [2, 1, -6, -2, 4, 2], [4, 4, -11, -10, 6, 12], [24, 16, -68, -35, 38, 36], [72, 60, -200, -140, 109, 148], [148, 110, -414, -248, 226, 257]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp13 : Fact (Nat.Prime 13) := fact_iff.2 (by norm_num)
instance hp41 : Fact (Nat.Prime 41) := fact_iff.2 (by norm_num)
instance hp1777 : Fact (Nat.Prime 1777) := fact_iff.2 (by norm_num)

def CD13 : CertificateDedekindCriterionLists l 13 where
  n := 2
  a' := [1, 11, 1, 10]
  b' := [5, 0, 9, 9, 11]
  k := [4, 1, 8, 8, 1]
  f := [4, 8, 0, 4, 3, 1]
  g := [6, 12, 0, 7, 3, 1]
  h := [8, 1]
  a := [4, 8, 0, 0, 6]
  b := [4, 3, 5, 0, 7]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD41 : CertificateDedekindCriterionLists l 41 where
  n := 2
  a' := [36, 6, 25, 9]
  b' := [37, 35, 38, 35, 31]
  k := [1, 30, 11, 3, 1]
  f := [8, 4, 10, 11, 10, 1]
  g := [18, 8, 23, 24, 21, 1]
  h := [18, 1]
  a := [17, 31, 28, 16, 25]
  b := [13, 4, 28, 13, 16]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1777 : CertificateDedekindCriterionLists l 1777 where
  n := 2
  a' := [149, 372, 492, 96]
  b' := [1287, 1153, 346, 818, 1047]
  k := [1433, 1298, 88, 43, 1]
  f := [308, 322, 534, 5, 443, 1]
  g := [632, 660, 1095, 9, 909, 1]
  h := [866, 1]
  a := [162, 410, 180, 66, 747]
  b := [773, 350, 142, 1521, 1030]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 4
  p := ![2, 13, 41, 1777]
  exp := ![1, 1, 1, 1]
  pdgood := [13, 41, 1777]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp13.out
    exact hp41.out
    exact hp1777.out
  a := [-357288, -1583520, 3098086, 1744852, -841794]
  b := [-232565, 733548, 650806, -871486, -337575, 140299]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 13 T_ofList CD13
    exact satisfiesDedekindCriterion_of_certificate_lists T l 41 T_ofList CD41
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1777 T_ofList CD1777

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 4
  n := 2
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0]], ![[0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1]]
  v := ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1]]
  v_ind := ![1, 2, 3, 4]
  w_ind := ![0, 5]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 1, 0]]
  a := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], ![0, 0, 0, 0]], ![![0, 0, 1, 0], ![0, 0, 0, 1], ![0, 0, 0, 0], ![2, -12, -4, 8]], ![![0, 0, 0, 1], ![0, 0, 0, 0], ![2, -12, -4, 8], ![8, -22, -20, 12]], ![![2, -6, -2, 4], ![6, -22, -14, 14], ![24, -90, -54, 50], ![92, -336, -210, 186]], ![![0, 0, 0, 0], ![2, -12, -4, 8], ![8, -22, -20, 12], ![32, -136, -70, 76]]]
  c := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![0, 0], ![0, 0], ![0, 0], ![0, 1]], ![![0, 0], ![0, 0], ![0, 1], ![2, 2]], ![![0, 0], ![0, 1], ![2, 2], ![4, 12]], ![![1, 2], ![4, 8], ![16, 30], ![60, 110]], ![![0, 1], ![2, 2], ![4, 12], ![24, 36]]]
  d := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2, 0, 0, 0], ![2, -12, -4, 8]], ![![0, 2, 0, 0], ![8, -22, -20, 12]], ![![0, 0, 2, 0], ![32, -136, -70, 76]], ![![0, 0, 0, 2], ![340, -1228, -776, 670]], ![![0, 0, 0, 2], ![120, -400, -280, 218]]]
  e := ![![![1, 0], ![0, 1]], ![![0, 0], ![2, 2]], ![![0, 0], ![4, 12]], ![![0, 0], ![24, 36]], ![![1, 1], ![220, 406]], ![![0, 0], ![72, 148]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 0, Sum.inl 1), (Sum.inl 0, Sum.inl 2), (Sum.inl 0, Sum.inl 3), (Sum.inl 0, Sum.inr 0), (Sum.inl 0, Sum.inr 1)]
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

end VoightMaximalOrderD6R716

namespace VoightMaximalOrderD6R717

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨15155664, [-1, -5, 14, 13, -6, -3, 1], 5⟩
local notation "l" => [-1, -5, 14, 13, -6, -3, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![5, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0], ![0, 0, 5, 0, 0, 0], ![0, 0, 0, 5, 0, 0], ![0, 0, 0, 0, 5, 0], ![2, 4, 0, 4, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-2, -4, 0, -4, 0, 5], ![-1, -1, -2, -5, 2, 3]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-2, -4, 0, -4, 0, 5], ![-5, -7, -14, -25, 6, 15], ![-7, -12, -7, -25, 1, 19]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-2, -4, 0, -4, 0, 5], ![-5, -7, -14, -25, 6, 15], ![-27, -44, -37, -113, 5, 75], ![-21, -30, -50, -106, 13, 62]], ![![0, 0, 0, 0, 1, 0], ![-2, -4, 0, -4, 0, 5], ![-5, -7, -14, -25, 6, 15], ![-27, -44, -37, -113, 5, 75], ![-85, -122, -194, -432, 37, 250], ![-88, -135, -154, -412, 18, 251]], ![![0, 0, 0, 0, 0, 1], ![-1, -1, -2, -5, 2, 3], ![-7, -12, -7, -25, 1, 19], ![-21, -30, -50, -106, 13, 62], ![-88, -135, -154, -412, 18, 251], ![-75, -107, -169, -385, 30, 221]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-5]], ![[], [], [], [], [-25], [-15, -5]], ![[], [], [], [-25], [-75, -25], [-95, -15, -5]], ![[], [], [-25], [-75, -25], [-375, -75, -25], [-310, -95, -15, -5]], ![[], [-5], [-15, -5], [-95, -15, -5], [-310, -95, -15, -5], [-331, -74, -23, -3, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-2, -4, 0, -4, 0, 5], [-1, -1, -2, -5, 2, 3]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-2, -4, 0, -4, 0, 5], [-5, -7, -14, -25, 6, 15], [-7, -12, -7, -25, 1, 19]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-2, -4, 0, -4, 0, 5], [-5, -7, -14, -25, 6, 15], [-27, -44, -37, -113, 5, 75], [-21, -30, -50, -106, 13, 62]], ![[0, 0, 0, 0, 1, 0], [-2, -4, 0, -4, 0, 5], [-5, -7, -14, -25, 6, 15], [-27, -44, -37, -113, 5, 75], [-85, -122, -194, -432, 37, 250], [-88, -135, -154, -412, 18, 251]], ![[0, 0, 0, 0, 0, 1], [-1, -1, -2, -5, 2, 3], [-7, -12, -7, -25, 1, 19], [-21, -30, -50, -106, 13, 62], [-88, -135, -154, -412, 18, 251], [-75, -107, -169, -385, 30, 221]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp315743 : Fact (Nat.Prime 315743) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 3
  a' := []
  b' := [1]
  k := [1]
  f := [1, 3, -6, -6, 4, 2]
  g := [1, 1, 1]
  h := [1, 0, 1, 0, 1]
  a := [0, 1]
  b := [1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 2
  a' := [0, 0, 0, 2]
  b' := [2, 0, 0, 2, 2]
  k := [2, 0, 0, 1, 1]
  f := [1, 3, -4, -4, 3, 2]
  g := [2, 2, 0, 1, 2, 1]
  h := [1, 1]
  a := [1, 2]
  b := [0, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD315743 : CertificateDedekindCriterionLists l 315743 where
  n := 2
  a' := [133990, 300933, 222486, 292283]
  b' := [186197, 91821, 120437, 277225, 4692]
  k := [150845, 63910, 167265, 253310, 1]
  f := [26402, 23453, 11334, 8598, 28129, 1]
  g := [267059, 237221, 114637, 86966, 284525, 1]
  h := [31215, 1]
  a := [313658, 282620, 79652, 226200, 294905]
  b := [3260, 3617, 43131, 312741, 20838]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [5] where
  n := 4
  p := ![2, 3, 5, 315743]
  exp := ![1, 1, 2, 1]
  pdgood := [2, 3, 315743]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp3.out
    exact hp5.out
    exact hp315743.out
  a := [-27059645, -50145798, 24453105, 24113724, -8731452]
  b := [-4060361, 14350783, 18181740, -6795577, -4746575, 1455242]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 315743 T_ofList CD315743

noncomputable def M5 : MaximalOrderCertificateOfUnramifiedLists 5 O Om hm where
  n := 6
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [3, 1, 0, 1, 0, 0], [4, 4, 3, 0, 2, 3]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [3, 1, 0, 1, 0, 0], [0, 3, 1, 0, 1, 0], [3, 3, 3, 0, 1, 4]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [3, 1, 0, 1, 0, 0], [0, 3, 1, 0, 1, 0], [3, 1, 3, 2, 0, 0], [4, 0, 0, 4, 3, 2]], ![[0, 0, 0, 0, 1, 0], [3, 1, 0, 1, 0, 0], [0, 3, 1, 0, 1, 0], [3, 1, 3, 2, 0, 0], [0, 3, 1, 3, 2, 0], [2, 0, 1, 3, 3, 1]], ![[0, 0, 0, 0, 0, 1], [4, 4, 3, 0, 2, 3], [3, 3, 3, 0, 1, 4], [4, 0, 0, 4, 3, 2], [2, 0, 1, 3, 3, 1], [0, 3, 1, 0, 0, 1]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![2, 3, 0, 1, 0, 0], ![4, 0, 0, 4, 2, 0], ![2, 2, 0, 2, 0, 0], ![4, 1, 3, 1, 0, 0], ![0, 1, 4, 2, 2, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [5]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 5 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M5
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

end VoightMaximalOrderD6R717

namespace VoightMaximalOrderD6R722

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨15187408, [-4, -6, 10, 8, -6, -2, 1], 2⟩
local notation "l" => [-4, -6, 10, 8, -6, -2, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 2, 0], ![0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 2], ![2, 3, -5, -4, 3, 2]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 2], ![4, 6, -10, -8, 6, 4], ![4, 8, -7, -13, 2, 10]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 2], ![4, 6, -10, -8, 6, 4], ![8, 16, -14, -26, 4, 20], ![20, 34, -42, -47, 17, 24]], ![![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 2], ![4, 6, -10, -8, 6, 4], ![8, 16, -14, -26, 4, 20], ![40, 68, -84, -94, 34, 48], ![48, 92, -86, -138, 25, 82]], ![![0, 0, 0, 0, 0, 1], ![2, 3, -5, -4, 3, 2], ![4, 8, -7, -13, 2, 10], ![20, 34, -42, -47, 17, 24], ![48, 92, -86, -138, 25, 82], ![82, 147, -159, -207, 54, 107]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-2]], ![[], [], [], [], [-4], [-4, -2]], ![[], [], [], [-4], [-8, -4], [-20, -4, -2]], ![[], [], [-4], [-8, -4], [-40, -8, -4], [-48, -20, -4, -2]], ![[], [-2], [-4, -2], [-20, -4, -2], [-48, -20, -4, -2], [-82, -24, -10, -2, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2], [2, 3, -5, -4, 3, 2]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2], [4, 6, -10, -8, 6, 4], [4, 8, -7, -13, 2, 10]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2], [4, 6, -10, -8, 6, 4], [8, 16, -14, -26, 4, 20], [20, 34, -42, -47, 17, 24]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 2], [4, 6, -10, -8, 6, 4], [8, 16, -14, -26, 4, 20], [40, 68, -84, -94, 34, 48], [48, 92, -86, -138, 25, 82]], ![[0, 0, 0, 0, 0, 1], [2, 3, -5, -4, 3, 2], [4, 8, -7, -13, 2, 10], [20, 34, -42, -47, 17, 24], [48, 92, -86, -138, 25, 82], [82, 147, -159, -207, 54, 107]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp949213 : Fact (Nat.Prime 949213) := fact_iff.2 (by norm_num)

def CD949213 : CertificateDedekindCriterionLists l 949213 where
  n := 2
  a' := [918044, 677069, 726924, 287261]
  b' := [915725, 778477, 335549, 343700, 322233]
  k := [819816, 643621, 556531, 195287, 1]
  f := [161128, 293080, 167604, 47819, 227258, 1]
  g := [405730, 737992, 422035, 120410, 572249, 1]
  h := [376962, 1]
  a := [122948, 856575, 124515, 260792, 369220]
  b := [741208, 132826, 579905, 525332, 579993]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 2
  p := ![2, 949213]
  exp := ![1, 1]
  pdgood := [949213]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp949213.out
  a := [-120488, -1462080, 1193046, 838712, -444594]
  b := [-236079, 308278, 549180, -341610, -164485, 74099]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 949213 T_ofList CD949213

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 4
  n := 2
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0], [0, 1, 1, 0, 1, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0]], ![[0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 1, 0], [0, 0, 1, 1, 0, 0], [0, 0, 0, 1, 1, 0], [0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 0, 1]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1]]
  v := ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 1]]
  v_ind := ![1, 2, 3, 4]
  w_ind := ![0, 1]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![1, 1, 0, 1, 1, 1], ![0, 0, 0, 0, 1, 0]]
  a := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], ![0, 0, 0, 0]], ![![0, 0, 1, 0], ![0, 0, 0, 1], ![0, 0, 0, 0], ![6, -10, -8, 6]], ![![0, 0, 0, 1], ![0, 0, 0, 0], ![6, -10, -8, 6], ![16, -14, -26, 4]], ![![4, -4, -4, 4], ![14, -16, -20, 8], ![56, -66, -80, 28], ![176, -184, -258, 64]], ![![0, 0, 0, 0], ![6, -10, -8, 6], ![16, -14, -26, 4], ![68, -84, -94, 34]]]
  c := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![0, 0], ![0, 0], ![0, 0], ![0, 1]], ![![0, 0], ![0, 0], ![0, 1], ![2, 2]], ![![0, 0], ![0, 1], ![2, 2], ![4, 10]], ![![1, 2], ![4, 8], ![16, 24], ![48, 76]], ![![0, 1], ![2, 2], ![4, 10], ![20, 24]]]
  d := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2, 0, 0, 0], ![6, -10, -8, 6]], ![![0, 2, 0, 0], ![16, -14, -26, 4]], ![![0, 0, 2, 0], ![68, -84, -94, 34]], ![![2, 0, 2, 2], ![552, -584, -792, 198]], ![![0, 0, 0, 2], ![184, -172, -276, 50]]]
  e := ![![![1, 0], ![0, 1]], ![![0, 0], ![2, 2]], ![![0, 0], ![4, 10]], ![![0, 0], ![20, 24]], ![![1, 1], ![152, 216]], ![![0, 0], ![48, 82]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 0, Sum.inl 1), (Sum.inl 0, Sum.inl 2), (Sum.inl 0, Sum.inl 3), (Sum.inl 0, Sum.inr 0), (Sum.inl 0, Sum.inr 1)]
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

end VoightMaximalOrderD6R722

namespace VoightMaximalOrderD6R725

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨15231824, [-1, -5, 8, 7, -8, -1, 1], 4⟩
local notation "l" => [-1, -5, 8, 7, -8, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-1, 0, -1, 0, 2, 0], ![0, 0, 0, 0, 0, 1], ![-4, 2, -8, -4, 9, 1]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-1, 0, -1, 0, 2, 0], ![0, -1, 0, -1, 0, 2], ![-4, 2, -8, -4, 9, 1], ![0, -2, -2, -12, 1, 10]], ![![0, 0, 0, 1, 0, 0], ![-1, 0, -1, 0, 2, 0], ![0, -1, 0, -1, 0, 2], ![-7, 4, -16, -8, 16, 2], ![0, -2, -2, -12, 1, 10], ![-28, 20, -70, -42, 66, 11]], ![![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1], ![-4, 2, -8, -4, 9, 1], ![0, -2, -2, -12, 1, 10], ![-16, 11, -39, -23, 38, 6], ![-1, -4, -14, -63, 8, 44]], ![![0, 0, 0, 0, 0, 1], ![-4, 2, -8, -4, 9, 1], ![0, -2, -2, -12, 1, 10], ![-28, 20, -70, -42, 66, 11], ![-1, -4, -14, -63, 8, 44], ![-113, 87, -293, -190, 270, 52]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-2]], ![[], [], [], [], [-2], [-2, -2]], ![[], [], [], [-4], [-2, -2], [-20, -2, -2]], ![[], [], [-2], [-2, -2], [-11, -1, -1], [-12, -11, -1, -1]], ![[], [-2], [-2, -2], [-20, -2, -2], [-12, -11, -1, -1], [-88, -12, -11, -1, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [-1, 0, -1, 0, 2, 0], [0, 0, 0, 0, 0, 1], [-4, 2, -8, -4, 9, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [-1, 0, -1, 0, 2, 0], [0, -1, 0, -1, 0, 2], [-4, 2, -8, -4, 9, 1], [0, -2, -2, -12, 1, 10]], ![[0, 0, 0, 1, 0, 0], [-1, 0, -1, 0, 2, 0], [0, -1, 0, -1, 0, 2], [-7, 4, -16, -8, 16, 2], [0, -2, -2, -12, 1, 10], [-28, 20, -70, -42, 66, 11]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [-4, 2, -8, -4, 9, 1], [0, -2, -2, -12, 1, 10], [-16, 11, -39, -23, 38, 6], [-1, -4, -14, -63, 8, 44]], ![[0, 0, 0, 0, 0, 1], [-4, 2, -8, -4, 9, 1], [0, -2, -2, -12, 1, 10], [-28, 20, -70, -42, 66, 11], [-1, -4, -14, -63, 8, 44], [-113, 87, -293, -190, 270, 52]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp613 : Fact (Nat.Prime 613) := fact_iff.2 (by norm_num)
instance hp1553 : Fact (Nat.Prime 1553) := fact_iff.2 (by norm_num)

def CD613 : CertificateDedekindCriterionLists l 613 where
  n := 2
  a' := [90, 480, 120, 293]
  b' := [408, 297, 312, 586, 64]
  k := [501, 461, 245, 58, 1]
  f := [108, 37, 128, 169, 152, 1]
  g := [239, 81, 283, 373, 335, 1]
  h := [277, 1]
  a := [375, 106, 401, 490, 45]
  b := [323, 177, 144, 389, 568]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1553 : CertificateDedekindCriterionLists l 1553 where
  n := 2
  a' := [388, 1494, 896, 696]
  b' := [474, 1095, 1425, 999, 482]
  k := [264, 441, 272, 19, 1]
  f := [463, 510, 822, 82, 9, 1]
  g := [466, 513, 827, 82, 9, 1]
  h := [1543, 1]
  a := [568, 355, 0, 752, 571]
  b := [952, 947, 0, 801, 982]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 3
  p := ![2, 613, 1553]
  exp := ![2, 1, 1]
  pdgood := [613, 1553]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp613.out
    exact hp1553.out
  a := [-2439836, -1576224, 8458107, 585216, -1640844]
  b := [-273624, 1879484, 845993, -2160675, -143115, 273474]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 613 T_ofList CD613
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1553 T_ofList CD1553

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 4
  n := 2
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 0]], ![[0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 0, 0], [1, 0, 0, 1, 0, 0]], ![[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 0], [1, 1, 1, 0, 0, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![1, 1, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0]]
  v := ![![1, 1, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0]]
  v_ind := ![2, 3, 4, 5]
  w_ind := ![0, 2]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0], ![1, 0, 0, 1, 1, 0], ![1, 1, 1, 0, 0, 1], ![1, 0, 0, 1, 0, 0], ![1, 1, 1, 0, 0, 0]]
  a := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![2, 1, 0, 0], ![-1, 1, 2, 0], ![0, 0, 1, 1], ![-8, -4, 9, 2]], ![![-8, -4, 12, 4], ![-18, -18, 18, 12], ![-41, -35, 40, 16], ![-84, -105, 74, 56]], ![![-8, -14, 12, 12], ![-70, -42, 68, 14], ![-22, -67, 18, 46], ![-303, -206, 280, 64]], ![![0, 0, 2, 2], ![-16, -6, 16, 2], ![-2, -12, 2, 10], ![-70, -42, 66, 12]], ![![2, 2, 2, 0], ![0, 0, 2, 2], ![-8, -4, 10, 2], ![-10, -16, 10, 12]]]
  c := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![-1, 0], ![0, 1], ![0, 0], ![4, 5]], ![![4, 5], ![15, 10], ![30, 25], ![80, 50]], ![![9, 5], ![42, 45], ![42, 10], ![196, 195]], ![![0, 0], ![8, 10], ![7, 0], ![42, 45]], ![![-2, 0], ![0, 0], ![4, 5], ![11, 5]]]
  d := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![2, 0, 0, 0]], ![![0, 2, 2, 0], ![-2, 0, 4, 2]], ![![2, 0, 0, 2], ![-14, -6, 18, 2]], ![![0, 2, 0, 0], ![-2, 0, 4, 0]], ![![2, 0, 0, 0], ![2, 2, 0, 0]]]
  e := ![![![1, 0], ![0, 1]], ![![1, 1], ![-1, 0]], ![![0, 0], ![0, 2]], ![![0, 0], ![6, 10]], ![![0, 0], ![0, 2]], ![![0, 0], ![-2, 0]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 2, Sum.inl 0), (Sum.inl 3, Sum.inl 0), (Sum.inl 2, Sum.inr 0), (Sum.inl 3, Sum.inr 0)]
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

end VoightMaximalOrderD6R725

end TraceEuclidean
