import TraceEuclidean.VoightMaximalOrderCertificates.Chunk060
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

namespace VoightMaximalOrderD6R563

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨12843125, [-1, -16, 19, 8, -9, -1, 1], 7⟩
local notation "l" => [-1, -16, 19, 8, -9, -1, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![7, 0, 0, 0, 0, 0], ![0, 7, 0, 0, 0, 0], ![0, 0, 7, 0, 0, 0], ![0, 0, 0, 7, 0, 0], ![0, 0, 0, 0, 7, 0], ![2, 1, 6, 3, 3, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-2, -1, -6, -3, -3, 7], ![-1, 2, -6, -2, 0, 4]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-2, -1, -6, -3, -3, 7], ![-1, 15, -25, -11, 6, 7], ![-4, 7, -22, -14, -2, 16]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-2, -1, -6, -3, -3, 7], ![-1, 15, -25, -11, 6, 7], ![-19, 7, -63, -57, -29, 70], ![-12, 30, -77, -48, -8, 50]], ![![0, 0, 0, 0, 1, 0], ![-2, -1, -6, -3, -3, 7], ![-1, 15, -25, -11, 6, 7], ![-19, 7, -63, -57, -29, 70], ![-12, 150, -239, -116, 30, 77], ![-34, 96, -222, -153, -24, 144]], ![![0, 0, 0, 0, 0, 1], ![-1, 2, -6, -2, 0, 4], ![-4, 7, -22, -14, -2, 16], ![-12, 30, -77, -48, -8, 50], ![-34, 96, -222, -153, -24, 144], ![-37, 100, -237, -161, -27, 156]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-7]], ![[], [], [], [], [-49], [-28, -7]], ![[], [], [], [-49], [-49, -49], [-112, -28, -7]], ![[], [], [-49], [-49, -49], [-490, -49, -49], [-350, -112, -28, -7]], ![[], [-7], [-28, -7], [-112, -28, -7], [-350, -112, -28, -7], [-367, -116, -31, -7, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-2, -1, -6, -3, -3, 7], [-1, 2, -6, -2, 0, 4]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-2, -1, -6, -3, -3, 7], [-1, 15, -25, -11, 6, 7], [-4, 7, -22, -14, -2, 16]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-2, -1, -6, -3, -3, 7], [-1, 15, -25, -11, 6, 7], [-19, 7, -63, -57, -29, 70], [-12, 30, -77, -48, -8, 50]], ![[0, 0, 0, 0, 1, 0], [-2, -1, -6, -3, -3, 7], [-1, 15, -25, -11, 6, 7], [-19, 7, -63, -57, -29, 70], [-12, 150, -239, -116, 30, 77], [-34, 96, -222, -153, -24, 144]], ![[0, 0, 0, 0, 0, 1], [-1, 2, -6, -2, 0, 4], [-4, 7, -22, -14, -2, 16], [-12, 30, -77, -48, -8, 50], [-34, 96, -222, -153, -24, 144], [-37, 100, -237, -161, -27, 156]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp20549 : Fact (Nat.Prime 20549) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 4
  a' := [1]
  b' := [0, 2]
  k := [4, 1, 1]
  f := [1, 4, -3, 0, 2, 1]
  g := [1, 0, 1]
  h := [4, 4, 0, 4, 1]
  a := [1]
  b := [0, 1, 3, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD20549 : CertificateDedekindCriterionLists l 20549 where
  n := 2
  a' := [19104, 15019, 1781, 8738]
  b' := [14998, 16403, 3141, 8572, 6472]
  k := [20313, 3205, 10739, 18246, 1]
  f := [899, 586, 776, 606, 1087, 1]
  g := [16050, 10448, 13845, 10807, 19397, 1]
  h := [1151, 1]
  a := [7889, 3133, 5935, 15166, 17943]
  b := [2362, 3188, 18513, 4301, 2606]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [7] where
  n := 3
  p := ![5, 7, 20549]
  exp := ![1, 2, 1]
  pdgood := [5, 20549]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp7.out
    exact hp20549.out
  a := [-1622217, 143016, 2342159, 43436, -451860]
  b := [-213268, 1106767, 92886, -625543, -19791, 75310]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 20549 T_ofList CD20549

noncomputable def M7 : MaximalOrderCertificateOfUnramifiedLists 7 O Om hm where
  n := 6
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [5, 6, 1, 4, 4, 0], [6, 2, 1, 5, 0, 4]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [5, 6, 1, 4, 4, 0], [6, 1, 3, 3, 6, 0], [3, 0, 6, 0, 5, 2]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [5, 6, 1, 4, 4, 0], [6, 1, 3, 3, 6, 0], [2, 0, 0, 6, 6, 0], [2, 2, 0, 1, 6, 1]], ![[0, 0, 0, 0, 1, 0], [5, 6, 1, 4, 4, 0], [6, 1, 3, 3, 6, 0], [2, 0, 0, 6, 6, 0], [2, 3, 6, 3, 2, 0], [1, 5, 2, 1, 4, 4]], ![[0, 0, 0, 0, 0, 1], [6, 2, 1, 5, 0, 4], [3, 0, 6, 0, 5, 2], [2, 2, 0, 1, 6, 1], [1, 5, 2, 1, 4, 4], [5, 2, 1, 0, 1, 2]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![5, 5, 4, 4, 4, 0], ![6, 4, 6, 3, 0, 0], ![5, 6, 3, 4, 1, 0], ![4, 0, 4, 3, 6, 0], ![3, 2, 4, 1, 6, 6]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [7]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 7 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M7
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

end VoightMaximalOrderD6R563

namespace VoightMaximalOrderD6R568

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨12933968, [-4, -8, 16, 6, -8, -1, 1], 4⟩
local notation "l" => [-4, -8, 16, 6, -8, -1, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![0, 0, 0, 2, 0, 0], ![0, 0, 0, 1, 1, 0], ![0, 0, 0, 0, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, -1, 2, 0], ![0, 0, 0, 0, 0, 1], ![2, 4, -8, -6, 6, 2]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, -1, 2, 0], ![0, 0, 0, 1, -2, 2], ![2, 4, -8, -6, 6, 2], ![4, 10, -12, -14, 0, 10]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, -1, 2, 0], ![0, 0, 0, 1, -2, 2], ![4, 8, -16, -13, 14, 2], ![4, 10, -12, -14, 0, 10], ![20, 44, -70, -58, 32, 20]], ![![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1], ![2, 4, -8, -6, 6, 2], ![4, 10, -12, -14, 0, 10], ![12, 27, -41, -36, 16, 15], ![30, 72, -93, -95, 18, 46]], ![![0, 0, 0, 0, 0, 1], ![2, 4, -8, -6, 6, 2], ![4, 10, -12, -14, 0, 10], ![20, 44, -70, -58, 32, 20], ![30, 72, -93, -95, 18, 46], ![92, 214, -296, -274, 86, 110]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-2]], ![[], [], [], [], [-2], [-4, -2]], ![[], [], [], [-4], [-4, -2], [-20, -4, -2]], ![[], [], [-2], [-4, -2], [-12, -3, -1], [-30, -12, -3, -1]], ![[], [-2], [-4, -2], [-20, -4, -2], [-30, -12, -3, -1], [-92, -30, -12, -3, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, -1, 2, 0], [0, 0, 0, 0, 0, 1], [2, 4, -8, -6, 6, 2]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, -1, 2, 0], [0, 0, 0, 1, -2, 2], [2, 4, -8, -6, 6, 2], [4, 10, -12, -14, 0, 10]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, -1, 2, 0], [0, 0, 0, 1, -2, 2], [4, 8, -16, -13, 14, 2], [4, 10, -12, -14, 0, 10], [20, 44, -70, -58, 32, 20]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [2, 4, -8, -6, 6, 2], [4, 10, -12, -14, 0, 10], [12, 27, -41, -36, 16, 15], [30, 72, -93, -95, 18, 46]], ![[0, 0, 0, 0, 0, 1], [2, 4, -8, -6, 6, 2], [4, 10, -12, -14, 0, 10], [20, 44, -70, -58, 32, 20], [30, 72, -93, -95, 18, 46], [92, 214, -296, -274, 86, 110]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp808373 : Fact (Nat.Prime 808373) := fact_iff.2 (by norm_num)

def CD808373 : CertificateDedekindCriterionLists l 808373 where
  n := 2
  a' := [434650, 162260, 74204, 51671]
  b' := [342803, 58704, 400773, 111604, 313015]
  k := [712337, 231426, 485556, 288162, 1]
  f := [29053, 89007, 137562, 166676, 176413, 1]
  g := [90293, 276622, 427524, 518006, 548267, 1]
  h := [260105, 1]
  a := [496498, 650582, 534269, 523325, 149246]
  b := [597435, 224693, 194526, 775563, 659127]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 2
  p := ![2, 808373]
  exp := ![2, 1]
  pdgood := [808373]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp808373.out
  a := [-684417, -185000, 1341513, 141105, -319986]
  b := [-61978, 529005, 121979, -369289, -32406, 53331]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 808373 T_ofList CD808373

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 4
  n := 2
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 1], [0, 0, 1, 1, 0, 0]], ![[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0], [0, 0, 0, 0, 0, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 1, 1, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0]]
  v := ![![0, 1, 1, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
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
  g := ![![1, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 1], ![0, 0, 1, 0, 1, 1], ![0, 0, 1, 1, 0, 0], ![0, 0, 0, 1, 0, 0]]
  a := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![2, 1, 0, 0], ![1, 0, 2, 0], ![0, 0, 1, 1], ![-8, -6, 6, 3]], ![![-20, -20, 8, 12], ![-78, -62, 36, 24], ![-101, -101, 24, 48], ![-308, -288, 86, 120]], ![![-28, -26, 14, 15], ![-90, -76, 36, 35], ![-142, -137, 40, 63], ![-401, -383, 104, 166]], ![![0, 0, 2, 2], ![-16, -12, 14, 4], ![-20, -20, 6, 12], ![-82, -72, 32, 30]], ![![0, 0, 0, 2], ![-16, -14, 16, 2], ![-12, -14, 0, 10], ![-70, -58, 32, 20]]]
  c := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![0, -1], ![0, 0], ![0, 0], ![1, 9]], ![![3, 27], ![11, 94], ![16, 139], ![48, 410]], ![![4, 36], ![13, 112], ![22, 191], ![63, 540]], ![![0, 0], ![2, 18], ![3, 27], ![12, 104]], ![![0, 0], ![2, 19], ![2, 18], ![10, 86]]]
  d := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![2, 0, 0, 0]], ![![2, 0, 0, 2], ![-16, -10, 12, 4]], ![![2, 0, 2, 2], ![-16, -10, 12, 6]], ![![2, 2, 0, 0], ![0, 0, 4, 0]], ![![0, 2, 0, 0], ![0, -2, 4, 0]]]
  e := ![![![1, 0], ![0, 1]], ![![1, 1], ![0, 0]], ![![0, -1], ![2, 17]], ![![0, -1], ![2, 17]], ![![0, -2], ![0, 0]], ![![0, -1], ![0, 1]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 2, Sum.inl 0), (Sum.inl 3, Sum.inl 0), (Sum.inl 2, Sum.inr 0), (Sum.inl 1, Sum.inr 1)]
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

end VoightMaximalOrderD6R568

namespace VoightMaximalOrderD6R570

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨13005368, [4, -14, 7, 15, -10, -1, 1], 2⟩
local notation "l" => [4, -14, 7, 15, -10, -1, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 2, 0], ![0, 1, 1, 0, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, -1, -1, 0, -1, 2], ![-2, 6, -4, -7, 4, 2]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, -1, -1, 0, -1, 2], ![-4, 13, -8, -15, 9, 2], ![-4, 6, -6, -18, -3, 12]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, -1, -1, 0, -1, 2], ![-4, 13, -8, -15, 9, 2], ![-4, -1, -4, -22, -16, 22], ![-24, 71, -39, -90, 33, 18]], ![![0, 0, 0, 0, 1, 0], ![0, -1, -1, 0, -1, 2], ![-4, 13, -8, -15, 9, 2], ![-4, -1, -4, -22, -16, 22], ![-44, 144, -73, -158, 82, 12], ![-36, 51, -34, -165, -51, 102]], ![![0, 0, 0, 0, 0, 1], ![-2, 6, -4, -7, 4, 2], ![-4, 6, -6, -18, -3, 12], ![-24, 71, -39, -90, 33, 18], ![-36, 51, -34, -165, -51, 102], ![-123, 345, -175, -469, 122, 109]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-2]], ![[], [], [], [], [-4], [-4, -2]], ![[], [], [], [-4], [-4, -4], [-24, -4, -2]], ![[], [], [-4], [-4, -4], [-44, -4, -4], [-36, -24, -4, -2]], ![[], [-2], [-4, -2], [-24, -4, -2], [-36, -24, -4, -2], [-123, -31, -14, -3, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, -1, -1, 0, -1, 2], [-2, 6, -4, -7, 4, 2]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, -1, -1, 0, -1, 2], [-4, 13, -8, -15, 9, 2], [-4, 6, -6, -18, -3, 12]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, -1, -1, 0, -1, 2], [-4, 13, -8, -15, 9, 2], [-4, -1, -4, -22, -16, 22], [-24, 71, -39, -90, 33, 18]], ![[0, 0, 0, 0, 1, 0], [0, -1, -1, 0, -1, 2], [-4, 13, -8, -15, 9, 2], [-4, -1, -4, -22, -16, 22], [-44, 144, -73, -158, 82, 12], [-36, 51, -34, -165, -51, 102]], ![[0, 0, 0, 0, 0, 1], [-2, 6, -4, -7, 4, 2], [-4, 6, -6, -18, -3, 12], [-24, 71, -39, -90, 33, 18], [-36, 51, -34, -165, -51, 102], [-123, 345, -175, -469, 122, 109]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp31 : Fact (Nat.Prime 31) := fact_iff.2 (by norm_num)
instance hp229 : Fact (Nat.Prime 229) := fact_iff.2 (by norm_num)

def CD31 : CertificateDedekindCriterionLists l 31 where
  n := 2
  a' := [3, 0, 10, 1]
  b' := [20, 19, 9, 13, 6]
  k := [1, 11, 6, 26, 1]
  f := [0, 2, 2, 2, 3, 1]
  g := [2, 23, 23, 27, 28, 1]
  h := [2, 1]
  a := [15, 0, 12, 17, 7]
  b := [16, 18, 28, 3, 24]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD229 : CertificateDedekindCriterionLists l 229 where
  n := 2
  a' := [178, 1, 126]
  b' := [217, 187, 109, 83]
  k := [14, 155, 1]
  f := [44, 95, 122, 145, 52, 1]
  g := [96, 69, 166, 77, 1]
  h := [105, 151, 1]
  a := [57, 101, 129, 127]
  b := [86, 210, 163, 69, 102]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 3
  p := ![2, 31, 229]
  exp := ![2, 1, 1]
  pdgood := [31, 229]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp31.out
    exact hp229.out
  a := [-937516, -826098, 1466691, 63423, -215190]
  b := [-269890, 431598, 340489, -367218, -16548, 35865]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 31 T_ofList CD31
    exact satisfiesDedekindCriterion_of_certificate_lists T l 229 T_ofList CD229

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 1
  n := 5
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0], [0, 0, 0, 1, 0, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0], [0, 1, 0, 1, 1, 0], [0, 0, 0, 0, 1, 0]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0], [0, 1, 0, 1, 1, 0], [0, 1, 0, 0, 0, 0], [0, 1, 1, 0, 1, 0]], ![[0, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0], [0, 1, 0, 1, 1, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 1, 0, 1, 1, 0]], ![[0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0], [0, 1, 0, 1, 1, 0], [1, 1, 1, 1, 0, 1]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 1, 0, 0, 1, 0]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![1, 1, 1, 1, 0, 1]]
  v := ![![0, 1, 0, 0, 1, 0]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![1, 1, 1, 1, 0, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  v_ind := ![4]
  w_ind := ![0, 1, 2, 4, 5]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 1, 0, 1], ![1, 0, 1, 1, 0, 1], ![0, 0, 1, 1, 1, 1], ![0, 1, 0, 0, 1, 0], ![0, 0, 0, 1, 1, 0], ![0, 0, 1, 0, 1, 0]]
  a := ![![![-61]], ![![-52]], ![![28]], ![![80]], ![![66]], ![![90]]]
  c := ![![![-84, -160, -4, 76, 63]], ![![-87, -168, -3, 79, 64]], ![![-116, -254, 21, 121, 71]], ![![-30, -87, 23, 42, 8]], ![![-42, -108, 20, 51, 18]], ![![-32, -94, 25, 45, 8]]]
  d := ![![![0], ![76], ![10], ![-8], ![396]], ![![0], ![76], ![10], ![-6], ![390]], ![![2], ![62], ![8], ![12], ![274]], ![![2], ![-12], ![-2], ![18], ![-106]], ![![2], ![2], ![0], ![16], ![-32]], ![![2], ![-14], ![-2], ![20], ![-122]]]
  e := ![![![0, 0, -1, -1, 1], ![-66, -156, 17, 69, 34], ![-4, -9, 0, 3, 2], ![-18, -32, -5, 12, 14], ![-345, -852, 149, 416, 165]], ![![0, 0, -1, 0, 1], ![-68, -158, 14, 68, 36], ![-4, -8, 0, 2, 2], ![-18, -32, -6, 12, 14], ![-363, -883, 143, 427, 179]], ![![-1, 0, -2, 0, 1], ![-100, -220, 9, 93, 60], ![-6, -10, -3, 1, 4], ![-24, -49, -4, 18, 16], ![-535, -1213, 135, 582, 306]], ![![0, 0, 0, 0, 0], ![-32, -60, -6, 24, 24], ![-2, -2, -2, 0, 2], ![-6, -16, 2, 6, 2], ![-176, -338, -8, 158, 130]], ![![0, 1, -1, -1, 0], ![-40, -80, -5, 31, 28], ![-2, -2, -3, -1, 2], ![-8, -19, 0, 6, 4], ![-222, -456, 11, 211, 150]], ![![0, 0, -1, 1, 0], ![-34, -63, -8, 24, 26], ![-2, -1, -2, -2, 2], ![-6, -17, 1, 7, 2], ![-190, -361, -14, 166, 142]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inr 0, Sum.inr 0), (Sum.inl 0, Sum.inr 1), (Sum.inr 0, Sum.inr 1), (Sum.inr 1, Sum.inr 1)]
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

end VoightMaximalOrderD6R570

namespace VoightMaximalOrderD6R573

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨13098625, [-1, -13, 15, 13, -8, -2, 1], 3⟩
local notation "l" => [-1, -13, 15, 13, -8, -2, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![3, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0], ![0, 0, 0, 3, 0, 0], ![0, 0, 0, 0, 3, 0], ![2, 0, 0, 1, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-2, 0, 0, -1, 0, 3], ![-1, 5, -5, -5, 3, 2]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-2, 0, 0, -1, 0, 3], ![-3, 13, -15, -15, 8, 6], ![-8, 9, -5, -18, 1, 13]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-2, 0, 0, -1, 0, 3], ![-3, 13, -15, -15, 8, 6], ![-22, 27, -17, -53, 3, 36], ![-15, 57, -56, -71, 21, 29]], ![![0, 0, 0, 0, 1, 0], ![-2, 0, 0, -1, 0, 3], ![-3, 13, -15, -15, 8, 6], ![-22, 27, -17, -53, 3, 36], ![-42, 158, -153, -200, 55, 81], ![-71, 130, -88, -222, 16, 121]], ![![0, 0, 0, 0, 0, 1], ![-1, 5, -5, -5, 3, 2], ![-8, 9, -5, -18, 1, 13], ![-15, 57, -56, -71, 21, 29], ![-71, 130, -88, -222, 16, 121], ![-56, 197, -177, -260, 54, 107]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-3]], ![[], [], [], [], [-9], [-6, -3]], ![[], [], [], [-9], [-18, -9], [-39, -6, -3]], ![[], [], [-9], [-18, -9], [-108, -18, -9], [-87, -39, -6, -3]], ![[], [-3], [-6, -3], [-39, -6, -3], [-87, -39, -6, -3], [-134, -31, -14, -2, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-2, 0, 0, -1, 0, 3], [-1, 5, -5, -5, 3, 2]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-2, 0, 0, -1, 0, 3], [-3, 13, -15, -15, 8, 6], [-8, 9, -5, -18, 1, 13]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-2, 0, 0, -1, 0, 3], [-3, 13, -15, -15, 8, 6], [-22, 27, -17, -53, 3, 36], [-15, 57, -56, -71, 21, 29]], ![[0, 0, 0, 0, 1, 0], [-2, 0, 0, -1, 0, 3], [-3, 13, -15, -15, 8, 6], [-22, 27, -17, -53, 3, 36], [-42, 158, -153, -200, 55, 81], [-71, 130, -88, -222, 16, 121]], ![[0, 0, 0, 0, 0, 1], [-1, 5, -5, -5, 3, 2], [-8, 9, -5, -18, 1, 13], [-15, 57, -56, -71, 21, 29], [-71, 130, -88, -222, 16, 121], [-56, 197, -177, -260, 54, 107]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp104789 : Fact (Nat.Prime 104789) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 1]
  b' := [2, 4, 3]
  k := [1]
  f := [1, 5, 2, 3, 6, 2]
  g := [2, 3, 4, 1]
  h := [2, 3, 4, 1]
  a := [4, 4, 1]
  b := [1, 4, 0, 4, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD104789 : CertificateDedekindCriterionLists l 104789 where
  n := 2
  a' := [89008, 67494, 45946, 21024]
  b' := [61104, 72923, 31645, 74713, 16753]
  k := [80503, 84943, 56732, 51868, 1]
  f := [56829, 47367, 62362, 27501, 19515, 1]
  g := [75520, 62945, 82872, 36545, 25933, 1]
  h := [78854, 1]
  a := [45162, 73702, 3895, 54838, 35054]
  b := [60055, 91808, 12781, 44540, 69735]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
  n := 3
  p := ![3, 5, 104789]
  exp := ![2, 1, 1]
  pdgood := [5, 104789]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp5.out
    exact hp104789.out
  a := [-1682735, -304168, 3296122, -71918, -844260]
  b := [-233290, 1167771, 103989, -1006748, -34917, 140710]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 104789 T_ofList CD104789

noncomputable def M3 : MaximalOrderCertificateOfUnramifiedLists 3 O Om hm where
  n := 6
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0], [2, 2, 1, 1, 0, 2]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0], [0, 1, 0, 0, 2, 0], [1, 0, 1, 0, 1, 1]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0], [0, 1, 0, 0, 2, 0], [2, 0, 1, 1, 0, 0], [0, 0, 1, 1, 0, 2]], ![[0, 0, 0, 0, 1, 0], [1, 0, 0, 2, 0, 0], [0, 1, 0, 0, 2, 0], [2, 0, 1, 1, 0, 0], [0, 2, 0, 1, 1, 0], [1, 1, 2, 0, 1, 1]], ![[0, 0, 0, 0, 0, 1], [2, 2, 1, 1, 0, 2], [1, 0, 1, 0, 1, 1], [0, 0, 1, 1, 0, 2], [1, 1, 2, 0, 1, 1], [1, 2, 0, 1, 0, 2]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![1, 0, 2, 2, 1, 0], ![2, 1, 2, 1, 2, 0], ![1, 1, 2, 1, 1, 0], ![2, 0, 1, 2, 0, 0], ![2, 1, 1, 1, 2, 1]]
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

end VoightMaximalOrderD6R573

end TraceEuclidean
