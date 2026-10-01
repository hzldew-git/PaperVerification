import TraceEuclidean.VoightMaximalOrderCertificates.Chunk053
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

namespace VoightMaximalOrderD6R484

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨11587216, [-17, 18, 29, -10, -13, 0, 1], 16⟩
local notation "l" => [-17, 18, 29, -10, -13, 0, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![4, 0, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0], ![0, 0, 4, 0, 0, 0], ![2, 2, 2, 2, 0, 0], ![2, 0, 0, 0, 2, 0], ![1, 3, 2, 0, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![-1, -1, -1, 2, 0, 0], ![-1, 0, 0, 1, 1, 0], ![0, -1, -1, 0, -1, 2], ![-2, -8, -10, 6, 6, 1]], ![![0, 0, 1, 0, 0, 0], ![-1, -1, -1, 2, 0, 0], ![-1, 0, 0, 0, 2, 0], ![-1, -2, -1, 1, 0, 2], ![-3, -14, -19, 10, 13, 0], ![2, -6, -14, -8, 6, 13]], ![![0, 0, 0, 1, 0, 0], ![-1, 0, 0, 1, 1, 0], ![-1, -2, -1, 1, 0, 2], ![-3, -9, -11, 7, 7, 2], ![3, -6, -14, -9, 5, 14], ![-2, -54, -76, 20, 38, 20]], ![![0, 0, 0, 0, 1, 0], ![0, -1, -1, 0, -1, 2], ![-3, -14, -19, 10, 13, 0], ![3, -6, -14, -9, 5, 14], ![-8, -94, -123, 56, 66, 10], ![18, -70, -140, -32, 64, 77]], ![![0, 0, 0, 0, 0, 1], ![-2, -8, -10, 6, 6, 1], ![2, -6, -14, -8, 6, 13], ![-2, -54, -76, 20, 38, 20], ![18, -70, -140, -32, 64, 77], ![18, -303, -464, 58, 221, 148]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-4]], ![[], [], [], [], [-8], [-4, -4]], ![[], [], [], [-4], [-4, -4], [-30, -4, -2]], ![[], [], [-8], [-4, -4], [-52, 0, -4], [-50, -26, -2, -2]], ![[], [-4], [-4, -4], [-30, -4, -2], [-50, -26, -2, -2], [-183, -40, -14, -2, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [-1, -1, -1, 2, 0, 0], [-1, 0, 0, 1, 1, 0], [0, -1, -1, 0, -1, 2], [-2, -8, -10, 6, 6, 1]], ![[0, 0, 1, 0, 0, 0], [-1, -1, -1, 2, 0, 0], [-1, 0, 0, 0, 2, 0], [-1, -2, -1, 1, 0, 2], [-3, -14, -19, 10, 13, 0], [2, -6, -14, -8, 6, 13]], ![[0, 0, 0, 1, 0, 0], [-1, 0, 0, 1, 1, 0], [-1, -2, -1, 1, 0, 2], [-3, -9, -11, 7, 7, 2], [3, -6, -14, -9, 5, 14], [-2, -54, -76, 20, 38, 20]], ![[0, 0, 0, 0, 1, 0], [0, -1, -1, 0, -1, 2], [-3, -14, -19, 10, 13, 0], [3, -6, -14, -9, 5, 14], [-8, -94, -123, 56, 66, 10], [18, -70, -140, -32, 64, 77]], ![[0, 0, 0, 0, 0, 1], [-2, -8, -10, 6, 6, 1], [2, -6, -14, -8, 6, 13], [-2, -54, -76, 20, 38, 20], [18, -70, -140, -32, 64, 77], [18, -303, -464, 58, 221, 148]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp23 : Fact (Nat.Prime 23) := fact_iff.2 (by norm_num)
instance hp37 : Fact (Nat.Prime 37) := fact_iff.2 (by norm_num)

def CD23 : CertificateDedekindCriterionLists l 23 where
  n := 2
  a' := [15, 14, 21]
  b' := [2, 9, 2, 12]
  k := [16, 19, 1]
  f := [1, 2, 2, 5, 3, 1]
  g := [2, 20, 11, 21, 1]
  h := [3, 2, 1]
  a := [18, 0, 15, 4]
  b := [3, 21, 1, 11, 19]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD37 : CertificateDedekindCriterionLists l 37 where
  n := 2
  a' := [17, 26, 21]
  b' := [22, 23, 2, 4]
  k := [14, 17, 1]
  f := [5, 6, 1, 7, 8, 1]
  g := [24, 0, 6, 27, 1]
  h := [7, 10, 1]
  a := [14, 32, 1, 10]
  b := [11, 33, 27, 4, 27]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 3
  p := ![2, 23, 37]
  exp := ![4, 1, 1]
  pdgood := [23, 37]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp23.out
    exact hp37.out
  a := [-4690, -10022, 14716, 4314, -2616]
  b := [-3673, 7060, 2606, -4342, -719, 436]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 23 T_ofList CD23
    exact satisfiesDedekindCriterion_of_certificate_lists T l 37 T_ofList CD37

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 4
  n := 2
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0], [1, 0, 0, 1, 1, 0], [0, 1, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0], [1, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 1, 0], [1, 0, 1, 1, 0, 0], [1, 1, 1, 1, 1, 0], [1, 0, 0, 1, 1, 0], [0, 0, 0, 0, 0, 0]], ![[0, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0], [1, 0, 1, 0, 1, 0], [1, 0, 0, 1, 1, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1]], ![[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 1, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![1, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![1, 0, 0, 1, 0, 0]]
  v := ![![1, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![1, 0, 0, 1, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 0]]
  v_ind := ![1, 2, 4, 5]
  w_ind := ![0, 1]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 1], ![0, 0, 1, 0, 1, 0], ![0, 0, 0, 1, 0, 0], ![1, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 1, 0]]
  a := ![![![1, 0, 1, 0], ![-2, 0, 0, 2], ![-6, -14, 6, 14], ![-54, -76, 38, 21]], ![![-8, -10, 6, 4], ![-20, -34, 20, 14], ![-164, -264, 130, 90], ![-381, -614, 291, 226]], ![![-2, -1, 0, 2], ![-14, -18, 16, 0], ![-108, -141, 80, 10], ![-76, -154, 70, 90]], ![![0, 0, 1, 0], ![-2, -1, 0, 2], ![-6, -14, 5, 14], ![-54, -76, 38, 20]], ![![0, 0, 0, 0], ![0, 2, 2, 0], ![-14, -18, 14, 0], ![-6, -14, 6, 14]], ![![0, 0, 0, 2], ![-14, -20, 14, 0], ![-94, -124, 66, 12], ![-78, -150, 70, 78]]]
  c := ![![![-2, 1], ![0, 1], ![13, -4], ![35, 10]], ![![2, 3], ![14, 2], ![142, 12], ![353, 16]], ![![0, 1], ![1, 5], ![46, 33], ![110, -20]], ![![-2, 1], ![0, 1], ![13, -4], ![35, 10]], ![![-1, 1], ![-2, 0], ![3, 5], ![12, -4]], ![![0, 0], ![2, 6], ![44, 28], ![100, -13]]]
  d := ![![![0, 0, 0, 0], ![-18, -22, 14, 4]], ![![2, 0, 2, 2], ![-118, -180, 90, 70]], ![![0, 2, 2, 0], ![-16, -28, 12, 32]], ![![0, 0, 0, 0], ![-18, -22, 14, 4]], ![![0, 2, 0, 0], ![-4, 0, 0, 4]], ![![2, 0, 2, 0], ![-10, -28, 14, 28]]]
  e := ![![![0, 1], ![2, 9]], ![![-2, 0], ![92, 12]], ![![-2, 0], ![26, -8]], ![![-1, 1], ![2, 8]], ![![0, 0], ![0, 2]], ![![-2, 0], ![22, -8]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 3, Sum.inl 0), (Sum.inl 0, Sum.inl 1), (Sum.inl 1, Sum.inl 1), (Sum.inl 0, Sum.inr 0), (Sum.inl 3, Sum.inr 1)]
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

end VoightMaximalOrderD6R484

namespace VoightMaximalOrderD6R489

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨11737724, [-4, -4, 11, 5, -7, -1, 1], 2⟩
local notation "l" => [-4, -4, 11, 5, -7, -1, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 2, 0], ![0, 1, 1, 1, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, -1, -1, -1, -1, 2], ![2, 1, -6, -3, 3, 2]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, -1, -1, -1, -1, 2], ![4, 3, -12, -6, 6, 2], ![4, 1, -14, -15, 0, 10]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, -1, -1, -1, -1, 2], ![4, 3, -12, -6, 6, 2], ![4, 0, -15, -24, -6, 16], ![20, 14, -59, -44, 15, 20]], ![![0, 0, 0, 0, 1, 0], ![0, -1, -1, -1, -1, 2], ![4, 3, -12, -6, 6, 2], ![4, 0, -15, -24, -6, 16], ![32, 26, -90, -57, 30, 20], ![40, 25, -121, -134, 1, 70]], ![![0, 0, 0, 0, 0, 1], ![2, 1, -6, -3, 3, 2], ![4, 1, -14, -15, 0, 10], ![20, 14, -59, -44, 15, 20], ![40, 25, -121, -134, 1, 70], ![103, 75, -298, -264, 47, 122]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-2]], ![[], [], [], [], [-4], [-4, -2]], ![[], [], [], [-4], [-4, -4], [-20, -4, -2]], ![[], [], [-4], [-4, -4], [-32, -4, -4], [-40, -20, -4, -2]], ![[], [-2], [-4, -2], [-20, -4, -2], [-40, -20, -4, -2], [-103, -33, -13, -3, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, -1, -1, -1, -1, 2], [2, 1, -6, -3, 3, 2]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, -1, -1, -1, -1, 2], [4, 3, -12, -6, 6, 2], [4, 1, -14, -15, 0, 10]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, -1, -1, -1, -1, 2], [4, 3, -12, -6, 6, 2], [4, 0, -15, -24, -6, 16], [20, 14, -59, -44, 15, 20]], ![[0, 0, 0, 0, 1, 0], [0, -1, -1, -1, -1, 2], [4, 3, -12, -6, 6, 2], [4, 0, -15, -24, -6, 16], [32, 26, -90, -57, 30, 20], [40, 25, -121, -134, 1, 70]], ![[0, 0, 0, 0, 0, 1], [2, 1, -6, -3, 3, 2], [4, 1, -14, -15, 0, 10], [20, 14, -59, -44, 15, 20], [40, 25, -121, -134, 1, 70], [103, 75, -298, -264, 47, 122]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp613 : Fact (Nat.Prime 613) := fact_iff.2 (by norm_num)
instance hp4787 : Fact (Nat.Prime 4787) := fact_iff.2 (by norm_num)

def CD613 : CertificateDedekindCriterionLists l 613 where
  n := 2
  a' := [384, 158, 579, 86]
  b' := [294, 578, 35, 302, 228]
  k := [324, 333, 76, 143, 1]
  f := [511, 226, 334, 178, 63, 1]
  g := [579, 255, 378, 201, 71, 1]
  h := [541, 1]
  a := [26, 35, 527, 200, 469]
  b := [553, 339, 476, 487, 144]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD4787 : CertificateDedekindCriterionLists l 4787 where
  n := 2
  a' := [4654, 658, 3873, 2536]
  b' := [2391, 2985, 822, 4184, 2365]
  k := [2486, 4713, 1240, 3720, 1]
  f := [426, 150, 27, 243, 474, 1]
  g := [3826, 1340, 240, 2182, 4253, 1]
  h := [533, 1]
  a := [1815, 4504, 1790, 1581, 3541]
  b := [2817, 2442, 4351, 193, 1246]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 3
  p := ![2, 613, 4787]
  exp := ![3, 1, 1]
  pdgood := [613, 4787]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp613.out
    exact hp4787.out
  a := [-4412450, -10252587, 25317336, 4614717, -6617574]
  b := [-1456412, 6654771, 3940709, -6818055, -952941, 1102929]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 613 T_ofList CD613
    exact satisfiesDedekindCriterion_of_certificate_lists T l 4787 T_ofList CD4787

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 1
  n := 5
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 1, 0], [0, 1, 0, 1, 1, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 1, 0], [0, 1, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 1, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 1, 0]], ![[0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 1, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 1, 1, 0, 1, 0]], ![[0, 0, 0, 0, 0, 1], [0, 1, 0, 1, 1, 0], [0, 1, 0, 1, 0, 0], [0, 0, 1, 0, 1, 0], [0, 1, 1, 0, 1, 0], [1, 1, 0, 0, 1, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![1, 0, 1, 1, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0]]
  v := ![![1, 0, 1, 1, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0]]
  v_ind := ![5]
  w_ind := ![0, 1, 2, 3, 4]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 1, 0, 1, 1, 0], ![1, 0, 0, 1, 0, 1], ![0, 0, 1, 0, 0, 0], ![0, 1, 0, 1, 1, 0], ![0, 1, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 0]]
  a := ![![![115]], ![![178]], ![![12]], ![![114]], ![![90]], ![![88]]]
  c := ![![![-20, -170, 13, 23, -165]], ![![-13, -310, 41, 53, -275]], ![![-4, -13, 0, 0, -14]], ![![-20, -170, 13, 23, -165]], ![![-20, -122, 3, 15, -128]], ![![-20, -118, 1, 14, -126]]]
  d := ![![![0], ![8], ![76], ![4], ![36]], ![![2], ![24], ![172], ![4], ![44]], ![![0], ![0], ![4], ![0], ![4]], ![![0], ![8], ![76], ![4], ![36]], ![![0], ![4], ![44], ![4], ![32]], ![![0], ![4], ![40], ![4], ![32]]]
  e := ![![![1, 0, 1, 1, 1], ![0, -16, 5, 2, -10], ![-2, -144, 24, 25, -120], ![-2, -2, 0, 0, -3], ![-10, -45, 1, 3, -47]], ![![0, -1, 0, 0, 0], ![-8, -26, -1, 0, -28], ![-42, -222, -4, 25, -244], ![0, -8, 4, 2, -5], ![2, -93, 21, 17, -71]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![2, -14, 6, 3, -8], ![0, 0, 0, 0, 1], ![-2, -3, -1, -1, -3]], ![![0, 0, 1, 1, 1], ![0, -17, 5, 2, -10], ![-2, -144, 23, 25, -120], ![-2, -2, 0, -1, -3], ![-10, -45, 1, 3, -48]], ![![0, 0, 1, 1, 0], ![2, -14, 6, 3, -7], ![10, -113, 29, 25, -80], ![-2, -2, -1, -1, -3], ![-12, -31, -5, 0, -40]], ![![0, 0, 1, 0, 0], ![2, -14, 6, 3, -8], ![12, -110, 30, 26, -77], ![-2, -3, -1, -1, -3], ![-12, -31, -6, 0, -40]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 0, Sum.inr 1), (Sum.inr 1, Sum.inr 1), (Sum.inr 2, Sum.inr 1), (Sum.inr 3, Sum.inr 1)]
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

end VoightMaximalOrderD6R489

namespace VoightMaximalOrderD6R492

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨11767301, [-49, 0, 70, 8, -16, -1, 1], 287⟩
local notation "l" => [-49, 0, 70, 8, -16, -1, 1]
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

def basisDenominator : ℤ := 287
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![287, 0, 0, 0, 0, 0], ![0, 287, 0, 0, 0, 0], ![0, 0, 287, 0, 0, 0], ![0, 0, 0, 287, 0, 0], ![0, 0, 0, 0, 287, 0], ![126, 119, 85, 75, 111, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-126, -119, -85, -75, -111, 287], ![-49, -46, -33, -29, -43, 112]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-126, -119, -85, -75, -111, 287], ![-77, -119, -155, -83, -95, 287], ![-70, -84, -87, -56, -72, 203]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-126, -119, -85, -75, -111, 287], ![-77, -119, -155, -83, -95, 287], ![-2093, -1974, -1515, -1353, -1879, 4879], ![-875, -840, -663, -574, -793, 2072]], ![![0, 0, 0, 0, 1, 0], ![-126, -119, -85, -75, -111, 287], ![-77, -119, -155, -83, -95, 287], ![-2093, -1974, -1515, -1353, -1879, 4879], ![-2317, -2926, -3266, -2081, -2581, 7175], ![-1610, -1820, -1811, -1276, -1647, 4473]], ![![0, 0, 0, 0, 0, 1], ![-49, -46, -33, -29, -43, 112], ![-70, -84, -87, -56, -72, 203], ![-875, -840, -663, -574, -793, 2072], ![-1610, -1820, -1811, -1276, -1647, 4473], ![-933, -1007, -946, -700, -921, 2477]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-287]], ![[], [], [], [], [-82369], [-32144, -287]], ![[], [], [], [-82369], [-82369, -82369], [-58261, -32144, -287]], ![[], [], [-82369], [-82369, -82369], [-1400273, -82369, -82369], [-594664, -58261, -32144, -287]], ![[], [-287], [-32144, -287], [-58261, -32144, -287], [-594664, -58261, -32144, -287], [-259329, -33090, -12710, -223, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-126, -119, -85, -75, -111, 287], [-49, -46, -33, -29, -43, 112]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-126, -119, -85, -75, -111, 287], [-77, -119, -155, -83, -95, 287], [-70, -84, -87, -56, -72, 203]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-126, -119, -85, -75, -111, 287], [-77, -119, -155, -83, -95, 287], [-2093, -1974, -1515, -1353, -1879, 4879], [-875, -840, -663, -574, -793, 2072]], ![[0, 0, 0, 0, 1, 0], [-126, -119, -85, -75, -111, 287], [-77, -119, -155, -83, -95, 287], [-2093, -1974, -1515, -1353, -1879, 4879], [-2317, -2926, -3266, -2081, -2581, 7175], [-1610, -1820, -1811, -1276, -1647, 4473]], ![[0, 0, 0, 0, 0, 1], [-49, -46, -33, -29, -43, 112], [-70, -84, -87, -56, -72, 203], [-875, -840, -663, -574, -793, 2072], [-1610, -1820, -1811, -1276, -1647, 4473], [-933, -1007, -946, -700, -921, 2477]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp13 : Fact (Nat.Prime 13) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp41 : Fact (Nat.Prime 41) := fact_iff.2 (by norm_num)

def CD13 : CertificateDedekindCriterionLists l 13 where
  n := 2
  a' := [10, 8, 12]
  b' := [11, 12, 10, 10]
  k := [4, 8, 1]
  f := [8, 5, 0, 9, 4, 1]
  g := [5, 5, 5, 10, 1]
  h := [11, 2, 1]
  a := [7, 7, 10]
  b := [11, 6, 1, 3]
  c := [3]
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [14, 24, 6, 12]
  b' := [28, 7, 3, 0, 15]
  k := [4, 14, 1, 25, 1]
  f := [5, 14, -1, 13, 8, 1]
  g := [6, 25, 1, 24, 12, 1]
  h := [16, 1]
  a := [0, 23, 7, 1, 25]
  b := [5, 18, 0, 12, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [7, 41] where
  n := 4
  p := ![7, 13, 29, 41]
  exp := ![2, 1, 1, 2]
  pdgood := [13, 29]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp7.out
    exact hp13.out
    exact hp29.out
    exact hp41.out
  a := [-633737, -941040, 962726, 193820, -149136]
  b := [-329364, 710285, 302241, -291088, -36446, 24856]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 13 T_ofList CD13
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29

noncomputable def M7 : MaximalOrderCertificateLists 7 O Om hm where
  m := 4
  n := 2
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 6, 2, 1, 0], [0, 3, 2, 6, 6, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 6, 2, 1, 0], [0, 0, 6, 1, 3, 0], [0, 0, 4, 0, 5, 0]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 6, 2, 1, 0], [0, 0, 6, 1, 3, 0], [0, 0, 4, 5, 4, 0], [0, 0, 2, 0, 5, 0]], ![[0, 0, 0, 0, 1, 0], [0, 0, 6, 2, 1, 0], [0, 0, 6, 1, 3, 0], [0, 0, 4, 5, 4, 0], [0, 0, 3, 5, 2, 0], [0, 0, 2, 5, 5, 0]], ![[0, 0, 0, 0, 0, 1], [0, 3, 2, 6, 6, 0], [0, 0, 4, 0, 5, 0], [0, 0, 2, 0, 5, 0], [0, 0, 2, 5, 5, 0], [5, 1, 6, 0, 3, 6]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 2, 1, 0, 0, 0], ![0, 3, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![4, 0, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0]]
  v := ![![0, 2, 1, 0, 0, 0], ![0, 3, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![4, 0, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 3, 1, 0]]
  v_ind := ![2, 3, 4, 5]
  w_ind := ![0, 2]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![6, 2, 6, 4, 10, 10], ![4, 2, 12, 4, 0, 10], ![10, 4, 8, 10, 0, 6], ![0, 12, 4, 2, 12, 0], ![0, 0, 2, 2, 4, 0]]
  a := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![-5110, -3756, -5180, 14028], ![-26444, -23148, -32372, 84350], ![-59108, -40664, -52118, 142282], ![-30786, -22434, -29330, 79276]], ![![-1862, -1414, -2004, 5418], ![-9254, -7802, -10918, 28672], ![-26528, -19596, -25770, 69384], ![-13174, -10010, -13332, 35762]], ![![-1750, -1414, -2030, 5432], ![-6790, -5362, -7336, 19614], ![-27790, -22316, -30114, 79744], ![-13102, -10464, -14204, 37688]], ![![-4046, -2926, -4018, 10906], ![-21854, -19390, -27160, 70602], ![-44870, -29806, -37772, 103894], ![-23786, -17024, -22106, 59976]], ![![-1470, -1078, -1484, 4018], ![-7560, -6622, -9254, 24108], ![-16744, -11494, -14714, 40180], ![-8736, -6356, -8302, 22442]]]
  c := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![-8798, 1491], ![-53342, 8603], ![-88462, 16741], ![-49504, 8999]], ![![-3408, 553], ![-18104, 2940], ![-43382, 7814], ![-22400, 3942]], ![![-3428, 539], ![-12338, 2073], ![-50140, 8592], ![-23688, 4037]], ![![-6832, 1169], ![-44674, 7168], ![-64414, 12467], ![-37406, 6885]], ![![-2520, 428], ![-15246, 2460], ![-24976, 4737], ![-14014, 2551]]]
  d := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![42, 28, 70, 70], ![-16492, -14476, -21504, 55860]], ![![84, 28, 0, 70], ![-4592, -3892, -5964, 15680]], ![![56, 70, 0, 42], ![-2716, -2324, -3472, 9408]], ![![28, 14, 84, 0], ![-14112, -12544, -18620, 48216]], ![![14, 14, 28, 0], ![-4760, -4172, -6188, 16072]]]
  e := ![![![1, 0], ![0, 1]], ![![-34, -16], ![-35420, 5350]], ![![-36, -17], ![-9940, 1460]], ![![-14, -21], ![-5964, 868]], ![![0, -7], ![-30576, 4606]], ![![0, -7], ![-10192, 1540]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 2, Sum.inl 0), (Sum.inl 3, Sum.inl 0), (Sum.inl 3, Sum.inr 0), (Sum.inl 0, Sum.inr 1)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

noncomputable def M41 : MaximalOrderCertificateOfUnramifiedLists 41 O Om hm where
  n := 6
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [38, 4, 38, 7, 12, 0], [33, 36, 8, 12, 39, 30]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [38, 4, 38, 7, 12, 0], [5, 4, 9, 40, 28, 0], [12, 39, 36, 26, 10, 39]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [38, 4, 38, 7, 12, 0], [5, 4, 9, 40, 28, 0], [39, 35, 2, 0, 7, 0], [27, 21, 34, 0, 27, 22]], ![[0, 0, 0, 0, 1, 0], [38, 4, 38, 7, 12, 0], [5, 4, 9, 40, 28, 0], [39, 35, 2, 0, 7, 0], [20, 26, 14, 10, 2, 0], [30, 25, 34, 36, 34, 4]], ![[0, 0, 0, 0, 0, 1], [33, 36, 8, 12, 39, 30], [12, 39, 36, 26, 10, 39], [27, 21, 34, 0, 27, 22], [30, 25, 34, 36, 34, 4], [10, 18, 38, 38, 22, 17]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![32, 5, 19, 35, 25, 0], ![5, 16, 36, 17, 18, 0], ![12, 22, 2, 9, 35, 0], ![16, 2, 30, 38, 34, 0], ![37, 20, 13, 11, 2, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [7, 41]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 7 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M7
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 41 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M41
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [7, 41] D q hq hbad)
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

end VoightMaximalOrderD6R492

namespace VoightMaximalOrderD6R495

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨11796113, [-13, -25, 57, 11, -17, -1, 1], 1651⟩
local notation "l" => [-13, -25, 57, 11, -17, -1, 1]
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

def basisDenominator : ℤ := 1651
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![1651, 0, 0, 0, 0, 0], ![0, 1651, 0, 0, 0, 0], ![0, 0, 1651, 0, 0, 0], ![0, 0, 0, 1651, 0, 0], ![0, 0, 0, 0, 1651, 0], ![650, 95, 1265, 470, 93, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-650, -95, -1265, -470, -93, 1651], ![-37, -5, -72, -26, -5, 94]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-650, -95, -1265, -470, -93, 1651], ![-637, -70, -1322, -481, -76, 1651], ![-228, -32, -448, -166, -31, 581]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-650, -95, -1265, -470, -93, 1651], ![-637, -70, -1322, -481, -76, 1651], ![-11687, -1672, -22802, -8528, -1668, 29718], ![-1347, -188, -2649, -984, -188, 3433]], ![![0, 0, 0, 0, 1, 0], ![-650, -95, -1265, -470, -93, 1651], ![-637, -70, -1322, -481, -76, 1651], ![-11687, -1672, -22802, -8528, -1668, 29718], ![-15366, -1817, -31348, -11510, -1994, 39624], ![-4821, -652, -9544, -3547, -665, 12314]], ![![0, 0, 0, 0, 0, 1], ![-37, -5, -72, -26, -5, 94], ![-228, -32, -448, -166, -31, 581], ![-1347, -188, -2649, -984, -188, 3433], ![-4821, -652, -9544, -3547, -665, 12314], ![-846, -117, -1667, -619, -117, 2158]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-1651]], ![[], [], [], [], [-2725801], [-155194, -1651]], ![[], [], [], [-2725801], [-2725801, -2725801], [-959231, -155194, -1651]], ![[], [], [-2725801], [-2725801, -2725801], [-49064418, -2725801, -2725801], [-5667883, -959231, -155194, -1651]], ![[], [-1651], [-155194, -1651], [-959231, -155194, -1651], [-5667883, -959231, -155194, -1651], [-723658, -102911, -9793, -187, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-650, -95, -1265, -470, -93, 1651], [-37, -5, -72, -26, -5, 94]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-650, -95, -1265, -470, -93, 1651], [-637, -70, -1322, -481, -76, 1651], [-228, -32, -448, -166, -31, 581]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-650, -95, -1265, -470, -93, 1651], [-637, -70, -1322, -481, -76, 1651], [-11687, -1672, -22802, -8528, -1668, 29718], [-1347, -188, -2649, -984, -188, 3433]], ![[0, 0, 0, 0, 1, 0], [-650, -95, -1265, -470, -93, 1651], [-637, -70, -1322, -481, -76, 1651], [-11687, -1672, -22802, -8528, -1668, 29718], [-15366, -1817, -31348, -11510, -1994, 39624], [-4821, -652, -9544, -3547, -665, 12314]], ![[0, 0, 0, 0, 0, 1], [-37, -5, -72, -26, -5, 94], [-228, -32, -448, -166, -31, 581], [-1347, -188, -2649, -984, -188, 3433], [-4821, -652, -9544, -3547, -665, 12314], [-846, -117, -1667, -619, -117, 2158]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp13 : Fact (Nat.Prime 13) := fact_iff.2 (by norm_num)
instance hp17 : Fact (Nat.Prime 17) := fact_iff.2 (by norm_num)
instance hp127 : Fact (Nat.Prime 127) := fact_iff.2 (by norm_num)

def CD7 : CertificateDedekindCriterionLists l 7 where
  n := 3
  a' := [1]
  b' := [3, 3]
  k := [1]
  f := [3, 5, -7, 0, 4, 1]
  g := [2, 2, 1]
  h := [4, 1, 1, 4, 1]
  a := [6, 6]
  b := [2, 2, 3, 3, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD17 : CertificateDedekindCriterionLists l 17 where
  n := 2
  a' := [10, 4]
  b' := [2, 12, 10]
  k := [1]
  f := [14, 5, 11, 3, 5, 1]
  g := [15, 2, 8, 1]
  h := [15, 2, 8, 1]
  a := [7, 15, 6]
  b := [6, 1, 7, 3, 11]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [13, 127] where
  n := 4
  p := ![7, 13, 17, 127]
  exp := ![1, 2, 1, 2]
  pdgood := [7, 17]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp7.out
    exact hp13.out
    exact hp17.out
    exact hp127.out
  a := [-20816013, -3107658, 17064854, 872092, -1601472]
  b := [-2150486, 12625779, 1508335, -4369490, -189834, 266912]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T l 17 T_ofList CD17

noncomputable def M13 : MaximalOrderCertificateOfUnramifiedLists 13 O Om hm where
  n := 6
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 9, 9, 11, 11, 0], [2, 8, 6, 0, 8, 3]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 9, 9, 11, 11, 0], [0, 8, 4, 0, 2, 0], [6, 7, 7, 3, 8, 9]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 9, 9, 11, 11, 0], [0, 8, 4, 0, 2, 0], [0, 5, 0, 0, 9, 0], [5, 7, 3, 4, 7, 1]], ![[0, 0, 0, 0, 1, 0], [0, 9, 9, 11, 11, 0], [0, 8, 4, 0, 2, 0], [0, 5, 0, 0, 9, 0], [0, 3, 8, 8, 8, 0], [2, 11, 11, 2, 11, 3]], ![[0, 0, 0, 0, 0, 1], [2, 8, 6, 0, 8, 3], [6, 7, 7, 3, 8, 9], [5, 7, 3, 4, 7, 1], [2, 11, 11, 2, 11, 3], [12, 0, 10, 5, 0, 0]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hindw := by decide
  hwFrobComp := by decide

noncomputable def M127 : MaximalOrderCertificateOfUnramifiedLists 127 O Om hm where
  n := 6
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [112, 32, 5, 38, 34, 0], [90, 122, 55, 101, 122, 94]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [112, 32, 5, 38, 34, 0], [125, 57, 75, 27, 51, 0], [26, 95, 60, 88, 96, 73]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [112, 32, 5, 38, 34, 0], [125, 57, 75, 27, 51, 0], [124, 106, 58, 108, 110, 0], [50, 66, 18, 32, 66, 4]], ![[0, 0, 0, 0, 1, 0], [112, 32, 5, 38, 34, 0], [125, 57, 75, 27, 51, 0], [124, 106, 58, 108, 110, 0], [1, 88, 21, 47, 38, 0], [5, 110, 108, 9, 97, 122]], ![[0, 0, 0, 0, 0, 1], [90, 122, 55, 101, 122, 94], [26, 95, 60, 88, 96, 73], [50, 66, 18, 32, 66, 4], [5, 110, 108, 9, 97, 122], [43, 10, 111, 16, 10, 126]]]
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
  by_cases hbad : q ∈ [13, 127]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 13 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M13
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 127 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M127
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [13, 127] D q hq hbad)
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

end VoightMaximalOrderD6R495

end TraceEuclidean
