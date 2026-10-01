import TraceEuclidean.VoightMaximalOrderCertificates.Chunk071
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

namespace VoightMaximalOrderD6R692

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨14801492, [-1, -4, 4, 11, -4, -3, 1], 2⟩
local notation "l" => [-1, -4, 4, 11, -4, -3, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 2, 0], ![1, 1, 1, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-1, -1, -1, 0, 0, 2], ![-1, 1, -3, -5, 2, 3]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-1, -1, -1, 0, 0, 2], ![-2, 1, -7, -11, 4, 6], ![-5, 0, -10, -18, 1, 13]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-1, -1, -1, 0, 0, 2], ![-2, 1, -7, -11, 4, 6], ![-10, 0, -21, -37, 1, 26], ![-14, 7, -40, -75, 8, 41]], ![![0, 0, 0, 0, 1, 0], ![-1, -1, -1, 0, 0, 2], ![-2, 1, -7, -11, 4, 6], ![-10, 0, -21, -37, 1, 26], ![-27, 15, -79, -151, 15, 80], ![-49, 19, -124, -245, 7, 139]], ![![0, 0, 0, 0, 0, 1], ![-1, 1, -3, -5, 2, 3], ![-5, 0, -10, -18, 1, 13], ![-14, 7, -40, -75, 8, 41], ![-49, 19, -124, -245, 7, 139], ![-76, 42, -209, -421, 18, 224]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-2]], ![[], [], [], [], [-4], [-6, -2]], ![[], [], [], [-4], [-12, -4], [-26, -6, -2]], ![[], [], [-4], [-12, -4], [-52, -12, -4], [-82, -26, -6, -2]], ![[], [-2], [-6, -2], [-26, -6, -2], [-82, -26, -6, -2], [-143, -42, -13, -3, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, -1, -1, 0, 0, 2], [-1, 1, -3, -5, 2, 3]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, -1, -1, 0, 0, 2], [-2, 1, -7, -11, 4, 6], [-5, 0, -10, -18, 1, 13]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, -1, -1, 0, 0, 2], [-2, 1, -7, -11, 4, 6], [-10, 0, -21, -37, 1, 26], [-14, 7, -40, -75, 8, 41]], ![[0, 0, 0, 0, 1, 0], [-1, -1, -1, 0, 0, 2], [-2, 1, -7, -11, 4, 6], [-10, 0, -21, -37, 1, 26], [-27, 15, -79, -151, 15, 80], [-49, 19, -124, -245, 7, 139]], ![[0, 0, 0, 0, 0, 1], [-1, 1, -3, -5, 2, 3], [-5, 0, -10, -18, 1, 13], [-14, 7, -40, -75, 8, 41], [-49, 19, -124, -245, 7, 139], [-76, 42, -209, -421, 18, 224]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp17 : Fact (Nat.Prime 17) := fact_iff.2 (by norm_num)
instance hp41 : Fact (Nat.Prime 41) := fact_iff.2 (by norm_num)
instance hp5309 : Fact (Nat.Prime 5309) := fact_iff.2 (by norm_num)

def CD17 : CertificateDedekindCriterionLists l 17 where
  n := 2
  a' := [6, 5, 6, 1]
  b' := [13, 7, 7, 14, 10]
  k := [15, 16, 7, 8, 1]
  f := [2, 3, 1, 2, 3, 1]
  g := [11, 12, 3, 14, 11, 1]
  h := [3, 1]
  a := [10, 16, 14, 3, 2]
  b := [6, 11, 11, 13, 15]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD41 : CertificateDedekindCriterionLists l 41 where
  n := 2
  a' := [24, 8, 40, 12]
  b' := [36, 35, 24, 39, 14]
  k := [21, 17, 6, 19, 1]
  f := [11, 29, 25, 2, 6, 1]
  g := [15, 39, 33, 2, 8, 1]
  h := [30, 1]
  a := [26, 15, 6, 38, 28]
  b := [22, 10, 32, 18, 13]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD5309 : CertificateDedekindCriterionLists l 5309 where
  n := 2
  a' := [5077, 3398, 156, 4140]
  b' := [2480, 1787, 1265, 548, 4481]
  k := [4761, 2794, 2518, 4869, 1]
  f := [1282, 2552, 456, 1050, 1317, 1]
  g := [2369, 4715, 841, 1940, 2433, 1]
  h := [2873, 1]
  a := [3214, 5167, 1046, 1932, 3235]
  b := [3563, 1181, 440, 3517, 2074]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 4
  p := ![2, 17, 41, 5309]
  exp := ![2, 1, 1, 1]
  pdgood := [17, 41, 5309]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp17.out
    exact hp41.out
    exact hp5309.out
  a := [3308216, -54591888, 18542145, 27014382, -9927936]
  b := [-4527427, 1284902, 18483099, -5113687, -5329725, 1654656]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 17 T_ofList CD17
    exact satisfiesDedekindCriterion_of_certificate_lists T l 41 T_ofList CD41
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5309 T_ofList CD5309

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 2
  n := 4
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 1, 1, 0, 0, 0], [1, 1, 1, 1, 0, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 1, 1, 0, 0, 0], [0, 1, 1, 1, 0, 0], [1, 0, 0, 0, 1, 1]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 1, 1, 0, 0, 0], [0, 1, 1, 1, 0, 0], [0, 0, 1, 1, 1, 0], [0, 1, 0, 1, 0, 1]], ![[0, 0, 0, 0, 1, 0], [1, 1, 1, 0, 0, 0], [0, 1, 1, 1, 0, 0], [0, 0, 1, 1, 1, 0], [1, 1, 1, 1, 1, 0], [1, 1, 0, 1, 1, 1]], ![[0, 0, 0, 0, 0, 1], [1, 1, 1, 1, 0, 1], [1, 0, 0, 0, 1, 1], [0, 1, 0, 1, 0, 1], [1, 1, 0, 1, 1, 1], [0, 0, 1, 1, 0, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![1, 0, 1, 1, 1, 0], ![1, 0, 1, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0], ![1, 0, 1, 1, 0, 0]]
  v := ![![1, 0, 1, 1, 1, 0], ![1, 0, 1, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0], ![1, 0, 1, 1, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0]]
  v_ind := ![4, 5]
  w_ind := ![0, 1, 2, 4]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 1], ![1, 0, 1, 1, 1, 0], ![1, 0, 1, 0, 0, 0], ![0, 1, 1, 1, 1, 0], ![0, 0, 1, 0, 1, 0]]
  a := ![![![5, 8], ![2, 13]], ![![42, 340], ![39, 426]], ![![32, 154], ![22, 202]], ![![6, 8], ![2, 14]], ![![32, 156], ![24, 204]], ![![26, 120], ![14, 158]]]
  c := ![![![0, 0, -2, -8], ![0, 0, -2, -10]], ![![83, 21, -12, -334], ![132, 34, 10, -438]], ![![32, 8, -12, -152], ![51, 13, -4, -198]], ![![0, 0, -2, -8], ![0, 0, -2, -10]], ![![30, 8, -14, -152], ![52, 14, -4, -202]], ![![32, 8, -4, -126], ![40, 10, -2, -154]]]
  d := ![![![0, 0], ![0, 4], ![2, 0], ![2, 4]], ![![2, 2], ![32, 156], ![10, 42], ![38, 190]], ![![2, 0], ![12, 72], ![10, 16], ![22, 84]], ![![0, 0], ![0, 4], ![2, 0], ![2, 4]], ![![2, 0], ![14, 72], ![10, 16], ![24, 84]], ![![2, 0], ![2, 60], ![10, 12], ![14, 68]]]
  e := ![![![0, 0, 1, 0], ![-5, -1, -5, 2], ![0, 0, 0, -1], ![-4, -1, -3, 0]], ![![-2, 0, -2, 0], ![30, 8, -14, -152], ![0, 0, -10, -34], ![30, 8, -22, -178]], ![![0, 0, 0, 0], ![-4, 0, -20, -52], ![0, 0, -4, -16], ![0, 0, -20, -68]], ![![1, 0, 1, 0], ![-5, 0, -5, 2], ![0, 0, 1, -1], ![-4, -1, -3, 1]], ![![0, 1, 1, -1], ![-4, -1, -19, -53], ![-1, 0, -6, -15], ![0, 1, -20, -70]], ![![0, 0, 1, -1], ![-8, -2, -19, -35], ![4, 1, -1, -17], ![1, 0, -14, -55]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 1, Sum.inr 0), (Sum.inr 0, Sum.inr 0), (Sum.inr 2, Sum.inr 0), (Sum.inr 3, Sum.inr 0)]
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

end VoightMaximalOrderD6R692

namespace VoightMaximalOrderD6R694

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨14886909, [-19, -21, 24, 18, -9, -3, 1], 57⟩
local notation "l" => [-19, -21, 24, 18, -9, -3, 1]
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

def basisDenominator : ℤ := 57
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![57, 0, 0, 0, 0, 0], ![0, 57, 0, 0, 0, 0], ![0, 0, 57, 0, 0, 0], ![0, 0, 0, 57, 0, 0], ![0, 0, 0, 0, 57, 0], ![19, 43, 19, 31, 43, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-19, -43, -19, -31, -43, 57], ![-15, -34, -15, -25, -34, 46]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-19, -43, -19, -31, -43, 57], ![-38, -108, -81, -111, -120, 171], ![-44, -117, -78, -111, -127, 178]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-19, -43, -19, -31, -43, 57], ![-38, -108, -81, -111, -120, 171], ![-285, -692, -393, -636, -765, 1026], ![-257, -635, -374, -591, -702, 949]], ![![0, 0, 0, 0, 1, 0], ![-19, -43, -19, -31, -43, 57], ![-38, -108, -81, -111, -120, 171], ![-285, -692, -393, -636, -765, 1026], ![-855, -2274, -1547, -2328, -2625, 3591], ![-897, -2337, -1532, -2337, -2671, 3640]], ![![0, 0, 0, 0, 0, 1], ![-15, -34, -15, -25, -34, 46], ![-44, -117, -78, -111, -127, 178], ![-257, -635, -374, -591, -702, 949], ![-897, -2337, -1532, -2337, -2671, 3640], ![-910, -2345, -1505, -2311, -2662, 3623]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-57]], ![[], [], [], [], [-3249], [-2622, -57]], ![[], [], [], [-3249], [-9747, -3249], [-10146, -2622, -57]], ![[], [], [-3249], [-9747, -3249], [-58482, -9747, -3249], [-54093, -10146, -2622, -57]], ![[], [-57], [-2622, -57], [-10146, -2622, -57], [-54093, -10146, -2622, -57], [-50882, -10048, -2187, -89, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-19, -43, -19, -31, -43, 57], [-15, -34, -15, -25, -34, 46]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-19, -43, -19, -31, -43, 57], [-38, -108, -81, -111, -120, 171], [-44, -117, -78, -111, -127, 178]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-19, -43, -19, -31, -43, 57], [-38, -108, -81, -111, -120, 171], [-285, -692, -393, -636, -765, 1026], [-257, -635, -374, -591, -702, 949]], ![[0, 0, 0, 0, 1, 0], [-19, -43, -19, -31, -43, 57], [-38, -108, -81, -111, -120, 171], [-285, -692, -393, -636, -765, 1026], [-855, -2274, -1547, -2328, -2625, 3591], [-897, -2337, -1532, -2337, -2671, 3640]], ![[0, 0, 0, 0, 0, 1], [-15, -34, -15, -25, -34, 46], [-44, -117, -78, -111, -127, 178], [-257, -635, -374, -591, -702, 949], [-897, -2337, -1532, -2337, -2671, 3640], [-910, -2345, -1505, -2311, -2662, 3623]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp2269 : Fact (Nat.Prime 2269) := fact_iff.2 (by norm_num)

def CD2269 : CertificateDedekindCriterionLists l 2269 where
  n := 2
  a' := [1675, 14, 492, 1518]
  b' := [242, 795, 1975, 942, 604]
  k := [302, 1701, 695, 1027, 1]
  f := [797, 94, 7, 361, 396, 1]
  g := [1031, 121, 9, 467, 512, 1]
  h := [1754, 1]
  a := [600, 505, 1011, 1649, 2037]
  b := [729, 1296, 1620, 936, 232]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3, 19] where
  n := 3
  p := ![3, 19, 2269]
  exp := ![3, 2, 1]
  pdgood := [2269]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp19.out
    exact hp2269.out
  a := [1002216, -6972174, 2704707, 2488464, -818652]
  b := [-1959907, 826154, 2519039, -823291, -482965, 136442]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2269 T_ofList CD2269

noncomputable def M3 : MaximalOrderCertificateLists 3 O Om hm where
  m := 4
  n := 2
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [2, 2, 2, 2, 2, 0], [0, 2, 0, 2, 2, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [2, 2, 2, 2, 2, 0], [1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 2, 1]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [2, 2, 2, 2, 2, 0], [1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [1, 1, 1, 0, 0, 1]], ![[0, 0, 0, 0, 1, 0], [2, 2, 2, 2, 2, 0], [1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 2, 1]], ![[0, 0, 0, 0, 0, 1], [0, 2, 0, 2, 2, 1], [1, 0, 0, 0, 2, 1], [1, 1, 1, 0, 0, 1], [0, 0, 1, 0, 2, 1], [2, 1, 1, 2, 2, 2]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![2, 0, 1, 0, 0, 0], ![0, 2, 0, 1, 0, 0], ![2, 0, 0, 0, 1, 0], ![2, 0, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0]]
  v := ![![2, 0, 1, 0, 0, 0], ![0, 2, 0, 1, 0, 0], ![2, 0, 0, 0, 1, 0], ![2, 0, 0, 0, 0, 1]]
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
  g := ![![1, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 1], ![2, 1, 2, 0, 1, 2], ![2, 0, 2, 0, 0, 2], ![0, 1, 1, 2, 2, 0], ![2, 1, 0, 2, 1, 0]]
  a := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![-75, -109, -126, 180], ![-419, -669, -811, 1098], ![-1649, -2510, -2876, 3927], ![-1611, -2472, -2857, 3896]], ![![-231, -332, -370, 531], ![-1275, -2036, -2476, 3336], ![-4788, -7255, -8246, 11274], ![-4709, -7206, -8281, 11294]], ![![-150, -222, -252, 360], ![-846, -1338, -1626, 2196], ![-3222, -4896, -5580, 7626], ![-3162, -4844, -5578, 7608]], ![![-198, -279, -321, 456], ![-1041, -1647, -1980, 2679], ![-3978, -6066, -6939, 9462], ![-3903, -5988, -6903, 9402]], ![![-117, -168, -204, 285], ![-591, -918, -1086, 1482], ![-2352, -3627, -4194, 5700], ![-2295, -3540, -4107, 5586]]]
  c := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![0, 35], ![-14, 198], ![75, 831], ![54, 806]], ![![6, 108], ![-35, 602], ![260, 2435], ![192, 2373]], ![![0, 70], ![-20, 396], ![162, 1634], ![120, 1588]], ![![4, 86], ![-19, 493], ![191, 2017], ![147, 1961]], ![![0, 48], ![-3, 282], ![84, 1185], ![70, 1147]]]
  d := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![3, 0, 0, 3], ![-39, -72, -102, 138]], ![![6, 0, 3, 6], ![-144, -237, -333, 447]], ![![6, 0, 0, 6], ![-90, -144, -204, 276]], ![![3, 6, 6, 0], ![-111, -183, -252, 342]], ![![0, 6, 3, 0], ![-54, -93, -123, 171]]]
  e := ![![![1, 0], ![0, 1]], ![![-3, 2], ![-13, 15]], ![![-8, 1], ![-29, 49]], ![![-6, 0], ![-18, 30]], ![![-6, -3], ![-24, 36]], ![![0, -3], ![-15, 21]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 3, Sum.inl 0), (Sum.inl 3, Sum.inl 1), (Sum.inl 0, Sum.inr 0), (Sum.inl 3, Sum.inr 0)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

noncomputable def M19 : MaximalOrderCertificateOfUnramifiedLists 19 O Om hm where
  n := 6
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 14, 0, 7, 14, 0], [4, 4, 4, 13, 4, 8]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 14, 0, 7, 14, 0], [0, 6, 14, 3, 13, 0], [13, 16, 17, 3, 6, 7]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 14, 0, 7, 14, 0], [0, 6, 14, 3, 13, 0], [0, 11, 6, 10, 14, 0], [9, 11, 6, 17, 1, 18]], ![[0, 0, 0, 0, 1, 0], [0, 14, 0, 7, 14, 0], [0, 6, 14, 3, 13, 0], [0, 11, 6, 10, 14, 0], [0, 6, 11, 9, 16, 0], [15, 0, 7, 0, 8, 11]], ![[0, 0, 0, 0, 0, 1], [4, 4, 4, 13, 4, 8], [13, 16, 17, 3, 6, 7], [9, 11, 6, 17, 1, 18], [15, 0, 7, 0, 8, 11], [2, 11, 15, 7, 17, 13]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![0, 14, 12, 0, 14, 0], ![0, 16, 7, 0, 7, 0], ![0, 13, 12, 1, 14, 0], ![0, 9, 1, 0, 18, 0], ![0, 13, 12, 0, 14, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [3, 19]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 3 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M3
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 19 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M19
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [3, 19] D q hq hbad)
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

end VoightMaximalOrderD6R694

namespace VoightMaximalOrderD6R704

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨15004240, [-17, -26, 35, 16, -11, -2, 1], 16⟩
local notation "l" => [-17, -26, 35, 16, -11, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![-1, -1, -1, 2, 0, 0], ![-1, 0, 0, 1, 1, 0], ![0, -1, -1, 0, -1, 2], ![5, 8, -6, -7, 4, 3]], ![![0, 0, 1, 0, 0, 0], ![-1, -1, -1, 2, 0, 0], ![-1, 0, 0, 0, 2, 0], ![-1, -2, -1, 1, 0, 2], ![11, 18, -11, -16, 9, 4], ![28, 31, -8, -40, 1, 17]], ![![0, 0, 0, 1, 0, 0], ![-1, 0, 0, 1, 1, 0], ![-1, -2, -1, 1, 0, 2], ![4, 7, -7, -6, 5, 4], ![29, 31, -8, -41, 0, 18], ![83, 105, -39, -111, 16, 37]], ![![0, 0, 0, 0, 1, 0], ![0, -1, -1, 0, -1, 2], ![11, 18, -11, -16, 9, 4], ![29, 31, -8, -41, 0, 18], ![110, 150, -61, -142, 32, 36], ![252, 297, -55, -337, 5, 107]], ![![0, 0, 0, 0, 0, 1], ![5, 8, -6, -7, 4, 3], ![28, 31, -8, -40, 1, 17], ![83, 105, -39, -111, 16, 37], ![252, 297, -55, -337, 5, 107], ![606, 747, -182, -790, 48, 229]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-4]], ![[], [], [], [], [-8], [-12, -4]], ![[], [], [], [-4], [-12, -4], [-42, -8, -2]], ![[], [], [-8], [-12, -4], [-60, -8, -4], [-106, -34, -6, -2]], ![[], [-4], [-12, -4], [-42, -8, -2], [-106, -34, -6, -2], [-275, -72, -20, -4, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [-1, -1, -1, 2, 0, 0], [-1, 0, 0, 1, 1, 0], [0, -1, -1, 0, -1, 2], [5, 8, -6, -7, 4, 3]], ![[0, 0, 1, 0, 0, 0], [-1, -1, -1, 2, 0, 0], [-1, 0, 0, 0, 2, 0], [-1, -2, -1, 1, 0, 2], [11, 18, -11, -16, 9, 4], [28, 31, -8, -40, 1, 17]], ![[0, 0, 0, 1, 0, 0], [-1, 0, 0, 1, 1, 0], [-1, -2, -1, 1, 0, 2], [4, 7, -7, -6, 5, 4], [29, 31, -8, -41, 0, 18], [83, 105, -39, -111, 16, 37]], ![[0, 0, 0, 0, 1, 0], [0, -1, -1, 0, -1, 2], [11, 18, -11, -16, 9, 4], [29, 31, -8, -41, 0, 18], [110, 150, -61, -142, 32, 36], [252, 297, -55, -337, 5, 107]], ![[0, 0, 0, 0, 0, 1], [5, 8, -6, -7, 4, 3], [28, 31, -8, -40, 1, 17], [83, 105, -39, -111, 16, 37], [252, 297, -55, -337, 5, 107], [606, 747, -182, -790, 48, 229]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp37 : Fact (Nat.Prime 37) := fact_iff.2 (by norm_num)
instance hp137 : Fact (Nat.Prime 137) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1]
  b' := [3, 0, 3]
  k := [3, 3, 1, 1, 1]
  f := [4, 6, -6, -2, 3, 1]
  g := [3, 1, 4, 2, 2, 1]
  h := [1, 1]
  a := [1, 1, 3, 1, 4]
  b := [4, 2, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD37 : CertificateDedekindCriterionLists l 37 where
  n := 2
  a' := [29, 0, 12]
  b' := [10, 9, 13, 34]
  k := [14, 29, 1]
  f := [5, 7, 8, 9, 4, 1]
  g := [24, 23, 34, 32, 1]
  h := [7, 3, 1]
  a := [0, 27, 32, 30]
  b := [17, 12, 10, 31, 7]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD137 : CertificateDedekindCriterionLists l 137 where
  n := 2
  a' := [39, 115, 112, 61]
  b' := [66, 52, 72, 46, 70]
  k := [98, 37, 82, 47, 1]
  f := [21, 27, 27, 31, 30, 1]
  g := [65, 82, 83, 95, 91, 1]
  h := [44, 1]
  a := [1, 62, 43, 78]
  b := [84, 97, 57, 59]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 4
  p := ![2, 5, 37, 137]
  exp := ![3, 1, 1, 1]
  pdgood := [5, 37, 137]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp5.out
    exact hp37.out
    exact hp137.out
  a := [-7374, -12376, 16288, 6576, -4986]
  b := [-2977, 7451, 6364, -5858, -1373, 831]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 37 T_ofList CD37
    exact satisfiesDedekindCriterion_of_certificate_lists T l 137 T_ofList CD137

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 4
  n := 2
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0], [1, 0, 0, 1, 1, 0], [0, 1, 1, 0, 1, 0], [1, 0, 0, 1, 0, 1]], ![[0, 0, 1, 0, 0, 0], [1, 1, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0], [1, 0, 1, 1, 0, 0], [1, 0, 1, 0, 1, 0], [0, 1, 0, 0, 1, 1]], ![[0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 1, 0], [1, 0, 1, 1, 0, 0], [0, 1, 1, 0, 1, 0], [1, 1, 0, 1, 0, 0], [1, 1, 1, 1, 0, 1]], ![[0, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0], [1, 0, 1, 0, 1, 0], [1, 1, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0], [0, 1, 1, 1, 1, 1]], ![[0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 1], [0, 1, 0, 0, 1, 1], [1, 1, 1, 1, 0, 1], [0, 1, 1, 1, 1, 1], [0, 1, 0, 0, 0, 1]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![1, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 1]]
  v := ![![1, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 1, 0]]
  w := ![![1, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 0, 1]]
  v_ind := ![1, 2, 3, 4]
  w_ind := ![0, 1]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 1], ![1, 0, 0, 0, 1, 0], ![1, 0, 0, 1, 1, 0], ![0, 1, 0, 0, 1, 0], ![1, 1, 1, 0, 1, 0]]
  a := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![8, -6, -3, 5], ![29, -7, -38, 3], ![110, -46, -114, 21], ![346, -73, -393, 15]], ![![0, -1, 0, 0], ![18, -10, -16, 10], ![31, -8, -40, 1], ![150, -61, -142, 34]], ![![0, -1, 2, 1], ![16, -11, -14, 10], ![38, -15, -45, 6], ![181, -69, -182, 34]], ![![0, 0, 0, 0], ![18, -12, -14, 10], ![32, -8, -40, 2], ![150, -62, -142, 32]], ![![0, 0, 2, 0], ![18, -10, -14, 12], ![30, -8, -38, 2], ![168, -72, -158, 42]]]
  c := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![-2, 2], ![10, 10], ![36, 22], ![134, 65]], ![![0, 1], ![3, 2], ![14, 9], ![47, 18]], ![![-2, 1], ![2, 3], ![14, 11], ![61, 27]], ![![-1, 1], ![2, 2], ![12, 9], ![47, 19]], ![![-2, 1], ![0, 2], ![11, 10], ![50, 21]]]
  d := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 2, 2, 0], ![1766, -456, -1880, 130]], ![![0, 0, 0, 2], ![594, -110, -674, 12]], ![![0, 0, 2, 2], ![804, -188, -894, 44]], ![![2, 0, 0, 2], ![612, -122, -688, 20]], ![![2, 2, 0, 2], ![674, -136, -768, 22]]]
  e := ![![![1, 0], ![0, 1]], ![![-2, 1], ![653, 285]], ![![0, 0], ![234, 108]], ![![-1, 0], ![308, 145]], ![![-2, 0], ![236, 110]], ![![-2, 0], ![262, 128]]]
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

end VoightMaximalOrderD6R704

namespace VoightMaximalOrderD6R705

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨15005125, [-36, -18, 41, 9, -12, -1, 1], 24⟩
local notation "l" => [-36, -18, 41, 9, -12, -1, 1]
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

def basisDenominator : ℤ := 12
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![12, 0, 0, 0, 0, 0], ![0, 12, 0, 0, 0, 0], ![0, 0, 12, 0, 0, 0], ![0, 0, 0, 12, 0, 0], ![0, 6, 0, 0, 6, 0], ![0, 8, 9, 0, 2, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, -1, 0, 0, 2, 0], ![0, -3, -4, 0, -2, 6], ![3, -1, -5, 0, 1, 3]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, -1, 0, 0, 2, 0], ![0, -6, -9, 0, -4, 12], ![18, 0, -25, -4, 10, 6], ![9, -3, -20, -5, 1, 15]], ![![0, 0, 0, 1, 0, 0], ![0, -1, 0, 0, 2, 0], ![0, -6, -9, 0, -4, 12], ![36, 0, -50, -9, 20, 12], ![18, -14, -70, -25, -22, 78], ![45, -4, -82, -20, 3, 51]], ![![0, 0, 0, 0, 1, 0], ![0, -3, -4, 0, -2, 6], ![18, 0, -25, -4, 10, 6], ![18, -14, -70, -25, -22, 78], ![117, 14, -160, -35, 35, 54], ![78, 2, -138, -41, 3, 87]], ![![0, 0, 0, 0, 0, 1], ![3, -1, -5, 0, 1, 3], ![9, -3, -20, -5, 1, 15], ![45, -4, -82, -20, 3, 51], ![78, 2, -138, -41, 3, 87], ![77, 2, -136, -40, 2, 87]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-12]], ![[], [], [], [], [-72], [-36, -12]], ![[], [], [], [-144], [-72, -72], [-180, -36, -12]], ![[], [], [-72], [-72, -72], [-468, -36, -36], [-312, -90, -18, -6]], ![[], [-12], [-36, -12], [-180, -36, -12], [-312, -90, -18, -6], [-308, -90, -21, -5, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, -1, 0, 0, 2, 0], [0, -3, -4, 0, -2, 6], [3, -1, -5, 0, 1, 3]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, -1, 0, 0, 2, 0], [0, -6, -9, 0, -4, 12], [18, 0, -25, -4, 10, 6], [9, -3, -20, -5, 1, 15]], ![[0, 0, 0, 1, 0, 0], [0, -1, 0, 0, 2, 0], [0, -6, -9, 0, -4, 12], [36, 0, -50, -9, 20, 12], [18, -14, -70, -25, -22, 78], [45, -4, -82, -20, 3, 51]], ![[0, 0, 0, 0, 1, 0], [0, -3, -4, 0, -2, 6], [18, 0, -25, -4, 10, 6], [18, -14, -70, -25, -22, 78], [117, 14, -160, -35, 35, 54], [78, 2, -138, -41, 3, 87]], ![[0, 0, 0, 0, 0, 1], [3, -1, -5, 0, 1, 3], [9, -3, -20, -5, 1, 15], [45, -4, -82, -20, 3, 51], [78, 2, -138, -41, 3, 87], [77, 2, -136, -40, 2, 87]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp120041 : Fact (Nat.Prime 120041) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 2]
  b' := [0, 0, 1]
  k := [1]
  f := [9, 6, -5, 1, 4, 1]
  g := [3, 2, 2, 1]
  h := [3, 2, 2, 1]
  a := [2, 1, 4]
  b := [1, 4, 1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD120041 : CertificateDedekindCriterionLists l 120041 where
  n := 2
  a' := [29906, 13883, 6755, 56639]
  b' := [41117, 79447, 31472, 111976, 84705]
  k := [50560, 71582, 65562, 105246, 1]
  f := [3981, 2574, 4194, 6430, 6942, 1]
  g := [64605, 41763, 68056, 104339, 112643, 1]
  h := [7397, 1]
  a := [21816, 6944, 66171, 104950, 8516]
  b := [107093, 47252, 5797, 97389, 111525]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3] where
  n := 4
  p := ![2, 3, 5, 120041]
  exp := ![3, 2, 1, 1]
  pdgood := [5, 120041]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp3.out
    exact hp5.out
    exact hp120041.out
  a := [-1594034, 1003104, 5531001, 12739, -1066278]
  b := [787248, 3174178, -54945, -1657014, -31742, 177713]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 120041 T_ofList CD120041

noncomputable def M2 : MaximalOrderCertificateOfUnramifiedLists 2 O Om hm where
  n := 6
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [1, 1, 1, 0, 1, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0], [1, 1, 0, 1, 1, 1]], ![[0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0], [1, 0, 0, 0, 1, 1]], ![[0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 1, 0], [0, 0, 0, 1, 1, 1]], ![[0, 0, 0, 0, 0, 1], [1, 1, 1, 0, 1, 1], [1, 1, 0, 1, 1, 1], [1, 0, 0, 0, 1, 1], [0, 0, 0, 1, 1, 1], [1, 0, 0, 0, 0, 1]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![1, 0, 0, 1, 1, 0], ![1, 0, 0, 0, 0, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hindw := by decide
  hwFrobComp := by decide

noncomputable def M3 : MaximalOrderCertificateOfUnramifiedLists 3 O Om hm where
  n := 6
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 2, 0, 0, 2, 0], [0, 0, 2, 0, 1, 0], [0, 2, 1, 0, 1, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 2, 0, 0, 2, 0], [0, 0, 0, 0, 2, 0], [0, 0, 2, 2, 1, 0], [0, 0, 1, 1, 1, 0]], ![[0, 0, 0, 1, 0, 0], [0, 2, 0, 0, 2, 0], [0, 0, 0, 0, 2, 0], [0, 0, 1, 0, 2, 0], [0, 1, 2, 2, 2, 0], [0, 2, 2, 1, 0, 0]], ![[0, 0, 0, 0, 1, 0], [0, 0, 2, 0, 1, 0], [0, 0, 2, 2, 1, 0], [0, 1, 2, 2, 2, 0], [0, 2, 2, 1, 2, 0], [0, 2, 0, 1, 0, 0]], ![[0, 0, 0, 0, 0, 1], [0, 2, 1, 0, 1, 0], [0, 0, 1, 1, 1, 0], [0, 2, 2, 1, 0, 0], [0, 2, 0, 1, 0, 0], [2, 2, 2, 2, 2, 0]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![0, 2, 1, 1, 0, 0], ![0, 1, 2, 1, 1, 0], ![0, 2, 2, 0, 2, 0], ![0, 0, 0, 0, 2, 0], ![0, 2, 2, 2, 1, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [2, 3]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 2 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M2
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 3 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M3
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2, 3] D q hq hbad)
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

end VoightMaximalOrderD6R705

end TraceEuclidean
