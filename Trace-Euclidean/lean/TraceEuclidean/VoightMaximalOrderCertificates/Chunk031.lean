import TraceEuclidean.VoightMaximalOrderCertificates.Chunk027
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

namespace VoightMaximalOrderD6R143

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4950125, [5, -25, 14, 14, -8, -2, 1], 5⟩
local notation "l" => [5, -25, 14, 14, -8, -2, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![5, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0], ![0, 0, 5, 0, 0, 0], ![0, 0, 0, 5, 0, 0], ![0, 0, 0, 0, 5, 0], ![0, 0, 4, 0, 2, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, -4, 0, -2, 5], ![-1, 5, -6, -2, 0, 4]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, -4, 0, -2, 5], ![-5, 25, -22, -14, 4, 10], ![-4, 19, -19, -14, -2, 16]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, -4, 0, -2, 5], ![-5, 25, -22, -14, 4, 10], ![-10, 45, -51, -42, -22, 60], ![-16, 76, -69, -51, -10, 54]], ![![0, 0, 0, 0, 1, 0], ![0, 0, -4, 0, -2, 5], ![-5, 25, -22, -14, 4, 10], ![-10, 45, -51, -42, -22, 60], ![-60, 290, -227, -171, 2, 130], ![-54, 254, -208, -177, -31, 166]], ![![0, 0, 0, 0, 0, 1], ![-1, 5, -6, -2, 0, 4], ![-4, 19, -19, -14, -2, 16], ![-16, 76, -69, -51, -10, 54], ![-54, 254, -208, -177, -31, 166], ![-58, 272, -222, -190, -37, 181]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-5]], ![[], [], [], [], [-25], [-20, -5]], ![[], [], [], [-25], [-50, -25], [-80, -20, -5]], ![[], [], [-25], [-50, -25], [-300, -50, -25], [-270, -80, -20, -5]], ![[], [-5], [-20, -5], [-80, -20, -5], [-270, -80, -20, -5], [-290, -90, -24, -6, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, -4, 0, -2, 5], [-1, 5, -6, -2, 0, 4]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, -4, 0, -2, 5], [-5, 25, -22, -14, 4, 10], [-4, 19, -19, -14, -2, 16]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, -4, 0, -2, 5], [-5, 25, -22, -14, 4, 10], [-10, 45, -51, -42, -22, 60], [-16, 76, -69, -51, -10, 54]], ![[0, 0, 0, 0, 1, 0], [0, 0, -4, 0, -2, 5], [-5, 25, -22, -14, 4, 10], [-10, 45, -51, -42, -22, 60], [-60, 290, -227, -171, 2, 130], [-54, 254, -208, -177, -31, 166]], ![[0, 0, 0, 0, 0, 1], [-1, 5, -6, -2, 0, 4], [-4, 19, -19, -14, -2, 16], [-16, 76, -69, -51, -10, 54], [-54, 254, -208, -177, -31, 166], [-58, 272, -222, -190, -37, 181]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp199 : Fact (Nat.Prime 199) := fact_iff.2 (by norm_num)

def CD199 : CertificateDedekindCriterionLists l 199 where
  n := 3
  a' := [98, 71, 157]
  b' := [17, 196, 128, 110]
  k := [116, 132, 136, 14, 115, 197, 1]
  f := [40, 70, 199, 184, 45, 1]
  g := [45, 45, 190, 65, 1]
  h := [177, 132, 1]
  a := [164, 103, 131, 99]
  b := [124, 60, 179, 58, 100]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [5] where
  n := 2
  p := ![5, 199]
  exp := ![3, 1]
  pdgood := [199]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp199.out
  a := [-12200, -4464, 17028, 3768, -3708]
  b := [-3435, 7460, 3622, -4620, -834, 618]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 199 T_ofList CD199

noncomputable def M5 : MaximalOrderCertificateLists 5 O Om hm where
  m := 3
  n := 3
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 1, 0, 3, 0], [4, 0, 4, 3, 0, 4]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 1, 0, 3, 0], [0, 0, 3, 1, 4, 0], [1, 4, 1, 1, 3, 1]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 1, 0, 3, 0], [0, 0, 3, 1, 4, 0], [0, 0, 4, 3, 3, 0], [4, 1, 1, 4, 0, 4]], ![[0, 0, 0, 0, 1, 0], [0, 0, 1, 0, 3, 0], [0, 0, 3, 1, 4, 0], [0, 0, 4, 3, 3, 0], [0, 0, 3, 4, 2, 0], [1, 4, 2, 3, 4, 1]], ![[0, 0, 0, 0, 0, 1], [4, 0, 4, 3, 0, 4], [1, 4, 1, 1, 3, 1], [4, 1, 1, 4, 0, 4], [1, 4, 2, 3, 4, 1], [2, 2, 3, 0, 3, 1]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 3, 4, 1, 0, 0], ![0, 3, 2, 0, 1, 0], ![1, 2, 3, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0]]
  v := ![![0, 3, 4, 1, 0, 0], ![0, 3, 2, 0, 1, 0], ![1, 2, 3, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 3, 0], ![0, 0, 0, 1, 4, 0]]
  v_ind := ![3, 4, 5]
  w_ind := ![0, 2, 3]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![0, 3, 3, 9, 9, 6], ![3, 12, 0, 0, 9, 3], ![6, 0, 9, 12, 9, 6], ![6, 9, 12, 3, 6, 6], ![12, 3, 0, 9, 9, 12]]
  a := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![-1665, -216, 2100], ![-3462, -369, 3420], ![-3870, -579, 3963]], ![![-1170, -150, 1425], ![-2400, -90, 2175], ![-2667, -327, 2619]], ![![-1695, -210, 2220], ![-3660, -390, 3675], ![-4095, -615, 4260]], ![![-1230, -150, 1620], ![-2700, -195, 2625], ![-3015, -420, 3105]], ![![-2340, -330, 2865], ![-4695, -585, 4650], ![-5250, -840, 5355]]]
  c := ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![-525, 795, -126], ![-909, 2007, -27], ![-1035, 2235, -22]], ![![-360, 585, -73], ![-600, 1422, -6], ![-693, 1560, 1]], ![![-552, 780, -151], ![-972, 2097, -42], ![-1107, 2340, -38]], ![![-405, 573, -109], ![-705, 1554, -27], ![-810, 1725, -22]], ![![-720, 1170, -145], ![-1230, 2745, -15], ![-1395, 3063, -8]]]
  d := ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![45, 45, 30], ![-45, -45, 345], ![-3105, 135, 3465]], ![![0, 45, 15], ![-30, -90, 285], ![-2340, 450, 2070]], ![![60, 45, 30], ![-15, -30, 345], ![-3150, 135, 3690]], ![![15, 30, 30], ![0, -45, 270], ![-2385, 270, 2565]], ![![45, 45, 60], ![-120, -45, 465], ![-4365, -90, 4905]]]
  e := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![-6, -63, -23], ![-75, -54, -74], ![-900, 1413, -231]], ![![0, -21, -9], ![-60, -24, -51], ![-585, 1152, -102]], ![![0, -75, -25], ![-75, -75, -85], ![-945, 1350, -270]], ![![0, -30, -10], ![-60, -45, -65], ![-675, 1035, -165]], ![![0, -75, -30], ![-105, -15, -90], ![-1260, 2070, -255]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 2, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 0, Sum.inr 1), (Sum.inl 2, Sum.inr 1)]
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

end VoightMaximalOrderD6R143

namespace VoightMaximalOrderD6R147

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5061656, [-4, 0, 13, 3, -7, -1, 1], 2⟩
local notation "l" => [-4, 0, 13, 3, -7, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, -1, -1, -1, -1, 2], ![2, -1, -7, -2, 3, 2]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, -1, -1, -1, -1, 2], ![4, -1, -14, -4, 6, 2], ![4, -3, -18, -14, 1, 10]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, -1, -1, -1, -1, 2], ![4, -1, -14, -4, 6, 2], ![4, -4, -21, -24, -4, 16], ![20, -7, -74, -39, 15, 22]], ![![0, 0, 0, 0, 1, 0], ![0, -1, -1, -1, -1, 2], ![4, -1, -14, -4, 6, 2], ![4, -4, -21, -24, -4, 16], ![32, -8, -112, -49, 28, 24], ![44, -17, -176, -133, 12, 74]], ![![0, 0, 0, 0, 0, 1], ![2, -1, -7, -2, 3, 2], ![4, -3, -18, -14, 1, 10], ![20, -7, -74, -39, 15, 22], ![44, -17, -176, -133, 12, 74], ![109, -35, -411, -262, 54, 140]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-2]], ![[], [], [], [], [-4], [-4, -2]], ![[], [], [], [-4], [-4, -4], [-20, -4, -2]], ![[], [], [-4], [-4, -4], [-32, -4, -4], [-44, -20, -4, -2]], ![[], [-2], [-4, -2], [-20, -4, -2], [-44, -20, -4, -2], [-109, -35, -13, -3, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, -1, -1, -1, -1, 2], [2, -1, -7, -2, 3, 2]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, -1, -1, -1, -1, 2], [4, -1, -14, -4, 6, 2], [4, -3, -18, -14, 1, 10]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, -1, -1, -1, -1, 2], [4, -1, -14, -4, 6, 2], [4, -4, -21, -24, -4, 16], [20, -7, -74, -39, 15, 22]], ![[0, 0, 0, 0, 1, 0], [0, -1, -1, -1, -1, 2], [4, -1, -14, -4, 6, 2], [4, -4, -21, -24, -4, 16], [32, -8, -112, -49, 28, 24], [44, -17, -176, -133, 12, 74]], ![[0, 0, 0, 0, 0, 1], [2, -1, -7, -2, 3, 2], [4, -3, -18, -14, 1, 10], [20, -7, -74, -39, 15, 22], [44, -17, -176, -133, 12, 74], [109, -35, -411, -262, 54, 140]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp23 : Fact (Nat.Prime 23) := fact_iff.2 (by norm_num)
instance hp27509 : Fact (Nat.Prime 27509) := fact_iff.2 (by norm_num)

def CD23 : CertificateDedekindCriterionLists l 23 where
  n := 2
  a' := [9, 0, 13, 3]
  b' := [12, 18, 21, 8, 4]
  k := [20, 2, 3, 16, 1]
  f := [2, 1, 1, 1, 3, 1]
  g := [14, 3, 11, 5, 19, 1]
  h := [3, 1]
  a := [11, 1, 8, 9, 16]
  b := [10, 15, 5, 17, 7]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD27509 : CertificateDedekindCriterionLists l 27509 where
  n := 2
  a' := [16507, 3566, 20731, 20692]
  b' := [24020, 13017, 967, 19797, 12367]
  k := [26860, 11521, 2562, 15402, 1]
  f := [1186, 143, 931, 631, 4721, 1]
  g := [5390, 649, 4231, 2867, 21455, 1]
  h := [6053, 1]
  a := [1008, 1918, 5127, 25527, 22505]
  b := [3213, 16420, 17589, 2442, 5004]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 3
  p := ![2, 23, 27509]
  exp := ![4, 1, 1]
  pdgood := [23, 27509]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp23.out
    exact hp27509.out
  a := [-2530828, -11732097, 10775198, 6086421, -3766734]
  b := [-1804938, 3547923, 3922533, -3178833, -1119035, 627789]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 23 T_ofList CD23
    exact satisfiesDedekindCriterion_of_certificate_lists T l 27509 T_ofList CD27509

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 1
  n := 5
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 1, 0], [0, 1, 1, 0, 1, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 1, 0], [0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 1, 0]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 1, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 1, 0, 1, 1, 0]], ![[0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 1, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0]], ![[0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 1, 0], [0, 1, 0, 0, 1, 0], [0, 1, 0, 1, 1, 0], [0, 1, 0, 1, 0, 0], [1, 1, 1, 0, 0, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![1, 1, 0, 1, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0]]
  v := ![![1, 1, 0, 1, 0, 1]]
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
  g := ![![1, 1, 0, 1, 1, 0], ![1, 1, 0, 1, 1, 1], ![0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 1, 0], ![0, 1, 0, 1, 1, 0], ![0, 1, 0, 0, 1, 0]]
  a := ![![![119]], ![![284]], ![![92]], ![![104]], ![![118]], ![![94]]]
  c := ![![![-22, -146, 17, -74, -160]], ![![-39, -392, 53, -178, -394]], ![![-22, -99, 4, -57, -125]], ![![-26, -108, 4, -65, -138]], ![![-22, -146, 17, -74, -160]], ![![-22, -102, 6, -58, -127]]]
  d := ![![![0], ![8], ![84], ![4], ![36]], ![![2], ![28], ![232], ![8], ![80]], ![![0], ![4], ![48], ![4], ![32]], ![![0], ![4], ![52], ![4], ![36]], ![![0], ![8], ![84], ![4], ![36]], ![![0], ![4], ![52], ![4], ![32]]]
  e := ![![![1, 0, 1, 1, 1], ![0, -14, 5, -6, -8], ![-6, -134, 24, -55, -116], ![-2, 0, 0, -2, -3], ![-10, -35, 3, -23, -45]], ![![0, 0, 1, 0, 0], ![-6, -32, 6, -19, -32], ![-36, -310, 36, -146, -323], ![-2, -7, 3, -5, -7], ![-12, -109, 18, -52, -106]], ![![0, 0, 1, 0, 0], ![2, -14, 6, -3, -6], ![8, -112, 28, -32, -73], ![-2, -1, -1, -3, -3], ![-12, -21, -4, -20, -40]], ![![0, 1, 1, 0, 0], ![2, -14, 7, -3, -6], ![10, -126, 34, -35, -79], ![-2, -1, -1, -3, -2], ![-14, -22, -5, -23, -43]], ![![0, 0, 1, 1, 1], ![0, -15, 5, -6, -8], ![-6, -134, 23, -55, -116], ![-2, 0, 0, -3, -3], ![-10, -35, 3, -23, -46]], ![![0, 0, 1, 1, 0], ![2, -14, 6, -3, -5], ![6, -113, 27, -35, -76], ![-2, 0, -1, -3, -3], ![-12, -21, -3, -20, -40]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 0, Sum.inr 1), (Sum.inr 0, Sum.inr 1), (Sum.inr 1, Sum.inr 1), (Sum.inr 2, Sum.inr 1)]
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

end VoightMaximalOrderD6R147

namespace VoightMaximalOrderD6R152

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5173625, [1, -7, 10, 8, -8, -1, 1], 2⟩
local notation "l" => [1, -7, 10, 8, -8, -1, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 2, 0], ![1, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-1, 0, 0, 0, 0, 2], ![-1, 4, -5, -4, 4, 1]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-1, 0, 0, 0, 0, 2], ![-2, 7, -10, -8, 8, 2], ![-5, 3, -1, -9, 0, 9]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-1, 0, 0, 0, 0, 2], ![-2, 7, -10, -8, 8, 2], ![-10, 6, -3, -18, 0, 18], ![-9, 31, -42, -37, 27, 9]], ![![0, 0, 0, 0, 1, 0], ![-1, 0, 0, 0, 0, 2], ![-2, 7, -10, -8, 8, 2], ![-10, 6, -3, -18, 0, 18], ![-18, 62, -84, -75, 54, 18], ![-36, 27, -14, -78, -1, 63]], ![![0, 0, 0, 0, 0, 1], ![-1, 4, -5, -4, 4, 1], ![-5, 3, -1, -9, 0, 9], ![-9, 31, -42, -37, 27, 9], ![-36, 27, -14, -78, -1, 63], ![-31, 108, -144, -133, 87, 31]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-2]], ![[], [], [], [], [-4], [-2, -2]], ![[], [], [], [-4], [-4, -4], [-18, -2, -2]], ![[], [], [-4], [-4, -4], [-36, -4, -4], [-18, -18, -2, -2]], ![[], [-2], [-2, -2], [-18, -2, -2], [-18, -18, -2, -2], [-63, -9, -9, -1, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, 0, 0, 0, 0, 2], [-1, 4, -5, -4, 4, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, 0, 0, 0, 0, 2], [-2, 7, -10, -8, 8, 2], [-5, 3, -1, -9, 0, 9]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-1, 0, 0, 0, 0, 2], [-2, 7, -10, -8, 8, 2], [-10, 6, -3, -18, 0, 18], [-9, 31, -42, -37, 27, 9]], ![[0, 0, 0, 0, 1, 0], [-1, 0, 0, 0, 0, 2], [-2, 7, -10, -8, 8, 2], [-10, 6, -3, -18, 0, 18], [-18, 62, -84, -75, 54, 18], [-36, 27, -14, -78, -1, 63]], ![[0, 0, 0, 0, 0, 1], [-1, 4, -5, -4, 4, 1], [-5, 3, -1, -9, 0, 9], [-9, 31, -42, -37, 27, 9], [-36, 27, -14, -78, -1, 63], [-31, 108, -144, -133, 87, 31]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp41389 : Fact (Nat.Prime 41389) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 1]
  b' := [1, 3, 3]
  k := [1]
  f := [0, 3, 2, 2, 4, 1]
  g := [1, 4, 2, 1]
  h := [1, 4, 2, 1]
  a := [1]
  b := [1, 3, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD41389 : CertificateDedekindCriterionLists l 41389 where
  n := 2
  a' := [16294, 7776, 17748, 2063]
  b' := [26510, 23758, 38667, 1022, 16143]
  k := [38104, 5741, 12627, 32873, 1]
  f := [14643, 24240, 13009, 7549, 9909, 1]
  g := [24289, 40207, 21577, 12521, 16436, 1]
  h := [24952, 1]
  a := [26746, 40643, 22303, 6454, 13345]
  b := [11302, 6040, 24656, 13905, 28044]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 3
  p := ![2, 5, 41389]
  exp := ![1, 1, 1]
  pdgood := [5, 41389]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp5.out
    exact hp41389.out
  a := [-7539482, -4531413, 10381044, 1020177, -1896102]
  b := [-1136196, 3645863, 1764953, -2588439, -222699, 316017]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 41389 T_ofList CD41389

noncomputable def M2 : MaximalOrderCertificateOfUnramifiedLists 2 O Om hm where
  n := 6
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0], [1, 0, 1, 0, 0, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [1, 1, 1, 1, 0, 1]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [1, 1, 0, 1, 1, 1]], ![[0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 1, 1]], ![[0, 0, 0, 0, 0, 1], [1, 0, 1, 0, 0, 1], [1, 1, 1, 1, 0, 1], [1, 1, 0, 1, 1, 1], [0, 1, 0, 0, 1, 1], [1, 0, 0, 1, 1, 1]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![1, 0, 0, 1, 1, 1]]
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

end VoightMaximalOrderD6R152

namespace VoightMaximalOrderD6R153

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5192000, [1, -13, 12, 9, -8, -1, 1], 4⟩
local notation "l" => [1, -13, 12, 9, -8, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-1, 0, -1, 0, 2, 0], ![0, 0, 0, 0, 0, 1], ![-5, 6, -10, -5, 9, 1]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-1, 0, -1, 0, 2, 0], ![0, -1, 0, -1, 0, 2], ![-5, 6, -10, -5, 9, 1], ![0, 1, 1, -15, -1, 10]], ![![0, 0, 0, 1, 0, 0], ![-1, 0, -1, 0, 2, 0], ![0, -1, 0, -1, 0, 2], ![-9, 12, -20, -10, 16, 2], ![0, 1, 1, -15, -1, 10], ![-35, 60, -84, -49, 60, 9]], ![![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1], ![-5, 6, -10, -5, 9, 1], ![0, 1, 1, -15, -1, 10], ![-20, 33, -47, -27, 35, 5], ![2, 10, 10, -72, -9, 40]], ![![0, 0, 0, 0, 0, 1], ![-5, 6, -10, -5, 9, 1], ![0, 1, 1, -15, -1, 10], ![-35, 60, -84, -49, 60, 9], ![2, 10, 10, -72, -9, 40], ![-128, 242, -318, -190, 216, 31]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-2]], ![[], [], [], [], [-2], [-2, -2]], ![[], [], [], [-4], [-2, -2], [-20, -2, -2]], ![[], [], [-2], [-2, -2], [-11, -1, -1], [-10, -11, -1, -1]], ![[], [-2], [-2, -2], [-20, -2, -2], [-10, -11, -1, -1], [-80, -10, -11, -1, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [-1, 0, -1, 0, 2, 0], [0, 0, 0, 0, 0, 1], [-5, 6, -10, -5, 9, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [-1, 0, -1, 0, 2, 0], [0, -1, 0, -1, 0, 2], [-5, 6, -10, -5, 9, 1], [0, 1, 1, -15, -1, 10]], ![[0, 0, 0, 1, 0, 0], [-1, 0, -1, 0, 2, 0], [0, -1, 0, -1, 0, 2], [-9, 12, -20, -10, 16, 2], [0, 1, 1, -15, -1, 10], [-35, 60, -84, -49, 60, 9]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [-5, 6, -10, -5, 9, 1], [0, 1, 1, -15, -1, 10], [-20, 33, -47, -27, 35, 5], [2, 10, 10, -72, -9, 40]], ![[0, 0, 0, 0, 0, 1], [-5, 6, -10, -5, 9, 1], [0, 1, 1, -15, -1, 10], [-35, 60, -84, -49, 60, 9], [2, 10, 10, -72, -9, 40], [-128, 242, -318, -190, 216, 31]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp59 : Fact (Nat.Prime 59) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 2]
  b' := [4, 4, 1]
  k := [1]
  f := [3, 9, 4, 3, 4, 1]
  g := [4, 4, 2, 1]
  h := [4, 4, 2, 1]
  a := [3, 3, 3]
  b := [3, 3, 1, 1, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [9, 3, 6, 10]
  b' := [10, 4, 2, 4, 9]
  k := [1, 7, 8, 8, 1]
  f := [0, 2, 0, 0, 2, 1]
  g := [1, 8, 4, 5, 9, 1]
  h := [1, 1]
  a := [9, 2, 6, 8, 5]
  b := [1, 7, 2, 5, 6]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD59 : CertificateDedekindCriterionLists l 59 where
  n := 2
  a' := [20, 49, 50, 38]
  b' := [4, 54, 6, 37, 16]
  k := [25, 43, 46, 23, 1]
  f := [43, 33, 18, 5, 9, 1]
  g := [54, 40, 22, 6, 11, 1]
  h := [47, 1]
  a := [15, 24, 45, 58, 41]
  b := [58, 26, 36, 24, 18]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 4
  p := ![2, 5, 11, 59]
  exp := ![3, 1, 1, 1]
  pdgood := [5, 11, 59]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp5.out
    exact hp11.out
    exact hp59.out
  a := [-19163, -416, 33050, -2167, -7422]
  b := [-3471, 12723, 1549, -9039, 155, 1237]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 59 T_ofList CD59

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 2
  n := 4
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 1, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0], [1, 0, 0, 1, 1, 1], [0, 1, 1, 1, 1, 0]], ![[0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0], [0, 1, 1, 1, 1, 0], [1, 0, 0, 1, 0, 1]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 1, 1], [0, 1, 1, 1, 1, 0], [0, 1, 1, 1, 1, 1], [0, 0, 0, 0, 1, 0]], ![[0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 1, 1], [0, 1, 1, 1, 1, 0], [1, 0, 0, 1, 0, 1], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![1, 1, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 1, 1], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1]]
  v := ![![1, 1, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 1, 1], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 1, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1]]
  v_ind := ![2, 3]
  w_ind := ![0, 1, 2, 5]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 1], ![1, 0, 0, 0, 0, 1], ![1, 0, 1, 0, 1, 1], ![1, 0, 0, 1, 0, 0], ![0, 1, 1, 1, 0, 0]]
  a := ![![![1, 0], ![0, 1]], ![![-20, -25], ![-103, -73]], ![![-8, -20], ![-84, -48]], ![![-18, -24], ![-82, -64]], ![![0, 0], ![-20, -8]], ![![0, 2], ![-20, -10]]]
  c := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![17, 10, 6, -2], ![66, 38, 50, -27]], ![![12, 4, 4, 2], ![49, 30, 42, -25]], ![![16, 10, 6, -3], ![56, 30, 41, -19]], ![![0, 1, -1, 0], ![10, 8, 8, -7]], ![![-2, 2, -2, -1], ![10, 9, 7, -7]]]
  d := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![0, 2], ![-878, -860], ![-22, -10], ![-784, -622]], ![![0, 0], ![-636, -534], ![-20, -10], ![-636, -380]], ![![2, 0], ![-728, -770], ![-20, -8], ![-614, -554]], ![![0, 2], ![-168, -128], ![-2, 0], ![-168, -98]], ![![2, 2], ![-204, -176], ![0, 2], ![-186, -138]]]
  e := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![-1, 1, -1, 0], ![684, 303, 498, -166], ![10, 11, 6, -9], ![542, 267, 437, -187]], ![![1, 0, 0, 1], ![454, 217, 360, -144], ![10, 9, 8, -8], ![380, 216, 344, -184]], ![![0, 1, -2, 0], ![595, 251, 422, -121], ![9, 9, 8, -7], ![458, 206, 354, -124]], ![![0, 0, 0, 0], ![112, 62, 84, -42], ![0, 2, 0, -2], ![98, 60, 84, -50]], ![![-2, 0, 0, 0], ![144, 78, 98, -46], ![-2, 2, -2, -2], ![122, 68, 92, -48]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 1, Sum.inr 0), (Sum.inr 1, Sum.inr 0), (Sum.inl 0, Sum.inr 1), (Sum.inl 1, Sum.inr 1)]
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

end VoightMaximalOrderD6R153

end TraceEuclidean
