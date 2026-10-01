import TraceEuclidean.VoightMaximalOrderCertificates.Chunk085
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

namespace VoightMaximalOrderD7R169

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨156519164, [4, -12, -7, 19, 5, -8, -1, 1], 2⟩
local notation "l" => [4, -12, -7, 19, 5, -8, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSeven := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSeven_irreducible row row_mem
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
def basisNumerator : Fin 7 → Fin 7 → ℤ := ![![2, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 0], ![0, 0, 0, 2, 0, 0, 0], ![0, 0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 2, 0], ![0, 1, 1, 1, 0, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 7 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, -1, -1, -1, 0, -1, 2], ![-2, 5, 3, -10, -2, 3, 2]], ![![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, -1, -1, -1, 0, -1, 2], ![-4, 11, 6, -20, -5, 7, 2], ![-4, 5, 8, -20, -14, 1, 10]], ![![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, -1, -1, -1, 0, -1, 2], ![-4, 11, 6, -20, -5, 7, 2], ![-4, -1, 10, -21, -24, -6, 18], ![-20, 45, 34, -93, -40, 15, 22]], ![![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, -1, -1, -1, 0, -1, 2], ![-4, 11, 6, -20, -5, 7, 2], ![-4, -1, 10, -21, -24, -6, 18], ![-36, 92, 59, -164, -57, 36, 24], ![-44, 75, 96, -201, -137, 11, 74]], ![![0, 0, 0, 0, 0, 1, 0], ![0, -1, -1, -1, 0, -1, 2], ![-4, 11, 6, -20, -5, 7, 2], ![-4, -1, 10, -21, -24, -6, 18], ![-36, 92, 59, -164, -57, 36, 24], ![-48, 48, 128, -217, -212, -21, 120], ![-148, 315, 286, -655, -349, 74, 170]], ![![0, 0, 0, 0, 0, 0, 1], ![-2, 5, 3, -10, -2, 3, 2], ![-4, 5, 8, -20, -14, 1, 10], ![-20, 45, 34, -93, -40, 15, 22], ![-44, 75, 96, -201, -137, 11, 74], ![-148, 315, 286, -655, -349, 74, 170], ![-257, 499, 541, -1133, -700, 90, 346]]]
  s := ![![[], [], [], [], [], [], []], ![[], [], [], [], [], [], [-2]], ![[], [], [], [], [], [-4], [-4, -2]], ![[], [], [], [], [-4], [-4, -4], [-20, -4, -2]], ![[], [], [], [-4], [-4, -4], [-36, -4, -4], [-44, -20, -4, -2]], ![[], [], [-4], [-4, -4], [-36, -4, -4], [-48, -36, -4, -4], [-148, -44, -20, -4, -2]], ![[], [-2], [-4, -2], [-20, -4, -2], [-44, -20, -4, -2], [-148, -44, -20, -4, -2], [-257, -99, -33, -12, -3, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 7 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 7) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 7) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 7) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 7 → Fin 7 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, -1, -1, -1, 0, -1, 2], [-2, 5, 3, -10, -2, 3, 2]], ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, -1, -1, -1, 0, -1, 2], [-4, 11, 6, -20, -5, 7, 2], [-4, 5, 8, -20, -14, 1, 10]], ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, -1, -1, -1, 0, -1, 2], [-4, 11, 6, -20, -5, 7, 2], [-4, -1, 10, -21, -24, -6, 18], [-20, 45, 34, -93, -40, 15, 22]], ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, -1, -1, -1, 0, -1, 2], [-4, 11, 6, -20, -5, 7, 2], [-4, -1, 10, -21, -24, -6, 18], [-36, 92, 59, -164, -57, 36, 24], [-44, 75, 96, -201, -137, 11, 74]], ![[0, 0, 0, 0, 0, 1, 0], [0, -1, -1, -1, 0, -1, 2], [-4, 11, 6, -20, -5, 7, 2], [-4, -1, 10, -21, -24, -6, 18], [-36, 92, 59, -164, -57, 36, 24], [-48, 48, 128, -217, -212, -21, 120], [-148, 315, 286, -655, -349, 74, 170]], ![[0, 0, 0, 0, 0, 0, 1], [-2, 5, 3, -10, -2, 3, 2], [-4, 5, 8, -20, -14, 1, 10], [-20, 45, 34, -93, -40, 15, 22], [-44, 75, 96, -201, -137, 11, 74], [-148, 315, 286, -655, -349, 74, 170], [-257, 499, 541, -1133, -700, 90, 346]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp39129791 : Fact (Nat.Prime 39129791) := fact_iff.2 (by norm_num)

def CD39129791 : CertificateDedekindCriterionLists l 39129791 where
  n := 2
  a' := [6948130, 2539091, 24715503, 30529037, 25752448]
  b' := [38699441, 16165417, 8415342, 19446964, 16090009, 8751189]
  k := [22127222, 21846265, 22758953, 8188605, 5496974, 1]
  f := [12067940, 4736016, 13675478, 2835809, 3582047, 9589393, 1]
  g := [28080668, 11020147, 31821218, 6598590, 8334999, 22313382, 1]
  h := [16816408, 1]
  a := [8521411, 22689612, 6410163, 2350448, 24720703, 17287497]
  b := [16272681, 32510077, 23647592, 10889592, 7236417, 21842294]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 2
  p := ![2, 39129791]
  exp := ![3, 1]
  pdgood := [39129791]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp39129791.out
  a := [9645466, -284898973, -356387908, 412175700, 152737426, -108685955]
  b := [-22871372, -77928523, 142754075, 100417005, -93155656, -24037713, 15526565]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 39129791 T_ofList CD39129791

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 1
  n := 6
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 0, 1, 0], [0, 1, 1, 0, 0, 1, 0]], ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 0, 1, 0], [0, 1, 0, 0, 1, 1, 0], [0, 1, 0, 0, 0, 1, 0]], ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 0, 1, 0], [0, 1, 0, 0, 1, 1, 0], [0, 1, 0, 1, 0, 0, 0], [0, 1, 0, 1, 0, 1, 0]], ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 0, 1, 0], [0, 1, 0, 0, 1, 1, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0], [0, 1, 0, 1, 1, 1, 0]], ![[0, 0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 0, 1, 0], [0, 1, 0, 0, 1, 1, 0], [0, 1, 0, 1, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0]], ![[0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 0], [0, 1, 0, 0, 0, 1, 0], [0, 1, 0, 1, 0, 1, 0], [0, 1, 0, 1, 1, 1, 0], [0, 1, 0, 1, 1, 0, 0], [1, 1, 1, 1, 0, 0, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![1, 1, 0, 0, 1, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 1, 0, 0], ![0, 1, 0, 1, 0, 1, 0], ![0, 1, 1, 0, 0, 0, 0]]
  v := ![![1, 1, 0, 0, 1, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 1, 0, 0], ![0, 1, 0, 1, 0, 1, 0], ![0, 1, 1, 0, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0]]
  v_ind := ![6]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 1, 1, 0, 0, 1, 0], ![1, 0, 0, 1, 1, 0, 1], ![0, 1, 0, 1, 0, 0, 0], ![0, 1, 0, 1, 1, 0, 0], ![0, 1, 1, 0, 0, 1, 0], ![0, 1, 0, 0, 1, 1, 0], ![0, 1, 0, 0, 1, 0, 0]]
  a := ![![![211]], ![![540]], ![![26]], ![![118]], ![![210]], ![![290]], ![![94]]]
  c := ![![![-200, -666, -482, 350, 57, 178]], ![![-457, -1322, -905, 531, 66, 393]], ![![-26, -93, -74, 57, 13, 22]], ![![-96, -268, -188, 106, 16, 75]], ![![-200, -666, -482, 350, 57, 178]], ![![-262, -826, -586, 397, 60, 227]], ![![-72, -182, -121, 54, 5, 55]]]
  d := ![![![0], ![52], ![40], ![56], ![288], ![8]], ![![2], ![188], ![56], ![192], ![480], ![28]], ![![0], ![4], ![4], ![4], ![44], ![0]], ![![0], ![40], ![8], ![40], ![96], ![4]], ![![0], ![52], ![40], ![56], ![288], ![8]], ![![0], ![84], ![44], ![88], ![336], ![12]], ![![0], ![36], ![4], ![36], ![56], ![4]]]
  e := ![![![1, 0, -1, 0, 1, 1], ![-62, -254, -201, 172, 36, 58], ![-24, -32, -14, -11, -6, 10], ![-64, -254, -200, 170, 35, 58], ![-200, -412, -238, 28, -20, 143], ![-8, -27, -25, 19, 6, 7]], ![![0, 2, 1, -2, 0, 0], ![-146, -380, -254, 121, 12, 112], ![-54, -188, -148, 114, 25, 42], ![-150, -394, -268, 132, 16, 115], ![-454, -1509, -1093, 793, 130, 397], ![-20, -45, -36, 16, 5, 11]], ![![0, 0, 1, 0, 0, 0], ![-6, -30, -28, 23, 8, 6], ![-2, 2, 0, -2, -1, 0], ![-6, -28, -28, 22, 8, 7], ![-26, -33, -15, -11, -8, 9], ![0, 3, 0, -2, 1, 1]], ![![0, 1, 1, 0, 0, 0], ![-28, -64, -43, 15, 2, 16], ![-8, -28, -28, 21, 7, 6], ![-28, -62, -44, 14, 3, 17], ![-92, -317, -243, 185, 36, 74], ![-2, 2, -1, -3, 1, 0]], ![![0, 0, -1, 0, 1, 1], ![-62, -255, -201, 172, 36, 58], ![-24, -32, -15, -11, -6, 10], ![-64, -254, -200, 169, 35, 58], ![-200, -412, -238, 28, -21, 143], ![-8, -27, -25, 19, 6, 6]], ![![0, 0, -1, 1, 1, 0], ![-82, -288, -216, 165, 31, 69], ![-30, -63, -43, 13, 1, 16], ![-84, -288, -217, 163, 31, 69], ![-260, -667, -439, 202, 15, 202], ![-10, -30, -27, 19, 6, 5]], ![![0, 0, 0, 1, 0, 0], ![-22, -34, -16, -8, -5, 10], ![-6, -28, -28, 22, 8, 7], ![-22, -33, -17, -9, -4, 11], ![-68, -283, -228, 194, 43, 65], ![-2, 1, 0, -3, 0, 0]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 0, Sum.inr 1), (Sum.inr 0, Sum.inr 1), (Sum.inr 1, Sum.inr 1), (Sum.inr 2, Sum.inr 1), (Sum.inr 3, Sum.inr 1)]
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

noncomputable def bOm : Basis (Fin 7) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 7 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 7
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 7 := T_degree

noncomputable def bQ : Basis (Fin 7) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 7) (Fin 7) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 7) :
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
          (∑ x : Fin 7,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 7,
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
        (List.ofFn fun i : Fin 7 =>
          (List.ofFn fun j : Fin 7 =>
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
      (voightPolynomialDiscriminantInput 7 row row_mem)
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

end VoightMaximalOrderD7R169

namespace VoightMaximalOrderD7R281

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨204909928, [1, -2, -8, 15, 6, -8, -1, 1], 2⟩
local notation "l" => [1, -2, -8, 15, 6, -8, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSeven := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSeven_irreducible row row_mem
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
def basisNumerator : Fin 7 → Fin 7 → ℤ := ![![2, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 0], ![0, 0, 0, 2, 0, 0, 0], ![0, 0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 2, 0], ![1, 1, 1, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 7 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![-1, -1, -1, 0, 0, 0, 2], ![-1, 1, 4, -7, -3, 4, 1]], ![![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![-1, -1, -1, 0, 0, 0, 2], ![-2, 1, 7, -15, -6, 8, 2], ![-5, -4, 1, -3, -10, 1, 9]], ![![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![-1, -1, -1, 0, 0, 0, 2], ![-2, 1, 7, -15, -6, 8, 2], ![-10, -8, 1, -7, -21, 2, 18], ![-10, 3, 31, -62, -30, 26, 11]], ![![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![-1, -1, -1, 0, 0, 0, 2], ![-2, 1, 7, -15, -6, 8, 2], ![-10, -8, 1, -7, -21, 2, 18], ![-20, 6, 62, -125, -61, 51, 22], ![-37, -25, 21, -46, -95, 14, 63]], ![![0, 0, 0, 0, 0, 1, 0], ![-1, -1, -1, 0, 0, 0, 2], ![-2, 1, 7, -15, -6, 8, 2], ![-10, -8, 1, -7, -21, 2, 18], ![-20, 6, 62, -125, -61, 51, 22], ![-73, -49, 43, -92, -191, 27, 124], ![-77, 12, 213, -420, -235, 157, 91]], ![![0, 0, 0, 0, 0, 0, 1], ![-1, 1, 4, -7, -3, 4, 1], ![-5, -4, 1, -3, -10, 1, 9], ![-10, 3, 31, -62, -30, 26, 11], ![-37, -25, 21, -46, -95, 14, 63], ![-77, 12, 213, -420, -235, 157, 91], ![-127, -73, 112, -217, -353, 67, 208]]]
  s := ![![[], [], [], [], [], [], []], ![[], [], [], [], [], [], [-2]], ![[], [], [], [], [], [-4], [-2, -2]], ![[], [], [], [], [-4], [-4, -4], [-18, -2, -2]], ![[], [], [], [-4], [-4, -4], [-36, -4, -4], [-22, -18, -2, -2]], ![[], [], [-4], [-4, -4], [-36, -4, -4], [-44, -36, -4, -4], [-126, -22, -18, -2, -2]], ![[], [-2], [-2, -2], [-18, -2, -2], [-22, -18, -2, -2], [-126, -22, -18, -2, -2], [-93, -64, -11, -9, -1, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 7 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 7) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 7) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 7) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 7 → Fin 7 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [-1, -1, -1, 0, 0, 0, 2], [-1, 1, 4, -7, -3, 4, 1]], ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [-1, -1, -1, 0, 0, 0, 2], [-2, 1, 7, -15, -6, 8, 2], [-5, -4, 1, -3, -10, 1, 9]], ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [-1, -1, -1, 0, 0, 0, 2], [-2, 1, 7, -15, -6, 8, 2], [-10, -8, 1, -7, -21, 2, 18], [-10, 3, 31, -62, -30, 26, 11]], ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [-1, -1, -1, 0, 0, 0, 2], [-2, 1, 7, -15, -6, 8, 2], [-10, -8, 1, -7, -21, 2, 18], [-20, 6, 62, -125, -61, 51, 22], [-37, -25, 21, -46, -95, 14, 63]], ![[0, 0, 0, 0, 0, 1, 0], [-1, -1, -1, 0, 0, 0, 2], [-2, 1, 7, -15, -6, 8, 2], [-10, -8, 1, -7, -21, 2, 18], [-20, 6, 62, -125, -61, 51, 22], [-73, -49, 43, -92, -191, 27, 124], [-77, 12, 213, -420, -235, 157, 91]], ![[0, 0, 0, 0, 0, 0, 1], [-1, 1, 4, -7, -3, 4, 1], [-5, -4, 1, -3, -10, 1, 9], [-10, 3, 31, -62, -30, 26, 11], [-37, -25, 21, -46, -95, 14, 63], [-77, 12, 213, -420, -235, 157, 91], [-127, -73, 112, -217, -353, 67, 208]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp127 : Fact (Nat.Prime 127) := fact_iff.2 (by norm_num)
instance hp201683 : Fact (Nat.Prime 201683) := fact_iff.2 (by norm_num)

def CD127 : CertificateDedekindCriterionLists l 127 where
  n := 2
  a' := [57, 34, 86, 17]
  b' := [15, 109, 24, 89, 103]
  k := [62, 50, 20, 82, 34, 1]
  f := [21, 28, 30, 40, 45, 30, 1]
  g := [58, 76, 81, 109, 122, 80, 1]
  h := [46, 1]
  a := [9, 90, 3, 26, 106, 16]
  b := [115, 62, 125, 37, 59, 111]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD201683 : CertificateDedekindCriterionLists l 201683 where
  n := 2
  a' := [179353, 51974, 73991, 72135, 158061]
  b' := [199170, 95574, 68555, 116744, 198558, 74498]
  k := [103997, 76589, 184358, 162149, 68766, 1]
  f := [52585, 59936, 32948, 52139, 25109, 44559, 1]
  g := [159582, 181888, 99986, 158227, 76197, 135224, 1]
  h := [66458, 1]
  a := [126749, 38211, 34342, 119909, 139097, 6601]
  b := [182638, 139547, 115770, 115539, 148790, 195082]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 3
  p := ![2, 127, 201683]
  exp := ![4, 1, 1]
  pdgood := [127, 201683]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp127.out
    exact hp201683.out
  a := [-998521030, -14154377362, -2180081911, 12349650451, 951445257, -2102449223]
  b := [-704170443, -445304107, 4777018415, 797973816, -2468110098, -178827878, 300349889]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 127 T_ofList CD127
    exact satisfiesDedekindCriterion_of_certificate_lists T l 201683 T_ofList CD201683

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 1
  n := 6
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [1, 1, 1, 0, 0, 0, 0], [1, 1, 0, 1, 1, 0, 1]], ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [1, 1, 1, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0], [1, 0, 1, 1, 0, 1, 1]], ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [1, 1, 1, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0], [0, 1, 1, 0, 0, 0, 1]], ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [1, 1, 1, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0], [0, 0, 0, 1, 1, 1, 0], [1, 1, 1, 0, 1, 0, 1]], ![[0, 0, 0, 0, 0, 1, 0], [1, 1, 1, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0], [0, 0, 0, 1, 1, 1, 0], [1, 1, 1, 0, 1, 1, 0], [1, 0, 1, 0, 1, 1, 1]], ![[0, 0, 0, 0, 0, 0, 1], [1, 1, 0, 1, 1, 0, 1], [1, 0, 1, 1, 0, 1, 1], [0, 1, 1, 0, 0, 0, 1], [1, 1, 1, 0, 1, 0, 1], [1, 0, 1, 0, 1, 1, 1], [1, 1, 0, 1, 1, 1, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 0, 1, 0, 1, 1, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 1, 0, 0], ![1, 0, 1, 0, 1, 0, 0], ![1, 1, 0, 1, 0, 0, 0], ![0, 1, 1, 1, 1, 1, 0]]
  v := ![![0, 0, 1, 0, 1, 1, 1]]
  w := ![![1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 1, 0, 0], ![1, 0, 1, 0, 1, 0, 0], ![1, 1, 0, 1, 0, 0, 0], ![0, 1, 1, 1, 1, 1, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0]]
  v_ind := ![6]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 1, 1, 1], ![1, 0, 0, 0, 1, 0, 0], ![0, 1, 1, 1, 0, 1, 0], ![1, 1, 1, 1, 0, 1, 1], ![1, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 1, 1]]
  a := ![![![105]], ![![728]], ![![106]], ![![286]], ![![658]], ![![14]], ![![746]]]
  c := ![![![-122, -130, -75, 83, 5, -19]], ![![-1049, -1070, -691, 793, 9, -85]], ![![-122, -130, -75, 83, 5, -19]], ![![-480, -471, -361, 401, -23, 4]], ![![-976, -991, -659, 753, -2, -62]], ![![-10, -11, -7, 6, 0, -2]], ![![-1086, -1107, -724, 828, 4, -80]]]
  d := ![![![0], ![36], ![44], ![40], ![4], ![88]], ![![2], ![210], ![298], ![238], ![70], ![782]], ![![0], ![36], ![44], ![40], ![4], ![88]], ![![0], ![52], ![96], ![56], ![44], ![392]], ![![2], ![178], ![262], ![202], ![70], ![742]], ![![0], ![4], ![4], ![4], ![0], ![8]], ![![2], ![210], ![302], ![238], ![74], ![818]]]
  e := ![![![0, 1, 0, 0, 0, 0], ![-16, -22, 1, -2, 8, -16], ![-28, -34, -14, 11, 4, -12], ![-16, -20, 2, -4, 9, -18], ![-10, -12, -16, 14, -6, 7], ![-165, -157, -145, 152, -20, 18]], ![![0, 0, 0, 0, 0, 0], ![-244, -260, -150, 166, 10, -38], ![-358, -378, -244, 260, 0, -36], ![-264, -282, -164, 178, 10, -42], ![-98, -102, -86, 86, -12, 8], ![-1204, -1202, -872, 968, -36, -30]], ![![1, 1, 0, 0, 0, 0], ![-16, -21, 1, -2, 8, -16], ![-28, -34, -13, 11, 4, -12], ![-16, -20, 2, -3, 9, -18], ![-10, -12, -16, 14, -5, 7], ![-165, -157, -145, 152, -20, 19]], ![![0, -1, 0, 0, 0, 1], ![-149, -135, -146, 154, -28, 34], ![-172, -167, -159, 162, -26, 24], ![-158, -148, -161, 167, -34, 42], ![-14, -20, 4, -7, 9, -18], ![-380, -434, -214, 230, 27, -87]], ![![0, -1, 0, 0, 1, 0], ![-238, -250, -167, 182, -4, -15], ![-337, -355, -243, 259, -10, -18], ![-256, -275, -181, 195, -5, -16], ![-90, -88, -69, 71, -3, -1], ![-1063, -1077, -739, 823, -13, -59]], ![![0, -1, 0, 1, 0, 0], ![0, 2, 1, -2, 1, -2], ![2, 2, 2, -3, 0, -1], ![-1, 1, 1, 0, 1, -2], ![2, -1, 1, -1, 0, 1], ![-9, -11, -14, 11, -5, 6]], ![![2, 1, 1, -2, 0, 0], ![-256, -274, -167, 183, 4, -30], ![-370, -392, -260, 275, -5, -30], ![-272, -296, -180, 192, 3, -33], ![-99, -99, -85, 84, -10, 5], ![-1221, -1224, -872, 967, -28, -46]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inr 0, Sum.inr 0), (Sum.inr 1, Sum.inr 0), (Sum.inr 2, Sum.inr 0), (Sum.inr 3, Sum.inr 0), (Sum.inr 4, Sum.inr 0)]
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

noncomputable def bOm : Basis (Fin 7) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 7 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 7
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 7 := T_degree

noncomputable def bQ : Basis (Fin 7) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 7) (Fin 7) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 7) :
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
          (∑ x : Fin 7,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 7,
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
        (List.ofFn fun i : Fin 7 =>
          (List.ofFn fun j : Fin 7 =>
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
      (voightPolynomialDiscriminantInput 7 row row_mem)
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

end VoightMaximalOrderD7R281

namespace VoightMaximalOrderD8R6

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨442050625, [-1, 11, -5, -36, 17, 26, -12, -2, 1], 63⟩
local notation "l" => [-1, 11, -5, -36, 17, 26, -12, -2, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsEight := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsEight_irreducible row row_mem
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

def basisDenominator : ℤ := 21
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![21, 0, 0, 0, 0, 0, 0, 0], ![0, 21, 0, 0, 0, 0, 0, 0], ![0, 0, 21, 0, 0, 0, 0, 0], ![0, 0, 0, 21, 0, 0, 0, 0], ![0, 0, 0, 0, 21, 0, 0, 0], ![0, 0, 0, 0, 0, 21, 0, 0], ![7, 14, 14, 7, 7, 0, 7, 0], ![18, 7, 20, 14, 16, 16, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![-1, -2, -2, -1, -1, 0, 3, 0], ![-6, -2, -6, -4, -5, -5, 0, 7], ![-3, -3, -4, 0, -3, -2, 4, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![-1, -2, -2, -1, -1, 0, 3, 0], ![-18, -7, -20, -14, -16, -16, 0, 21], ![-16, -17, -20, -1, -20, -19, 13, 14], ![-28, -13, -31, -18, -24, -27, 2, 32]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![-1, -2, -2, -1, -1, 0, 3, 0], ![-18, -7, -20, -14, -16, -16, 0, 21], ![-47, -49, -59, -4, -61, -58, 36, 42], ![-101, -46, -113, -53, -89, -113, -1, 119], ![-81, -74, -99, -12, -97, -98, 47, 78]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![-1, -2, -2, -1, -1, 0, 3, 0], ![-18, -7, -20, -14, -16, -16, 0, 21], ![-47, -49, -59, -4, -61, -58, 36, 42], ![-284, -129, -317, -145, -252, -325, -6, 336], ![-238, -230, -290, 4, -292, -322, 137, 231], ![-418, -213, -472, -189, -383, -488, 18, 485]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![-1, -2, -2, -1, -1, 0, 3, 0], ![-18, -7, -20, -14, -16, -16, 0, 21], ![-47, -49, -59, -4, -61, -58, 36, 42], ![-284, -129, -317, -145, -252, -325, -6, 336], ![-647, -630, -787, 32, -798, -894, 369, 630], ![-1193, -561, -1332, -516, -1052, -1439, -42, 1421], ![-1075, -933, -1285, -56, -1246, -1443, 476, 1096]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-6, -2, -6, -4, -5, -5, 0, 7], ![-16, -17, -20, -1, -20, -19, 13, 14], ![-101, -46, -113, -53, -89, -113, -1, 119], ![-238, -230, -290, 4, -292, -322, 137, 231], ![-1193, -561, -1332, -516, -1052, -1439, -42, 1421], ![-985, -936, -1190, 72, -1187, -1389, 510, 980], ![-1754, -916, -1976, -661, -1605, -2154, 44, 2052]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-3, -3, -4, 0, -3, -2, 4, 2], ![-28, -13, -31, -18, -24, -27, 2, 32], ![-81, -74, -99, -12, -97, -98, 47, 78], ![-418, -213, -472, -189, -383, -488, 18, 485], ![-1075, -933, -1285, -56, -1246, -1443, 476, 1096], ![-1754, -916, -1976, -661, -1605, -2154, 44, 2052], ![-1747, -1400, -2065, -197, -1938, -2306, 632, 1833]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-21]], ![[], [], [], [], [], [], [-147], [-42, -21]], ![[], [], [], [], [], [-441], [-294, -147], [-672, -42, -21]], ![[], [], [], [], [-441], [-882, -441], [-2499, -294, -147], [-1638, -672, -42, -21]], ![[], [], [], [-441], [-882, -441], [-7056, -882, -441], [-4851, -2499, -294, -147], [-10185, -1638, -672, -42, -21]], ![[], [], [-147], [-294, -147], [-2499, -294, -147], [-4851, -2499, -294, -147], [-10976, -1764, -882, -98, -49], [-8484, -3647, -567, -231, -14, -7]], ![[], [-21], [-42, -21], [-672, -42, -21], [-1638, -672, -42, -21], [-10185, -1638, -672, -42, -21], [-8484, -3647, -567, -231, -14, -7], [-15027, -2904, -1043, -126, -48, -2, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 8 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 8) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 8) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 8) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [-1, -2, -2, -1, -1, 0, 3, 0], [-6, -2, -6, -4, -5, -5, 0, 7], [-3, -3, -4, 0, -3, -2, 4, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [-1, -2, -2, -1, -1, 0, 3, 0], [-18, -7, -20, -14, -16, -16, 0, 21], [-16, -17, -20, -1, -20, -19, 13, 14], [-28, -13, -31, -18, -24, -27, 2, 32]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [-1, -2, -2, -1, -1, 0, 3, 0], [-18, -7, -20, -14, -16, -16, 0, 21], [-47, -49, -59, -4, -61, -58, 36, 42], [-101, -46, -113, -53, -89, -113, -1, 119], [-81, -74, -99, -12, -97, -98, 47, 78]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [-1, -2, -2, -1, -1, 0, 3, 0], [-18, -7, -20, -14, -16, -16, 0, 21], [-47, -49, -59, -4, -61, -58, 36, 42], [-284, -129, -317, -145, -252, -325, -6, 336], [-238, -230, -290, 4, -292, -322, 137, 231], [-418, -213, -472, -189, -383, -488, 18, 485]], ![[0, 0, 0, 0, 0, 1, 0, 0], [-1, -2, -2, -1, -1, 0, 3, 0], [-18, -7, -20, -14, -16, -16, 0, 21], [-47, -49, -59, -4, -61, -58, 36, 42], [-284, -129, -317, -145, -252, -325, -6, 336], [-647, -630, -787, 32, -798, -894, 369, 630], [-1193, -561, -1332, -516, -1052, -1439, -42, 1421], [-1075, -933, -1285, -56, -1246, -1443, 476, 1096]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-6, -2, -6, -4, -5, -5, 0, 7], [-16, -17, -20, -1, -20, -19, 13, 14], [-101, -46, -113, -53, -89, -113, -1, 119], [-238, -230, -290, 4, -292, -322, 137, 231], [-1193, -561, -1332, -516, -1052, -1439, -42, 1421], [-985, -936, -1190, 72, -1187, -1389, 510, 980], [-1754, -916, -1976, -661, -1605, -2154, 44, 2052]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-3, -3, -4, 0, -3, -2, 4, 2], [-28, -13, -31, -18, -24, -27, 2, 32], [-81, -74, -99, -12, -97, -98, 47, 78], [-418, -213, -472, -189, -383, -488, 18, 485], [-1075, -933, -1285, -56, -1246, -1443, 476, 1096], [-1754, -916, -1976, -661, -1605, -2154, 44, 2052], [-1747, -1400, -2065, -197, -1938, -2306, 632, 1833]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1]
  b' := [1, 1]
  k := [1]
  f := [1, 1, 5, 12, 4, -2, 6, 2]
  g := [2, 4, 1, 4, 1]
  h := [2, 4, 1, 4, 1]
  a := [2, 1, 2]
  b := [2, 2, 1, 0, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [7, 11, 28]
  b' := [14, 23, 28, 22]
  k := [1]
  f := [5, 17, 22, 36, 43, 16, 28, 2]
  g := [12, 21, 8, 28, 1]
  h := [12, 21, 8, 28, 1]
  a := [19, 8, 1, 20]
  b := [26, 4, 4, 15, 21, 7, 18]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3, 7] where
  n := 4
  p := ![3, 5, 7, 29]
  exp := ![2, 1, 2, 1]
  pdgood := [5, 29]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp5.out
    exact hp7.out
    exact hp29.out
  a := [44328, 131536, -212968, -229392, 203052, 20576, -23872]
  b := [9843, -23422, -55400, 55804, 48290, -34996, -3318, 2984]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29

noncomputable def M3 : MaximalOrderCertificateOfUnramifiedLists 3 O Om hm where
  n := 8
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [2, 1, 1, 2, 2, 0, 0, 0], [0, 1, 0, 2, 1, 1, 0, 1], [0, 0, 2, 0, 0, 1, 1, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [2, 1, 1, 2, 2, 0, 0, 0], [0, 2, 1, 1, 2, 2, 0, 0], [2, 1, 1, 2, 1, 2, 1, 2], [2, 2, 2, 0, 0, 0, 2, 2]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [2, 1, 1, 2, 2, 0, 0, 0], [0, 2, 1, 1, 2, 2, 0, 0], [1, 2, 1, 2, 2, 2, 0, 0], [1, 2, 1, 1, 1, 1, 2, 2], [0, 1, 0, 0, 2, 1, 2, 0]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [2, 1, 1, 2, 2, 0, 0, 0], [0, 2, 1, 1, 2, 2, 0, 0], [1, 2, 1, 2, 2, 2, 0, 0], [1, 0, 1, 2, 0, 2, 0, 0], [2, 1, 1, 1, 2, 2, 2, 0], [2, 0, 2, 0, 1, 1, 0, 2]], ![[0, 0, 0, 0, 0, 1, 0, 0], [2, 1, 1, 2, 2, 0, 0, 0], [0, 2, 1, 1, 2, 2, 0, 0], [1, 2, 1, 2, 2, 2, 0, 0], [1, 0, 1, 2, 0, 2, 0, 0], [1, 0, 2, 2, 0, 0, 0, 0], [1, 0, 0, 0, 1, 1, 0, 2], [2, 0, 2, 1, 2, 0, 2, 1]], ![[0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 2, 1, 1, 0, 1], [2, 1, 1, 2, 1, 2, 1, 2], [1, 2, 1, 1, 1, 1, 2, 2], [2, 1, 1, 1, 2, 2, 2, 0], [1, 0, 0, 0, 1, 1, 0, 2], [2, 0, 1, 0, 1, 0, 0, 2], [1, 2, 1, 2, 0, 0, 2, 0]], ![[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 2, 0, 0, 1, 1, 2], [2, 2, 2, 0, 0, 0, 2, 2], [0, 1, 0, 0, 2, 1, 2, 0], [2, 0, 2, 0, 1, 1, 0, 2], [2, 0, 2, 1, 2, 0, 2, 1], [1, 2, 1, 2, 0, 0, 2, 0], [2, 1, 2, 1, 0, 1, 2, 0]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 2, 0, 2, 0, 0], ![0, 1, 2, 1, 0, 2, 0, 0], ![0, 2, 2, 0, 0, 1, 0, 0], ![0, 2, 2, 2, 1, 1, 0, 0], ![1, 1, 0, 1, 0, 1, 0, 0], ![0, 0, 2, 2, 0, 0, 2, 0], ![1, 2, 1, 1, 2, 1, 0, 2]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5, 6, 7]
  hindw := by decide
  hwFrobComp := by decide

noncomputable def M7 : MaximalOrderCertificateOfUnramifiedLists 7 O Om hm where
  n := 8
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [6, 5, 5, 6, 6, 0, 3, 0], [1, 5, 1, 3, 2, 2, 0, 0], [4, 4, 3, 0, 4, 5, 4, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [6, 5, 5, 6, 6, 0, 3, 0], [3, 0, 1, 0, 5, 5, 0, 0], [5, 4, 1, 6, 1, 2, 6, 0], [0, 1, 4, 3, 4, 1, 2, 4]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [6, 5, 5, 6, 6, 0, 3, 0], [3, 0, 1, 0, 5, 5, 0, 0], [2, 0, 4, 3, 2, 5, 1, 0], [4, 3, 6, 3, 2, 6, 6, 0], [3, 3, 6, 2, 1, 0, 5, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [6, 5, 5, 6, 6, 0, 3, 0], [3, 0, 1, 0, 5, 5, 0, 0], [2, 0, 4, 3, 2, 5, 1, 0], [3, 4, 5, 2, 0, 4, 1, 0], [0, 1, 4, 4, 2, 0, 4, 0], [2, 4, 4, 0, 2, 2, 4, 2]], ![[0, 0, 0, 0, 0, 1, 0, 0], [6, 5, 5, 6, 6, 0, 3, 0], [3, 0, 1, 0, 5, 5, 0, 0], [2, 0, 4, 3, 2, 5, 1, 0], [3, 4, 5, 2, 0, 4, 1, 0], [4, 0, 4, 4, 0, 2, 5, 0], [4, 6, 5, 2, 5, 3, 0, 0], [3, 5, 3, 0, 0, 6, 0, 4]], ![[0, 0, 0, 0, 0, 0, 1, 0], [1, 5, 1, 3, 2, 2, 0, 0], [5, 4, 1, 6, 1, 2, 6, 0], [4, 3, 6, 3, 2, 6, 6, 0], [0, 1, 4, 4, 2, 0, 4, 0], [4, 6, 5, 2, 5, 3, 0, 0], [2, 2, 0, 2, 3, 4, 6, 0], [3, 1, 5, 4, 5, 2, 2, 1]], ![[0, 0, 0, 0, 0, 0, 0, 1], [4, 4, 3, 0, 4, 5, 4, 2], [0, 1, 4, 3, 4, 1, 2, 4], [3, 3, 6, 2, 1, 0, 5, 1], [2, 4, 4, 0, 2, 2, 4, 2], [3, 5, 3, 0, 0, 6, 0, 4], [3, 1, 5, 4, 5, 2, 2, 1], [3, 0, 0, 6, 1, 4, 2, 6]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5, 6, 7]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [3, 7]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 3 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M3
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 7 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M7
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [3, 7] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 8) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 8 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 8
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 8 := T_degree

noncomputable def bQ : Basis (Fin 8) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 8) (Fin 8) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 8) :
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
          (∑ x : Fin 8,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 8,
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
        (List.ofFn fun i : Fin 8 =>
          (List.ofFn fun j : Fin 8 =>
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
      (voightPolynomialDiscriminantInput 8 row row_mem)
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

end VoightMaximalOrderD8R6

namespace VoightMaximalOrderD8R15

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨740605625, [1, 4, -14, -12, 21, 8, -9, -1, 1], 23⟩
local notation "l" => [1, 4, -14, -12, 21, 8, -9, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsEight := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsEight_irreducible row row_mem
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

def basisDenominator : ℤ := 23
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![23, 0, 0, 0, 0, 0, 0, 0], ![0, 23, 0, 0, 0, 0, 0, 0], ![0, 0, 23, 0, 0, 0, 0, 0], ![0, 0, 0, 23, 0, 0, 0, 0], ![0, 0, 0, 0, 23, 0, 0, 0], ![0, 0, 0, 0, 0, 23, 0, 0], ![0, 0, 0, 0, 0, 0, 23, 0], ![2, 4, 10, 2, 15, 9, 10, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -4, -10, -2, -15, -9, -10, 23], ![-1, -2, -4, 0, -8, -4, -4, 11]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -4, -10, -2, -15, -9, -10, 23], ![-3, -8, 4, 10, -36, -17, -1, 23], ![-3, -7, -6, 4, -28, -16, -8, 29]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -4, -10, -2, -15, -9, -10, 23], ![-3, -8, 4, 10, -36, -17, -1, 23], ![-21, -45, -90, 6, -159, -119, -99, 230], ![-13, -29, -43, 10, -108, -72, -52, 135]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -4, -10, -2, -15, -9, -10, 23], ![-3, -8, 4, 10, -36, -17, -1, 23], ![-21, -45, -90, 6, -159, -119, -99, 230], ![-32, -85, 25, 108, -349, -188, -49, 253], ![-31, -75, -49, 61, -290, -180, -92, 289]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -4, -10, -2, -15, -9, -10, 23], ![-3, -8, 4, 10, -36, -17, -1, 23], ![-21, -45, -90, 6, -159, -119, -99, 230], ![-32, -85, 25, 108, -349, -188, -49, 253], ![-155, -342, -607, 123, -1181, -920, -710, 1656], ![-105, -241, -311, 135, -871, -618, -416, 1063]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -4, -10, -2, -15, -9, -10, 23], ![-3, -8, 4, 10, -36, -17, -1, 23], ![-21, -45, -90, 6, -159, -119, -99, 230], ![-32, -85, 25, 108, -349, -188, -49, 253], ![-155, -342, -607, 123, -1181, -920, -710, 1656], ![-236, -627, 134, 813, -2475, -1415, -444, 1886], ![-231, -567, -333, 521, -2129, -1379, -710, 2125]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, -4, 0, -8, -4, -4, 11], ![-3, -7, -6, 4, -28, -16, -8, 29], ![-13, -29, -43, 10, -108, -72, -52, 135], ![-31, -75, -49, 61, -290, -180, -92, 289], ![-105, -241, -311, 135, -871, -618, -416, 1063], ![-231, -567, -333, 521, -2129, -1379, -710, 2125], ![-195, -467, -391, 369, -1732, -1157, -661, 1861]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-23]], ![[], [], [], [], [], [], [-529], [-253, -23]], ![[], [], [], [], [], [-529], [-529, -529], [-667, -253, -23]], ![[], [], [], [], [-529], [-529, -529], [-5290, -529, -529], [-3105, -667, -253, -23]], ![[], [], [], [-529], [-529, -529], [-5290, -529, -529], [-5819, -5290, -529, -529], [-6647, -3105, -667, -253, -23]], ![[], [], [-529], [-529, -529], [-5290, -529, -529], [-5819, -5290, -529, -529], [-38088, -5819, -5290, -529, -529], [-24449, -6647, -3105, -667, -253, -23]], ![[], [-23], [-253, -23], [-667, -253, -23], [-3105, -667, -253, -23], [-6647, -3105, -667, -253, -23], [-24449, -6647, -3105, -667, -253, -23], [-17553, -5635, -2067, -539, -148, -21, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 8 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 8) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 8) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 8) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-2, -4, -10, -2, -15, -9, -10, 23], [-1, -2, -4, 0, -8, -4, -4, 11]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-2, -4, -10, -2, -15, -9, -10, 23], [-3, -8, 4, 10, -36, -17, -1, 23], [-3, -7, -6, 4, -28, -16, -8, 29]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-2, -4, -10, -2, -15, -9, -10, 23], [-3, -8, 4, 10, -36, -17, -1, 23], [-21, -45, -90, 6, -159, -119, -99, 230], [-13, -29, -43, 10, -108, -72, -52, 135]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-2, -4, -10, -2, -15, -9, -10, 23], [-3, -8, 4, 10, -36, -17, -1, 23], [-21, -45, -90, 6, -159, -119, -99, 230], [-32, -85, 25, 108, -349, -188, -49, 253], [-31, -75, -49, 61, -290, -180, -92, 289]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-2, -4, -10, -2, -15, -9, -10, 23], [-3, -8, 4, 10, -36, -17, -1, 23], [-21, -45, -90, 6, -159, -119, -99, 230], [-32, -85, 25, 108, -349, -188, -49, 253], [-155, -342, -607, 123, -1181, -920, -710, 1656], [-105, -241, -311, 135, -871, -618, -416, 1063]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-2, -4, -10, -2, -15, -9, -10, 23], [-3, -8, 4, 10, -36, -17, -1, 23], [-21, -45, -90, 6, -159, -119, -99, 230], [-32, -85, 25, 108, -349, -188, -49, 253], [-155, -342, -607, 123, -1181, -920, -710, 1656], [-236, -627, 134, 813, -2475, -1415, -444, 1886], [-231, -567, -333, 521, -2129, -1379, -710, 2125]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, -4, 0, -8, -4, -4, 11], [-3, -7, -6, 4, -28, -16, -8, 29], [-13, -29, -43, 10, -108, -72, -52, 135], [-31, -75, -49, 61, -290, -180, -92, 289], [-105, -241, -311, 135, -871, -618, -416, 1063], [-231, -567, -333, 521, -2129, -1379, -710, 2125], [-195, -467, -391, 369, -1732, -1157, -661, 1861]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp23 : Fact (Nat.Prime 23) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp1409 : Fact (Nat.Prime 1409) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 2, 3]
  b' := [4, 2, 1, 3]
  k := [1]
  f := [0, 0, 4, 4, -2, 0, 3, 1]
  g := [1, 2, 1, 2, 1]
  h := [1, 2, 1, 2, 1]
  a := [0, 4, 4]
  b := [1, 3, 3, 3, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [10, 15, 9, 10, 18]
  b' := [27, 8, 11, 23, 17, 26]
  k := [16, 5, 7, 23, 1]
  f := [3, 6, 21, 30, 23, 17, 8, 1]
  g := [4, 5, 23, 21, 14, 11, 1]
  h := [22, 17, 1]
  a := [21, 5, 11, 9, 5, 8]
  b := [28, 24, 2, 13, 8, 19, 21]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1409 : CertificateDedekindCriterionLists l 1409 where
  n := 2
  a' := [1376, 243, 901, 116, 236, 335]
  b' := [187, 659, 464, 823, 1256, 844, 556]
  k := [123, 1235, 140, 198, 1302, 1128, 1]
  f := [31, 112, 111, 109, 72, 1, 126, 1]
  g := [312, 1125, 1109, 1089, 717, 5, 1268, 1]
  h := [140, 1]
  a := [1125, 620, 750, 819, 879, 338, 813]
  b := [1234, 712, 907, 502, 181, 986, 596]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [23] where
  n := 4
  p := ![5, 23, 29, 1409]
  exp := ![1, 2, 1, 1]
  pdgood := [5, 29, 1409]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp23.out
    exact hp29.out
    exact hp1409.out
  a := [76185621, 123964716, -375469946, -208637740, 289276755, 38908018, -45746096]
  b := [7972931, -51366283, -51255158, 101548546, 42599411, -49043181, -5578285, 5718262]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1409 T_ofList CD1409

noncomputable def M23 : MaximalOrderCertificateOfUnramifiedLists 23 O Om hm where
  n := 8
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [21, 19, 13, 21, 8, 14, 13, 0], [22, 21, 19, 0, 15, 19, 19, 11]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [21, 19, 13, 21, 8, 14, 13, 0], [20, 15, 4, 10, 10, 6, 22, 0], [20, 16, 17, 4, 18, 7, 15, 6]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [21, 19, 13, 21, 8, 14, 13, 0], [20, 15, 4, 10, 10, 6, 22, 0], [2, 1, 2, 6, 2, 19, 16, 0], [10, 17, 3, 10, 7, 20, 17, 20]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [21, 19, 13, 21, 8, 14, 13, 0], [20, 15, 4, 10, 10, 6, 22, 0], [2, 1, 2, 6, 2, 19, 16, 0], [14, 7, 2, 16, 19, 19, 20, 0], [15, 17, 20, 15, 9, 4, 0, 13]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [21, 19, 13, 21, 8, 14, 13, 0], [20, 15, 4, 10, 10, 6, 22, 0], [2, 1, 2, 6, 2, 19, 16, 0], [14, 7, 2, 16, 19, 19, 20, 0], [6, 3, 14, 8, 15, 0, 3, 0], [10, 12, 11, 20, 3, 3, 21, 5]], ![[0, 0, 0, 0, 0, 0, 1, 0], [21, 19, 13, 21, 8, 14, 13, 0], [20, 15, 4, 10, 10, 6, 22, 0], [2, 1, 2, 6, 2, 19, 16, 0], [14, 7, 2, 16, 19, 19, 20, 0], [6, 3, 14, 8, 15, 0, 3, 0], [17, 17, 19, 8, 9, 11, 16, 0], [22, 8, 12, 15, 10, 1, 3, 9]], ![[0, 0, 0, 0, 0, 0, 0, 1], [22, 21, 19, 0, 15, 19, 19, 11], [20, 16, 17, 4, 18, 7, 15, 6], [10, 17, 3, 10, 7, 20, 17, 20], [15, 17, 20, 15, 9, 4, 0, 13], [10, 12, 11, 20, 3, 3, 21, 5], [22, 8, 12, 15, 10, 1, 3, 9], [12, 16, 0, 1, 16, 16, 6, 21]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![4, 18, 5, 20, 7, 8, 11, 0], ![12, 21, 11, 6, 6, 12, 22, 0], ![11, 21, 11, 15, 22, 17, 11, 0], ![9, 8, 11, 17, 16, 22, 15, 0], ![4, 14, 12, 18, 15, 3, 19, 0], ![5, 8, 18, 20, 0, 18, 6, 0], ![10, 4, 11, 22, 15, 17, 1, 22]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5, 6, 7]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [23]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 23 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M23
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [23] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 8) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 8 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 8
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 8 := T_degree

noncomputable def bQ : Basis (Fin 8) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 8) (Fin 8) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 8) :
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
          (∑ x : Fin 8,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 8,
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
        (List.ofFn fun i : Fin 8 =>
          (List.ofFn fun j : Fin 8 =>
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
      (voightPolynomialDiscriminantInput 8 row row_mem)
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

end VoightMaximalOrderD8R15

end TraceEuclidean
