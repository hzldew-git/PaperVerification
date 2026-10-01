import TraceEuclidean.VoightMaximalOrderCertificates.Chunk064
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

namespace VoightMaximalOrderD6R612

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨13515229, [-49, -49, 63, 22, -15, -2, 1], 301⟩
local notation "l" => [-49, -49, 63, 22, -15, -2, 1]
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

def basisDenominator : ℤ := 301
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![301, 0, 0, 0, 0, 0], ![0, 301, 0, 0, 0, 0], ![0, 0, 301, 0, 0, 0], ![0, 0, 0, 301, 0, 0], ![0, 0, 0, 0, 301, 0], ![77, 112, 120, 111, 26, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-77, -112, -120, -111, -26, 301], ![-7, -10, -11, -10, -2, 28]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-77, -112, -120, -111, -26, 301], ![-105, -175, -303, -244, -37, 602], ![-42, -63, -78, -69, -14, 182]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-77, -112, -120, -111, -26, 301], ![-105, -175, -303, -244, -37, 602], ![-1365, -1981, -2357, -2216, -486, 5719], ![-196, -294, -385, -344, -69, 882]], ![![0, 0, 0, 0, 1, 0], ![-77, -112, -120, -111, -26, 301], ![-105, -175, -303, -244, -37, 602], ![-1365, -1981, -2357, -2216, -486, 5719], ![-2611, -4123, -6570, -5601, -1018, 13846], ![-861, -1288, -1716, -1546, -314, 3927]], ![![0, 0, 0, 0, 0, 1], ![-7, -10, -11, -10, -2, 28], ![-42, -63, -78, -69, -14, 182], ![-196, -294, -385, -344, -69, 882], ![-861, -1288, -1716, -1546, -314, 3927], ![-177, -265, -348, -312, -63, 799]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-301]], ![[], [], [], [], [-90601], [-8428, -301]], ![[], [], [], [-90601], [-181202, -90601], [-54782, -8428, -301]], ![[], [], [-90601], [-181202, -90601], [-1721419, -181202, -90601], [-265482, -54782, -8428, -301]], ![[], [-301], [-8428, -301], [-54782, -8428, -301], [-265482, -54782, -8428, -301], [-50533, -8842, -1021, -54, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-77, -112, -120, -111, -26, 301], [-7, -10, -11, -10, -2, 28]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-77, -112, -120, -111, -26, 301], [-105, -175, -303, -244, -37, 602], [-42, -63, -78, -69, -14, 182]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-77, -112, -120, -111, -26, 301], [-105, -175, -303, -244, -37, 602], [-1365, -1981, -2357, -2216, -486, 5719], [-196, -294, -385, -344, -69, 882]], ![[0, 0, 0, 0, 1, 0], [-77, -112, -120, -111, -26, 301], [-105, -175, -303, -244, -37, 602], [-1365, -1981, -2357, -2216, -486, 5719], [-2611, -4123, -6570, -5601, -1018, 13846], [-861, -1288, -1716, -1546, -314, 3927]], ![[0, 0, 0, 0, 0, 1], [-7, -10, -11, -10, -2, 28], [-42, -63, -78, -69, -14, 182], [-196, -294, -385, -344, -69, 882], [-861, -1288, -1716, -1546, -314, 3927], [-177, -265, -348, -312, -63, 799]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp13 : Fact (Nat.Prime 13) := fact_iff.2 (by norm_num)
instance hp43 : Fact (Nat.Prime 43) := fact_iff.2 (by norm_num)
instance hp433 : Fact (Nat.Prime 433) := fact_iff.2 (by norm_num)

def CD13 : CertificateDedekindCriterionLists l 13 where
  n := 2
  a' := [8, 9, 6, 7]
  b' := [7, 4, 5, 2, 9]
  k := [4, 0, 5, 7, 1]
  f := [5, 5, -3, 0, 3, 1]
  g := [8, 4, 10, 6, 9, 1]
  h := [2, 1]
  a := [2, 12, 0, 0, 7]
  b := [7, 4, 2, 3, 6]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD433 : CertificateDedekindCriterionLists l 433 where
  n := 2
  a' := [281, 289, 308, 158]
  b' := [195, 354, 286, 139, 55]
  k := [13, 429, 115, 377, 1]
  f := [22, 22, 5, 21, 26, 1]
  g := [351, 338, 70, 335, 404, 1]
  h := [27, 1]
  a := [17, 385, 223, 60, 155]
  b := [126, 416, 133, 75, 278]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [7, 43] where
  n := 4
  p := ![7, 13, 43, 433]
  exp := ![2, 1, 2, 1]
  pdgood := [13, 433]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp7.out
    exact hp13.out
    exact hp43.out
    exact hp433.out
  a := [-8580524, -5288696, 12819984, 1623360, -2041380]
  b := [-1827497, 9169942, 2554934, -3936644, -383970, 340230]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 13 T_ofList CD13
    exact satisfiesDedekindCriterion_of_certificate_lists T l 433 T_ofList CD433

noncomputable def M7 : MaximalOrderCertificateLists 7 O Om hm where
  m := 4
  n := 2
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 6, 1, 2, 0], [0, 4, 3, 4, 5, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 6, 1, 2, 0], [0, 0, 5, 1, 5, 0], [0, 0, 6, 1, 0, 0]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 6, 1, 2, 0], [0, 0, 5, 1, 5, 0], [0, 0, 2, 3, 4, 0], [0, 0, 0, 6, 1, 0]], ![[0, 0, 0, 0, 1, 0], [0, 0, 6, 1, 2, 0], [0, 0, 5, 1, 5, 0], [0, 0, 2, 3, 4, 0], [0, 0, 3, 6, 4, 0], [0, 0, 6, 1, 1, 0]], ![[0, 0, 0, 0, 0, 1], [0, 4, 3, 4, 5, 0], [0, 0, 6, 1, 0, 0], [0, 0, 0, 6, 1, 0], [0, 0, 6, 1, 1, 0], [5, 1, 2, 3, 0, 1]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 4, 1, 0, 0, 0], ![0, 5, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![3, 3, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0]]
  v := ![![0, 4, 1, 0, 0, 0], ![0, 5, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![3, 3, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 5, 2, 0]]
  v_ind := ![2, 3, 4, 5]
  w_ind := ![0, 2]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![0, 4, 16, 12, 16, 16], ![16, 4, 0, 20, 8, 16], ![16, 20, 4, 16, 20, 24], ![0, 4, 24, 20, 4, 0], ![0, 0, 12, 20, 20, 0]]
  a := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![-15904, -14016, -2856, 37212], ![-59888, -55264, -11916, 143976], ![-168280, -147212, -28276, 369096], ![-45164, -40724, -8352, 105064]], ![![-10584, -9464, -1920, 25172], ![-36736, -33336, -6828, 86184], ![-128768, -115356, -23196, 292040], ![-30436, -27364, -5544, 70584]], ![![-20412, -18116, -3696, 47992], ![-74928, -69188, -14812, 179844], ![-216552, -190232, -36876, 477792], ![-57284, -51708, -10588, 133280]], ![![-5516, -4872, -980, 13244], ![-20748, -18508, -3724, 48160], ![-81648, -73444, -14868, 186620], ![-17836, -15960, -3220, 41440]], ![![-18060, -15932, -3248, 42140], ![-66640, -61572, -13272, 160132], ![-184576, -161476, -31024, 404544], ![-50120, -45192, -9268, 116424]]]
  c := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![-17184, 427], ![-66588, 1636], ![-168936, 7665], ![-48412, 1506]], ![![-11640, 259], ![-39764, 1166], ![-134160, 5151], ![-32508, 1028]], ![![-22164, 546], ![-83152, 2096], ![-218824, 9657], ![-61404, 1922]], ![![-6132, 105], ![-22204, 658], ![-85820, 3129], ![-19092, 576]], ![![-19460, 501], ![-74060, 1844], ![-185136, 8452], ![-53648, 1690]]]
  d := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![112, 84, 112, 112], ![-58576, -53760, -12208, 147392]], ![![0, 140, 56, 112], ![-31696, -29344, -6160, 79968]], ![![28, 112, 140, 168], ![-74032, -68768, -15456, 187376]], ![![168, 140, 28, 0], ![-13328, -11760, -2352, 33712]], ![![84, 140, 140, 0], ![-67200, -61824, -14000, 168560]]]
  e := ![![![1, 0], ![0, 1]], ![![-48, -46], ![-68544, 660]], ![![-32, -38], ![-37184, 380]], ![![-56, -42], ![-87136, 868]], ![![0, -49], ![-15680, 28]], ![![0, -42], ![-78400, 840]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 2, Sum.inl 0), (Sum.inl 3, Sum.inl 0), (Sum.inl 3, Sum.inr 0), (Sum.inl 0, Sum.inr 1)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

noncomputable def M43 : MaximalOrderCertificateOfUnramifiedLists 43 O Om hm where
  n := 6
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [9, 17, 9, 18, 17, 0], [36, 33, 32, 33, 41, 28]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [9, 17, 9, 18, 17, 0], [24, 40, 41, 14, 6, 0], [1, 23, 8, 17, 29, 10]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [9, 17, 9, 18, 17, 0], [24, 40, 41, 14, 6, 0], [11, 40, 8, 20, 30, 0], [19, 7, 2, 0, 17, 22]], ![[0, 0, 0, 0, 1, 0], [9, 17, 9, 18, 17, 0], [24, 40, 41, 14, 6, 0], [11, 40, 8, 20, 30, 0], [12, 5, 9, 32, 14, 0], [42, 2, 4, 2, 30, 14]], ![[0, 0, 0, 0, 0, 1], [36, 33, 32, 33, 41, 28], [1, 23, 8, 17, 29, 10], [19, 7, 2, 0, 17, 22], [42, 2, 4, 2, 30, 14], [38, 36, 39, 32, 23, 25]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![36, 21, 11, 39, 5, 0], ![32, 13, 6, 6, 14, 0], ![39, 36, 37, 11, 9, 0], ![26, 24, 39, 21, 7, 0], ![30, 31, 2, 11, 40, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [7, 43]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 7 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M7
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 43 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M43
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [7, 43] D q hq hbad)
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

end VoightMaximalOrderD6R612

namespace VoightMaximalOrderD6R615

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨13602384, [19, -53, 32, 15, -12, -1, 1], 4⟩
local notation "l" => [19, -53, 32, 15, -12, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-1, 0, -1, 0, 2, 0], ![0, 0, 0, 0, 0, 1], ![-16, 26, -22, -8, 13, 1]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-1, 0, -1, 0, 2, 0], ![0, -1, 0, -1, 0, 2], ![-16, 26, -22, -8, 13, 1], ![-8, 10, 12, -30, -3, 14]], ![![0, 0, 0, 1, 0, 0], ![-1, 0, -1, 0, 2, 0], ![0, -1, 0, -1, 0, 2], ![-31, 52, -44, -16, 24, 2], ![-8, 10, 12, -30, -3, 14], ![-194, 356, -268, -100, 122, 11]], ![![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1], ![-16, 26, -22, -8, 13, 1], ![-8, 10, 12, -30, -3, 14], ![-105, 191, -145, -54, 68, 6], ![-42, 51, 113, -193, -30, 74]], ![![0, 0, 0, 0, 0, 1], ![-16, 26, -22, -8, 13, 1], ![-8, 10, 12, -30, -3, 14], ![-194, 356, -268, -100, 122, 11], ![-42, 51, 113, -193, -30, 74], ![-991, 1882, -1384, -479, 576, 44]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-2]], ![[], [], [], [], [-2], [-2, -2]], ![[], [], [], [-4], [-2, -2], [-28, -2, -2]], ![[], [], [-2], [-2, -2], [-15, -1, -1], [-12, -15, -1, -1]], ![[], [-2], [-2, -2], [-28, -2, -2], [-12, -15, -1, -1], [-148, -12, -15, -1, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [-1, 0, -1, 0, 2, 0], [0, 0, 0, 0, 0, 1], [-16, 26, -22, -8, 13, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [-1, 0, -1, 0, 2, 0], [0, -1, 0, -1, 0, 2], [-16, 26, -22, -8, 13, 1], [-8, 10, 12, -30, -3, 14]], ![[0, 0, 0, 1, 0, 0], [-1, 0, -1, 0, 2, 0], [0, -1, 0, -1, 0, 2], [-31, 52, -44, -16, 24, 2], [-8, 10, 12, -30, -3, 14], [-194, 356, -268, -100, 122, 11]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [-16, 26, -22, -8, 13, 1], [-8, 10, 12, -30, -3, 14], [-105, 191, -145, -54, 68, 6], [-42, 51, 113, -193, -30, 74]], ![[0, 0, 0, 0, 0, 1], [-16, 26, -22, -8, 13, 1], [-8, 10, 12, -30, -3, 14], [-194, 356, -268, -100, 122, 11], [-42, 51, 113, -193, -30, 74], [-991, 1882, -1384, -479, 576, 44]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp23 : Fact (Nat.Prime 23) := fact_iff.2 (by norm_num)
instance hp37 : Fact (Nat.Prime 37) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 2
  a' := [2]
  b' := [0, 1, 2]
  k := [1]
  f := [-5, 19, -9, -3, 5, 1]
  g := [2, 1, 1, 1]
  h := [2, 1, 1, 1]
  a := [0, 1, 1]
  b := [2, 0, 1, 1, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD23 : CertificateDedekindCriterionLists l 23 where
  n := 2
  a' := [1, 4, 15, 10]
  b' := [19, 3, 13, 0, 21]
  k := [21, 21, 7, 9, 1]
  f := [7, 9, 6, 6, 4, 1]
  g := [10, 8, 9, 8, 4, 1]
  h := [18, 1]
  a := [7, 9, 3, 9, 3]
  b := [9, 17, 3, 14, 20]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD37 : CertificateDedekindCriterionLists l 37 where
  n := 2
  a' := [1, 29, 36]
  b' := [4, 23, 19, 28]
  k := [20, 27, 1]
  f := [3, 18, 4, 12, 9, 1]
  g := [26, 3, 17, 13, 1]
  h := [5, 23, 1]
  a := [36, 18, 33, 12]
  b := [3, 31, 31, 15, 25]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 4
  p := ![2, 3, 23, 37]
  exp := ![2, 1, 1, 1]
  pdgood := [3, 23, 37]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp3.out
    exact hp23.out
    exact hp37.out
  a := [-52337, -5046, 37014, -4, -4704]
  b := [-18955, 27639, 3997, -9414, -130, 784]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
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
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 0]], ![[0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0], [1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 0], [1, 1, 1, 0, 0, 0], [0, 1, 1, 1, 0, 0]], ![[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1], [0, 1, 1, 1, 0, 0], [1, 0, 0, 1, 0, 0]]]
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
  g := ![![1, 0, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 0], ![1, 1, 1, 0, 0, 1], ![0, 1, 1, 1, 1, 1], ![1, 1, 1, 0, 0, 0], ![0, 1, 1, 1, 0, 0]]
  a := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![0, 1, 4, 2], ![-43, -15, 24, 4], ![-10, -38, 11, 15], ![-256, -130, 119, 26]], ![![-8, -36, 12, 16], ![-268, -100, 124, 14], ![91, -201, -16, 76], ![-1394, -517, 586, 60]], ![![-32, -44, 28, 20], ![-300, -146, 146, 30], ![-42, -285, 48, 96], ![-1549, -810, 678, 144]], ![![2, 2, 2, 0], ![0, 0, 2, 2], ![-22, -8, 14, 2], ![-10, -38, 10, 16]], ![![0, 2, 4, 2], ![-44, -16, 26, 4], ![-10, -38, 10, 16], ![-278, -138, 132, 26]]]
  c := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![-1, 0], ![14, 47], ![12, 23], ![92, 311]], ![![10, 23], ![87, 312], ![26, -7], ![448, 1656]], ![![17, 47], ![106, 359], ![78, 160], ![554, 1937]], ![![-2, 0], ![0, 0], ![7, 24], ![12, 23]], ![![-2, 0], ![14, 48], ![12, 23], ![99, 335]]]
  d := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2, 2, 0, 0], ![-2, 2, 4, 0]], ![![2, 0, 0, 2], ![-42, -14, 26, 2]], ![![2, 2, 2, 2], ![-44, -14, 30, 4]], ![![2, 0, 0, 0], ![2, 2, 0, 0]], ![![2, 2, 0, 0], ![0, 2, 4, 0]]]
  e := ![![![1, 0], ![0, 1]], ![![-1, -1], ![-1, 2]], ![![0, 0], ![12, 48]], ![![-2, 0], ![12, 48]], ![![0, 0], ![-2, 0]], ![![-2, 0], ![-2, 0]]]
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

end VoightMaximalOrderD6R615

namespace VoightMaximalOrderD6R616

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨13603625, [25, -55, 19, 21, -10, -2, 1], 5⟩
local notation "l" => [25, -55, 19, 21, -10, -2, 1]
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![5, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0], ![0, 0, 5, 0, 0, 0], ![0, 0, 0, 5, 0, 0], ![0, 0, 0, 0, 5, 0], ![0, 4, 1, 0, 3, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, -4, -1, 0, -3, 5], ![-5, 7, -4, -4, -1, 5]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, -4, -1, 0, -3, 5], ![-25, 47, -21, -21, 4, 10], ![-25, 34, -12, -24, -6, 20]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, -4, -1, 0, -3, 5], ![-25, 47, -21, -21, 4, 10], ![-50, 29, 3, -61, -43, 70], ![-100, 139, -40, -92, -26, 70]], ![![0, 0, 0, 0, 1, 0], ![0, -4, -1, 0, -3, 5], ![-25, 47, -21, -21, 4, 10], ![-50, 29, 3, -61, -43, 70], ![-350, 612, -208, -277, -2, 135], ![-350, 494, -115, -320, -84, 220]], ![![0, 0, 0, 0, 0, 1], ![-5, 7, -4, -4, -1, 5], ![-25, 34, -12, -24, -6, 20], ![-100, 139, -40, -92, -26, 70], ![-350, 494, -115, -320, -84, 220], ![-439, 614, -135, -399, -110, 276]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-5]], ![[], [], [], [], [-25], [-25, -5]], ![[], [], [], [-25], [-50, -25], [-100, -25, -5]], ![[], [], [-25], [-50, -25], [-350, -50, -25], [-350, -100, -25, -5]], ![[], [-5], [-25, -5], [-100, -25, -5], [-350, -100, -25, -5], [-439, -131, -35, -8, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, -4, -1, 0, -3, 5], [-5, 7, -4, -4, -1, 5]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, -4, -1, 0, -3, 5], [-25, 47, -21, -21, 4, 10], [-25, 34, -12, -24, -6, 20]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, -4, -1, 0, -3, 5], [-25, 47, -21, -21, 4, 10], [-50, 29, 3, -61, -43, 70], [-100, 139, -40, -92, -26, 70]], ![[0, 0, 0, 0, 1, 0], [0, -4, -1, 0, -3, 5], [-25, 47, -21, -21, 4, 10], [-50, 29, 3, -61, -43, 70], [-350, 612, -208, -277, -2, 135], [-350, 494, -115, -320, -84, 220]], ![[0, 0, 0, 0, 0, 1], [-5, 7, -4, -4, -1, 5], [-25, 34, -12, -24, -6, 20], [-100, 139, -40, -92, -26, 70], [-350, 494, -115, -320, -84, 220], [-439, 614, -135, -399, -110, 276]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp2221 : Fact (Nat.Prime 2221) := fact_iff.2 (by norm_num)

def CD7 : CertificateDedekindCriterionLists l 7 where
  n := 2
  a' := [0, 4, 2]
  b' := [4, 5, 6, 3]
  k := [2, 2, 1]
  f := [-1, 13, 0, -2, 2, 1]
  g := [6, 2, 1, 0, 1]
  h := [3, 5, 1]
  a := [3, 2, 3, 5]
  b := [3, 1, 0, 1, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2221 : CertificateDedekindCriterionLists l 2221 where
  n := 2
  a' := [347, 1265, 2214, 18]
  b' := [825, 909, 1441, 76, 1329]
  k := [2187, 1921, 1737, 1769, 1]
  f := [125, 134, 188, 224, 203, 1]
  g := [1234, 1317, 1850, 2203, 1994, 1]
  h := [225, 1]
  a := [1143, 2180, 768, 1755, 1915]
  b := [93, 1775, 1133, 1007, 306]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [5] where
  n := 3
  p := ![5, 7, 2221]
  exp := ![3, 1, 1]
  pdgood := [7, 2221]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp7.out
    exact hp2221.out
  a := [-3646337, -931992, 3210510, 215550, -460404]
  b := [-1692760, 2053161, 611239, -821520, -61503, 76734]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2221 T_ofList CD2221

noncomputable def M5 : MaximalOrderCertificateLists 5 O Om hm where
  m := 3
  n := 3
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 1, 4, 0, 2, 0], [0, 2, 1, 1, 4, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 1, 4, 0, 2, 0], [0, 2, 4, 4, 4, 0], [0, 4, 3, 1, 4, 0]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 1, 4, 0, 2, 0], [0, 2, 4, 4, 4, 0], [0, 4, 3, 4, 2, 0], [0, 4, 0, 3, 4, 0]], ![[0, 0, 0, 0, 1, 0], [0, 1, 4, 0, 2, 0], [0, 2, 4, 4, 4, 0], [0, 4, 3, 4, 2, 0], [0, 2, 2, 3, 3, 0], [0, 4, 0, 0, 1, 0]], ![[0, 0, 0, 0, 0, 1], [0, 2, 1, 1, 4, 0], [0, 4, 3, 1, 4, 0], [0, 4, 0, 3, 4, 0], [0, 4, 0, 0, 1, 0], [1, 4, 0, 1, 0, 1]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 2, 4, 1, 0, 0], ![0, 2, 1, 0, 1, 0], ![2, 0, 2, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 3, 2, 0, 0, 0], ![0, 1, 0, 0, 0, 0]]
  v := ![![0, 2, 4, 1, 0, 0], ![0, 2, 1, 0, 1, 0], ![2, 0, 2, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 3, 2, 0, 0, 0], ![0, 1, 0, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 3, 1, 0], ![0, 0, 1, 3, 4, 0]]
  v_ind := ![3, 4, 5]
  w_ind := ![0, 1, 2]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![6, 4, 6, 0, 0, 4], ![8, 8, 8, 6, 0, 0], ![6, 0, 2, 2, 8, 8], ![0, 0, 2, 4, 6, 0], ![0, 6, 6, 6, 2, 0]]
  a := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![-750, -198, 670], ![-1518, -344, 1080], ![-1940, -516, 1418]], ![![-70, -20, 220], ![-510, -240, 570], ![-748, -232, 688]], ![![-2760, -690, 2310], ![-5360, -840, 3410], ![-6700, -1640, 4670]], ![![-950, -220, 850], ![-2070, -190, 1250], ![-2580, -580, 1800]], ![![-380, -90, 450], ![-1070, -260, 850], ![-1420, -370, 1110]]]
  c := ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![-436, 150, 158], ![-770, 360, 154], ![-990, 474, 154]], ![![-118, -25, 145], ![-328, 100, 102], ![-440, 150, 168]], ![![-1510, 565, 495], ![-2610, 1250, 670], ![-3338, 1648, 490]], ![![-540, 172, 226], ![-1000, 455, 359], ![-1290, 617, 237]], ![![-270, 40, 184], ![-580, 227, 193], ![-760, 318, 206]]]
  d := ![![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]], ![![0, 0, 20], ![-1070, -240, 1100], ![-50, -20, 100]], ![![30, 0, 0], ![200, -10, 300], ![40, 30, 0]], ![![10, 40, 40], ![-4050, -650, 3700], ![-150, -150, 400]], ![![20, 30, 0], ![-1230, -70, 1250], ![10, -70, 150]], ![![30, 10, 0], ![-270, -40, 650], ![30, 0, 50]]]
  e := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![-2, -1, 7], ![-700, 172, 382], ![-60, -4, 74]], ![![8, -8, 20], ![-120, -125, 275], ![0, -15, 25]], ![![-10, -15, 25], ![-2400, 625, 1375], ![-200, -25, 225]], ![![0, -10, 10], ![-800, 110, 650], ![-60, -30, 90]], ![![0, -10, 20], ![-360, -60, 420], ![-20, -20, 40]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 2, Sum.inl 0), (Sum.inl 2, Sum.inr 0), (Sum.inl 0, Sum.inr 1), (Sum.inl 1, Sum.inr 1)]
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

end VoightMaximalOrderD6R616

namespace VoightMaximalOrderD6R621

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨13695125, [11, -35, 12, 22, -9, -3, 1], 61⟩
local notation "l" => [11, -35, 12, 22, -9, -3, 1]
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

def basisDenominator : ℤ := 61
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![61, 0, 0, 0, 0, 0], ![0, 61, 0, 0, 0, 0], ![0, 0, 61, 0, 0, 0], ![0, 0, 0, 61, 0, 0], ![0, 0, 0, 0, 61, 0], ![60, 53, 37, 18, 8, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-60, -53, -37, -18, -8, 61], ![-11, -8, -6, -3, -1, 11]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-60, -53, -37, -18, -8, 61], ![-191, -124, -123, -76, -15, 183], ![-61, -46, -37, -21, -6, 60]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-60, -53, -37, -18, -8, 61], ![-191, -124, -123, -76, -15, 183], ![-1113, -860, -667, -402, -139, 1098], ![-300, -223, -184, -109, -33, 294]], ![![0, 0, 0, 0, 1, 0], ![-60, -53, -37, -18, -8, 61], ![-191, -124, -123, -76, -15, 183], ![-1113, -860, -667, -402, -139, 1098], ![-3738, -2530, -2305, -1459, -388, 3599], ![-1254, -903, -766, -472, -139, 1221]], ![![0, 0, 0, 0, 0, 1], ![-11, -8, -6, -3, -1, 11], ![-61, -46, -37, -21, -6, 60], ![-300, -223, -184, -109, -33, 294], ![-1254, -903, -766, -472, -139, 1221], ![-383, -279, -233, -141, -42, 375]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-61]], ![[], [], [], [], [-3721], [-671, -61]], ![[], [], [], [-3721], [-11163, -3721], [-3660, -671, -61]], ![[], [], [-3721], [-11163, -3721], [-66978, -11163, -3721], [-17934, -3660, -671, -61]], ![[], [-61], [-671, -61], [-3660, -671, -61], [-17934, -3660, -671, -61], [-5113, -1009, -166, -19, -1]]]
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
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-60, -53, -37, -18, -8, 61], [-11, -8, -6, -3, -1, 11]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-60, -53, -37, -18, -8, 61], [-191, -124, -123, -76, -15, 183], [-61, -46, -37, -21, -6, 60]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-60, -53, -37, -18, -8, 61], [-191, -124, -123, -76, -15, 183], [-1113, -860, -667, -402, -139, 1098], [-300, -223, -184, -109, -33, 294]], ![[0, 0, 0, 0, 1, 0], [-60, -53, -37, -18, -8, 61], [-191, -124, -123, -76, -15, 183], [-1113, -860, -667, -402, -139, 1098], [-3738, -2530, -2305, -1459, -388, 3599], [-1254, -903, -766, -472, -139, 1221]], ![[0, 0, 0, 0, 0, 1], [-11, -8, -6, -3, -1, 11], [-61, -46, -37, -21, -6, 60], [-300, -223, -184, -109, -33, 294], [-1254, -903, -766, -472, -139, 1221], [-383, -279, -233, -141, -42, 375]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp61 : Fact (Nat.Prime 61) := fact_iff.2 (by norm_num)
instance hp331 : Fact (Nat.Prime 331) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 1]
  b' := [2, 4, 3]
  k := [1]
  f := [-2, 7, -2, -4, 2, 1]
  g := [1, 0, 1, 1]
  h := [1, 0, 1, 1]
  a := [0, 3, 2]
  b := [1, 1, 2, 0, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD331 : CertificateDedekindCriterionLists l 331 where
  n := 3
  a' := [107, 4, 278]
  b' := [83, 329, 73, 96]
  k := [191, 137, 213, 292, 12, 95, 1]
  f := [127, 272, 283, 216, 81, 1]
  g := [192, 247, 216, 141, 1]
  h := [219, 187, 1]
  a := [117, 103, 189, 306]
  b := [195, 29, 305, 297, 25]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [61] where
  n := 3
  p := ![5, 61, 331]
  exp := ![1, 2, 1]
  pdgood := [5, 331]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp61.out
    exact hp331.out
  a := [-3056400, -1806678, 3621663, 765360, -500940]
  b := [-1136533, 1709250, 925887, -894663, -169305, 83490]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 331 T_ofList CD331

noncomputable def M61 : MaximalOrderCertificateOfUnramifiedLists 61 O Om hm where
  n := 6
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 8, 24, 43, 53, 0], [50, 53, 55, 58, 60, 11]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 8, 24, 43, 53, 0], [53, 59, 60, 46, 46, 0], [0, 15, 24, 40, 55, 60]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 8, 24, 43, 53, 0], [53, 59, 60, 46, 46, 0], [46, 55, 4, 25, 44, 0], [5, 21, 60, 13, 28, 50]], ![[0, 0, 0, 0, 1, 0], [1, 8, 24, 43, 53, 0], [53, 59, 60, 46, 46, 0], [46, 55, 4, 25, 44, 0], [44, 32, 13, 5, 39, 0], [27, 12, 27, 16, 44, 1]], ![[0, 0, 0, 0, 0, 1], [50, 53, 55, 58, 60, 11], [0, 15, 24, 40, 55, 60], [5, 21, 60, 13, 28, 50], [27, 12, 27, 16, 44, 1], [44, 26, 11, 42, 19, 9]]]
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
  by_cases hbad : q ∈ [61]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 61 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M61
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [61] D q hq hbad)
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

end VoightMaximalOrderD6R621

end TraceEuclidean
