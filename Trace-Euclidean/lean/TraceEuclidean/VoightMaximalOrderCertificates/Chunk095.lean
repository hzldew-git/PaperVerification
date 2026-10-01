import TraceEuclidean.VoightMaximalOrderCertificates.Chunk091
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

namespace VoightMaximalOrderD8R139

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2265893125, [-1, 15, -4, -31, 10, 18, -6, -3, 1], 27⟩
local notation "l" => [-1, 15, -4, -31, 10, 18, -6, -3, 1]
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

def basisDenominator : ℤ := 3
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![3, 0, 0, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0, 0, 0], ![0, 0, 0, 3, 0, 0, 0, 0], ![0, 0, 0, 0, 3, 0, 0, 0], ![1, 2, 1, 2, 1, 1, 0, 0], ![2, 2, 1, 2, 1, 0, 1, 0], ![2, 0, 1, 2, 1, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![-1, -2, -1, -2, -1, 3, 0, 0], ![-1, -1, 0, -1, 0, 1, 1, 0], ![-1, 0, 0, -1, 0, 1, 0, 1], ![0, 3, 4, 16, 0, -17, 6, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![-1, -2, -1, -2, -1, 3, 0, 0], ![-2, -2, -1, -2, -1, 0, 3, 0], ![-2, -2, -1, -2, -1, 2, 1, 1], ![-1, 1, 4, 15, -1, -16, 7, 3], ![11, 26, 15, 63, 16, -62, 1, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![-1, -2, -1, -2, -1, 3, 0, 0], ![-2, -2, -1, -2, -1, 0, 3, 0], ![-2, 0, -1, -2, -1, 0, 0, 3], ![-2, 1, 3, 14, -1, -17, 8, 4], ![10, 26, 14, 63, 16, -63, 2, 16], ![45, 86, 70, 284, 47, -268, 28, 46]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![-1, -2, -1, -2, -1, 3, 0, 0], ![-2, -2, -1, -2, -1, 0, 3, 0], ![-2, 0, -1, -2, -1, 0, 0, 3], ![1, 9, 13, 49, -1, -54, 18, 9], ![10, 29, 18, 78, 15, -80, 7, 20], ![45, 89, 74, 299, 47, -285, 33, 50], ![193, 357, 223, 952, 237, -881, 8, 166]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![-1, -1, 0, -1, 0, 1, 1, 0], ![-2, -2, -1, -2, -1, 2, 1, 1], ![-2, 1, 3, 14, -1, -17, 8, 4], ![10, 29, 18, 78, 15, -80, 7, 20], ![20, 49, 39, 161, 25, -159, 22, 32], ![89, 176, 116, 490, 110, -462, 20, 90], ![310, 553, 390, 1631, 354, -1499, 64, 262]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-1, 0, 0, -1, 0, 1, 0, 1], ![-1, 1, 4, 15, -1, -16, 7, 3], ![10, 26, 14, 63, 16, -63, 2, 16], ![45, 89, 74, 299, 47, -285, 33, 50], ![89, 176, 116, 490, 110, -462, 20, 90], ![252, 451, 324, 1350, 286, -1242, 61, 217], ![816, 1423, 931, 3978, 970, -3613, 43, 638]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 3, 4, 16, 0, -17, 6, 3], ![11, 26, 15, 63, 16, -62, 1, 15], ![45, 86, 70, 284, 47, -268, 28, 46], ![193, 357, 223, 952, 237, -881, 8, 166], ![310, 553, 390, 1631, 354, -1499, 64, 262], ![816, 1423, 931, 3978, 970, -3613, 43, 638], ![2335, 3936, 2685, 11422, 2701, -10275, 179, 1742]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-3]], ![[], [], [], [], [], [], [-3], [-9, -3]], ![[], [], [], [], [], [-3], [-9, -3], [-45, -9, -3]], ![[], [], [], [], [-9], [-12, -3], [-48, -9, -3], [-138, -45, -9, -3]], ![[], [], [], [-3], [-12, -3], [-26, -5, -1], [-73, -21, -4, -1], [-247, -68, -20, -4, -1]], ![[], [], [-3], [-9, -3], [-48, -9, -3], [-73, -21, -4, -1], [-206, -55, -17, -3, -1], [-587, -188, -51, -16, -3, -1]], ![[], [-3], [-9, -3], [-45, -9, -3], [-138, -45, -9, -3], [-247, -68, -20, -4, -1], [-587, -188, -51, -16, -3, -1], [-1712, -528, -171, -47, -15, -3, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [-1, -2, -1, -2, -1, 3, 0, 0], [-1, -1, 0, -1, 0, 1, 1, 0], [-1, 0, 0, -1, 0, 1, 0, 1], [0, 3, 4, 16, 0, -17, 6, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [-1, -2, -1, -2, -1, 3, 0, 0], [-2, -2, -1, -2, -1, 0, 3, 0], [-2, -2, -1, -2, -1, 2, 1, 1], [-1, 1, 4, 15, -1, -16, 7, 3], [11, 26, 15, 63, 16, -62, 1, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [-1, -2, -1, -2, -1, 3, 0, 0], [-2, -2, -1, -2, -1, 0, 3, 0], [-2, 0, -1, -2, -1, 0, 0, 3], [-2, 1, 3, 14, -1, -17, 8, 4], [10, 26, 14, 63, 16, -63, 2, 16], [45, 86, 70, 284, 47, -268, 28, 46]], ![[0, 0, 0, 0, 1, 0, 0, 0], [-1, -2, -1, -2, -1, 3, 0, 0], [-2, -2, -1, -2, -1, 0, 3, 0], [-2, 0, -1, -2, -1, 0, 0, 3], [1, 9, 13, 49, -1, -54, 18, 9], [10, 29, 18, 78, 15, -80, 7, 20], [45, 89, 74, 299, 47, -285, 33, 50], [193, 357, 223, 952, 237, -881, 8, 166]], ![[0, 0, 0, 0, 0, 1, 0, 0], [-1, -1, 0, -1, 0, 1, 1, 0], [-2, -2, -1, -2, -1, 2, 1, 1], [-2, 1, 3, 14, -1, -17, 8, 4], [10, 29, 18, 78, 15, -80, 7, 20], [20, 49, 39, 161, 25, -159, 22, 32], [89, 176, 116, 490, 110, -462, 20, 90], [310, 553, 390, 1631, 354, -1499, 64, 262]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-1, 0, 0, -1, 0, 1, 0, 1], [-1, 1, 4, 15, -1, -16, 7, 3], [10, 26, 14, 63, 16, -63, 2, 16], [45, 89, 74, 299, 47, -285, 33, 50], [89, 176, 116, 490, 110, -462, 20, 90], [252, 451, 324, 1350, 286, -1242, 61, 217], [816, 1423, 931, 3978, 970, -3613, 43, 638]], ![[0, 0, 0, 0, 0, 0, 0, 1], [0, 3, 4, 16, 0, -17, 6, 3], [11, 26, 15, 63, 16, -62, 1, 15], [45, 86, 70, 284, 47, -268, 28, 46], [193, 357, 223, 952, 237, -881, 8, 166], [310, 553, 390, 1631, 354, -1499, 64, 262], [816, 1423, 931, 3978, 970, -3613, 43, 638], [2335, 3936, 2685, 11422, 2701, -10275, 179, 1742]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp3625429 : Fact (Nat.Prime 3625429) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 3, 1]
  b' := [3, 4, 2, 1]
  k := [1]
  f := [1, -3, 4, 7, 2, -2, 3, 1]
  g := [2, 0, 4, 1, 1]
  h := [2, 0, 4, 1, 1]
  a := [3, 0, 2, 1]
  b := [4, 2, 0, 1, 4, 1, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3625429 : CertificateDedekindCriterionLists l 3625429 where
  n := 2
  a' := [869562, 2713634, 781576, 2984070, 435380, 3030942]
  b' := [2070482, 1531742, 446461, 2641730, 2604850, 2517029, 1638682]
  k := [3482736, 2308873, 1503961, 553574, 2862441, 1230003, 1]
  f := [2585865, 466051, 2475352, 1136697, 985699, 281610, 510674, 1]
  g := [3114134, 561260, 2981044, 1368913, 1187068, 339140, 615000, 1]
  h := [3010426, 1]
  a := [576721, 1521577, 669776, 1645094, 1285769, 3175180, 438061]
  b := [531515, 3106038, 973816, 736208, 1416389, 3069590, 3187368]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
  n := 3
  p := ![3, 5, 3625429]
  exp := ![2, 1, 1]
  pdgood := [5, 3625429]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp5.out
    exact hp3625429.out
  a := [65410350, 149437324, -306356234, -308118634, 245759955, 96186998, -48710064]
  b := [15236977, -47321474, -83187175, 82454764, 71021996, -41337987, -14306659, 6088758]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3625429 T_ofList CD3625429

noncomputable def M3 : MaximalOrderCertificateOfUnramifiedLists 3 O Om hm where
  n := 8
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [2, 1, 2, 1, 2, 0, 0, 0], [2, 2, 0, 2, 0, 1, 1, 0], [2, 0, 0, 2, 0, 1, 0, 1], [0, 0, 1, 1, 0, 1, 0, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [2, 1, 2, 1, 2, 0, 0, 0], [1, 1, 2, 1, 2, 0, 0, 0], [1, 1, 2, 1, 2, 2, 1, 1], [2, 1, 1, 0, 2, 2, 1, 0], [2, 2, 0, 0, 1, 1, 1, 0]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [2, 1, 2, 1, 2, 0, 0, 0], [1, 1, 2, 1, 2, 0, 0, 0], [1, 0, 2, 1, 2, 0, 0, 0], [1, 1, 0, 2, 2, 1, 2, 1], [1, 2, 2, 0, 1, 0, 2, 1], [0, 2, 1, 2, 2, 2, 1, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0], [2, 1, 2, 1, 2, 0, 0, 0], [1, 1, 2, 1, 2, 0, 0, 0], [1, 0, 2, 1, 2, 0, 0, 0], [1, 0, 1, 1, 2, 0, 0, 0], [1, 2, 0, 0, 0, 1, 1, 2], [0, 2, 2, 2, 2, 0, 0, 2], [1, 0, 1, 1, 0, 1, 2, 1]], ![[0, 0, 0, 0, 0, 1, 0, 0], [2, 2, 0, 2, 0, 1, 1, 0], [1, 1, 2, 1, 2, 2, 1, 1], [1, 1, 0, 2, 2, 1, 2, 1], [1, 2, 0, 0, 0, 1, 1, 2], [2, 1, 0, 2, 1, 0, 1, 2], [2, 2, 2, 1, 2, 0, 2, 0], [1, 1, 0, 2, 0, 1, 1, 1]], ![[0, 0, 0, 0, 0, 0, 1, 0], [2, 0, 0, 2, 0, 1, 0, 1], [2, 1, 1, 0, 2, 2, 1, 0], [1, 2, 2, 0, 1, 0, 2, 1], [0, 2, 2, 2, 2, 0, 0, 2], [2, 2, 2, 1, 2, 0, 2, 0], [0, 1, 0, 0, 1, 0, 1, 1], [0, 1, 1, 0, 1, 2, 1, 2]], ![[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 1, 0, 1, 0, 0], [2, 2, 0, 0, 1, 1, 1, 0], [0, 2, 1, 2, 2, 2, 1, 1], [1, 0, 1, 1, 0, 1, 2, 1], [1, 1, 0, 2, 0, 1, 1, 1], [0, 1, 1, 0, 1, 2, 1, 2], [1, 0, 0, 1, 1, 0, 2, 2]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![2, 1, 1, 1, 1, 0, 0, 0], ![0, 2, 0, 1, 0, 0, 0, 0], ![2, 2, 0, 0, 1, 0, 0, 0], ![1, 1, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 2, 0, 1, 2, 0], ![1, 1, 0, 1, 2, 0, 1, 0], ![2, 2, 1, 0, 1, 2, 0, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5, 6, 7]
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

end VoightMaximalOrderD8R139

namespace VoightMaximalOrderD8R144

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2349018125, [-19, 55, 1, -68, 16, 26, -8, -3, 1], 23⟩
local notation "l" => [-19, 55, 1, -68, 16, 26, -8, -3, 1]
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
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![23, 0, 0, 0, 0, 0, 0, 0], ![0, 23, 0, 0, 0, 0, 0, 0], ![0, 0, 23, 0, 0, 0, 0, 0], ![0, 0, 0, 23, 0, 0, 0, 0], ![0, 0, 0, 0, 23, 0, 0, 0], ![0, 0, 0, 0, 0, 23, 0, 0], ![0, 0, 0, 0, 0, 0, 23, 0], ![5, 5, 18, 19, 2, 7, 10, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-5, -5, -18, -19, -2, -7, -10, 23], ![-2, -5, -10, -7, -1, -5, -5, 13]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-5, -5, -18, -19, -2, -7, -10, 23], ![4, -70, -55, 11, -22, -47, -22, 69], ![-1, -42, -45, -6, -10, -31, -20, 54]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-5, -5, -18, -19, -2, -7, -10, 23], ![4, -70, -55, 11, -22, -47, -22, 69], ![-28, -231, -364, -120, -14, -213, -172, 391], ![-8, -171, -222, -43, -20, -140, -101, 242]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-5, -5, -18, -19, -2, -7, -10, 23], ![4, -70, -55, 11, -22, -47, -22, 69], ![-28, -231, -364, -120, -14, -213, -172, 391], ![78, -1123, -1045, 167, -167, -765, -448, 1127], ![21, -713, -773, 3, -83, -523, -340, 823]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-5, -5, -18, -19, -2, -7, -10, 23], ![4, -70, -55, 11, -22, -47, -22, 69], ![-28, -231, -364, -120, -14, -213, -172, 391], ![78, -1123, -1045, 167, -167, -765, -448, 1127], ![-14, -3317, -4329, -422, -64, -2666, -1920, 4347], ![54, -2394, -2823, -74, -140, -1818, -1238, 2879]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-5, -5, -18, -19, -2, -7, -10, 23], ![4, -70, -55, 11, -22, -47, -22, 69], ![-28, -231, -364, -120, -14, -213, -172, 391], ![78, -1123, -1045, 167, -167, -765, -448, 1127], ![-14, -3317, -4329, -422, -64, -2666, -1920, 4347], ![906, -12149, -12227, 1722, -929, -8359, -5201, 12351], ![432, -8151, -8900, 546, -477, -5869, -3833, 8953]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-2, -5, -10, -7, -1, -5, -5, 13], ![-1, -42, -45, -6, -10, -31, -20, 54], ![-8, -171, -222, -43, -20, -140, -101, 242], ![21, -713, -773, 3, -83, -523, -340, 823], ![54, -2394, -2823, -74, -140, -1818, -1238, 2879], ![432, -8151, -8900, 546, -477, -5869, -3833, 8953], ![253, -5604, -6264, 228, -314, -4092, -2708, 6313]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-23]], ![[], [], [], [], [], [], [-529], [-299, -23]], ![[], [], [], [], [], [-529], [-1587, -529], [-1242, -299, -23]], ![[], [], [], [], [-529], [-1587, -529], [-8993, -1587, -529], [-5566, -1242, -299, -23]], ![[], [], [], [-529], [-1587, -529], [-8993, -1587, -529], [-25921, -8993, -1587, -529], [-18929, -5566, -1242, -299, -23]], ![[], [], [-529], [-1587, -529], [-8993, -1587, -529], [-25921, -8993, -1587, -529], [-99981, -25921, -8993, -1587, -529], [-66217, -18929, -5566, -1242, -299, -23]], ![[], [-23], [-299, -23], [-1242, -299, -23], [-5566, -1242, -299, -23], [-18929, -5566, -1242, -299, -23], [-66217, -18929, -5566, -1242, -299, -23], [-45253, -13176, -3666, -875, -191, -23, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-5, -5, -18, -19, -2, -7, -10, 23], [-2, -5, -10, -7, -1, -5, -5, 13]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-5, -5, -18, -19, -2, -7, -10, 23], [4, -70, -55, 11, -22, -47, -22, 69], [-1, -42, -45, -6, -10, -31, -20, 54]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-5, -5, -18, -19, -2, -7, -10, 23], [4, -70, -55, 11, -22, -47, -22, 69], [-28, -231, -364, -120, -14, -213, -172, 391], [-8, -171, -222, -43, -20, -140, -101, 242]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-5, -5, -18, -19, -2, -7, -10, 23], [4, -70, -55, 11, -22, -47, -22, 69], [-28, -231, -364, -120, -14, -213, -172, 391], [78, -1123, -1045, 167, -167, -765, -448, 1127], [21, -713, -773, 3, -83, -523, -340, 823]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-5, -5, -18, -19, -2, -7, -10, 23], [4, -70, -55, 11, -22, -47, -22, 69], [-28, -231, -364, -120, -14, -213, -172, 391], [78, -1123, -1045, 167, -167, -765, -448, 1127], [-14, -3317, -4329, -422, -64, -2666, -1920, 4347], [54, -2394, -2823, -74, -140, -1818, -1238, 2879]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-5, -5, -18, -19, -2, -7, -10, 23], [4, -70, -55, 11, -22, -47, -22, 69], [-28, -231, -364, -120, -14, -213, -172, 391], [78, -1123, -1045, 167, -167, -765, -448, 1127], [-14, -3317, -4329, -422, -64, -2666, -1920, 4347], [906, -12149, -12227, 1722, -929, -8359, -5201, 12351], [432, -8151, -8900, 546, -477, -5869, -3833, 8953]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-2, -5, -10, -7, -1, -5, -5, 13], [-1, -42, -45, -6, -10, -31, -20, 54], [-8, -171, -222, -43, -20, -140, -101, 242], [21, -713, -773, 3, -83, -523, -340, 823], [54, -2394, -2823, -74, -140, -1818, -1238, 2879], [432, -8151, -8900, 546, -477, -5869, -3833, 8953], [253, -5604, -6264, 228, -314, -4092, -2708, 6313]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp23 : Fact (Nat.Prime 23) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp41 : Fact (Nat.Prime 41) := fact_iff.2 (by norm_num)
instance hp109 : Fact (Nat.Prime 109) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 0, 3]
  b' := [0, 4, 2, 3]
  k := [1]
  f := [4, -11, 1, 14, -1, -4, 3, 1]
  g := [1, 0, 3, 1, 1]
  h := [1, 0, 3, 1, 1]
  a := [2, 0, 2, 2]
  b := [3, 2, 1, 2, 4, 4, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [23, 1, 23, 10, 28]
  b' := [7, 15, 4, 8, 6, 5]
  k := [2, 15, 8, 4, 1]
  f := [5, 2, 14, 11, 8, 13, 7, 1]
  g := [7, 2, 21, 1, 12, 15, 1]
  h := [18, 11, 1]
  a := [12, 24, 18, 24, 0, 25]
  b := [4, 28, 15, 25, 25, 26, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD41 : CertificateDedekindCriterionLists l 41 where
  n := 2
  a' := [34, 26, 18, 21, 2, 16]
  b' := [34, 19, 33, 10, 20, 6, 27]
  k := [12, 26, 40, 0, 13, 26, 1]
  f := [5, 0, 3, 8, 6, 1, 5, 1]
  g := [31, 4, 20, 40, 37, 5, 32, 1]
  h := [6, 1]
  a := [21, 10, 8, 40, 35, 31, 7]
  b := [35, 19, 10, 25, 30, 35, 34]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD109 : CertificateDedekindCriterionLists l 109 where
  n := 2
  a' := [5, 15, 95, 65, 52, 71]
  b' := [28, 43, 78, 72, 55, 46, 21]
  k := [14, 100, 102, 65, 11, 49, 1]
  f := [55, 23, 49, 37, 81, 35, 18, 1]
  g := [72, 30, 64, 47, 106, 45, 23, 1]
  h := [83, 1]
  a := [86, 29, 79, 16, 28, 90, 73]
  b := [63, 74, 0, 96, 60, 57, 36]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [23] where
  n := 5
  p := ![5, 23, 29, 41, 109]
  exp := ![1, 2, 1, 1, 1]
  pdgood := [5, 29, 41, 109]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp23.out
    exact hp29.out
    exact hp41.out
    exact hp109.out
  a := [310984995, 407547590, -910272866, -701927170, 679930412, 172018348, -110560992]
  b := [113663810, -174329057, -299731119, 276903168, 179167836, -118172374, -26684840, 13820124]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
    exact satisfiesDedekindCriterion_of_certificate_lists T l 41 T_ofList CD41
    exact satisfiesDedekindCriterion_of_certificate_lists T l 109 T_ofList CD109

noncomputable def M23 : MaximalOrderCertificateOfUnramifiedLists 23 O Om hm where
  n := 8
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [18, 18, 5, 4, 21, 16, 13, 0], [21, 18, 13, 16, 22, 18, 18, 13]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [18, 18, 5, 4, 21, 16, 13, 0], [4, 22, 14, 11, 1, 22, 1, 0], [22, 4, 1, 17, 13, 15, 3, 8]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [18, 18, 5, 4, 21, 16, 13, 0], [4, 22, 14, 11, 1, 22, 1, 0], [18, 22, 4, 18, 9, 17, 12, 0], [15, 13, 8, 3, 3, 21, 14, 12]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [18, 18, 5, 4, 21, 16, 13, 0], [4, 22, 14, 11, 1, 22, 1, 0], [18, 22, 4, 18, 9, 17, 12, 0], [9, 4, 13, 6, 17, 17, 12, 0], [21, 0, 9, 3, 9, 6, 5, 18]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [18, 18, 5, 4, 21, 16, 13, 0], [4, 22, 14, 11, 1, 22, 1, 0], [18, 22, 4, 18, 9, 17, 12, 0], [9, 4, 13, 6, 17, 17, 12, 0], [9, 18, 18, 15, 5, 2, 12, 0], [8, 21, 6, 18, 21, 22, 4, 4]], ![[0, 0, 0, 0, 0, 0, 1, 0], [18, 18, 5, 4, 21, 16, 13, 0], [4, 22, 14, 11, 1, 22, 1, 0], [18, 22, 4, 18, 9, 17, 12, 0], [9, 4, 13, 6, 17, 17, 12, 0], [9, 18, 18, 15, 5, 2, 12, 0], [9, 18, 9, 20, 14, 13, 20, 0], [18, 14, 1, 17, 6, 19, 8, 6]], ![[0, 0, 0, 0, 0, 0, 0, 1], [21, 18, 13, 16, 22, 18, 18, 13], [22, 4, 1, 17, 13, 15, 3, 8], [15, 13, 8, 3, 3, 21, 14, 12], [21, 0, 9, 3, 9, 6, 5, 18], [8, 21, 6, 18, 21, 22, 4, 4], [18, 14, 1, 17, 6, 19, 8, 6], [0, 8, 15, 21, 8, 2, 6, 11]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![10, 12, 22, 15, 19, 15, 13, 0], ![1, 20, 3, 18, 0, 13, 5, 0], ![20, 17, 7, 22, 0, 8, 22, 0], ![20, 12, 13, 18, 0, 22, 13, 0], ![9, 5, 0, 13, 11, 12, 21, 0], ![22, 5, 19, 12, 18, 19, 20, 0], ![1, 18, 3, 17, 19, 14, 4, 22]]
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

end VoightMaximalOrderD8R144

namespace VoightMaximalOrderD8R145

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2349018125, [1, -1, -36, -16, 35, 9, -11, -1, 1], 83⟩
local notation "l" => [1, -1, -36, -16, 35, 9, -11, -1, 1]
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

def basisDenominator : ℤ := 83
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![83, 0, 0, 0, 0, 0, 0, 0], ![0, 83, 0, 0, 0, 0, 0, 0], ![0, 0, 83, 0, 0, 0, 0, 0], ![0, 0, 0, 83, 0, 0, 0, 0], ![0, 0, 0, 0, 83, 0, 0, 0], ![0, 0, 0, 0, 0, 83, 0, 0], ![0, 0, 0, 0, 0, 0, 83, 0], ![26, 45, 52, 58, 66, 12, 66, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-26, -45, -52, -58, -66, -12, -66, 83], ![-21, -36, -41, -46, -53, -9, -53, 67]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-26, -45, -52, -58, -66, -12, -66, 83], ![-27, -44, -16, -42, -101, -21, -55, 83], ![-29, -48, -27, -49, -99, -20, -62, 90]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-26, -45, -52, -58, -66, -12, -66, 83], ![-27, -44, -16, -42, -101, -21, -55, 83], ![-313, -540, -587, -644, -811, -188, -790, 996], ![-278, -479, -514, -571, -727, -165, -698, 884]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-26, -45, -52, -58, -66, -12, -66, 83], ![-27, -44, -16, -42, -101, -21, -55, 83], ![-313, -540, -587, -644, -811, -188, -790, 996], ![-376, -619, -296, -583, -1292, -295, -836, 1162], ![-416, -692, -427, -694, -1355, -307, -949, 1294]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-26, -45, -52, -58, -66, -12, -66, 83], ![-27, -44, -16, -42, -101, -21, -55, 83], ![-313, -540, -587, -644, -811, -188, -790, 996], ![-376, -619, -296, -583, -1292, -295, -836, 1162], ![-2666, -4588, -4789, -5260, -6993, -1718, -6705, 8466], ![-2500, -4295, -4398, -4909, -6642, -1613, -6255, 7931]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-26, -45, -52, -58, -66, -12, -66, 83], ![-27, -44, -16, -42, -101, -21, -55, 83], ![-313, -540, -587, -644, -811, -188, -790, 996], ![-376, -619, -296, -583, -1292, -295, -836, 1162], ![-2666, -4588, -4789, -5260, -6993, -1718, -6705, 8466], ![-3456, -5717, -3034, -5335, -11428, -2727, -7886, 10707], ![-3921, -6541, -4206, -6434, -12422, -2961, -9126, 12212]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-21, -36, -41, -46, -53, -9, -53, 67], ![-29, -48, -27, -49, -99, -20, -62, 90], ![-278, -479, -514, -571, -727, -165, -698, 884], ![-416, -692, -427, -694, -1355, -307, -949, 1294], ![-2500, -4295, -4398, -4909, -6642, -1613, -6255, 7931], ![-3921, -6541, -4206, -6434, -12422, -2961, -9126, 12212], ![-4265, -7153, -5112, -7274, -13133, -3119, -10048, 13329]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-83]], ![[], [], [], [], [], [], [-6889], [-5561, -83]], ![[], [], [], [], [], [-6889], [-6889, -6889], [-7470, -5561, -83]], ![[], [], [], [], [-6889], [-6889, -6889], [-82668, -6889, -6889], [-73372, -7470, -5561, -83]], ![[], [], [], [-6889], [-6889, -6889], [-82668, -6889, -6889], [-96446, -82668, -6889, -6889], [-107402, -73372, -7470, -5561, -83]], ![[], [], [-6889], [-6889, -6889], [-82668, -6889, -6889], [-96446, -82668, -6889, -6889], [-702678, -96446, -82668, -6889, -6889], [-658273, -107402, -73372, -7470, -5561, -83]], ![[], [-83], [-5561, -83], [-7470, -5561, -83], [-73372, -7470, -5561, -83], [-107402, -73372, -7470, -5561, -83], [-658273, -107402, -73372, -7470, -5561, -83], [-618279, -113821, -65198, -7694, -4524, -133, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-26, -45, -52, -58, -66, -12, -66, 83], [-21, -36, -41, -46, -53, -9, -53, 67]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-26, -45, -52, -58, -66, -12, -66, 83], [-27, -44, -16, -42, -101, -21, -55, 83], [-29, -48, -27, -49, -99, -20, -62, 90]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-26, -45, -52, -58, -66, -12, -66, 83], [-27, -44, -16, -42, -101, -21, -55, 83], [-313, -540, -587, -644, -811, -188, -790, 996], [-278, -479, -514, -571, -727, -165, -698, 884]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-26, -45, -52, -58, -66, -12, -66, 83], [-27, -44, -16, -42, -101, -21, -55, 83], [-313, -540, -587, -644, -811, -188, -790, 996], [-376, -619, -296, -583, -1292, -295, -836, 1162], [-416, -692, -427, -694, -1355, -307, -949, 1294]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-26, -45, -52, -58, -66, -12, -66, 83], [-27, -44, -16, -42, -101, -21, -55, 83], [-313, -540, -587, -644, -811, -188, -790, 996], [-376, -619, -296, -583, -1292, -295, -836, 1162], [-2666, -4588, -4789, -5260, -6993, -1718, -6705, 8466], [-2500, -4295, -4398, -4909, -6642, -1613, -6255, 7931]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-26, -45, -52, -58, -66, -12, -66, 83], [-27, -44, -16, -42, -101, -21, -55, 83], [-313, -540, -587, -644, -811, -188, -790, 996], [-376, -619, -296, -583, -1292, -295, -836, 1162], [-2666, -4588, -4789, -5260, -6993, -1718, -6705, 8466], [-3456, -5717, -3034, -5335, -11428, -2727, -7886, 10707], [-3921, -6541, -4206, -6434, -12422, -2961, -9126, 12212]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-21, -36, -41, -46, -53, -9, -53, 67], [-29, -48, -27, -49, -99, -20, -62, 90], [-278, -479, -514, -571, -727, -165, -698, 884], [-416, -692, -427, -694, -1355, -307, -949, 1294], [-2500, -4295, -4398, -4909, -6642, -1613, -6255, 7931], [-3921, -6541, -4206, -6434, -12422, -2961, -9126, 12212], [-4265, -7153, -5112, -7274, -13133, -3119, -10048, 13329]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp41 : Fact (Nat.Prime 41) := fact_iff.2 (by norm_num)
instance hp83 : Fact (Nat.Prime 83) := fact_iff.2 (by norm_num)
instance hp109 : Fact (Nat.Prime 109) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 1, 1]
  b' := [4, 4, 4, 1]
  k := [1]
  f := [0, 1, 8, 4, -5, -1, 3, 1]
  g := [1, 2, 0, 2, 1]
  h := [1, 2, 0, 2, 1]
  a := [2, 1, 3, 1]
  b := [1, 1, 1, 2, 4, 1, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [9, 19, 13, 15, 15]
  b' := [17, 16, 6, 8, 16, 12]
  k := [16, 20, 24, 5, 1]
  f := [3, 15, 30, 19, 1, 3, 3, 1]
  g := [4, 15, 20, 0, 2, 2, 1]
  h := [22, 26, 1]
  a := [28, 3, 7, 0, 25, 24]
  b := [1, 5, 18, 23, 28, 9, 5]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD41 : CertificateDedekindCriterionLists l 41 where
  n := 2
  a' := [25, 37, 1, 23, 0, 6]
  b' := [10, 35, 8, 37, 16, 7, 5]
  k := [5, 2, 11, 32, 9, 37, 1]
  f := [15, 5, 22, 11, 13, 2, 10, 1]
  g := [28, 8, 39, 18, 25, 3, 18, 1]
  h := [22, 1]
  a := [4, 14, 9, 4, 8, 0, 29]
  b := [14, 20, 39, 25, 27, 27, 12]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD109 : CertificateDedekindCriterionLists l 109 where
  n := 2
  a' := [50, 45, 13, 84, 3, 39]
  b' := [102, 99, 103, 45, 15, 9, 10]
  k := [9, 45, 83, 58, 25, 36, 1]
  f := [35, 35, 31, 34, 29, 5, 24, 1]
  g := [106, 103, 90, 100, 86, 13, 72, 1]
  h := [36, 1]
  a := [17, 84, 44, 88, 1, 47, 61]
  b := [89, 92, 13, 90, 8, 47, 48]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [83] where
  n := 5
  p := ![5, 29, 41, 83, 109]
  exp := ![1, 1, 1, 2, 1]
  pdgood := [5, 29, 41, 109]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp29.out
    exact hp41.out
    exact hp83.out
    exact hp109.out
  a := [4492991517, 4118642776, -10749824778, -3813678646, 5952682365, 596770318, -775656016]
  b := [28885072, -2454073925, -1309323022, 2887857988, 767680358, -1011997187, -86715915, 96957002]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
    exact satisfiesDedekindCriterion_of_certificate_lists T l 41 T_ofList CD41
    exact satisfiesDedekindCriterion_of_certificate_lists T l 109 T_ofList CD109

noncomputable def M83 : MaximalOrderCertificateOfUnramifiedLists 83 O Om hm where
  n := 8
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [57, 38, 31, 25, 17, 71, 17, 0], [62, 47, 42, 37, 30, 74, 30, 67]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [57, 38, 31, 25, 17, 71, 17, 0], [56, 39, 67, 41, 65, 62, 28, 0], [54, 35, 56, 34, 67, 63, 21, 7]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [57, 38, 31, 25, 17, 71, 17, 0], [56, 39, 67, 41, 65, 62, 28, 0], [19, 41, 77, 20, 19, 61, 40, 0], [54, 19, 67, 10, 20, 1, 49, 54]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [57, 38, 31, 25, 17, 71, 17, 0], [56, 39, 67, 41, 65, 62, 28, 0], [19, 41, 77, 20, 19, 61, 40, 0], [39, 45, 36, 81, 36, 37, 77, 0], [82, 55, 71, 53, 56, 25, 47, 49]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [57, 38, 31, 25, 17, 71, 17, 0], [56, 39, 67, 41, 65, 62, 28, 0], [19, 41, 77, 20, 19, 61, 40, 0], [39, 45, 36, 81, 36, 37, 77, 0], [73, 60, 25, 52, 62, 25, 18, 0], [73, 21, 1, 71, 81, 47, 53, 46]], ![[0, 0, 0, 0, 0, 0, 1, 0], [57, 38, 31, 25, 17, 71, 17, 0], [56, 39, 67, 41, 65, 62, 28, 0], [19, 41, 77, 20, 19, 61, 40, 0], [39, 45, 36, 81, 36, 37, 77, 0], [73, 60, 25, 52, 62, 25, 18, 0], [30, 10, 37, 60, 26, 12, 82, 0], [63, 16, 27, 40, 28, 27, 4, 11]], ![[0, 0, 0, 0, 0, 0, 0, 1], [62, 47, 42, 37, 30, 74, 30, 67], [54, 35, 56, 34, 67, 63, 21, 7], [54, 19, 67, 10, 20, 1, 49, 54], [82, 55, 71, 53, 56, 25, 47, 49], [73, 21, 1, 71, 81, 47, 53, 46], [63, 16, 27, 40, 28, 27, 4, 11], [51, 68, 34, 30, 64, 35, 78, 49]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![37, 7, 0, 6, 38, 10, 44, 0], ![63, 66, 21, 3, 59, 39, 67, 0], ![26, 56, 52, 63, 66, 32, 8, 0], ![38, 54, 20, 65, 34, 11, 3, 0], ![52, 51, 23, 67, 74, 53, 39, 0], ![13, 50, 27, 70, 18, 14, 71, 0], ![30, 13, 66, 18, 36, 60, 60, 82]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5, 6, 7]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [83]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 83 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M83
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [83] D q hq hbad)
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

end VoightMaximalOrderD8R145

namespace VoightMaximalOrderD8R146

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2349018125, [1, -1, -36, -16, 35, 9, -11, -1, 1], 83⟩
local notation "l" => [1, -1, -36, -16, 35, 9, -11, -1, 1]
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

def basisDenominator : ℤ := 83
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![83, 0, 0, 0, 0, 0, 0, 0], ![0, 83, 0, 0, 0, 0, 0, 0], ![0, 0, 83, 0, 0, 0, 0, 0], ![0, 0, 0, 83, 0, 0, 0, 0], ![0, 0, 0, 0, 83, 0, 0, 0], ![0, 0, 0, 0, 0, 83, 0, 0], ![0, 0, 0, 0, 0, 0, 83, 0], ![26, 45, 52, 58, 66, 12, 66, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-26, -45, -52, -58, -66, -12, -66, 83], ![-21, -36, -41, -46, -53, -9, -53, 67]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-26, -45, -52, -58, -66, -12, -66, 83], ![-27, -44, -16, -42, -101, -21, -55, 83], ![-29, -48, -27, -49, -99, -20, -62, 90]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-26, -45, -52, -58, -66, -12, -66, 83], ![-27, -44, -16, -42, -101, -21, -55, 83], ![-313, -540, -587, -644, -811, -188, -790, 996], ![-278, -479, -514, -571, -727, -165, -698, 884]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-26, -45, -52, -58, -66, -12, -66, 83], ![-27, -44, -16, -42, -101, -21, -55, 83], ![-313, -540, -587, -644, -811, -188, -790, 996], ![-376, -619, -296, -583, -1292, -295, -836, 1162], ![-416, -692, -427, -694, -1355, -307, -949, 1294]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-26, -45, -52, -58, -66, -12, -66, 83], ![-27, -44, -16, -42, -101, -21, -55, 83], ![-313, -540, -587, -644, -811, -188, -790, 996], ![-376, -619, -296, -583, -1292, -295, -836, 1162], ![-2666, -4588, -4789, -5260, -6993, -1718, -6705, 8466], ![-2500, -4295, -4398, -4909, -6642, -1613, -6255, 7931]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-26, -45, -52, -58, -66, -12, -66, 83], ![-27, -44, -16, -42, -101, -21, -55, 83], ![-313, -540, -587, -644, -811, -188, -790, 996], ![-376, -619, -296, -583, -1292, -295, -836, 1162], ![-2666, -4588, -4789, -5260, -6993, -1718, -6705, 8466], ![-3456, -5717, -3034, -5335, -11428, -2727, -7886, 10707], ![-3921, -6541, -4206, -6434, -12422, -2961, -9126, 12212]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-21, -36, -41, -46, -53, -9, -53, 67], ![-29, -48, -27, -49, -99, -20, -62, 90], ![-278, -479, -514, -571, -727, -165, -698, 884], ![-416, -692, -427, -694, -1355, -307, -949, 1294], ![-2500, -4295, -4398, -4909, -6642, -1613, -6255, 7931], ![-3921, -6541, -4206, -6434, -12422, -2961, -9126, 12212], ![-4265, -7153, -5112, -7274, -13133, -3119, -10048, 13329]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-83]], ![[], [], [], [], [], [], [-6889], [-5561, -83]], ![[], [], [], [], [], [-6889], [-6889, -6889], [-7470, -5561, -83]], ![[], [], [], [], [-6889], [-6889, -6889], [-82668, -6889, -6889], [-73372, -7470, -5561, -83]], ![[], [], [], [-6889], [-6889, -6889], [-82668, -6889, -6889], [-96446, -82668, -6889, -6889], [-107402, -73372, -7470, -5561, -83]], ![[], [], [-6889], [-6889, -6889], [-82668, -6889, -6889], [-96446, -82668, -6889, -6889], [-702678, -96446, -82668, -6889, -6889], [-658273, -107402, -73372, -7470, -5561, -83]], ![[], [-83], [-5561, -83], [-7470, -5561, -83], [-73372, -7470, -5561, -83], [-107402, -73372, -7470, -5561, -83], [-658273, -107402, -73372, -7470, -5561, -83], [-618279, -113821, -65198, -7694, -4524, -133, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-26, -45, -52, -58, -66, -12, -66, 83], [-21, -36, -41, -46, -53, -9, -53, 67]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-26, -45, -52, -58, -66, -12, -66, 83], [-27, -44, -16, -42, -101, -21, -55, 83], [-29, -48, -27, -49, -99, -20, -62, 90]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-26, -45, -52, -58, -66, -12, -66, 83], [-27, -44, -16, -42, -101, -21, -55, 83], [-313, -540, -587, -644, -811, -188, -790, 996], [-278, -479, -514, -571, -727, -165, -698, 884]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-26, -45, -52, -58, -66, -12, -66, 83], [-27, -44, -16, -42, -101, -21, -55, 83], [-313, -540, -587, -644, -811, -188, -790, 996], [-376, -619, -296, -583, -1292, -295, -836, 1162], [-416, -692, -427, -694, -1355, -307, -949, 1294]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-26, -45, -52, -58, -66, -12, -66, 83], [-27, -44, -16, -42, -101, -21, -55, 83], [-313, -540, -587, -644, -811, -188, -790, 996], [-376, -619, -296, -583, -1292, -295, -836, 1162], [-2666, -4588, -4789, -5260, -6993, -1718, -6705, 8466], [-2500, -4295, -4398, -4909, -6642, -1613, -6255, 7931]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-26, -45, -52, -58, -66, -12, -66, 83], [-27, -44, -16, -42, -101, -21, -55, 83], [-313, -540, -587, -644, -811, -188, -790, 996], [-376, -619, -296, -583, -1292, -295, -836, 1162], [-2666, -4588, -4789, -5260, -6993, -1718, -6705, 8466], [-3456, -5717, -3034, -5335, -11428, -2727, -7886, 10707], [-3921, -6541, -4206, -6434, -12422, -2961, -9126, 12212]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-21, -36, -41, -46, -53, -9, -53, 67], [-29, -48, -27, -49, -99, -20, -62, 90], [-278, -479, -514, -571, -727, -165, -698, 884], [-416, -692, -427, -694, -1355, -307, -949, 1294], [-2500, -4295, -4398, -4909, -6642, -1613, -6255, 7931], [-3921, -6541, -4206, -6434, -12422, -2961, -9126, 12212], [-4265, -7153, -5112, -7274, -13133, -3119, -10048, 13329]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp41 : Fact (Nat.Prime 41) := fact_iff.2 (by norm_num)
instance hp83 : Fact (Nat.Prime 83) := fact_iff.2 (by norm_num)
instance hp109 : Fact (Nat.Prime 109) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 1, 1]
  b' := [4, 4, 4, 1]
  k := [1]
  f := [0, 1, 8, 4, -5, -1, 3, 1]
  g := [1, 2, 0, 2, 1]
  h := [1, 2, 0, 2, 1]
  a := [2, 1, 3, 1]
  b := [1, 1, 1, 2, 4, 1, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [9, 19, 13, 15, 15]
  b' := [17, 16, 6, 8, 16, 12]
  k := [16, 20, 24, 5, 1]
  f := [3, 15, 30, 19, 1, 3, 3, 1]
  g := [4, 15, 20, 0, 2, 2, 1]
  h := [22, 26, 1]
  a := [28, 3, 7, 0, 25, 24]
  b := [1, 5, 18, 23, 28, 9, 5]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD41 : CertificateDedekindCriterionLists l 41 where
  n := 2
  a' := [25, 37, 1, 23, 0, 6]
  b' := [10, 35, 8, 37, 16, 7, 5]
  k := [5, 2, 11, 32, 9, 37, 1]
  f := [15, 5, 22, 11, 13, 2, 10, 1]
  g := [28, 8, 39, 18, 25, 3, 18, 1]
  h := [22, 1]
  a := [4, 14, 9, 4, 8, 0, 29]
  b := [14, 20, 39, 25, 27, 27, 12]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD109 : CertificateDedekindCriterionLists l 109 where
  n := 2
  a' := [50, 45, 13, 84, 3, 39]
  b' := [102, 99, 103, 45, 15, 9, 10]
  k := [9, 45, 83, 58, 25, 36, 1]
  f := [35, 35, 31, 34, 29, 5, 24, 1]
  g := [106, 103, 90, 100, 86, 13, 72, 1]
  h := [36, 1]
  a := [17, 84, 44, 88, 1, 47, 61]
  b := [89, 92, 13, 90, 8, 47, 48]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [83] where
  n := 5
  p := ![5, 29, 41, 83, 109]
  exp := ![1, 1, 1, 2, 1]
  pdgood := [5, 29, 41, 109]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp29.out
    exact hp41.out
    exact hp83.out
    exact hp109.out
  a := [4492991517, 4118642776, -10749824778, -3813678646, 5952682365, 596770318, -775656016]
  b := [28885072, -2454073925, -1309323022, 2887857988, 767680358, -1011997187, -86715915, 96957002]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
    exact satisfiesDedekindCriterion_of_certificate_lists T l 41 T_ofList CD41
    exact satisfiesDedekindCriterion_of_certificate_lists T l 109 T_ofList CD109

noncomputable def M83 : MaximalOrderCertificateOfUnramifiedLists 83 O Om hm where
  n := 8
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [57, 38, 31, 25, 17, 71, 17, 0], [62, 47, 42, 37, 30, 74, 30, 67]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [57, 38, 31, 25, 17, 71, 17, 0], [56, 39, 67, 41, 65, 62, 28, 0], [54, 35, 56, 34, 67, 63, 21, 7]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [57, 38, 31, 25, 17, 71, 17, 0], [56, 39, 67, 41, 65, 62, 28, 0], [19, 41, 77, 20, 19, 61, 40, 0], [54, 19, 67, 10, 20, 1, 49, 54]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [57, 38, 31, 25, 17, 71, 17, 0], [56, 39, 67, 41, 65, 62, 28, 0], [19, 41, 77, 20, 19, 61, 40, 0], [39, 45, 36, 81, 36, 37, 77, 0], [82, 55, 71, 53, 56, 25, 47, 49]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [57, 38, 31, 25, 17, 71, 17, 0], [56, 39, 67, 41, 65, 62, 28, 0], [19, 41, 77, 20, 19, 61, 40, 0], [39, 45, 36, 81, 36, 37, 77, 0], [73, 60, 25, 52, 62, 25, 18, 0], [73, 21, 1, 71, 81, 47, 53, 46]], ![[0, 0, 0, 0, 0, 0, 1, 0], [57, 38, 31, 25, 17, 71, 17, 0], [56, 39, 67, 41, 65, 62, 28, 0], [19, 41, 77, 20, 19, 61, 40, 0], [39, 45, 36, 81, 36, 37, 77, 0], [73, 60, 25, 52, 62, 25, 18, 0], [30, 10, 37, 60, 26, 12, 82, 0], [63, 16, 27, 40, 28, 27, 4, 11]], ![[0, 0, 0, 0, 0, 0, 0, 1], [62, 47, 42, 37, 30, 74, 30, 67], [54, 35, 56, 34, 67, 63, 21, 7], [54, 19, 67, 10, 20, 1, 49, 54], [82, 55, 71, 53, 56, 25, 47, 49], [73, 21, 1, 71, 81, 47, 53, 46], [63, 16, 27, 40, 28, 27, 4, 11], [51, 68, 34, 30, 64, 35, 78, 49]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![37, 7, 0, 6, 38, 10, 44, 0], ![63, 66, 21, 3, 59, 39, 67, 0], ![26, 56, 52, 63, 66, 32, 8, 0], ![38, 54, 20, 65, 34, 11, 3, 0], ![52, 51, 23, 67, 74, 53, 39, 0], ![13, 50, 27, 70, 18, 14, 71, 0], ![30, 13, 66, 18, 36, 60, 60, 82]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5, 6, 7]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [83]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 83 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M83
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [83] D q hq hbad)
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

end VoightMaximalOrderD8R146

end TraceEuclidean
