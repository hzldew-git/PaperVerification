import TraceEuclidean.VoightMaximalOrderCertificates.Chunk089
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

namespace VoightMaximalOrderD8R88

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1781343125, [1, 23, -28, -29, 30, 13, -10, -2, 1], 13⟩
local notation "l" => [1, 23, -28, -29, 30, 13, -10, -2, 1]
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

def basisDenominator : ℤ := 13
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![13, 0, 0, 0, 0, 0, 0, 0], ![0, 13, 0, 0, 0, 0, 0, 0], ![0, 0, 13, 0, 0, 0, 0, 0], ![0, 0, 0, 13, 0, 0, 0, 0], ![0, 0, 0, 0, 13, 0, 0, 0], ![0, 0, 0, 0, 0, 13, 0, 0], ![0, 0, 0, 0, 0, 0, 13, 0], ![2, 3, 3, 1, 6, 1, 4, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -3, -3, -1, -6, -1, -4, 13], ![-1, -3, 1, 2, -5, -1, -1, 6]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -3, -3, -1, -6, -1, -4, 13], ![-5, -29, 22, 27, -42, -15, 2, 26], ![-4, -16, 6, 14, -22, -10, -3, 23]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -3, -3, -1, -6, -1, -4, 13], ![-5, -29, 22, 27, -42, -15, 2, 26], ![-30, -89, -9, 72, -115, -70, -49, 182], ![-17, -64, 16, 55, -83, -42, -21, 99]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -3, -3, -1, -6, -1, -4, 13], ![-5, -29, 22, 27, -42, -15, 2, 26], ![-30, -89, -9, 72, -115, -70, -49, 182], ![-84, -429, 240, 404, -544, -248, -56, 455], ![-57, -251, 98, 235, -314, -161, -57, 321]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -3, -3, -1, -6, -1, -4, 13], ![-5, -29, 22, 27, -42, -15, 2, 26], ![-30, -89, -9, 72, -115, -70, -49, 182], ![-84, -429, 240, 404, -544, -248, -56, 455], ![-343, -1281, 194, 1206, -1535, -943, -479, 2002], ![-207, -849, 241, 797, -1028, -578, -254, 1185]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -3, -3, -1, -6, -1, -4, 13], ![-5, -29, 22, 27, -42, -15, 2, 26], ![-30, -89, -9, 72, -115, -70, -49, 182], ![-84, -429, 240, 404, -544, -248, -56, 455], ![-343, -1281, 194, 1206, -1535, -943, -479, 2002], ![-1044, -4912, 2158, 4677, -5930, -3058, -1029, 5785], ![-677, -3000, 1098, 2865, -3604, -1959, -747, 3808]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -3, 1, 2, -5, -1, -1, 6], ![-4, -16, 6, 14, -22, -10, -3, 23], ![-17, -64, 16, 55, -83, -42, -21, 99], ![-57, -251, 98, 235, -314, -161, -57, 321], ![-207, -849, 241, 797, -1028, -578, -254, 1185], ![-677, -3000, 1098, 2865, -3604, -1959, -747, 3808], ![-431, -1872, 639, 1787, -2245, -1240, -492, 2436]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-13]], ![[], [], [], [], [], [], [-169], [-78, -13]], ![[], [], [], [], [], [-169], [-338, -169], [-299, -78, -13]], ![[], [], [], [], [-169], [-338, -169], [-2366, -338, -169], [-1287, -299, -78, -13]], ![[], [], [], [-169], [-338, -169], [-2366, -338, -169], [-5915, -2366, -338, -169], [-4173, -1287, -299, -78, -13]], ![[], [], [-169], [-338, -169], [-2366, -338, -169], [-5915, -2366, -338, -169], [-26026, -5915, -2366, -338, -169], [-15405, -4173, -1287, -299, -78, -13]], ![[], [-13], [-78, -13], [-299, -78, -13], [-1287, -299, -78, -13], [-4173, -1287, -299, -78, -13], [-15405, -4173, -1287, -299, -78, -13], [-9507, -2715, -777, -203, -48, -10, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-2, -3, -3, -1, -6, -1, -4, 13], [-1, -3, 1, 2, -5, -1, -1, 6]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-2, -3, -3, -1, -6, -1, -4, 13], [-5, -29, 22, 27, -42, -15, 2, 26], [-4, -16, 6, 14, -22, -10, -3, 23]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-2, -3, -3, -1, -6, -1, -4, 13], [-5, -29, 22, 27, -42, -15, 2, 26], [-30, -89, -9, 72, -115, -70, -49, 182], [-17, -64, 16, 55, -83, -42, -21, 99]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-2, -3, -3, -1, -6, -1, -4, 13], [-5, -29, 22, 27, -42, -15, 2, 26], [-30, -89, -9, 72, -115, -70, -49, 182], [-84, -429, 240, 404, -544, -248, -56, 455], [-57, -251, 98, 235, -314, -161, -57, 321]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-2, -3, -3, -1, -6, -1, -4, 13], [-5, -29, 22, 27, -42, -15, 2, 26], [-30, -89, -9, 72, -115, -70, -49, 182], [-84, -429, 240, 404, -544, -248, -56, 455], [-343, -1281, 194, 1206, -1535, -943, -479, 2002], [-207, -849, 241, 797, -1028, -578, -254, 1185]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-2, -3, -3, -1, -6, -1, -4, 13], [-5, -29, 22, 27, -42, -15, 2, 26], [-30, -89, -9, 72, -115, -70, -49, 182], [-84, -429, 240, 404, -544, -248, -56, 455], [-343, -1281, 194, 1206, -1535, -943, -479, 2002], [-1044, -4912, 2158, 4677, -5930, -3058, -1029, 5785], [-677, -3000, 1098, 2865, -3604, -1959, -747, 3808]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-1, -3, 1, 2, -5, -1, -1, 6], [-4, -16, 6, 14, -22, -10, -3, 23], [-17, -64, 16, 55, -83, -42, -21, 99], [-57, -251, 98, 235, -314, -161, -57, 321], [-207, -849, 241, 797, -1028, -578, -254, 1185], [-677, -3000, 1098, 2865, -3604, -1959, -747, 3808], [-431, -1872, 639, 1787, -2245, -1240, -492, 2436]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp13 : Fact (Nat.Prime 13) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp3389 : Fact (Nat.Prime 3389) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 4, 2]
  b' := [1, 0, 1, 2]
  k := [1]
  f := [3, -3, 9, 13, -2, 1, 6, 2]
  g := [4, 1, 2, 4, 1]
  h := [4, 1, 2, 4, 1]
  a := [2, 4, 0, 1]
  b := [0, 1, 2, 4, 2, 2, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [27, 5, 28, 3, 17]
  b' := [27, 28, 14, 0, 25, 2]
  k := [7, 5, 26, 10, 1]
  f := [19, 34, 35, 20, 17, 18, 5, 1]
  g := [23, 20, 21, 2, 19, 4, 1]
  h := [24, 23, 1]
  a := [24, 6, 17, 28, 23, 19]
  b := [13, 5, 0, 27, 15, 16, 10]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3389 : CertificateDedekindCriterionLists l 3389 where
  n := 2
  a' := [2307, 1293, 1078, 2866, 446, 1728]
  b' := [2191, 2489, 3033, 2545, 476, 2206, 2658]
  k := [1260, 1971, 2234, 1604, 382, 3074, 1]
  f := [343, 1648, 1380, 1352, 211, 123, 839, 1]
  g := [628, 3017, 2525, 2474, 385, 225, 1536, 1]
  h := [1851, 1]
  a := [3003, 2882, 728, 2386, 3385, 2255, 1266]
  b := [1792, 1979, 3217, 1319, 3058, 2396, 2123]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [13] where
  n := 4
  p := ![5, 13, 29, 3389]
  exp := ![1, 2, 1, 1]
  pdgood := [5, 29, 3389]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp13.out
    exact hp29.out
    exact hp3389.out
  a := [3284204, 106204886, -120023735, -296950668, 166470046, 100814704, -40697888]
  b := [3467967, 541938, -82550838, 49331345, 68449057, -32602052, -13873647, 5087236]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3389 T_ofList CD3389

noncomputable def M13 : MaximalOrderCertificateOfUnramifiedLists 13 O Om hm where
  n := 8
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [11, 10, 10, 12, 7, 12, 9, 0], [12, 10, 1, 2, 8, 12, 12, 6]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [11, 10, 10, 12, 7, 12, 9, 0], [8, 10, 9, 1, 10, 11, 2, 0], [9, 10, 6, 1, 4, 3, 10, 10]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [11, 10, 10, 12, 7, 12, 9, 0], [8, 10, 9, 1, 10, 11, 2, 0], [9, 2, 4, 7, 2, 8, 3, 0], [9, 1, 3, 3, 8, 10, 5, 8]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [11, 10, 10, 12, 7, 12, 9, 0], [8, 10, 9, 1, 10, 11, 2, 0], [9, 2, 4, 7, 2, 8, 3, 0], [7, 0, 6, 1, 2, 12, 9, 0], [8, 9, 7, 1, 11, 8, 8, 9]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [11, 10, 10, 12, 7, 12, 9, 0], [8, 10, 9, 1, 10, 11, 2, 0], [9, 2, 4, 7, 2, 8, 3, 0], [7, 0, 6, 1, 2, 12, 9, 0], [8, 6, 12, 10, 12, 6, 2, 0], [1, 9, 7, 4, 12, 7, 6, 2]], ![[0, 0, 0, 0, 0, 0, 1, 0], [11, 10, 10, 12, 7, 12, 9, 0], [8, 10, 9, 1, 10, 11, 2, 0], [9, 2, 4, 7, 2, 8, 3, 0], [7, 0, 6, 1, 2, 12, 9, 0], [8, 6, 12, 10, 12, 6, 2, 0], [9, 2, 0, 10, 11, 10, 11, 0], [12, 3, 6, 5, 10, 4, 7, 12]], ![[0, 0, 0, 0, 0, 0, 0, 1], [12, 10, 1, 2, 8, 12, 12, 6], [9, 10, 6, 1, 4, 3, 10, 10], [9, 1, 3, 3, 8, 10, 5, 8], [8, 9, 7, 1, 11, 8, 8, 9], [1, 9, 7, 4, 12, 7, 6, 2], [12, 3, 6, 5, 10, 4, 7, 12], [11, 0, 2, 6, 4, 8, 2, 5]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![4, 2, 8, 2, 9, 0, 5, 0], ![4, 1, 6, 9, 2, 10, 1, 0], ![11, 8, 6, 1, 1, 5, 8, 0], ![9, 3, 4, 10, 6, 2, 1, 0], ![0, 6, 5, 5, 8, 4, 9, 0], ![7, 10, 1, 8, 8, 7, 7, 0], ![2, 1, 5, 7, 9, 9, 0, 12]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5, 6, 7]
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

end VoightMaximalOrderD8R88

namespace VoightMaximalOrderD8R89

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1787650625, [-1, 19, -16, -33, 27, 15, -12, -1, 1], 227⟩
local notation "l" => [-1, 19, -16, -33, 27, 15, -12, -1, 1]
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

def basisDenominator : ℤ := 227
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![227, 0, 0, 0, 0, 0, 0, 0], ![0, 227, 0, 0, 0, 0, 0, 0], ![0, 0, 227, 0, 0, 0, 0, 0], ![0, 0, 0, 227, 0, 0, 0, 0], ![0, 0, 0, 0, 227, 0, 0, 0], ![0, 0, 0, 0, 0, 227, 0, 0], ![0, 0, 0, 0, 0, 0, 227, 0], ![40, 159, 190, 67, 11, 67, 209, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-40, -159, -190, -67, -11, -67, -209, 227], ![-37, -147, -175, -61, -10, -62, -193, 210]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-40, -159, -190, -67, -11, -67, -209, 227], ![-39, -178, -174, -34, -38, -82, -197, 227], ![-50, -220, -227, -54, -38, -99, -255, 289]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-40, -159, -190, -67, -11, -67, -209, 227], ![-39, -178, -174, -34, -38, -82, -197, 227], ![-519, -2085, -2473, -822, -137, -913, -2720, 2951], ![-493, -1988, -2345, -771, -139, -871, -2581, 2805]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-40, -159, -190, -67, -11, -67, -209, 227], ![-39, -178, -174, -34, -38, -82, -197, 227], ![-519, -2085, -2473, -822, -137, -913, -2720, 2951], ![-387, -1836, -1710, -244, -412, -859, -1976, 2270], ![-545, -2449, -2473, -523, -430, -1122, -2807, 3163]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-40, -159, -190, -67, -11, -67, -209, 227], ![-39, -178, -174, -34, -38, -82, -197, 227], ![-519, -2085, -2473, -822, -137, -913, -2720, 2951], ![-387, -1836, -1710, -244, -412, -859, -1976, 2270], ![-4950, -19893, -23646, -7788, -1208, -8760, -25985, 28148], ![-4751, -19193, -22644, -7347, -1276, -8467, -24918, 27041]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-40, -159, -190, -67, -11, -67, -209, 227], ![-39, -178, -174, -34, -38, -82, -197, 227], ![-519, -2085, -2473, -822, -137, -913, -2720, 2951], ![-387, -1836, -1710, -244, -412, -859, -1976, 2270], ![-4950, -19893, -23646, -7788, -1208, -8760, -25985, 28148], ![-2076, -11091, -8643, 321, -3433, -5389, -10459, 12485], ![-3797, -17816, -16948, -2639, -3659, -8312, -19518, 22224]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-37, -147, -175, -61, -10, -62, -193, 210], ![-50, -220, -227, -54, -38, -99, -255, 289], ![-493, -1988, -2345, -771, -139, -871, -2581, 2805], ![-545, -2449, -2473, -523, -430, -1122, -2807, 3163], ![-4751, -19193, -22644, -7347, -1276, -8467, -24918, 27041], ![-3797, -17816, -16948, -2639, -3659, -8312, -19518, 22224], ![-5321, -23798, -24287, -5225, -3891, -10915, -27533, 30855]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-227]], ![[], [], [], [], [], [], [-51529], [-47670, -227]], ![[], [], [], [], [], [-51529], [-51529, -51529], [-65603, -47670, -227]], ![[], [], [], [], [-51529], [-51529, -51529], [-669877, -51529, -51529], [-636735, -65603, -47670, -227]], ![[], [], [], [-51529], [-51529, -51529], [-669877, -51529, -51529], [-515290, -669877, -51529, -51529], [-718001, -636735, -65603, -47670, -227]], ![[], [], [-51529], [-51529, -51529], [-669877, -51529, -51529], [-515290, -669877, -51529, -51529], [-6389596, -515290, -669877, -51529, -51529], [-6138307, -718001, -636735, -65603, -47670, -227]], ![[], [-227], [-47670, -227], [-65603, -47670, -227], [-636735, -65603, -47670, -227], [-718001, -636735, -65603, -47670, -227], [-6138307, -718001, -636735, -65603, -47670, -227], [-5975991, -893482, -611148, -77287, -44246, -419, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-40, -159, -190, -67, -11, -67, -209, 227], [-37, -147, -175, -61, -10, -62, -193, 210]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-40, -159, -190, -67, -11, -67, -209, 227], [-39, -178, -174, -34, -38, -82, -197, 227], [-50, -220, -227, -54, -38, -99, -255, 289]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-40, -159, -190, -67, -11, -67, -209, 227], [-39, -178, -174, -34, -38, -82, -197, 227], [-519, -2085, -2473, -822, -137, -913, -2720, 2951], [-493, -1988, -2345, -771, -139, -871, -2581, 2805]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-40, -159, -190, -67, -11, -67, -209, 227], [-39, -178, -174, -34, -38, -82, -197, 227], [-519, -2085, -2473, -822, -137, -913, -2720, 2951], [-387, -1836, -1710, -244, -412, -859, -1976, 2270], [-545, -2449, -2473, -523, -430, -1122, -2807, 3163]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-40, -159, -190, -67, -11, -67, -209, 227], [-39, -178, -174, -34, -38, -82, -197, 227], [-519, -2085, -2473, -822, -137, -913, -2720, 2951], [-387, -1836, -1710, -244, -412, -859, -1976, 2270], [-4950, -19893, -23646, -7788, -1208, -8760, -25985, 28148], [-4751, -19193, -22644, -7347, -1276, -8467, -24918, 27041]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-40, -159, -190, -67, -11, -67, -209, 227], [-39, -178, -174, -34, -38, -82, -197, 227], [-519, -2085, -2473, -822, -137, -913, -2720, 2951], [-387, -1836, -1710, -244, -412, -859, -1976, 2270], [-4950, -19893, -23646, -7788, -1208, -8760, -25985, 28148], [-2076, -11091, -8643, 321, -3433, -5389, -10459, 12485], [-3797, -17816, -16948, -2639, -3659, -8312, -19518, 22224]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-37, -147, -175, -61, -10, -62, -193, 210], [-50, -220, -227, -54, -38, -99, -255, 289], [-493, -1988, -2345, -771, -139, -871, -2581, 2805], [-545, -2449, -2473, -523, -430, -1122, -2807, 3163], [-4751, -19193, -22644, -7347, -1276, -8467, -24918, 27041], [-3797, -17816, -16948, -2639, -3659, -8312, -19518, 22224], [-5321, -23798, -24287, -5225, -3891, -10915, -27533, 30855]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp179 : Fact (Nat.Prime 179) := fact_iff.2 (by norm_num)
instance hp227 : Fact (Nat.Prime 227) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 3, 3]
  b' := [4, 2, 2, 3]
  k := [1]
  f := [1, -3, 5, 9, -3, -1, 4, 1]
  g := [2, 1, 2, 2, 1]
  h := [2, 1, 2, 2, 1]
  a := [3, 3, 3, 3]
  b := [4, 1, 1, 4, 2, 1, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD19 : CertificateDedekindCriterionLists l 19 where
  n := 2
  a' := [14, 18, 6, 12, 15, 4]
  b' := [12, 8, 11, 0, 11, 8, 13]
  k := [3, 5, 2, 16, 15, 9, 1]
  f := [3, 11, 12, 15, 12, 6, 4, 1]
  g := [4, 16, 14, 17, 17, 8, 4, 1]
  h := [14, 1]
  a := [0, 7, 18, 5, 8, 14, 12]
  b := [5, 8, 8, 6, 16, 5, 7]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [27, 25, 14, 24, 6]
  b' := [24, 9, 21, 28, 15, 28]
  k := [20, 9, 18, 5, 1]
  f := [9, 23, 12, 28, 9, 12, 3, 1]
  g := [26, 1, 28, 5, 13, 2, 1]
  h := [10, 26, 1]
  a := [15, 16, 17, 2, 9, 17]
  b := [6, 20, 16, 1, 11, 3, 12]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD179 : CertificateDedekindCriterionLists l 179 where
  n := 2
  a' := [165, 128, 17, 102, 28, 164]
  b' := [104, 27, 73, 138, 6, 42, 130]
  k := [98, 81, 100, 84, 74, 39, 1]
  f := [8, 79, 45, 28, 32, 9, 17, 1]
  g := [9, 89, 50, 31, 36, 10, 19, 1]
  h := [159, 1]
  a := [172, 47, 24, 110, 173, 94, 97]
  b := [66, 83, 144, 31, 6, 100, 82]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [227] where
  n := 5
  p := ![5, 19, 29, 179, 227]
  exp := ![1, 1, 1, 1, 2]
  pdgood := [5, 19, 29, 179]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp19.out
    exact hp29.out
    exact hp179.out
    exact hp227.out
  a := [17838294476, 8292100554, -85307893980, -23078298972, 62730415971, 1390026414, -7275913168]
  b := [2276292799, -13568111838, -8751141295, 23683673554, 6023465489, -10647525647, -287439445, 909489146]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19 T_ofList CD19
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
    exact satisfiesDedekindCriterion_of_certificate_lists T l 179 T_ofList CD179

noncomputable def M227 : MaximalOrderCertificateOfUnramifiedLists 227 O Om hm where
  n := 8
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [187, 68, 37, 160, 216, 160, 18, 0], [190, 80, 52, 166, 217, 165, 34, 210]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [187, 68, 37, 160, 216, 160, 18, 0], [188, 49, 53, 193, 189, 145, 30, 0], [177, 7, 0, 173, 189, 128, 199, 62]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [187, 68, 37, 160, 216, 160, 18, 0], [188, 49, 53, 193, 189, 145, 30, 0], [162, 185, 24, 86, 90, 222, 4, 0], [188, 55, 152, 137, 88, 37, 143, 81]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [187, 68, 37, 160, 216, 160, 18, 0], [188, 49, 53, 193, 189, 145, 30, 0], [162, 185, 24, 86, 90, 222, 4, 0], [67, 207, 106, 210, 42, 49, 67, 0], [136, 48, 24, 158, 24, 13, 144, 212]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [187, 68, 37, 160, 216, 160, 18, 0], [188, 49, 53, 193, 189, 145, 30, 0], [162, 185, 24, 86, 90, 222, 4, 0], [67, 207, 106, 210, 42, 49, 67, 0], [44, 83, 189, 157, 154, 93, 120, 0], [16, 102, 56, 144, 86, 159, 52, 28]], ![[0, 0, 0, 0, 0, 0, 1, 0], [187, 68, 37, 160, 216, 160, 18, 0], [188, 49, 53, 193, 189, 145, 30, 0], [162, 185, 24, 86, 90, 222, 4, 0], [67, 207, 106, 210, 42, 49, 67, 0], [44, 83, 189, 157, 154, 93, 120, 0], [194, 32, 210, 94, 199, 59, 210, 0], [62, 117, 77, 85, 200, 87, 4, 205]], ![[0, 0, 0, 0, 0, 0, 0, 1], [190, 80, 52, 166, 217, 165, 34, 210], [177, 7, 0, 173, 189, 128, 199, 62], [188, 55, 152, 137, 88, 37, 143, 81], [136, 48, 24, 158, 24, 13, 144, 212], [16, 102, 56, 144, 86, 159, 52, 28], [62, 117, 77, 85, 200, 87, 4, 205], [127, 37, 2, 223, 195, 208, 161, 210]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![72, 130, 23, 120, 77, 29, 147, 0], ![125, 15, 198, 191, 226, 111, 115, 0], ![102, 92, 30, 12, 50, 3, 18, 0], ![156, 32, 152, 77, 71, 2, 226, 0], ![170, 29, 178, 174, 110, 85, 138, 0], ![176, 198, 107, 216, 32, 30, 185, 0], ![177, 200, 22, 73, 224, 137, 217, 226]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5, 6, 7]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [227]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 227 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M227
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [227] D q hq hbad)
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

end VoightMaximalOrderD8R89

namespace VoightMaximalOrderD8R96

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1844418125, [-1, -16, -25, 17, 37, -2, -12, 0, 1], 167⟩
local notation "l" => [-1, -16, -25, 17, 37, -2, -12, 0, 1]
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

def basisDenominator : ℤ := 167
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![167, 0, 0, 0, 0, 0, 0, 0], ![0, 167, 0, 0, 0, 0, 0, 0], ![0, 0, 167, 0, 0, 0, 0, 0], ![0, 0, 0, 167, 0, 0, 0, 0], ![0, 0, 0, 0, 167, 0, 0, 0], ![0, 0, 0, 0, 0, 167, 0, 0], ![0, 0, 0, 0, 0, 0, 167, 0], ![124, 159, 104, 100, 130, 2, 66, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-124, -159, -104, -100, -130, -2, -66, 167], ![-49, -62, -40, -39, -51, 0, -26, 66]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-124, -159, -104, -100, -130, -2, -66, 167], ![1, 16, 25, -17, -37, 2, 12, 0], ![-10, -7, 2, -14, -25, 1, 0, 14]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-124, -159, -104, -100, -130, -2, -66, 167], ![1, 16, 25, -17, -37, 2, 12, 0], ![-1488, -1907, -1232, -1175, -1577, -61, -790, 2004], ![-686, -878, -567, -544, -728, -25, -363, 924]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-124, -159, -104, -100, -130, -2, -66, 167], ![1, 16, 25, -17, -37, 2, 12, 0], ![-1488, -1907, -1232, -1175, -1577, -61, -790, 2004], ![-236, -126, 93, -388, -679, 3, -25, 334], ![-264, -257, -86, -303, -478, -2, -91, 363]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-124, -159, -104, -100, -130, -2, -66, 167], ![1, 16, 25, -17, -37, 2, 12, 0], ![-1488, -1907, -1232, -1175, -1577, -61, -790, 2004], ![-236, -126, 93, -388, -679, 3, -25, 334], ![-13266, -16969, -10886, -10433, -14172, -629, -7031, 17869], ![-6503, -8301, -5313, -5143, -6986, -296, -3434, 8761]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-124, -159, -104, -100, -130, -2, -66, 167], ![1, 16, 25, -17, -37, 2, 12, 0], ![-1488, -1907, -1232, -1175, -1577, -61, -790, 2004], ![-236, -126, 93, -388, -679, 3, -25, 334], ![-13266, -16969, -10886, -10433, -14172, -629, -7031, 17869], ![-3737, -3215, -505, -4677, -7722, -110, -1177, 5177], ![-3473, -3679, -1605, -3592, -5534, -118, -1438, 4748]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-49, -62, -40, -39, -51, 0, -26, 66], ![-10, -7, 2, -14, -25, 1, 0, 14], ![-686, -878, -567, -544, -728, -25, -363, 924], ![-264, -257, -86, -303, -478, -2, -91, 363], ![-6503, -8301, -5313, -5143, -6986, -296, -3434, 8761], ![-3473, -3679, -1605, -3592, -5534, -118, -1438, 4748], ![-2445, -2757, -1405, -2346, -3495, -82, -1094, 3328]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-167]], ![[], [], [], [], [], [], [-27889], [-11022, -167]], ![[], [], [], [], [], [-27889], [0, -27889], [-2338, -11022, -167]], ![[], [], [], [], [-27889], [0, -27889], [-334668, 0, -27889], [-154308, -2338, -11022, -167]], ![[], [], [], [-27889], [0, -27889], [-334668, 0, -27889], [-55778, -334668, 0, -27889], [-60621, -154308, -2338, -11022, -167]], ![[], [], [-27889], [0, -27889], [-334668, 0, -27889], [-55778, -334668, 0, -27889], [-2984123, -55778, -334668, 0, -27889], [-1463087, -60621, -154308, -2338, -11022, -167]], ![[], [-167], [-11022, -167], [-2338, -11022, -167], [-154308, -2338, -11022, -167], [-60621, -154308, -2338, -11022, -167], [-1463087, -60621, -154308, -2338, -11022, -167], [-712243, -43091, -70055, -2110, -4372, -132, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-124, -159, -104, -100, -130, -2, -66, 167], [-49, -62, -40, -39, -51, 0, -26, 66]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-124, -159, -104, -100, -130, -2, -66, 167], [1, 16, 25, -17, -37, 2, 12, 0], [-10, -7, 2, -14, -25, 1, 0, 14]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-124, -159, -104, -100, -130, -2, -66, 167], [1, 16, 25, -17, -37, 2, 12, 0], [-1488, -1907, -1232, -1175, -1577, -61, -790, 2004], [-686, -878, -567, -544, -728, -25, -363, 924]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-124, -159, -104, -100, -130, -2, -66, 167], [1, 16, 25, -17, -37, 2, 12, 0], [-1488, -1907, -1232, -1175, -1577, -61, -790, 2004], [-236, -126, 93, -388, -679, 3, -25, 334], [-264, -257, -86, -303, -478, -2, -91, 363]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-124, -159, -104, -100, -130, -2, -66, 167], [1, 16, 25, -17, -37, 2, 12, 0], [-1488, -1907, -1232, -1175, -1577, -61, -790, 2004], [-236, -126, 93, -388, -679, 3, -25, 334], [-13266, -16969, -10886, -10433, -14172, -629, -7031, 17869], [-6503, -8301, -5313, -5143, -6986, -296, -3434, 8761]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-124, -159, -104, -100, -130, -2, -66, 167], [1, 16, 25, -17, -37, 2, 12, 0], [-1488, -1907, -1232, -1175, -1577, -61, -790, 2004], [-236, -126, 93, -388, -679, 3, -25, 334], [-13266, -16969, -10886, -10433, -14172, -629, -7031, 17869], [-3737, -3215, -505, -4677, -7722, -110, -1177, 5177], [-3473, -3679, -1605, -3592, -5534, -118, -1438, 4748]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-49, -62, -40, -39, -51, 0, -26, 66], [-10, -7, 2, -14, -25, 1, 0, 14], [-686, -878, -567, -544, -728, -25, -363, 924], [-264, -257, -86, -303, -478, -2, -91, 363], [-6503, -8301, -5313, -5143, -6986, -296, -3434, 8761], [-3473, -3679, -1605, -3592, -5534, -118, -1438, 4748], [-2445, -2757, -1405, -2346, -3495, -82, -1094, 3328]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp167 : Fact (Nat.Prime 167) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 4, 2]
  b' := [4, 4, 4, 2]
  k := [1]
  f := [2, 8, 13, 3, -3, 2, 4]
  g := [3, 4, 4, 0, 1]
  h := [3, 4, 4, 0, 1]
  a := [3, 4, 2, 4]
  b := [0, 1, 2, 1, 4, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [5, 4, 6, 2]
  b' := [5, 6, 5, 4, 7]
  k := [8, 1, 4, 7, 1]
  f := [5, 5, 5, 4, 2, 9, 4, 1]
  g := [6, 3, 2, 6, 5, 9, 1]
  h := [9, 2, 1]
  a := [0, 8, 2, 5, 9, 8]
  b := [2, 7, 4, 5, 0, 9, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 4
  a' := [2, 23, 22, 4]
  b' := [6, 15, 8, 12, 5]
  k := [13, 11, 28, 9, 19, 28, 6, 4, 13, 1, 21, 25, 1]
  f := [1, 8, 13, 9, 16, 11, 2, 1]
  g := [2, 14, 15, 8, 28, 1]
  h := [14, 10, 1, 1]
  a := [28, 16, 10, 24, 4]
  b := [1, 18, 7, 23, 10, 22, 25]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [167] where
  n := 4
  p := ![5, 11, 29, 167]
  exp := ![1, 1, 1, 2]
  pdgood := [5, 11, 29]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp11.out
    exact hp29.out
    exact hp167.out
  a := [304359237, 473932202, -1587813382, -539602260, 913317856, 80278872, -108324176]
  b := [-21802637, -265846759, -88979957, 433402576, 87399468, -154786298, -10034859, 13540522]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29

noncomputable def M167 : MaximalOrderCertificateOfUnramifiedLists 167 O Om hm where
  n := 8
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [43, 8, 63, 67, 37, 165, 101, 0], [118, 105, 127, 128, 116, 0, 141, 66]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [43, 8, 63, 67, 37, 165, 101, 0], [1, 16, 25, 150, 130, 2, 12, 0], [157, 160, 2, 153, 142, 1, 0, 14]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [43, 8, 63, 67, 37, 165, 101, 0], [1, 16, 25, 150, 130, 2, 12, 0], [15, 97, 104, 161, 93, 106, 45, 0], [149, 124, 101, 124, 107, 142, 138, 89]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [43, 8, 63, 67, 37, 165, 101, 0], [1, 16, 25, 150, 130, 2, 12, 0], [15, 97, 104, 161, 93, 106, 45, 0], [98, 41, 93, 113, 156, 3, 142, 0], [70, 77, 81, 31, 23, 165, 76, 29]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [43, 8, 63, 67, 37, 165, 101, 0], [1, 16, 25, 150, 130, 2, 12, 0], [15, 97, 104, 161, 93, 106, 45, 0], [98, 41, 93, 113, 156, 3, 142, 0], [94, 65, 136, 88, 23, 39, 150, 0], [10, 49, 31, 34, 28, 38, 73, 77]], ![[0, 0, 0, 0, 0, 0, 1, 0], [43, 8, 63, 67, 37, 165, 101, 0], [1, 16, 25, 150, 130, 2, 12, 0], [15, 97, 104, 161, 93, 106, 45, 0], [98, 41, 93, 113, 156, 3, 142, 0], [94, 65, 136, 88, 23, 39, 150, 0], [104, 125, 163, 166, 127, 57, 159, 0], [34, 162, 65, 82, 144, 49, 65, 72]], ![[0, 0, 0, 0, 0, 0, 0, 1], [118, 105, 127, 128, 116, 0, 141, 66], [157, 160, 2, 153, 142, 1, 0, 14], [149, 124, 101, 124, 107, 142, 138, 89], [70, 77, 81, 31, 23, 165, 76, 29], [10, 49, 31, 34, 28, 38, 73, 77], [34, 162, 65, 82, 144, 49, 65, 72], [60, 82, 98, 159, 12, 85, 75, 155]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![72, 58, 159, 45, 45, 67, 65, 0], ![52, 31, 35, 61, 160, 39, 10, 0], ![50, 166, 21, 67, 81, 140, 101, 0], ![19, 78, 28, 72, 61, 37, 2, 0], ![165, 144, 133, 84, 58, 114, 116, 0], ![124, 146, 10, 80, 9, 3, 166, 0], ![153, 41, 163, 13, 150, 134, 38, 166]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5, 6, 7]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [167]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 167 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M167
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [167] D q hq hbad)
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

end VoightMaximalOrderD8R96

namespace VoightMaximalOrderD8R104

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1928580625, [1, 2, -11, -15, 16, 11, -7, -2, 1], 2⟩
local notation "l" => [1, 2, -11, -15, 16, 11, -7, -2, 1]
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

def basisDenominator : ℤ := 2
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![2, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 0, 0], ![0, 0, 0, 2, 0, 0, 0, 0], ![0, 0, 0, 0, 2, 0, 0, 0], ![0, 0, 0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 0, 2, 0], ![1, 1, 0, 1, 1, 0, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-1, -1, 0, -1, -1, 0, -1, 2], ![-2, -2, 6, 6, -9, -5, 2, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-1, -1, 0, -1, -1, 0, -1, 2], ![-3, -4, 11, 13, -18, -11, 5, 4], ![-8, -10, 16, 22, -23, -24, -1, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-1, -1, 0, -1, -1, 0, -1, 2], ![-3, -4, 11, 13, -18, -11, 5, 4], ![-13, -16, 20, 30, -28, -38, -8, 22], ![-25, -33, 68, 95, -94, -88, 3, 37]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-1, -1, 0, -1, -1, 0, -1, 2], ![-3, -4, 11, 13, -18, -11, 5, 4], ![-13, -16, 20, 30, -28, -38, -8, 22], ![-36, -49, 116, 160, -160, -138, 14, 50], ![-77, -102, 189, 287, -241, -279, -17, 117]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-1, -1, 0, -1, -1, 0, -1, 2], ![-3, -4, 11, 13, -18, -11, 5, 4], ![-13, -16, 20, 30, -28, -38, -8, 22], ![-36, -49, 116, 160, -160, -138, 14, 50], ![-114, -150, 251, 402, -304, -410, -52, 178], ![-217, -294, 600, 908, -749, -826, -28, 317]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-1, -1, 0, -1, -1, 0, -1, 2], ![-3, -4, 11, 13, -18, -11, 5, 4], ![-13, -16, 20, 30, -28, -38, -8, 22], ![-36, -49, 116, 160, -160, -138, 14, 50], ![-114, -150, 251, 402, -304, -410, -52, 178], ![-304, -418, 918, 1371, -1148, -1194, -2, 430], ![-606, -823, 1608, 2530, -1917, -2334, -164, 895]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-2, -2, 6, 6, -9, -5, 2, 3], ![-8, -10, 16, 22, -23, -24, -1, 13], ![-25, -33, 68, 95, -94, -88, 3, 37], ![-77, -102, 189, 287, -241, -279, -17, 117], ![-217, -294, 600, 908, -749, -826, -28, 317], ![-606, -823, 1608, 2530, -1917, -2334, -164, 895], ![-1168, -1596, 3209, 5030, -3811, -4549, -278, 1705]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-2]], ![[], [], [], [], [], [], [-4], [-6, -2]], ![[], [], [], [], [], [-4], [-8, -4], [-26, -6, -2]], ![[], [], [], [], [-4], [-8, -4], [-44, -8, -4], [-74, -26, -6, -2]], ![[], [], [], [-4], [-8, -4], [-44, -8, -4], [-100, -44, -8, -4], [-234, -74, -26, -6, -2]], ![[], [], [-4], [-8, -4], [-44, -8, -4], [-100, -44, -8, -4], [-356, -100, -44, -8, -4], [-634, -234, -74, -26, -6, -2]], ![[], [-2], [-6, -2], [-26, -6, -2], [-74, -26, -6, -2], [-234, -74, -26, -6, -2], [-634, -234, -74, -26, -6, -2], [-1263, -450, -158, -51, -16, -4, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-1, -1, 0, -1, -1, 0, -1, 2], [-2, -2, 6, 6, -9, -5, 2, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-1, -1, 0, -1, -1, 0, -1, 2], [-3, -4, 11, 13, -18, -11, 5, 4], [-8, -10, 16, 22, -23, -24, -1, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-1, -1, 0, -1, -1, 0, -1, 2], [-3, -4, 11, 13, -18, -11, 5, 4], [-13, -16, 20, 30, -28, -38, -8, 22], [-25, -33, 68, 95, -94, -88, 3, 37]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-1, -1, 0, -1, -1, 0, -1, 2], [-3, -4, 11, 13, -18, -11, 5, 4], [-13, -16, 20, 30, -28, -38, -8, 22], [-36, -49, 116, 160, -160, -138, 14, 50], [-77, -102, 189, 287, -241, -279, -17, 117]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-1, -1, 0, -1, -1, 0, -1, 2], [-3, -4, 11, 13, -18, -11, 5, 4], [-13, -16, 20, 30, -28, -38, -8, 22], [-36, -49, 116, 160, -160, -138, 14, 50], [-114, -150, 251, 402, -304, -410, -52, 178], [-217, -294, 600, 908, -749, -826, -28, 317]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-1, -1, 0, -1, -1, 0, -1, 2], [-3, -4, 11, 13, -18, -11, 5, 4], [-13, -16, 20, 30, -28, -38, -8, 22], [-36, -49, 116, 160, -160, -138, 14, 50], [-114, -150, 251, 402, -304, -410, -52, 178], [-304, -418, 918, 1371, -1148, -1194, -2, 430], [-606, -823, 1608, 2530, -1917, -2334, -164, 895]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-2, -2, 6, 6, -9, -5, 2, 3], [-8, -10, 16, 22, -23, -24, -1, 13], [-25, -33, 68, 95, -94, -88, 3, 37], [-77, -102, 189, 287, -241, -279, -17, 117], [-217, -294, 600, 908, -749, -826, -28, 317], [-606, -823, 1608, 2530, -1917, -2334, -164, 895], [-1168, -1596, 3209, 5030, -3811, -4549, -278, 1705]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp239 : Fact (Nat.Prime 239) := fact_iff.2 (by norm_num)
instance hp12911 : Fact (Nat.Prime 12911) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2]
  b' := [2, 2]
  k := [1]
  f := [3, 6, 7, 11, 5, 1, 5, 2]
  g := [4, 4, 1, 4, 1]
  h := [4, 4, 1, 4, 1]
  a := [2, 4, 2]
  b := [0, 4, 0, 1, 3, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD239 : CertificateDedekindCriterionLists l 239 where
  n := 2
  a' := [30, 199, 8, 72, 0, 179]
  b' := [226, 34, 204, 59, 17, 195, 111]
  k := [45, 85, 73, 86, 81, 201, 1]
  f := [7, 11, 16, 15, 9, 9, 17, 1]
  g := [93, 141, 204, 187, 110, 114, 219, 1]
  h := [18, 1]
  a := [188, 118, 102, 237, 167, 89, 222]
  b := [230, 147, 41, 198, 165, 62, 17]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD12911 : CertificateDedekindCriterionLists l 12911 where
  n := 2
  a' := [5013, 12430, 11376, 5089, 3898, 4264]
  b' := [4077, 8075, 778, 10112, 304, 5796, 8613]
  k := [8340, 8577, 7471, 8421, 8156, 10381, 1]
  f := [625, 434, 105, 4, 168, 1191, 1141, 1]
  g := [6384, 4428, 1069, 40, 1716, 12164, 11645, 1]
  h := [1264, 1]
  a := [11229, 11254, 1945, 5396, 4646, 10077, 10910]
  b := [6966, 8366, 1404, 11084, 7337, 3438, 2001]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 4
  p := ![2, 5, 239, 12911]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 239, 12911]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp5.out
    exact hp239.out
    exact hp12911.out
  a := [12851942, 211795382, -168108890, -270651375, 149675030, 72461882, -34696408]
  b := [9002674, -19720219, -71417500, 47315748, 53917745, -25932244, -10141998, 4337051]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 239 T_ofList CD239
    exact satisfiesDedekindCriterion_of_certificate_lists T l 12911 T_ofList CD12911

noncomputable def M2 : MaximalOrderCertificateOfUnramifiedLists 2 O Om hm where
  n := 8
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 1, 0], [0, 0, 0, 0, 1, 1, 0, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 1, 0], [1, 0, 1, 1, 0, 1, 1, 0], [0, 0, 0, 0, 1, 0, 1, 1]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 1, 0], [1, 0, 1, 1, 0, 1, 1, 0], [1, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 1, 0, 0, 1, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 1, 0], [1, 0, 1, 1, 0, 1, 1, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [1, 0, 1, 1, 1, 1, 1, 1]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 1, 0], [1, 0, 1, 1, 0, 1, 1, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0, 1]], ![[0, 0, 0, 0, 0, 0, 1, 0], [1, 1, 0, 1, 1, 0, 1, 0], [1, 0, 1, 1, 0, 1, 1, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 1, 0, 0, 1]], ![[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1, 0, 1], [0, 0, 0, 0, 1, 0, 1, 1], [1, 1, 0, 1, 0, 0, 1, 1], [1, 0, 1, 1, 1, 1, 1, 1], [1, 0, 0, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 0, 0, 1], [0, 0, 1, 0, 1, 1, 0, 1]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 1, 1, 0], ![1, 1, 0, 1, 1, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 1, 1, 1, 1, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5, 6, 7]
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

end VoightMaximalOrderD8R104

end TraceEuclidean
