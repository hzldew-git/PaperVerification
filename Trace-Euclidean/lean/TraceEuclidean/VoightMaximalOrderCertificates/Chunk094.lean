import TraceEuclidean.VoightMaximalOrderCertificates.Chunk090
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

namespace VoightMaximalOrderD8R109

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1965663125, [5, 5, -19, -12, 22, 7, -9, -1, 1], 7⟩
local notation "l" => [5, 5, -19, -12, 22, 7, -9, -1, 1]
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

def basisDenominator : ℤ := 7
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![7, 0, 0, 0, 0, 0, 0, 0], ![0, 7, 0, 0, 0, 0, 0, 0], ![0, 0, 7, 0, 0, 0, 0, 0], ![0, 0, 0, 7, 0, 0, 0, 0], ![0, 0, 0, 0, 7, 0, 0, 0], ![0, 0, 0, 0, 0, 7, 0, 0], ![0, 0, 0, 0, 0, 0, 7, 0], ![6, 3, 3, 3, 6, 4, 4, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-6, -3, -3, -3, -6, -4, -4, 7], ![-5, -2, 1, 0, -7, -3, -1, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-6, -3, -3, -3, -6, -4, -4, 7], ![-11, -8, 16, 9, -28, -11, 5, 7], ![-19, -12, 6, 4, -29, -18, -4, 18]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-6, -3, -3, -3, -6, -4, -4, 7], ![-11, -8, 16, 9, -28, -11, 5, 7], ![-65, -40, -16, 1, -70, -69, -38, 70], ![-66, -43, 18, 18, -98, -67, -20, 62]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-6, -3, -3, -3, -6, -4, -4, 7], ![-11, -8, 16, 9, -28, -11, 5, 7], ![-65, -40, -16, 1, -70, -69, -38, 70], ![-122, -91, 144, 98, -261, -128, 13, 84], ![-190, -130, 79, 78, -296, -204, -49, 170]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-6, -3, -3, -3, -6, -4, -4, 7], ![-11, -8, 16, 9, -28, -11, 5, 7], ![-65, -40, -16, 1, -70, -69, -38, 70], ![-122, -91, 144, 98, -261, -128, 13, 84], ![-498, -329, -46, 105, -568, -565, -264, 511], ![-556, -383, 187, 226, -818, -610, -178, 507]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-6, -3, -3, -3, -6, -4, -4, 7], ![-11, -8, 16, 9, -28, -11, 5, 7], ![-65, -40, -16, 1, -70, -69, -38, 70], ![-122, -91, 144, 98, -261, -128, 13, 84], ![-498, -329, -46, 105, -568, -565, -264, 511], ![-971, -728, 974, 746, -1888, -1045, -20, 707], ![-1467, -1036, 658, 721, -2255, -1627, -405, 1289]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-5, -2, 1, 0, -7, -3, -1, 5], ![-19, -12, 6, 4, -29, -18, -4, 18], ![-66, -43, 18, 18, -98, -67, -20, 62], ![-190, -130, 79, 78, -296, -204, -49, 170], ![-556, -383, 187, 226, -818, -610, -178, 507], ![-1467, -1036, 658, 721, -2255, -1627, -405, 1289], ![-1931, -1351, 771, 885, -2906, -2134, -571, 1725]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-7]], ![[], [], [], [], [], [], [-49], [-35, -7]], ![[], [], [], [], [], [-49], [-49, -49], [-126, -35, -7]], ![[], [], [], [], [-49], [-49, -49], [-490, -49, -49], [-434, -126, -35, -7]], ![[], [], [], [-49], [-49, -49], [-490, -49, -49], [-588, -490, -49, -49], [-1190, -434, -126, -35, -7]], ![[], [], [-49], [-49, -49], [-490, -49, -49], [-588, -490, -49, -49], [-3577, -588, -490, -49, -49], [-3549, -1190, -434, -126, -35, -7]], ![[], [-7], [-35, -7], [-126, -35, -7], [-434, -126, -35, -7], [-1190, -434, -126, -35, -7], [-3549, -1190, -434, -126, -35, -7], [-4441, -1561, -523, -160, -42, -9, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-6, -3, -3, -3, -6, -4, -4, 7], [-5, -2, 1, 0, -7, -3, -1, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-6, -3, -3, -3, -6, -4, -4, 7], [-11, -8, 16, 9, -28, -11, 5, 7], [-19, -12, 6, 4, -29, -18, -4, 18]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-6, -3, -3, -3, -6, -4, -4, 7], [-11, -8, 16, 9, -28, -11, 5, 7], [-65, -40, -16, 1, -70, -69, -38, 70], [-66, -43, 18, 18, -98, -67, -20, 62]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-6, -3, -3, -3, -6, -4, -4, 7], [-11, -8, 16, 9, -28, -11, 5, 7], [-65, -40, -16, 1, -70, -69, -38, 70], [-122, -91, 144, 98, -261, -128, 13, 84], [-190, -130, 79, 78, -296, -204, -49, 170]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-6, -3, -3, -3, -6, -4, -4, 7], [-11, -8, 16, 9, -28, -11, 5, 7], [-65, -40, -16, 1, -70, -69, -38, 70], [-122, -91, 144, 98, -261, -128, 13, 84], [-498, -329, -46, 105, -568, -565, -264, 511], [-556, -383, 187, 226, -818, -610, -178, 507]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-6, -3, -3, -3, -6, -4, -4, 7], [-11, -8, 16, 9, -28, -11, 5, 7], [-65, -40, -16, 1, -70, -69, -38, 70], [-122, -91, 144, 98, -261, -128, 13, 84], [-498, -329, -46, 105, -568, -565, -264, 511], [-971, -728, 974, 746, -1888, -1045, -20, 707], [-1467, -1036, 658, 721, -2255, -1627, -405, 1289]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-5, -2, 1, 0, -7, -3, -1, 5], [-19, -12, 6, 4, -29, -18, -4, 18], [-66, -43, 18, 18, -98, -67, -20, 62], [-190, -130, 79, 78, -296, -204, -49, 170], [-556, -383, 187, 226, -818, -610, -178, 507], [-1467, -1036, 658, 721, -2255, -1627, -405, 1289], [-1931, -1351, 771, 885, -2906, -2134, -571, 1725]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp1279 : Fact (Nat.Prime 1279) := fact_iff.2 (by norm_num)
instance hp2459 : Fact (Nat.Prime 2459) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 2, 4]
  b' := [4, 4, 4, 4]
  k := [1]
  f := [-1, -1, 7, 4, -1, 1, 3, 1]
  g := [0, 4, 1, 2, 1]
  h := [0, 4, 1, 2, 1]
  a := [4, 4, 0, 2]
  b := [2, 1, 2, 1, 0, 3, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1279 : CertificateDedekindCriterionLists l 1279 where
  n := 2
  a' := [905, 1009, 525, 963, 1052, 424]
  b' := [142, 458, 937, 790, 977, 883, 853]
  k := [460, 974, 384, 793, 508, 1192, 1]
  f := [20, 5, 29, 42, 31, 21, 42, 1]
  g := [595, 135, 859, 1229, 894, 604, 1235, 1]
  h := [43, 1]
  a := [677, 627, 30, 2, 994, 1002, 510]
  b := [721, 562, 110, 962, 579, 1182, 769]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2459 : CertificateDedekindCriterionLists l 2459 where
  n := 2
  a' := [1255, 857, 1706, 1023, 1086, 529]
  b' := [500, 129, 721, 2045, 365, 1942, 627]
  k := [370, 44, 1720, 1784, 1548, 2197, 1]
  f := [865, 661, 407, 513, 1195, 987, 608, 1]
  g := [1564, 1194, 735, 927, 2160, 1783, 1098, 1]
  h := [1360, 1]
  a := [2198, 670, 904, 2270, 1386, 1421, 863]
  b := [2204, 1307, 2306, 2259, 1932, 960, 1596]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [7] where
  n := 4
  p := ![5, 7, 1279, 2459]
  exp := ![1, 2, 1, 1]
  pdgood := [5, 1279, 2459]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp7.out
    exact hp1279.out
    exact hp2459.out
  a := [45454639, 1354818688, -4251524998, -1799754430, 4200730652, 447788500, -706329952]
  b := [108653350, -574507867, -514521731, 1349560818, 397663988, -726406790, -67009968, 88291244]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1279 T_ofList CD1279
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2459 T_ofList CD2459

noncomputable def M7 : MaximalOrderCertificateOfUnramifiedLists 7 O Om hm where
  n := 8
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [1, 4, 4, 4, 1, 3, 3, 0], [2, 5, 1, 0, 0, 4, 6, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [1, 4, 4, 4, 1, 3, 3, 0], [3, 6, 2, 2, 0, 3, 5, 0], [2, 2, 6, 4, 6, 3, 3, 4]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [1, 4, 4, 4, 1, 3, 3, 0], [3, 6, 2, 2, 0, 3, 5, 0], [5, 2, 5, 1, 0, 1, 4, 0], [4, 6, 4, 4, 0, 3, 1, 6]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [1, 4, 4, 4, 1, 3, 3, 0], [3, 6, 2, 2, 0, 3, 5, 0], [5, 2, 5, 1, 0, 1, 4, 0], [4, 0, 4, 0, 5, 5, 6, 0], [6, 3, 2, 1, 5, 6, 0, 2]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [1, 4, 4, 4, 1, 3, 3, 0], [3, 6, 2, 2, 0, 3, 5, 0], [5, 2, 5, 1, 0, 1, 4, 0], [4, 0, 4, 0, 5, 5, 6, 0], [6, 0, 3, 0, 6, 2, 2, 0], [4, 2, 5, 2, 1, 6, 4, 3]], ![[0, 0, 0, 0, 0, 0, 1, 0], [1, 4, 4, 4, 1, 3, 3, 0], [3, 6, 2, 2, 0, 3, 5, 0], [5, 2, 5, 1, 0, 1, 4, 0], [4, 0, 4, 0, 5, 5, 6, 0], [6, 0, 3, 0, 6, 2, 2, 0], [2, 0, 1, 4, 2, 5, 1, 0], [3, 0, 0, 0, 6, 4, 1, 1]], ![[0, 0, 0, 0, 0, 0, 0, 1], [2, 5, 1, 0, 0, 4, 6, 5], [2, 2, 6, 4, 6, 3, 3, 4], [4, 6, 4, 4, 0, 3, 1, 6], [6, 3, 2, 1, 5, 6, 0, 2], [4, 2, 5, 2, 1, 6, 4, 3], [3, 0, 0, 0, 6, 4, 1, 1], [1, 0, 1, 3, 6, 1, 3, 3]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![3, 1, 6, 5, 6, 2, 2, 0], ![4, 2, 6, 5, 2, 3, 0, 0], ![0, 6, 5, 3, 3, 1, 6, 0], ![4, 6, 6, 4, 5, 6, 4, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![1, 3, 1, 5, 0, 0, 0, 0], ![0, 5, 3, 4, 6, 2, 5, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5, 6, 7]
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

end VoightMaximalOrderD8R109

namespace VoightMaximalOrderD8R120

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2051578125, [1, 6, -11, -28, 14, 19, -9, -2, 1], 9⟩
local notation "l" => [1, 6, -11, -28, 14, 19, -9, -2, 1]
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
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![3, 0, 0, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0, 0, 0], ![0, 0, 0, 3, 0, 0, 0, 0], ![0, 0, 0, 0, 3, 0, 0, 0], ![0, 0, 0, 0, 0, 3, 0, 0], ![1, 2, 1, 2, 2, 0, 1, 0], ![2, 2, 1, 2, 0, 2, 2, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![-1, -2, -1, -2, -2, 0, 3, 0], ![0, 1, 1, 1, 2, 0, -2, 1], ![-4, -6, 2, 5, -6, -9, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![-1, -2, -1, -2, -2, 0, 3, 0], ![0, 2, 1, 2, 4, -2, -6, 3], ![-4, -8, 1, 4, -9, -7, 7, 2], ![-7, -7, 14, 43, 5, -42, -21, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![-1, -2, -1, -2, -2, 0, 3, 0], ![0, 2, 1, 2, 4, -2, -6, 3], ![-10, -20, 4, 14, -24, -23, 15, 6], ![-1, 5, 10, 32, 20, -27, -29, 15], ![-34, -58, 52, 172, -29, -166, -27, 55]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![-1, -2, -1, -2, -2, 0, 3, 0], ![0, 2, 1, 2, 4, -2, -6, 3], ![-10, -20, 4, 14, -24, -23, 15, 6], ![-1, 15, 30, 95, 54, -78, -81, 39], ![-33, -66, 33, 110, -62, -115, 22, 31], ![-54, -59, 191, 632, 120, -524, -279, 193]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![-1, -2, -1, -2, -2, 0, 3, 0], ![0, 2, 1, 2, 4, -2, -6, 3], ![-10, -20, 4, 14, -24, -23, 15, 6], ![-1, 15, 30, 95, 54, -78, -81, 39], ![-78, -160, 90, 300, -145, -297, 45, 75], ![-9, 33, 133, 440, 198, -341, -296, 146], ![-248, -443, 572, 1925, -36, -1617, -435, 493]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![0, 1, 1, 1, 2, 0, -2, 1], ![-4, -8, 1, 4, -9, -7, 7, 2], ![-1, 5, 10, 32, 20, -27, -29, 15], ![-33, -66, 33, 110, -62, -115, 22, 31], ![-9, 33, 133, 440, 198, -341, -296, 146], ![-105, -209, 153, 513, -145, -469, -1, 128], ![-182, -220, 743, 2499, 502, -1971, -1043, 687]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-4, -6, 2, 5, -6, -9, 3, 4], ![-7, -7, 14, 43, 5, -42, -21, 19], ![-34, -58, 52, 172, -29, -166, -27, 55], ![-54, -59, 191, 632, 120, -524, -279, 193], ![-248, -443, 572, 1925, -36, -1617, -435, 493], ![-182, -220, 743, 2499, 502, -1971, -1043, 687], ![-988, -1656, 3118, 10591, 1027, -8358, -3249, 2615]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-3]], ![[], [], [], [], [], [], [-3], [-12, -3]], ![[], [], [], [], [], [-9], [-6, -3], [-57, -12, -3]], ![[], [], [], [], [-9], [-18, -9], [-45, -6, -3], [-165, -57, -12, -3]], ![[], [], [], [-9], [-18, -9], [-117, -18, -9], [-93, -45, -6, -3], [-579, -165, -57, -12, -3]], ![[], [], [-3], [-6, -3], [-45, -6, -3], [-93, -45, -6, -3], [-181, -37, -17, -2, -1], [-647, -240, -65, -21, -4, -1]], ![[], [-3], [-12, -3], [-57, -12, -3], [-165, -57, -12, -3], [-579, -165, -57, -12, -3], [-647, -240, -65, -21, -4, -1], [-2953, -998, -343, -101, -29, -6, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [-1, -2, -1, -2, -2, 0, 3, 0], [0, 1, 1, 1, 2, 0, -2, 1], [-4, -6, 2, 5, -6, -9, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [-1, -2, -1, -2, -2, 0, 3, 0], [0, 2, 1, 2, 4, -2, -6, 3], [-4, -8, 1, 4, -9, -7, 7, 2], [-7, -7, 14, 43, 5, -42, -21, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [-1, -2, -1, -2, -2, 0, 3, 0], [0, 2, 1, 2, 4, -2, -6, 3], [-10, -20, 4, 14, -24, -23, 15, 6], [-1, 5, 10, 32, 20, -27, -29, 15], [-34, -58, 52, 172, -29, -166, -27, 55]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [-1, -2, -1, -2, -2, 0, 3, 0], [0, 2, 1, 2, 4, -2, -6, 3], [-10, -20, 4, 14, -24, -23, 15, 6], [-1, 15, 30, 95, 54, -78, -81, 39], [-33, -66, 33, 110, -62, -115, 22, 31], [-54, -59, 191, 632, 120, -524, -279, 193]], ![[0, 0, 0, 0, 0, 1, 0, 0], [-1, -2, -1, -2, -2, 0, 3, 0], [0, 2, 1, 2, 4, -2, -6, 3], [-10, -20, 4, 14, -24, -23, 15, 6], [-1, 15, 30, 95, 54, -78, -81, 39], [-78, -160, 90, 300, -145, -297, 45, 75], [-9, 33, 133, 440, 198, -341, -296, 146], [-248, -443, 572, 1925, -36, -1617, -435, 493]], ![[0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 2, 0, -2, 1], [-4, -8, 1, 4, -9, -7, 7, 2], [-1, 5, 10, 32, 20, -27, -29, 15], [-33, -66, 33, 110, -62, -115, 22, 31], [-9, 33, 133, 440, 198, -341, -296, 146], [-105, -209, 153, 513, -145, -469, -1, 128], [-182, -220, 743, 2499, 502, -1971, -1043, 687]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-4, -6, 2, 5, -6, -9, 3, 4], [-7, -7, 14, 43, 5, -42, -21, 19], [-34, -58, 52, 172, -29, -166, -27, 55], [-54, -59, 191, 632, 120, -524, -279, 193], [-248, -443, 572, 1925, -36, -1617, -435, 493], [-182, -220, 743, 2499, 502, -1971, -1043, 687], [-988, -1656, 3118, 10591, 1027, -8358, -3249, 2615]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1621 : Fact (Nat.Prime 1621) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 4
  a' := [3]
  b' := [1, 1]
  k := [1]
  f := [1, 2, 6, 10, 0, -2, 3, 1]
  g := [3, 2, 1]
  h := [2, 4, 3, 4, 1, 1, 1]
  a := [1]
  b := [0, 1, 4, 2, 4, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1621 : CertificateDedekindCriterionLists l 1621 where
  n := 2
  a' := [1616, 723, 271, 1573, 1594, 386]
  b' := [836, 1457, 858, 381, 462, 345, 408]
  k := [708, 221, 1595, 870, 1021, 1444, 1]
  f := [195, 778, 659, 850, 135, 517, 400, 1]
  g := [352, 1404, 1188, 1533, 242, 933, 721, 1]
  h := [898, 1]
  a := [1475, 880, 1012, 478, 1026, 405, 1620]
  b := [546, 181, 591, 1615, 142, 895, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
  n := 3
  p := ![3, 5, 1621]
  exp := ![3, 1, 1]
  pdgood := [5, 1621]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp5.out
    exact hp1621.out
  a := [53733, 579250, -394157, -874468, 620826, 127020, -101680]
  b := [27517, -49379, -210865, 131311, 180714, -107792, -19055, 12710]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1621 T_ofList CD1621

noncomputable def M3 : MaximalOrderCertificateLists 3 O Om hm where
  m := 4
  n := 4
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [2, 1, 2, 1, 1, 0, 0, 0], [0, 1, 1, 1, 2, 0, 1, 1], [2, 0, 2, 2, 0, 0, 0, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [2, 1, 2, 1, 1, 0, 0, 0], [0, 2, 1, 2, 1, 1, 0, 0], [2, 1, 1, 1, 0, 2, 1, 2], [2, 2, 2, 1, 2, 0, 0, 1]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [2, 1, 2, 1, 1, 0, 0, 0], [0, 2, 1, 2, 1, 1, 0, 0], [2, 1, 1, 2, 0, 1, 0, 0], [2, 2, 1, 2, 2, 0, 1, 0], [2, 2, 1, 1, 1, 2, 0, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [2, 1, 2, 1, 1, 0, 0, 0], [0, 2, 1, 2, 1, 1, 0, 0], [2, 1, 1, 2, 0, 1, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, 2, 1, 2, 1, 1], [0, 1, 2, 2, 0, 1, 0, 1]], ![[0, 0, 0, 0, 0, 1, 0, 0], [2, 1, 2, 1, 1, 0, 0, 0], [0, 2, 1, 2, 1, 1, 0, 0], [2, 1, 1, 2, 0, 1, 0, 0], [2, 0, 0, 2, 0, 0, 0, 0], [0, 2, 0, 0, 2, 0, 0, 0], [0, 0, 1, 2, 0, 1, 1, 2], [1, 1, 2, 2, 0, 0, 0, 1]], ![[0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 2, 0, 1, 1], [2, 1, 1, 1, 0, 2, 1, 2], [2, 2, 1, 2, 2, 0, 1, 0], [0, 0, 0, 2, 1, 2, 1, 1], [0, 0, 1, 2, 0, 1, 1, 2], [0, 1, 0, 0, 2, 2, 2, 2], [1, 2, 2, 0, 1, 0, 1, 0]], ![[0, 0, 0, 0, 0, 0, 0, 1], [2, 0, 2, 2, 0, 0, 0, 1], [2, 2, 2, 1, 2, 0, 0, 1], [2, 2, 1, 1, 1, 2, 0, 1], [0, 1, 2, 2, 0, 1, 0, 1], [1, 1, 2, 2, 0, 0, 0, 1], [1, 2, 2, 0, 1, 0, 1, 0], [2, 0, 1, 1, 1, 0, 0, 2]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![1, 1, 0, 1, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 0, 0, 0], ![2, 2, 1, 0, 0, 1, 0, 0], ![2, 2, 1, 0, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 0, 1, 0], ![2, 2, 0, 0, 0, 0, 0, 0]]
  v := ![![1, 1, 0, 1, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 0, 0, 0], ![2, 2, 1, 0, 0, 1, 0, 0], ![2, 2, 1, 0, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 0, 1, 0], ![2, 2, 0, 0, 0, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 1, 2, 1, 1], ![0, 0, 1, 0, 0, 2, 1, 1], ![0, 0, 0, 1, 0, 0, 0, 0]]
  v_ind := ![3, 4, 5, 7]
  w_ind := ![0, 1, 2, 3]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0, 0, 0], ![2, 4, 2, 0, 4, 2, 0, 4], ![4, 2, 2, 0, 0, 0, 0, 0], ![2, 2, 0, 4, 4, 0, 4, 2], ![4, 0, 2, 4, 2, 0, 0, 0], ![4, 0, 0, 2, 2, 4, 0, 0], ![4, 2, 0, 0, 4, 2, 0, 0], ![4, 4, 2, 0, 0, 0, 0, 2]]
  a := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![744, -168, -746, 264], ![2960, 484, -2544, 972], ![8884, -244, -7608, 2406], ![49056, 4476, -39114, 12396]], ![![6, 2, 2, 0], ![0, 2, 2, 0], ![6, 6, 0, 6], ![102, 0, -102, 50]], ![![492, 36, -462, 196], ![1878, -120, -1728, 604], ![6174, 810, -5136, 1824], ![34536, 4388, -27514, 9054]], ![![6, 6, 0, 6], ![30, -30, -48, 24], ![258, 30, -240, 108], ![2046, 144, -1788, 648]], ![![54, -96, -90, 30], ![408, 186, -366, 186], ![1410, -516, -1380, 402], ![9300, 42, -7842, 2484]], ![![36, -30, -48, 24], ![240, 12, -246, 108], ![966, -78, -894, 312], ![6378, 396, -5340, 1776]], ![![360, -66, -348, 120], ![1362, 240, -1146, 432], ![3960, -84, -3354, 1050], ![21402, 2028, -16956, 5346]]]
  c := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![-18, 322, -350, 17], ![174, 1090, -1516, -108], ![216, 3378, -4052, -58], ![2526, 17266, -22286, -1326]], ![![0, 0, 0, -1], ![0, -2, 4, -1], ![0, 2, -4, -2], ![0, 44, -56, -2]], ![![18, 188, -248, -16], ![24, 752, -898, -4], ![342, 2224, -2994, -200], ![2004, 12064, -16026, -1123]], ![![2, -4, 4, -4], ![-6, 16, -10, 2], ![12, 98, -134, -11], ![84, 774, -1008, -45]], ![![-18, 34, -12, 13], ![44, 146, -250, -35], ![-66, 622, -604, 68], ![294, 3478, -4260, -106]], ![![-6, 18, -14, 2], ![6, 100, -132, -5], ![8, 392, -464, 2], ![270, 2350, -3006, -130]], ![![-6, 152, -168, 7], ![84, 494, -690, -53], ![102, 1494, -1794, -30], ![1124, 7488, -9674, -597]]]
  d := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 12, 6, 12], ![35016, 6570, -28152, 10008], ![34500, 6504, -27636, 9762], ![108, -144, -180, 120]], ![![0, 0, 0, 0], ![42, -30, -42, 18], ![36, -36, -42, 18], ![12, 0, 0, 0]], ![![12, 12, 0, 6], ![23436, 576, -19806, 6492], ![23148, 678, -19482, 6354], ![108, 24, -84, 84]], ![![12, 6, 0, 0], ![1044, -198, -1032, 378], ![1056, -192, -1044, 378], ![36, 36, 12, 0]], ![![6, 6, 12, 0], ![6156, 2196, -4980, 2100], ![6144, 2160, -4962, 2064], ![-36, -24, 36, 0]], ![![0, 12, 6, 0], ![3954, 456, -3450, 1290], ![3960, 456, -3438, 1272], ![-24, 0, 36, 0]], ![![0, 0, 0, 6], ![15570, 3054, -12372, 4374], ![15300, 3018, -12120, 4260], ![72, -72, -108, 60]]]
  e := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![2, -8, 8, -6], ![2394, 12182, -17018, -1460], ![2372, 11974, -16726, -1437], ![-36, 56, -20, 4]], ![![2, 2, -2, 1], ![-4, 16, -2, -1], ![-6, 14, 0, 1], ![-4, 8, -8, 4]], ![![4, -10, 14, -5], ![830, 8702, -10826, -377], ![844, 8574, -10696, -381], ![4, 8, -4, -26]], ![![6, 0, 0, -3], ![-12, 438, -480, 9], ![-12, 444, -492, 12], ![12, -12, 12, -12]], ![![6, -6, 6, -6], ![606, 2088, -3318, -423], ![600, 2082, -3294, -411], ![0, -36, 60, -6]], ![![6, -6, 6, -3], ![198, 1476, -1980, -117], ![198, 1476, -1980, -114], ![0, -24, 36, -6]], ![![0, 0, 0, 0], ![1098, 5364, -7524, -678], ![1086, 5256, -7374, -666], ![-24, 48, -36, 12]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 0, Sum.inl 1), (Sum.inl 3, Sum.inl 1), (Sum.inl 0, Sum.inr 0), (Sum.inl 1, Sum.inr 0), (Sum.inl 2, Sum.inr 0), (Sum.inl 3, Sum.inr 0)]
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

end VoightMaximalOrderD8R120

namespace VoightMaximalOrderD8R131

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2152960000, [16, 0, -56, 0, 52, 0, -14, 0, 1], 4096⟩
local notation "l" => [16, 0, -56, 0, 52, 0, -14, 0, 1]
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

def basisDenominator : ℤ := 8
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![8, 0, 0, 0, 0, 0, 0, 0], ![0, 8, 0, 0, 0, 0, 0, 0], ![0, 0, 4, 0, 0, 0, 0, 0], ![0, 0, 0, 4, 0, 0, 0, 0], ![0, 0, 0, 0, 2, 0, 0, 0], ![0, 0, 0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 2, 0, 1, 0], ![0, 0, 0, 4, 0, 2, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 2, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, -2, 0, 2, 0], ![0, 0, 0, -1, 0, 0, 0, 1], ![-2, 0, 14, 0, -40, 0, 16, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, -1, 0, 1, 0], ![0, 0, 0, -1, 0, -1, 0, 1], ![-1, 0, 7, 0, -21, 0, 8, 0], ![0, -1, 0, -1, 0, -20, 0, 8]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 2, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, -2, 0, 2, 0], ![0, 0, 0, -1, 0, -1, 0, 1], ![-2, 0, 14, 0, -40, 0, 14, 0], ![0, -1, 0, -1, 0, -21, 0, 8], ![-16, 0, 110, 0, -282, 0, 88, 0]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, -1, 0, 1, 0], ![0, 0, 0, -1, 0, -1, 0, 1], ![-1, 0, 7, 0, -20, 0, 7, 0], ![0, -1, 0, 0, 0, -20, 0, 7], ![-8, 0, 55, 0, -140, 0, 43, 0], ![0, -8, 0, 11, 0, -141, 0, 44]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, -2, 0, 2, 0], ![0, 0, 0, -1, 0, -1, 0, 1], ![-2, 0, 14, 0, -40, 0, 14, 0], ![0, -1, 0, 0, 0, -20, 0, 7], ![-14, 0, 96, 0, -240, 0, 72, 0], ![0, -8, 0, 12, 0, -140, 0, 43], ![-88, 0, 600, 0, -1456, 0, 422, 0]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, -1, 0, 0, 0, 1], ![-1, 0, 7, 0, -21, 0, 8, 0], ![0, -1, 0, -1, 0, -21, 0, 8], ![-8, 0, 55, 0, -140, 0, 43, 0], ![0, -8, 0, 12, 0, -140, 0, 43], ![-51, 0, 348, 0, -848, 0, 247, 0], ![0, -52, 0, 100, 0, -869, 0, 255]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-2, 0, 14, 0, -40, 0, 16, 0], ![0, -1, 0, -1, 0, -20, 0, 8], ![-16, 0, 110, 0, -282, 0, 88, 0], ![0, -8, 0, 11, 0, -141, 0, 44], ![-88, 0, 600, 0, -1456, 0, 422, 0], ![0, -52, 0, 100, 0, -869, 0, 255], ![-526, 0, 3576, 0, -8544, 0, 2430, 0]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-8]], ![[], [], [], [], [], [], [-4], [0, -4]], ![[], [], [], [], [], [-8], [0, -4], [-64, 0, -4]], ![[], [], [], [], [-4], [0, -4], [-32, 0, -2], [0, -32, 0, -2]], ![[], [], [], [-8], [0, -4], [-56, 0, -4], [0, -32, 0, -2], [-352, 0, -32, 0, -2]], ![[], [], [-4], [0, -4], [-32, 0, -2], [0, -32, 0, -2], [-204, 0, -18, 0, -1], [0, -208, 0, -18, 0, -1]], ![[], [-8], [0, -4], [-64, 0, -4], [0, -32, 0, -2], [-352, 0, -32, 0, -2], [0, -208, 0, -18, 0, -1], [-2104, 0, -212, 0, -18, 0, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 2, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, -2, 0, 2, 0], [0, 0, 0, -1, 0, 0, 0, 1], [-2, 0, 14, 0, -40, 0, 16, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, -1, 0, 1, 0], [0, 0, 0, -1, 0, -1, 0, 1], [-1, 0, 7, 0, -21, 0, 8, 0], [0, -1, 0, -1, 0, -20, 0, 8]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, -2, 0, 2, 0], [0, 0, 0, -1, 0, -1, 0, 1], [-2, 0, 14, 0, -40, 0, 14, 0], [0, -1, 0, -1, 0, -21, 0, 8], [-16, 0, 110, 0, -282, 0, 88, 0]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, -1, 0, 1, 0], [0, 0, 0, -1, 0, -1, 0, 1], [-1, 0, 7, 0, -20, 0, 7, 0], [0, -1, 0, 0, 0, -20, 0, 7], [-8, 0, 55, 0, -140, 0, 43, 0], [0, -8, 0, 11, 0, -141, 0, 44]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, -2, 0, 2, 0], [0, 0, 0, -1, 0, -1, 0, 1], [-2, 0, 14, 0, -40, 0, 14, 0], [0, -1, 0, 0, 0, -20, 0, 7], [-14, 0, 96, 0, -240, 0, 72, 0], [0, -8, 0, 12, 0, -140, 0, 43], [-88, 0, 600, 0, -1456, 0, 422, 0]], ![[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, -1, 0, 0, 0, 1], [-1, 0, 7, 0, -21, 0, 8, 0], [0, -1, 0, -1, 0, -21, 0, 8], [-8, 0, 55, 0, -140, 0, 43, 0], [0, -8, 0, 12, 0, -140, 0, 43], [-51, 0, 348, 0, -848, 0, 247, 0], [0, -52, 0, 100, 0, -869, 0, 255]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-2, 0, 14, 0, -40, 0, 16, 0], [0, -1, 0, -1, 0, -20, 0, 8], [-16, 0, 110, 0, -282, 0, 88, 0], [0, -8, 0, 11, 0, -141, 0, 44], [-88, 0, 600, 0, -1456, 0, 422, 0], [0, -52, 0, 100, 0, -869, 0, 255], [-526, 0, 3576, 0, -8544, 0, 2430, 0]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 0, 3]
  b' := [0, 1, 0, 3]
  k := [1]
  f := [0, 0, 16, 0, -7, 0, 4]
  g := [4, 0, 3, 0, 1]
  h := [4, 0, 3, 0, 1]
  a := [0, 0, 3]
  b := [4, 0, 2, 0, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [11, 0, 26, 0, 17]
  b' := [0, 5, 0, 14, 0, 2]
  k := [4, 0, 11, 0, 1]
  f := [0, 0, 4, 0, 0, 0, 1]
  g := [8, 0, 26, 0, 13, 0, 1]
  h := [2, 0, 1]
  a := [2, 0, 5, 0, 26]
  b := [11, 0, 14, 0, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 3
  p := ![2, 5, 29]
  exp := ![6, 1, 1]
  pdgood := [5, 29]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp5.out
    exact hp29.out
  a := [580, 0, -9464, 0, 4908, 0, -504]
  b := [0, -1642, 0, 2653, 0, -834, 0, 63]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 4
  n := 4
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 1, 0, 1, 0, 1], [1, 0, 1, 0, 1, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 1, 0, 1, 0, 1], [1, 0, 1, 0, 0, 0, 1, 0], [0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 1, 0, 0]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]], ![[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0, 0, 1], [1, 0, 1, 0, 1, 0, 0, 0], [0, 1, 0, 1, 0, 1, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0, 1]], ![[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 0, 1, 0]]
  v := ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 0, 1, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0]]
  v_ind := ![1, 3, 5, 7]
  w_ind := ![0, 2, 4, 6]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 1]]
  a := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![0, -1, 0, 1], ![-1, -1, -21, 8], ![-8, 12, -140, 43], ![-52, 100, -869, 255]], ![![0, 0, 1, 0], ![0, -1, -1, 1], ![-1, 0, -20, 7], ![-8, 11, -141, 44]], ![![0, 1, 0, 0], ![0, 0, 1, 0], ![0, -1, -1, 1], ![-1, -1, -20, 8]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]
  c := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![-1, -1, 1, 0], ![-8, -19, 7, 0], ![-44, -121, 48, -11], ![-264, -748, 307, -88]], ![![0, 1, 0, 0], ![-1, -1, 0, 1], ![-8, -20, 7, 0], ![-52, -141, 55, -11]], ![![-10, -21, 8, 1], ![-60, -160, 62, -11], ![-299, -849, 348, -100], ![-1742, -5020, 2095, -661]], ![![-10, -21, 7, 2], ![-60, -161, 62, -11], ![-298, -848, 348, -101], ![-1733, -5000, 2088, -662]]]
  d := ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2, 0, 2, 0], ![-2, 0, -38, 14], ![-14, 22, -280, 90], ![-14, 22, -278, 88]], ![![0, 2, 0, 0], ![0, -2, -2, 2], ![-2, 0, -40, 16], ![-2, 0, -42, 16]], ![![2, 0, 2, 2], ![-18, 22, -320, 102], ![-120, 220, -2058, 618], ![-118, 222, -2016, 600]], ![![0, 0, 2, 2], ![-18, 22, -322, 102], ![-122, 220, -2058, 616], ![-120, 224, -2016, 598]]]
  e := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![-1, 0, 0, 1], ![-51, -140, 55, -12], ![-308, -869, 355, -99], ![-299, -848, 348, -100]], ![![0, 1, 0, 0], ![-8, -20, 7, 0], ![-52, -140, 55, -11], ![-51, -139, 55, -12]], ![![0, 0, 1, -1], ![-1, -1, 0, 1], ![-9, -20, 8, 0], ![-9, -21, 8, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 2, Sum.inl 0), (Sum.inl 3, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 1, Sum.inr 0), (Sum.inl 2, Sum.inr 0), (Sum.inl 3, Sum.inr 0)]
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

end VoightMaximalOrderD8R131

namespace VoightMaximalOrderD8R138

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2262505625, [4, -6, -21, 9, 25, -2, -9, 0, 1], 2⟩
local notation "l" => [4, -6, -21, 9, 25, -2, -9, 0, 1]
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
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![2, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 0, 0], ![0, 0, 0, 2, 0, 0, 0, 0], ![0, 0, 0, 0, 2, 0, 0, 0], ![0, 0, 0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 0, 2, 0], ![0, 1, 1, 1, 0, 1, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, -1, -1, -1, 0, -1, 0, 2], ![-2, 3, 11, -4, -12, 1, 5, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, -1, -1, -1, 0, -1, 0, 2], ![-4, 6, 21, -9, -25, 2, 9, 0], ![0, -7, -2, 6, -4, -17, 1, 10]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, -1, -1, -1, 0, -1, 0, 2], ![-4, 6, 21, -9, -25, 2, 9, 0], ![0, -13, -3, 12, -9, -34, 2, 18], ![-20, 29, 102, -43, -114, 5, 33, 2]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, -1, -1, -1, 0, -1, 0, 2], ![-4, 6, 21, -9, -25, 2, 9, 0], ![0, -13, -3, 12, -9, -34, 2, 18], ![-36, 52, 183, -77, -204, 7, 56, 4], ![-4, -47, 18, 61, -67, -145, 15, 66]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, -1, -1, -1, 0, -1, 0, 2], ![-4, 6, 21, -9, -25, 2, 9, 0], ![0, -13, -3, 12, -9, -34, 2, 18], ![-36, 52, 183, -77, -204, 7, 56, 4], ![-8, -80, 40, 111, -125, -256, 27, 112], ![-132, 179, 664, -261, -731, -16, 185, 30]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![0, -1, -1, -1, 0, -1, 0, 2], ![-4, 6, 21, -9, -25, 2, 9, 0], ![0, -13, -3, 12, -9, -34, 2, 18], ![-36, 52, 183, -77, -204, 7, 56, 4], ![-8, -80, 40, 111, -125, -256, 27, 112], ![-224, 301, 1125, -435, -1233, -40, 304, 54], ![-60, -227, 324, 359, -621, -886, 134, 370]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-2, 3, 11, -4, -12, 1, 5, 0], ![0, -7, -2, 6, -4, -17, 1, 10], ![-20, 29, 102, -43, -114, 5, 33, 2], ![-4, -47, 18, 61, -67, -145, 15, 66], ![-132, 179, 664, -261, -731, -16, 185, 30], ![-60, -227, 324, 359, -621, -886, 134, 370], ![-447, 560, 2242, -796, -2471, -206, 594, 155]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-2]], ![[], [], [], [], [], [], [-4], [0, -2]], ![[], [], [], [], [], [-4], [0, -4], [-20, 0, -2]], ![[], [], [], [], [-4], [0, -4], [-36, 0, -4], [-4, -20, 0, -2]], ![[], [], [], [-4], [0, -4], [-36, 0, -4], [-8, -36, 0, -4], [-132, -4, -20, 0, -2]], ![[], [], [-4], [0, -4], [-36, 0, -4], [-8, -36, 0, -4], [-224, -8, -36, 0, -4], [-60, -132, -4, -20, 0, -2]], ![[], [-2], [0, -2], [-20, 0, -2], [-4, -20, 0, -2], [-132, -4, -20, 0, -2], [-60, -132, -4, -20, 0, -2], [-447, -33, -77, -2, -11, 0, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, -1, -1, -1, 0, -1, 0, 2], [-2, 3, 11, -4, -12, 1, 5, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, -1, -1, -1, 0, -1, 0, 2], [-4, 6, 21, -9, -25, 2, 9, 0], [0, -7, -2, 6, -4, -17, 1, 10]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, -1, -1, -1, 0, -1, 0, 2], [-4, 6, 21, -9, -25, 2, 9, 0], [0, -13, -3, 12, -9, -34, 2, 18], [-20, 29, 102, -43, -114, 5, 33, 2]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, -1, -1, -1, 0, -1, 0, 2], [-4, 6, 21, -9, -25, 2, 9, 0], [0, -13, -3, 12, -9, -34, 2, 18], [-36, 52, 183, -77, -204, 7, 56, 4], [-4, -47, 18, 61, -67, -145, 15, 66]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, -1, -1, -1, 0, -1, 0, 2], [-4, 6, 21, -9, -25, 2, 9, 0], [0, -13, -3, 12, -9, -34, 2, 18], [-36, 52, 183, -77, -204, 7, 56, 4], [-8, -80, 40, 111, -125, -256, 27, 112], [-132, 179, 664, -261, -731, -16, 185, 30]], ![[0, 0, 0, 0, 0, 0, 1, 0], [0, -1, -1, -1, 0, -1, 0, 2], [-4, 6, 21, -9, -25, 2, 9, 0], [0, -13, -3, 12, -9, -34, 2, 18], [-36, 52, 183, -77, -204, 7, 56, 4], [-8, -80, 40, 111, -125, -256, 27, 112], [-224, 301, 1125, -435, -1233, -40, 304, 54], [-60, -227, 324, 359, -621, -886, 134, 370]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-2, 3, 11, -4, -12, 1, 5, 0], [0, -7, -2, 6, -4, -17, 1, 10], [-20, 29, 102, -43, -114, 5, 33, 2], [-4, -47, 18, 61, -67, -145, 15, 66], [-132, 179, 664, -261, -731, -16, 185, 30], [-60, -227, 324, 359, -621, -886, 134, 370], [-447, 560, 2242, -796, -2471, -206, 594, 155]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp199 : Fact (Nat.Prime 199) := fact_iff.2 (by norm_num)
instance hp18191 : Fact (Nat.Prime 18191) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 0, 2]
  b' := [1, 2, 0, 2]
  k := [1]
  f := [1, 6, 11, 3, -2, 2, 3]
  g := [3, 4, 3, 0, 1]
  h := [3, 4, 3, 0, 1]
  a := [3, 3, 4, 1]
  b := [1, 0, 4, 4, 1, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD199 : CertificateDedekindCriterionLists l 199 where
  n := 2
  a' := [175, 19, 181, 69, 140, 196]
  b' := [75, 51, 125, 10, 167, 2, 171]
  k := [10, 108, 37, 128, 32, 188, 1]
  f := [29, 4, 7, 76, 56, 38, 50, 1]
  g := [55, 7, 13, 144, 105, 71, 94, 1]
  h := [105, 1]
  a := [180, 120, 52, 63, 132, 167, 160]
  b := [162, 178, 79, 73, 73, 107, 39]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD18191 : CertificateDedekindCriterionLists l 18191 where
  n := 2
  a' := [2468, 5036, 12738, 10622, 14343, 6674]
  b' := [421, 9973, 1621, 702, 2580, 10694, 4244]
  k := [18049, 4053, 1013, 11634, 11008, 13681, 1]
  f := [896, 929, 1797, 529, 491, 1206, 1976, 1]
  g := [7228, 7491, 14493, 4261, 3959, 9727, 15936, 1]
  h := [2255, 1]
  a := [9380, 11351, 5791, 11473, 11904, 9528, 14730]
  b := [16467, 2325, 15268, 368, 5988, 8399, 3461]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 4
  p := ![2, 5, 199, 18191]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 199, 18191]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp5.out
    exact hp199.out
    exact hp18191.out
  a := [25335011, 99411915, -212143698, -154804348, 179545962, 41090328, -35308536]
  b := [10856659, -35057014, -35259522, 69006021, 27597023, -32373771, -5136291, 4413567]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 199 T_ofList CD199
    exact satisfiesDedekindCriterion_of_certificate_lists T l 18191 T_ofList CD18191

noncomputable def M2 : MaximalOrderCertificateOfUnramifiedLists 2 O Om hm where
  n := 8
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 0, 1, 0, 0], [0, 1, 1, 0, 0, 1, 1, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 0, 1, 0, 0], [0, 0, 1, 1, 1, 0, 1, 0], [0, 1, 0, 0, 0, 1, 1, 0]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 0, 1, 0, 0], [0, 0, 1, 1, 1, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0, 0], [0, 1, 0, 1, 0, 1, 1, 0]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 0, 1, 0, 0], [0, 0, 1, 1, 1, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0, 0], [0, 0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 1, 1, 1, 1, 0]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 0, 1, 0, 0], [0, 0, 1, 1, 1, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0, 0], [0, 0, 1, 1, 0, 1, 0, 0], [0, 0, 0, 1, 1, 0, 1, 0], [0, 1, 0, 1, 1, 0, 1, 0]], ![[0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 1, 1, 0, 1, 0, 0], [0, 0, 1, 1, 1, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0, 0], [0, 0, 1, 1, 0, 1, 0, 0], [0, 0, 0, 1, 1, 0, 1, 0], [0, 1, 1, 1, 1, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0]], ![[0, 0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 0, 1, 1, 0], [0, 1, 0, 0, 0, 1, 1, 0], [0, 1, 0, 1, 0, 1, 1, 0], [0, 1, 0, 1, 1, 1, 1, 0], [0, 1, 0, 1, 1, 0, 1, 0], [0, 1, 0, 1, 1, 0, 0, 0], [1, 0, 0, 0, 1, 0, 0, 1]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 1, 1, 0, 1, 0], ![0, 1, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 1, 0], ![0, 1, 1, 1, 1, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![1, 1, 1, 1, 1, 0, 1, 1]]
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

end VoightMaximalOrderD8R138

end TraceEuclidean
