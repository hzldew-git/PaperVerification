import TraceEuclidean.VoightMaximalOrderCertificates.Chunk088
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

namespace VoightMaximalOrderD8R75

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1632593125, [-1, 3, 7, -23, 2, 18, -5, -3, 1], 3⟩
local notation "l" => [-1, 3, 7, -23, 2, 18, -5, -3, 1]
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
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![3, 0, 0, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0, 0, 0], ![0, 0, 0, 3, 0, 0, 0, 0], ![0, 0, 0, 0, 3, 0, 0, 0], ![0, 0, 0, 0, 0, 3, 0, 0], ![0, 0, 0, 0, 0, 0, 3, 0], ![2, 1, 0, 1, 1, 2, 2, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -1, 0, -1, -1, -2, -2, 3], ![-3, -2, -2, 6, -2, -9, -1, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -1, 0, -1, -1, -2, -2, 3], ![-5, -6, -7, 20, -5, -24, -1, 9], ![-13, -12, -12, 29, -3, -45, -12, 22]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -1, 0, -1, -1, -2, -2, 3], ![-5, -6, -7, 20, -5, -24, -1, 9], ![-25, -22, -24, 48, 3, -84, -31, 42], ![-42, -45, -56, 132, -3, -177, -43, 74]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -1, 0, -1, -1, -2, -2, 3], ![-5, -6, -7, 20, -5, -24, -1, 9], ![-25, -22, -24, 48, 3, -84, -31, 42], ![-64, -78, -106, 259, -5, -313, -64, 117], ![-136, -147, -193, 431, 27, -583, -165, 241]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -1, 0, -1, -1, -2, -2, 3], ![-5, -6, -7, 20, -5, -24, -1, 9], ![-25, -22, -24, 48, 3, -84, -31, 42], ![-64, -78, -106, 259, -5, -313, -64, 117], ![-223, -234, -312, 660, 89, -930, -302, 393], ![-393, -453, -629, 1418, 114, -1812, -494, 710]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -1, 0, -1, -1, -2, -2, 3], ![-5, -6, -7, 20, -5, -24, -1, 9], ![-25, -22, -24, 48, 3, -84, -31, 42], ![-64, -78, -106, 259, -5, -313, -64, 117], ![-223, -234, -312, 660, 89, -930, -302, 393], ![-575, -707, -1020, 2348, 176, -2844, -719, 1059], ![-1142, -1319, -1873, 4125, 492, -5288, -1534, 2068]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-3, -2, -2, 6, -2, -9, -1, 5], ![-13, -12, -12, 29, -3, -45, -12, 22], ![-42, -45, -56, 132, -3, -177, -43, 74], ![-136, -147, -193, 431, 27, -583, -165, 241], ![-393, -453, -629, 1418, 114, -1812, -494, 710], ![-1142, -1319, -1873, 4125, 492, -5288, -1534, 2068], ![-2129, -2494, -3570, 7908, 919, -10007, -2851, 3872]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-3]], ![[], [], [], [], [], [], [-9], [-15, -3]], ![[], [], [], [], [], [-9], [-27, -9], [-66, -15, -3]], ![[], [], [], [], [-9], [-27, -9], [-126, -27, -9], [-222, -66, -15, -3]], ![[], [], [], [-9], [-27, -9], [-126, -27, -9], [-351, -126, -27, -9], [-723, -222, -66, -15, -3]], ![[], [], [-9], [-27, -9], [-126, -27, -9], [-351, -126, -27, -9], [-1179, -351, -126, -27, -9], [-2130, -723, -222, -66, -15, -3]], ![[], [-3], [-15, -3], [-66, -15, -3], [-222, -66, -15, -3], [-723, -222, -66, -15, -3], [-2130, -723, -222, -66, -15, -3], [-4067, -1367, -439, -129, -34, -7, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-2, -1, 0, -1, -1, -2, -2, 3], [-3, -2, -2, 6, -2, -9, -1, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-2, -1, 0, -1, -1, -2, -2, 3], [-5, -6, -7, 20, -5, -24, -1, 9], [-13, -12, -12, 29, -3, -45, -12, 22]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-2, -1, 0, -1, -1, -2, -2, 3], [-5, -6, -7, 20, -5, -24, -1, 9], [-25, -22, -24, 48, 3, -84, -31, 42], [-42, -45, -56, 132, -3, -177, -43, 74]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-2, -1, 0, -1, -1, -2, -2, 3], [-5, -6, -7, 20, -5, -24, -1, 9], [-25, -22, -24, 48, 3, -84, -31, 42], [-64, -78, -106, 259, -5, -313, -64, 117], [-136, -147, -193, 431, 27, -583, -165, 241]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-2, -1, 0, -1, -1, -2, -2, 3], [-5, -6, -7, 20, -5, -24, -1, 9], [-25, -22, -24, 48, 3, -84, -31, 42], [-64, -78, -106, 259, -5, -313, -64, 117], [-223, -234, -312, 660, 89, -930, -302, 393], [-393, -453, -629, 1418, 114, -1812, -494, 710]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-2, -1, 0, -1, -1, -2, -2, 3], [-5, -6, -7, 20, -5, -24, -1, 9], [-25, -22, -24, 48, 3, -84, -31, 42], [-64, -78, -106, 259, -5, -313, -64, 117], [-223, -234, -312, 660, 89, -930, -302, 393], [-575, -707, -1020, 2348, 176, -2844, -719, 1059], [-1142, -1319, -1873, 4125, 492, -5288, -1534, 2068]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-3, -2, -2, 6, -2, -9, -1, 5], [-13, -12, -12, 29, -3, -45, -12, 22], [-42, -45, -56, 132, -3, -177, -43, 74], [-136, -147, -193, 431, 27, -583, -165, 241], [-393, -453, -629, 1418, 114, -1812, -494, 710], [-1142, -1319, -1873, 4125, 492, -5288, -1534, 2068], [-2129, -2494, -3570, 7908, 919, -10007, -2851, 3872]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp151 : Fact (Nat.Prime 151) := fact_iff.2 (by norm_num)
instance hp17299 : Fact (Nat.Prime 17299) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 2, 3]
  b' := [3, 2, 4, 3]
  k := [1]
  f := [1, 1, 1, 7, 2, -2, 2, 1]
  g := [2, 2, 2, 1, 1]
  h := [2, 2, 2, 1, 1]
  a := [0, 1, 0, 1]
  b := [3, 4, 0, 1, 4, 4, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD151 : CertificateDedekindCriterionLists l 151 where
  n := 2
  a' := [143, 142, 62, 23, 91, 80]
  b' := [146, 72, 55, 49, 59, 83, 118]
  k := [101, 102, 91, 125, 49, 127, 1]
  f := [45, 66, 44, 69, 64, 57, 36, 1]
  g := [79, 115, 76, 120, 111, 99, 62, 1]
  h := [86, 1]
  a := [25, 48, 24, 36, 134, 116, 106]
  b := [24, 129, 119, 32, 146, 73, 45]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD17299 : CertificateDedekindCriterionLists l 17299 where
  n := 2
  a' := [8929, 9101, 458, 6086, 472, 1725]
  b' := [14003, 9822, 15408, 8859, 13158, 10595, 12110]
  k := [6792, 2695, 2544, 9614, 10377, 721, 1]
  f := [14738, 16885, 15581, 16326, 6877, 8675, 352, 1]
  g := [15053, 17245, 15913, 16674, 7023, 8860, 359, 1]
  h := [16937, 1]
  a := [15337, 3261, 3299, 6687, 14659, 2731, 801]
  b := [3431, 14915, 8965, 1607, 8022, 2876, 16498]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
  n := 4
  p := ![3, 5, 151, 17299]
  exp := ![2, 1, 1, 1]
  pdgood := [5, 151, 17299]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp5.out
    exact hp151.out
    exact hp17299.out
  a := [722047107, 5869564994, -4131353423, -8290109930, 4097283632, 1969586500, -886389664]
  b := [279864604, -71560261, -2160625608, 898754171, 1720643471, -667401950, -287747828, 110798708]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 151 T_ofList CD151
    exact satisfiesDedekindCriterion_of_certificate_lists T l 17299 T_ofList CD17299

noncomputable def M3 : MaximalOrderCertificateOfUnramifiedLists 3 O Om hm where
  n := 8
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [1, 2, 0, 2, 2, 1, 1, 0], [0, 1, 1, 0, 1, 0, 2, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [1, 2, 0, 2, 2, 1, 1, 0], [1, 0, 2, 2, 1, 0, 2, 0], [2, 0, 0, 2, 0, 0, 0, 1]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [1, 2, 0, 2, 2, 1, 1, 0], [1, 0, 2, 2, 1, 0, 2, 0], [2, 2, 0, 0, 0, 0, 2, 0], [0, 0, 1, 0, 0, 0, 2, 2]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [1, 2, 0, 2, 2, 1, 1, 0], [1, 0, 2, 2, 1, 0, 2, 0], [2, 2, 0, 0, 0, 0, 2, 0], [2, 0, 2, 1, 1, 2, 2, 0], [2, 0, 2, 2, 0, 2, 0, 1]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [1, 2, 0, 2, 2, 1, 1, 0], [1, 0, 2, 2, 1, 0, 2, 0], [2, 2, 0, 0, 0, 0, 2, 0], [2, 0, 2, 1, 1, 2, 2, 0], [2, 0, 0, 0, 2, 0, 1, 0], [0, 0, 1, 2, 0, 0, 1, 2]], ![[0, 0, 0, 0, 0, 0, 1, 0], [1, 2, 0, 2, 2, 1, 1, 0], [1, 0, 2, 2, 1, 0, 2, 0], [2, 2, 0, 0, 0, 0, 2, 0], [2, 0, 2, 1, 1, 2, 2, 0], [2, 0, 0, 0, 2, 0, 1, 0], [1, 1, 0, 2, 2, 0, 1, 0], [1, 1, 2, 0, 0, 1, 2, 1]], ![[0, 0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 0, 1, 0, 2, 2], [2, 0, 0, 2, 0, 0, 0, 1], [0, 0, 1, 0, 0, 0, 2, 2], [2, 0, 2, 2, 0, 2, 0, 1], [0, 0, 1, 2, 0, 0, 1, 2], [1, 1, 2, 0, 0, 1, 2, 1], [1, 2, 0, 0, 1, 1, 2, 2]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 1, 2, 1, 2, 0], ![2, 1, 2, 2, 0, 2, 2, 0], ![2, 0, 2, 2, 0, 0, 0, 0], ![1, 0, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 1, 0, 0], ![1, 0, 2, 2, 1, 2, 1, 0], ![2, 1, 2, 2, 1, 1, 2, 1]]
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

end VoightMaximalOrderD8R75

namespace VoightMaximalOrderD8R78

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1665705625, [-19, 51, 3, -70, 25, 22, -10, -2, 1], 7⟩
local notation "l" => [-19, 51, 3, -70, 25, 22, -10, -2, 1]
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
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![7, 0, 0, 0, 0, 0, 0, 0], ![0, 7, 0, 0, 0, 0, 0, 0], ![0, 0, 7, 0, 0, 0, 0, 0], ![0, 0, 0, 7, 0, 0, 0, 0], ![0, 0, 0, 0, 7, 0, 0, 0], ![0, 0, 0, 0, 0, 7, 0, 0], ![0, 0, 0, 0, 0, 0, 7, 0], ![4, 3, 0, 0, 1, 0, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-4, -3, 0, 0, -1, 0, -1, 7], ![1, -8, 0, 10, -4, -3, 1, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-4, -3, 0, 0, -1, 0, -1, 7], ![11, -57, -3, 70, -27, -22, 8, 14], ![-1, -26, -8, 30, -3, -13, -1, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-4, -3, 0, 0, -1, 0, -1, 7], ![11, -57, -3, 70, -27, -22, 8, 14], ![-18, -125, -57, 137, 6, -69, -16, 98], ![20, -126, -26, 152, -33, -51, 4, 41]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-4, -3, 0, 0, -1, 0, -1, 7], ![11, -57, -3, 70, -27, -22, 8, 14], ![-18, -125, -57, 137, 6, -69, -16, 98], ![162, -754, -125, 923, -239, -288, 45, 182], ![25, -320, -126, 384, -16, -156, -14, 151]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-4, -3, 0, 0, -1, 0, -1, 7], ![11, -57, -3, 70, -27, -22, 8, 14], ![-18, -125, -57, 137, 6, -69, -16, 98], ![162, -754, -125, 923, -239, -288, 45, 182], ![2, -1429, -754, 1695, 150, -785, -151, 861], ![207, -1141, -320, 1384, -206, -469, 9, 355]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-4, -3, 0, 0, -1, 0, -1, 7], ![11, -57, -3, 70, -27, -22, 8, 14], ![-18, -125, -57, 137, 6, -69, -16, 98], ![162, -754, -125, 923, -239, -288, 45, 182], ![2, -1429, -754, 1695, 150, -785, -151, 861], ![1465, -6433, -1429, 7856, -1598, -2433, 227, 1526], ![319, -2660, -1141, 3230, -45, -1271, -123, 1128]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![1, -8, 0, 10, -4, -3, 1, 3], ![-1, -26, -8, 30, -3, -13, -1, 16], ![20, -126, -26, 152, -33, -51, 4, 41], ![25, -320, -126, 384, -16, -156, -14, 151], ![207, -1141, -320, 1384, -206, -469, 9, 355], ![319, -2660, -1141, 3230, -45, -1271, -123, 1128], ![281, -1620, -561, 1969, -176, -695, -22, 545]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-7]], ![[], [], [], [], [], [], [-49], [-21, -7]], ![[], [], [], [], [], [-49], [-98, -49], [-112, -21, -7]], ![[], [], [], [], [-49], [-98, -49], [-686, -98, -49], [-287, -112, -21, -7]], ![[], [], [], [-49], [-98, -49], [-686, -98, -49], [-1274, -686, -98, -49], [-1057, -287, -112, -21, -7]], ![[], [], [-49], [-98, -49], [-686, -98, -49], [-1274, -686, -98, -49], [-6027, -1274, -686, -98, -49], [-2485, -1057, -287, -112, -21, -7]], ![[], [-7], [-21, -7], [-112, -21, -7], [-287, -112, -21, -7], [-1057, -287, -112, -21, -7], [-2485, -1057, -287, -112, -21, -7], [-1527, -522, -195, -58, -19, -4, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-4, -3, 0, 0, -1, 0, -1, 7], [1, -8, 0, 10, -4, -3, 1, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-4, -3, 0, 0, -1, 0, -1, 7], [11, -57, -3, 70, -27, -22, 8, 14], [-1, -26, -8, 30, -3, -13, -1, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-4, -3, 0, 0, -1, 0, -1, 7], [11, -57, -3, 70, -27, -22, 8, 14], [-18, -125, -57, 137, 6, -69, -16, 98], [20, -126, -26, 152, -33, -51, 4, 41]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-4, -3, 0, 0, -1, 0, -1, 7], [11, -57, -3, 70, -27, -22, 8, 14], [-18, -125, -57, 137, 6, -69, -16, 98], [162, -754, -125, 923, -239, -288, 45, 182], [25, -320, -126, 384, -16, -156, -14, 151]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-4, -3, 0, 0, -1, 0, -1, 7], [11, -57, -3, 70, -27, -22, 8, 14], [-18, -125, -57, 137, 6, -69, -16, 98], [162, -754, -125, 923, -239, -288, 45, 182], [2, -1429, -754, 1695, 150, -785, -151, 861], [207, -1141, -320, 1384, -206, -469, 9, 355]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-4, -3, 0, 0, -1, 0, -1, 7], [11, -57, -3, 70, -27, -22, 8, 14], [-18, -125, -57, 137, 6, -69, -16, 98], [162, -754, -125, 923, -239, -288, 45, 182], [2, -1429, -754, 1695, 150, -785, -151, 861], [1465, -6433, -1429, 7856, -1598, -2433, 227, 1526], [319, -2660, -1141, 3230, -45, -1271, -123, 1128]], ![[0, 0, 0, 0, 0, 0, 0, 1], [1, -8, 0, 10, -4, -3, 1, 3], [-1, -26, -8, 30, -3, -13, -1, 16], [20, -126, -26, 152, -33, -51, 4, 41], [25, -320, -126, 384, -16, -156, -14, 151], [207, -1141, -320, 1384, -206, -469, 9, 355], [319, -2660, -1141, 3230, -45, -1271, -123, 1128], [281, -1620, -561, 1969, -176, -695, -22, 545]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp3169 : Fact (Nat.Prime 3169) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 2, 1]
  b' := [2, 0, 3, 1]
  k := [1]
  f := [4, -9, 2, 18, 1, 0, 6, 2]
  g := [1, 3, 2, 4, 1]
  h := [1, 3, 2, 4, 1]
  a := [0, 2, 3, 3]
  b := [1, 4, 2, 3, 0, 0, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [16, 7, 5, 7, 22]
  b' := [24, 21, 27, 15, 7, 6]
  k := [2, 0, 18, 28, 1]
  f := [5, 19, 18, 8, 14, 18, 8, 1]
  g := [7, 28, 7, 2, 22, 13, 1]
  h := [18, 14, 1]
  a := [1, 26, 28, 20, 5, 14]
  b := [16, 10, 0, 26, 21, 7, 15]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3169 : CertificateDedekindCriterionLists l 3169 where
  n := 2
  a' := [1203, 2880, 1796, 2132, 105, 101]
  b' := [2566, 1227, 867, 2025, 2625, 2888, 891]
  k := [778, 2673, 3020, 2767, 1321, 919, 1]
  f := [1063, 362, 1119, 416, 465, 420, 725, 1]
  g := [2997, 1018, 3154, 1170, 1310, 1183, 2043, 1]
  h := [1124, 1]
  a := [770, 2453, 1091, 1528, 283, 2137, 2053]
  b := [3119, 216, 3108, 117, 915, 560, 1116]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [7] where
  n := 4
  p := ![5, 7, 29, 3169]
  exp := ![1, 2, 1, 1]
  pdgood := [5, 29, 3169]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp7.out
    exact hp29.out
    exact hp3169.out
  a := [271981040, 197217792, -996471480, -55367456, 547821084, 884448, -73168448]
  b := [101767755, -210480422, -140645050, 287868420, 35654762, -95316536, -2397070, 9146056]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3169 T_ofList CD3169

noncomputable def M7 : MaximalOrderCertificateOfUnramifiedLists 7 O Om hm where
  n := 8
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [3, 4, 0, 0, 6, 0, 6, 0], [1, 6, 0, 3, 3, 4, 1, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [3, 4, 0, 0, 6, 0, 6, 0], [4, 6, 4, 0, 1, 6, 1, 0], [6, 2, 6, 2, 4, 1, 6, 2]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [3, 4, 0, 0, 6, 0, 6, 0], [4, 6, 4, 0, 1, 6, 1, 0], [3, 1, 6, 4, 6, 1, 5, 0], [6, 0, 2, 5, 2, 5, 4, 6]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [3, 4, 0, 0, 6, 0, 6, 0], [4, 6, 4, 0, 1, 6, 1, 0], [3, 1, 6, 4, 6, 1, 5, 0], [1, 2, 1, 6, 6, 6, 3, 0], [4, 2, 0, 6, 5, 5, 0, 4]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [3, 4, 0, 0, 6, 0, 6, 0], [4, 6, 4, 0, 1, 6, 1, 0], [3, 1, 6, 4, 6, 1, 5, 0], [1, 2, 1, 6, 6, 6, 3, 0], [2, 6, 2, 1, 3, 6, 3, 0], [4, 0, 2, 5, 4, 0, 2, 5]], ![[0, 0, 0, 0, 0, 0, 1, 0], [3, 4, 0, 0, 6, 0, 6, 0], [4, 6, 4, 0, 1, 6, 1, 0], [3, 1, 6, 4, 6, 1, 5, 0], [1, 2, 1, 6, 6, 6, 3, 0], [2, 6, 2, 1, 3, 6, 3, 0], [2, 0, 6, 2, 5, 3, 3, 0], [4, 0, 0, 3, 4, 3, 3, 1]], ![[0, 0, 0, 0, 0, 0, 0, 1], [1, 6, 0, 3, 3, 4, 1, 3], [6, 2, 6, 2, 4, 1, 6, 2], [6, 0, 2, 5, 2, 5, 4, 6], [4, 2, 0, 6, 5, 5, 0, 4], [4, 0, 2, 5, 4, 0, 2, 5], [4, 0, 0, 3, 4, 3, 3, 1], [1, 4, 6, 2, 6, 5, 6, 6]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![4, 5, 3, 2, 4, 5, 2, 0], ![2, 2, 4, 1, 6, 1, 0, 0], ![2, 2, 5, 2, 2, 6, 1, 0], ![1, 1, 0, 4, 0, 2, 1, 0], ![2, 2, 2, 1, 1, 3, 3, 0], ![4, 4, 1, 2, 1, 0, 2, 0], ![1, 1, 0, 4, 6, 2, 1, 1]]
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

end VoightMaximalOrderD8R78

namespace VoightMaximalOrderD8R85

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1735088125, [1, 19, -6, -42, 18, 19, -9, -2, 1], 49⟩
local notation "l" => [1, 19, -6, -42, 18, 19, -9, -2, 1]
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
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![7, 0, 0, 0, 0, 0, 0, 0], ![0, 7, 0, 0, 0, 0, 0, 0], ![0, 0, 7, 0, 0, 0, 0, 0], ![0, 0, 0, 7, 0, 0, 0, 0], ![0, 0, 0, 0, 7, 0, 0, 0], ![0, 0, 0, 0, 0, 7, 0, 0], ![5, 5, 2, 2, 2, 0, 1, 0], ![0, 5, 5, 2, 2, 2, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![-5, -5, -2, -2, -2, 0, 7, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-8, -12, -3, 3, -6, -3, 11, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![-5, -5, -2, -2, -2, 0, 7, 0], ![0, -5, -5, -2, -2, -2, 0, 7], ![-8, -12, -3, 3, -6, -3, 11, 2], ![-1, -17, -12, 9, -3, -12, 1, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![-5, -5, -2, -2, -2, 0, 7, 0], ![0, -5, -5, -2, -2, -2, 0, 7], ![-46, -74, -22, 20, -40, -23, 63, 14], ![-1, -17, -12, 9, -3, -12, 1, 15], ![-60, -121, -38, 57, -57, -48, 81, 31]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![-5, -5, -2, -2, -2, 0, 7, 0], ![0, -5, -5, -2, -2, -2, 0, 7], ![-46, -74, -22, 20, -40, -23, 63, 14], ![3, -99, -70, 66, -18, -82, -7, 91], ![-60, -121, -38, 57, -57, -48, 81, 31], ![-8, -192, -118, 151, -33, -150, 5, 143]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![-5, -5, -2, -2, -2, 0, 7, 0], ![0, -5, -5, -2, -2, -2, 0, 7], ![-46, -74, -22, 20, -40, -23, 63, 14], ![3, -99, -70, 66, -18, -82, -7, 91], ![-318, -679, -208, 367, -316, -291, 427, 175], ![-8, -192, -118, 151, -33, -150, 5, 143], ![-394, -974, -321, 611, -407, -462, 523, 291]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![-8, -12, -3, 3, -6, -3, 11, 2], ![-1, -17, -12, 9, -3, -12, 1, 15], ![-60, -121, -38, 57, -57, -48, 81, 31], ![-8, -192, -118, 151, -33, -150, 5, 143], ![-76, -182, -61, 107, -77, -84, 102, 56], ![-28, -328, -182, 275, -61, -245, 28, 214]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-8, -12, -3, 3, -6, -3, 11, 2], ![-1, -17, -12, 9, -3, -12, 1, 15], ![-60, -121, -38, 57, -57, -48, 81, 31], ![-8, -192, -118, 151, -33, -150, 5, 143], ![-394, -974, -321, 611, -407, -462, 523, 291], ![-28, -328, -182, 275, -61, -245, 28, 214], ![-487, -1371, -480, 950, -519, -703, 639, 456]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-7]], ![[], [], [], [], [], [], [-7], [-14, -7]], ![[], [], [], [], [], [-49], [-14, -7], [-105, -14, -7]], ![[], [], [], [], [-49], [-98, -49], [-105, -14, -7], [-217, -105, -14, -7]], ![[], [], [], [-49], [-98, -49], [-637, -98, -49], [-217, -105, -14, -7], [-1001, -217, -105, -14, -7]], ![[], [], [-7], [-14, -7], [-105, -14, -7], [-217, -105, -14, -7], [-179, -37, -17, -2, -1], [-392, -179, -37, -17, -2, -1]], ![[], [-7], [-14, -7], [-105, -14, -7], [-217, -105, -14, -7], [-1001, -217, -105, -14, -7], [-392, -179, -37, -17, -2, -1], [-1498, -392, -179, -37, -17, -2, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [-5, -5, -2, -2, -2, 0, 7, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-8, -12, -3, 3, -6, -3, 11, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [-5, -5, -2, -2, -2, 0, 7, 0], [0, -5, -5, -2, -2, -2, 0, 7], [-8, -12, -3, 3, -6, -3, 11, 2], [-1, -17, -12, 9, -3, -12, 1, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [-5, -5, -2, -2, -2, 0, 7, 0], [0, -5, -5, -2, -2, -2, 0, 7], [-46, -74, -22, 20, -40, -23, 63, 14], [-1, -17, -12, 9, -3, -12, 1, 15], [-60, -121, -38, 57, -57, -48, 81, 31]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [-5, -5, -2, -2, -2, 0, 7, 0], [0, -5, -5, -2, -2, -2, 0, 7], [-46, -74, -22, 20, -40, -23, 63, 14], [3, -99, -70, 66, -18, -82, -7, 91], [-60, -121, -38, 57, -57, -48, 81, 31], [-8, -192, -118, 151, -33, -150, 5, 143]], ![[0, 0, 0, 0, 0, 1, 0, 0], [-5, -5, -2, -2, -2, 0, 7, 0], [0, -5, -5, -2, -2, -2, 0, 7], [-46, -74, -22, 20, -40, -23, 63, 14], [3, -99, -70, 66, -18, -82, -7, 91], [-318, -679, -208, 367, -316, -291, 427, 175], [-8, -192, -118, 151, -33, -150, 5, 143], [-394, -974, -321, 611, -407, -462, 523, 291]], ![[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [-8, -12, -3, 3, -6, -3, 11, 2], [-1, -17, -12, 9, -3, -12, 1, 15], [-60, -121, -38, 57, -57, -48, 81, 31], [-8, -192, -118, 151, -33, -150, 5, 143], [-76, -182, -61, 107, -77, -84, 102, 56], [-28, -328, -182, 275, -61, -245, 28, 214]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-8, -12, -3, 3, -6, -3, 11, 2], [-1, -17, -12, 9, -3, -12, 1, 15], [-60, -121, -38, 57, -57, -48, 81, 31], [-8, -192, -118, 151, -33, -150, 5, 143], [-394, -974, -321, 611, -407, -462, 523, 291], [-28, -328, -182, 275, -61, -245, 28, 214], [-487, -1371, -480, 950, -519, -703, 639, 456]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp3301 : Fact (Nat.Prime 3301) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 3, 4]
  b' := [3, 1, 2, 4]
  k := [1]
  f := [0, -3, 2, 10, 0, -3, 5, 2]
  g := [1, 2, 0, 4, 1]
  h := [1, 2, 0, 4, 1]
  a := [1, 1]
  b := [1, 1, 4, 1, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [26, 28, 8, 4, 9]
  b' := [1, 7, 16, 7, 18, 13]
  k := [16, 16, 14, 17, 1]
  f := [6, 8, 9, 6, 5, 8, 5, 1]
  g := [25, 18, 20, 2, 19, 22, 1]
  h := [7, 5, 1]
  a := [4, 0, 1, 1, 26, 5]
  b := [13, 23, 5, 23, 18, 1, 24]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3301 : CertificateDedekindCriterionLists l 3301 where
  n := 2
  a' := [2781, 3035, 3120, 228, 1406, 2725]
  b' := [3146, 3052, 2520, 3120, 1029, 2377, 1497]
  k := [1126, 2499, 1526, 1848, 1579, 1369, 1]
  f := [164, 857, 832, 675, 153, 662, 683, 1]
  g := [561, 2931, 2843, 2306, 521, 2264, 2334, 1]
  h := [965, 1]
  a := [192, 315, 2470, 97, 739, 2553, 2622]
  b := [750, 21, 262, 1610, 612, 2059, 679]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [7] where
  n := 4
  p := ![5, 7, 29, 3301]
  exp := ![1, 2, 1, 1]
  pdgood := [5, 29, 3301]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp7.out
    exact hp29.out
    exact hp3301.out
  a := [12395282, 12749108, -84832569, -14325728, 62134830, 2046108, -9224880]
  b := [582017, -12698698, -8530475, 25207061, 5266609, -10801896, -544041, 1153110]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3301 T_ofList CD3301

noncomputable def M7 : MaximalOrderCertificateOfUnramifiedLists 7 O Om hm where
  n := 8
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [2, 2, 5, 5, 5, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [6, 2, 4, 3, 1, 4, 4, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [2, 2, 5, 5, 5, 0, 0, 0], [0, 2, 2, 5, 5, 5, 0, 0], [6, 2, 4, 3, 1, 4, 4, 2], [6, 4, 2, 2, 4, 2, 1, 1]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [2, 2, 5, 5, 5, 0, 0, 0], [0, 2, 2, 5, 5, 5, 0, 0], [3, 3, 6, 6, 2, 5, 0, 0], [6, 4, 2, 2, 4, 2, 1, 1], [3, 5, 4, 1, 6, 1, 4, 3]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [2, 2, 5, 5, 5, 0, 0, 0], [0, 2, 2, 5, 5, 5, 0, 0], [3, 3, 6, 6, 2, 5, 0, 0], [3, 6, 0, 3, 3, 2, 0, 0], [3, 5, 4, 1, 6, 1, 4, 3], [6, 4, 1, 4, 2, 4, 5, 3]], ![[0, 0, 0, 0, 0, 1, 0, 0], [2, 2, 5, 5, 5, 0, 0, 0], [0, 2, 2, 5, 5, 5, 0, 0], [3, 3, 6, 6, 2, 5, 0, 0], [3, 6, 0, 3, 3, 2, 0, 0], [4, 0, 2, 3, 6, 3, 0, 0], [6, 4, 1, 4, 2, 4, 5, 3], [5, 6, 1, 2, 6, 0, 5, 4]], ![[0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1], [6, 2, 4, 3, 1, 4, 4, 2], [6, 4, 2, 2, 4, 2, 1, 1], [3, 5, 4, 1, 6, 1, 4, 3], [6, 4, 1, 4, 2, 4, 5, 3], [1, 0, 2, 2, 0, 0, 4, 0], [0, 1, 0, 2, 2, 0, 0, 4]], ![[0, 0, 0, 0, 0, 0, 0, 1], [6, 2, 4, 3, 1, 4, 4, 2], [6, 4, 2, 2, 4, 2, 1, 1], [3, 5, 4, 1, 6, 1, 4, 3], [6, 4, 1, 4, 2, 4, 5, 3], [5, 6, 1, 2, 6, 0, 5, 4], [0, 1, 0, 2, 2, 0, 0, 4], [3, 1, 3, 5, 6, 4, 2, 1]]]
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

end VoightMaximalOrderD8R85

namespace VoightMaximalOrderD8R87

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1781343125, [-1, 12, -34, -2, 35, -1, -11, 0, 1], 7⟩
local notation "l" => [-1, 12, -34, -2, 35, -1, -11, 0, 1]
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
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![7, 0, 0, 0, 0, 0, 0, 0], ![0, 7, 0, 0, 0, 0, 0, 0], ![0, 0, 7, 0, 0, 0, 0, 0], ![0, 0, 0, 7, 0, 0, 0, 0], ![0, 0, 0, 0, 7, 0, 0, 0], ![0, 0, 0, 0, 0, 7, 0, 0], ![0, 0, 0, 0, 0, 0, 7, 0], ![4, 3, 1, 5, 6, 0, 2, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-4, -3, -1, -5, -6, 0, -2, 7], ![-1, -2, 5, -1, -6, 1, 1, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-4, -3, -1, -5, -6, 0, -2, 7], ![1, -12, 34, 2, -35, 1, 11, 0], ![-6, -8, 7, -2, -19, -4, 1, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-4, -3, -1, -5, -6, 0, -2, 7], ![1, -12, 34, 2, -35, 1, 11, 0], ![-44, -32, -23, -21, -64, -35, -21, 77], ![-15, -31, 46, -9, -74, -8, 5, 29]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-4, -3, -1, -5, -6, 0, -2, 7], ![1, -12, 34, 2, -35, 1, 11, 0], ![-44, -32, -23, -21, -64, -35, -21, 77], ![7, -135, 374, 5, -357, 13, 84, 7], ![-49, -88, 109, -8, -213, -45, 11, 93]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-4, -3, -1, -5, -6, 0, -2, 7], ![1, -12, 34, 2, -35, 1, 11, 0], ![-44, -32, -23, -21, -64, -35, -21, 77], ![7, -135, 374, 5, -357, 13, 84, 7], ![-343, -259, -184, -53, -541, -350, -148, 602], ![-137, -268, 366, -39, -632, -120, 26, 263]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-4, -3, -1, -5, -6, 0, -2, 7], ![1, -12, 34, 2, -35, 1, 11, 0], ![-44, -32, -23, -21, -64, -35, -21, 77], ![7, -135, 374, 5, -357, 13, 84, 7], ![-343, -259, -184, -53, -541, -350, -148, 602], ![-10, -1103, 2899, -46, -2777, 61, 548, 168], ![-367, -741, 1021, -27, -1773, -369, 91, 708]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 5, -1, -6, 1, 1, 2], ![-6, -8, 7, -2, -19, -4, 1, 11], ![-15, -31, 46, -9, -74, -8, 5, 29], ![-49, -88, 109, -8, -213, -45, 11, 93], ![-137, -268, 366, -39, -632, -120, 26, 263], ![-367, -741, 1021, -27, -1773, -369, 91, 708], ![-312, -605, 808, -42, -1436, -302, 62, 599]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-7]], ![[], [], [], [], [], [], [-49], [-14, -7]], ![[], [], [], [], [], [-49], [0, -49], [-77, -14, -7]], ![[], [], [], [], [-49], [0, -49], [-539, 0, -49], [-203, -77, -14, -7]], ![[], [], [], [-49], [0, -49], [-539, 0, -49], [-49, -539, 0, -49], [-651, -203, -77, -14, -7]], ![[], [], [-49], [0, -49], [-539, 0, -49], [-49, -539, 0, -49], [-4214, -49, -539, 0, -49], [-1841, -651, -203, -77, -14, -7]], ![[], [-7], [-14, -7], [-77, -14, -7], [-203, -77, -14, -7], [-651, -203, -77, -14, -7], [-1841, -651, -203, -77, -14, -7], [-1468, -526, -168, -57, -15, -4, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-4, -3, -1, -5, -6, 0, -2, 7], [-1, -2, 5, -1, -6, 1, 1, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-4, -3, -1, -5, -6, 0, -2, 7], [1, -12, 34, 2, -35, 1, 11, 0], [-6, -8, 7, -2, -19, -4, 1, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-4, -3, -1, -5, -6, 0, -2, 7], [1, -12, 34, 2, -35, 1, 11, 0], [-44, -32, -23, -21, -64, -35, -21, 77], [-15, -31, 46, -9, -74, -8, 5, 29]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-4, -3, -1, -5, -6, 0, -2, 7], [1, -12, 34, 2, -35, 1, 11, 0], [-44, -32, -23, -21, -64, -35, -21, 77], [7, -135, 374, 5, -357, 13, 84, 7], [-49, -88, 109, -8, -213, -45, 11, 93]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-4, -3, -1, -5, -6, 0, -2, 7], [1, -12, 34, 2, -35, 1, 11, 0], [-44, -32, -23, -21, -64, -35, -21, 77], [7, -135, 374, 5, -357, 13, 84, 7], [-343, -259, -184, -53, -541, -350, -148, 602], [-137, -268, 366, -39, -632, -120, 26, 263]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-4, -3, -1, -5, -6, 0, -2, 7], [1, -12, 34, 2, -35, 1, 11, 0], [-44, -32, -23, -21, -64, -35, -21, 77], [7, -135, 374, 5, -357, 13, 84, 7], [-343, -259, -184, -53, -541, -350, -148, 602], [-10, -1103, 2899, -46, -2777, 61, 548, 168], [-367, -741, 1021, -27, -1773, -369, 91, 708]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 5, -1, -6, 1, 1, 2], [-6, -8, 7, -2, -19, -4, 1, 11], [-15, -31, 46, -9, -74, -8, 5, 29], [-49, -88, 109, -8, -213, -45, 11, 93], [-137, -268, 366, -39, -632, -120, 26, 263], [-367, -741, 1021, -27, -1773, -369, 91, 708], [-312, -605, 808, -42, -1436, -302, 62, 599]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp3389 : Fact (Nat.Prime 3389) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 0, 3]
  b' := [2, 2, 0, 3]
  k := [1]
  f := [2, 0, 10, 2, -5, 1, 3]
  g := [3, 2, 2, 0, 1]
  h := [3, 2, 2, 0, 1]
  a := [4, 0, 4, 4]
  b := [1, 1, 1, 0, 4, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [5, 19, 5, 26, 1]
  b' := [6, 21, 12, 13, 8, 24]
  k := [6, 1, 26, 11, 1]
  f := [5, 9, 19, 11, 15, 19, 8, 1]
  g := [9, 12, 25, 5, 25, 20, 1]
  h := [16, 9, 1]
  a := [7, 1, 19, 13, 18, 26]
  b := [22, 5, 9, 12, 6, 4, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3389 : CertificateDedekindCriterionLists l 3389 where
  n := 2
  a' := [90, 3350, 2059, 1396, 1568, 3043]
  b' := [3260, 3012, 2757, 252, 1278, 173, 1986]
  k := [2062, 2364, 3040, 2349, 3212, 1327, 1]
  f := [310, 808, 542, 525, 873, 668, 718, 1]
  g := [1019, 2655, 1779, 1724, 2868, 2193, 2358, 1]
  h := [1031, 1]
  a := [1476, 407, 1171, 1431, 1073, 1448, 3088]
  b := [1307, 2268, 1350, 2701, 72, 3095, 301]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [7] where
  n := 4
  p := ![5, 7, 29, 3389]
  exp := ![1, 2, 1, 1]
  pdgood := [5, 29, 3389]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp7.out
    exact hp29.out
    exact hp3389.out
  a := [329391607, -102135988, -718116624, 84511024, 353740176, -5842720, -43857920]
  b := [29455871, -170986337, 21374515, 182649766, -14628153, -59293682, 730340, 5482240]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3389 T_ofList CD3389

noncomputable def M7 : MaximalOrderCertificateOfUnramifiedLists 7 O Om hm where
  n := 8
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [3, 4, 6, 2, 1, 0, 5, 0], [6, 5, 5, 6, 1, 1, 1, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [3, 4, 6, 2, 1, 0, 5, 0], [1, 2, 6, 2, 0, 1, 4, 0], [1, 6, 0, 5, 2, 3, 1, 4]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [3, 4, 6, 2, 1, 0, 5, 0], [1, 2, 6, 2, 0, 1, 4, 0], [5, 3, 5, 0, 6, 0, 0, 0], [6, 4, 4, 5, 3, 6, 5, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [3, 4, 6, 2, 1, 0, 5, 0], [1, 2, 6, 2, 0, 1, 4, 0], [5, 3, 5, 0, 6, 0, 0, 0], [0, 5, 3, 5, 0, 6, 0, 0], [0, 3, 4, 6, 4, 4, 4, 2]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [3, 4, 6, 2, 1, 0, 5, 0], [1, 2, 6, 2, 0, 1, 4, 0], [5, 3, 5, 0, 6, 0, 0, 0], [0, 5, 3, 5, 0, 6, 0, 0], [0, 0, 5, 3, 5, 0, 6, 0], [3, 5, 2, 3, 5, 6, 5, 4]], ![[0, 0, 0, 0, 0, 0, 1, 0], [3, 4, 6, 2, 1, 0, 5, 0], [1, 2, 6, 2, 0, 1, 4, 0], [5, 3, 5, 0, 6, 0, 0, 0], [0, 5, 3, 5, 0, 6, 0, 0], [0, 0, 5, 3, 5, 0, 6, 0], [4, 3, 1, 3, 2, 5, 2, 0], [4, 1, 6, 1, 5, 2, 0, 1]], ![[0, 0, 0, 0, 0, 0, 0, 1], [6, 5, 5, 6, 1, 1, 1, 2], [1, 6, 0, 5, 2, 3, 1, 4], [6, 4, 4, 5, 3, 6, 5, 1], [0, 3, 4, 6, 4, 4, 4, 2], [3, 5, 2, 3, 5, 6, 5, 4], [4, 1, 6, 1, 5, 2, 0, 1], [3, 4, 3, 0, 6, 6, 6, 4]]]
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

end VoightMaximalOrderD8R87

end TraceEuclidean
