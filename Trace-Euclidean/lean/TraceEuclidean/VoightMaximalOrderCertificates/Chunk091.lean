import TraceEuclidean.VoightMaximalOrderCertificates.Chunk087
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

namespace VoightMaximalOrderD8R53

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1410504129, [1, -1, -15, 1, 22, -1, -9, 0, 1], 4⟩
local notation "l" => [1, -1, -15, 1, 22, -1, -9, 0, 1]
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
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![2, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 0, 0], ![0, 0, 0, 2, 0, 0, 0, 0], ![0, 0, 0, 0, 2, 0, 0, 0], ![0, 0, 0, 0, 0, 2, 0, 0], ![1, 0, 0, 1, 1, 1, 1, 0], ![1, 1, 0, 1, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![-1, 0, 0, -1, -1, -1, 2, 0], ![-1, 0, 0, -1, 0, 0, 1, 1], ![-5, 1, 8, -5, -15, -4, 9, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![-1, 0, 0, -1, -1, -1, 2, 0], ![-1, -1, 0, -1, 0, 0, 0, 2], ![-6, 0, 8, -6, -16, -4, 10, 1], ![-5, -5, 1, 3, -1, -11, 1, 9]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![-1, 0, 0, -1, -1, -1, 2, 0], ![-1, -1, 0, -1, 0, 0, 0, 2], ![-10, 1, 15, -10, -31, -8, 18, 0], ![-11, -5, 8, -3, -17, -16, 11, 10], ![-35, 4, 67, -34, -121, -26, 60, 1]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![-1, 0, 0, -1, -1, -1, 2, 0], ![-1, -1, 0, -1, 0, 0, 0, 2], ![-10, 1, 15, -10, -31, -8, 18, 0], ![-10, -10, 1, 5, -2, -23, 2, 18], ![-45, -1, 75, -37, -137, -41, 69, 11], ![-39, -34, 12, 28, -23, -99, 17, 60]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![-1, 0, 0, -1, -1, -1, 2, 0], ![-1, -1, 0, -1, 0, 0, 0, 2], ![-10, 1, 15, -10, -31, -8, 18, 0], ![-10, -10, 1, 5, -2, -23, 2, 18], ![-69, 8, 134, -68, -242, -51, 118, 2], ![-83, -34, 87, -8, -161, -140, 86, 69], ![-218, 21, 446, -206, -773, -164, 359, 17]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-1, 0, 0, -1, 0, 0, 1, 1], ![-6, 0, 8, -6, -16, -4, 10, 1], ![-11, -5, 8, -3, -17, -16, 11, 10], ![-45, -1, 75, -37, -137, -41, 69, 11], ![-83, -34, 87, -8, -161, -140, 86, 69], ![-215, -27, 344, -126, -609, -247, 297, 88], ![-286, -105, 341, -23, -607, -483, 310, 219]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-5, 1, 8, -5, -15, -4, 9, 0], ![-5, -5, 1, 3, -1, -11, 1, 9], ![-35, 4, 67, -34, -121, -26, 60, 1], ![-39, -34, 12, 28, -23, -99, 17, 60], ![-218, 21, 446, -206, -773, -164, 359, 17], ![-286, -105, 341, -23, -607, -483, 310, 219], ![-671, 42, 1373, -592, -2339, -543, 1065, 93]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-2]], ![[], [], [], [], [], [], [-2], [0, -2]], ![[], [], [], [], [], [-4], [-2, -2], [-18, 0, -2]], ![[], [], [], [], [-4], [0, -4], [-20, -2, -2], [-2, -18, 0, -2]], ![[], [], [], [-4], [0, -4], [-36, 0, -4], [-22, -20, -2, -2], [-120, -2, -18, 0, -2]], ![[], [], [-2], [-2, -2], [-20, -2, -2], [-22, -20, -2, -2], [-91, -23, -12, -2, -1], [-87, -70, -11, -10, -1, -1]], ![[], [-2], [0, -2], [-18, 0, -2], [-2, -18, 0, -2], [-120, -2, -18, 0, -2], [-87, -70, -11, -10, -1, -1], [-369, -17, -61, -1, -9, 0, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [-1, 0, 0, -1, -1, -1, 2, 0], [-1, 0, 0, -1, 0, 0, 1, 1], [-5, 1, 8, -5, -15, -4, 9, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [-1, 0, 0, -1, -1, -1, 2, 0], [-1, -1, 0, -1, 0, 0, 0, 2], [-6, 0, 8, -6, -16, -4, 10, 1], [-5, -5, 1, 3, -1, -11, 1, 9]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [-1, 0, 0, -1, -1, -1, 2, 0], [-1, -1, 0, -1, 0, 0, 0, 2], [-10, 1, 15, -10, -31, -8, 18, 0], [-11, -5, 8, -3, -17, -16, 11, 10], [-35, 4, 67, -34, -121, -26, 60, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [-1, 0, 0, -1, -1, -1, 2, 0], [-1, -1, 0, -1, 0, 0, 0, 2], [-10, 1, 15, -10, -31, -8, 18, 0], [-10, -10, 1, 5, -2, -23, 2, 18], [-45, -1, 75, -37, -137, -41, 69, 11], [-39, -34, 12, 28, -23, -99, 17, 60]], ![[0, 0, 0, 0, 0, 1, 0, 0], [-1, 0, 0, -1, -1, -1, 2, 0], [-1, -1, 0, -1, 0, 0, 0, 2], [-10, 1, 15, -10, -31, -8, 18, 0], [-10, -10, 1, 5, -2, -23, 2, 18], [-69, 8, 134, -68, -242, -51, 118, 2], [-83, -34, 87, -8, -161, -140, 86, 69], [-218, 21, 446, -206, -773, -164, 359, 17]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-1, 0, 0, -1, 0, 0, 1, 1], [-6, 0, 8, -6, -16, -4, 10, 1], [-11, -5, 8, -3, -17, -16, 11, 10], [-45, -1, 75, -37, -137, -41, 69, 11], [-83, -34, 87, -8, -161, -140, 86, 69], [-215, -27, 344, -126, -609, -247, 297, 88], [-286, -105, 341, -23, -607, -483, 310, 219]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-5, 1, 8, -5, -15, -4, 9, 0], [-5, -5, 1, 3, -1, -11, 1, 9], [-35, 4, 67, -34, -121, -26, 60, 1], [-39, -34, 12, 28, -23, -99, 17, 60], [-218, 21, 446, -206, -773, -164, 359, 17], [-286, -105, 341, -23, -607, -483, 310, 219], [-671, 42, 1373, -592, -2339, -543, 1065, 93]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp89 : Fact (Nat.Prime 89) := fact_iff.2 (by norm_num)
instance hp1327 : Fact (Nat.Prime 1327) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 2
  a' := [2, 1, 1]
  b' := [1, 0, 1, 2, 1, 1]
  k := [1, 2, 1, 0, 1]
  f := [0, 1, 6, 1, -6, 1, 4]
  g := [1, 2, 2, 2, 2, 0, 1]
  h := [1, 0, 1]
  a := [0, 1, 0, 1, 1, 1]
  b := [1, 1, 1, 0, 1, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD89 : CertificateDedekindCriterionLists l 89 where
  n := 2
  a' := [12, 67, 62, 52, 81, 76]
  b' := [78, 15, 6, 52, 59, 76, 40]
  k := [16, 34, 33, 9, 19, 44, 1]
  f := [3, 52, 16, 10, 27, 23, 17, 1]
  g := [4, 69, 20, 13, 36, 30, 22, 1]
  h := [67, 1]
  a := [36, 67, 2, 26, 25, 23, 19]
  b := [40, 60, 18, 13, 2, 72, 70]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1327 : CertificateDedekindCriterionLists l 1327 where
  n := 2
  a' := [737, 66, 1036, 1095, 784]
  b' := [1122, 1319, 958, 807, 43, 754]
  k := [281, 901, 393, 961, 1]
  f := [47, 52, 129, 188, 82, 238, 158, 1]
  g := [231, 99, 566, 540, 35, 1144, 1]
  h := [270, 183, 1]
  a := [94, 113, 946, 101, 79, 727]
  b := [383, 10, 246, 1135, 1038, 163, 600]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 4
  p := ![2, 3, 89, 1327]
  exp := ![1, 1, 1, 1]
  pdgood := [3, 89, 1327]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp3.out
    exact hp89.out
    exact hp1327.out
  a := [695926, -150657, -3524941, 727460, 2836620, -75944, -466608]
  b := [-12692, -465823, 123440, 990617, -134164, -485811, 9493, 58326]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 89 T_ofList CD89
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1327 T_ofList CD1327

noncomputable def M2 : MaximalOrderCertificateOfUnramifiedLists 2 O Om hm where
  n := 8
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 1, 1, 0, 0], [1, 0, 0, 1, 0, 0, 1, 1], [1, 1, 0, 1, 1, 0, 1, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 1, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1], [1, 1, 1, 1, 1, 1, 1, 1]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 1, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0, 0], [0, 1, 1, 0, 1, 0, 0, 0], [1, 1, 0, 1, 1, 0, 1, 0], [1, 0, 1, 0, 1, 0, 0, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 1, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0, 0], [0, 1, 1, 0, 1, 0, 0, 0], [0, 0, 1, 1, 0, 1, 0, 0], [1, 1, 1, 1, 1, 1, 1, 1], [1, 0, 0, 0, 1, 1, 1, 0]], ![[0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 1, 1, 0, 0], [1, 1, 0, 1, 0, 0, 0, 0], [0, 1, 1, 0, 1, 0, 0, 0], [0, 0, 1, 1, 0, 1, 0, 0], [1, 0, 0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 0, 1, 1]], ![[0, 0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 1, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 0, 1], [1, 1, 0, 1, 1, 0, 1, 0], [1, 1, 1, 1, 1, 1, 1, 1], [1, 0, 1, 0, 1, 0, 0, 1], [1, 1, 0, 0, 1, 1, 1, 0], [0, 1, 1, 1, 1, 1, 0, 1]], ![[0, 0, 0, 0, 0, 0, 0, 1], [1, 1, 0, 1, 1, 0, 1, 0], [1, 1, 1, 1, 1, 1, 1, 1], [1, 0, 1, 0, 1, 0, 0, 1], [1, 0, 0, 0, 1, 1, 1, 0], [0, 1, 0, 0, 1, 0, 1, 1], [0, 1, 1, 1, 1, 1, 0, 1], [1, 0, 1, 0, 1, 1, 1, 1]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 1, 1, 0, 0], ![0, 1, 1, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 1, 0, 0], ![1, 1, 0, 0, 1, 1, 1, 0], ![1, 0, 1, 0, 1, 1, 1, 1]]
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

end VoightMaximalOrderD8R53

namespace VoightMaximalOrderD8R64

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1503813125, [-1, 14, 15, -49, 7, 24, -7, -3, 1], 103⟩
local notation "l" => [-1, 14, 15, -49, 7, 24, -7, -3, 1]
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

def basisDenominator : ℤ := 103
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![103, 0, 0, 0, 0, 0, 0, 0], ![0, 103, 0, 0, 0, 0, 0, 0], ![0, 0, 103, 0, 0, 0, 0, 0], ![0, 0, 0, 103, 0, 0, 0, 0], ![0, 0, 0, 0, 103, 0, 0, 0], ![0, 0, 0, 0, 0, 103, 0, 0], ![0, 0, 0, 0, 0, 0, 103, 0], ![17, 51, 97, 10, 51, 47, 94, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-17, -51, -97, -10, -51, -47, -94, 103], ![-16, -48, -91, -8, -48, -44, -88, 97]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-17, -51, -97, -10, -51, -47, -94, 103], ![-50, -167, -306, 19, -160, -165, -275, 309], ![-56, -184, -339, 13, -176, -180, -308, 345]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-17, -51, -97, -10, -51, -47, -94, 103], ![-50, -167, -306, 19, -160, -165, -275, 309], ![-269, -857, -1611, -28, -788, -831, -1507, 1648], ![-284, -908, -1703, -19, -839, -880, -1588, 1741]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-17, -51, -97, -10, -51, -47, -94, 103], ![-50, -167, -306, 19, -160, -165, -275, 309], ![-269, -857, -1611, -28, -788, -831, -1507, 1648], ![-749, -2516, -4646, 275, -2275, -2471, -4197, 4635], ![-860, -2864, -5303, 249, -2599, -2807, -4816, 5313]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-17, -51, -97, -10, -51, -47, -94, 103], ![-50, -167, -306, 19, -160, -165, -275, 309], ![-269, -857, -1611, -28, -788, -831, -1507, 1648], ![-749, -2516, -4646, 275, -2275, -2471, -4197, 4635], ![-2811, -9182, -17192, 244, -8158, -8956, -15833, 17304], ![-3136, -10268, -19195, 353, -9159, -10019, -17647, 19313]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-17, -51, -97, -10, -51, -47, -94, 103], ![-50, -167, -306, 19, -160, -165, -275, 309], ![-269, -857, -1611, -28, -788, -831, -1507, 1648], ![-749, -2516, -4646, 275, -2275, -2471, -4197, 4635], ![-2811, -9182, -17192, 244, -8158, -8956, -15833, 17304], ![-7703, -25920, -48045, 2706, -22865, -25383, -43406, 47689], ![-9009, -30163, -55992, 2771, -26674, -29522, -50745, 55720]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-16, -48, -91, -8, -48, -44, -88, 97], ![-56, -184, -339, 13, -176, -180, -308, 345], ![-284, -908, -1703, -19, -839, -880, -1588, 1741], ![-860, -2864, -5303, 249, -2599, -2807, -4816, 5313], ![-3136, -10268, -19195, 353, -9159, -10019, -17647, 19313], ![-9009, -30163, -55992, 2771, -26674, -29522, -50745, 55720], ![-10447, -34844, -64746, 2875, -30894, -34087, -58817, 64566]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-103]], ![[], [], [], [], [], [], [-10609], [-9991, -103]], ![[], [], [], [], [], [-10609], [-31827, -10609], [-35535, -9991, -103]], ![[], [], [], [], [-10609], [-31827, -10609], [-169744, -31827, -10609], [-179323, -35535, -9991, -103]], ![[], [], [], [-10609], [-31827, -10609], [-169744, -31827, -10609], [-477405, -169744, -31827, -10609], [-547239, -179323, -35535, -9991, -103]], ![[], [], [-10609], [-31827, -10609], [-169744, -31827, -10609], [-477405, -169744, -31827, -10609], [-1782312, -477405, -169744, -31827, -10609], [-1989239, -547239, -179323, -35535, -9991, -103]], ![[], [-103], [-9991, -103], [-35535, -9991, -103], [-179323, -35535, -9991, -103], [-547239, -179323, -35535, -9991, -103], [-1989239, -547239, -179323, -35535, -9991, -103], [-2222554, -619224, -190139, -38781, -9510, -191, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-17, -51, -97, -10, -51, -47, -94, 103], [-16, -48, -91, -8, -48, -44, -88, 97]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-17, -51, -97, -10, -51, -47, -94, 103], [-50, -167, -306, 19, -160, -165, -275, 309], [-56, -184, -339, 13, -176, -180, -308, 345]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-17, -51, -97, -10, -51, -47, -94, 103], [-50, -167, -306, 19, -160, -165, -275, 309], [-269, -857, -1611, -28, -788, -831, -1507, 1648], [-284, -908, -1703, -19, -839, -880, -1588, 1741]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-17, -51, -97, -10, -51, -47, -94, 103], [-50, -167, -306, 19, -160, -165, -275, 309], [-269, -857, -1611, -28, -788, -831, -1507, 1648], [-749, -2516, -4646, 275, -2275, -2471, -4197, 4635], [-860, -2864, -5303, 249, -2599, -2807, -4816, 5313]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-17, -51, -97, -10, -51, -47, -94, 103], [-50, -167, -306, 19, -160, -165, -275, 309], [-269, -857, -1611, -28, -788, -831, -1507, 1648], [-749, -2516, -4646, 275, -2275, -2471, -4197, 4635], [-2811, -9182, -17192, 244, -8158, -8956, -15833, 17304], [-3136, -10268, -19195, 353, -9159, -10019, -17647, 19313]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-17, -51, -97, -10, -51, -47, -94, 103], [-50, -167, -306, 19, -160, -165, -275, 309], [-269, -857, -1611, -28, -788, -831, -1507, 1648], [-749, -2516, -4646, 275, -2275, -2471, -4197, 4635], [-2811, -9182, -17192, 244, -8158, -8956, -15833, 17304], [-7703, -25920, -48045, 2706, -22865, -25383, -43406, 47689], [-9009, -30163, -55992, 2771, -26674, -29522, -50745, 55720]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-16, -48, -91, -8, -48, -44, -88, 97], [-56, -184, -339, 13, -176, -180, -308, 345], [-284, -908, -1703, -19, -839, -880, -1588, 1741], [-860, -2864, -5303, 249, -2599, -2807, -4816, 5313], [-3136, -10268, -19195, 353, -9159, -10019, -17647, 19313], [-9009, -30163, -55992, 2771, -26674, -29522, -50745, 55720], [-10447, -34844, -64746, 2875, -30894, -34087, -58817, 64566]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp103 : Fact (Nat.Prime 103) := fact_iff.2 (by norm_num)
instance hp2861 : Fact (Nat.Prime 2861) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1]
  b' := [4, 1]
  k := [1]
  f := [1, -2, -2, 11, 0, -4, 2, 1]
  g := [2, 1, 1, 1, 1]
  h := [2, 1, 1, 1, 1]
  a := [3, 0, 4, 4]
  b := [4, 1, 1, 0, 0, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [24, 4, 3, 14, 6]
  b' := [18, 23, 17, 1, 0, 28]
  k := [20, 24, 25, 4, 1]
  f := [9, 18, 14, 14, 15, 13, 7, 1]
  g := [26, 25, 12, 20, 21, 15, 1]
  h := [10, 11, 1]
  a := [0, 14, 3, 19, 7, 7]
  b := [19, 7, 5, 8, 7, 20, 22]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2861 : CertificateDedekindCriterionLists l 2861 where
  n := 2
  a' := [1221, 634, 1083, 157, 1289, 1124]
  b' := [2328, 1458, 1315, 2312, 2378, 28, 1883]
  k := [1920, 2296, 1895, 743, 146, 1527, 1]
  f := [1285, 1564, 211, 2080, 464, 1568, 559, 1]
  g := [1754, 2134, 287, 2839, 632, 2140, 762, 1]
  h := [2096, 1]
  a := [185, 177, 1908, 1156, 1290, 2495, 2745]
  b := [605, 1186, 697, 1897, 494, 2567, 116]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [103] where
  n := 4
  p := ![5, 29, 103, 2861]
  exp := ![1, 1, 2, 1]
  pdgood := [5, 29, 2861]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp29.out
    exact hp103.out
    exact hp2861.out
  a := [1690297621, 10930949998, -19906334922, -13724919748, 13158026376, 2892744354, -1953326544]
  b := [435099159, -1841870819, -5648457019, 5024287596, 3285361958, -2176796814, -453155226, 244165818]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2861 T_ofList CD2861

noncomputable def M103 : MaximalOrderCertificateOfUnramifiedLists 103 O Om hm where
  n := 8
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [86, 52, 6, 93, 52, 56, 9, 0], [87, 55, 12, 95, 55, 59, 15, 97]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [86, 52, 6, 93, 52, 56, 9, 0], [53, 39, 3, 19, 46, 41, 34, 0], [47, 22, 73, 13, 30, 26, 1, 36]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [86, 52, 6, 93, 52, 56, 9, 0], [53, 39, 3, 19, 46, 41, 34, 0], [40, 70, 37, 75, 36, 96, 38, 0], [25, 19, 48, 84, 88, 47, 60, 93]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [86, 52, 6, 93, 52, 56, 9, 0], [53, 39, 3, 19, 46, 41, 34, 0], [40, 70, 37, 75, 36, 96, 38, 0], [75, 59, 92, 69, 94, 1, 26, 0], [67, 20, 53, 43, 79, 77, 25, 60]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [86, 52, 6, 93, 52, 56, 9, 0], [53, 39, 3, 19, 46, 41, 34, 0], [40, 70, 37, 75, 36, 96, 38, 0], [75, 59, 92, 69, 94, 1, 26, 0], [73, 88, 9, 38, 82, 5, 29, 0], [57, 32, 66, 44, 8, 75, 69, 52]], ![[0, 0, 0, 0, 0, 0, 1, 0], [86, 52, 6, 93, 52, 56, 9, 0], [53, 39, 3, 19, 46, 41, 34, 0], [40, 70, 37, 75, 36, 96, 38, 0], [75, 59, 92, 69, 94, 1, 26, 0], [73, 88, 9, 38, 82, 5, 29, 0], [22, 36, 56, 28, 1, 58, 60, 0], [55, 16, 40, 93, 3, 39, 34, 100]], ![[0, 0, 0, 0, 0, 0, 0, 1], [87, 55, 12, 95, 55, 59, 15, 97], [47, 22, 73, 13, 30, 26, 1, 36], [25, 19, 48, 84, 88, 47, 60, 93], [67, 20, 53, 43, 79, 77, 25, 60], [57, 32, 66, 44, 8, 75, 69, 52], [55, 16, 40, 93, 3, 39, 34, 100], [59, 73, 41, 94, 6, 6, 99, 88]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![93, 101, 56, 74, 93, 19, 8, 0], ![49, 91, 69, 76, 26, 102, 7, 0], ![28, 98, 72, 65, 55, 68, 99, 0], ![59, 48, 83, 69, 55, 92, 34, 0], ![100, 98, 93, 78, 94, 66, 95, 0], ![4, 79, 99, 55, 15, 34, 56, 0], ![67, 99, 71, 24, 30, 62, 10, 102]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5, 6, 7]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [103]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 103 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M103
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [103] D q hq hbad)
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

end VoightMaximalOrderD8R64

namespace VoightMaximalOrderD8R66

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1534132224, [1, -4, -12, 8, 21, -4, -10, 0, 1], 19⟩
local notation "l" => [1, -4, -12, 8, 21, -4, -10, 0, 1]
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

def basisDenominator : ℤ := 19
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![19, 0, 0, 0, 0, 0, 0, 0], ![0, 19, 0, 0, 0, 0, 0, 0], ![0, 0, 19, 0, 0, 0, 0, 0], ![0, 0, 0, 19, 0, 0, 0, 0], ![0, 0, 0, 0, 19, 0, 0, 0], ![0, 0, 0, 0, 0, 19, 0, 0], ![0, 0, 0, 0, 0, 0, 19, 0], ![7, 18, 18, 6, 10, 16, 8, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-7, -18, -18, -6, -10, -16, -8, 19], ![-3, -7, -6, -2, -5, -6, -2, 8]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-7, -18, -18, -6, -10, -16, -8, 19], ![-1, 4, 12, -8, -21, 4, 10, 0], ![-10, -23, -19, -10, -22, -21, -6, 26]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-7, -18, -18, -6, -10, -16, -8, 19], ![-1, 4, 12, -8, -21, 4, 10, 0], ![-70, -181, -176, -48, -108, -181, -76, 190], ![-36, -84, -71, -35, -80, -82, -25, 94]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-7, -18, -18, -6, -10, -16, -8, 19], ![-1, 4, 12, -8, -21, 4, 10, 0], ![-70, -181, -176, -48, -108, -181, -76, 190], ![-38, -32, 47, -100, -238, -32, 47, 76], ![-107, -244, -198, -109, -255, -244, -70, 277]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-7, -18, -18, -6, -10, -16, -8, 19], ![-1, 4, 12, -8, -21, 4, 10, 0], ![-70, -181, -176, -48, -108, -181, -76, 190], ![-38, -32, 47, -100, -238, -32, 47, 76], ![-557, -1416, -1334, -387, -950, -1446, -560, 1501], ![-341, -786, -646, -332, -794, -797, -238, 886]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-7, -18, -18, -6, -10, -16, -8, 19], ![-1, 4, 12, -8, -21, 4, 10, 0], ![-70, -181, -176, -48, -108, -181, -76, 190], ![-38, -32, 47, -100, -238, -32, 47, 76], ![-557, -1416, -1334, -387, -950, -1446, -560, 1501], ![-583, -984, -342, -976, -2292, -996, 32, 1368], ![-992, -2259, -1818, -990, -2382, -2302, -665, 2566]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-3, -7, -6, -2, -5, -6, -2, 8], ![-10, -23, -19, -10, -22, -21, -6, 26], ![-36, -84, -71, -35, -80, -82, -25, 94], ![-107, -244, -198, -109, -255, -244, -70, 277], ![-341, -786, -646, -332, -794, -797, -238, 886], ![-992, -2259, -1818, -990, -2382, -2302, -665, 2566], ![-945, -2164, -1759, -932, -2234, -2196, -644, 2450]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-19]], ![[], [], [], [], [], [], [-361], [-152, -19]], ![[], [], [], [], [], [-361], [0, -361], [-494, -152, -19]], ![[], [], [], [], [-361], [0, -361], [-3610, 0, -361], [-1786, -494, -152, -19]], ![[], [], [], [-361], [0, -361], [-3610, 0, -361], [-1444, -3610, 0, -361], [-5263, -1786, -494, -152, -19]], ![[], [], [-361], [0, -361], [-3610, 0, -361], [-1444, -3610, 0, -361], [-28519, -1444, -3610, 0, -361], [-16834, -5263, -1786, -494, -152, -19]], ![[], [-19], [-152, -19], [-494, -152, -19], [-1786, -494, -152, -19], [-5263, -1786, -494, -152, -19], [-16834, -5263, -1786, -494, -152, -19], [-15344, -4932, -1531, -440, -106, -16, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-7, -18, -18, -6, -10, -16, -8, 19], [-3, -7, -6, -2, -5, -6, -2, 8]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-7, -18, -18, -6, -10, -16, -8, 19], [-1, 4, 12, -8, -21, 4, 10, 0], [-10, -23, -19, -10, -22, -21, -6, 26]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-7, -18, -18, -6, -10, -16, -8, 19], [-1, 4, 12, -8, -21, 4, 10, 0], [-70, -181, -176, -48, -108, -181, -76, 190], [-36, -84, -71, -35, -80, -82, -25, 94]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-7, -18, -18, -6, -10, -16, -8, 19], [-1, 4, 12, -8, -21, 4, 10, 0], [-70, -181, -176, -48, -108, -181, -76, 190], [-38, -32, 47, -100, -238, -32, 47, 76], [-107, -244, -198, -109, -255, -244, -70, 277]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-7, -18, -18, -6, -10, -16, -8, 19], [-1, 4, 12, -8, -21, 4, 10, 0], [-70, -181, -176, -48, -108, -181, -76, 190], [-38, -32, 47, -100, -238, -32, 47, 76], [-557, -1416, -1334, -387, -950, -1446, -560, 1501], [-341, -786, -646, -332, -794, -797, -238, 886]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-7, -18, -18, -6, -10, -16, -8, 19], [-1, 4, 12, -8, -21, 4, 10, 0], [-70, -181, -176, -48, -108, -181, -76, 190], [-38, -32, 47, -100, -238, -32, 47, 76], [-557, -1416, -1334, -387, -950, -1446, -560, 1501], [-583, -984, -342, -976, -2292, -996, 32, 1368], [-992, -2259, -1818, -990, -2382, -2302, -665, 2566]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-3, -7, -6, -2, -5, -6, -2, 8], [-10, -23, -19, -10, -22, -21, -6, 26], [-36, -84, -71, -35, -80, -82, -25, 94], [-107, -244, -198, -109, -255, -244, -70, 277], [-341, -786, -646, -332, -794, -797, -238, 886], [-992, -2259, -1818, -990, -2382, -2302, -665, 2566], [-945, -2164, -1759, -932, -2234, -2196, -644, 2450]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp17 : Fact (Nat.Prime 17) := fact_iff.2 (by norm_num)
instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 4
  a' := []
  b' := [1]
  k := [1]
  f := [0, 3, 7, -3, -10, 3, 6, 1]
  g := [1, 1, 1]
  h := [1, 1, 0, 1, 0, 1, 1]
  a := [1]
  b := [1, 0, 0, 1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 2
  a' := [0, 1]
  b' := [1, 0, 2]
  k := [1]
  f := [0, 2, 5, -2, -6, 2, 4]
  g := [1, 1, 1, 0, 1]
  h := [1, 1, 1, 0, 1]
  a := [0, 2]
  b := [1, 2, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD17 : CertificateDedekindCriterionLists l 17 where
  n := 2
  a' := [10, 16, 0, 16, 7]
  b' := [16, 16, 15, 5, 16, 13]
  k := [16, 1, 5, 12, 1]
  f := [3, 11, 11, 9, 2, 5, 5, 1]
  g := [13, 10, 13, 2, 5, 6, 1]
  h := [4, 11, 1]
  a := [8, 6, 4, 5, 12, 14]
  b := [10, 9, 3, 6, 8, 2, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [19] where
  n := 4
  p := ![2, 3, 17, 19]
  exp := ![2, 1, 1, 2]
  pdgood := [2, 3, 17]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp3.out
    exact hp17.out
    exact hp19.out
  a := [112368, 208124, -1023452, -129788, 841456, 61512, -119744]
  b := [9681, -118423, -32467, 278934, 12994, -142602, -7689, 14968]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 17 T_ofList CD17

noncomputable def M19 : MaximalOrderCertificateOfUnramifiedLists 19 O Om hm where
  n := 8
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [12, 1, 1, 13, 9, 3, 11, 0], [16, 12, 13, 17, 14, 13, 17, 8]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [12, 1, 1, 13, 9, 3, 11, 0], [18, 4, 12, 11, 17, 4, 10, 0], [9, 15, 0, 9, 16, 17, 13, 7]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [12, 1, 1, 13, 9, 3, 11, 0], [18, 4, 12, 11, 17, 4, 10, 0], [6, 9, 14, 9, 6, 9, 0, 0], [2, 11, 5, 3, 15, 13, 13, 18]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [12, 1, 1, 13, 9, 3, 11, 0], [18, 4, 12, 11, 17, 4, 10, 0], [6, 9, 14, 9, 6, 9, 0, 0], [0, 6, 9, 14, 9, 6, 9, 0], [7, 3, 11, 5, 11, 3, 6, 11]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [12, 1, 1, 13, 9, 3, 11, 0], [18, 4, 12, 11, 17, 4, 10, 0], [6, 9, 14, 9, 6, 9, 0, 0], [0, 6, 9, 14, 9, 6, 9, 0], [13, 9, 15, 12, 0, 17, 10, 0], [1, 12, 0, 10, 4, 1, 9, 12]], ![[0, 0, 0, 0, 0, 0, 1, 0], [12, 1, 1, 13, 9, 3, 11, 0], [18, 4, 12, 11, 17, 4, 10, 0], [6, 9, 14, 9, 6, 9, 0, 0], [0, 6, 9, 14, 9, 6, 9, 0], [13, 9, 15, 12, 0, 17, 10, 0], [6, 4, 0, 12, 7, 11, 13, 0], [15, 2, 6, 17, 12, 16, 0, 1]], ![[0, 0, 0, 0, 0, 0, 0, 1], [16, 12, 13, 17, 14, 13, 17, 8], [9, 15, 0, 9, 16, 17, 13, 7], [2, 11, 5, 3, 15, 13, 13, 18], [7, 3, 11, 5, 11, 3, 6, 11], [1, 12, 0, 10, 4, 1, 9, 12], [15, 2, 6, 17, 12, 16, 0, 1], [5, 2, 8, 18, 8, 8, 2, 18]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![11, 11, 13, 5, 8, 13, 16, 0], ![5, 3, 2, 14, 6, 2, 2, 0], ![6, 8, 5, 13, 5, 4, 13, 0], ![15, 17, 2, 12, 6, 16, 18, 0], ![5, 7, 18, 12, 5, 10, 4, 0], ![17, 9, 15, 1, 0, 16, 15, 0], ![17, 6, 5, 16, 2, 12, 15, 18]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5, 6, 7]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [19]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 19 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M19
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [19] D q hq hbad)
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

end VoightMaximalOrderD8R66

namespace VoightMaximalOrderD8R70

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1571093125, [1, 7, -28, -20, 30, 9, -10, -1, 1], 7⟩
local notation "l" => [1, 7, -28, -20, 30, 9, -10, -1, 1]
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
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![7, 0, 0, 0, 0, 0, 0, 0], ![0, 7, 0, 0, 0, 0, 0, 0], ![0, 0, 7, 0, 0, 0, 0, 0], ![0, 0, 0, 7, 0, 0, 0, 0], ![0, 0, 0, 0, 7, 0, 0, 0], ![0, 0, 0, 0, 0, 7, 0, 0], ![0, 0, 0, 0, 0, 0, 7, 0], ![2, 3, 1, 0, 4, 3, 2, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -3, -1, 0, -4, -3, -2, 7], ![-1, -2, 4, 3, -6, -2, 1, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -3, -1, 0, -4, -3, -2, 7], ![-3, -10, 27, 20, -34, -12, 8, 7], ![-5, -10, 9, 13, -19, -15, -1, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -3, -1, 0, -4, -3, -2, 7], ![-3, -10, 27, 20, -34, -12, 8, 7], ![-23, -41, 10, 48, -54, -72, -21, 77], ![-14, -34, 55, 57, -79, -48, 3, 41]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -3, -1, 0, -4, -3, -2, 7], ![-3, -10, 27, 20, -34, -12, 8, 7], ![-23, -41, 10, 48, -54, -72, -21, 77], ![-35, -114, 288, 241, -330, -145, 47, 84], ![-47, -105, 127, 178, -201, -170, -13, 144]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -3, -1, 0, -4, -3, -2, 7], ![-3, -10, 27, 20, -34, -12, 8, 7], ![-23, -41, 10, 48, -54, -72, -21, 77], ![-35, -114, 288, 241, -330, -145, 47, 84], ![-178, -344, 175, 540, -451, -639, -155, 581], ![-118, -296, 484, 559, -634, -450, 0, 341]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-2, -3, -1, 0, -4, -3, -2, 7], ![-3, -10, 27, 20, -34, -12, 8, 7], ![-23, -41, 10, 48, -54, -72, -21, 77], ![-35, -114, 288, 241, -330, -145, 47, 84], ![-178, -344, 175, 540, -451, -639, -155, 581], ![-271, -875, 2135, 1918, -2326, -1148, 252, 658], ![-341, -800, 1068, 1507, -1487, -1316, -109, 1023]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -2, 4, 3, -6, -2, 1, 3], ![-5, -10, 9, 13, -19, -15, -1, 16], ![-14, -34, 55, 57, -79, -48, 3, 41], ![-47, -105, 127, 178, -201, -170, -13, 144], ![-118, -296, 484, 559, -634, -450, 0, 341], ![-341, -800, 1068, 1507, -1487, -1316, -109, 1023], ![-291, -712, 1074, 1366, -1416, -1127, -49, 854]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-7]], ![[], [], [], [], [], [], [-49], [-21, -7]], ![[], [], [], [], [], [-49], [-49, -49], [-112, -21, -7]], ![[], [], [], [], [-49], [-49, -49], [-539, -49, -49], [-287, -112, -21, -7]], ![[], [], [], [-49], [-49, -49], [-539, -49, -49], [-588, -539, -49, -49], [-1008, -287, -112, -21, -7]], ![[], [], [-49], [-49, -49], [-539, -49, -49], [-588, -539, -49, -49], [-4067, -588, -539, -49, -49], [-2387, -1008, -287, -112, -21, -7]], ![[], [-7], [-21, -7], [-112, -21, -7], [-287, -112, -21, -7], [-1008, -287, -112, -21, -7], [-2387, -1008, -287, -112, -21, -7], [-2307, -817, -286, -86, -25, -5, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-2, -3, -1, 0, -4, -3, -2, 7], [-1, -2, 4, 3, -6, -2, 1, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-2, -3, -1, 0, -4, -3, -2, 7], [-3, -10, 27, 20, -34, -12, 8, 7], [-5, -10, 9, 13, -19, -15, -1, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-2, -3, -1, 0, -4, -3, -2, 7], [-3, -10, 27, 20, -34, -12, 8, 7], [-23, -41, 10, 48, -54, -72, -21, 77], [-14, -34, 55, 57, -79, -48, 3, 41]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-2, -3, -1, 0, -4, -3, -2, 7], [-3, -10, 27, 20, -34, -12, 8, 7], [-23, -41, 10, 48, -54, -72, -21, 77], [-35, -114, 288, 241, -330, -145, 47, 84], [-47, -105, 127, 178, -201, -170, -13, 144]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-2, -3, -1, 0, -4, -3, -2, 7], [-3, -10, 27, 20, -34, -12, 8, 7], [-23, -41, 10, 48, -54, -72, -21, 77], [-35, -114, 288, 241, -330, -145, 47, 84], [-178, -344, 175, 540, -451, -639, -155, 581], [-118, -296, 484, 559, -634, -450, 0, 341]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-2, -3, -1, 0, -4, -3, -2, 7], [-3, -10, 27, 20, -34, -12, 8, 7], [-23, -41, 10, 48, -54, -72, -21, 77], [-35, -114, 288, 241, -330, -145, 47, 84], [-178, -344, 175, 540, -451, -639, -155, 581], [-271, -875, 2135, 1918, -2326, -1148, 252, 658], [-341, -800, 1068, 1507, -1487, -1316, -109, 1023]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-1, -2, 4, 3, -6, -2, 1, 3], [-5, -10, 9, 13, -19, -15, -1, 16], [-14, -34, 55, 57, -79, -48, 3, 41], [-47, -105, 127, 178, -201, -170, -13, 144], [-118, -296, 484, 559, -634, -450, 0, 341], [-341, -800, 1068, 1507, -1487, -1316, -109, 1023], [-291, -712, 1074, 1366, -1416, -1127, -49, 854]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp61 : Fact (Nat.Prime 61) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 4, 4]
  b' := [1, 0, 1, 4]
  k := [1]
  f := [0, -1, 7, 6, -3, 1, 4, 1]
  g := [1, 1, 3, 2, 1]
  h := [1, 1, 3, 2, 1]
  a := [1, 1, 0, 4]
  b := [1, 0, 1, 4, 3, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [27, 21, 6, 12, 3]
  b' := [20, 20, 5, 17, 14, 14]
  k := [1, 2, 19, 23, 1]
  f := [0, 1, 13, 16, 0, 3, 7, 1]
  g := [1, 19, 25, 0, 5, 11, 1]
  h := [1, 17, 1]
  a := [24, 15, 13, 0, 28]
  b := [1, 15, 1, 0, 25, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD61 : CertificateDedekindCriterionLists l 61 where
  n := 2
  a' := [26, 4, 16, 22, 3, 10]
  b' := [6, 35, 36, 42, 4, 1, 16]
  k := [39, 16, 25, 11, 49, 48, 1]
  f := [5, 2, 5, 4, 0, 3, 6, 1]
  g := [51, 13, 44, 30, 0, 32, 54, 1]
  h := [6, 1]
  a := [25, 56, 13, 35, 40, 5, 35]
  b := [49, 54, 11, 30, 43, 28, 26]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [7] where
  n := 4
  p := ![5, 7, 29, 61]
  exp := ![1, 2, 1, 1]
  pdgood := [5, 29, 61]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp7.out
    exact hp29.out
    exact hp61.out
  a := [460236, -1024086, -2942403, 1545202, 2504442, -309996, -422112]
  b := [-3833, -344602, 495703, 1017877, -246989, -455580, 32154, 52764]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
    exact satisfiesDedekindCriterion_of_certificate_lists T l 61 T_ofList CD61

noncomputable def M7 : MaximalOrderCertificateLists 7 O Om hm where
  m := 2
  n := 6
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [5, 4, 6, 0, 3, 4, 5, 0], [6, 5, 4, 3, 1, 5, 1, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [5, 4, 6, 0, 3, 4, 5, 0], [4, 4, 6, 6, 1, 2, 1, 0], [2, 4, 2, 6, 2, 6, 6, 2]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [5, 4, 6, 0, 3, 4, 5, 0], [4, 4, 6, 6, 1, 2, 1, 0], [5, 1, 3, 6, 2, 5, 0, 0], [0, 1, 6, 1, 5, 1, 3, 6]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [5, 4, 6, 0, 3, 4, 5, 0], [4, 4, 6, 6, 1, 2, 1, 0], [5, 1, 3, 6, 2, 5, 0, 0], [0, 5, 1, 3, 6, 2, 5, 0], [2, 0, 1, 3, 2, 5, 1, 4]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [5, 4, 6, 0, 3, 4, 5, 0], [4, 4, 6, 6, 1, 2, 1, 0], [5, 1, 3, 6, 2, 5, 0, 0], [0, 5, 1, 3, 6, 2, 5, 0], [4, 6, 0, 1, 4, 5, 6, 0], [1, 5, 1, 6, 3, 5, 0, 5]], ![[0, 0, 0, 0, 0, 0, 1, 0], [5, 4, 6, 0, 3, 4, 5, 0], [4, 4, 6, 6, 1, 2, 1, 0], [5, 1, 3, 6, 2, 5, 0, 0], [0, 5, 1, 3, 6, 2, 5, 0], [4, 6, 0, 1, 4, 5, 6, 0], [2, 0, 0, 0, 5, 0, 0, 0], [2, 5, 4, 2, 4, 0, 3, 1]], ![[0, 0, 0, 0, 0, 0, 0, 1], [6, 5, 4, 3, 1, 5, 1, 3], [2, 4, 2, 6, 2, 6, 6, 2], [0, 1, 6, 1, 5, 1, 3, 6], [2, 0, 1, 3, 2, 5, 1, 4], [1, 5, 1, 6, 3, 5, 0, 5], [2, 5, 4, 2, 4, 0, 3, 1], [3, 2, 3, 1, 5, 0, 0, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![4, 0, 1, 2, 3, 1, 0, 0], ![2, 4, 4, 2, 0, 0, 1, 0]]
  b2 := ![![1, 0, 0, 0, 0, 0, 0, 0], ![4, 2, 1, 4, 0, 0, 0, 2], ![2, 4, 5, 2, 0, 0, 0, 0], ![4, 1, 1, 5, 0, 0, 0, 4], ![1, 2, 2, 1, 1, 0, 0, 3], ![5, 4, 3, 0, 4, 0, 0, 1]]
  v := ![![4, 0, 1, 2, 3, 1, 0, 0], ![2, 4, 4, 2, 0, 0, 1, 0]]
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![4, 2, 1, 4, 0, 0, 0, 2], ![2, 4, 5, 2, 0, 0, 0, 0], ![4, 1, 1, 5, 0, 0, 0, 4], ![1, 2, 2, 1, 1, 0, 0, 3], ![5, 4, 3, 0, 4, 0, 0, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 5, 2], ![0, 0, 1, 0, 0, 0, 6, 0], ![0, 0, 0, 1, 0, 0, 5, 4], ![0, 0, 0, 0, 1, 0, 3, 3], ![0, 0, 0, 0, 0, 1, 6, 1]]
  v_ind := ![5, 6]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![0, 1320, 1320, 0, 0, 220, 220, 1320], ![660, 440, 220, 220, 440, 1320, 1100, 660], ![660, 880, 220, 0, 880, 220, 0, 880], ![880, 440, 440, 1100, 1320, 1100, 880, 220], ![220, 220, 220, 0, 0, 1320, 1320, 220], ![660, 0, 1320, 1320, 440, 440, 660, 220], ![0, 880, 0, 220, 440, 660, 220, 0], ![660, 1100, 1320, 220, 660, 220, 660, 0]]
  a := ![![![-1766160, -52360], ![-2416260, -107580]], ![![-2619540, -71940], ![-3435520, 20900]], ![![-1124200, -29260], ![-1584660, -80080]], ![![-1911140, -43120], ![-2530220, 72380]], ![![-2365440, -67760], ![-3001460, 101640]], ![![-1293600, -30800], ![-1681680, 77000]], ![![-575960, -9240], ![-823900, -27720]], ![![-973280, -26180], ![-1168860, 160160]]]
  c := ![![![-319704, -725571, 172491, 789426, -583308, 251482], ![-492464, -994791, 239371, 1088926, -816048, 354602]], ![![-462028, -1072582, 253902, 1166272, -860176, 370804], ![-611436, -1479884, 357324, 1594664, -1177612, 488608]], ![![-196900, -461230, 109010, 501160, -368720, 158840], ![-324324, -645876, 154616, 708576, -531168, 232672]], ![![-325360, -781900, 183700, 848880, -622900, 268200], ![-419836, -1108779, 266959, 1187214, -869972, 354278]], ![![-420504, -967421, 229141, 1052526, -777408, 335482], ![-497644, -1326486, 321266, 1418096, -1040408, 420592]], ![![-224364, -530236, 124696, 575956, -423248, 182372], ![-269780, -749315, 180675, 798790, -583420, 233910]], ![![-93324, -236016, 55396, 255596, -186428, 79772], ![-155400, -341250, 81950, 371540, -275560, 118500]], ![![-173068, -397117, 93137, 432182, -318496, 138034], ![-144592, -561278, 135718, 585328, -419464, 155136]]]
  d := ![![![1540, 1540], ![-29036700, -1188880], ![-2025100, 49280], ![-56157640, -2430120], ![-42698040, -1908060], ![-21442960, -865480]], ![![9240, 7700], ![-44037840, -2443980], ![-2827440, 60060], ![-85152760, -4720100], ![-64299620, -3158540], ![-31181920, -418880]], ![![1540, 0], ![-18863460, -668360], ![-1168860, 52360], ![-36624280, -1412180], ![-27915580, -1165780], ![-13929300, -602140]], ![![7700, 6160], ![-33243980, -1923460], ![-1864940, 60060], ![-64465940, -3682140], ![-48616260, -2353120], ![-23009140, -23100]], ![![9240, 9240], ![-39739700, -2551780], ![-2610300, 26180], ![-76716640, -4824820], ![-57728440, -3039960], ![-27703060, -18480]], ![![3080, 4620], ![-22482460, -1418340], ![-1329020, 23100], ![-43526560, -2679600], ![-32765040, -1658580], ![-15455440, 92400]], ![![4620, 1540], ![-10148600, -378840], ![-502040, 40040], ![-19753580, -774620], ![-14973420, -577500], ![-7156380, -177100]], ![![1540, 4620], ![-17066280, -1449140], ![-1037960, -13860], ![-32985260, -2654960], ![-24681580, -1479940], ![-11323620, 458920]]]
  e := ![![![1232, 583, -143, -858, 1364, -506], ![-5871516, -12037144, 2912404, 13152644, -9851812, 4254908], ![-252108, -844702, 189882, 902072, -630876, 264584], ![-11506592, -23264243, 5637643, 25442638, -19097944, 8259506], ![-8800504, -17660766, 4277306, 19326836, -14519788, 6289692], ![-4225480, -8809190, 2109470, 9628000, -7185660, 3119000]], ![![3248, 1977, -1177, -2622, 2936, -1614], ![-9094652, -17954843, 4330843, 19707498, -14808704, 6485506], ![-296028, -1146787, 250987, 1224082, -845256, 358714], ![-17756948, -34784112, 8408092, 38185972, -28741416, 12576564], ![-13275232, -26417553, 6386193, 28950618, -21766084, 9474506], ![-5690860, -13083390, 3128510, 14184660, -10503860, 4455980]], ![![252, 793, -253, -798, 884, -166], ![-3711540, -7839395, 1892935, 8549350, -6381200, 2744690], ![-125316, -492609, 109109, 522674, -358672, 148518], ![-7319692, -15197803, 3675243, 16592738, -12415324, 5351626], ![-5640416, -11542739, 2788379, 12618094, -9455332, 4090338], ![-2729636, -5680964, 1352604, 6215964, -4634532, 2022848]], ![![532, 1118, -858, -1428, 1524, -876], ![-6801648, -13485212, 3241392, 14808972, -11108256, 4881364], ![-182872, -762248, 162668, 811268, -550584, 233236], ![-13293108, -26206792, 6312592, 28779012, -21622376, 9488904], ![-9883300, -19915645, 4796165, 21818490, -16367480, 7132270], ![-4031160, -9720490, 2310770, 10503960, -7738100, 3256560]], ![![3552, 1783, -1243, -2558, 2864, -1706], ![-8372196, -16075469, 3878149, 17692814, -13331572, 5882198], ![-279668, -1044017, 228217, 1117862, -775396, 332614], ![-16289512, -31130223, 7526123, 34256438, -25848384, 11383166], ![-12050564, -23646031, 5717371, 25945426, -19537988, 8530722], ![-4927720, -11755375, 2812755, 12701510, -9385440, 3937290]], ![![56, -826, -154, 556, -48, -208], ![-4675276, -9088859, 2185799, 9997674, -7512072, 3314618], ![-159308, -545517, 118217, 583822, -402136, 171814], ![-9099660, -17640735, 4250235, 19400030, -14596920, 6428930], ![-6728908, -13406152, 3228412, 14699152, -11037976, 4819244], ![-2701764, -6580586, 1564486, 7099516, -5227688, 2187692]], ![![448, 1862, -462, -1932, 1596, -784], ![-1975652, -4180113, 1001693, 4563258, -3402224, 1471946], ![-34748, -211267, 43967, 221942, -146216, 59654], ![-3888528, -8140027, 1956647, 8891022, -6642216, 2874074], ![-2935912, -6181273, 1488333, 6748098, -5038964, 2176426], ![-1273300, -2964780, 708400, 3218740, -2371180, 1013600]], ![![252, -252, -308, -28, 224, -56], ![-3692948, -6768272, 1630552, 7491932, -5656616, 2540664], ![-143052, -415968, 91168, 449148, -312984, 137536], ![-7156156, -13141044, 3167164, 14534324, -10986332, 4916828], ![-5201280, -10001600, 2403940, 11003720, -8290100, 3653720], ![-1884456, -4938514, 1165934, 5291384, -3881892, 1587628]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 1, Sum.inr 0), (Sum.inr 0, Sum.inr 0), (Sum.inr 1, Sum.inr 0), (Sum.inl 0, Sum.inr 1), (Sum.inl 1, Sum.inr 1)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [7]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 7 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M7
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

end VoightMaximalOrderD8R70

end TraceEuclidean
