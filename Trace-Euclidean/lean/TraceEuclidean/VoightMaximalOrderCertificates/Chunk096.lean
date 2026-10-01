import TraceEuclidean.VoightMaximalOrderCertificates.Chunk092
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

namespace VoightMaximalOrderD8R149

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2393655625, [1, 1, -13, 4, 23, -4, -12, 0, 1], 17⟩
local notation "l" => [1, 1, -13, 4, 23, -4, -12, 0, 1]
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

def basisDenominator : ℤ := 17
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![17, 0, 0, 0, 0, 0, 0, 0], ![0, 17, 0, 0, 0, 0, 0, 0], ![0, 0, 17, 0, 0, 0, 0, 0], ![0, 0, 0, 17, 0, 0, 0, 0], ![0, 0, 0, 0, 17, 0, 0, 0], ![0, 0, 0, 0, 0, 17, 0, 0], ![0, 0, 0, 0, 0, 0, 17, 0], ![8, 12, 4, 0, 14, 9, 2, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-8, -12, -4, 0, -14, -9, -2, 17], ![-1, -1, 1, 0, -3, 0, 1, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-8, -12, -4, 0, -14, -9, -2, 17], ![-1, -1, 13, -4, -23, 4, 12, 0], ![-10, -15, -3, 1, -20, -12, 0, 21]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-8, -12, -4, 0, -14, -9, -2, 17], ![-1, -1, 13, -4, -23, 4, 12, 0], ![-96, -145, -49, 13, -172, -131, -20, 204], ![-21, -31, 6, -3, -62, -20, 9, 42]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-8, -12, -4, 0, -14, -9, -2, 17], ![-1, -1, 13, -4, -23, 4, 12, 0], ![-96, -145, -49, 13, -172, -131, -20, 204], ![-44, -60, 139, -49, -319, 8, 113, 68], ![-114, -171, -25, 6, -255, -143, 4, 237]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-8, -12, -4, 0, -14, -9, -2, 17], ![-1, -1, 13, -4, -23, 4, 12, 0], ![-96, -145, -49, 13, -172, -131, -20, 204], ![-44, -60, 139, -49, -319, 8, 113, 68], ![-972, -1468, -444, 139, -1835, -1336, -150, 2057], ![-269, -399, 50, -25, -761, -291, 86, 542]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-8, -12, -4, 0, -14, -9, -2, 17], ![-1, -1, 13, -4, -23, 4, 12, 0], ![-96, -145, -49, 13, -172, -131, -20, 204], ![-44, -60, 139, -49, -319, 8, 113, 68], ![-972, -1468, -444, 139, -1835, -1336, -150, 2057], ![-857, -1229, 1189, -444, -3932, -485, 1021, 1564], ![-1230, -1843, -201, 50, -2855, -1535, 79, 2546]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-1, -1, 1, 0, -3, 0, 1, 2], ![-10, -15, -3, 1, -20, -12, 0, 21], ![-21, -31, 6, -3, -62, -20, 9, 42], ![-114, -171, -25, 6, -255, -143, 4, 237], ![-269, -399, 50, -25, -761, -291, 86, 542], ![-1230, -1843, -201, 50, -2855, -1535, 79, 2546], ![-571, -851, 5, -14, -1467, -665, 109, 1167]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-17]], ![[], [], [], [], [], [], [-289], [-34, -17]], ![[], [], [], [], [], [-289], [0, -289], [-357, -34, -17]], ![[], [], [], [], [-289], [0, -289], [-3468, 0, -289], [-714, -357, -34, -17]], ![[], [], [], [-289], [0, -289], [-3468, 0, -289], [-1156, -3468, 0, -289], [-4029, -714, -357, -34, -17]], ![[], [], [-289], [0, -289], [-3468, 0, -289], [-1156, -3468, 0, -289], [-34969, -1156, -3468, 0, -289], [-9214, -4029, -714, -357, -34, -17]], ![[], [-17], [-34, -17], [-357, -34, -17], [-714, -357, -34, -17], [-4029, -714, -357, -34, -17], [-9214, -4029, -714, -357, -34, -17], [-6371, -1692, -538, -116, -34, -4, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-8, -12, -4, 0, -14, -9, -2, 17], [-1, -1, 1, 0, -3, 0, 1, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-8, -12, -4, 0, -14, -9, -2, 17], [-1, -1, 13, -4, -23, 4, 12, 0], [-10, -15, -3, 1, -20, -12, 0, 21]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-8, -12, -4, 0, -14, -9, -2, 17], [-1, -1, 13, -4, -23, 4, 12, 0], [-96, -145, -49, 13, -172, -131, -20, 204], [-21, -31, 6, -3, -62, -20, 9, 42]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-8, -12, -4, 0, -14, -9, -2, 17], [-1, -1, 13, -4, -23, 4, 12, 0], [-96, -145, -49, 13, -172, -131, -20, 204], [-44, -60, 139, -49, -319, 8, 113, 68], [-114, -171, -25, 6, -255, -143, 4, 237]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-8, -12, -4, 0, -14, -9, -2, 17], [-1, -1, 13, -4, -23, 4, 12, 0], [-96, -145, -49, 13, -172, -131, -20, 204], [-44, -60, 139, -49, -319, 8, 113, 68], [-972, -1468, -444, 139, -1835, -1336, -150, 2057], [-269, -399, 50, -25, -761, -291, 86, 542]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-8, -12, -4, 0, -14, -9, -2, 17], [-1, -1, 13, -4, -23, 4, 12, 0], [-96, -145, -49, 13, -172, -131, -20, 204], [-44, -60, 139, -49, -319, 8, 113, 68], [-972, -1468, -444, 139, -1835, -1336, -150, 2057], [-857, -1229, 1189, -444, -3932, -485, 1021, 1564], [-1230, -1843, -201, 50, -2855, -1535, 79, 2546]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-1, -1, 1, 0, -3, 0, 1, 2], [-10, -15, -3, 1, -20, -12, 0, 21], [-21, -31, 6, -3, -62, -20, 9, 42], [-114, -171, -25, 6, -255, -143, 4, 237], [-269, -399, 50, -25, -761, -291, 86, 542], [-1230, -1843, -201, 50, -2855, -1535, 79, 2546], [-571, -851, 5, -14, -1467, -665, 109, 1167]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp17 : Fact (Nat.Prime 17) := fact_iff.2 (by norm_num)
instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp103 : Fact (Nat.Prime 103) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 3, 1]
  b' := [2, 2, 3, 1]
  k := [1]
  f := [0, 1, 6, 4, -1, 2, 4]
  g := [1, 3, 4, 0, 1]
  h := [1, 3, 4, 0, 1]
  a := [1, 4]
  b := [1, 1, 3, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD19 : CertificateDedekindCriterionLists l 19 where
  n := 2
  a' := [4, 10, 5, 17]
  b' := [1, 3, 1, 2, 13]
  k := [5, 13, 16, 7, 1]
  f := [1, 5, 7, 2, 2, 3, 5, 1]
  g := [10, 18, 1, 9, 3, 13, 1]
  h := [2, 6, 1]
  a := [13, 6, 5, 1, 11, 13]
  b := [14, 0, 5, 7, 8, 17, 6]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD103 : CertificateDedekindCriterionLists l 103 where
  n := 2
  a' := [47, 27, 66, 50, 90]
  b' := [57, 45, 24, 20, 86, 88]
  k := [8, 43, 87, 55, 1]
  f := [11, 23, 34, 19, 6, 34, 19, 1]
  g := [27, 41, 59, 12, 7, 79, 1]
  h := [42, 24, 1]
  a := [8, 87, 74, 17, 89, 44]
  b := [54, 97, 40, 98, 30, 79, 59]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [17] where
  n := 4
  p := ![5, 17, 19, 103]
  exp := ![1, 2, 1, 1]
  pdgood := [5, 19, 103]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp17.out
    exact hp19.out
    exact hp103.out
  a := [4252848, -35099424, -64077312, 45198272, 73552512, -2624000, -8543936]
  b := [-1424983, -6202982, 10286024, 18545980, -8235772, -12398040, 328000, 1067992]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19 T_ofList CD19
    exact satisfiesDedekindCriterion_of_certificate_lists T l 103 T_ofList CD103

noncomputable def M17 : MaximalOrderCertificateOfUnramifiedLists 17 O Om hm where
  n := 8
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [9, 5, 13, 0, 3, 8, 15, 0], [16, 16, 1, 0, 14, 0, 1, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [9, 5, 13, 0, 3, 8, 15, 0], [16, 16, 13, 13, 11, 4, 12, 0], [7, 2, 14, 1, 14, 5, 0, 4]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [9, 5, 13, 0, 3, 8, 15, 0], [16, 16, 13, 13, 11, 4, 12, 0], [6, 8, 2, 13, 15, 5, 14, 0], [13, 3, 6, 14, 6, 14, 9, 8]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [9, 5, 13, 0, 3, 8, 15, 0], [16, 16, 13, 13, 11, 4, 12, 0], [6, 8, 2, 13, 15, 5, 14, 0], [7, 8, 3, 2, 4, 8, 11, 0], [5, 16, 9, 6, 0, 10, 4, 16]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [9, 5, 13, 0, 3, 8, 15, 0], [16, 16, 13, 13, 11, 4, 12, 0], [6, 8, 2, 13, 15, 5, 14, 0], [7, 8, 3, 2, 4, 8, 11, 0], [14, 11, 15, 3, 1, 7, 3, 0], [3, 9, 16, 9, 4, 15, 1, 15]], ![[0, 0, 0, 0, 0, 0, 1, 0], [9, 5, 13, 0, 3, 8, 15, 0], [16, 16, 13, 13, 11, 4, 12, 0], [6, 8, 2, 13, 15, 5, 14, 0], [7, 8, 3, 2, 4, 8, 11, 0], [14, 11, 15, 3, 1, 7, 3, 0], [10, 12, 16, 15, 12, 8, 1, 0], [11, 10, 3, 16, 1, 12, 11, 13]], ![[0, 0, 0, 0, 0, 0, 0, 1], [16, 16, 1, 0, 14, 0, 1, 2], [7, 2, 14, 1, 14, 5, 0, 4], [13, 3, 6, 14, 6, 14, 9, 8], [5, 16, 9, 6, 0, 10, 4, 16], [3, 9, 16, 9, 4, 15, 1, 15], [11, 10, 3, 16, 1, 12, 11, 13], [7, 16, 5, 3, 12, 15, 7, 11]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![16, 15, 7, 13, 1, 6, 11, 0], ![11, 12, 6, 7, 6, 4, 3, 0], ![13, 8, 10, 9, 2, 4, 1, 0], ![14, 12, 9, 9, 0, 13, 9, 0], ![9, 15, 8, 16, 1, 3, 6, 0], ![10, 12, 16, 4, 12, 8, 1, 0], ![0, 15, 0, 4, 5, 4, 1, 16]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5, 6, 7]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [17]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 17 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M17
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [17] D q hq hbad)
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

end VoightMaximalOrderD8R149

namespace VoightMaximalOrderD8R153

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2450570632, [4, 4, -21, -8, 25, 6, -9, -1, 1], 2⟩
local notation "l" => [4, 4, -21, -8, 25, 6, -9, -1, 1]
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
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![2, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 0, 0], ![0, 0, 0, 2, 0, 0, 0, 0], ![0, 0, 0, 0, 2, 0, 0, 0], ![0, 0, 0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 0, 2, 0], ![0, 1, 0, 1, 0, 1, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, -1, 0, -1, 0, -1, -1, 2], ![-2, -3, 11, 3, -12, -4, 4, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, -1, 0, -1, 0, -1, -1, 2], ![-4, -5, 21, 7, -25, -7, 8, 2], ![-4, -12, 19, 13, -21, -24, 0, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, -1, 0, -1, 0, -1, -1, 2], ![-4, -5, 21, 7, -25, -7, 8, 2], ![-4, -18, 17, 19, -17, -41, -7, 20], ![-24, -40, 120, 55, -131, -69, 24, 24]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, -1, 0, -1, 0, -1, -1, 2], ![-4, -5, 21, 7, -25, -7, 8, 2], ![-4, -18, 17, 19, -17, -41, -7, 20], ![-40, -57, 202, 84, -221, -90, 46, 26], ![-48, -120, 224, 168, -233, -251, 3, 96]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, -1, 0, -1, 0, -1, -1, 2], ![-4, -5, 21, 7, -25, -7, 8, 2], ![-4, -18, 17, 19, -17, -41, -7, 20], ![-40, -57, 202, 84, -221, -90, 46, 26], ![-52, -164, 229, 234, -228, -371, -32, 144], ![-192, -339, 936, 509, -984, -620, 130, 198]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![0, -1, 0, -1, 0, -1, -1, 2], ![-4, -5, 21, 7, -25, -7, 8, 2], ![-4, -18, 17, 19, -17, -41, -7, 20], ![-40, -57, 202, 84, -221, -90, 46, 26], ![-52, -164, 229, 234, -228, -371, -32, 144], ![-288, -452, 1420, 693, -1494, -772, 237, 224], ![-396, -916, 1839, 1400, -1867, -1906, 42, 656]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-2, -3, 11, 3, -12, -4, 4, 2], ![-4, -12, 19, 13, -21, -24, 0, 12], ![-24, -40, 120, 55, -131, -69, 24, 24], ![-48, -120, 224, 168, -233, -251, 3, 96], ![-192, -339, 936, 509, -984, -620, 130, 198], ![-396, -916, 1839, 1400, -1867, -1906, 42, 656], ![-963, -1852, 4603, 2866, -4733, -3566, 438, 1138]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-2]], ![[], [], [], [], [], [], [-4], [-4, -2]], ![[], [], [], [], [], [-4], [-4, -4], [-24, -4, -2]], ![[], [], [], [], [-4], [-4, -4], [-40, -4, -4], [-48, -24, -4, -2]], ![[], [], [], [-4], [-4, -4], [-40, -4, -4], [-52, -40, -4, -4], [-192, -48, -24, -4, -2]], ![[], [], [-4], [-4, -4], [-40, -4, -4], [-52, -40, -4, -4], [-288, -52, -40, -4, -4], [-396, -192, -48, -24, -4, -2]], ![[], [-2], [-4, -2], [-24, -4, -2], [-48, -24, -4, -2], [-192, -48, -24, -4, -2], [-396, -192, -48, -24, -4, -2], [-963, -320, -133, -38, -15, -3, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, -1, 0, -1, 0, -1, -1, 2], [-2, -3, 11, 3, -12, -4, 4, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, -1, 0, -1, 0, -1, -1, 2], [-4, -5, 21, 7, -25, -7, 8, 2], [-4, -12, 19, 13, -21, -24, 0, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, -1, 0, -1, 0, -1, -1, 2], [-4, -5, 21, 7, -25, -7, 8, 2], [-4, -18, 17, 19, -17, -41, -7, 20], [-24, -40, 120, 55, -131, -69, 24, 24]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, -1, 0, -1, 0, -1, -1, 2], [-4, -5, 21, 7, -25, -7, 8, 2], [-4, -18, 17, 19, -17, -41, -7, 20], [-40, -57, 202, 84, -221, -90, 46, 26], [-48, -120, 224, 168, -233, -251, 3, 96]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, -1, 0, -1, 0, -1, -1, 2], [-4, -5, 21, 7, -25, -7, 8, 2], [-4, -18, 17, 19, -17, -41, -7, 20], [-40, -57, 202, 84, -221, -90, 46, 26], [-52, -164, 229, 234, -228, -371, -32, 144], [-192, -339, 936, 509, -984, -620, 130, 198]], ![[0, 0, 0, 0, 0, 0, 1, 0], [0, -1, 0, -1, 0, -1, -1, 2], [-4, -5, 21, 7, -25, -7, 8, 2], [-4, -18, 17, 19, -17, -41, -7, 20], [-40, -57, 202, 84, -221, -90, 46, 26], [-52, -164, 229, 234, -228, -371, -32, 144], [-288, -452, 1420, 693, -1494, -772, 237, 224], [-396, -916, 1839, 1400, -1867, -1906, 42, 656]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-2, -3, 11, 3, -12, -4, 4, 2], [-4, -12, 19, 13, -21, -24, 0, 12], [-24, -40, 120, 55, -131, -69, 24, 24], [-48, -120, 224, 168, -233, -251, 3, 96], [-192, -339, 936, 509, -984, -620, 130, 198], [-396, -916, 1839, 1400, -1867, -1906, 42, 656], [-963, -1852, 4603, 2866, -4733, -3566, 438, 1138]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp269 : Fact (Nat.Prime 269) := fact_iff.2 (by norm_num)
instance hp1138741 : Fact (Nat.Prime 1138741) := fact_iff.2 (by norm_num)

def CD269 : CertificateDedekindCriterionLists l 269 where
  n := 2
  a' := [31, 182, 183, 10, 70, 147]
  b' := [9, 122, 41, 182, 165, 132, 248]
  k := [211, 109, 170, 80, 68, 265, 1]
  f := [92, 122, 49, 11, 92, 32, 67, 1]
  g := [182, 240, 95, 21, 182, 62, 132, 1]
  h := [136, 1]
  a := [178, 247, 81, 192, 202, 156, 255]
  b := [80, 76, 248, 65, 249, 10, 14]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1138741 : CertificateDedekindCriterionLists l 1138741 where
  n := 2
  a' := [962664, 620482, 95038, 9572, 814208, 347474]
  b' := [78092, 1126649, 485616, 823790, 424322, 987772, 601070]
  k := [101462, 216881, 391217, 199352, 730593, 426230, 1]
  f := [133896, 102154, 137887, 212122, 41660, 232090, 244801, 1]
  g := [427988, 326526, 440744, 678030, 133161, 741857, 782485, 1]
  h := [356255, 1]
  a := [212893, 766416, 911646, 654261, 688303, 500086, 137998]
  b := [747808, 925285, 604776, 840392, 893249, 730468, 1000743]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 3
  p := ![2, 269, 1138741]
  exp := ![4, 1, 1]
  pdgood := [269, 1138741]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp269.out
    exact hp1138741.out
  a := [1502629586, -1783332568, -19247693376, -5432822966, 13995750572, 1785975779, -2388640168]
  b := [-277344270, -2631411853, -374058806, 5540797701, 1227983496, -2426025187, -260569475, 298580021]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 269 T_ofList CD269
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1138741 T_ofList CD1138741

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 1
  n := 7
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 1, 0, 1, 1, 0], [0, 1, 1, 1, 0, 0, 0, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 1, 0, 1, 1, 0], [0, 1, 1, 1, 1, 1, 0, 0], [0, 0, 1, 1, 1, 0, 0, 0]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 1, 0, 1, 1, 0], [0, 1, 1, 1, 1, 1, 0, 0], [0, 0, 1, 1, 1, 1, 1, 0], [0, 0, 0, 1, 1, 1, 0, 0]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 1, 0, 1, 1, 0], [0, 1, 1, 1, 1, 1, 0, 0], [0, 0, 1, 1, 1, 1, 1, 0], [0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 1, 0]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 1, 0, 1, 1, 0], [0, 1, 1, 1, 1, 1, 0, 0], [0, 0, 1, 1, 1, 1, 1, 0], [0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0]], ![[0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 1, 0, 1, 1, 0], [0, 1, 1, 1, 1, 1, 0, 0], [0, 0, 1, 1, 1, 1, 1, 0], [0, 1, 0, 0, 1, 0, 0, 0], [0, 0, 1, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 1, 0], [0, 0, 1, 0, 1, 0, 0, 0]], ![[0, 0, 0, 0, 0, 0, 0, 1], [0, 1, 1, 1, 0, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0, 0], [0, 0, 0, 1, 1, 1, 0, 0], [0, 0, 0, 0, 1, 1, 1, 0], [0, 1, 0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0, 0], [1, 0, 1, 0, 1, 0, 0, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![1, 1, 1, 0, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 1, 0, 0], ![0, 0, 0, 1, 1, 1, 1, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 1, 1, 0], ![0, 0, 0, 0, 0, 0, 1, 0]]
  v := ![![1, 1, 1, 0, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 1, 0, 0], ![0, 0, 0, 1, 1, 1, 1, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 1, 1, 0], ![0, 0, 0, 0, 0, 0, 1, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0]]
  v_ind := ![7]
  w_ind := ![0, 1, 2, 3, 4, 5, 6]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 1, 1, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 1, 0, 0], ![0, 0, 1, 1, 0, 0, 0, 0], ![0, 0, 1, 1, 1, 1, 0, 0], ![0, 0, 1, 1, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0]]
  a := ![![![37]], ![![1168]], ![![980]], ![![334]], ![![36]], ![![332]], ![![236]], ![![24]]]
  c := ![![![-32, -44, -31, 177, 96, -67, 110]], ![![-1071, -1524, -875, 6534, 3273, -2685, 3783]], ![![-822, -1201, -418, 4776, 2281, -2088, 2610]], ![![-302, -424, -265, 1771, 913, -707, 1053]], ![![-32, -44, -31, 177, 96, -67, 110]], ![![-300, -422, -261, 1760, 906, -704, 1044]], ![![-228, -314, -253, 1379, 734, -523, 853]], ![![-24, -32, -33, 142, 80, -49, 94]]]
  d := ![![![0], ![12], ![56], ![0], ![8], ![52], ![44]], ![![2], ![668], ![1960], ![48], ![424], ![1768], ![1320]], ![![0], ![544], ![1360], ![48], ![392], ![1260], ![828]], ![![0], ![160], ![544], ![8], ![104], ![496], ![388]], ![![0], ![12], ![56], ![0], ![8], ![52], ![44]], ![![0], ![160], ![540], ![8], ![104], ![492], ![384]], ![![0], ![112], ![440], ![4], ![64], ![396], ![332]], ![![0], ![8], ![48], ![0], ![4], ![44], ![40]]]
  e := ![![![1, 0, 0, 2, 1, -1, 1], ![-10, -12, -10, 41, 28, -12, 30], ![-40, -58, -8, 176, 89, -78, 96], ![0, 0, 0, 0, 0, 1, 0], ![-8, -10, -14, 40, 28, -10, 31], ![-38, -55, -12, 175, 88, -75, 97], ![-30, -45, 3, 135, 61, -67, 66]], ![![0, 0, 0, 0, 0, 0, 0], ![-604, -848, -530, 3542, 1826, -1414, 2106], ![-1644, -2402, -836, 9552, 4562, -4176, 5220], ![-48, -64, -66, 284, 160, -98, 188], ![-408, -564, -440, 2474, 1308, -948, 1518], ![-1500, -2186, -820, 8790, 4218, -3814, 4838], ![-1060, -1582, -310, 6102, 2782, -2804, 3164]], ![![0, 0, 1, 0, 0, 0, 0], ![-432, -628, -192, 2311, 1124, -1008, 1270], ![-1220, -1720, -1036, 7134, 3655, -2870, 4212], ![-32, -48, 6, 136, 62, -69, 64], ![-300, -446, -70, 1606, 740, -740, 833], ![-1122, -1589, -904, 6565, 3334, -2673, 3837], ![-798, -1105, -855, 4863, 2559, -1873, 2972]], ![![0, 1, 0, 0, 0, 0, 0], ![-140, -192, -135, 746, 412, -278, 470], ![-432, -628, -192, 2311, 1124, -1008, 1270], ![-8, -10, -14, 40, 27, -10, 32], ![-100, -134, -128, 570, 322, -199, 374], ![-400, -580, -198, 2176, 1062, -940, 1207], ![-294, -439, -52, 1567, 714, -733, 799]], ![![0, 0, 0, 2, 1, -1, 1], ![-10, -13, -10, 41, 28, -12, 30], ![-40, -58, -9, 176, 89, -78, 96], ![0, 0, 0, -1, 0, 1, 0], ![-8, -10, -14, 40, 27, -10, 31], ![-38, -55, -12, 175, 88, -76, 97], ![-30, -45, 3, 135, 61, -67, 65]], ![![0, 0, 1, 1, 1, -1, 0], ![-140, -192, -136, 745, 411, -277, 469], ![-430, -625, -196, 2311, 1123, -1006, 1272], ![-8, -10, -15, 40, 27, -9, 32], ![-100, -134, -128, 569, 322, -199, 373], ![-398, -577, -202, 2175, 1061, -937, 1208], ![-292, -436, -55, 1566, 713, -731, 801]], ![![0, 0, 0, 1, 1, 0, 0], ![-108, -144, -142, 610, 349, -209, 406], ![-332, -494, -64, 1742, 802, -809, 897], ![-6, -7, -18, 39, 26, -7, 34], ![-76, -96, -149, 474, 287, -140, 341], ![-306, -453, -88, 1646, 766, -748, 867], ![-226, -353, 83, 1133, 454, -603, 489]], ![![0, 0, 0, 1, 0, 0, 0], ![-8, -10, -14, 40, 27, -10, 32], ![-32, -48, 6, 136, 62, -69, 64], ![0, 0, 0, 0, 0, 0, 1], ![-6, -7, -18, 39, 26, -7, 33], ![-30, -45, 3, 135, 61, -67, 66], ![-24, -38, 21, 95, 35, -59, 31]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 0, Sum.inr 1), (Sum.inr 0, Sum.inr 1), (Sum.inr 1, Sum.inr 1), (Sum.inr 2, Sum.inr 1), (Sum.inr 3, Sum.inr 1), (Sum.inr 4, Sum.inr 1)]
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

end VoightMaximalOrderD8R153

namespace VoightMaximalOrderD10R27

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1131659253125, [-1, -6, 0, 31, 10, -48, -6, 28, -4, -4, 1], 23⟩
local notation "l" => [-1, -6, 0, 31, 10, -48, -6, 28, -4, -4, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsTen := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsTen_irreducible row row_mem
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
def basisNumerator : Fin 10 → Fin 10 → ℤ := ![![23, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 23, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 23, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 23, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 23, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 23, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 23, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 23, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 23, 0], ![9, 20, 19, 7, 19, 5, 7, 18, 14, 1]]

noncomputable def BQ : SubalgebraBuilderLists 10 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![-9, -20, -19, -7, -19, -5, -7, -18, -14, 23], ![-7, -15, -14, -6, -15, -1, -5, -15, -10, 18]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![-9, -20, -19, -7, -19, -5, -7, -18, -14, 23], ![-35, -74, -76, -59, -86, 28, -22, -100, -52, 92], ![-36, -77, -77, -52, -86, 17, -21, -95, -55, 94]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![-9, -20, -19, -7, -19, -5, -7, -18, -14, 23], ![-35, -74, -76, -59, -86, 28, -22, -100, -52, 92], ![-176, -375, -374, -264, -451, 82, -68, -466, -292, 460], ![-163, -346, -348, -256, -417, 95, -68, -441, -265, 427]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![-9, -20, -19, -7, -19, -5, -7, -18, -14, 23], ![-35, -74, -76, -59, -86, 28, -22, -100, -52, 92], ![-176, -375, -374, -264, -451, 82, -68, -466, -292, 460], ![-592, -1236, -1267, -1090, -1616, 549, -174, -1712, -978, 1564], ![-604, -1268, -1289, -1055, -1626, 481, -185, -1703, -1001, 1591]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![-9, -20, -19, -7, -19, -5, -7, -18, -14, 23], ![-35, -74, -76, -59, -86, 28, -22, -100, -52, 92], ![-176, -375, -374, -264, -451, 82, -68, -466, -292, 460], ![-592, -1236, -1267, -1090, -1616, 549, -174, -1712, -978, 1564], ![-2146, -4492, -4550, -3805, -5968, 1710, -425, -6030, -3660, 5658], ![-2128, -4449, -4523, -3828, -5901, 1788, -467, -6032, -3599, 5615]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![-9, -20, -19, -7, -19, -5, -7, -18, -14, 23], ![-35, -74, -76, -59, -86, 28, -22, -100, -52, 92], ![-176, -375, -374, -264, -451, 82, -68, -466, -292, 460], ![-592, -1236, -1267, -1090, -1616, 549, -174, -1712, -978, 1564], ![-2146, -4492, -4550, -3805, -5968, 1710, -425, -6030, -3660, 5658], ![-6666, -13816, -14164, -12878, -19135, 6674, -960, -19415, -11370, 17664], ![-6914, -14373, -14678, -13020, -19672, 6479, -1094, -19910, -11796, 18293]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![-9, -20, -19, -7, -19, -5, -7, -18, -14, 23], ![-35, -74, -76, -59, -86, 28, -22, -100, -52, 92], ![-176, -375, -374, -264, -451, 82, -68, -466, -292, 460], ![-592, -1236, -1267, -1090, -1616, 549, -174, -1712, -978, 1564], ![-2146, -4492, -4550, -3805, -5968, 1710, -425, -6030, -3660, 5658], ![-6666, -13816, -14164, -12878, -19135, 6674, -960, -19415, -11370, 17664], ![-21318, -44226, -45082, -40558, -61808, 20051, -2056, -61260, -36875, 56442], ![-21887, -45389, -46351, -41864, -63291, 21015, -2414, -63161, -37696, 57966]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![-9, -20, -19, -7, -19, -5, -7, -18, -14, 23], ![-35, -74, -76, -59, -86, 28, -22, -100, -52, 92], ![-176, -375, -374, -264, -451, 82, -68, -466, -292, 460], ![-592, -1236, -1267, -1090, -1616, 549, -174, -1712, -978, 1564], ![-2146, -4492, -4550, -3805, -5968, 1710, -425, -6030, -3660, 5658], ![-6666, -13816, -14164, -12878, -19135, 6674, -960, -19415, -11370, 17664], ![-21318, -44226, -45082, -40558, -61808, 20051, -2056, -61260, -36875, 56442], ![-63219, -130448, -133789, -125609, -186563, 66125, -4034, -184936, -109430, 167831], ![-66498, -137457, -140689, -130275, -195130, 67223, -4943, -193376, -115077, 176380]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-7, -15, -14, -6, -15, -1, -5, -15, -10, 18], ![-36, -77, -77, -52, -86, 17, -21, -95, -55, 94], ![-163, -346, -348, -256, -417, 95, -68, -441, -265, 427], ![-604, -1268, -1289, -1055, -1626, 481, -185, -1703, -1001, 1591], ![-2128, -4449, -4523, -3828, -5901, 1788, -467, -6032, -3599, 5615], ![-6914, -14373, -14678, -13020, -19672, 6479, -1094, -19910, -11796, 18293], ![-21887, -45389, -46351, -41864, -63291, 21015, -2414, -63161, -37696, 57966], ![-66498, -137457, -140689, -130275, -195130, 67223, -4943, -193376, -115077, 176380], ![-69408, -143617, -146883, -134959, -202762, 69029, -5925, -201326, -119930, 184012]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-23]], ![[], [], [], [], [], [], [], [], [-529], [-414, -23]], ![[], [], [], [], [], [], [], [-529], [-2116, -529], [-2162, -414, -23]], ![[], [], [], [], [], [], [-529], [-2116, -529], [-10580, -2116, -529], [-9821, -2162, -414, -23]], ![[], [], [], [], [], [-529], [-2116, -529], [-10580, -2116, -529], [-35972, -10580, -2116, -529], [-36593, -9821, -2162, -414, -23]], ![[], [], [], [], [-529], [-2116, -529], [-10580, -2116, -529], [-35972, -10580, -2116, -529], [-130134, -35972, -10580, -2116, -529], [-129145, -36593, -9821, -2162, -414, -23]], ![[], [], [], [-529], [-2116, -529], [-10580, -2116, -529], [-35972, -10580, -2116, -529], [-130134, -35972, -10580, -2116, -529], [-406272, -130134, -35972, -10580, -2116, -529], [-420739, -129145, -36593, -9821, -2162, -414, -23]], ![[], [], [-529], [-2116, -529], [-10580, -2116, -529], [-35972, -10580, -2116, -529], [-130134, -35972, -10580, -2116, -529], [-406272, -130134, -35972, -10580, -2116, -529], [-1298166, -406272, -130134, -35972, -10580, -2116, -529], [-1333218, -420739, -129145, -36593, -9821, -2162, -414, -23]], ![[], [-23], [-414, -23], [-2162, -414, -23], [-9821, -2162, -414, -23], [-36593, -9821, -2162, -414, -23], [-129145, -36593, -9821, -2162, -414, -23], [-420739, -129145, -36593, -9821, -2162, -414, -23], [-1333218, -420739, -129145, -36593, -9821, -2162, -414, -23], [-1373571, -430341, -129349, -36342, -9392, -2074, -364, -32, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 10 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 10) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 10) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 10) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [-9, -20, -19, -7, -19, -5, -7, -18, -14, 23], [-7, -15, -14, -6, -15, -1, -5, -15, -10, 18]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [-9, -20, -19, -7, -19, -5, -7, -18, -14, 23], [-35, -74, -76, -59, -86, 28, -22, -100, -52, 92], [-36, -77, -77, -52, -86, 17, -21, -95, -55, 94]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [-9, -20, -19, -7, -19, -5, -7, -18, -14, 23], [-35, -74, -76, -59, -86, 28, -22, -100, -52, 92], [-176, -375, -374, -264, -451, 82, -68, -466, -292, 460], [-163, -346, -348, -256, -417, 95, -68, -441, -265, 427]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [-9, -20, -19, -7, -19, -5, -7, -18, -14, 23], [-35, -74, -76, -59, -86, 28, -22, -100, -52, 92], [-176, -375, -374, -264, -451, 82, -68, -466, -292, 460], [-592, -1236, -1267, -1090, -1616, 549, -174, -1712, -978, 1564], [-604, -1268, -1289, -1055, -1626, 481, -185, -1703, -1001, 1591]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [-9, -20, -19, -7, -19, -5, -7, -18, -14, 23], [-35, -74, -76, -59, -86, 28, -22, -100, -52, 92], [-176, -375, -374, -264, -451, 82, -68, -466, -292, 460], [-592, -1236, -1267, -1090, -1616, 549, -174, -1712, -978, 1564], [-2146, -4492, -4550, -3805, -5968, 1710, -425, -6030, -3660, 5658], [-2128, -4449, -4523, -3828, -5901, 1788, -467, -6032, -3599, 5615]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [-9, -20, -19, -7, -19, -5, -7, -18, -14, 23], [-35, -74, -76, -59, -86, 28, -22, -100, -52, 92], [-176, -375, -374, -264, -451, 82, -68, -466, -292, 460], [-592, -1236, -1267, -1090, -1616, 549, -174, -1712, -978, 1564], [-2146, -4492, -4550, -3805, -5968, 1710, -425, -6030, -3660, 5658], [-6666, -13816, -14164, -12878, -19135, 6674, -960, -19415, -11370, 17664], [-6914, -14373, -14678, -13020, -19672, 6479, -1094, -19910, -11796, 18293]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [-9, -20, -19, -7, -19, -5, -7, -18, -14, 23], [-35, -74, -76, -59, -86, 28, -22, -100, -52, 92], [-176, -375, -374, -264, -451, 82, -68, -466, -292, 460], [-592, -1236, -1267, -1090, -1616, 549, -174, -1712, -978, 1564], [-2146, -4492, -4550, -3805, -5968, 1710, -425, -6030, -3660, 5658], [-6666, -13816, -14164, -12878, -19135, 6674, -960, -19415, -11370, 17664], [-21318, -44226, -45082, -40558, -61808, 20051, -2056, -61260, -36875, 56442], [-21887, -45389, -46351, -41864, -63291, 21015, -2414, -63161, -37696, 57966]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [-9, -20, -19, -7, -19, -5, -7, -18, -14, 23], [-35, -74, -76, -59, -86, 28, -22, -100, -52, 92], [-176, -375, -374, -264, -451, 82, -68, -466, -292, 460], [-592, -1236, -1267, -1090, -1616, 549, -174, -1712, -978, 1564], [-2146, -4492, -4550, -3805, -5968, 1710, -425, -6030, -3660, 5658], [-6666, -13816, -14164, -12878, -19135, 6674, -960, -19415, -11370, 17664], [-21318, -44226, -45082, -40558, -61808, 20051, -2056, -61260, -36875, 56442], [-63219, -130448, -133789, -125609, -186563, 66125, -4034, -184936, -109430, 167831], [-66498, -137457, -140689, -130275, -195130, 67223, -4943, -193376, -115077, 176380]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-7, -15, -14, -6, -15, -1, -5, -15, -10, 18], [-36, -77, -77, -52, -86, 17, -21, -95, -55, 94], [-163, -346, -348, -256, -417, 95, -68, -441, -265, 427], [-604, -1268, -1289, -1055, -1626, 481, -185, -1703, -1001, 1591], [-2128, -4449, -4523, -3828, -5901, 1788, -467, -6032, -3599, 5615], [-6914, -14373, -14678, -13020, -19672, 6479, -1094, -19910, -11796, 18293], [-21887, -45389, -46351, -41864, -63291, 21015, -2414, -63161, -37696, 57966], [-66498, -137457, -140689, -130275, -195130, 67223, -4943, -193376, -115077, 176380], [-69408, -143617, -146883, -134959, -202762, 69029, -5925, -201326, -119930, 184012]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp23 : Fact (Nat.Prime 23) := fact_iff.2 (by norm_num)
instance hp5471 : Fact (Nat.Prime 5471) := fact_iff.2 (by norm_num)
instance hp66191 : Fact (Nat.Prime 66191) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 3, 3]
  b' := [2, 3, 2, 0, 1]
  k := [1]
  f := [1, 2, 1, -5, 1, 12, 3, -4, 3, 2]
  g := [2, 1, 1, 1, 3, 1]
  h := [2, 1, 1, 1, 3, 1]
  a := [2, 4, 4, 2, 4]
  b := [2, 0, 2, 1, 1, 3, 1, 3, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD5471 : CertificateDedekindCriterionLists l 5471 where
  n := 2
  a' := [4850, 1240, 4120, 800, 3435, 2147, 2800, 1390]
  b' := [334, 2199, 5107, 4757, 14, 3372, 3941, 5353, 2885]
  k := [1627, 4970, 1108, 3708, 2672, 2308, 490, 5114, 1]
  f := [2879, 1849, 1904, 2407, 2561, 2758, 670, 211, 1360, 1]
  g := [5409, 3472, 3576, 4521, 4810, 5180, 1257, 396, 2555, 1]
  h := [2912, 1]
  a := [5381, 3649, 5178, 440, 1936, 4106, 1843, 545, 2400]
  b := [1733, 4464, 300, 273, 671, 2261, 1741, 651, 3071]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD66191 : CertificateDedekindCriterionLists l 66191 where
  n := 2
  a' := [45991, 20773, 52599, 49951, 54850, 17749, 64061, 4817]
  b' := [34841, 15676, 57594, 19565, 59717, 16115, 35755, 19006, 28883]
  k := [5387, 3641, 8345, 18421, 30348, 44906, 4597, 953, 1]
  f := [18166, 8491, 7448, 14978, 29036, 27055, 30868, 22185, 16543, 1]
  g := [36865, 17230, 15114, 30395, 58923, 54902, 62640, 45019, 33570, 1]
  h := [32617, 1]
  a := [832, 45980, 40625, 11345, 24966, 35658, 60112, 20350, 48022]
  b := [25833, 32268, 10752, 53715, 15541, 65411, 15296, 59012, 18169]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [23] where
  n := 4
  p := ![5, 23, 5471, 66191]
  exp := ![1, 2, 1, 1]
  pdgood := [5, 5471, 66191]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp23.out
    exact hp5471.out
    exact hp66191.out
  a := [8055169926835, -22880759374644, -67775824674024, 106350511432972, 77134718561152, -122597174176652, 8248570084500, 24846515708662, -6144616606520]
  b := [-1502167719780, -4241710031061, 10893130497058, 15908160443864, -23346106795574, -11574144298522, 17575227932130, -1207390499964, -2730436235127, 614461660652]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5471 T_ofList CD5471
    exact satisfiesDedekindCriterion_of_certificate_lists T l 66191 T_ofList CD66191

noncomputable def M23 : MaximalOrderCertificateOfUnramifiedLists 23 O Om hm where
  n := 10
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [14, 3, 4, 16, 4, 18, 16, 5, 9, 0], [16, 8, 9, 17, 8, 22, 18, 8, 13, 18]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [14, 3, 4, 16, 4, 18, 16, 5, 9, 0], [11, 18, 16, 10, 6, 5, 1, 15, 17, 0], [10, 15, 15, 17, 6, 17, 2, 20, 14, 2]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [14, 3, 4, 16, 4, 18, 16, 5, 9, 0], [11, 18, 16, 10, 6, 5, 1, 15, 17, 0], [8, 16, 17, 12, 9, 13, 1, 17, 7, 0], [21, 22, 20, 20, 20, 3, 1, 19, 11, 13]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [14, 3, 4, 16, 4, 18, 16, 5, 9, 0], [11, 18, 16, 10, 6, 5, 1, 15, 17, 0], [8, 16, 17, 12, 9, 13, 1, 17, 7, 0], [6, 6, 21, 14, 17, 20, 10, 13, 11, 0], [17, 20, 22, 3, 7, 21, 22, 22, 11, 4]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [14, 3, 4, 16, 4, 18, 16, 5, 9, 0], [11, 18, 16, 10, 6, 5, 1, 15, 17, 0], [8, 16, 17, 12, 9, 13, 1, 17, 7, 0], [6, 6, 21, 14, 17, 20, 10, 13, 11, 0], [16, 16, 4, 13, 12, 8, 12, 19, 20, 0], [11, 13, 8, 13, 10, 17, 16, 17, 12, 3]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [14, 3, 4, 16, 4, 18, 16, 5, 9, 0], [11, 18, 16, 10, 6, 5, 1, 15, 17, 0], [8, 16, 17, 12, 9, 13, 1, 17, 7, 0], [6, 6, 21, 14, 17, 20, 10, 13, 11, 0], [16, 16, 4, 13, 12, 8, 12, 19, 20, 0], [4, 7, 4, 2, 1, 4, 6, 20, 15, 0], [9, 2, 19, 21, 16, 16, 10, 8, 3, 8]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [14, 3, 4, 16, 4, 18, 16, 5, 9, 0], [11, 18, 16, 10, 6, 5, 1, 15, 17, 0], [8, 16, 17, 12, 9, 13, 1, 17, 7, 0], [6, 6, 21, 14, 17, 20, 10, 13, 11, 0], [16, 16, 4, 13, 12, 8, 12, 19, 20, 0], [4, 7, 4, 2, 1, 4, 6, 20, 15, 0], [3, 3, 21, 14, 16, 18, 14, 12, 17, 0], [9, 13, 17, 19, 5, 16, 1, 20, 1, 6]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [14, 3, 4, 16, 4, 18, 16, 5, 9, 0], [11, 18, 16, 10, 6, 5, 1, 15, 17, 0], [8, 16, 17, 12, 9, 13, 1, 17, 7, 0], [6, 6, 21, 14, 17, 20, 10, 13, 11, 0], [16, 16, 4, 13, 12, 8, 12, 19, 20, 0], [4, 7, 4, 2, 1, 4, 6, 20, 15, 0], [3, 3, 21, 14, 16, 18, 14, 12, 17, 0], [8, 8, 2, 17, 13, 0, 14, 7, 4, 0], [18, 14, 2, 20, 2, 17, 2, 8, 15, 16]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [16, 8, 9, 17, 8, 22, 18, 8, 13, 18], [10, 15, 15, 17, 6, 17, 2, 20, 14, 2], [21, 22, 20, 20, 20, 3, 1, 19, 11, 13], [17, 20, 22, 3, 7, 21, 22, 22, 11, 4], [11, 13, 8, 13, 10, 17, 16, 17, 12, 3], [9, 2, 19, 21, 16, 16, 10, 8, 3, 8], [9, 13, 17, 19, 5, 16, 1, 20, 1, 6], [18, 14, 2, 20, 2, 17, 2, 8, 15, 16], [6, 18, 18, 5, 6, 6, 9, 16, 15, 12]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 13, 10, 18, 3, 22, 10, 0, 1, 0], ![16, 18, 14, 2, 21, 1, 0, 8, 3, 0], ![2, 16, 10, 16, 20, 1, 21, 1, 7, 0], ![12, 13, 15, 13, 22, 18, 22, 11, 16, 0], ![4, 17, 1, 19, 5, 0, 20, 5, 1, 0], ![17, 8, 5, 22, 5, 16, 19, 9, 8, 0], ![4, 18, 4, 10, 17, 9, 8, 8, 0, 0], ![10, 2, 22, 10, 14, 16, 6, 2, 0, 0], ![0, 12, 13, 15, 20, 9, 2, 3, 2, 22]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
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

noncomputable def bOm : Basis (Fin 10) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 10 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 10
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 10 := T_degree

noncomputable def bQ : Basis (Fin 10) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 10) (Fin 10) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 10) :
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
          (∑ x : Fin 10,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 10,
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
        (List.ofFn fun i : Fin 10 =>
          (List.ofFn fun j : Fin 10 =>
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
      (voightPolynomialDiscriminantInput 10 row row_mem)
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

end VoightMaximalOrderD10R27

namespace VoightMaximalOrderD10R36

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1261262503125, [1, -9, -18, 56, 9, -64, 10, 25, -7, -3, 1], 9⟩
local notation "l" => [1, -9, -18, 56, 9, -64, 10, 25, -7, -3, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsTen := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsTen_irreducible row row_mem
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
def basisNumerator : Fin 10 → Fin 10 → ℤ := ![![3, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 3, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 3, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 3, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 3, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 3, 0, 0], ![1, 1, 0, 1, 1, 2, 2, 1, 1, 0], ![1, 2, 1, 1, 2, 0, 1, 0, 2, 1]]

noncomputable def BQ : SubalgebraBuilderLists 10 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![-1, -1, 0, -1, -1, -2, -2, -1, 3, 0], ![0, 0, 0, 0, 0, 1, 1, 1, -1, 1], ![-1, 1, 5, -19, -5, 24, -3, -7, -3, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![-1, -1, 0, -1, -1, -2, -2, -1, 3, 0], ![1, 0, -1, 1, 0, 4, 3, 2, -6, 3], ![-2, 0, 5, -20, -6, 21, -5, -8, 1, 4], ![2, 11, 26, -83, -37, 126, 20, -34, -33, 22]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![-1, -1, 0, -1, -1, -2, -2, -1, 3, 0], ![1, 0, -1, 1, 0, 4, 3, 2, -6, 3], ![-5, 2, 15, -60, -16, 62, -15, -26, 3, 9], ![4, 10, 20, -63, -32, 107, 26, -24, -37, 21], ![12, 58, 121, -358, -159, 526, 95, -133, -135, 77]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![-1, -1, 0, -1, -1, -2, -2, -1, 3, 0], ![1, 0, -1, 1, 0, 4, 3, 2, -6, 3], ![-5, 2, 15, -60, -16, 62, -15, -26, 3, 9], ![17, 30, 47, -130, -79, 255, 90, -49, -108, 48], ![3, 49, 115, -355, -144, 483, 55, -134, -98, 68], ![56, 222, 443, -1209, -610, 1820, 426, -446, -495, 250]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![-1, -1, 0, -1, -1, -2, -2, -1, 3, 0], ![1, 0, -1, 1, 0, 4, 3, 2, -6, 3], ![-5, 2, 15, -60, -16, 62, -15, -26, 3, 9], ![17, 30, 47, -130, -79, 255, 90, -49, -108, 48], ![1, 114, 270, -816, -321, 1063, 101, -305, -183, 132], ![66, 205, 389, -1043, -561, 1658, 449, -385, -508, 242], ![196, 752, 1472, -3861, -2013, 5787, 1467, -1373, -1593, 755]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![-1, -1, 0, -1, -1, -2, -2, -1, 3, 0], ![1, 0, -1, 1, 0, 4, 3, 2, -6, 3], ![-5, 2, 15, -60, -16, 62, -15, -26, 3, 9], ![17, 30, 47, -130, -79, 255, 90, -49, -108, 48], ![1, 114, 270, -816, -321, 1063, 101, -305, -183, 132], ![173, 438, 774, -1933, -1171, 3274, 1094, -701, -1128, 477], ![143, 693, 1415, -3824, -1868, 5509, 1194, -1368, -1373, 702], ![618, 2324, 4527, -11500, -6263, 17260, 4675, -4038, -4791, 2182]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![-1, -1, 0, -1, -1, -2, -2, -1, 3, 0], ![1, 0, -1, 1, 0, 4, 3, 2, -6, 3], ![-5, 2, 15, -60, -16, 62, -15, -26, 3, 9], ![17, 30, 47, -130, -79, 255, 90, -49, -108, 48], ![1, 114, 270, -816, -321, 1063, 101, -305, -183, 132], ![173, 438, 774, -1933, -1171, 3274, 1094, -701, -1128, 477], ![224, 1351, 2823, -7588, -3617, 10551, 2117, -2672, -2406, 1257], ![666, 2213, 4203, -10555, -5966, 16343, 4766, -3725, -4837, 2137], ![1856, 6838, 13234, -32893, -18372, 49390, 13999, -11352, -13869, 6119]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1, 1, 1, -1, 1], ![-2, 0, 5, -20, -6, 21, -5, -8, 1, 4], ![4, 10, 20, -63, -32, 107, 26, -24, -37, 21], ![3, 49, 115, -355, -144, 483, 55, -134, -98, 68], ![66, 205, 389, -1043, -561, 1658, 449, -385, -508, 242], ![143, 693, 1415, -3824, -1868, 5509, 1194, -1368, -1373, 702], ![666, 2213, 4203, -10555, -5966, 16343, 4766, -3725, -4837, 2137], ![893, 3532, 6948, -17794, -9505, 26401, 6893, -6231, -7161, 3321], ![2928, 10866, 21078, -52292, -29278, 78391, 22223, -18037, -21938, 9684]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 5, -19, -5, 24, -3, -7, -3, 5], ![2, 11, 26, -83, -37, 126, 20, -34, -33, 22], ![12, 58, 121, -358, -159, 526, 95, -133, -135, 77], ![56, 222, 443, -1209, -610, 1820, 426, -446, -495, 250], ![196, 752, 1472, -3861, -2013, 5787, 1467, -1373, -1593, 755], ![618, 2324, 4527, -11500, -6263, 17260, 4675, -4038, -4791, 2182], ![1856, 6838, 13234, -32893, -18372, 49390, 13999, -11352, -13869, 6119], ![2928, 10866, 21078, -52292, -29278, 78391, 22223, -18037, -21938, 9684], ![8611, 31601, 61131, -148919, -85305, 223228, 65557, -50740, -62910, 27110]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-3]], ![[], [], [], [], [], [], [], [], [-3], [-15, -3]], ![[], [], [], [], [], [], [], [-9], [-12, -3], [-66, -15, -3]], ![[], [], [], [], [], [], [-9], [-27, -9], [-63, -12, -3], [-231, -66, -15, -3]], ![[], [], [], [], [], [-9], [-27, -9], [-144, -27, -9], [-204, -63, -12, -3], [-750, -231, -66, -15, -3]], ![[], [], [], [], [-9], [-27, -9], [-144, -27, -9], [-396, -144, -27, -9], [-726, -204, -63, -12, -3], [-2265, -750, -231, -66, -15, -3]], ![[], [], [], [-9], [-27, -9], [-144, -27, -9], [-396, -144, -27, -9], [-1431, -396, -144, -27, -9], [-2106, -726, -204, -63, -12, -3], [-6546, -2265, -750, -231, -66, -15, -3]], ![[], [], [-3], [-12, -3], [-63, -12, -3], [-204, -63, -12, -3], [-726, -204, -63, -12, -3], [-2106, -726, -204, -63, -12, -3], [-3484, -1127, -361, -99, -27, -5, -1], [-10411, -3618, -1209, -382, -111, -29, -6, -1]], ![[], [-3], [-15, -3], [-66, -15, -3], [-231, -66, -15, -3], [-750, -231, -66, -15, -3], [-2265, -750, -231, -66, -15, -3], [-6546, -2265, -750, -231, -66, -15, -3], [-10411, -3618, -1209, -382, -111, -29, -6, -1], [-29902, -10783, -3780, -1279, -409, -122, -32, -7, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 10 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 10) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 10) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 10) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [-1, -1, 0, -1, -1, -2, -2, -1, 3, 0], [0, 0, 0, 0, 0, 1, 1, 1, -1, 1], [-1, 1, 5, -19, -5, 24, -3, -7, -3, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [-1, -1, 0, -1, -1, -2, -2, -1, 3, 0], [1, 0, -1, 1, 0, 4, 3, 2, -6, 3], [-2, 0, 5, -20, -6, 21, -5, -8, 1, 4], [2, 11, 26, -83, -37, 126, 20, -34, -33, 22]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [-1, -1, 0, -1, -1, -2, -2, -1, 3, 0], [1, 0, -1, 1, 0, 4, 3, 2, -6, 3], [-5, 2, 15, -60, -16, 62, -15, -26, 3, 9], [4, 10, 20, -63, -32, 107, 26, -24, -37, 21], [12, 58, 121, -358, -159, 526, 95, -133, -135, 77]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [-1, -1, 0, -1, -1, -2, -2, -1, 3, 0], [1, 0, -1, 1, 0, 4, 3, 2, -6, 3], [-5, 2, 15, -60, -16, 62, -15, -26, 3, 9], [17, 30, 47, -130, -79, 255, 90, -49, -108, 48], [3, 49, 115, -355, -144, 483, 55, -134, -98, 68], [56, 222, 443, -1209, -610, 1820, 426, -446, -495, 250]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [-1, -1, 0, -1, -1, -2, -2, -1, 3, 0], [1, 0, -1, 1, 0, 4, 3, 2, -6, 3], [-5, 2, 15, -60, -16, 62, -15, -26, 3, 9], [17, 30, 47, -130, -79, 255, 90, -49, -108, 48], [1, 114, 270, -816, -321, 1063, 101, -305, -183, 132], [66, 205, 389, -1043, -561, 1658, 449, -385, -508, 242], [196, 752, 1472, -3861, -2013, 5787, 1467, -1373, -1593, 755]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [-1, -1, 0, -1, -1, -2, -2, -1, 3, 0], [1, 0, -1, 1, 0, 4, 3, 2, -6, 3], [-5, 2, 15, -60, -16, 62, -15, -26, 3, 9], [17, 30, 47, -130, -79, 255, 90, -49, -108, 48], [1, 114, 270, -816, -321, 1063, 101, -305, -183, 132], [173, 438, 774, -1933, -1171, 3274, 1094, -701, -1128, 477], [143, 693, 1415, -3824, -1868, 5509, 1194, -1368, -1373, 702], [618, 2324, 4527, -11500, -6263, 17260, 4675, -4038, -4791, 2182]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [-1, -1, 0, -1, -1, -2, -2, -1, 3, 0], [1, 0, -1, 1, 0, 4, 3, 2, -6, 3], [-5, 2, 15, -60, -16, 62, -15, -26, 3, 9], [17, 30, 47, -130, -79, 255, 90, -49, -108, 48], [1, 114, 270, -816, -321, 1063, 101, -305, -183, 132], [173, 438, 774, -1933, -1171, 3274, 1094, -701, -1128, 477], [224, 1351, 2823, -7588, -3617, 10551, 2117, -2672, -2406, 1257], [666, 2213, 4203, -10555, -5966, 16343, 4766, -3725, -4837, 2137], [1856, 6838, 13234, -32893, -18372, 49390, 13999, -11352, -13869, 6119]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 1, 1, -1, 1], [-2, 0, 5, -20, -6, 21, -5, -8, 1, 4], [4, 10, 20, -63, -32, 107, 26, -24, -37, 21], [3, 49, 115, -355, -144, 483, 55, -134, -98, 68], [66, 205, 389, -1043, -561, 1658, 449, -385, -508, 242], [143, 693, 1415, -3824, -1868, 5509, 1194, -1368, -1373, 702], [666, 2213, 4203, -10555, -5966, 16343, 4766, -3725, -4837, 2137], [893, 3532, 6948, -17794, -9505, 26401, 6893, -6231, -7161, 3321], [2928, 10866, 21078, -52292, -29278, 78391, 22223, -18037, -21938, 9684]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 5, -19, -5, 24, -3, -7, -3, 5], [2, 11, 26, -83, -37, 126, 20, -34, -33, 22], [12, 58, 121, -358, -159, 526, 95, -133, -135, 77], [56, 222, 443, -1209, -610, 1820, 426, -446, -495, 250], [196, 752, 1472, -3861, -2013, 5787, 1467, -1373, -1593, 755], [618, 2324, 4527, -11500, -6263, 17260, 4675, -4038, -4791, 2182], [1856, 6838, 13234, -32893, -18372, 49390, 13999, -11352, -13869, 6119], [2928, 10866, 21078, -52292, -29278, 78391, 22223, -18037, -21938, 9684], [8611, 31601, 61131, -148919, -85305, 223228, 65557, -50740, -62910, 27110]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp109 : Fact (Nat.Prime 109) := fact_iff.2 (by norm_num)
instance hp411421 : Fact (Nat.Prime 411421) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 0, 2]
  b' := [1, 1, 0, 3, 2]
  k := [1]
  f := [0, 3, 7, -6, 3, 16, 1, -3, 2, 1]
  g := [1, 3, 4, 1, 1, 1]
  h := [1, 3, 4, 1, 1, 1]
  a := [0, 1, 4]
  b := [1, 2, 2, 1, 4, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD109 : CertificateDedekindCriterionLists l 109 where
  n := 2
  a' := [84, 80, 4, 104, 40, 58, 106, 3]
  b' := [48, 20, 2, 26, 39, 102, 95, 55, 36]
  k := [61, 60, 6, 75, 83, 94, 36, 103, 1]
  f := [19, 22, 36, 33, 19, 4, 20, 14, 26, 1]
  g := [37, 42, 69, 64, 36, 6, 39, 27, 50, 1]
  h := [56, 1]
  a := [80, 72, 28, 32, 2, 29, 25, 50, 50]
  b := [65, 42, 82, 69, 40, 107, 31, 60, 59]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD411421 : CertificateDedekindCriterionLists l 411421 where
  n := 2
  a' := [38926, 246269, 106045, 173969, 393454, 281020, 138366, 342579]
  b' := [37732, 407920, 267631, 165075, 158933, 204335, 265967, 371591, 99076]
  k := [140968, 95512, 201046, 357229, 182633, 132174, 390069, 30329, 1]
  f := [225614, 211233, 70220, 55631, 222796, 72102, 162076, 374789, 14605, 1]
  g := [234249, 219317, 72907, 57760, 231323, 74861, 168279, 389133, 15163, 1]
  h := [396255, 1]
  a := [25607, 100748, 112852, 129582, 284734, 255842, 175330, 279299, 259466]
  b := [206099, 240043, 349180, 170090, 334134, 237704, 33697, 93958, 151955]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
  n := 4
  p := ![3, 5, 109, 411421]
  exp := ![2, 1, 1, 1]
  pdgood := [5, 109, 411421]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp5.out
    exact hp109.out
    exact hp411421.out
  a := [-6754254642, -38060666622, 114100947477, 109430289870, -197239515021, -76946741528, 98164500249, 14677204204, -13507949820]
  b := [-974697183, 6424080416, 20356389879, -33255346947, -29764313083, 34566943071, 13684704427, -12361390809, -1872958915, 1350794982]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 109 T_ofList CD109
    exact satisfiesDedekindCriterion_of_certificate_lists T l 411421 T_ofList CD411421

noncomputable def M3 : MaximalOrderCertificateLists 3 O Om hm where
  m := 2
  n := 8
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [2, 2, 0, 2, 2, 1, 1, 2, 0, 0], [0, 0, 0, 0, 0, 1, 1, 1, 2, 1], [2, 1, 2, 2, 1, 0, 0, 2, 0, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [2, 2, 0, 2, 2, 1, 1, 2, 0, 0], [1, 0, 2, 1, 0, 1, 0, 2, 0, 0], [1, 0, 2, 1, 0, 0, 1, 1, 1, 1], [2, 2, 2, 1, 2, 0, 2, 2, 0, 1]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [2, 2, 0, 2, 2, 1, 1, 2, 0, 0], [1, 0, 2, 1, 0, 1, 0, 2, 0, 0], [1, 2, 0, 0, 2, 2, 0, 1, 0, 0], [1, 1, 2, 0, 1, 2, 2, 0, 2, 0], [0, 1, 1, 2, 0, 1, 2, 2, 0, 2]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [2, 2, 0, 2, 2, 1, 1, 2, 0, 0], [1, 0, 2, 1, 0, 1, 0, 2, 0, 0], [1, 2, 0, 0, 2, 2, 0, 1, 0, 0], [2, 0, 2, 2, 2, 0, 0, 2, 0, 0], [0, 1, 1, 2, 0, 0, 1, 1, 1, 2], [2, 0, 2, 0, 2, 2, 0, 1, 0, 1]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [2, 2, 0, 2, 2, 1, 1, 2, 0, 0], [1, 0, 2, 1, 0, 1, 0, 2, 0, 0], [1, 2, 0, 0, 2, 2, 0, 1, 0, 0], [2, 0, 2, 2, 2, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 1, 2, 1, 0, 0], [0, 1, 2, 1, 0, 2, 2, 2, 2, 2], [1, 2, 2, 0, 0, 0, 0, 1, 0, 2]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [2, 2, 0, 2, 2, 1, 1, 2, 0, 0], [1, 0, 2, 1, 0, 1, 0, 2, 0, 0], [1, 2, 0, 0, 2, 2, 0, 1, 0, 0], [2, 0, 2, 2, 2, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 1, 2, 1, 0, 0], [2, 0, 0, 2, 2, 1, 2, 1, 0, 0], [2, 0, 2, 1, 1, 1, 0, 0, 1, 0], [0, 2, 0, 2, 1, 1, 1, 0, 0, 1]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [2, 2, 0, 2, 2, 1, 1, 2, 0, 0], [1, 0, 2, 1, 0, 1, 0, 2, 0, 0], [1, 2, 0, 0, 2, 2, 0, 1, 0, 0], [2, 0, 2, 2, 2, 0, 0, 2, 0, 0], [1, 0, 0, 0, 0, 1, 2, 1, 0, 0], [2, 0, 0, 2, 2, 1, 2, 1, 0, 0], [2, 1, 0, 2, 1, 0, 2, 1, 0, 0], [0, 2, 0, 2, 1, 2, 2, 1, 2, 1], [2, 1, 1, 2, 0, 1, 1, 0, 0, 2]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, 1, 1, 2, 1], [1, 0, 2, 1, 0, 0, 1, 1, 1, 1], [1, 1, 2, 0, 1, 2, 2, 0, 2, 0], [0, 1, 1, 2, 0, 0, 1, 1, 1, 2], [0, 1, 2, 1, 0, 2, 2, 2, 2, 2], [2, 0, 2, 1, 1, 1, 0, 0, 1, 0], [0, 2, 0, 2, 1, 2, 2, 1, 2, 1], [2, 1, 0, 2, 2, 1, 2, 0, 0, 0], [0, 0, 0, 1, 2, 1, 2, 2, 1, 0]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 1, 2, 2, 1, 0, 0, 2, 0, 2], [2, 2, 2, 1, 2, 0, 2, 2, 0, 1], [0, 1, 1, 2, 0, 1, 2, 2, 0, 2], [2, 0, 2, 0, 2, 2, 0, 1, 0, 1], [1, 2, 2, 0, 0, 0, 0, 1, 0, 2], [0, 2, 0, 2, 1, 1, 1, 0, 0, 1], [2, 1, 1, 2, 0, 1, 1, 0, 0, 2], [0, 0, 0, 1, 2, 1, 2, 2, 1, 0], [1, 2, 0, 1, 0, 1, 1, 2, 0, 2]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![1, 0, 0, 1, 0, 2, 0, 1, 0, 0], ![1, 1, 0, 1, 1, 2, 1, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 2, 0, 0, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 1, 2, 0, 0, 0], ![1, 0, 0, 0, 2, 1, 0, 0, 0, 0], ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0], ![2, 2, 1, 2, 2, 1, 1, 0, 0, 0], ![0, 1, 2, 1, 2, 2, 1, 0, 0, 0], ![2, 0, 1, 0, 2, 1, 1, 0, 2, 0]]
  v := ![![1, 0, 0, 1, 0, 2, 0, 1, 0, 0], ![1, 1, 0, 1, 1, 2, 1, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 2, 0, 0, 0, 0, 0, 0, 0], ![2, 1, 0, 0, 0, 1, 2, 0, 0, 0], ![1, 0, 0, 0, 2, 1, 0, 0, 0, 0], ![0, 2, 1, 1, 2, 1, 1, 0, 0, 0], ![2, 2, 1, 2, 2, 1, 1, 0, 0, 0], ![0, 1, 2, 1, 2, 2, 1, 0, 0, 0], ![2, 0, 1, 0, 2, 1, 1, 0, 2, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 2, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 2, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 2]]
  v_ind := ![7, 9]
  w_ind := ![0, 1, 2, 3, 4, 5, 6, 8]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![8, 8, 8, 0, 8, 4, 4, 8, 0, 8], ![0, 8, 0, 0, 4, 4, 8, 8, 8, 4], ![0, 8, 0, 0, 8, 0, 8, 4, 0, 8], ![8, 0, 0, 8, 0, 4, 0, 8, 0, 0], ![8, 4, 4, 0, 4, 8, 8, 4, 0, 4], ![0, 8, 4, 8, 0, 0, 0, 0, 0, 0], ![4, 4, 4, 0, 8, 0, 4, 0, 0, 8], ![0, 4, 4, 0, 4, 4, 8, 8, 0, 0], ![0, 4, 4, 4, 8, 0, 4, 8, 0, 0], ![0, 4, 4, 4, 4, 4, 0, 8, 0, 0]]
  a := ![![![-145244, 77256], ![-594588, 319744]], ![![-127524, 69628], ![-540524, 291328]], ![![-133812, 72816], ![-555336, 298284]], ![![-28104, 12912], ![-108852, 59280]], ![![-79548, 42984], ![-332916, 179352]], ![![-216, 84], ![-1236, 768]], ![![-117372, 64404], ![-486636, 261000]], ![![-34428, 17676], ![-145536, 79176]], ![![-30096, 15024], ![-124188, 67572]], ![![-28164, 13104], ![-110352, 60120]]]
  c := ![![![-3215346, 560637, 465160, 852582, -1468814, 758812, -164666, -27792], ![-13171578, 2299985, 1923496, 3490678, -6025018, 3100326, -660334, -121286]], ![![-2801532, 488382, 405848, 743360, -1280636, 661036, -142660, -24996], ![-11955522, 2086901, 1743004, 3169106, -5467914, 2815542, -601374, -109310]], ![![-2949470, 514551, 428644, 782478, -1348610, 695202, -149286, -26722], ![-12306264, 2148944, 1797296, 3261172, -5629160, 2896570, -616892, -113266]], ![![-635628, 110378, 89048, 168100, -288644, 151324, -35096, -3796], ![-2398934, 418571, 349164, 636262, -1097134, 565240, -120986, -21932]], ![![-1753788, 305778, 253880, 465240, -801448, 413840, -89560, -15420], ![-7367358, 1286191, 1074740, 1952738, -3369710, 1734690, -370130, -67534]], ![![-4698, 803, 592, 1218, -2106, 1148, -310, 12], ![-26664, 4644, 3752, 7112, -12168, 6320, -1432, -204]], ![![-2584860, 451130, 376756, 685808, -1182472, 608758, -129912, -23982], ![-10792086, 1884799, 1577088, 2859602, -4936758, 2539692, -540382, -99512]], ![![-763830, 132859, 108568, 202546, -348010, 181134, -40686, -5690], ![-3205062, 559051, 465792, 850082, -1465554, 755548, -162154, -29032]], ![![-672042, 116873, 95192, 178102, -305918, 159492, -36134, -4748], ![-2735898, 477275, 397848, 725610, -1251110, 644826, -138242, -24862]], ![![-636108, 110494, 89228, 168296, -288944, 151368, -35020, -3884], ![-2431374, 424209, 353792, 644870, -1111950, 572930, -122682, -22198]]]
  d := ![![![24, 24], ![-1896, 1440], ![-278448, 154596], ![-65460, 36660], ![-189000, 105768], ![-192732, 107916], ![-230688, 128292], ![-1278228, 697044]], ![![24, 12], ![-1248, 1032], ![-247128, 136104], ![-55188, 31416], ![-164952, 92052], ![-167652, 93792], ![-199956, 111732], ![-1150884, 625776]], ![![12, 24], ![-1944, 1368], ![-264360, 144048], ![-61608, 34536], ![-179424, 98820], ![-182832, 100896], ![-217824, 120192], ![-1202880, 649728]], ![![24, 0], ![72, 144], ![-42360, 27468], ![-9888, 5652], ![-27900, 18036], ![-28488, 18252], ![-35472, 21384], ![-216360, 127212]], ![![12, 12], ![-912, 720], ![-153300, 84804], ![-34944, 19788], ![-103032, 57636], ![-104880, 58764], ![-125244, 69924], ![-710808, 387204]], ![![0, 0], ![0, 0], ![108, 144], ![36, 0], ![96, 72], ![96, 72], ![84, 72], ![-1200, 1224]], ![![0, 24], ![-1968, 1296], ![-236028, 127272], ![-55560, 31008], ![-161040, 87804], ![-164184, 89736], ![-195192, 106980], ![-1062792, 570792]], ![![24, 0], ![72, 144], ![-58812, 35064], ![-12324, 7272], ![-37932, 22932], ![-38460, 23220], ![-46668, 27468], ![-294396, 166476]], ![![24, 0], ![48, 144], ![-49992, 30384], ![-10836, 6336], ![-32508, 19944], ![-33036, 20196], ![-40320, 23832], ![-250668, 143004]], ![![24, 0], ![72, 144], ![-42984, 27648], ![-9888, 5688], ![-28224, 18144], ![-28800, 18360], ![-35748, 21528], ![-219504, 128568]]]
  e := ![![![492, -70, -60, -116, 216, -132, 32, 0], ![-38964, 6802, 5408, 10420, -17852, 9244, -2092, -300], ![-6086436, 1060908, 883436, 1615464, -2783836, 1435666, -308004, -55806], ![-1423260, 247700, 204100, 378188, -650144, 336766, -73868, -12150], ![-4119462, 717695, 595688, 1093842, -1883626, 972636, -210010, -37068], ![-4200942, 731865, 607024, 1115530, -1920718, 992030, -214514, -37602], ![-5034664, 876990, 726680, 1336836, -2301304, 1189264, -257868, -44556], ![-28152346, 4912123, 4101024, 7465726, -12877290, 6632350, -1416638, -259034]], ![![264, -40, -32, -68, 128, -76, 12, 4], ![-26412, 4634, 3592, 7052, -12076, 6248, -1484, -144], ![-5403996, 941234, 779664, 1434616, -2469556, 1276734, -277268, -47434], ![-1193436, 207582, 170380, 317288, -545076, 282720, -62424, -10000], ![-3593718, 625705, 516628, 954486, -1642022, 849762, -185594, -31026], ![-3651720, 635806, 524724, 969964, -1668468, 863526, -188768, -31442], ![-4353368, 757888, 625436, 1156376, -1989024, 1029574, -225100, -37490], ![-25333800, 4417986, 3677292, 6719620, -11582516, 5974258, -1285064, -227750]], ![![396, -60, -48, -96, 180, -108, 24, 0], ![-40368, 7020, 5568, 10752, -18456, 9612, -2208, -276], ![-5802408, 1011138, 839832, 1539360, -2652132, 1369680, -295944, -51480], ![-1338330, 232923, 192156, 355566, -611466, 316602, -69258, -11538], ![-3924246, 683535, 566232, 1041546, -1793406, 927096, -201270, -34380], ![-3997980, 696384, 576600, 1061232, -1827024, 944574, -205260, -34938], ![-4762212, 829488, 686892, 1264200, -2176296, 1125120, -244440, -41700], ![-26550264, 4632126, 3862464, 7039308, -12140436, 6257034, -1341168, -240438]], ![![192, -30, -24, -48, 84, -48, 12, 0], ![1848, -276, -216, -432, 792, -504, 144, -24], ![-888606, 155055, 131244, 237054, -408594, 208674, -42510, -10206], ![-214578, 37293, 30168, 57138, -97818, 50994, -11598, -1602], ![-586098, 102219, 85740, 156414, -269142, 137916, -28710, -6336], ![-599796, 104562, 87480, 159984, -275292, 141270, -29604, -6318], ![-757452, 131874, 109152, 201708, -346716, 178986, -38628, -7086], ![-4669692, 814734, 684312, 1241184, -2140644, 1098690, -230052, -47394]], ![![220, -32, -24, -52, 96, -60, 16, 0], ![-19176, 3360, 2656, 5120, -8776, 4532, -1040, -132], ![-3350814, 583821, 484676, 889446, -1531886, 791120, -170910, -29964], ![-757560, 131824, 108404, 201356, -346048, 179336, -39460, -6408], ![-2245092, 391024, 323608, 596196, -1026172, 530496, -115268, -19740], ![-2285280, 398022, 329216, 606908, -1044488, 540044, -117472, -20016], ![-2729888, 475410, 393028, 724992, -1247540, 645230, -140540, -23790], ![-15647828, 2729456, 2274576, 4150112, -7155612, 3688616, -791164, -141996]], ![![-48, 8, 4, 8, -20, 16, -4, 0], ![4, -6, -8, -4, -4, 8, 12, 0], ![2400, -366, -288, -580, 1036, -640, 180, -24], ![120, -18, -20, -44, 68, -40, 0, 12], ![1656, -260, -200, -404, 728, -450, 128, -6], ![1644, -260, -200, -408, 728, -442, 128, -6], ![1234, -197, -156, -314, 550, -342, 90, 6], ![-24612, 4356, 3584, 6680, -11384, 5706, -1184, -306]], ![![288, -42, -36, -68, 124, -76, 20, 0], ![-41040, 7120, 5656, 10920, -18736, 9796, -2256, -276], ![-5195810, 905531, 751972, 1377946, -2374390, 1226460, -265322, -45648], ![-1208718, 210415, 173920, 321054, -552338, 285784, -62286, -10536], ![-3532038, 615275, 509796, 937126, -1613902, 834358, -181206, -30750], ![-3599730, 627077, 519380, 955210, -1644810, 850386, -184806, -31302], ![-4276660, 745040, 617460, 1135004, -1954356, 1010120, -219200, -37476], ![-23500190, 4100491, 3419380, 6229350, -10744846, 5537706, -1187322, -211950]], ![![318, -49, -36, -78, 146, -88, 22, 0], ![1740, -266, -224, -436, 748, -472, 124, 0], ![-1256352, 218714, 181824, 334348, -575296, 296686, -63480, -12054], ![-263930, 45857, 37100, 70310, -120410, 62734, -14218, -2022], ![-808020, 140628, 116196, 215148, -369824, 191056, -41368, -7464], ![-820212, 142744, 117772, 218376, -375312, 193990, -42144, -7470], ![-1000366, 174001, 142924, 266222, -457254, 236926, -52074, -8658], ![-6402420, 1115860, 929316, 1700368, -2929432, 1510234, -323400, -59586]], ![![360, -56, -44, -88, 164, -96, 24, 0], ![1428, -222, -176, -348, 604, -388, 116, -12], ![-1063590, 185265, 154776, 283134, -487542, 250802, -52982, -10698], ![-233028, 40500, 32820, 62064, -106304, 55354, -12520, -1794], ![-690458, 120223, 99792, 183890, -316294, 163044, -34910, -6660], ![-702798, 122359, 101380, 187150, -321838, 166024, -35702, -6660], ![-864252, 150372, 123856, 229996, -395196, 204520, -44684, -7656], ![-5442962, 948929, 792148, 1445674, -2491634, 1283000, -273106, -51804]], ![![222, -33, -28, -54, 102, -60, 14, 0], ![1968, -308, -232, -472, 840, -528, 160, -24], ![-902928, 157506, 133048, 240780, -415004, 212180, -43456, -10176], ![-214260, 37244, 30136, 57056, -97684, 50904, -11568, -1608], ![-593436, 103466, 86664, 158308, -272440, 139718, -29188, -6318], ![-607004, 105796, 88388, 161856, -278520, 143024, -30076, -6300], ![-763594, 132931, 109944, 203322, -349482, 180470, -39022, -7086], ![-4740468, 826964, 693852, 1259848, -2172624, 1115704, -234252, -47628]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 1, Sum.inr 0), (Sum.inr 0, Sum.inr 0), (Sum.inr 1, Sum.inr 0), (Sum.inr 2, Sum.inr 0), (Sum.inr 3, Sum.inr 0), (Sum.inr 4, Sum.inr 0), (Sum.inr 5, Sum.inr 0)]
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

noncomputable def bOm : Basis (Fin 10) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 10 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 10
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 10 := T_degree

noncomputable def bQ : Basis (Fin 10) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 10) (Fin 10) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 10) :
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
          (∑ x : Fin 10,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 10,
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
        (List.ofFn fun i : Fin 10 =>
          (List.ofFn fun j : Fin 10 =>
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
      (voightPolynomialDiscriminantInput 10 row row_mem)
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

end VoightMaximalOrderD10R36

end TraceEuclidean
