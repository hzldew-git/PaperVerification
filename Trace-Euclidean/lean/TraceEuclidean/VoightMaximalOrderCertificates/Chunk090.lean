import TraceEuclidean.VoightMaximalOrderCertificates.Chunk086
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

namespace VoightMaximalOrderD8R16

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨803680625, [-1, 14, -14, -24, 22, 12, -9, -2, 1], 16⟩
local notation "l" => [-1, 14, -14, -24, 22, 12, -9, -2, 1]
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
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![2, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, 0, 0], ![0, 0, 0, 2, 0, 0, 0, 0], ![1, 0, 0, 1, 1, 0, 0, 0], ![1, 1, 0, 1, 0, 1, 0, 0], ![1, 1, 1, 1, 0, 0, 1, 0], ![1, 1, 1, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![-1, 0, 0, -1, 2, 0, 0, 0], ![-1, 0, 0, -1, 1, 1, 0, 0], ![-1, 0, 0, -1, 1, 0, 1, 0], ![-1, 0, 0, 0, 1, 0, 0, 1], ![12, -6, 2, 25, -22, -12, 9, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![-1, 0, 0, -1, 2, 0, 0, 0], ![-1, -1, 0, -1, 0, 2, 0, 0], ![-1, -1, 0, -1, 0, 1, 1, 0], ![-1, -1, 0, 0, 0, 1, 0, 1], ![11, -7, 2, 24, -21, -11, 9, 2], ![24, 0, -2, 61, -19, -46, 6, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![-1, 0, 0, -1, 2, 0, 0, 0], ![-1, -1, 0, -1, 0, 2, 0, 0], ![-1, -1, -1, -1, 0, 0, 2, 0], ![-1, -1, -1, 0, 0, 0, 1, 1], ![11, -7, 1, 24, -21, -12, 10, 2], ![23, -1, -3, 60, -19, -45, 7, 13], ![154, -54, 26, 327, -223, -175, 71, 32]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![-1, 0, 0, -1, 1, 1, 0, 0], ![-1, -1, 0, -1, 0, 1, 1, 0], ![-1, -1, -1, 0, 0, 0, 1, 1], ![5, -4, 0, 12, -10, -6, 5, 2], ![17, -4, -1, 42, -20, -28, 8, 8], ![88, -28, 11, 193, -121, -110, 40, 23], ![269, -46, 18, 612, -300, -391, 92, 84]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![-1, 0, 0, -1, 1, 0, 1, 0], ![-1, -1, 0, 0, 0, 1, 0, 1], ![11, -7, 1, 24, -21, -12, 10, 2], ![17, -4, -1, 42, -20, -28, 8, 8], ![88, -34, 14, 187, -133, -99, 46, 18], ![209, -23, 4, 491, -209, -332, 65, 76], ![880, -243, 130, 1912, -1146, -1092, 344, 209]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-1, 0, 0, 0, 1, 0, 0, 1], ![11, -7, 2, 24, -21, -11, 9, 2], ![23, -1, -3, 60, -19, -45, 7, 13], ![88, -28, 11, 193, -121, -110, 40, 23], ![209, -23, 4, 491, -209, -332, 65, 76], ![832, -220, 115, 1821, -1064, -1056, 320, 207], ![2375, -382, 183, 5396, -2591, -3438, 768, 711]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![12, -6, 2, 25, -22, -12, 9, 2], ![24, 0, -2, 61, -19, -46, 6, 13], ![154, -54, 26, 327, -223, -175, 71, 32], ![269, -46, 18, 612, -300, -391, 92, 84], ![880, -243, 130, 1912, -1146, -1092, 344, 209], ![2375, -382, 183, 5396, -2591, -3438, 768, 711], ![8128, -1845, 1022, 17979, -9811, -10732, 2869, 2107]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-2]], ![[], [], [], [], [], [], [-2], [-4, -2]], ![[], [], [], [], [], [-2], [-4, -2], [-26, -4, -2]], ![[], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-45, -15, -3, -1]], ![[], [], [], [-2], [-3, -1], [-15, -2, -1], [-35, -14, -2, -1], [-149, -34, -14, -2, -1]], ![[], [], [-2], [-4, -2], [-15, -3, -1], [-35, -14, -2, -1], [-141, -34, -13, -2, -1], [-399, -138, -33, -13, -2, -1]], ![[], [-2], [-4, -2], [-26, -4, -2], [-45, -15, -3, -1], [-149, -34, -14, -2, -1], [-399, -138, -33, -13, -2, -1], [-1377, -384, -135, -32, -13, -2, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [-1, 0, 0, -1, 2, 0, 0, 0], [-1, 0, 0, -1, 1, 1, 0, 0], [-1, 0, 0, -1, 1, 0, 1, 0], [-1, 0, 0, 0, 1, 0, 0, 1], [12, -6, 2, 25, -22, -12, 9, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [-1, 0, 0, -1, 2, 0, 0, 0], [-1, -1, 0, -1, 0, 2, 0, 0], [-1, -1, 0, -1, 0, 1, 1, 0], [-1, -1, 0, 0, 0, 1, 0, 1], [11, -7, 2, 24, -21, -11, 9, 2], [24, 0, -2, 61, -19, -46, 6, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0], [-1, 0, 0, -1, 2, 0, 0, 0], [-1, -1, 0, -1, 0, 2, 0, 0], [-1, -1, -1, -1, 0, 0, 2, 0], [-1, -1, -1, 0, 0, 0, 1, 1], [11, -7, 1, 24, -21, -12, 10, 2], [23, -1, -3, 60, -19, -45, 7, 13], [154, -54, 26, 327, -223, -175, 71, 32]], ![[0, 0, 0, 0, 1, 0, 0, 0], [-1, 0, 0, -1, 1, 1, 0, 0], [-1, -1, 0, -1, 0, 1, 1, 0], [-1, -1, -1, 0, 0, 0, 1, 1], [5, -4, 0, 12, -10, -6, 5, 2], [17, -4, -1, 42, -20, -28, 8, 8], [88, -28, 11, 193, -121, -110, 40, 23], [269, -46, 18, 612, -300, -391, 92, 84]], ![[0, 0, 0, 0, 0, 1, 0, 0], [-1, 0, 0, -1, 1, 0, 1, 0], [-1, -1, 0, 0, 0, 1, 0, 1], [11, -7, 1, 24, -21, -12, 10, 2], [17, -4, -1, 42, -20, -28, 8, 8], [88, -34, 14, 187, -133, -99, 46, 18], [209, -23, 4, 491, -209, -332, 65, 76], [880, -243, 130, 1912, -1146, -1092, 344, 209]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-1, 0, 0, 0, 1, 0, 0, 1], [11, -7, 2, 24, -21, -11, 9, 2], [23, -1, -3, 60, -19, -45, 7, 13], [88, -28, 11, 193, -121, -110, 40, 23], [209, -23, 4, 491, -209, -332, 65, 76], [832, -220, 115, 1821, -1064, -1056, 320, 207], [2375, -382, 183, 5396, -2591, -3438, 768, 711]], ![[0, 0, 0, 0, 0, 0, 0, 1], [12, -6, 2, 25, -22, -12, 9, 2], [24, 0, -2, 61, -19, -46, 6, 13], [154, -54, 26, 327, -223, -175, 71, 32], [269, -46, 18, 612, -300, -391, 92, 84], [880, -243, 130, 1912, -1146, -1092, 344, 209], [2375, -382, 183, 5396, -2591, -3438, 768, 711], [8128, -1845, 1022, 17979, -9811, -10732, 2869, 2107]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp139 : Fact (Nat.Prime 139) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 3, 2]
  b' := [4, 3, 0, 2]
  k := [1]
  f := [1, -2, 3, 8, -2, -2, 5, 2]
  g := [2, 1, 0, 4, 1]
  h := [2, 1, 0, 4, 1]
  a := [2, 3, 2, 2]
  b := [2, 2, 3, 3, 0, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [6, 2, 8, 0, 4, 2]
  b' := [7, 1, 3, 3, 1, 7, 6]
  k := [8, 1, 10, 3, 0, 5, 1]
  f := [1, 1, 4, 4, -1, 1, 3, 1]
  g := [5, 10, 10, 5, 3, 10, 7, 1]
  h := [2, 1]
  a := [3, 4, 3, 3, 3, 3, 1]
  b := [4, 6, 7, 5, 1, 1, 10]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [20, 15, 9, 23, 18]
  b' := [14, 23, 19, 28, 9, 26]
  k := [20, 12, 6, 28, 1]
  f := [9, 20, 18, 19, 14, 6, 7, 1]
  g := [26, 23, 16, 28, 2, 13, 1]
  h := [10, 14, 1]
  a := [4, 21, 3, 11, 6, 10]
  b := [2, 18, 22, 14, 17, 25, 19]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD139 : CertificateDedekindCriterionLists l 139 where
  n := 2
  a' := [12, 19, 86, 132, 53, 23]
  b' := [126, 14, 39, 80, 138, 7, 96]
  k := [103, 72, 127, 14, 2, 91, 1]
  f := [1, 15, 13, 6, 10, 2, 19, 1]
  g := [6, 91, 74, 32, 60, 10, 114, 1]
  h := [23, 1]
  a := [28, 116, 35, 122, 10, 31, 50]
  b := [65, 60, 40, 74, 43, 132, 89]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 5
  p := ![2, 5, 11, 29, 139]
  exp := ![1, 1, 1, 1, 1]
  pdgood := [5, 11, 29, 139]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp5.out
    exact hp11.out
    exact hp29.out
    exact hp139.out
  a := [565374, 45836, -2603114, -293630, 1933300, 268106, -278072]
  b := [72056, -417988, -131801, 731011, 121470, -326699, -42203, 34759]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
    exact satisfiesDedekindCriterion_of_certificate_lists T l 139 T_ofList CD139

noncomputable def M2 : MaximalOrderCertificateOfUnramifiedLists 2 O Om hm where
  n := 8
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 1, 1, 1, 0, 0], [1, 0, 0, 1, 1, 0, 1, 0], [1, 0, 0, 0, 1, 0, 0, 1], [0, 0, 0, 1, 0, 0, 1, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0, 0], [1, 1, 0, 1, 0, 0, 0, 0], [1, 1, 0, 1, 0, 1, 1, 0], [1, 1, 0, 0, 0, 1, 0, 1], [1, 1, 0, 0, 1, 1, 1, 0], [0, 0, 0, 1, 1, 0, 0, 1]], ![[0, 0, 0, 1, 0, 0, 0, 0], [1, 0, 0, 1, 0, 0, 0, 0], [1, 1, 0, 1, 0, 0, 0, 0], [1, 1, 1, 1, 0, 0, 0, 0], [1, 1, 1, 0, 0, 0, 1, 1], [1, 1, 1, 0, 1, 0, 0, 0], [1, 1, 1, 0, 1, 1, 1, 1], [0, 0, 0, 1, 1, 1, 1, 0]], ![[0, 0, 0, 0, 1, 0, 0, 0], [1, 0, 0, 1, 1, 1, 0, 0], [1, 1, 0, 1, 0, 1, 1, 0], [1, 1, 1, 0, 0, 0, 1, 1], [1, 0, 0, 0, 0, 0, 1, 0], [1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0, 1], [1, 0, 0, 0, 0, 1, 0, 0]], ![[0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 1, 0, 1, 0], [1, 1, 0, 0, 0, 1, 0, 1], [1, 1, 1, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 1, 1, 0, 0], [1, 1, 0, 1, 1, 0, 1, 0], [0, 1, 0, 0, 0, 0, 0, 1]], ![[0, 0, 0, 0, 0, 0, 1, 0], [1, 0, 0, 0, 1, 0, 0, 1], [1, 1, 0, 0, 1, 1, 1, 0], [1, 1, 1, 0, 1, 1, 1, 1], [0, 0, 1, 1, 1, 0, 0, 1], [1, 1, 0, 1, 1, 0, 1, 0], [0, 0, 1, 1, 0, 0, 0, 1], [1, 0, 1, 0, 1, 0, 0, 1]], ![[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 1, 0, 0, 1, 0], [0, 0, 0, 1, 1, 0, 0, 1], [0, 0, 0, 1, 1, 1, 1, 0], [1, 0, 0, 0, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0, 1], [1, 0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 1, 1, 0, 1, 1]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![1, 0, 0, 1, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 1, 1, 1, 0, 0], ![0, 0, 1, 1, 0, 0, 0, 1], ![0, 1, 0, 1, 1, 0, 1, 1]]
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

end VoightMaximalOrderD8R16

namespace VoightMaximalOrderD8R23

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1064390625, [1, 0, -17, 0, 44, 0, -13, 0, 1], 256⟩
local notation "l" => [1, 0, -17, 0, 44, 0, -13, 0, 1]
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
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![8, 0, 0, 0, 0, 0, 0, 0], ![0, 8, 0, 0, 0, 0, 0, 0], ![0, 0, 8, 0, 0, 0, 0, 0], ![4, 0, 0, 4, 0, 0, 0, 0], ![4, 4, 0, 4, 4, 0, 0, 0], ![4, 0, 4, 4, 0, 4, 0, 0], ![2, 4, 0, 4, 4, 0, 2, 0], ![3, 7, 4, 4, 4, 0, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![-1, 0, 0, 2, 0, 0, 0, 0], ![0, 0, 0, -1, 1, 0, 0, 0], ![0, 0, 0, -2, 1, 1, 0, 0], ![0, 0, 0, 0, -1, 0, 2, 0], ![0, -1, -1, -2, 0, 1, -1, 2], ![1, 5, 2, 10, -17, 1, 6, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![-1, 0, 0, 2, 0, 0, 0, 0], ![0, -1, 0, -2, 2, 0, 0, 0], ![0, 0, 0, -1, 0, 1, 0, 0], ![0, 0, 0, 0, -2, 1, 2, 0], ![0, -2, -2, -2, -1, 1, -2, 4], ![3, 11, 4, 22, -37, 1, 15, 0], ![-1, 0, 1, 26, -25, -10, 2, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, -1, 1, 0, 0, 0], ![0, 0, 0, -1, 0, 1, 0, 0], ![0, 0, 0, 1, -1, 0, 1, 0], ![0, -1, -1, 0, -1, 0, 0, 2], ![3, 11, 4, 22, -36, 1, 14, 0], ![-2, -6, -2, 15, -8, -11, -6, 15], ![6, 31, 12, 76, -105, -5, 28, 9]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, -2, 1, 1, 0, 0], ![0, 0, 0, 0, -2, 1, 2, 0], ![0, -1, -1, 0, -1, 0, 0, 2], ![3, 9, 2, 20, -36, 1, 12, 4], ![-1, 0, 1, 52, -51, -21, 2, 28], ![15, 73, 28, 174, -245, -10, 68, 18], ![3, 54, 33, 268, -282, -73, 44, 74]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, -1, 0, 2, 0], ![0, -2, -2, -2, -1, 1, -2, 4], ![3, 11, 4, 22, -36, 1, 14, 0], ![-1, 0, 1, 52, -51, -21, 2, 28], ![34, 159, 61, 320, -475, 2, 150, 4], ![-29, -48, 9, 272, -138, -171, -60, 166], ![50, 337, 149, 898, -1127, -101, 266, 106]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![0, -1, -1, -2, 0, 1, -1, 2], ![3, 11, 4, 22, -37, 1, 15, 0], ![-2, -6, -2, 15, -8, -11, -6, 15], ![15, 73, 28, 174, -245, -10, 68, 18], ![-29, -48, 9, 272, -138, -171, -60, 166], ![86, 467, 186, 988, -1381, -21, 391, 32], ![-20, 184, 158, 1225, -1106, -414, 106, 356]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, 2, 10, -17, 1, 6, 1], ![-1, 0, 1, 26, -25, -10, 2, 13], ![6, 31, 12, 76, -105, -5, 28, 9], ![3, 54, 33, 268, -282, -73, 44, 74], ![50, 337, 149, 898, -1127, -101, 266, 106], ![-20, 184, 158, 1225, -1106, -414, 106, 356], ![70, 784, 413, 2583, -2875, -488, 553, 425]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-8]], ![[], [], [], [], [], [], [-16], [-8, -8]], ![[], [], [], [], [], [-16], [0, -8], [-52, -4, -4]], ![[], [], [], [], [-16], [-16, -16], [-120, -8, -8], [-124, -56, -8, -4]], ![[], [], [], [-16], [-16, -16], [-240, 0, -16], [-24, -128, 0, -8], [-572, -76, -56, -4, -4]], ![[], [], [-16], [0, -8], [-120, -8, -8], [-24, -128, 0, -8], [-724, -16, -68, 0, -4], [-486, -314, -42, -30, -2, -2]], ![[], [-8], [-8, -8], [-52, -4, -4], [-124, -56, -8, -4], [-572, -76, -56, -4, -4], [-486, -314, -42, -30, -2, -2], [-1441, -370, -154, -34, -14, -2, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [-1, 0, 0, 2, 0, 0, 0, 0], [0, 0, 0, -1, 1, 0, 0, 0], [0, 0, 0, -2, 1, 1, 0, 0], [0, 0, 0, 0, -1, 0, 2, 0], [0, -1, -1, -2, 0, 1, -1, 2], [1, 5, 2, 10, -17, 1, 6, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0], [-1, 0, 0, 2, 0, 0, 0, 0], [0, -1, 0, -2, 2, 0, 0, 0], [0, 0, 0, -1, 0, 1, 0, 0], [0, 0, 0, 0, -2, 1, 2, 0], [0, -2, -2, -2, -1, 1, -2, 4], [3, 11, 4, 22, -37, 1, 15, 0], [-1, 0, 1, 26, -25, -10, 2, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, -1, 1, 0, 0, 0], [0, 0, 0, -1, 0, 1, 0, 0], [0, 0, 0, 1, -1, 0, 1, 0], [0, -1, -1, 0, -1, 0, 0, 2], [3, 11, 4, 22, -36, 1, 14, 0], [-2, -6, -2, 15, -8, -11, -6, 15], [6, 31, 12, 76, -105, -5, 28, 9]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, -2, 1, 1, 0, 0], [0, 0, 0, 0, -2, 1, 2, 0], [0, -1, -1, 0, -1, 0, 0, 2], [3, 9, 2, 20, -36, 1, 12, 4], [-1, 0, 1, 52, -51, -21, 2, 28], [15, 73, 28, 174, -245, -10, 68, 18], [3, 54, 33, 268, -282, -73, 44, 74]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, -1, 0, 2, 0], [0, -2, -2, -2, -1, 1, -2, 4], [3, 11, 4, 22, -36, 1, 14, 0], [-1, 0, 1, 52, -51, -21, 2, 28], [34, 159, 61, 320, -475, 2, 150, 4], [-29, -48, 9, 272, -138, -171, -60, 166], [50, 337, 149, 898, -1127, -101, 266, 106]], ![[0, 0, 0, 0, 0, 0, 1, 0], [0, -1, -1, -2, 0, 1, -1, 2], [3, 11, 4, 22, -37, 1, 15, 0], [-2, -6, -2, 15, -8, -11, -6, 15], [15, 73, 28, 174, -245, -10, 68, 18], [-29, -48, 9, 272, -138, -171, -60, 166], [86, 467, 186, 988, -1381, -21, 391, 32], [-20, 184, 158, 1225, -1106, -414, 106, 356]], ![[0, 0, 0, 0, 0, 0, 0, 1], [1, 5, 2, 10, -17, 1, 6, 1], [-1, 0, 1, 26, -25, -10, 2, 13], [6, 31, 12, 76, -105, -5, 28, 9], [3, 54, 33, 268, -282, -73, 44, 74], [50, 337, 149, 898, -1127, -101, 266, 106], [-20, 184, 158, 1225, -1106, -414, 106, 356], [70, 784, 413, 2583, -2875, -488, 553, 425]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 2
  a' := [2, 0, 2]
  b' := [0, 0, 0, 1]
  k := [1]
  f := [1, 0, 7, 0, -13, 0, 5]
  g := [2, 0, 1, 0, 1]
  h := [2, 0, 1, 0, 1]
  a := [1]
  b := [0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 4
  a' := [2]
  b' := [0, 4]
  k := [1]
  f := [1, 0, 5, 0, -6, 0, 4]
  g := [3, 0, 1]
  h := [2, 0, 2, 0, 4, 0, 1]
  a := [4]
  b := [4, 0, 2, 0, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [23, 0, 10, 0, 7]
  b' := [0, 1, 0, 22, 0, 23]
  k := [25, 0, 28, 0, 1]
  f := [19, 0, 3, 0, 16, 0, 2]
  g := [24, 0, 2, 0, 22, 0, 1]
  h := [23, 0, 1]
  a := [23, 0, 22, 0, 7]
  b := [6, 0, 7, 0, 15]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 4
  p := ![2, 3, 5, 29]
  exp := ![4, 1, 1, 1]
  pdgood := [3, 5, 29]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp3.out
    exact hp5.out
    exact hp29.out
  a := [6960, 0, -84558, 0, 39166, 0, -4072]
  b := [0, -5967, 0, 21550, 0, -6550, 0, 509]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29

noncomputable def M2 : MaximalOrderCertificateOfUnramifiedLists 2 O Om hm where
  n := 8
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0, 1, 1, 0], [1, 1, 0, 0, 1, 1, 0, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0], [1, 1, 0, 0, 1, 1, 1, 0], [1, 0, 1, 0, 1, 0, 0, 1]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0, 0], [0, 0, 0, 1, 1, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 1, 0, 1], [0, 1, 0, 0, 1, 1, 0, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 1, 1, 0, 1, 0, 0, 0], [1, 1, 0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 1, 1, 0, 0], [1, 1, 0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0, 0]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0], [1, 1, 0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 1, 1, 0, 0], [0, 1, 1, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0, 0], [0, 1, 1, 0, 1, 1, 0, 0]], ![[0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 1, 0, 0, 1, 1, 0], [1, 1, 0, 0, 1, 1, 1, 0], [0, 0, 0, 1, 0, 1, 0, 1], [1, 1, 0, 0, 1, 0, 0, 0], [1, 0, 1, 0, 0, 1, 0, 0], [0, 1, 0, 0, 1, 1, 1, 0], [0, 0, 0, 1, 0, 0, 0, 0]], ![[0, 0, 0, 0, 0, 0, 0, 1], [1, 1, 0, 0, 1, 1, 0, 1], [1, 0, 1, 0, 1, 0, 0, 1], [0, 1, 0, 0, 1, 1, 0, 1], [1, 0, 1, 0, 0, 1, 0, 0], [0, 1, 1, 0, 1, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 1, 1, 1, 0, 1, 1]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 1, 0], ![1, 1, 0, 0, 0, 1, 0, 0], ![0, 1, 1, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 1, 1, 1, 0], ![0, 0, 1, 1, 1, 0, 1, 1]]
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

end VoightMaximalOrderD8R23

namespace VoightMaximalOrderD8R25

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1095205625, [-1, 8, 2, -23, 2, 18, -5, -3, 1], 7⟩
local notation "l" => [-1, 8, 2, -23, 2, 18, -5, -3, 1]
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
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![7, 0, 0, 0, 0, 0, 0, 0], ![0, 7, 0, 0, 0, 0, 0, 0], ![0, 0, 7, 0, 0, 0, 0, 0], ![0, 0, 0, 7, 0, 0, 0, 0], ![0, 0, 0, 0, 7, 0, 0, 0], ![0, 0, 0, 0, 0, 7, 0, 0], ![0, 0, 0, 0, 0, 0, 7, 0], ![3, 6, 5, 0, 1, 5, 2, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-3, -6, -5, 0, -1, -5, -2, 7], ![-2, -5, -3, 4, -1, -6, 0, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-3, -6, -5, 0, -1, -5, -2, 7], ![-8, -26, -17, 23, -5, -33, -1, 21], ![-10, -27, -20, 17, -1, -31, -6, 25]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-3, -6, -5, 0, -1, -5, -2, 7], ![-8, -26, -17, 23, -5, -33, -1, 21], ![-39, -107, -84, 67, 3, -126, -31, 98], ![-32, -99, -72, 80, -2, -121, -19, 83]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-3, -6, -5, 0, -1, -5, -2, 7], ![-8, -26, -17, 23, -5, -33, -1, 21], ![-39, -107, -84, 67, 3, -126, -31, 98], ![-103, -343, -246, 308, 0, -430, -64, 273], ![-109, -333, -253, 260, 16, -405, -83, 282]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-3, -6, -5, 0, -1, -5, -2, 7], ![-8, -26, -17, 23, -5, -33, -1, 21], ![-39, -107, -84, 67, 3, -126, -31, 98], ![-103, -343, -246, 308, 0, -430, -64, 273], ![-354, -1084, -842, 846, 99, -1318, -302, 917], ![-315, -1021, -764, 875, 61, -1261, -239, 829]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-3, -6, -5, 0, -1, -5, -2, 7], ![-8, -26, -17, 23, -5, -33, -1, 21], ![-39, -107, -84, 67, 3, -126, -31, 98], ![-103, -343, -246, 308, 0, -430, -64, 273], ![-354, -1084, -842, 846, 99, -1318, -302, 917], ![-928, -3127, -2325, 2826, 231, -3893, -714, 2471], ![-941, -3026, -2313, 2552, 285, -3718, -783, 2472]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-2, -5, -3, 4, -1, -6, 0, 5], ![-10, -27, -20, 17, -1, -31, -6, 25], ![-32, -99, -72, 80, -2, -121, -19, 83], ![-109, -333, -253, 260, 16, -405, -83, 282], ![-315, -1021, -764, 875, 61, -1261, -239, 829], ![-941, -3026, -2313, 2552, 285, -3718, -783, 2472], ![-889, -2894, -2192, 2489, 249, -3567, -718, 2344]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-7]], ![[], [], [], [], [], [], [-49], [-35, -7]], ![[], [], [], [], [], [-49], [-147, -49], [-175, -35, -7]], ![[], [], [], [], [-49], [-147, -49], [-686, -147, -49], [-581, -175, -35, -7]], ![[], [], [], [-49], [-147, -49], [-686, -147, -49], [-1911, -686, -147, -49], [-1974, -581, -175, -35, -7]], ![[], [], [-49], [-147, -49], [-686, -147, -49], [-1911, -686, -147, -49], [-6419, -1911, -686, -147, -49], [-5803, -1974, -581, -175, -35, -7]], ![[], [-7], [-35, -7], [-175, -35, -7], [-581, -175, -35, -7], [-1974, -581, -175, -35, -7], [-5803, -1974, -581, -175, -35, -7], [-5654, -1838, -578, -159, -40, -7, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-3, -6, -5, 0, -1, -5, -2, 7], [-2, -5, -3, 4, -1, -6, 0, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-3, -6, -5, 0, -1, -5, -2, 7], [-8, -26, -17, 23, -5, -33, -1, 21], [-10, -27, -20, 17, -1, -31, -6, 25]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-3, -6, -5, 0, -1, -5, -2, 7], [-8, -26, -17, 23, -5, -33, -1, 21], [-39, -107, -84, 67, 3, -126, -31, 98], [-32, -99, -72, 80, -2, -121, -19, 83]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-3, -6, -5, 0, -1, -5, -2, 7], [-8, -26, -17, 23, -5, -33, -1, 21], [-39, -107, -84, 67, 3, -126, -31, 98], [-103, -343, -246, 308, 0, -430, -64, 273], [-109, -333, -253, 260, 16, -405, -83, 282]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-3, -6, -5, 0, -1, -5, -2, 7], [-8, -26, -17, 23, -5, -33, -1, 21], [-39, -107, -84, 67, 3, -126, -31, 98], [-103, -343, -246, 308, 0, -430, -64, 273], [-354, -1084, -842, 846, 99, -1318, -302, 917], [-315, -1021, -764, 875, 61, -1261, -239, 829]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-3, -6, -5, 0, -1, -5, -2, 7], [-8, -26, -17, 23, -5, -33, -1, 21], [-39, -107, -84, 67, 3, -126, -31, 98], [-103, -343, -246, 308, 0, -430, -64, 273], [-354, -1084, -842, 846, 99, -1318, -302, 917], [-928, -3127, -2325, 2826, 231, -3893, -714, 2471], [-941, -3026, -2313, 2552, 285, -3718, -783, 2472]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-2, -5, -3, 4, -1, -6, 0, 5], [-10, -27, -20, 17, -1, -31, -6, 25], [-32, -99, -72, 80, -2, -121, -19, 83], [-109, -333, -253, 260, 16, -405, -83, 282], [-315, -1021, -764, 875, 61, -1261, -239, 829], [-941, -3026, -2313, 2552, 285, -3718, -783, 2472], [-889, -2894, -2192, 2489, 249, -3567, -718, 2344]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp349 : Fact (Nat.Prime 349) := fact_iff.2 (by norm_num)
instance hp5021 : Fact (Nat.Prime 5021) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 2, 3]
  b' := [3, 2, 4, 3]
  k := [1]
  f := [1, 0, 2, 7, 2, -2, 2, 1]
  g := [2, 2, 2, 1, 1]
  h := [2, 2, 2, 1, 1]
  a := [1, 0, 3]
  b := [0, 0, 0, 4, 2, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD349 : CertificateDedekindCriterionLists l 349 where
  n := 2
  a' := [29, 266, 247, 230, 268, 154]
  b' := [100, 339, 282, 335, 179, 59, 327]
  k := [36, 181, 315, 18, 160, 68, 1]
  f := [47, 27, 136, 11, 108, 76, 83, 1]
  g := [118, 67, 341, 25, 271, 189, 207, 1]
  h := [139, 1]
  a := [54, 17, 188, 61, 112, 88, 92]
  b := [153, 243, 317, 70, 134, 152, 257]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD5021 : CertificateDedekindCriterionLists l 5021 where
  n := 2
  a' := [3577, 3271, 2628, 1389, 4373, 2978]
  b' := [3854, 851, 4397, 4679, 3543, 2244, 3161]
  k := [2820, 2646, 1165, 1487, 3160, 4036, 1]
  f := [376, 154, 222, 317, 153, 151, 443, 1]
  g := [3845, 1567, 2267, 3237, 1558, 1541, 4527, 1]
  h := [491, 1]
  a := [2524, 3253, 3479, 4430, 4871, 1911, 772]
  b := [1409, 1869, 4523, 1556, 3380, 2770, 4249]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [7] where
  n := 4
  p := ![5, 7, 349, 5021]
  exp := ![1, 2, 1, 1]
  pdgood := [5, 349, 5021]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp7.out
    exact hp349.out
    exact hp5021.out
  a := [-60460469, 1173219796, 1036965329, -4509643134, 1266147229, 1248910400, -457508672]
  b := [46107517, 184059185, -722836271, -164978429, 942049862, -227506471, -177559519, 57188584]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 349 T_ofList CD349
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5021 T_ofList CD5021

noncomputable def M7 : MaximalOrderCertificateOfUnramifiedLists 7 O Om hm where
  n := 8
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [4, 1, 2, 0, 6, 2, 5, 0], [5, 2, 4, 4, 6, 1, 0, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [4, 1, 2, 0, 6, 2, 5, 0], [6, 2, 4, 2, 2, 2, 6, 0], [4, 1, 1, 3, 6, 4, 1, 4]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [4, 1, 2, 0, 6, 2, 5, 0], [6, 2, 4, 2, 2, 2, 6, 0], [3, 5, 0, 4, 3, 0, 4, 0], [3, 6, 5, 3, 5, 5, 2, 6]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [4, 1, 2, 0, 6, 2, 5, 0], [6, 2, 4, 2, 2, 2, 6, 0], [3, 5, 0, 4, 3, 0, 4, 0], [2, 0, 6, 0, 0, 4, 6, 0], [3, 3, 6, 1, 2, 1, 1, 2]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [4, 1, 2, 0, 6, 2, 5, 0], [6, 2, 4, 2, 2, 2, 6, 0], [3, 5, 0, 4, 3, 0, 4, 0], [2, 0, 6, 0, 0, 4, 6, 0], [3, 1, 5, 6, 1, 5, 6, 0], [0, 1, 6, 0, 5, 6, 6, 3]], ![[0, 0, 0, 0, 0, 0, 1, 0], [4, 1, 2, 0, 6, 2, 5, 0], [6, 2, 4, 2, 2, 2, 6, 0], [3, 5, 0, 4, 3, 0, 4, 0], [2, 0, 6, 0, 0, 4, 6, 0], [3, 1, 5, 6, 1, 5, 6, 0], [3, 2, 6, 5, 0, 6, 0, 0], [4, 5, 4, 4, 5, 6, 1, 1]], ![[0, 0, 0, 0, 0, 0, 0, 1], [5, 2, 4, 4, 6, 1, 0, 5], [4, 1, 1, 3, 6, 4, 1, 4], [3, 6, 5, 3, 5, 5, 2, 6], [3, 3, 6, 1, 2, 1, 1, 2], [0, 1, 6, 0, 5, 6, 6, 3], [4, 5, 4, 4, 5, 6, 1, 1], [0, 4, 6, 4, 4, 3, 3, 6]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![2, 5, 0, 0, 0, 5, 5, 0], ![3, 2, 3, 5, 0, 4, 0, 0], ![3, 3, 5, 3, 0, 4, 1, 0], ![6, 4, 4, 3, 1, 1, 0, 0], ![1, 1, 4, 3, 0, 0, 5, 0], ![5, 4, 3, 4, 0, 2, 4, 0], ![2, 0, 2, 5, 0, 5, 1, 1]]
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

end VoightMaximalOrderD8R25

namespace VoightMaximalOrderD8R49

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1377663125, [1, 5, -22, -5, 33, 0, -12, 0, 1], 689⟩
local notation "l" => [1, 5, -22, -5, 33, 0, -12, 0, 1]
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

def basisDenominator : ℤ := 689
def basisNumerator : Fin 8 → Fin 8 → ℤ := ![![689, 0, 0, 0, 0, 0, 0, 0], ![0, 689, 0, 0, 0, 0, 0, 0], ![0, 0, 689, 0, 0, 0, 0, 0], ![0, 0, 0, 689, 0, 0, 0, 0], ![0, 0, 0, 0, 689, 0, 0, 0], ![0, 0, 0, 0, 0, 689, 0, 0], ![0, 0, 0, 0, 0, 0, 689, 0], ![368, 82, 312, 474, 316, 153, 601, 1]]

noncomputable def BQ : SubalgebraBuilderLists 8 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-368, -82, -312, -474, -316, -153, -601, 689], ![-321, -71, -272, -413, -275, -133, -524, 601]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-368, -82, -312, -474, -316, -153, -601, 689], ![-1, -5, 22, 5, -33, 0, 12, 0], ![-89, -24, -55, -109, -104, -36, -133, 165]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-368, -82, -312, -474, -316, -153, -601, 689], ![-1, -5, 22, 5, -33, 0, 12, 0], ![-4416, -985, -3749, -5666, -3787, -1869, -7212, 8268], ![-4021, -898, -3408, -5158, -3456, -1700, -6563, 7528]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-368, -82, -312, -474, -316, -153, -601, 689], ![-1, -5, 22, 5, -33, 0, 12, 0], ![-4416, -985, -3749, -5666, -3787, -1869, -7212, 8268], ![-12, -60, 263, 55, -374, 5, 111, 0], ![-1304, -343, -858, -1610, -1450, -541, -2009, 2421]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![-368, -82, -312, -474, -316, -153, -601, 689], ![-1, -5, 22, 5, -33, 0, 12, 0], ![-4416, -985, -3749, -5666, -3787, -1869, -7212, 8268], ![-12, -60, 263, 55, -374, 5, 111, 0], ![-40848, -9114, -34692, -52351, -35021, -17357, -66706, 76479], ![-37829, -8457, -32047, -48465, -32541, -16066, -61736, 70820]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![-368, -82, -312, -474, -316, -153, -601, 689], ![-1, -5, 22, 5, -33, 0, 12, 0], ![-4416, -985, -3749, -5666, -3787, -1869, -7212, 8268], ![-12, -60, 263, 55, -374, 5, 111, 0], ![-40848, -9114, -34692, -52351, -35021, -17357, -66706, 76479], ![-1951, -965, 870, -1875, -4980, -710, -2047, 3445], ![-14372, -3697, -9865, -17843, -15389, -5993, -22410, 26716]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![-321, -71, -272, -413, -275, -133, -524, 601], ![-89, -24, -55, -109, -104, -36, -133, 165], ![-4021, -898, -3408, -5158, -3456, -1700, -6563, 7528], ![-1304, -343, -858, -1610, -1450, -541, -2009, 2421], ![-37829, -8457, -32047, -48465, -32541, -16066, -61736, 70820], ![-14372, -3697, -9865, -17843, -15389, -5993, -22410, 26716], ![-24857, -6004, -18921, -31323, -24183, -10448, -39595, 46360]]]
  s := ![![[], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [-689]], ![[], [], [], [], [], [], [-474721], [-414089, -689]], ![[], [], [], [], [], [-474721], [0, -474721], [-113685, -414089, -689]], ![[], [], [], [], [-474721], [0, -474721], [-5696652, 0, -474721], [-5186792, -113685, -414089, -689]], ![[], [], [], [-474721], [0, -474721], [-5696652, 0, -474721], [0, -5696652, 0, -474721], [-1668069, -5186792, -113685, -414089, -689]], ![[], [], [-474721], [0, -474721], [-5696652, 0, -474721], [0, -5696652, 0, -474721], [-52694031, 0, -5696652, 0, -474721], [-48794980, -1668069, -5186792, -113685, -414089, -689]], ![[], [-689], [-414089, -689], [-113685, -414089, -689], [-5186792, -113685, -414089, -689], [-1668069, -5186792, -113685, -414089, -689], [-48794980, -1668069, -5186792, -113685, -414089, -689], [-45604601, -3014951, -4742384, -198962, -361519, -1202, -1]]]
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
def Table : Fin 8 → Fin 8 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-368, -82, -312, -474, -316, -153, -601, 689], [-321, -71, -272, -413, -275, -133, -524, 601]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-368, -82, -312, -474, -316, -153, -601, 689], [-1, -5, 22, 5, -33, 0, 12, 0], [-89, -24, -55, -109, -104, -36, -133, 165]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-368, -82, -312, -474, -316, -153, -601, 689], [-1, -5, 22, 5, -33, 0, 12, 0], [-4416, -985, -3749, -5666, -3787, -1869, -7212, 8268], [-4021, -898, -3408, -5158, -3456, -1700, -6563, 7528]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-368, -82, -312, -474, -316, -153, -601, 689], [-1, -5, 22, 5, -33, 0, 12, 0], [-4416, -985, -3749, -5666, -3787, -1869, -7212, 8268], [-12, -60, 263, 55, -374, 5, 111, 0], [-1304, -343, -858, -1610, -1450, -541, -2009, 2421]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [-368, -82, -312, -474, -316, -153, -601, 689], [-1, -5, 22, 5, -33, 0, 12, 0], [-4416, -985, -3749, -5666, -3787, -1869, -7212, 8268], [-12, -60, 263, 55, -374, 5, 111, 0], [-40848, -9114, -34692, -52351, -35021, -17357, -66706, 76479], [-37829, -8457, -32047, -48465, -32541, -16066, -61736, 70820]], ![[0, 0, 0, 0, 0, 0, 1, 0], [-368, -82, -312, -474, -316, -153, -601, 689], [-1, -5, 22, 5, -33, 0, 12, 0], [-4416, -985, -3749, -5666, -3787, -1869, -7212, 8268], [-12, -60, 263, 55, -374, 5, 111, 0], [-40848, -9114, -34692, -52351, -35021, -17357, -66706, 76479], [-1951, -965, 870, -1875, -4980, -710, -2047, 3445], [-14372, -3697, -9865, -17843, -15389, -5993, -22410, 26716]], ![[0, 0, 0, 0, 0, 0, 0, 1], [-321, -71, -272, -413, -275, -133, -524, 601], [-89, -24, -55, -109, -104, -36, -133, 165], [-4021, -898, -3408, -5158, -3456, -1700, -6563, 7528], [-1304, -343, -858, -1610, -1450, -541, -2009, 2421], [-37829, -8457, -32047, -48465, -32541, -16066, -61736, 70820], [-14372, -3697, -9865, -17843, -15389, -5993, -22410, 26716], [-24857, -6004, -18921, -31323, -24183, -10448, -39595, 46360]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp13 : Fact (Nat.Prime 13) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp53 : Fact (Nat.Prime 53) := fact_iff.2 (by norm_num)
instance hp2621 : Fact (Nat.Prime 2621) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 0, 4]
  b' := [0, 4, 0, 4]
  k := [1]
  f := [0, -1, 6, 1, -3, 0, 4]
  g := [1, 0, 4, 0, 1]
  h := [1, 0, 4, 0, 1]
  a := [2, 1, 2]
  b := [1, 2, 0, 1, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [21, 26, 3, 27, 2]
  b' := [7, 26, 3, 6, 25, 19]
  k := [20, 10, 20, 11, 1]
  f := [3, 9, 9, 6, 1, 5, 7, 1]
  g := [22, 17, 16, 2, 7, 20, 1]
  h := [4, 9, 1]
  a := [12, 9, 27, 3, 18, 1]
  b := [5, 19, 5, 3, 2, 24, 28]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2621 : CertificateDedekindCriterionLists l 2621 where
  n := 2
  a' := [2283, 280, 2410, 101, 504, 2057]
  b' := [1901, 1672, 2397, 834, 2025, 679, 455]
  k := [2085, 623, 1676, 1452, 1587, 1757, 1]
  f := [283, 208, 208, 416, 56, 86, 361, 1]
  g := [1717, 1258, 1259, 2521, 334, 521, 2189, 1]
  h := [432, 1]
  a := [2209, 1098, 649, 698, 1337, 1005, 2550]
  b := [2147, 117, 690, 2311, 1686, 257, 71]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [13, 53] where
  n := 5
  p := ![5, 13, 29, 53, 2621]
  exp := ![1, 2, 1, 2, 1]
  pdgood := [5, 29, 2621]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp13.out
    exact hp29.out
    exact hp53.out
    exact hp2621.out
  a := [163120540685, -114093243462, -755915847240, 152270061008, 469368800992, -18046887448, -53983937104]
  b := [3458960352, -109863040895, 26588913104, 199648863828, -25801340419, -78915076538, 2255860931, 6747992138]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2621 T_ofList CD2621

noncomputable def M13 : MaximalOrderCertificateOfUnramifiedLists 13 O Om hm where
  n := 8
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [9, 9, 0, 7, 9, 3, 10, 0], [4, 7, 1, 3, 11, 10, 9, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [9, 9, 0, 7, 9, 3, 10, 0], [12, 8, 9, 5, 6, 0, 12, 0], [2, 2, 10, 8, 0, 3, 10, 9]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [9, 9, 0, 7, 9, 3, 10, 0], [12, 8, 9, 5, 6, 0, 12, 0], [4, 3, 8, 2, 9, 3, 3, 0], [9, 12, 11, 3, 2, 3, 2, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [9, 9, 0, 7, 9, 3, 10, 0], [12, 8, 9, 5, 6, 0, 12, 0], [4, 3, 8, 2, 9, 3, 3, 0], [1, 5, 3, 3, 3, 5, 7, 0], [9, 8, 0, 2, 6, 5, 6, 3]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [9, 9, 0, 7, 9, 3, 10, 0], [12, 8, 9, 5, 6, 0, 12, 0], [4, 3, 8, 2, 9, 3, 3, 0], [1, 5, 3, 3, 3, 5, 7, 0], [11, 12, 5, 0, 1, 11, 10, 0], [1, 6, 11, 12, 11, 2, 1, 9]], ![[0, 0, 0, 0, 0, 0, 1, 0], [9, 9, 0, 7, 9, 3, 10, 0], [12, 8, 9, 5, 6, 0, 12, 0], [4, 3, 8, 2, 9, 3, 3, 0], [1, 5, 3, 3, 3, 5, 7, 0], [11, 12, 5, 0, 1, 11, 10, 0], [12, 10, 12, 10, 12, 5, 7, 0], [6, 8, 2, 6, 3, 0, 2, 1]], ![[0, 0, 0, 0, 0, 0, 0, 1], [4, 7, 1, 3, 11, 10, 9, 3], [2, 2, 10, 8, 0, 3, 10, 9], [9, 12, 11, 3, 2, 3, 2, 1], [9, 8, 0, 2, 6, 5, 6, 3], [1, 6, 11, 12, 11, 2, 1, 9], [6, 8, 2, 6, 3, 0, 2, 1], [12, 2, 7, 7, 10, 4, 3, 2]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![7, 2, 6, 4, 9, 3, 8, 0], ![0, 5, 5, 7, 2, 4, 4, 0], ![0, 6, 3, 8, 12, 8, 9, 0], ![7, 1, 12, 3, 9, 0, 11, 0], ![3, 11, 2, 3, 8, 0, 6, 0], ![5, 0, 0, 2, 7, 4, 2, 0], ![7, 0, 12, 3, 10, 12, 6, 12]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5, 6, 7]
  hindw := by decide
  hwFrobComp := by decide

noncomputable def M53 : MaximalOrderCertificateOfUnramifiedLists 53 O Om hm where
  n := 8
  t := 1
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [3, 24, 6, 3, 2, 6, 35, 0], [50, 35, 46, 11, 43, 26, 6, 18]], ![[0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [3, 24, 6, 3, 2, 6, 35, 0], [52, 48, 22, 5, 20, 0, 12, 0], [17, 29, 51, 50, 2, 17, 26, 6]], ![[0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [3, 24, 6, 3, 2, 6, 35, 0], [52, 48, 22, 5, 20, 0, 12, 0], [36, 22, 14, 5, 29, 39, 49, 0], [7, 3, 37, 36, 42, 49, 9, 2]], ![[0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [3, 24, 6, 3, 2, 6, 35, 0], [52, 48, 22, 5, 20, 0, 12, 0], [36, 22, 14, 5, 29, 39, 49, 0], [41, 46, 51, 2, 50, 5, 5, 0], [21, 28, 43, 33, 34, 42, 5, 36]], ![[0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [3, 24, 6, 3, 2, 6, 35, 0], [52, 48, 22, 5, 20, 0, 12, 0], [36, 22, 14, 5, 29, 39, 49, 0], [41, 46, 51, 2, 50, 5, 5, 0], [15, 2, 23, 13, 12, 27, 21, 0], [13, 23, 18, 30, 1, 46, 9, 12]], ![[0, 0, 0, 0, 0, 0, 1, 0], [3, 24, 6, 3, 2, 6, 35, 0], [52, 48, 22, 5, 20, 0, 12, 0], [36, 22, 14, 5, 29, 39, 49, 0], [41, 46, 51, 2, 50, 5, 5, 0], [15, 2, 23, 13, 12, 27, 21, 0], [10, 42, 22, 33, 2, 32, 20, 0], [44, 13, 46, 18, 34, 49, 9, 4]], ![[0, 0, 0, 0, 0, 0, 0, 1], [50, 35, 46, 11, 43, 26, 6, 18], [17, 29, 51, 50, 2, 17, 26, 6], [7, 3, 37, 36, 42, 49, 9, 2], [21, 28, 43, 33, 34, 42, 5, 36], [13, 23, 18, 30, 1, 46, 9, 12], [44, 13, 46, 18, 34, 49, 9, 4], [0, 38, 0, 0, 38, 46, 49, 38]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0, 0, 0], ![5, 2, 3, 47, 8, 18, 39, 0], ![46, 5, 1, 29, 34, 48, 5, 0], ![36, 39, 11, 36, 39, 7, 19, 0], ![13, 5, 16, 22, 32, 46, 39, 0], ![31, 45, 1, 44, 40, 24, 13, 0], ![39, 15, 48, 25, 16, 14, 11, 0], ![39, 22, 4, 40, 10, 41, 46, 52]]
  wFrob := ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5, 6, 7]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [13, 53]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 13 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M13
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 53 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M53
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [13, 53] D q hq hbad)
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

end VoightMaximalOrderD8R49

end TraceEuclidean
