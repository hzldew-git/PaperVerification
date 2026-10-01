import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk221
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

namespace VoightMaximalOrderD10R643

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6677215840625, [-1, 1, 20, 16, -42, -33, 29, 19, -8, -3, 1], 1⟩
local notation "l" => [-1, 1, 20, 16, -42, -33, 29, 19, -8, -3, 1]
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

def basisDenominator : ℤ := 1
def basisNumerator : Fin 10 → Fin 10 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 10 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -20, -16, 42, 33, -29, -19, 8, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -20, -16, 42, 33, -29, -19, 8, 3], ![3, -2, -61, -68, 110, 141, -54, -86, 5, 17]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -20, -16, 42, 33, -29, -19, 8, 3], ![3, -2, -61, -68, 110, 141, -54, -86, 5, 17], ![17, -14, -342, -333, 646, 671, -352, -377, 50, 56]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -20, -16, 42, 33, -29, -19, 8, 3], ![3, -2, -61, -68, 110, 141, -54, -86, 5, 17], ![17, -14, -342, -333, 646, 671, -352, -377, 50, 56], ![56, -39, -1134, -1238, 2019, 2494, -953, -1416, 71, 218]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -20, -16, 42, 33, -29, -19, 8, 3], ![3, -2, -61, -68, 110, 141, -54, -86, 5, 17], ![17, -14, -342, -333, 646, 671, -352, -377, 50, 56], ![56, -39, -1134, -1238, 2019, 2494, -953, -1416, 71, 218], ![218, -162, -4399, -4622, 7918, 9213, -3828, -5095, 328, 725]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -20, -16, 42, 33, -29, -19, 8, 3], ![3, -2, -61, -68, 110, 141, -54, -86, 5, 17], ![17, -14, -342, -333, 646, 671, -352, -377, 50, 56], ![56, -39, -1134, -1238, 2019, 2494, -953, -1416, 71, 218], ![218, -162, -4399, -4622, 7918, 9213, -3828, -5095, 328, 725], ![725, -507, -14662, -15999, 25828, 31843, -11812, -17603, 705, 2503]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -20, -16, 42, 33, -29, -19, 8, 3], ![3, -2, -61, -68, 110, 141, -54, -86, 5, 17], ![17, -14, -342, -333, 646, 671, -352, -377, 50, 56], ![56, -39, -1134, -1238, 2019, 2494, -953, -1416, 71, 218], ![218, -162, -4399, -4622, 7918, 9213, -3828, -5095, 328, 725], ![725, -507, -14662, -15999, 25828, 31843, -11812, -17603, 705, 2503], ![2503, -1778, -50567, -54710, 89127, 108427, -40744, -59369, 2421, 8214]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -20, -16, 42, 33, -29, -19, 8, 3], ![3, -2, -61, -68, 110, 141, -54, -86, 5, 17], ![17, -14, -342, -333, 646, 671, -352, -377, 50, 56], ![56, -39, -1134, -1238, 2019, 2494, -953, -1416, 71, 218], ![218, -162, -4399, -4622, 7918, 9213, -3828, -5095, 328, 725], ![725, -507, -14662, -15999, 25828, 31843, -11812, -17603, 705, 2503], ![2503, -1778, -50567, -54710, 89127, 108427, -40744, -59369, 2421, 8214], ![8214, -5711, -166058, -181991, 290278, 360189, -129779, -196810, 6343, 27063]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -20, -16, 42, 33, -29, -19, 8, 3], ![3, -2, -61, -68, 110, 141, -54, -86, 5, 17], ![17, -14, -342, -333, 646, 671, -352, -377, 50, 56], ![56, -39, -1134, -1238, 2019, 2494, -953, -1416, 71, 218], ![218, -162, -4399, -4622, 7918, 9213, -3828, -5095, 328, 725], ![725, -507, -14662, -15999, 25828, 31843, -11812, -17603, 705, 2503], ![2503, -1778, -50567, -54710, 89127, 108427, -40744, -59369, 2421, 8214], ![8214, -5711, -166058, -181991, 290278, 360189, -129779, -196810, 6343, 27063], ![27063, -18849, -546971, -599066, 954655, 1183357, -424638, -643976, 19694, 87532]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-56, -17, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-56, -17, -3, -1], [-218, -56, -17, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-56, -17, -3, -1], [-218, -56, -17, -3, -1], [-725, -218, -56, -17, -3, -1]], ![[], [], [], [-1], [-3, -1], [-17, -3, -1], [-56, -17, -3, -1], [-218, -56, -17, -3, -1], [-725, -218, -56, -17, -3, -1], [-2503, -725, -218, -56, -17, -3, -1]], ![[], [], [-1], [-3, -1], [-17, -3, -1], [-56, -17, -3, -1], [-218, -56, -17, -3, -1], [-725, -218, -56, -17, -3, -1], [-2503, -725, -218, -56, -17, -3, -1], [-8214, -2503, -725, -218, -56, -17, -3, -1]], ![[], [-1], [-3, -1], [-17, -3, -1], [-56, -17, -3, -1], [-218, -56, -17, -3, -1], [-725, -218, -56, -17, -3, -1], [-2503, -725, -218, -56, -17, -3, -1], [-8214, -2503, -725, -218, -56, -17, -3, -1], [-27063, -8214, -2503, -725, -218, -56, -17, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -20, -16, 42, 33, -29, -19, 8, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -20, -16, 42, 33, -29, -19, 8, 3], [3, -2, -61, -68, 110, 141, -54, -86, 5, 17]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -20, -16, 42, 33, -29, -19, 8, 3], [3, -2, -61, -68, 110, 141, -54, -86, 5, 17], [17, -14, -342, -333, 646, 671, -352, -377, 50, 56]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -20, -16, 42, 33, -29, -19, 8, 3], [3, -2, -61, -68, 110, 141, -54, -86, 5, 17], [17, -14, -342, -333, 646, 671, -352, -377, 50, 56], [56, -39, -1134, -1238, 2019, 2494, -953, -1416, 71, 218]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -20, -16, 42, 33, -29, -19, 8, 3], [3, -2, -61, -68, 110, 141, -54, -86, 5, 17], [17, -14, -342, -333, 646, 671, -352, -377, 50, 56], [56, -39, -1134, -1238, 2019, 2494, -953, -1416, 71, 218], [218, -162, -4399, -4622, 7918, 9213, -3828, -5095, 328, 725]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -20, -16, 42, 33, -29, -19, 8, 3], [3, -2, -61, -68, 110, 141, -54, -86, 5, 17], [17, -14, -342, -333, 646, 671, -352, -377, 50, 56], [56, -39, -1134, -1238, 2019, 2494, -953, -1416, 71, 218], [218, -162, -4399, -4622, 7918, 9213, -3828, -5095, 328, 725], [725, -507, -14662, -15999, 25828, 31843, -11812, -17603, 705, 2503]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -20, -16, 42, 33, -29, -19, 8, 3], [3, -2, -61, -68, 110, 141, -54, -86, 5, 17], [17, -14, -342, -333, 646, 671, -352, -377, 50, 56], [56, -39, -1134, -1238, 2019, 2494, -953, -1416, 71, 218], [218, -162, -4399, -4622, 7918, 9213, -3828, -5095, 328, 725], [725, -507, -14662, -15999, 25828, 31843, -11812, -17603, 705, 2503], [2503, -1778, -50567, -54710, 89127, 108427, -40744, -59369, 2421, 8214]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -20, -16, 42, 33, -29, -19, 8, 3], [3, -2, -61, -68, 110, 141, -54, -86, 5, 17], [17, -14, -342, -333, 646, 671, -352, -377, 50, 56], [56, -39, -1134, -1238, 2019, 2494, -953, -1416, 71, 218], [218, -162, -4399, -4622, 7918, 9213, -3828, -5095, 328, 725], [725, -507, -14662, -15999, 25828, 31843, -11812, -17603, 705, 2503], [2503, -1778, -50567, -54710, 89127, 108427, -40744, -59369, 2421, 8214], [8214, -5711, -166058, -181991, 290278, 360189, -129779, -196810, 6343, 27063]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -20, -16, 42, 33, -29, -19, 8, 3], [3, -2, -61, -68, 110, 141, -54, -86, 5, 17], [17, -14, -342, -333, 646, 671, -352, -377, 50, 56], [56, -39, -1134, -1238, 2019, 2494, -953, -1416, 71, 218], [218, -162, -4399, -4622, 7918, 9213, -3828, -5095, 328, 725], [725, -507, -14662, -15999, 25828, 31843, -11812, -17603, 705, 2503], [2503, -1778, -50567, -54710, 89127, 108427, -40744, -59369, 2421, 8214], [8214, -5711, -166058, -181991, 290278, 360189, -129779, -196810, 6343, 27063], [27063, -18849, -546971, -599066, 954655, 1183357, -424638, -643976, 19694, 87532]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp31 : Fact (Nat.Prime 31) := fact_iff.2 (by norm_num)
instance hp6266009 : Fact (Nat.Prime 6266009) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 1, 3]
  b' := [2, 3, 1, 1, 3]
  k := [1]
  f := [2, 1, 1, 2, 14, 13, -2, -1, 3, 1]
  g := [3, 1, 4, 3, 1, 1]
  h := [3, 1, 4, 3, 1, 1]
  a := [3, 2, 0, 4]
  b := [0, 1, 3, 4, 2, 2, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [1, 2, 8, 7, 9, 3, 8, 3]
  b' := [9, 0, 1, 8, 1, 1, 10, 2, 7]
  k := [8, 0, 3, 7, 4, 5, 3, 1, 1]
  f := [5, 7, 3, -1, 12, 8, 6, 0, 9, 2]
  g := [6, 8, 5, 0, 10, 5, 10, 1, 10, 1]
  h := [9, 1]
  a := [7, 8, 3, 4, 1, 0, 4, 5, 5]
  b := [9, 8, 5, 10, 1, 2, 2, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD31 : CertificateDedekindCriterionLists l 31 where
  n := 2
  a' := [8, 26, 29, 7, 9, 12, 29]
  b' := [27, 6, 29, 14, 15, 17, 19, 14]
  k := [26, 3, 27, 20, 4, 28, 6, 7, 1]
  f := [21, 10, 19, 17, 2, 17, 24, 2, 2, 1]
  g := [25, 11, 23, 20, 0, 19, 29, 2, 2, 1]
  h := [26, 1]
  a := [20, 10, 18, 21, 6, 23, 10, 6, 4]
  b := [13, 25, 1, 28, 23, 28, 21, 25, 27]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD6266009 : CertificateDedekindCriterionLists l 6266009 where
  n := 2
  a' := [5254976, 3154495, 2577845, 2155264, 2472822, 1545710, 4912512, 141370]
  b' := [1209178, 5393022, 1046051, 4243009, 2460470, 36712, 3251060, 1752047, 5554078]
  k := [2785875, 3411145, 1100985, 1451073, 1997868, 92533, 6005077, 2664313, 1]
  f := [4836419, 2837688, 1702472, 83419, 317055, 3635195, 1701195, 527187, 1048938, 1]
  g := [6142270, 3603873, 2162145, 105942, 402661, 4616711, 2160523, 669529, 1332155, 1]
  h := [4933851, 1]
  a := [652827, 3166459, 5391534, 591064, 4733182, 4393285, 1303366, 2563012, 5834805]
  b := [1775781, 4124406, 2693801, 4978650, 3287307, 2798197, 2083928, 3915139, 431204]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 11, 31, 6266009]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 11, 31, 6266009]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp11.out
    exact hp31.out
    exact hp6266009.out
  a := [-26345481630, -612632810890, -16666772757, 2513517339776, 46447822780, -2535534070334, 274910022716, 671704041078, -172159775140]
  b := [-15661936285, 40190122140, 267043726813, -37712194707, -580009382325, 44814534518, 376733410934, -48830386848, -72335197362, 17215977514]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 31 T_ofList CD31
    exact satisfiesDedekindCriterion_of_certificate_lists T l 6266009 T_ofList CD6266009

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ []
  · fin_cases hbad
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [] D q hq hbad)
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

end VoightMaximalOrderD10R643

namespace VoightMaximalOrderD10R645

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6695183565625, [1, -13, 2, 106, -28, -94, 27, 29, -9, -3, 1], 1⟩
local notation "l" => [1, -13, 2, 106, -28, -94, 27, 29, -9, -3, 1]
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

def basisDenominator : ℤ := 1
def basisNumerator : Fin 10 → Fin 10 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 10 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 13, -2, -106, 28, 94, -27, -29, 9, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 13, -2, -106, 28, 94, -27, -29, 9, 3], ![-3, 38, 7, -320, -22, 310, 13, -114, -2, 18]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 13, -2, -106, 28, 94, -27, -29, 9, 3], ![-3, 38, 7, -320, -22, 310, 13, -114, -2, 18], ![-18, 231, 2, -1901, 184, 1670, -176, -509, 48, 52]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 13, -2, -106, 28, 94, -27, -29, 9, 3], ![-3, 38, 7, -320, -22, 310, 13, -114, -2, 18], ![-18, 231, 2, -1901, 184, 1670, -176, -509, 48, 52], ![-52, 658, 127, -5510, -445, 5072, 266, -1684, -41, 204]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 13, -2, -106, 28, 94, -27, -29, 9, 3], ![-3, 38, 7, -320, -22, 310, 13, -114, -2, 18], ![-18, 231, 2, -1901, 184, 1670, -176, -509, 48, 52], ![-52, 658, 127, -5510, -445, 5072, 266, -1684, -41, 204], ![-204, 2600, 250, -21497, 202, 18731, -436, -5650, 152, 571]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 13, -2, -106, 28, 94, -27, -29, 9, 3], ![-3, 38, 7, -320, -22, 310, 13, -114, -2, 18], ![-18, 231, 2, -1901, 184, 1670, -176, -509, 48, 52], ![-52, 658, 127, -5510, -445, 5072, 266, -1684, -41, 204], ![-204, 2600, 250, -21497, 202, 18731, -436, -5650, 152, 571], ![-571, 7219, 1458, -60276, -5509, 53876, 3314, -16995, -511, 1865]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 13, -2, -106, 28, 94, -27, -29, 9, 3], ![-3, 38, 7, -320, -22, 310, 13, -114, -2, 18], ![-18, 231, 2, -1901, 184, 1670, -176, -509, 48, 52], ![-52, 658, 127, -5510, -445, 5072, 266, -1684, -41, 204], ![-204, 2600, 250, -21497, 202, 18731, -436, -5650, 152, 571], ![-571, 7219, 1458, -60276, -5509, 53876, 3314, -16995, -511, 1865], ![-1865, 23674, 3489, -196232, -8056, 169801, 3521, -50771, -210, 5084]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 13, -2, -106, 28, 94, -27, -29, 9, 3], ![-3, 38, 7, -320, -22, 310, 13, -114, -2, 18], ![-18, 231, 2, -1901, 184, 1670, -176, -509, 48, 52], ![-52, 658, 127, -5510, -445, 5072, 266, -1684, -41, 204], ![-204, 2600, 250, -21497, 202, 18731, -436, -5650, 152, 571], ![-571, 7219, 1458, -60276, -5509, 53876, 3314, -16995, -511, 1865], ![-1865, 23674, 3489, -196232, -8056, 169801, 3521, -50771, -210, 5084], ![-5084, 64227, 13506, -535415, -53880, 469840, 32533, -143915, -5015, 15042]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 13, -2, -106, 28, 94, -27, -29, 9, 3], ![-3, 38, 7, -320, -22, 310, 13, -114, -2, 18], ![-18, 231, 2, -1901, 184, 1670, -176, -509, 48, 52], ![-52, 658, 127, -5510, -445, 5072, 266, -1684, -41, 204], ![-204, 2600, 250, -21497, 202, 18731, -436, -5650, 152, 571], ![-571, 7219, 1458, -60276, -5509, 53876, 3314, -16995, -511, 1865], ![-1865, 23674, 3489, -196232, -8056, 169801, 3521, -50771, -210, 5084], ![-5084, 64227, 13506, -535415, -53880, 469840, 32533, -143915, -5015, 15042], ![-15042, 190462, 34143, -1580946, -114239, 1360068, 63706, -403685, -8537, 40111]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-18, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-18, -3, -1], [-52, -18, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-18, -3, -1], [-52, -18, -3, -1], [-204, -52, -18, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-18, -3, -1], [-52, -18, -3, -1], [-204, -52, -18, -3, -1], [-571, -204, -52, -18, -3, -1]], ![[], [], [], [-1], [-3, -1], [-18, -3, -1], [-52, -18, -3, -1], [-204, -52, -18, -3, -1], [-571, -204, -52, -18, -3, -1], [-1865, -571, -204, -52, -18, -3, -1]], ![[], [], [-1], [-3, -1], [-18, -3, -1], [-52, -18, -3, -1], [-204, -52, -18, -3, -1], [-571, -204, -52, -18, -3, -1], [-1865, -571, -204, -52, -18, -3, -1], [-5084, -1865, -571, -204, -52, -18, -3, -1]], ![[], [-1], [-3, -1], [-18, -3, -1], [-52, -18, -3, -1], [-204, -52, -18, -3, -1], [-571, -204, -52, -18, -3, -1], [-1865, -571, -204, -52, -18, -3, -1], [-5084, -1865, -571, -204, -52, -18, -3, -1], [-15042, -5084, -1865, -571, -204, -52, -18, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 13, -2, -106, 28, 94, -27, -29, 9, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 13, -2, -106, 28, 94, -27, -29, 9, 3], [-3, 38, 7, -320, -22, 310, 13, -114, -2, 18]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 13, -2, -106, 28, 94, -27, -29, 9, 3], [-3, 38, 7, -320, -22, 310, 13, -114, -2, 18], [-18, 231, 2, -1901, 184, 1670, -176, -509, 48, 52]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 13, -2, -106, 28, 94, -27, -29, 9, 3], [-3, 38, 7, -320, -22, 310, 13, -114, -2, 18], [-18, 231, 2, -1901, 184, 1670, -176, -509, 48, 52], [-52, 658, 127, -5510, -445, 5072, 266, -1684, -41, 204]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 13, -2, -106, 28, 94, -27, -29, 9, 3], [-3, 38, 7, -320, -22, 310, 13, -114, -2, 18], [-18, 231, 2, -1901, 184, 1670, -176, -509, 48, 52], [-52, 658, 127, -5510, -445, 5072, 266, -1684, -41, 204], [-204, 2600, 250, -21497, 202, 18731, -436, -5650, 152, 571]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 13, -2, -106, 28, 94, -27, -29, 9, 3], [-3, 38, 7, -320, -22, 310, 13, -114, -2, 18], [-18, 231, 2, -1901, 184, 1670, -176, -509, 48, 52], [-52, 658, 127, -5510, -445, 5072, 266, -1684, -41, 204], [-204, 2600, 250, -21497, 202, 18731, -436, -5650, 152, 571], [-571, 7219, 1458, -60276, -5509, 53876, 3314, -16995, -511, 1865]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 13, -2, -106, 28, 94, -27, -29, 9, 3], [-3, 38, 7, -320, -22, 310, 13, -114, -2, 18], [-18, 231, 2, -1901, 184, 1670, -176, -509, 48, 52], [-52, 658, 127, -5510, -445, 5072, 266, -1684, -41, 204], [-204, 2600, 250, -21497, 202, 18731, -436, -5650, 152, 571], [-571, 7219, 1458, -60276, -5509, 53876, 3314, -16995, -511, 1865], [-1865, 23674, 3489, -196232, -8056, 169801, 3521, -50771, -210, 5084]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 13, -2, -106, 28, 94, -27, -29, 9, 3], [-3, 38, 7, -320, -22, 310, 13, -114, -2, 18], [-18, 231, 2, -1901, 184, 1670, -176, -509, 48, 52], [-52, 658, 127, -5510, -445, 5072, 266, -1684, -41, 204], [-204, 2600, 250, -21497, 202, 18731, -436, -5650, 152, 571], [-571, 7219, 1458, -60276, -5509, 53876, 3314, -16995, -511, 1865], [-1865, 23674, 3489, -196232, -8056, 169801, 3521, -50771, -210, 5084], [-5084, 64227, 13506, -535415, -53880, 469840, 32533, -143915, -5015, 15042]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 13, -2, -106, 28, 94, -27, -29, 9, 3], [-3, 38, 7, -320, -22, 310, 13, -114, -2, 18], [-18, 231, 2, -1901, 184, 1670, -176, -509, 48, 52], [-52, 658, 127, -5510, -445, 5072, 266, -1684, -41, 204], [-204, 2600, 250, -21497, 202, 18731, -436, -5650, 152, 571], [-571, 7219, 1458, -60276, -5509, 53876, 3314, -16995, -511, 1865], [-1865, 23674, 3489, -196232, -8056, 169801, 3521, -50771, -210, 5084], [-5084, 64227, 13506, -535415, -53880, 469840, 32533, -143915, -5015, 15042], [-15042, 190462, 34143, -1580946, -114239, 1360068, 63706, -403685, -8537, 40111]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp137699 : Fact (Nat.Prime 137699) := fact_iff.2 (by norm_num)
instance hp15559 : Fact (Nat.Prime 15559) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 0, 1]
  b' := [3, 1, 0, 1, 1]
  k := [1]
  f := [3, 9, 6, -18, 8, 22, -3, -5, 2, 1]
  g := [4, 4, 2, 0, 1, 1]
  h := [4, 4, 2, 0, 1, 1]
  a := [4, 1, 4, 1, 4]
  b := [1, 3, 4, 0, 3, 2, 4, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD137699 : CertificateDedekindCriterionLists l 137699 where
  n := 2
  a' := [135249, 99467, 124228, 62560, 53808, 46801, 55969, 78555]
  b' := [31134, 31839, 29665, 35412, 19779, 12753, 13431, 29630, 83071]
  k := [96811, 78648, 97469, 69279, 84988, 105411, 56553, 18629, 1]
  f := [34659, 101087, 41630, 83462, 84211, 7162, 87675, 8885, 8683, 1]
  g := [37174, 108422, 44650, 89518, 90321, 7681, 94037, 9529, 9313, 1]
  h := [128383, 1]
  a := [81166, 16331, 46716, 59210, 56722, 134297, 64514, 46237, 76179]
  b := [6332, 82505, 115862, 86363, 41481, 68878, 15033, 27281, 61520]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD15559 : CertificateDedekindCriterionLists l 15559 where
  n := 2
  a' := [8157, 7621, 4669, 10841, 14993, 3671, 8640, 3373]
  b' := [10746, 2851, 12416, 7799, 7225, 6100, 7059, 6318, 1354]
  k := [11705, 1746, 13091, 2660, 13985, 4899, 2356, 8856, 1]
  f := [661, 2287, 2441, 1892, 918, 2345, 1957, 3123, 2629, 1]
  g := [3070, 10621, 11334, 8784, 4261, 10890, 9086, 14502, 12206, 1]
  h := [3350, 1]
  a := [7226, 11909, 2579, 232, 8133, 9275, 8798, 13627, 3979]
  b := [1409, 558, 12959, 9644, 15225, 2445, 7618, 4824, 11580]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 137699, 15559]
  exp := ![1, 1, 1]
  pdgood := [5, 137699, 15559]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp137699.out
    exact hp15559.out
  a := [-6973062646, -47282235208, 43130624317, 93036285036, -61770409516, -55725344718, 31390221903, 9580210578, -4941119640]
  b := [-1360412027, 2917379314, 17147080723, -11745373093, -21785745942, 11567654380, 8764161324, -4141248099, -1106254647, 494111964]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 137699 T_ofList CD137699
    exact satisfiesDedekindCriterion_of_certificate_lists T l 15559 T_ofList CD15559

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ []
  · fin_cases hbad
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [] D q hq hbad)
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

end VoightMaximalOrderD10R645

namespace VoightMaximalOrderD10R649

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6707391041857, [-1, -2, 20, -2, -43, 4, 33, -1, -10, 0, 1], 1⟩
local notation "l" => [-1, -2, 20, -2, -43, 4, 33, -1, -10, 0, 1]
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

def basisDenominator : ℤ := 1
def basisNumerator : Fin 10 → Fin 10 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 10 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -20, 2, 43, -4, -33, 1, 10, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -20, 2, 43, -4, -33, 1, 10, 0], ![0, 1, 2, -20, 2, 43, -4, -33, 1, 10]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -20, 2, 43, -4, -33, 1, 10, 0], ![0, 1, 2, -20, 2, 43, -4, -33, 1, 10], ![10, 20, -199, 22, 410, -38, -287, 6, 67, 1]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -20, 2, 43, -4, -33, 1, 10, 0], ![0, 1, 2, -20, 2, 43, -4, -33, 1, 10], ![10, 20, -199, 22, 410, -38, -287, 6, 67, 1], ![1, 12, 0, -197, 65, 406, -71, -286, 16, 67]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -20, 2, 43, -4, -33, 1, 10, 0], ![0, 1, 2, -20, 2, 43, -4, -33, 1, 10], ![10, 20, -199, 22, 410, -38, -287, 6, 67, 1], ![1, 12, 0, -197, 65, 406, -71, -286, 16, 67], ![67, 135, -1328, 134, 2684, -203, -1805, -4, 384, 16]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -20, 2, 43, -4, -33, 1, 10, 0], ![0, 1, 2, -20, 2, 43, -4, -33, 1, 10], ![10, 20, -199, 22, 410, -38, -287, 6, 67, 1], ![1, 12, 0, -197, 65, 406, -71, -286, 16, 67], ![67, 135, -1328, 134, 2684, -203, -1805, -4, 384, 16], ![16, 99, -185, -1296, 822, 2620, -731, -1789, 156, 384]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -20, 2, 43, -4, -33, 1, 10, 0], ![0, 1, 2, -20, 2, 43, -4, -33, 1, 10], ![10, 20, -199, 22, 410, -38, -287, 6, 67, 1], ![1, 12, 0, -197, 65, 406, -71, -286, 16, 67], ![67, 135, -1328, 134, 2684, -203, -1805, -4, 384, 16], ![16, 99, -185, -1296, 822, 2620, -731, -1789, 156, 384], ![384, 784, -7581, 583, 15216, -714, -10052, -347, 2051, 156]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -20, 2, 43, -4, -33, 1, 10, 0], ![0, 1, 2, -20, 2, 43, -4, -33, 1, 10], ![10, 20, -199, 22, 410, -38, -287, 6, 67, 1], ![1, 12, 0, -197, 65, 406, -71, -286, 16, 67], ![67, 135, -1328, 134, 2684, -203, -1805, -4, 384, 16], ![16, 99, -185, -1296, 822, 2620, -731, -1789, 156, 384], ![384, 784, -7581, 583, 15216, -714, -10052, -347, 2051, 156], ![156, 696, -2336, -7269, 7291, 14592, -5862, -9896, 1213, 2051]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -20, 2, 43, -4, -33, 1, 10, 0], ![0, 1, 2, -20, 2, 43, -4, -33, 1, 10], ![10, 20, -199, 22, 410, -38, -287, 6, 67, 1], ![1, 12, 0, -197, 65, 406, -71, -286, 16, 67], ![67, 135, -1328, 134, 2684, -203, -1805, -4, 384, 16], ![16, 99, -185, -1296, 822, 2620, -731, -1789, 156, 384], ![384, 784, -7581, 583, 15216, -714, -10052, -347, 2051, 156], ![156, 696, -2336, -7269, 7291, 14592, -5862, -9896, 1213, 2051], ![2051, 4258, -40324, 1766, 80924, -913, -53091, -3811, 10614, 1213]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-10, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-67, -1, -10, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-67, -1, -10, 0, -1], [-16, -67, -1, -10, 0, -1]], ![[], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-67, -1, -10, 0, -1], [-16, -67, -1, -10, 0, -1], [-384, -16, -67, -1, -10, 0, -1]], ![[], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-67, -1, -10, 0, -1], [-16, -67, -1, -10, 0, -1], [-384, -16, -67, -1, -10, 0, -1], [-156, -384, -16, -67, -1, -10, 0, -1]], ![[], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-67, -1, -10, 0, -1], [-16, -67, -1, -10, 0, -1], [-384, -16, -67, -1, -10, 0, -1], [-156, -384, -16, -67, -1, -10, 0, -1], [-2051, -156, -384, -16, -67, -1, -10, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -20, 2, 43, -4, -33, 1, 10, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -20, 2, 43, -4, -33, 1, 10, 0], [0, 1, 2, -20, 2, 43, -4, -33, 1, 10]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -20, 2, 43, -4, -33, 1, 10, 0], [0, 1, 2, -20, 2, 43, -4, -33, 1, 10], [10, 20, -199, 22, 410, -38, -287, 6, 67, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -20, 2, 43, -4, -33, 1, 10, 0], [0, 1, 2, -20, 2, 43, -4, -33, 1, 10], [10, 20, -199, 22, 410, -38, -287, 6, 67, 1], [1, 12, 0, -197, 65, 406, -71, -286, 16, 67]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -20, 2, 43, -4, -33, 1, 10, 0], [0, 1, 2, -20, 2, 43, -4, -33, 1, 10], [10, 20, -199, 22, 410, -38, -287, 6, 67, 1], [1, 12, 0, -197, 65, 406, -71, -286, 16, 67], [67, 135, -1328, 134, 2684, -203, -1805, -4, 384, 16]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -20, 2, 43, -4, -33, 1, 10, 0], [0, 1, 2, -20, 2, 43, -4, -33, 1, 10], [10, 20, -199, 22, 410, -38, -287, 6, 67, 1], [1, 12, 0, -197, 65, 406, -71, -286, 16, 67], [67, 135, -1328, 134, 2684, -203, -1805, -4, 384, 16], [16, 99, -185, -1296, 822, 2620, -731, -1789, 156, 384]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -20, 2, 43, -4, -33, 1, 10, 0], [0, 1, 2, -20, 2, 43, -4, -33, 1, 10], [10, 20, -199, 22, 410, -38, -287, 6, 67, 1], [1, 12, 0, -197, 65, 406, -71, -286, 16, 67], [67, 135, -1328, 134, 2684, -203, -1805, -4, 384, 16], [16, 99, -185, -1296, 822, 2620, -731, -1789, 156, 384], [384, 784, -7581, 583, 15216, -714, -10052, -347, 2051, 156]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -20, 2, 43, -4, -33, 1, 10, 0], [0, 1, 2, -20, 2, 43, -4, -33, 1, 10], [10, 20, -199, 22, 410, -38, -287, 6, 67, 1], [1, 12, 0, -197, 65, 406, -71, -286, 16, 67], [67, 135, -1328, 134, 2684, -203, -1805, -4, 384, 16], [16, 99, -185, -1296, 822, 2620, -731, -1789, 156, 384], [384, 784, -7581, 583, 15216, -714, -10052, -347, 2051, 156], [156, 696, -2336, -7269, 7291, 14592, -5862, -9896, 1213, 2051]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -20, 2, 43, -4, -33, 1, 10, 0], [0, 1, 2, -20, 2, 43, -4, -33, 1, 10], [10, 20, -199, 22, 410, -38, -287, 6, 67, 1], [1, 12, 0, -197, 65, 406, -71, -286, 16, 67], [67, 135, -1328, 134, 2684, -203, -1805, -4, 384, 16], [16, 99, -185, -1296, 822, 2620, -731, -1789, 156, 384], [384, 784, -7581, 583, 15216, -714, -10052, -347, 2051, 156], [156, 696, -2336, -7269, 7291, 14592, -5862, -9896, 1213, 2051], [2051, 4258, -40324, 1766, 80924, -913, -53091, -3811, 10614, 1213]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp55432983817 : Fact (Nat.Prime 55432983817) := fact_iff.2 (by norm_num)

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [3, 2, 7, 5, 5, 10, 10]
  b' := [5, 7, 0, 6, 9, 2, 5, 7]
  k := [7, 1, 7, 0, 6, 8, 1]
  f := [1, 6, 7, 7, 10, 5, 1, 3, 4, 1]
  g := [2, 10, 5, 6, 4, 5, 1, 4, 1]
  h := [5, 7, 1]
  a := [8, 0, 10, 5, 10, 7, 6, 9]
  b := [2, 10, 0, 2, 4, 9, 8, 5, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD55432983817 : CertificateDedekindCriterionLists l 55432983817 where
  n := 2
  a' := [42597232053, 20269092739, 31555312147, 14831624307, 17037676823, 23544247228, 46514916307, 52565174492]
  b' := [9451194277, 38068776496, 6867580520, 34906553688, 50428738902, 51088502917, 51116368322, 173578863, 24955527177]
  k := [13356513340, 19962118598, 17735946663, 52591108700, 3994191205, 16377500718, 34202549049, 28285204525, 1]
  f := [5400426367, 7530239723, 8441801790, 8266090950, 11353751232, 9121519966, 7441383546, 11840988889, 10250047641, 1]
  g := [22054234653, 30751955966, 34474588654, 33757021589, 46366393472, 37250418399, 30389085546, 48356172221, 41859094171, 1]
  h := [13573889646, 1]
  a := [32906643602, 95881117, 1162992248, 14939921837, 717686515, 10879229860, 4393104543, 44797795143, 19812379645]
  b := [15799330828, 38337962741, 9887317288, 5703775175, 48619249299, 1839817409, 3868262290, 48649044451, 35620604172]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![11, 55432983817]
  exp := ![1, 1]
  pdgood := [11, 55432983817]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp11.out
    exact hp55432983817.out
  a := [-485030822009, -2405888113964, 9984818373908, 10729227116940, -22579053628899, -8320234552486, 12633287552920, 1583254426490, -1898810191020]
  b := [-62365999989, 440654879211, 1563366291107, -3614445066448, -2256445590570, 4300393652783, 1091710034816, -1643090793496, -158325442649, 189881019102]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 55432983817 T_ofList CD55432983817

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ []
  · fin_cases hbad
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [] D q hq hbad)
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

end VoightMaximalOrderD10R649

namespace VoightMaximalOrderD10R650

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6712338666357, [-1, -7, 10, 37, -22, -51, 18, 22, -7, -3, 1], 1⟩
local notation "l" => [-1, -7, 10, 37, -22, -51, 18, 22, -7, -3, 1]
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

def basisDenominator : ℤ := 1
def basisNumerator : Fin 10 → Fin 10 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 10 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -10, -37, 22, 51, -18, -22, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -10, -37, 22, 51, -18, -22, 7, 3], ![3, 22, -23, -121, 29, 175, -3, -84, -1, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -10, -37, 22, 51, -18, -22, 7, 3], ![3, 22, -23, -121, 29, 175, -3, -84, -1, 16], ![16, 115, -138, -615, 231, 845, -113, -355, 28, 47]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -10, -37, 22, 51, -18, -22, 7, 3], ![3, 22, -23, -121, 29, 175, -3, -84, -1, 16], ![16, 115, -138, -615, 231, 845, -113, -355, 28, 47], ![47, 345, -355, -1877, 419, 2628, -1, -1147, -26, 169]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -10, -37, 22, 51, -18, -22, 7, 3], ![3, 22, -23, -121, 29, 175, -3, -84, -1, 16], ![16, 115, -138, -615, 231, 845, -113, -355, 28, 47], ![47, 345, -355, -1877, 419, 2628, -1, -1147, -26, 169], ![169, 1230, -1345, -6608, 1841, 9038, -414, -3719, 36, 481]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -10, -37, 22, 51, -18, -22, 7, 3], ![3, 22, -23, -121, 29, 175, -3, -84, -1, 16], ![16, 115, -138, -615, 231, 845, -113, -355, 28, 47], ![47, 345, -355, -1877, 419, 2628, -1, -1147, -26, 169], ![169, 1230, -1345, -6608, 1841, 9038, -414, -3719, 36, 481], ![481, 3536, -3580, -19142, 3974, 26372, 380, -10996, -352, 1479]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -10, -37, 22, 51, -18, -22, 7, 3], ![3, 22, -23, -121, 29, 175, -3, -84, -1, 16], ![16, 115, -138, -615, 231, 845, -113, -355, 28, 47], ![47, 345, -355, -1877, 419, 2628, -1, -1147, -26, 169], ![169, 1230, -1345, -6608, 1841, 9038, -414, -3719, 36, 481], ![481, 3536, -3580, -19142, 3974, 26372, 380, -10996, -352, 1479], ![1479, 10834, -11254, -58303, 13396, 79403, -250, -32158, -643, 4085]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -10, -37, 22, 51, -18, -22, 7, 3], ![3, 22, -23, -121, 29, 175, -3, -84, -1, 16], ![16, 115, -138, -615, 231, 845, -113, -355, 28, 47], ![47, 345, -355, -1877, 419, 2628, -1, -1147, -26, 169], ![169, 1230, -1345, -6608, 1841, 9038, -414, -3719, 36, 481], ![481, 3536, -3580, -19142, 3974, 26372, 380, -10996, -352, 1479], ![1479, 10834, -11254, -58303, 13396, 79403, -250, -32158, -643, 4085], ![4085, 30074, -30016, -162399, 31567, 221731, 5873, -90120, -3563, 11612]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -10, -37, 22, 51, -18, -22, 7, 3], ![3, 22, -23, -121, 29, 175, -3, -84, -1, 16], ![16, 115, -138, -615, 231, 845, -113, -355, 28, 47], ![47, 345, -355, -1877, 419, 2628, -1, -1147, -26, 169], ![169, 1230, -1345, -6608, 1841, 9038, -414, -3719, 36, 481], ![481, 3536, -3580, -19142, 3974, 26372, 380, -10996, -352, 1479], ![1479, 10834, -11254, -58303, 13396, 79403, -250, -32158, -643, 4085], ![4085, 30074, -30016, -162399, 31567, 221731, 5873, -90120, -3563, 11612], ![11612, 85369, -86046, -459660, 93065, 623779, 12715, -249591, -8836, 31273]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1], [-169, -47, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1], [-169, -47, -16, -3, -1], [-481, -169, -47, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1], [-169, -47, -16, -3, -1], [-481, -169, -47, -16, -3, -1], [-1479, -481, -169, -47, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1], [-169, -47, -16, -3, -1], [-481, -169, -47, -16, -3, -1], [-1479, -481, -169, -47, -16, -3, -1], [-4085, -1479, -481, -169, -47, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-47, -16, -3, -1], [-169, -47, -16, -3, -1], [-481, -169, -47, -16, -3, -1], [-1479, -481, -169, -47, -16, -3, -1], [-4085, -1479, -481, -169, -47, -16, -3, -1], [-11612, -4085, -1479, -481, -169, -47, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -10, -37, 22, 51, -18, -22, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -10, -37, 22, 51, -18, -22, 7, 3], [3, 22, -23, -121, 29, 175, -3, -84, -1, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -10, -37, 22, 51, -18, -22, 7, 3], [3, 22, -23, -121, 29, 175, -3, -84, -1, 16], [16, 115, -138, -615, 231, 845, -113, -355, 28, 47]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -10, -37, 22, 51, -18, -22, 7, 3], [3, 22, -23, -121, 29, 175, -3, -84, -1, 16], [16, 115, -138, -615, 231, 845, -113, -355, 28, 47], [47, 345, -355, -1877, 419, 2628, -1, -1147, -26, 169]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -10, -37, 22, 51, -18, -22, 7, 3], [3, 22, -23, -121, 29, 175, -3, -84, -1, 16], [16, 115, -138, -615, 231, 845, -113, -355, 28, 47], [47, 345, -355, -1877, 419, 2628, -1, -1147, -26, 169], [169, 1230, -1345, -6608, 1841, 9038, -414, -3719, 36, 481]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -10, -37, 22, 51, -18, -22, 7, 3], [3, 22, -23, -121, 29, 175, -3, -84, -1, 16], [16, 115, -138, -615, 231, 845, -113, -355, 28, 47], [47, 345, -355, -1877, 419, 2628, -1, -1147, -26, 169], [169, 1230, -1345, -6608, 1841, 9038, -414, -3719, 36, 481], [481, 3536, -3580, -19142, 3974, 26372, 380, -10996, -352, 1479]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -10, -37, 22, 51, -18, -22, 7, 3], [3, 22, -23, -121, 29, 175, -3, -84, -1, 16], [16, 115, -138, -615, 231, 845, -113, -355, 28, 47], [47, 345, -355, -1877, 419, 2628, -1, -1147, -26, 169], [169, 1230, -1345, -6608, 1841, 9038, -414, -3719, 36, 481], [481, 3536, -3580, -19142, 3974, 26372, 380, -10996, -352, 1479], [1479, 10834, -11254, -58303, 13396, 79403, -250, -32158, -643, 4085]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -10, -37, 22, 51, -18, -22, 7, 3], [3, 22, -23, -121, 29, 175, -3, -84, -1, 16], [16, 115, -138, -615, 231, 845, -113, -355, 28, 47], [47, 345, -355, -1877, 419, 2628, -1, -1147, -26, 169], [169, 1230, -1345, -6608, 1841, 9038, -414, -3719, 36, 481], [481, 3536, -3580, -19142, 3974, 26372, 380, -10996, -352, 1479], [1479, 10834, -11254, -58303, 13396, 79403, -250, -32158, -643, 4085], [4085, 30074, -30016, -162399, 31567, 221731, 5873, -90120, -3563, 11612]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -10, -37, 22, 51, -18, -22, 7, 3], [3, 22, -23, -121, 29, 175, -3, -84, -1, 16], [16, 115, -138, -615, 231, 845, -113, -355, 28, 47], [47, 345, -355, -1877, 419, 2628, -1, -1147, -26, 169], [169, 1230, -1345, -6608, 1841, 9038, -414, -3719, 36, 481], [481, 3536, -3580, -19142, 3974, 26372, 380, -10996, -352, 1479], [1479, 10834, -11254, -58303, 13396, 79403, -250, -32158, -643, 4085], [4085, 30074, -30016, -162399, 31567, 221731, 5873, -90120, -3563, 11612], [11612, 85369, -86046, -459660, 93065, 623779, 12715, -249591, -8836, 31273]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp3613 : Fact (Nat.Prime 3613) := fact_iff.2 (by norm_num)
instance hp22936169 : Fact (Nat.Prime 22936169) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 5
  a' := [2, 2, 1, 1]
  b' := [0, 0, 1, 0, 2, 1]
  k := [1, 0, 1, 2, 2, 1, 1, 0, 1, 1, 2, 0, 0, 1, 1, 2, 1, 0, 2, 2, 1]
  f := [1, 4, -2, -9, 10, 19, -3, -6, 3, 2]
  g := [2, 1, 2, 2, 0, 1, 1]
  h := [1, 2, 0, 2, 1]
  a := [2, 0, 0, 2, 2, 1]
  b := [1, 0, 1, 2, 1, 0, 1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3613 : CertificateDedekindCriterionLists l 3613 where
  n := 2
  a' := [954, 2200, 3536, 2210, 2945, 2959, 506, 2120]
  b' := [1515, 3315, 2203, 581, 1459, 2725, 1084, 1813, 2976]
  k := [1255, 2246, 214, 1411, 2431, 826, 1695, 1561, 1]
  f := [1039, 628, 859, 1873, 633, 2528, 1025, 1714, 611, 1]
  g := [1326, 801, 1096, 2390, 807, 3226, 1307, 2187, 779, 1]
  h := [2831, 1]
  a := [3039, 1628, 626, 2003, 3031, 835, 2979, 3529, 426]
  b := [1368, 1712, 3354, 1975, 623, 1651, 875, 3005, 3187]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD22936169 : CertificateDedekindCriterionLists l 22936169 where
  n := 2
  a' := [442107, 2178436, 19974331, 1529094, 21893977, 4103105, 1000865, 10264600]
  b' := [9098602, 13955511, 12345311, 741660, 19775449, 18997418, 16146582, 20641238, 11601805]
  k := [10553463, 7018315, 3482757, 15352098, 2018583, 18555047, 8447174, 19724106, 1]
  f := [1011099, 1520632, 1511163, 733974, 518181, 627516, 739229, 309619, 1493573, 1]
  g := [14439791, 21716567, 21581333, 10482077, 7400283, 8961729, 10557133, 4421750, 21330136, 1]
  h := [1606030, 1]
  a := [18585172, 19145632, 13843155, 7309682, 9286332, 17721070, 8375746, 8376164, 6403174]
  b := [12108458, 12387636, 819947, 7157268, 13026855, 19010221, 14930716, 7258993, 16532995]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![3, 3613, 22936169]
  exp := ![1, 1, 1]
  pdgood := [3, 3613, 22936169]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp3613.out
    exact hp22936169.out
  a := [7739983575, -967502212430, 362716606871, 3534252646418, -994306897781, -2463770807494, 761466551510, 469895338704, -164730237720]
  b := [-36620731338, 25843957235, 419882383153, -138994336093, -742154427766, 187273123281, 355820691259, -98455177526, -51931441002, 16473023772]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3613 T_ofList CD3613
    exact satisfiesDedekindCriterion_of_certificate_lists T l 22936169 T_ofList CD22936169

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ []
  · fin_cases hbad
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [] D q hq hbad)
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

end VoightMaximalOrderD10R650

end TraceEuclidean
