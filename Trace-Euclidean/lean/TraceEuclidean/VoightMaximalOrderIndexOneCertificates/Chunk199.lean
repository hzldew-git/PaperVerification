import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk195
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

namespace VoightMaximalOrderD10R341

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4493375094592, [-2, -2, 16, 8, -37, -11, 31, 6, -10, -1, 1], 1⟩
local notation "l" => [-2, -2, 16, 8, -37, -11, 31, 6, -10, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 2, -16, -8, 37, 11, -31, -6, 10, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 2, -16, -8, 37, 11, -31, -6, 10, 1], ![2, 4, -14, -24, 29, 48, -20, -37, 4, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 2, -16, -8, 37, 11, -31, -6, 10, 1], ![2, 4, -14, -24, 29, 48, -20, -37, 4, 11], ![22, 24, -172, -102, 383, 150, -293, -86, 73, 15]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 2, -16, -8, 37, 11, -31, -6, 10, 1], ![2, 4, -14, -24, 29, 48, -20, -37, 4, 11], ![22, 24, -172, -102, 383, 150, -293, -86, 73, 15], ![30, 52, -216, -292, 453, 548, -315, -383, 64, 88]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 2, -16, -8, 37, 11, -31, -6, 10, 1], ![2, 4, -14, -24, 29, 48, -20, -37, 4, 11], ![22, 24, -172, -102, 383, 150, -293, -86, 73, 15], ![30, 52, -216, -292, 453, 548, -315, -383, 64, 88], ![176, 206, -1356, -920, 2964, 1421, -2180, -843, 497, 152]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 2, -16, -8, 37, 11, -31, -6, 10, 1], ![2, 4, -14, -24, 29, 48, -20, -37, 4, 11], ![22, 24, -172, -102, 383, 150, -293, -86, 73, 15], ![30, 52, -216, -292, 453, 548, -315, -383, 64, 88], ![176, 206, -1356, -920, 2964, 1421, -2180, -843, 497, 152], ![304, 480, -2226, -2572, 4704, 4636, -3291, -3092, 677, 649]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 2, -16, -8, 37, 11, -31, -6, 10, 1], ![2, 4, -14, -24, 29, 48, -20, -37, 4, 11], ![22, 24, -172, -102, 383, 150, -293, -86, 73, 15], ![30, 52, -216, -292, 453, 548, -315, -383, 64, 88], ![176, 206, -1356, -920, 2964, 1421, -2180, -843, 497, 152], ![304, 480, -2226, -2572, 4704, 4636, -3291, -3092, 677, 649], ![1298, 1602, -9904, -7418, 21441, 11843, -15483, -7185, 3398, 1326]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 2, -16, -8, 37, 11, -31, -6, 10, 1], ![2, 4, -14, -24, 29, 48, -20, -37, 4, 11], ![22, 24, -172, -102, 383, 150, -293, -86, 73, 15], ![30, 52, -216, -292, 453, 548, -315, -383, 64, 88], ![176, 206, -1356, -920, 2964, 1421, -2180, -843, 497, 152], ![304, 480, -2226, -2572, 4704, 4636, -3291, -3092, 677, 649], ![1298, 1602, -9904, -7418, 21441, 11843, -15483, -7185, 3398, 1326], ![2652, 3950, -19614, -20512, 41644, 36027, -29263, -23439, 6075, 4724]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 2, -16, -8, 37, 11, -31, -6, 10, 1], ![2, 4, -14, -24, 29, 48, -20, -37, 4, 11], ![22, 24, -172, -102, 383, 150, -293, -86, 73, 15], ![30, 52, -216, -292, 453, 548, -315, -383, 64, 88], ![176, 206, -1356, -920, 2964, 1421, -2180, -843, 497, 152], ![304, 480, -2226, -2572, 4704, 4636, -3291, -3092, 677, 649], ![1298, 1602, -9904, -7418, 21441, 11843, -15483, -7185, 3398, 1326], ![2652, 3950, -19614, -20512, 41644, 36027, -29263, -23439, 6075, 4724], ![9448, 12100, -71634, -57406, 154276, 93608, -110417, -57607, 23801, 10799]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-15, -11, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-15, -11, -1, -1], [-88, -15, -11, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-15, -11, -1, -1], [-88, -15, -11, -1, -1], [-152, -88, -15, -11, -1, -1]], ![[], [], [], [-1], [-1, -1], [-11, -1, -1], [-15, -11, -1, -1], [-88, -15, -11, -1, -1], [-152, -88, -15, -11, -1, -1], [-649, -152, -88, -15, -11, -1, -1]], ![[], [], [-1], [-1, -1], [-11, -1, -1], [-15, -11, -1, -1], [-88, -15, -11, -1, -1], [-152, -88, -15, -11, -1, -1], [-649, -152, -88, -15, -11, -1, -1], [-1326, -649, -152, -88, -15, -11, -1, -1]], ![[], [-1], [-1, -1], [-11, -1, -1], [-15, -11, -1, -1], [-88, -15, -11, -1, -1], [-152, -88, -15, -11, -1, -1], [-649, -152, -88, -15, -11, -1, -1], [-1326, -649, -152, -88, -15, -11, -1, -1], [-4724, -1326, -649, -152, -88, -15, -11, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 2, -16, -8, 37, 11, -31, -6, 10, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 2, -16, -8, 37, 11, -31, -6, 10, 1], [2, 4, -14, -24, 29, 48, -20, -37, 4, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 2, -16, -8, 37, 11, -31, -6, 10, 1], [2, 4, -14, -24, 29, 48, -20, -37, 4, 11], [22, 24, -172, -102, 383, 150, -293, -86, 73, 15]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 2, -16, -8, 37, 11, -31, -6, 10, 1], [2, 4, -14, -24, 29, 48, -20, -37, 4, 11], [22, 24, -172, -102, 383, 150, -293, -86, 73, 15], [30, 52, -216, -292, 453, 548, -315, -383, 64, 88]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 2, -16, -8, 37, 11, -31, -6, 10, 1], [2, 4, -14, -24, 29, 48, -20, -37, 4, 11], [22, 24, -172, -102, 383, 150, -293, -86, 73, 15], [30, 52, -216, -292, 453, 548, -315, -383, 64, 88], [176, 206, -1356, -920, 2964, 1421, -2180, -843, 497, 152]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 2, -16, -8, 37, 11, -31, -6, 10, 1], [2, 4, -14, -24, 29, 48, -20, -37, 4, 11], [22, 24, -172, -102, 383, 150, -293, -86, 73, 15], [30, 52, -216, -292, 453, 548, -315, -383, 64, 88], [176, 206, -1356, -920, 2964, 1421, -2180, -843, 497, 152], [304, 480, -2226, -2572, 4704, 4636, -3291, -3092, 677, 649]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 2, -16, -8, 37, 11, -31, -6, 10, 1], [2, 4, -14, -24, 29, 48, -20, -37, 4, 11], [22, 24, -172, -102, 383, 150, -293, -86, 73, 15], [30, 52, -216, -292, 453, 548, -315, -383, 64, 88], [176, 206, -1356, -920, 2964, 1421, -2180, -843, 497, 152], [304, 480, -2226, -2572, 4704, 4636, -3291, -3092, 677, 649], [1298, 1602, -9904, -7418, 21441, 11843, -15483, -7185, 3398, 1326]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 2, -16, -8, 37, 11, -31, -6, 10, 1], [2, 4, -14, -24, 29, 48, -20, -37, 4, 11], [22, 24, -172, -102, 383, 150, -293, -86, 73, 15], [30, 52, -216, -292, 453, 548, -315, -383, 64, 88], [176, 206, -1356, -920, 2964, 1421, -2180, -843, 497, 152], [304, 480, -2226, -2572, 4704, 4636, -3291, -3092, 677, 649], [1298, 1602, -9904, -7418, 21441, 11843, -15483, -7185, 3398, 1326], [2652, 3950, -19614, -20512, 41644, 36027, -29263, -23439, 6075, 4724]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 2, -16, -8, 37, 11, -31, -6, 10, 1], [2, 4, -14, -24, 29, 48, -20, -37, 4, 11], [22, 24, -172, -102, 383, 150, -293, -86, 73, 15], [30, 52, -216, -292, 453, 548, -315, -383, 64, 88], [176, 206, -1356, -920, 2964, 1421, -2180, -843, 497, 152], [304, 480, -2226, -2572, 4704, 4636, -3291, -3092, 677, 649], [1298, 1602, -9904, -7418, 21441, 11843, -15483, -7185, 3398, 1326], [2652, 3950, -19614, -20512, 41644, 36027, -29263, -23439, 6075, 4724], [9448, 12100, -71634, -57406, 154276, 93608, -110417, -57607, 23801, 10799]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp4111 : Fact (Nat.Prime 4111) := fact_iff.2 (by norm_num)
instance hp4421 : Fact (Nat.Prime 4421) := fact_iff.2 (by norm_num)
instance hp3863 : Fact (Nat.Prime 3863) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 4
  a' := [1]
  b' := [1, 1]
  k := [1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1]
  f := [1, 1, -8, -4, 19, 6, -15, -3, 5, 1]
  g := [0, 1, 1, 1, 0, 0, 1, 1]
  h := [0, 0, 0, 1]
  a := [1, 1, 1, 1, 1, 1]
  b := [0, 0, 0, 1, 0, 0, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD4111 : CertificateDedekindCriterionLists l 4111 where
  n := 2
  a' := [3775, 2017, 846, 758, 1433, 2730, 2010, 136]
  b' := [631, 3865, 1389, 44, 3019, 976, 1333, 2470, 1812]
  k := [921, 19, 4056, 3845, 1729, 395, 1943, 3322, 1]
  f := [106, 18, 289, 195, 254, 110, 124, 337, 357, 1]
  g := [1106, 185, 3015, 2027, 2645, 1141, 1291, 3513, 3716, 1]
  h := [394, 1]
  a := [3036, 380, 2442, 2395, 1455, 758, 774, 2190, 3729]
  b := [1824, 687, 1369, 67, 2700, 3179, 1939, 1415, 382]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD4421 : CertificateDedekindCriterionLists l 4421 where
  n := 2
  a' := [3048, 1708, 4026, 123, 1917, 717, 1689, 3922]
  b' := [1328, 3392, 4169, 2959, 3003, 3899, 3765, 2899, 3494]
  k := [2595, 3822, 1309, 4122, 2687, 1188, 657, 3661, 1]
  f := [662, 1732, 1890, 337, 221, 1518, 430, 2357, 1073, 1]
  g := [1130, 2956, 3225, 574, 377, 2591, 733, 4023, 1830, 1]
  h := [2590, 1]
  a := [2346, 2154, 1151, 2061, 3491, 4267, 1746, 1532, 2476]
  b := [4146, 1652, 3419, 21, 2618, 3971, 768, 2717, 1945]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3863 : CertificateDedekindCriterionLists l 3863 where
  n := 2
  a' := [92, 919, 510, 2684, 1948, 2257, 378, 3733]
  b' := [857, 1913, 2267, 1862, 2478, 2653, 2232, 2444, 3019]
  k := [1441, 1173, 581, 919, 1534, 1537, 483, 900, 1]
  f := [669, 117, 71, 707, 510, 968, 846, 249, 913, 1]
  g := [1745, 304, 185, 1844, 1329, 2524, 2205, 648, 2381, 1]
  h := [1481, 1]
  a := [2852, 1859, 2721, 2081, 1058, 1696, 1123, 1490, 1622]
  b := [1096, 1845, 3410, 1643, 1427, 1495, 1239, 3861, 2241]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![2, 4111, 4421, 3863]
  exp := ![2, 1, 1, 1]
  pdgood := [2, 4111, 4421, 3863]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp4111.out
    exact hp4421.out
    exact hp3863.out
  a := [-215404483688, 498297039978, 12812919883759, 8365617891486, -25570861764718, -11633273218394, 14912842126435, 2769358286930, -2220331705200]
  b := [74986511982, 916891635422, 535651517295, -4029657375057, -2272035842661, 4759538447858, 1695640401844, -1927639956161, -299139145745, 222033170520]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 4111 T_ofList CD4111
    exact satisfiesDedekindCriterion_of_certificate_lists T l 4421 T_ofList CD4421
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3863 T_ofList CD3863

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

end VoightMaximalOrderD10R341

namespace VoightMaximalOrderD10R342

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4513369292693, [1, -28, -40, 131, 2, -107, 22, 31, -9, -3, 1], 1⟩
local notation "l" => [1, -28, -40, 131, 2, -107, 22, 31, -9, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 28, 40, -131, -2, 107, -22, -31, 9, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 28, 40, -131, -2, 107, -22, -31, 9, 3], ![-3, 83, 148, -353, -137, 319, 41, -115, -4, 18]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 28, 40, -131, -2, 107, -22, -31, 9, 3], ![-3, 83, 148, -353, -137, 319, 41, -115, -4, 18], ![-18, 501, 803, -2210, -389, 1789, -77, -517, 47, 50]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 28, 40, -131, -2, 107, -22, -31, 9, 3], ![-3, 83, 148, -353, -137, 319, 41, -115, -4, 18], ![-18, 501, 803, -2210, -389, 1789, -77, -517, 47, 50], ![-50, 1382, 2501, -5747, -2310, 4961, 689, -1627, -67, 197]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 28, 40, -131, -2, 107, -22, -31, 9, 3], ![-3, 83, 148, -353, -137, 319, 41, -115, -4, 18], ![-18, 501, 803, -2210, -389, 1789, -77, -517, 47, 50], ![-50, 1382, 2501, -5747, -2310, 4961, 689, -1627, -67, 197], ![-197, 5466, 9262, -23306, -6141, 18769, 627, -5418, 146, 524]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 28, 40, -131, -2, 107, -22, -31, 9, 3], ![-3, 83, 148, -353, -137, 319, 41, -115, -4, 18], ![-18, 501, 803, -2210, -389, 1789, -77, -517, 47, 50], ![-50, 1382, 2501, -5747, -2310, 4961, 689, -1627, -67, 197], ![-197, 5466, 9262, -23306, -6141, 18769, 627, -5418, 146, 524], ![-524, 14475, 26426, -59382, -24354, 49927, 7241, -15617, -702, 1718]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 28, 40, -131, -2, 107, -22, -31, 9, 3], ![-3, 83, 148, -353, -137, 319, 41, -115, -4, 18], ![-18, 501, 803, -2210, -389, 1789, -77, -517, 47, 50], ![-50, 1382, 2501, -5747, -2310, 4961, 689, -1627, -67, 197], ![-197, 5466, 9262, -23306, -6141, 18769, 627, -5418, 146, 524], ![-524, 14475, 26426, -59382, -24354, 49927, 7241, -15617, -702, 1718], ![-1718, 47580, 83195, -198632, -62818, 159472, 12131, -46017, -155, 4452]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 28, 40, -131, -2, 107, -22, -31, 9, 3], ![-3, 83, 148, -353, -137, 319, 41, -115, -4, 18], ![-18, 501, 803, -2210, -389, 1789, -77, -517, 47, 50], ![-50, 1382, 2501, -5747, -2310, 4961, 689, -1627, -67, 197], ![-197, 5466, 9262, -23306, -6141, 18769, 627, -5418, 146, 524], ![-524, 14475, 26426, -59382, -24354, 49927, 7241, -15617, -702, 1718], ![-1718, 47580, 83195, -198632, -62818, 159472, 12131, -46017, -155, 4452], ![-4452, 122938, 225660, -500017, -207536, 413546, 61528, -125881, -5949, 13201]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 28, 40, -131, -2, 107, -22, -31, 9, 3], ![-3, 83, 148, -353, -137, 319, 41, -115, -4, 18], ![-18, 501, 803, -2210, -389, 1789, -77, -517, 47, 50], ![-50, 1382, 2501, -5747, -2310, 4961, 689, -1627, -67, 197], ![-197, 5466, 9262, -23306, -6141, 18769, 627, -5418, 146, 524], ![-524, 14475, 26426, -59382, -24354, 49927, 7241, -15617, -702, 1718], ![-1718, 47580, 83195, -198632, -62818, 159472, 12131, -46017, -155, 4452], ![-4452, 122938, 225660, -500017, -207536, 413546, 61528, -125881, -5949, 13201], ![-13201, 365176, 650978, -1503671, -526419, 1204971, 123124, -347703, -7072, 33654]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-18, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-18, -3, -1], [-50, -18, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-18, -3, -1], [-50, -18, -3, -1], [-197, -50, -18, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-18, -3, -1], [-50, -18, -3, -1], [-197, -50, -18, -3, -1], [-524, -197, -50, -18, -3, -1]], ![[], [], [], [-1], [-3, -1], [-18, -3, -1], [-50, -18, -3, -1], [-197, -50, -18, -3, -1], [-524, -197, -50, -18, -3, -1], [-1718, -524, -197, -50, -18, -3, -1]], ![[], [], [-1], [-3, -1], [-18, -3, -1], [-50, -18, -3, -1], [-197, -50, -18, -3, -1], [-524, -197, -50, -18, -3, -1], [-1718, -524, -197, -50, -18, -3, -1], [-4452, -1718, -524, -197, -50, -18, -3, -1]], ![[], [-1], [-3, -1], [-18, -3, -1], [-50, -18, -3, -1], [-197, -50, -18, -3, -1], [-524, -197, -50, -18, -3, -1], [-1718, -524, -197, -50, -18, -3, -1], [-4452, -1718, -524, -197, -50, -18, -3, -1], [-13201, -4452, -1718, -524, -197, -50, -18, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 28, 40, -131, -2, 107, -22, -31, 9, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 28, 40, -131, -2, 107, -22, -31, 9, 3], [-3, 83, 148, -353, -137, 319, 41, -115, -4, 18]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 28, 40, -131, -2, 107, -22, -31, 9, 3], [-3, 83, 148, -353, -137, 319, 41, -115, -4, 18], [-18, 501, 803, -2210, -389, 1789, -77, -517, 47, 50]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 28, 40, -131, -2, 107, -22, -31, 9, 3], [-3, 83, 148, -353, -137, 319, 41, -115, -4, 18], [-18, 501, 803, -2210, -389, 1789, -77, -517, 47, 50], [-50, 1382, 2501, -5747, -2310, 4961, 689, -1627, -67, 197]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 28, 40, -131, -2, 107, -22, -31, 9, 3], [-3, 83, 148, -353, -137, 319, 41, -115, -4, 18], [-18, 501, 803, -2210, -389, 1789, -77, -517, 47, 50], [-50, 1382, 2501, -5747, -2310, 4961, 689, -1627, -67, 197], [-197, 5466, 9262, -23306, -6141, 18769, 627, -5418, 146, 524]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 28, 40, -131, -2, 107, -22, -31, 9, 3], [-3, 83, 148, -353, -137, 319, 41, -115, -4, 18], [-18, 501, 803, -2210, -389, 1789, -77, -517, 47, 50], [-50, 1382, 2501, -5747, -2310, 4961, 689, -1627, -67, 197], [-197, 5466, 9262, -23306, -6141, 18769, 627, -5418, 146, 524], [-524, 14475, 26426, -59382, -24354, 49927, 7241, -15617, -702, 1718]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 28, 40, -131, -2, 107, -22, -31, 9, 3], [-3, 83, 148, -353, -137, 319, 41, -115, -4, 18], [-18, 501, 803, -2210, -389, 1789, -77, -517, 47, 50], [-50, 1382, 2501, -5747, -2310, 4961, 689, -1627, -67, 197], [-197, 5466, 9262, -23306, -6141, 18769, 627, -5418, 146, 524], [-524, 14475, 26426, -59382, -24354, 49927, 7241, -15617, -702, 1718], [-1718, 47580, 83195, -198632, -62818, 159472, 12131, -46017, -155, 4452]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 28, 40, -131, -2, 107, -22, -31, 9, 3], [-3, 83, 148, -353, -137, 319, 41, -115, -4, 18], [-18, 501, 803, -2210, -389, 1789, -77, -517, 47, 50], [-50, 1382, 2501, -5747, -2310, 4961, 689, -1627, -67, 197], [-197, 5466, 9262, -23306, -6141, 18769, 627, -5418, 146, 524], [-524, 14475, 26426, -59382, -24354, 49927, 7241, -15617, -702, 1718], [-1718, 47580, 83195, -198632, -62818, 159472, 12131, -46017, -155, 4452], [-4452, 122938, 225660, -500017, -207536, 413546, 61528, -125881, -5949, 13201]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 28, 40, -131, -2, 107, -22, -31, 9, 3], [-3, 83, 148, -353, -137, 319, 41, -115, -4, 18], [-18, 501, 803, -2210, -389, 1789, -77, -517, 47, 50], [-50, 1382, 2501, -5747, -2310, 4961, 689, -1627, -67, 197], [-197, 5466, 9262, -23306, -6141, 18769, 627, -5418, 146, 524], [-524, 14475, 26426, -59382, -24354, 49927, 7241, -15617, -702, 1718], [-1718, 47580, 83195, -198632, -62818, 159472, 12131, -46017, -155, 4452], [-4452, 122938, 225660, -500017, -207536, 413546, 61528, -125881, -5949, 13201], [-13201, 365176, 650978, -1503671, -526419, 1204971, 123124, -347703, -7072, 33654]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp12502408013 : Fact (Nat.Prime 12502408013) := fact_iff.2 (by norm_num)

def CD19 : CertificateDedekindCriterionLists l 19 where
  n := 2
  a' := [8, 6, 5, 2, 1, 13, 18]
  b' := [1, 9, 11, 16, 3, 10, 14, 12]
  k := [4, 14, 9, 3, 5, 8, 1]
  f := [1, 4, 12, -1, 9, 13, 6, 7, 4, 1]
  g := [2, 4, 17, 4, 14, 8, 9, 12, 1]
  h := [10, 4, 1]
  a := [18, 10, 6, 0, 13, 2, 17, 16]
  b := [1, 14, 13, 18, 4, 0, 17, 16, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD12502408013 : CertificateDedekindCriterionLists l 12502408013 where
  n := 2
  a' := [3620078089, 936956281, 4282438750, 7800873101, 1823248231, 12322459521, 10045731331, 11798089152]
  b' := [4402142605, 2143904403, 8223125865, 2490784020, 583655768, 1433886607, 8624238957, 5301979868, 2856570543]
  k := [7480132291, 10454009174, 9565516490, 3652662914, 12122664810, 9533748992, 7548910801, 11666230044, 1]
  f := [342123174, 204546036, 94472633, 408241212, 272651056, 306306189, 205002901, 237491068, 404107805, 1]
  g := [10230749161, 6116683513, 2825081372, 12207923205, 8153275675, 9159688725, 6130345470, 7101861915, 12084319027, 1]
  h := [418088983, 1]
  a := [1330847833, 4510587730, 8644092223, 6752268868, 11802591614, 3732594139, 9275559957, 7856570077, 4768413908]
  b := [7482032317, 1076758375, 2922659217, 1829270223, 10707617954, 3185755304, 3760468704, 9433560988, 7733994105]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![19, 12502408013]
  exp := ![1, 1]
  pdgood := [19, 12502408013]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp19.out
    exact hp12502408013.out
  a := [-238809765181, -1487471748728, 2052140880939, 7526323837536, -3679556827683, -7015773089042, 2802180883518, 1546668808244, -617370602320]
  b := [-17012697051, 234293480015, 993724003940, -331268370145, -2279554793127, 675001412875, 1195064840963, -394951751310, -173187998894, 61737060232]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19 T_ofList CD19
    exact satisfiesDedekindCriterion_of_certificate_lists T l 12502408013 T_ofList CD12502408013

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

end VoightMaximalOrderD10R342

namespace VoightMaximalOrderD10R345

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4536939940625, [-1, -14, 11, 52, -27, -56, 26, 21, -10, -2, 1], 1⟩
local notation "l" => [-1, -14, 11, 52, -27, -56, 26, 21, -10, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -11, -52, 27, 56, -26, -21, 10, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -11, -52, 27, 56, -26, -21, 10, 2], ![2, 29, -8, -115, 2, 139, 4, -68, -1, 14]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -11, -52, 27, 56, -26, -21, 10, 2], ![2, 29, -8, -115, 2, 139, 4, -68, -1, 14], ![14, 198, -125, -736, 263, 786, -225, -290, 72, 27]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -11, -52, 27, 56, -26, -21, 10, 2], ![2, 29, -8, -115, 2, 139, 4, -68, -1, 14], ![14, 198, -125, -736, 263, 786, -225, -290, 72, 27], ![27, 392, -99, -1529, -7, 1775, 84, -792, -20, 126]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -11, -52, 27, 56, -26, -21, 10, 2], ![2, 29, -8, -115, 2, 139, 4, -68, -1, 14], ![14, 198, -125, -736, 263, 786, -225, -290, 72, 27], ![27, 392, -99, -1529, -7, 1775, 84, -792, -20, 126], ![126, 1791, -994, -6651, 1873, 7049, -1501, -2562, 468, 232]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -11, -52, 27, 56, -26, -21, 10, 2], ![2, 29, -8, -115, 2, 139, 4, -68, -1, 14], ![14, 198, -125, -736, 263, 786, -225, -290, 72, 27], ![27, 392, -99, -1529, -7, 1775, 84, -792, -20, 126], ![126, 1791, -994, -6651, 1873, 7049, -1501, -2562, 468, 232], ![232, 3374, -761, -13058, -387, 14865, 1017, -6373, -242, 932]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -11, -52, 27, 56, -26, -21, 10, 2], ![2, 29, -8, -115, 2, 139, 4, -68, -1, 14], ![14, 198, -125, -736, 263, 786, -225, -290, 72, 27], ![27, 392, -99, -1529, -7, 1775, 84, -792, -20, 126], ![126, 1791, -994, -6651, 1873, 7049, -1501, -2562, 468, 232], ![232, 3374, -761, -13058, -387, 14865, 1017, -6373, -242, 932], ![932, 13280, -6878, -49225, 12106, 51805, -9367, -18555, 2947, 1622]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -11, -52, 27, 56, -26, -21, 10, 2], ![2, 29, -8, -115, 2, 139, 4, -68, -1, 14], ![14, 198, -125, -736, 263, 786, -225, -290, 72, 27], ![27, 392, -99, -1529, -7, 1775, 84, -792, -20, 126], ![126, 1791, -994, -6651, 1873, 7049, -1501, -2562, 468, 232], ![232, 3374, -761, -13058, -387, 14865, 1017, -6373, -242, 932], ![932, 13280, -6878, -49225, 12106, 51805, -9367, -18555, 2947, 1622], ![1622, 23640, -4562, -91222, -5431, 102938, 9633, -43429, -2335, 6191]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -11, -52, 27, 56, -26, -21, 10, 2], ![2, 29, -8, -115, 2, 139, 4, -68, -1, 14], ![14, 198, -125, -736, 263, 786, -225, -290, 72, 27], ![27, 392, -99, -1529, -7, 1775, 84, -792, -20, 126], ![126, 1791, -994, -6651, 1873, 7049, -1501, -2562, 468, 232], ![232, 3374, -761, -13058, -387, 14865, 1017, -6373, -242, 932], ![932, 13280, -6878, -49225, 12106, 51805, -9367, -18555, 2947, 1622], ![1622, 23640, -4562, -91222, -5431, 102938, 9633, -43429, -2335, 6191], ![6191, 88296, -44461, -326494, 75935, 341265, -58028, -120378, 18481, 10047]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-27, -14, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-27, -14, -2, -1], [-126, -27, -14, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-27, -14, -2, -1], [-126, -27, -14, -2, -1], [-232, -126, -27, -14, -2, -1]], ![[], [], [], [-1], [-2, -1], [-14, -2, -1], [-27, -14, -2, -1], [-126, -27, -14, -2, -1], [-232, -126, -27, -14, -2, -1], [-932, -232, -126, -27, -14, -2, -1]], ![[], [], [-1], [-2, -1], [-14, -2, -1], [-27, -14, -2, -1], [-126, -27, -14, -2, -1], [-232, -126, -27, -14, -2, -1], [-932, -232, -126, -27, -14, -2, -1], [-1622, -932, -232, -126, -27, -14, -2, -1]], ![[], [-1], [-2, -1], [-14, -2, -1], [-27, -14, -2, -1], [-126, -27, -14, -2, -1], [-232, -126, -27, -14, -2, -1], [-932, -232, -126, -27, -14, -2, -1], [-1622, -932, -232, -126, -27, -14, -2, -1], [-6191, -1622, -932, -232, -126, -27, -14, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -11, -52, 27, 56, -26, -21, 10, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -11, -52, 27, 56, -26, -21, 10, 2], [2, 29, -8, -115, 2, 139, 4, -68, -1, 14]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -11, -52, 27, 56, -26, -21, 10, 2], [2, 29, -8, -115, 2, 139, 4, -68, -1, 14], [14, 198, -125, -736, 263, 786, -225, -290, 72, 27]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -11, -52, 27, 56, -26, -21, 10, 2], [2, 29, -8, -115, 2, 139, 4, -68, -1, 14], [14, 198, -125, -736, 263, 786, -225, -290, 72, 27], [27, 392, -99, -1529, -7, 1775, 84, -792, -20, 126]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -11, -52, 27, 56, -26, -21, 10, 2], [2, 29, -8, -115, 2, 139, 4, -68, -1, 14], [14, 198, -125, -736, 263, 786, -225, -290, 72, 27], [27, 392, -99, -1529, -7, 1775, 84, -792, -20, 126], [126, 1791, -994, -6651, 1873, 7049, -1501, -2562, 468, 232]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -11, -52, 27, 56, -26, -21, 10, 2], [2, 29, -8, -115, 2, 139, 4, -68, -1, 14], [14, 198, -125, -736, 263, 786, -225, -290, 72, 27], [27, 392, -99, -1529, -7, 1775, 84, -792, -20, 126], [126, 1791, -994, -6651, 1873, 7049, -1501, -2562, 468, 232], [232, 3374, -761, -13058, -387, 14865, 1017, -6373, -242, 932]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -11, -52, 27, 56, -26, -21, 10, 2], [2, 29, -8, -115, 2, 139, 4, -68, -1, 14], [14, 198, -125, -736, 263, 786, -225, -290, 72, 27], [27, 392, -99, -1529, -7, 1775, 84, -792, -20, 126], [126, 1791, -994, -6651, 1873, 7049, -1501, -2562, 468, 232], [232, 3374, -761, -13058, -387, 14865, 1017, -6373, -242, 932], [932, 13280, -6878, -49225, 12106, 51805, -9367, -18555, 2947, 1622]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -11, -52, 27, 56, -26, -21, 10, 2], [2, 29, -8, -115, 2, 139, 4, -68, -1, 14], [14, 198, -125, -736, 263, 786, -225, -290, 72, 27], [27, 392, -99, -1529, -7, 1775, 84, -792, -20, 126], [126, 1791, -994, -6651, 1873, 7049, -1501, -2562, 468, 232], [232, 3374, -761, -13058, -387, 14865, 1017, -6373, -242, 932], [932, 13280, -6878, -49225, 12106, 51805, -9367, -18555, 2947, 1622], [1622, 23640, -4562, -91222, -5431, 102938, 9633, -43429, -2335, 6191]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -11, -52, 27, 56, -26, -21, 10, 2], [2, 29, -8, -115, 2, 139, 4, -68, -1, 14], [14, 198, -125, -736, 263, 786, -225, -290, 72, 27], [27, 392, -99, -1529, -7, 1775, 84, -792, -20, 126], [126, 1791, -994, -6651, 1873, 7049, -1501, -2562, 468, 232], [232, 3374, -761, -13058, -387, 14865, 1017, -6373, -242, 932], [932, 13280, -6878, -49225, 12106, 51805, -9367, -18555, 2947, 1622], [1622, 23640, -4562, -91222, -5431, 102938, 9633, -43429, -2335, 6191], [6191, 88296, -44461, -326494, 75935, 341265, -58028, -120378, 18481, 10047]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp10181 : Fact (Nat.Prime 10181) := fact_iff.2 (by norm_num)
instance hp142601 : Fact (Nat.Prime 142601) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 3, 1]
  b' := [3, 0, 1, 4, 4]
  k := [1]
  f := [2, 4, -2, -8, 11, 14, -4, -1, 6, 2]
  g := [3, 1, 0, 2, 4, 1]
  h := [3, 1, 0, 2, 4, 1]
  a := [4, 4, 1, 2, 1]
  b := [1, 0, 0, 0, 2, 0, 4, 3, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD10181 : CertificateDedekindCriterionLists l 10181 where
  n := 2
  a' := [373, 4264, 7264, 6627, 6514, 2403, 2434, 8375]
  b' := [7231, 8556, 10172, 4204, 5239, 5144, 7722, 7636, 6988]
  k := [5654, 1082, 7276, 5712, 2012, 8948, 39, 7476, 1]
  f := [3563, 1211, 6284, 6231, 4179, 131, 3582, 2722, 2365, 1]
  g := [5631, 1913, 9931, 9846, 6603, 206, 5661, 4301, 3737, 1]
  h := [6442, 1]
  a := [5997, 8459, 1035, 368, 5302, 9925, 4314, 4001, 4369]
  b := [1653, 3583, 451, 6815, 5360, 6919, 6451, 3839, 5812]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD142601 : CertificateDedekindCriterionLists l 142601 where
  n := 2
  a' := [56269, 61320, 22297, 119776, 54190, 104216, 103040, 29147]
  b' := [136413, 63776, 136339, 115679, 51420, 80952, 54645, 17539, 12606]
  k := [108447, 28234, 133895, 139791, 13835, 80999, 37347, 102441, 1]
  f := [18677, 5261, 6940, 5534, 480, 3992, 4612, 10330, 17252, 1]
  g := [132644, 37357, 49286, 39300, 3407, 28351, 32753, 73362, 122520, 1]
  h := [20079, 1]
  a := [29457, 135603, 111123, 30376, 101586, 95775, 103764, 23899, 2141]
  b := [36937, 105487, 133609, 120278, 60133, 53821, 99395, 45309, 140460]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 10181, 142601]
  exp := ![1, 1, 1]
  pdgood := [5, 10181, 142601]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp10181.out
    exact hp142601.out
  a := [-324185116119, 326136781622, 3792960953253, -452232230198, -6754896668792, 13864644366, 3436871960828, -35576424916, -439226563080]
  b := [22637572301, 336462959619, -70804698764, -1245263002603, -42643556477, 1280880754154, 78807979151, -448056193468, -5226888770, 43922656308]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 10181 T_ofList CD10181
    exact satisfiesDedekindCriterion_of_certificate_lists T l 142601 T_ofList CD142601

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

end VoightMaximalOrderD10R345

namespace VoightMaximalOrderD10R349

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4568883229493, [-1, -2, 10, 19, -19, -33, 15, 18, -6, -3, 1], 1⟩
local notation "l" => [-1, -2, 10, 19, -19, -33, 15, 18, -6, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -19, 19, 33, -15, -18, 6, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -19, 19, 33, -15, -18, 6, 3], ![3, 7, -28, -67, 38, 118, -12, -69, 0, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -19, 19, 33, -15, -18, 6, 3], ![3, 7, -28, -67, 38, 118, -12, -69, 0, 15], ![15, 33, -143, -313, 218, 533, -107, -282, 21, 45]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -19, 19, 33, -15, -18, 6, 3], ![3, 7, -28, -67, 38, 118, -12, -69, 0, 15], ![15, 33, -143, -313, 218, 533, -107, -282, 21, 45], ![45, 105, -417, -998, 542, 1703, -142, -917, -12, 156]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -19, 19, 33, -15, -18, 6, 3], ![3, 7, -28, -67, 38, 118, -12, -69, 0, 15], ![15, 33, -143, -313, 218, 533, -107, -282, 21, 45], ![45, 105, -417, -998, 542, 1703, -142, -917, -12, 156], ![156, 357, -1455, -3381, 1966, 5690, -637, -2950, 19, 456]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -19, 19, 33, -15, -18, 6, 3], ![3, 7, -28, -67, 38, 118, -12, -69, 0, 15], ![15, 33, -143, -313, 218, 533, -107, -282, 21, 45], ![45, 105, -417, -998, 542, 1703, -142, -917, -12, 156], ![156, 357, -1455, -3381, 1966, 5690, -637, -2950, 19, 456], ![456, 1068, -4203, -10119, 5283, 17014, -1150, -8845, -214, 1387]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -19, 19, 33, -15, -18, 6, 3], ![3, 7, -28, -67, 38, 118, -12, -69, 0, 15], ![15, 33, -143, -313, 218, 533, -107, -282, 21, 45], ![45, 105, -417, -998, 542, 1703, -142, -917, -12, 156], ![156, 357, -1455, -3381, 1966, 5690, -637, -2950, 19, 456], ![456, 1068, -4203, -10119, 5283, 17014, -1150, -8845, -214, 1387], ![1387, 3230, -12802, -30556, 16234, 51054, -3791, -26116, -523, 3947]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -19, 19, 33, -15, -18, 6, 3], ![3, 7, -28, -67, 38, 118, -12, -69, 0, 15], ![15, 33, -143, -313, 218, 533, -107, -282, 21, 45], ![45, 105, -417, -998, 542, 1703, -142, -917, -12, 156], ![156, 357, -1455, -3381, 1966, 5690, -637, -2950, 19, 456], ![456, 1068, -4203, -10119, 5283, 17014, -1150, -8845, -214, 1387], ![1387, 3230, -12802, -30556, 16234, 51054, -3791, -26116, -523, 3947], ![3947, 9281, -36240, -87795, 44437, 146485, -8151, -74837, -2434, 11318]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -19, 19, 33, -15, -18, 6, 3], ![3, 7, -28, -67, 38, 118, -12, -69, 0, 15], ![15, 33, -143, -313, 218, 533, -107, -282, 21, 45], ![45, 105, -417, -998, 542, 1703, -142, -917, -12, 156], ![156, 357, -1455, -3381, 1966, 5690, -637, -2950, 19, 456], ![456, 1068, -4203, -10119, 5283, 17014, -1150, -8845, -214, 1387], ![1387, 3230, -12802, -30556, 16234, 51054, -3791, -26116, -523, 3947], ![3947, 9281, -36240, -87795, 44437, 146485, -8151, -74837, -2434, 11318], ![11318, 26583, -103899, -251282, 127247, 417931, -23285, -211875, -6929, 31520]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-45, -15, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-45, -15, -3, -1], [-156, -45, -15, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-45, -15, -3, -1], [-156, -45, -15, -3, -1], [-456, -156, -45, -15, -3, -1]], ![[], [], [], [-1], [-3, -1], [-15, -3, -1], [-45, -15, -3, -1], [-156, -45, -15, -3, -1], [-456, -156, -45, -15, -3, -1], [-1387, -456, -156, -45, -15, -3, -1]], ![[], [], [-1], [-3, -1], [-15, -3, -1], [-45, -15, -3, -1], [-156, -45, -15, -3, -1], [-456, -156, -45, -15, -3, -1], [-1387, -456, -156, -45, -15, -3, -1], [-3947, -1387, -456, -156, -45, -15, -3, -1]], ![[], [-1], [-3, -1], [-15, -3, -1], [-45, -15, -3, -1], [-156, -45, -15, -3, -1], [-456, -156, -45, -15, -3, -1], [-1387, -456, -156, -45, -15, -3, -1], [-3947, -1387, -456, -156, -45, -15, -3, -1], [-11318, -3947, -1387, -456, -156, -45, -15, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -19, 19, 33, -15, -18, 6, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -19, 19, 33, -15, -18, 6, 3], [3, 7, -28, -67, 38, 118, -12, -69, 0, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -19, 19, 33, -15, -18, 6, 3], [3, 7, -28, -67, 38, 118, -12, -69, 0, 15], [15, 33, -143, -313, 218, 533, -107, -282, 21, 45]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -19, 19, 33, -15, -18, 6, 3], [3, 7, -28, -67, 38, 118, -12, -69, 0, 15], [15, 33, -143, -313, 218, 533, -107, -282, 21, 45], [45, 105, -417, -998, 542, 1703, -142, -917, -12, 156]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -19, 19, 33, -15, -18, 6, 3], [3, 7, -28, -67, 38, 118, -12, -69, 0, 15], [15, 33, -143, -313, 218, 533, -107, -282, 21, 45], [45, 105, -417, -998, 542, 1703, -142, -917, -12, 156], [156, 357, -1455, -3381, 1966, 5690, -637, -2950, 19, 456]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -19, 19, 33, -15, -18, 6, 3], [3, 7, -28, -67, 38, 118, -12, -69, 0, 15], [15, 33, -143, -313, 218, 533, -107, -282, 21, 45], [45, 105, -417, -998, 542, 1703, -142, -917, -12, 156], [156, 357, -1455, -3381, 1966, 5690, -637, -2950, 19, 456], [456, 1068, -4203, -10119, 5283, 17014, -1150, -8845, -214, 1387]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -19, 19, 33, -15, -18, 6, 3], [3, 7, -28, -67, 38, 118, -12, -69, 0, 15], [15, 33, -143, -313, 218, 533, -107, -282, 21, 45], [45, 105, -417, -998, 542, 1703, -142, -917, -12, 156], [156, 357, -1455, -3381, 1966, 5690, -637, -2950, 19, 456], [456, 1068, -4203, -10119, 5283, 17014, -1150, -8845, -214, 1387], [1387, 3230, -12802, -30556, 16234, 51054, -3791, -26116, -523, 3947]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -19, 19, 33, -15, -18, 6, 3], [3, 7, -28, -67, 38, 118, -12, -69, 0, 15], [15, 33, -143, -313, 218, 533, -107, -282, 21, 45], [45, 105, -417, -998, 542, 1703, -142, -917, -12, 156], [156, 357, -1455, -3381, 1966, 5690, -637, -2950, 19, 456], [456, 1068, -4203, -10119, 5283, 17014, -1150, -8845, -214, 1387], [1387, 3230, -12802, -30556, 16234, 51054, -3791, -26116, -523, 3947], [3947, 9281, -36240, -87795, 44437, 146485, -8151, -74837, -2434, 11318]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -19, 19, 33, -15, -18, 6, 3], [3, 7, -28, -67, 38, 118, -12, -69, 0, 15], [15, 33, -143, -313, 218, 533, -107, -282, 21, 45], [45, 105, -417, -998, 542, 1703, -142, -917, -12, 156], [156, 357, -1455, -3381, 1966, 5690, -637, -2950, 19, 456], [456, 1068, -4203, -10119, 5283, 17014, -1150, -8845, -214, 1387], [1387, 3230, -12802, -30556, 16234, 51054, -3791, -26116, -523, 3947], [3947, 9281, -36240, -87795, 44437, 146485, -8151, -74837, -2434, 11318], [11318, 26583, -103899, -251282, 127247, 417931, -23285, -211875, -6929, 31520]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp17 : Fact (Nat.Prime 17) := fact_iff.2 (by norm_num)
instance hp193 : Fact (Nat.Prime 193) := fact_iff.2 (by norm_num)
instance hp11508493 : Fact (Nat.Prime 11508493) := fact_iff.2 (by norm_num)

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [9, 7, 7, 3, 8, 5, 2]
  b' := [0, 6, 2, 8, 0, 3, 4, 8]
  k := [8, 0, 3, 10, 3, 4, 1]
  f := [1, 2, 1, 0, 4, 5, 0, 0, 2, 1]
  g := [5, 5, 3, 4, 7, 2, 2, 6, 1]
  h := [2, 2, 1]
  a := [2, 1, 6, 9, 2, 10, 3, 1]
  b := [2, 8, 2, 7, 0, 10, 2, 1, 10]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD17 : CertificateDedekindCriterionLists l 17 where
  n := 2
  a' := [2, 7, 2, 16, 3, 2, 14, 12]
  b' := [3, 8, 14, 10, 13, 15, 1, 8, 10]
  k := [4, 4, 6, 2, 13, 8, 1, 10, 1]
  f := [1, 2, 2, 1, 3, 4, 1, 0, 2, 1]
  g := [8, 12, 16, 10, 11, 12, 10, 4, 12, 1]
  h := [2, 1]
  a := [15, 16, 4, 14, 11, 0, 7, 3]
  b := [11, 16, 1, 10, 13, 11, 6, 14]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD193 : CertificateDedekindCriterionLists l 193 where
  n := 2
  a' := [143, 98, 166, 114, 145, 4, 63, 88]
  b' := [157, 81, 42, 3, 97, 21, 73, 151, 76]
  k := [129, 6, 7, 172, 123, 42, 129, 142, 1]
  f := [1, 10, 22, 11, 5, 21, 7, 8, 21, 1]
  g := [8, 80, 174, 82, 36, 166, 50, 63, 166, 1]
  h := [24, 1]
  a := [109, 42, 136, 33, 111, 169, 111, 170, 72]
  b := [83, 90, 110, 43, 55, 107, 35, 41, 121]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11508493 : CertificateDedekindCriterionLists l 11508493 where
  n := 2
  a' := [10650451, 8796093, 7324254, 9777844, 5587640, 8841501, 2748599, 9989529]
  b' := [2592093, 4192268, 939659, 4187776, 7124260, 10146808, 6872099, 1595668, 6562381]
  k := [3495620, 9167606, 9681162, 543703, 936375, 5932758, 978566, 5704538, 1]
  f := [2437069, 1090709, 2611767, 2105026, 2646669, 1318717, 703263, 1781337, 2170215, 1]
  g := [9664791, 4325469, 10357597, 8347990, 10496008, 5229690, 2788959, 7064325, 8606514, 1]
  h := [2901976, 1]
  a := [1106679, 9821150, 7350148, 10241322, 11110942, 8185328, 1498110, 9338063, 10175222]
  b := [1566215, 1042983, 69906, 10109960, 1617935, 5335353, 9430810, 2188837, 1333271]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![11, 17, 193, 11508493]
  exp := ![1, 1, 1, 1]
  pdgood := [11, 17, 193, 11508493]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp11.out
    exact hp17.out
    exact hp193.out
    exact hp11508493.out
  a := [1700219767065, -25397683885592, -3722834084264, 88570482247654, -10684981099202, -73206021707646, 16723163982648, 16635614927224, -5219412913920]
  b := [-1057786393964, 420758236091, 9820869895985, -1002547021330, -18124360466770, 2675657118416, 10400367816144, -2222349946146, -1820143880140, 521941291392]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 17 T_ofList CD17
    exact satisfiesDedekindCriterion_of_certificate_lists T l 193 T_ofList CD193
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11508493 T_ofList CD11508493

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

end VoightMaximalOrderD10R349

end TraceEuclidean
