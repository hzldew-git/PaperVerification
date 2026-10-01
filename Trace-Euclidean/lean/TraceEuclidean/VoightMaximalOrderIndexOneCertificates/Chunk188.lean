import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk184
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

namespace VoightMaximalOrderD10R215

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3303091095488, [-1, -7, -1, 31, 9, -46, -4, 27, -4, -4, 1], 1⟩
local notation "l" => [-1, -7, -1, 31, 9, -46, -4, 27, -4, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 1, -31, -9, 46, 4, -27, 4, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 1, -31, -9, 46, 4, -27, 4, 4], ![4, 29, 11, -123, -67, 175, 62, -104, -11, 20]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 1, -31, -9, 46, 4, -27, 4, 4], ![4, 29, 11, -123, -67, 175, 62, -104, -11, 20], ![20, 144, 49, -609, -303, 853, 255, -478, -24, 69]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 1, -31, -9, 46, 4, -27, 4, 4], ![4, 29, 11, -123, -67, 175, 62, -104, -11, 20], ![20, 144, 49, -609, -303, 853, 255, -478, -24, 69], ![69, 503, 213, -2090, -1230, 2871, 1129, -1608, -202, 252]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 1, -31, -9, 46, 4, -27, 4, 4], ![4, 29, 11, -123, -67, 175, 62, -104, -11, 20], ![20, 144, 49, -609, -303, 853, 255, -478, -24, 69], ![69, 503, 213, -2090, -1230, 2871, 1129, -1608, -202, 252], ![252, 1833, 755, -7599, -4358, 10362, 3879, -5675, -600, 806]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 1, -31, -9, 46, 4, -27, 4, 4], ![4, 29, 11, -123, -67, 175, 62, -104, -11, 20], ![20, 144, 49, -609, -303, 853, 255, -478, -24, 69], ![69, 503, 213, -2090, -1230, 2871, 1129, -1608, -202, 252], ![252, 1833, 755, -7599, -4358, 10362, 3879, -5675, -600, 806], ![806, 5894, 2639, -24231, -14853, 32718, 13586, -17883, -2451, 2624]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 1, -31, -9, 46, 4, -27, 4, 4], ![4, 29, 11, -123, -67, 175, 62, -104, -11, 20], ![20, 144, 49, -609, -303, 853, 255, -478, -24, 69], ![69, 503, 213, -2090, -1230, 2871, 1129, -1608, -202, 252], ![252, 1833, 755, -7599, -4358, 10362, 3879, -5675, -600, 806], ![806, 5894, 2639, -24231, -14853, 32718, 13586, -17883, -2451, 2624], ![2624, 19174, 8518, -78705, -47847, 105851, 43214, -57262, -7387, 8045]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 1, -31, -9, 46, 4, -27, 4, 4], ![4, 29, 11, -123, -67, 175, 62, -104, -11, 20], ![20, 144, 49, -609, -303, 853, 255, -478, -24, 69], ![69, 503, 213, -2090, -1230, 2871, 1129, -1608, -202, 252], ![252, 1833, 755, -7599, -4358, 10362, 3879, -5675, -600, 806], ![806, 5894, 2639, -24231, -14853, 32718, 13586, -17883, -2451, 2624], ![2624, 19174, 8518, -78705, -47847, 105851, 43214, -57262, -7387, 8045], ![8045, 58939, 27219, -240877, -151110, 322223, 138031, -174001, -25082, 24793]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, 1, -31, -9, 46, 4, -27, 4, 4], ![4, 29, 11, -123, -67, 175, 62, -104, -11, 20], ![20, 144, 49, -609, -303, 853, 255, -478, -24, 69], ![69, 503, 213, -2090, -1230, 2871, 1129, -1608, -202, 252], ![252, 1833, 755, -7599, -4358, 10362, 3879, -5675, -600, 806], ![806, 5894, 2639, -24231, -14853, 32718, 13586, -17883, -2451, 2624], ![2624, 19174, 8518, -78705, -47847, 105851, 43214, -57262, -7387, 8045], ![8045, 58939, 27219, -240877, -151110, 322223, 138031, -174001, -25082, 24793], ![24793, 181596, 83732, -741364, -464014, 989368, 421395, -531380, -74829, 74090]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1], [-252, -69, -20, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1], [-252, -69, -20, -4, -1], [-806, -252, -69, -20, -4, -1]], ![[], [], [], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1], [-252, -69, -20, -4, -1], [-806, -252, -69, -20, -4, -1], [-2624, -806, -252, -69, -20, -4, -1]], ![[], [], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1], [-252, -69, -20, -4, -1], [-806, -252, -69, -20, -4, -1], [-2624, -806, -252, -69, -20, -4, -1], [-8045, -2624, -806, -252, -69, -20, -4, -1]], ![[], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1], [-252, -69, -20, -4, -1], [-806, -252, -69, -20, -4, -1], [-2624, -806, -252, -69, -20, -4, -1], [-8045, -2624, -806, -252, -69, -20, -4, -1], [-24793, -8045, -2624, -806, -252, -69, -20, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 1, -31, -9, 46, 4, -27, 4, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 1, -31, -9, 46, 4, -27, 4, 4], [4, 29, 11, -123, -67, 175, 62, -104, -11, 20]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 1, -31, -9, 46, 4, -27, 4, 4], [4, 29, 11, -123, -67, 175, 62, -104, -11, 20], [20, 144, 49, -609, -303, 853, 255, -478, -24, 69]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 1, -31, -9, 46, 4, -27, 4, 4], [4, 29, 11, -123, -67, 175, 62, -104, -11, 20], [20, 144, 49, -609, -303, 853, 255, -478, -24, 69], [69, 503, 213, -2090, -1230, 2871, 1129, -1608, -202, 252]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 1, -31, -9, 46, 4, -27, 4, 4], [4, 29, 11, -123, -67, 175, 62, -104, -11, 20], [20, 144, 49, -609, -303, 853, 255, -478, -24, 69], [69, 503, 213, -2090, -1230, 2871, 1129, -1608, -202, 252], [252, 1833, 755, -7599, -4358, 10362, 3879, -5675, -600, 806]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 1, -31, -9, 46, 4, -27, 4, 4], [4, 29, 11, -123, -67, 175, 62, -104, -11, 20], [20, 144, 49, -609, -303, 853, 255, -478, -24, 69], [69, 503, 213, -2090, -1230, 2871, 1129, -1608, -202, 252], [252, 1833, 755, -7599, -4358, 10362, 3879, -5675, -600, 806], [806, 5894, 2639, -24231, -14853, 32718, 13586, -17883, -2451, 2624]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 1, -31, -9, 46, 4, -27, 4, 4], [4, 29, 11, -123, -67, 175, 62, -104, -11, 20], [20, 144, 49, -609, -303, 853, 255, -478, -24, 69], [69, 503, 213, -2090, -1230, 2871, 1129, -1608, -202, 252], [252, 1833, 755, -7599, -4358, 10362, 3879, -5675, -600, 806], [806, 5894, 2639, -24231, -14853, 32718, 13586, -17883, -2451, 2624], [2624, 19174, 8518, -78705, -47847, 105851, 43214, -57262, -7387, 8045]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 1, -31, -9, 46, 4, -27, 4, 4], [4, 29, 11, -123, -67, 175, 62, -104, -11, 20], [20, 144, 49, -609, -303, 853, 255, -478, -24, 69], [69, 503, 213, -2090, -1230, 2871, 1129, -1608, -202, 252], [252, 1833, 755, -7599, -4358, 10362, 3879, -5675, -600, 806], [806, 5894, 2639, -24231, -14853, 32718, 13586, -17883, -2451, 2624], [2624, 19174, 8518, -78705, -47847, 105851, 43214, -57262, -7387, 8045], [8045, 58939, 27219, -240877, -151110, 322223, 138031, -174001, -25082, 24793]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, 1, -31, -9, 46, 4, -27, 4, 4], [4, 29, 11, -123, -67, 175, 62, -104, -11, 20], [20, 144, 49, -609, -303, 853, 255, -478, -24, 69], [69, 503, 213, -2090, -1230, 2871, 1129, -1608, -202, 252], [252, 1833, 755, -7599, -4358, 10362, 3879, -5675, -600, 806], [806, 5894, 2639, -24231, -14853, 32718, 13586, -17883, -2451, 2624], [2624, 19174, 8518, -78705, -47847, 105851, 43214, -57262, -7387, 8045], [8045, 58939, 27219, -240877, -151110, 322223, 138031, -174001, -25082, 24793], [24793, 181596, 83732, -741364, -464014, 989368, 421395, -531380, -74829, 74090]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp109 : Fact (Nat.Prime 109) := fact_iff.2 (by norm_num)
instance hp397 : Fact (Nat.Prime 397) := fact_iff.2 (by norm_num)
instance hp1192679 : Fact (Nat.Prime 1192679) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 0, 0, 1]
  b' := [1, 1, 0, 0, 0, 1]
  k := [1, 1, 0, 0, 1]
  f := [1, 4, 1, -14, -4, 24, 3, -13, 3, 2]
  g := [1, 0, 1, 1, 0, 1, 0, 1]
  h := [1, 1, 0, 1]
  a := [0, 1, 1]
  b := [1, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD109 : CertificateDedekindCriterionLists l 109 where
  n := 2
  a' := [92, 79, 92, 53, 84, 72, 13, 6]
  b' := [95, 2, 74, 42, 47, 61, 91, 85, 72]
  k := [100, 100, 17, 40, 15, 8, 108, 68, 1]
  f := [71, 66, 23, 69, 31, 37, 30, 39, 22, 1]
  g := [106, 97, 33, 103, 45, 54, 44, 58, 32, 1]
  h := [73, 1]
  a := [8, 44, 85, 89, 74, 47, 26, 20, 9]
  b := [80, 98, 41, 56, 74, 32, 81, 70, 100]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD397 : CertificateDedekindCriterionLists l 397 where
  n := 2
  a' := [22, 76, 245, 106, 93, 257, 59, 255]
  b' := [212, 76, 378, 107, 322, 234, 234, 67, 104]
  k := [310, 43, 32, 327, 285, 267, 30, 32, 1]
  f := [358, 316, 250, 97, 342, 233, 119, 237, 14, 1]
  g := [375, 330, 261, 101, 358, 243, 124, 248, 14, 1]
  h := [379, 1]
  a := [34, 363, 362, 105, 355, 257, 20, 122, 111]
  b := [66, 95, 165, 309, 66, 29, 10, 275, 286]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1192679 : CertificateDedekindCriterionLists l 1192679 where
  n := 2
  a' := [456132, 278351, 687570, 754450, 668316, 797374, 567851, 1036486]
  b' := [1006615, 177242, 623764, 922039, 64858, 136294, 645064, 362869, 944994]
  k := [140248, 304928, 655000, 375007, 768065, 563818, 774465, 465642, 1]
  f := [165431, 85291, 607540, 375382, 250047, 642728, 71128, 597831, 187371, 1]
  g := [205558, 105979, 754905, 466434, 310698, 798628, 88380, 742841, 232819, 1]
  h := [959856, 1]
  a := [353684, 262023, 385351, 854325, 810302, 497000, 915295, 1051203, 1147111]
  b := [146801, 481108, 546642, 505482, 1163405, 1011255, 326710, 850435, 45568]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![2, 109, 397, 1192679]
  exp := ![1, 1, 1, 1]
  pdgood := [2, 109, 397, 1192679]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp109.out
    exact hp397.out
    exact hp1192679.out
  a := [418669436181, -1946706457641, -3003897169542, 15829540203718, 1627489423923, -21575465422359, 4806071933148, 4666011950322, -1423702379670]
  b := [-74555861845, -119266838848, 1359573066137, 518317970110, -3964621100758, -178329680817, 3217867520403, -612876048348, -523549290219, 142370237967]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 109 T_ofList CD109
    exact satisfiesDedekindCriterion_of_certificate_lists T l 397 T_ofList CD397
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1192679 T_ofList CD1192679

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

end VoightMaximalOrderD10R215

namespace VoightMaximalOrderD10R218

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3320687998525, [-1, -12, 36, 11, -65, -2, 42, 0, -11, 0, 1], 1⟩
local notation "l" => [-1, -12, 36, 11, -65, -2, 42, 0, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 12, -36, -11, 65, 2, -42, 0, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 12, -36, -11, 65, 2, -42, 0, 11, 0], ![0, 1, 12, -36, -11, 65, 2, -42, 0, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 12, -36, -11, 65, 2, -42, 0, 11, 0], ![0, 1, 12, -36, -11, 65, 2, -42, 0, 11], ![11, 132, -395, -109, 679, 11, -397, 2, 79, 0]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 12, -36, -11, 65, 2, -42, 0, 11, 0], ![0, 1, 12, -36, -11, 65, 2, -42, 0, 11], ![11, 132, -395, -109, 679, 11, -397, 2, 79, 0], ![0, 11, 132, -395, -109, 679, 11, -397, 2, 79]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 12, -36, -11, 65, 2, -42, 0, 11, 0], ![0, 1, 12, -36, -11, 65, 2, -42, 0, 11], ![11, 132, -395, -109, 679, 11, -397, 2, 79, 0], ![0, 11, 132, -395, -109, 679, 11, -397, 2, 79], ![79, 948, -2833, -737, 4740, 49, -2639, 11, 472, 2]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 12, -36, -11, 65, 2, -42, 0, 11, 0], ![0, 1, 12, -36, -11, 65, 2, -42, 0, 11], ![11, 132, -395, -109, 679, 11, -397, 2, 79, 0], ![0, 11, 132, -395, -109, 679, 11, -397, 2, 79], ![79, 948, -2833, -737, 4740, 49, -2639, 11, 472, 2], ![2, 103, 876, -2855, -607, 4744, -35, -2639, 33, 472]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 12, -36, -11, 65, 2, -42, 0, 11, 0], ![0, 1, 12, -36, -11, 65, 2, -42, 0, 11], ![11, 132, -395, -109, 679, 11, -397, 2, 79, 0], ![0, 11, 132, -395, -109, 679, 11, -397, 2, 79], ![79, 948, -2833, -737, 4740, 49, -2639, 11, 472, 2], ![2, 103, 876, -2855, -607, 4744, -35, -2639, 33, 472], ![472, 5666, -16889, -4316, 27825, 337, -15080, -35, 2553, 33]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 12, -36, -11, 65, 2, -42, 0, 11, 0], ![0, 1, 12, -36, -11, 65, 2, -42, 0, 11], ![11, 132, -395, -109, 679, 11, -397, 2, 79, 0], ![0, 11, 132, -395, -109, 679, 11, -397, 2, 79], ![79, 948, -2833, -737, 4740, 49, -2639, 11, 472, 2], ![2, 103, 876, -2855, -607, 4744, -35, -2639, 33, 472], ![472, 5666, -16889, -4316, 27825, 337, -15080, -35, 2553, 33], ![33, 868, 4478, -17252, -2171, 27891, -1049, -15080, 328, 2553]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 12, -36, -11, 65, 2, -42, 0, 11, 0], ![0, 1, 12, -36, -11, 65, 2, -42, 0, 11], ![11, 132, -395, -109, 679, 11, -397, 2, 79, 0], ![0, 11, 132, -395, -109, 679, 11, -397, 2, 79], ![79, 948, -2833, -737, 4740, 49, -2639, 11, 472, 2], ![2, 103, 876, -2855, -607, 4744, -35, -2639, 33, 472], ![472, 5666, -16889, -4316, 27825, 337, -15080, -35, 2553, 33], ![33, 868, 4478, -17252, -2171, 27891, -1049, -15080, 328, 2553], ![2553, 30669, -91040, -23605, 148693, 2935, -79335, -1049, 13003, 328]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [0, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [0, -11, 0, -1], [-79, 0, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [0, -11, 0, -1], [-79, 0, -11, 0, -1], [-2, -79, 0, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [0, -11, 0, -1], [-79, 0, -11, 0, -1], [-2, -79, 0, -11, 0, -1], [-472, -2, -79, 0, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [0, -11, 0, -1], [-79, 0, -11, 0, -1], [-2, -79, 0, -11, 0, -1], [-472, -2, -79, 0, -11, 0, -1], [-33, -472, -2, -79, 0, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [0, -11, 0, -1], [-79, 0, -11, 0, -1], [-2, -79, 0, -11, 0, -1], [-472, -2, -79, 0, -11, 0, -1], [-33, -472, -2, -79, 0, -11, 0, -1], [-2553, -33, -472, -2, -79, 0, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 12, -36, -11, 65, 2, -42, 0, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 12, -36, -11, 65, 2, -42, 0, 11, 0], [0, 1, 12, -36, -11, 65, 2, -42, 0, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 12, -36, -11, 65, 2, -42, 0, 11, 0], [0, 1, 12, -36, -11, 65, 2, -42, 0, 11], [11, 132, -395, -109, 679, 11, -397, 2, 79, 0]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 12, -36, -11, 65, 2, -42, 0, 11, 0], [0, 1, 12, -36, -11, 65, 2, -42, 0, 11], [11, 132, -395, -109, 679, 11, -397, 2, 79, 0], [0, 11, 132, -395, -109, 679, 11, -397, 2, 79]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 12, -36, -11, 65, 2, -42, 0, 11, 0], [0, 1, 12, -36, -11, 65, 2, -42, 0, 11], [11, 132, -395, -109, 679, 11, -397, 2, 79, 0], [0, 11, 132, -395, -109, 679, 11, -397, 2, 79], [79, 948, -2833, -737, 4740, 49, -2639, 11, 472, 2]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 12, -36, -11, 65, 2, -42, 0, 11, 0], [0, 1, 12, -36, -11, 65, 2, -42, 0, 11], [11, 132, -395, -109, 679, 11, -397, 2, 79, 0], [0, 11, 132, -395, -109, 679, 11, -397, 2, 79], [79, 948, -2833, -737, 4740, 49, -2639, 11, 472, 2], [2, 103, 876, -2855, -607, 4744, -35, -2639, 33, 472]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 12, -36, -11, 65, 2, -42, 0, 11, 0], [0, 1, 12, -36, -11, 65, 2, -42, 0, 11], [11, 132, -395, -109, 679, 11, -397, 2, 79, 0], [0, 11, 132, -395, -109, 679, 11, -397, 2, 79], [79, 948, -2833, -737, 4740, 49, -2639, 11, 472, 2], [2, 103, 876, -2855, -607, 4744, -35, -2639, 33, 472], [472, 5666, -16889, -4316, 27825, 337, -15080, -35, 2553, 33]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 12, -36, -11, 65, 2, -42, 0, 11, 0], [0, 1, 12, -36, -11, 65, 2, -42, 0, 11], [11, 132, -395, -109, 679, 11, -397, 2, 79, 0], [0, 11, 132, -395, -109, 679, 11, -397, 2, 79], [79, 948, -2833, -737, 4740, 49, -2639, 11, 472, 2], [2, 103, 876, -2855, -607, 4744, -35, -2639, 33, 472], [472, 5666, -16889, -4316, 27825, 337, -15080, -35, 2553, 33], [33, 868, 4478, -17252, -2171, 27891, -1049, -15080, 328, 2553]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 12, -36, -11, 65, 2, -42, 0, 11, 0], [0, 1, 12, -36, -11, 65, 2, -42, 0, 11], [11, 132, -395, -109, 679, 11, -397, 2, 79, 0], [0, 11, 132, -395, -109, 679, 11, -397, 2, 79], [79, 948, -2833, -737, 4740, 49, -2639, 11, 472, 2], [2, 103, 876, -2855, -607, 4744, -35, -2639, 33, 472], [472, 5666, -16889, -4316, 27825, 337, -15080, -35, 2553, 33], [33, 868, 4478, -17252, -2171, 27891, -1049, -15080, 328, 2553], [2553, 30669, -91040, -23605, 148693, 2935, -79335, -1049, 13003, 328]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp330689 : Fact (Nat.Prime 330689) := fact_iff.2 (by norm_num)
instance hp401669 : Fact (Nat.Prime 401669) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 3
  a' := [4, 4, 3, 1, 2, 3]
  b' := [1, 1, 2, 1, 3, 0, 4]
  k := [1, 3, 4, 0, 2, 3, 3, 3, 0, 1, 4, 1, 4, 4, 1]
  f := [1, 4, -6, -1, 15, 3, -6, 2, 4, 1]
  g := [4, 0, 2, 2, 4, 3, 2, 3, 1]
  h := [1, 2, 1]
  a := [2, 4, 3, 2, 4, 0, 1]
  b := [1, 2, 4, 4, 1, 4, 4, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD330689 : CertificateDedekindCriterionLists l 330689 where
  n := 2
  a' := [236103, 20741, 16023, 54479, 233431, 252498, 27573, 77298]
  b' := [68128, 185388, 280148, 54760, 254644, 188572, 265020, 326314, 101641]
  k := [98852, 64466, 271509, 224406, 253587, 88084, 288631, 164282, 1]
  f := [200125, 90271, 30475, 205799, 78213, 67926, 49816, 72307, 61738, 1]
  g := [266263, 120103, 40546, 273812, 104060, 90374, 66279, 96203, 82141, 1]
  h := [248548, 1]
  a := [296096, 88546, 84326, 322554, 281165, 221274, 238647, 257491, 189153]
  b := [71989, 147233, 13897, 326488, 184809, 232846, 21360, 221227, 141536]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD401669 : CertificateDedekindCriterionLists l 401669 where
  n := 2
  a' := [93682, 75120, 372309, 121890, 303113, 42670, 74594, 112108]
  b' := [380351, 194359, 345459, 371448, 42369, 175167, 186917, 177307, 210693]
  k := [204613, 137255, 210571, 124994, 128057, 368839, 304390, 351649, 1]
  f := [6729, 17988, 14677, 7515, 20151, 3811, 20559, 6318, 23453, 1]
  g := [108070, 288889, 235706, 120684, 323627, 61193, 330182, 101456, 376659, 1]
  h := [25010, 1]
  a := [185449, 358739, 198364, 158385, 158197, 117544, 74784, 308569, 9628]
  b := [148459, 278668, 125871, 259822, 125420, 267397, 292131, 230714, 392041]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 330689, 401669]
  exp := ![1, 1, 1]
  pdgood := [5, 330689, 401669]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp330689.out
    exact hp401669.out
  a := [-831880147457, 1519680776136, 8770788195678, -888799145292, -14069788686564, -96921154128, 6155895303760, 74275362910, -792738668600]
  b := [13978545646, 789111356655, 26888905643, -2871714898002, 7297886666, 2558334736322, 26032695253, -789992037468, -7427536291, 79273866860]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 330689 T_ofList CD330689
    exact satisfiesDedekindCriterion_of_certificate_lists T l 401669 T_ofList CD401669

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

end VoightMaximalOrderD10R218

namespace VoightMaximalOrderD10R220

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3369887595188, [1, 7, 8, -30, -54, 14, 44, -1, -12, 0, 1], 1⟩
local notation "l" => [1, 7, 8, -30, -54, 14, 44, -1, -12, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -8, 30, 54, -14, -44, 1, 12, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -8, 30, 54, -14, -44, 1, 12, 0], ![0, -1, -7, -8, 30, 54, -14, -44, 1, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -8, 30, 54, -14, -44, 1, 12, 0], ![0, -1, -7, -8, 30, 54, -14, -44, 1, 12], ![-12, -84, -97, 353, 640, -138, -474, -2, 100, 1]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -8, 30, 54, -14, -44, 1, 12, 0], ![0, -1, -7, -8, 30, 54, -14, -44, 1, 12], ![-12, -84, -97, 353, 640, -138, -474, -2, 100, 1], ![-1, -19, -92, -67, 407, 626, -182, -473, 10, 100]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -8, 30, 54, -14, -44, 1, 12, 0], ![0, -1, -7, -8, 30, 54, -14, -44, 1, 12], ![-12, -84, -97, 353, 640, -138, -474, -2, 100, 1], ![-1, -19, -92, -67, 407, 626, -182, -473, 10, 100], ![-100, -701, -819, 2908, 5333, -993, -3774, -82, 727, 10]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -8, 30, 54, -14, -44, 1, 12, 0], ![0, -1, -7, -8, 30, 54, -14, -44, 1, 12], ![-12, -84, -97, 353, 640, -138, -474, -2, 100, 1], ![-1, -19, -92, -67, 407, 626, -182, -473, 10, 100], ![-100, -701, -819, 2908, 5333, -993, -3774, -82, 727, 10], ![-10, -170, -781, -519, 3448, 5193, -1433, -3764, 38, 727]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -8, 30, 54, -14, -44, 1, 12, 0], ![0, -1, -7, -8, 30, 54, -14, -44, 1, 12], ![-12, -84, -97, 353, 640, -138, -474, -2, 100, 1], ![-1, -19, -92, -67, 407, 626, -182, -473, 10, 100], ![-100, -701, -819, 2908, 5333, -993, -3774, -82, 727, 10], ![-10, -170, -781, -519, 3448, 5193, -1433, -3764, 38, 727], ![-727, -5099, -5986, 21029, 38739, -6730, -26795, -706, 4960, 38]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -8, 30, 54, -14, -44, 1, 12, 0], ![0, -1, -7, -8, 30, 54, -14, -44, 1, 12], ![-12, -84, -97, 353, 640, -138, -474, -2, 100, 1], ![-1, -19, -92, -67, 407, 626, -182, -473, 10, 100], ![-100, -701, -819, 2908, 5333, -993, -3774, -82, 727, 10], ![-10, -170, -781, -519, 3448, 5193, -1433, -3764, 38, 727], ![-727, -5099, -5986, 21029, 38739, -6730, -26795, -706, 4960, 38], ![-38, -993, -5403, -4846, 23081, 38207, -8402, -26757, -250, 4960]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -8, 30, 54, -14, -44, 1, 12, 0], ![0, -1, -7, -8, 30, 54, -14, -44, 1, 12], ![-12, -84, -97, 353, 640, -138, -474, -2, 100, 1], ![-1, -19, -92, -67, 407, 626, -182, -473, 10, 100], ![-100, -701, -819, 2908, 5333, -993, -3774, -82, 727, 10], ![-10, -170, -781, -519, 3448, 5193, -1433, -3764, 38, 727], ![-727, -5099, -5986, 21029, 38739, -6730, -26795, -706, 4960, 38], ![-38, -993, -5403, -4846, 23081, 38207, -8402, -26757, -250, 4960], ![-4960, -34758, -40673, 143397, 262994, -46359, -180033, -3442, 32763, -250]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-1, -12, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-1, -12, 0, -1], [-100, -1, -12, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-12, 0, -1], [-1, -12, 0, -1], [-100, -1, -12, 0, -1], [-10, -100, -1, -12, 0, -1]], ![[], [], [], [-1], [0, -1], [-12, 0, -1], [-1, -12, 0, -1], [-100, -1, -12, 0, -1], [-10, -100, -1, -12, 0, -1], [-727, -10, -100, -1, -12, 0, -1]], ![[], [], [-1], [0, -1], [-12, 0, -1], [-1, -12, 0, -1], [-100, -1, -12, 0, -1], [-10, -100, -1, -12, 0, -1], [-727, -10, -100, -1, -12, 0, -1], [-38, -727, -10, -100, -1, -12, 0, -1]], ![[], [-1], [0, -1], [-12, 0, -1], [-1, -12, 0, -1], [-100, -1, -12, 0, -1], [-10, -100, -1, -12, 0, -1], [-727, -10, -100, -1, -12, 0, -1], [-38, -727, -10, -100, -1, -12, 0, -1], [-4960, -38, -727, -10, -100, -1, -12, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -8, 30, 54, -14, -44, 1, 12, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -8, 30, 54, -14, -44, 1, 12, 0], [0, -1, -7, -8, 30, 54, -14, -44, 1, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -8, 30, 54, -14, -44, 1, 12, 0], [0, -1, -7, -8, 30, 54, -14, -44, 1, 12], [-12, -84, -97, 353, 640, -138, -474, -2, 100, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -8, 30, 54, -14, -44, 1, 12, 0], [0, -1, -7, -8, 30, 54, -14, -44, 1, 12], [-12, -84, -97, 353, 640, -138, -474, -2, 100, 1], [-1, -19, -92, -67, 407, 626, -182, -473, 10, 100]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -8, 30, 54, -14, -44, 1, 12, 0], [0, -1, -7, -8, 30, 54, -14, -44, 1, 12], [-12, -84, -97, 353, 640, -138, -474, -2, 100, 1], [-1, -19, -92, -67, 407, 626, -182, -473, 10, 100], [-100, -701, -819, 2908, 5333, -993, -3774, -82, 727, 10]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -8, 30, 54, -14, -44, 1, 12, 0], [0, -1, -7, -8, 30, 54, -14, -44, 1, 12], [-12, -84, -97, 353, 640, -138, -474, -2, 100, 1], [-1, -19, -92, -67, 407, 626, -182, -473, 10, 100], [-100, -701, -819, 2908, 5333, -993, -3774, -82, 727, 10], [-10, -170, -781, -519, 3448, 5193, -1433, -3764, 38, 727]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -8, 30, 54, -14, -44, 1, 12, 0], [0, -1, -7, -8, 30, 54, -14, -44, 1, 12], [-12, -84, -97, 353, 640, -138, -474, -2, 100, 1], [-1, -19, -92, -67, 407, 626, -182, -473, 10, 100], [-100, -701, -819, 2908, 5333, -993, -3774, -82, 727, 10], [-10, -170, -781, -519, 3448, 5193, -1433, -3764, 38, 727], [-727, -5099, -5986, 21029, 38739, -6730, -26795, -706, 4960, 38]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -8, 30, 54, -14, -44, 1, 12, 0], [0, -1, -7, -8, 30, 54, -14, -44, 1, 12], [-12, -84, -97, 353, 640, -138, -474, -2, 100, 1], [-1, -19, -92, -67, 407, 626, -182, -473, 10, 100], [-100, -701, -819, 2908, 5333, -993, -3774, -82, 727, 10], [-10, -170, -781, -519, 3448, 5193, -1433, -3764, 38, 727], [-727, -5099, -5986, 21029, 38739, -6730, -26795, -706, 4960, 38], [-38, -993, -5403, -4846, 23081, 38207, -8402, -26757, -250, 4960]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -8, 30, 54, -14, -44, 1, 12, 0], [0, -1, -7, -8, 30, 54, -14, -44, 1, 12], [-12, -84, -97, 353, 640, -138, -474, -2, 100, 1], [-1, -19, -92, -67, 407, 626, -182, -473, 10, 100], [-100, -701, -819, 2908, 5333, -993, -3774, -82, 727, 10], [-10, -170, -781, -519, 3448, 5193, -1433, -3764, 38, 727], [-727, -5099, -5986, 21029, 38739, -6730, -26795, -706, 4960, 38], [-38, -993, -5403, -4846, 23081, 38207, -8402, -26757, -250, 4960], [-4960, -34758, -40673, 143397, 262994, -46359, -180033, -3442, 32763, -250]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp842471898797 : Fact (Nat.Prime 842471898797) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 3
  a' := [0, 0, 1]
  b' := [1, 0, 0, 1, 0, 0, 1]
  k := [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1]
  f := [0, -3, -3, 16, 28, -6, -21, 1, 7]
  g := [1, 1, 1, 1, 1, 1, 1, 0, 1]
  h := [1, 0, 1]
  a := [1, 0, 0, 0, 1, 1]
  b := [1, 0, 0, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD842471898797 : CertificateDedekindCriterionLists l 842471898797 where
  n := 2
  a' := [123694153521, 39158923105, 259844500269, 643856593736, 581054843790, 233865900905, 72456014847, 252555039046]
  b' := [90088546736, 264168272987, 350924579304, 655632727890, 529042720334, 659274962390, 340890337449, 766447494204, 439978272771]
  k := [233942947202, 614435418661, 351491011006, 645761995705, 345289335193, 673882852484, 711458907688, 427195929670, 1]
  f := [237256241341, 228416113648, 114208460381, 405842758713, 234348133548, 112357486810, 269628893302, 386650514500, 159442935277, 1]
  g := [317840675769, 305997985587, 152999533419, 543687853926, 313944824848, 150519873928, 361208747005, 517976935487, 213597964835, 1]
  h := [628873933962, 1]
  a := [44856379845, 419415228095, 699755342771, 118889774652, 103802125245, 524179830372, 14498529868, 277242318478, 203994745052]
  b := [597243004593, 599656649842, 54835682695, 761523479633, 187416672257, 155745336206, 828267943489, 581036449825, 638477153745]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![2, 842471898797]
  exp := ![1, 1]
  pdgood := [2, 842471898797]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp842471898797.out
  a := [-265065502366811, 279157341136024, 2451782683615251, 121302144353542, -2970295666052961, -268129253170044, 1101793748988048, 36999379693550, -116133667141980]
  b := [38107206594915, 138083695701859, -152150084331475, -625130591825753, 5036854609411, 499393332827997, 32208766429197, -138051455012880, -3699937969355, 11613366714198]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 842471898797 T_ofList CD842471898797

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

end VoightMaximalOrderD10R220

namespace VoightMaximalOrderD10R221

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3372427390293, [1, 12, 32, -23, -69, 10, 46, -1, -12, 0, 1], 1⟩
local notation "l" => [1, 12, 32, -23, -69, 10, 46, -1, -12, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -32, 23, 69, -10, -46, 1, 12, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -32, 23, 69, -10, -46, 1, 12, 0], ![0, -1, -12, -32, 23, 69, -10, -46, 1, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -32, 23, 69, -10, -46, 1, 12, 0], ![0, -1, -12, -32, 23, 69, -10, -46, 1, 12], ![-12, -144, -385, 264, 796, -97, -483, 2, 98, 1]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -32, 23, 69, -10, -46, 1, 12, 0], ![0, -1, -12, -32, 23, 69, -10, -46, 1, 12], ![-12, -144, -385, 264, 796, -97, -483, 2, 98, 1], ![-1, -24, -176, -362, 333, 786, -143, -482, 14, 98]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -32, 23, 69, -10, -46, 1, 12, 0], ![0, -1, -12, -32, 23, 69, -10, -46, 1, 12], ![-12, -144, -385, 264, 796, -97, -483, 2, 98, 1], ![-1, -24, -176, -362, 333, 786, -143, -482, 14, 98], ![-98, -1177, -3160, 2078, 6400, -647, -3722, -45, 694, 14]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -32, 23, 69, -10, -46, 1, 12, 0], ![0, -1, -12, -32, 23, 69, -10, -46, 1, 12], ![-12, -144, -385, 264, 796, -97, -483, 2, 98, 1], ![-1, -24, -176, -362, 333, 786, -143, -482, 14, 98], ![-98, -1177, -3160, 2078, 6400, -647, -3722, -45, 694, 14], ![-14, -266, -1625, -2838, 3044, 6260, -1291, -3708, 123, 694]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -32, 23, 69, -10, -46, 1, 12, 0], ![0, -1, -12, -32, 23, 69, -10, -46, 1, 12], ![-12, -144, -385, 264, 796, -97, -483, 2, 98, 1], ![-1, -24, -176, -362, 333, 786, -143, -482, 14, 98], ![-98, -1177, -3160, 2078, 6400, -647, -3722, -45, 694, 14], ![-14, -266, -1625, -2838, 3044, 6260, -1291, -3708, 123, 694], ![-694, -8342, -22474, 14337, 45048, -3896, -25664, -597, 4620, 123]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -32, 23, 69, -10, -46, 1, 12, 0], ![0, -1, -12, -32, 23, 69, -10, -46, 1, 12], ![-12, -144, -385, 264, 796, -97, -483, 2, 98, 1], ![-1, -24, -176, -362, 333, 786, -143, -482, 14, 98], ![-98, -1177, -3160, 2078, 6400, -647, -3722, -45, 694, 14], ![-14, -266, -1625, -2838, 3044, 6260, -1291, -3708, 123, 694], ![-694, -8342, -22474, 14337, 45048, -3896, -25664, -597, 4620, 123], ![-123, -2170, -12278, -19645, 22824, 43818, -9554, -25541, 879, 4620]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -32, 23, 69, -10, -46, 1, 12, 0], ![0, -1, -12, -32, 23, 69, -10, -46, 1, 12], ![-12, -144, -385, 264, 796, -97, -483, 2, 98, 1], ![-1, -24, -176, -362, 333, 786, -143, -482, 14, 98], ![-98, -1177, -3160, 2078, 6400, -647, -3722, -45, 694, 14], ![-14, -266, -1625, -2838, 3044, 6260, -1291, -3708, 123, 694], ![-694, -8342, -22474, 14337, 45048, -3896, -25664, -597, 4620, 123], ![-123, -2170, -12278, -19645, 22824, 43818, -9554, -25541, 879, 4620], ![-4620, -55563, -150010, 93982, 299135, -23376, -168702, -4934, 29899, 879]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-1, -12, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-1, -12, 0, -1], [-98, -1, -12, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-12, 0, -1], [-1, -12, 0, -1], [-98, -1, -12, 0, -1], [-14, -98, -1, -12, 0, -1]], ![[], [], [], [-1], [0, -1], [-12, 0, -1], [-1, -12, 0, -1], [-98, -1, -12, 0, -1], [-14, -98, -1, -12, 0, -1], [-694, -14, -98, -1, -12, 0, -1]], ![[], [], [-1], [0, -1], [-12, 0, -1], [-1, -12, 0, -1], [-98, -1, -12, 0, -1], [-14, -98, -1, -12, 0, -1], [-694, -14, -98, -1, -12, 0, -1], [-123, -694, -14, -98, -1, -12, 0, -1]], ![[], [-1], [0, -1], [-12, 0, -1], [-1, -12, 0, -1], [-98, -1, -12, 0, -1], [-14, -98, -1, -12, 0, -1], [-694, -14, -98, -1, -12, 0, -1], [-123, -694, -14, -98, -1, -12, 0, -1], [-4620, -123, -694, -14, -98, -1, -12, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -32, 23, 69, -10, -46, 1, 12, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -32, 23, 69, -10, -46, 1, 12, 0], [0, -1, -12, -32, 23, 69, -10, -46, 1, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -32, 23, 69, -10, -46, 1, 12, 0], [0, -1, -12, -32, 23, 69, -10, -46, 1, 12], [-12, -144, -385, 264, 796, -97, -483, 2, 98, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -32, 23, 69, -10, -46, 1, 12, 0], [0, -1, -12, -32, 23, 69, -10, -46, 1, 12], [-12, -144, -385, 264, 796, -97, -483, 2, 98, 1], [-1, -24, -176, -362, 333, 786, -143, -482, 14, 98]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -32, 23, 69, -10, -46, 1, 12, 0], [0, -1, -12, -32, 23, 69, -10, -46, 1, 12], [-12, -144, -385, 264, 796, -97, -483, 2, 98, 1], [-1, -24, -176, -362, 333, 786, -143, -482, 14, 98], [-98, -1177, -3160, 2078, 6400, -647, -3722, -45, 694, 14]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -32, 23, 69, -10, -46, 1, 12, 0], [0, -1, -12, -32, 23, 69, -10, -46, 1, 12], [-12, -144, -385, 264, 796, -97, -483, 2, 98, 1], [-1, -24, -176, -362, 333, 786, -143, -482, 14, 98], [-98, -1177, -3160, 2078, 6400, -647, -3722, -45, 694, 14], [-14, -266, -1625, -2838, 3044, 6260, -1291, -3708, 123, 694]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -32, 23, 69, -10, -46, 1, 12, 0], [0, -1, -12, -32, 23, 69, -10, -46, 1, 12], [-12, -144, -385, 264, 796, -97, -483, 2, 98, 1], [-1, -24, -176, -362, 333, 786, -143, -482, 14, 98], [-98, -1177, -3160, 2078, 6400, -647, -3722, -45, 694, 14], [-14, -266, -1625, -2838, 3044, 6260, -1291, -3708, 123, 694], [-694, -8342, -22474, 14337, 45048, -3896, -25664, -597, 4620, 123]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -32, 23, 69, -10, -46, 1, 12, 0], [0, -1, -12, -32, 23, 69, -10, -46, 1, 12], [-12, -144, -385, 264, 796, -97, -483, 2, 98, 1], [-1, -24, -176, -362, 333, 786, -143, -482, 14, 98], [-98, -1177, -3160, 2078, 6400, -647, -3722, -45, 694, 14], [-14, -266, -1625, -2838, 3044, 6260, -1291, -3708, 123, 694], [-694, -8342, -22474, 14337, 45048, -3896, -25664, -597, 4620, 123], [-123, -2170, -12278, -19645, 22824, 43818, -9554, -25541, 879, 4620]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -32, 23, 69, -10, -46, 1, 12, 0], [0, -1, -12, -32, 23, 69, -10, -46, 1, 12], [-12, -144, -385, 264, 796, -97, -483, 2, 98, 1], [-1, -24, -176, -362, 333, 786, -143, -482, 14, 98], [-98, -1177, -3160, 2078, 6400, -647, -3722, -45, 694, 14], [-14, -266, -1625, -2838, 3044, 6260, -1291, -3708, 123, 694], [-694, -8342, -22474, 14337, 45048, -3896, -25664, -597, 4620, 123], [-123, -2170, -12278, -19645, 22824, 43818, -9554, -25541, 879, 4620], [-4620, -55563, -150010, 93982, 299135, -23376, -168702, -4934, 29899, 879]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp13 : Fact (Nat.Prime 13) := fact_iff.2 (by norm_num)
instance hp3202685081 : Fact (Nat.Prime 3202685081) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 3
  a' := [0, 1, 1, 1, 1, 1, 2]
  b' := [2, 0, 0, 1, 0, 0, 0, 2]
  k := [1, 0, 1, 1, 1, 2, 1, 1, 0, 2, 2, 0, 0, 0, 1]
  f := [0, -3, -9, 9, 24, -3, -15, 1, 5, 1]
  g := [1, 2, 2, 0, 1, 0, 0, 2, 1]
  h := [1, 1, 1]
  a := [2, 1, 1, 2, 1, 1, 2]
  b := [1, 1, 2, 0, 1, 0, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD13 : CertificateDedekindCriterionLists l 13 where
  n := 2
  a' := [4, 11, 6, 11, 12, 3, 0, 2]
  b' := [2, 7, 8, 0, 7, 10, 12, 6, 7]
  k := [9, 2, 0, 9, 1, 3, 10, 8, 1]
  f := [2, 0, -1, 4, 9, 1, -2, 3, 4, 1]
  g := [3, 1, 2, 3, 5, 2, 2, 4, 4, 1]
  h := [9, 1]
  a := [0, 8, 6, 4, 1, 1, 12, 10, 3]
  b := [9, 9, 0, 11, 2, 9, 4, 3, 10]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3202685081 : CertificateDedekindCriterionLists l 3202685081 where
  n := 2
  a' := [2473230735, 3133067878, 2917939794, 2227330684, 423166340, 2347463248, 1490173446, 1330629777]
  b' := [2171052486, 1299794539, 1871552509, 1043612053, 2750750651, 649346956, 2397082894, 946920846, 3054837328]
  k := [2492390429, 1774857410, 744747762, 1987944743, 397440163, 2946672658, 396701964, 2025406872, 1]
  f := [1265248494, 338806700, 1185658517, 2046770120, 957988253, 956828828, 1276296765, 90421001, 692482052, 1]
  g := [1850331707, 495479569, 1733937292, 2993248889, 1400986483, 1399290911, 1866488980, 132233980, 1012703436, 1]
  h := [2189981645, 1]
  a := [1315584423, 84776713, 1023764191, 3013966514, 904188508, 1841762680, 2848710712, 545708989, 14390489]
  b := [3049518319, 601882429, 651170707, 2259000191, 1102761574, 1277240748, 2030537217, 3167102071, 3188294592]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![3, 13, 3202685081]
  exp := ![2, 1, 1]
  pdgood := [3, 13, 3202685081]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp13.out
    exact hp3202685081.out
  a := [-14112292903887, -32500248182176, 97921781356049, 117908854314494, -152154556427763, -76094226117618, 73357475314276, 10275660314650, -8985674555360]
  b := [1207250588197, 10381977115351, 13544027079798, -32900431279361, -22689499373816, 28960166533955, 9806010850617, -9492309424714, -1027566031465, 898567455536]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 13 T_ofList CD13
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3202685081 T_ofList CD3202685081

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

end VoightMaximalOrderD10R221

end TraceEuclidean
