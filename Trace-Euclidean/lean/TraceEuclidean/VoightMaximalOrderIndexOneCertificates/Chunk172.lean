import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk168
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

namespace VoightMaximalOrderD10R48

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1466566140909, [-1, -2, 10, 14, -32, -20, 30, 11, -10, -2, 1], 1⟩
local notation "l" => [-1, -2, 10, 14, -32, -20, 30, 11, -10, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -14, 32, 20, -30, -11, 10, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -14, 32, 20, -30, -11, 10, 2], ![2, 5, -18, -38, 50, 72, -40, -52, 9, 14]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -14, 32, 20, -30, -11, 10, 2], ![2, 5, -18, -38, 50, 72, -40, -52, 9, 14], ![14, 30, -135, -214, 410, 330, -348, -194, 88, 37]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -14, 32, 20, -30, -11, 10, 2], ![2, 5, -18, -38, 50, 72, -40, -52, 9, 14], ![14, 30, -135, -214, 410, 330, -348, -194, 88, 37], ![37, 88, -340, -653, 970, 1150, -780, -755, 176, 162]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -14, 32, 20, -30, -11, 10, 2], ![2, 5, -18, -38, 50, 72, -40, -52, 9, 14], ![14, 30, -135, -214, 410, 330, -348, -194, 88, 37], ![37, 88, -340, -653, 970, 1150, -780, -755, 176, 162], ![162, 361, -1532, -2608, 4531, 4210, -3710, -2562, 865, 500]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -14, 32, 20, -30, -11, 10, 2], ![2, 5, -18, -38, 50, 72, -40, -52, 9, 14], ![14, 30, -135, -214, 410, 330, -348, -194, 88, 37], ![37, 88, -340, -653, 970, 1150, -780, -755, 176, 162], ![162, 361, -1532, -2608, 4531, 4210, -3710, -2562, 865, 500], ![500, 1162, -4639, -8532, 13392, 14531, -10790, -9210, 2438, 1865]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -14, 32, 20, -30, -11, 10, 2], ![2, 5, -18, -38, 50, 72, -40, -52, 9, 14], ![14, 30, -135, -214, 410, 330, -348, -194, 88, 37], ![37, 88, -340, -653, 970, 1150, -780, -755, 176, 162], ![162, 361, -1532, -2608, 4531, 4210, -3710, -2562, 865, 500], ![500, 1162, -4639, -8532, 13392, 14531, -10790, -9210, 2438, 1865], ![1865, 4230, -17488, -30749, 51148, 50692, -41419, -31305, 9440, 6168]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -14, 32, 20, -30, -11, 10, 2], ![2, 5, -18, -38, 50, 72, -40, -52, 9, 14], ![14, 30, -135, -214, 410, 330, -348, -194, 88, 37], ![37, 88, -340, -653, 970, 1150, -780, -755, 176, 162], ![162, 361, -1532, -2608, 4531, 4210, -3710, -2562, 865, 500], ![500, 1162, -4639, -8532, 13392, 14531, -10790, -9210, 2438, 1865], ![1865, 4230, -17488, -30749, 51148, 50692, -41419, -31305, 9440, 6168], ![6168, 14201, -57450, -103840, 166627, 174508, -134348, -109267, 30375, 21776]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -14, 32, 20, -30, -11, 10, 2], ![2, 5, -18, -38, 50, 72, -40, -52, 9, 14], ![14, 30, -135, -214, 410, 330, -348, -194, 88, 37], ![37, 88, -340, -653, 970, 1150, -780, -755, 176, 162], ![162, 361, -1532, -2608, 4531, 4210, -3710, -2562, 865, 500], ![500, 1162, -4639, -8532, 13392, 14531, -10790, -9210, 2438, 1865], ![1865, 4230, -17488, -30749, 51148, 50692, -41419, -31305, 9440, 6168], ![6168, 14201, -57450, -103840, 166627, 174508, -134348, -109267, 30375, 21776], ![21776, 49720, -203559, -362314, 592992, 602147, -478772, -373884, 108493, 73927]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-37, -14, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-37, -14, -2, -1], [-162, -37, -14, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-37, -14, -2, -1], [-162, -37, -14, -2, -1], [-500, -162, -37, -14, -2, -1]], ![[], [], [], [-1], [-2, -1], [-14, -2, -1], [-37, -14, -2, -1], [-162, -37, -14, -2, -1], [-500, -162, -37, -14, -2, -1], [-1865, -500, -162, -37, -14, -2, -1]], ![[], [], [-1], [-2, -1], [-14, -2, -1], [-37, -14, -2, -1], [-162, -37, -14, -2, -1], [-500, -162, -37, -14, -2, -1], [-1865, -500, -162, -37, -14, -2, -1], [-6168, -1865, -500, -162, -37, -14, -2, -1]], ![[], [-1], [-2, -1], [-14, -2, -1], [-37, -14, -2, -1], [-162, -37, -14, -2, -1], [-500, -162, -37, -14, -2, -1], [-1865, -500, -162, -37, -14, -2, -1], [-6168, -1865, -500, -162, -37, -14, -2, -1], [-21776, -6168, -1865, -500, -162, -37, -14, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -14, 32, 20, -30, -11, 10, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -14, 32, 20, -30, -11, 10, 2], [2, 5, -18, -38, 50, 72, -40, -52, 9, 14]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -14, 32, 20, -30, -11, 10, 2], [2, 5, -18, -38, 50, 72, -40, -52, 9, 14], [14, 30, -135, -214, 410, 330, -348, -194, 88, 37]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -14, 32, 20, -30, -11, 10, 2], [2, 5, -18, -38, 50, 72, -40, -52, 9, 14], [14, 30, -135, -214, 410, 330, -348, -194, 88, 37], [37, 88, -340, -653, 970, 1150, -780, -755, 176, 162]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -14, 32, 20, -30, -11, 10, 2], [2, 5, -18, -38, 50, 72, -40, -52, 9, 14], [14, 30, -135, -214, 410, 330, -348, -194, 88, 37], [37, 88, -340, -653, 970, 1150, -780, -755, 176, 162], [162, 361, -1532, -2608, 4531, 4210, -3710, -2562, 865, 500]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -14, 32, 20, -30, -11, 10, 2], [2, 5, -18, -38, 50, 72, -40, -52, 9, 14], [14, 30, -135, -214, 410, 330, -348, -194, 88, 37], [37, 88, -340, -653, 970, 1150, -780, -755, 176, 162], [162, 361, -1532, -2608, 4531, 4210, -3710, -2562, 865, 500], [500, 1162, -4639, -8532, 13392, 14531, -10790, -9210, 2438, 1865]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -14, 32, 20, -30, -11, 10, 2], [2, 5, -18, -38, 50, 72, -40, -52, 9, 14], [14, 30, -135, -214, 410, 330, -348, -194, 88, 37], [37, 88, -340, -653, 970, 1150, -780, -755, 176, 162], [162, 361, -1532, -2608, 4531, 4210, -3710, -2562, 865, 500], [500, 1162, -4639, -8532, 13392, 14531, -10790, -9210, 2438, 1865], [1865, 4230, -17488, -30749, 51148, 50692, -41419, -31305, 9440, 6168]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -14, 32, 20, -30, -11, 10, 2], [2, 5, -18, -38, 50, 72, -40, -52, 9, 14], [14, 30, -135, -214, 410, 330, -348, -194, 88, 37], [37, 88, -340, -653, 970, 1150, -780, -755, 176, 162], [162, 361, -1532, -2608, 4531, 4210, -3710, -2562, 865, 500], [500, 1162, -4639, -8532, 13392, 14531, -10790, -9210, 2438, 1865], [1865, 4230, -17488, -30749, 51148, 50692, -41419, -31305, 9440, 6168], [6168, 14201, -57450, -103840, 166627, 174508, -134348, -109267, 30375, 21776]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -14, 32, 20, -30, -11, 10, 2], [2, 5, -18, -38, 50, 72, -40, -52, 9, 14], [14, 30, -135, -214, 410, 330, -348, -194, 88, 37], [37, 88, -340, -653, 970, 1150, -780, -755, 176, 162], [162, 361, -1532, -2608, 4531, 4210, -3710, -2562, 865, 500], [500, 1162, -4639, -8532, 13392, 14531, -10790, -9210, 2438, 1865], [1865, 4230, -17488, -30749, 51148, 50692, -41419, -31305, 9440, 6168], [6168, 14201, -57450, -103840, 166627, 174508, -134348, -109267, 30375, 21776], [21776, 49720, -203559, -362314, 592992, 602147, -478772, -373884, 108493, 73927]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp367 : Fact (Nat.Prime 367) := fact_iff.2 (by norm_num)
instance hp36497 : Fact (Nat.Prime 36497) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 2
  a' := [0, 0, 0, 2, 2]
  b' := [2, 2, 2, 2, 0, 1, 2, 2]
  k := [2, 0, 2, 1, 0, 0, 0, 2, 1]
  f := [1, 2, -2, -4, 11, 7, -10, -3, 4, 1]
  g := [2, 2, 2, 0, 1, 0, 0, 2, 0, 1]
  h := [1, 1]
  a := [0, 0, 1, 1, 2, 1, 2, 0, 1]
  b := [2, 1, 1, 1, 2, 0, 0, 2, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD367 : CertificateDedekindCriterionLists l 367 where
  n := 2
  a' := [288, 324, 147, 259, 280, 55, 78, 175]
  b' := [19, 135, 259, 51, 126, 343, 241, 13, 266]
  k := [24, 59, 256, 341, 80, 15, 60, 307, 1]
  f := [26, 22, 12, 19, 8, 12, 23, 13, 27, 1]
  g := [329, 267, 143, 236, 92, 148, 287, 155, 336, 1]
  h := [29, 1]
  a := [56, 157, 273, 125, 197, 263, 58, 1, 235]
  b := [357, 340, 97, 105, 68, 134, 111, 315, 132]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD36497 : CertificateDedekindCriterionLists l 36497 where
  n := 2
  a' := [32266, 28563, 29733, 35913, 32120, 5201, 1205]
  b' := [8108, 4311, 7882, 5255, 21832, 21014, 28258, 22660]
  k := [24845, 13447, 18980, 13418, 18298, 16467, 1]
  f := [2887, 8487, 16986, 30501, 17324, 3118, 11854, 23982, 7267, 1]
  g := [3898, 10015, 19224, 34060, 10772, 218, 15924, 26481, 1]
  h := [27031, 10014, 1]
  a := [28838, 18574, 27956, 8350, 30241, 13053, 20424, 21850]
  b := [4137, 28656, 4340, 36106, 18238, 13786, 8958, 16982, 14647]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![3, 367, 36497]
  exp := ![1, 1, 1]
  pdgood := [3, 367, 36497]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp367.out
    exact hp36497.out
  a := [3198014803, -41170374908, 43912865558, 92027874392, -86742591726, -62879263212, 44052159488, 13219096004, -6114392480]
  b := [-1619099000, 1196182651, 13164763654, -13002765462, -17621469493, 15111818658, 8730728964, -5583830654, -1444197450, 611439248]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 367 T_ofList CD367
    exact satisfiesDedekindCriterion_of_certificate_lists T l 36497 T_ofList CD36497

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

end VoightMaximalOrderD10R48

namespace VoightMaximalOrderD10R52

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1485695628125, [11, -24, -25, 71, 11, -69, 9, 26, -7, -3, 1], 1⟩
local notation "l" => [11, -24, -25, 71, 11, -69, 9, 26, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 24, 25, -71, -11, 69, -9, -26, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 24, 25, -71, -11, 69, -9, -26, 7, 3], ![-33, 61, 99, -188, -104, 196, 42, -87, -5, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 24, 25, -71, -11, 69, -9, -26, 7, 3], ![-33, 61, 99, -188, -104, 196, 42, -87, -5, 16], ![-176, 351, 461, -1037, -364, 1000, 52, -374, 25, 43]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 24, 25, -71, -11, 69, -9, -26, 7, 3], ![-33, 61, 99, -188, -104, 196, 42, -87, -5, 16], ![-176, 351, 461, -1037, -364, 1000, 52, -374, 25, 43], ![-473, 856, 1426, -2592, -1510, 2603, 613, -1066, -73, 154]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 24, 25, -71, -11, 69, -9, -26, 7, 3], ![-33, 61, 99, -188, -104, 196, 42, -87, -5, 16], ![-176, 351, 461, -1037, -364, 1000, 52, -374, 25, 43], ![-473, 856, 1426, -2592, -1510, 2603, 613, -1066, -73, 154], ![-1694, 3223, 4706, -9508, -4286, 9116, 1217, -3391, 12, 389]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 24, 25, -71, -11, 69, -9, -26, 7, 3], ![-33, 61, 99, -188, -104, 196, 42, -87, -5, 16], ![-176, 351, 461, -1037, -364, 1000, 52, -374, 25, 43], ![-473, 856, 1426, -2592, -1510, 2603, 613, -1066, -73, 154], ![-1694, 3223, 4706, -9508, -4286, 9116, 1217, -3391, 12, 389], ![-4279, 7642, 12948, -22913, -13787, 22555, 5615, -8897, -668, 1179]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 24, 25, -71, -11, 69, -9, -26, 7, 3], ![-33, 61, 99, -188, -104, 196, 42, -87, -5, 16], ![-176, 351, 461, -1037, -364, 1000, 52, -374, 25, 43], ![-473, 856, 1426, -2592, -1510, 2603, 613, -1066, -73, 154], ![-1694, 3223, 4706, -9508, -4286, 9116, 1217, -3391, 12, 389], ![-4279, 7642, 12948, -22913, -13787, 22555, 5615, -8897, -668, 1179], ![-12969, 24017, 37117, -70761, -35882, 67564, 11944, -25039, -644, 2869]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 24, 25, -71, -11, 69, -9, -26, 7, 3], ![-33, 61, 99, -188, -104, 196, 42, -87, -5, 16], ![-176, 351, 461, -1037, -364, 1000, 52, -374, 25, 43], ![-473, 856, 1426, -2592, -1510, 2603, 613, -1066, -73, 154], ![-1694, 3223, 4706, -9508, -4286, 9116, 1217, -3391, 12, 389], ![-4279, 7642, 12948, -22913, -13787, 22555, 5615, -8897, -668, 1179], ![-12969, 24017, 37117, -70761, -35882, 67564, 11944, -25039, -644, 2869], ![-31559, 55887, 95742, -166582, -102320, 162079, 41743, -62650, -4956, 7963]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-11, 24, 25, -71, -11, 69, -9, -26, 7, 3], ![-33, 61, 99, -188, -104, 196, 42, -87, -5, 16], ![-176, 351, 461, -1037, -364, 1000, 52, -374, 25, 43], ![-473, 856, 1426, -2592, -1510, 2603, 613, -1066, -73, 154], ![-1694, 3223, 4706, -9508, -4286, 9116, 1217, -3391, 12, 389], ![-4279, 7642, 12948, -22913, -13787, 22555, 5615, -8897, -668, 1179], ![-12969, 24017, 37117, -70761, -35882, 67564, 11944, -25039, -644, 2869], ![-31559, 55887, 95742, -166582, -102320, 162079, 41743, -62650, -4956, 7963], ![-87593, 159553, 254962, -469631, -254175, 447127, 90412, -165295, -6909, 18933]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1], [-154, -43, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1], [-154, -43, -16, -3, -1], [-389, -154, -43, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1], [-154, -43, -16, -3, -1], [-389, -154, -43, -16, -3, -1], [-1179, -389, -154, -43, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1], [-154, -43, -16, -3, -1], [-389, -154, -43, -16, -3, -1], [-1179, -389, -154, -43, -16, -3, -1], [-2869, -1179, -389, -154, -43, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1], [-154, -43, -16, -3, -1], [-389, -154, -43, -16, -3, -1], [-1179, -389, -154, -43, -16, -3, -1], [-2869, -1179, -389, -154, -43, -16, -3, -1], [-7963, -2869, -1179, -389, -154, -43, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 24, 25, -71, -11, 69, -9, -26, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 24, 25, -71, -11, 69, -9, -26, 7, 3], [-33, 61, 99, -188, -104, 196, 42, -87, -5, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 24, 25, -71, -11, 69, -9, -26, 7, 3], [-33, 61, 99, -188, -104, 196, 42, -87, -5, 16], [-176, 351, 461, -1037, -364, 1000, 52, -374, 25, 43]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 24, 25, -71, -11, 69, -9, -26, 7, 3], [-33, 61, 99, -188, -104, 196, 42, -87, -5, 16], [-176, 351, 461, -1037, -364, 1000, 52, -374, 25, 43], [-473, 856, 1426, -2592, -1510, 2603, 613, -1066, -73, 154]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 24, 25, -71, -11, 69, -9, -26, 7, 3], [-33, 61, 99, -188, -104, 196, 42, -87, -5, 16], [-176, 351, 461, -1037, -364, 1000, 52, -374, 25, 43], [-473, 856, 1426, -2592, -1510, 2603, 613, -1066, -73, 154], [-1694, 3223, 4706, -9508, -4286, 9116, 1217, -3391, 12, 389]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 24, 25, -71, -11, 69, -9, -26, 7, 3], [-33, 61, 99, -188, -104, 196, 42, -87, -5, 16], [-176, 351, 461, -1037, -364, 1000, 52, -374, 25, 43], [-473, 856, 1426, -2592, -1510, 2603, 613, -1066, -73, 154], [-1694, 3223, 4706, -9508, -4286, 9116, 1217, -3391, 12, 389], [-4279, 7642, 12948, -22913, -13787, 22555, 5615, -8897, -668, 1179]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 24, 25, -71, -11, 69, -9, -26, 7, 3], [-33, 61, 99, -188, -104, 196, 42, -87, -5, 16], [-176, 351, 461, -1037, -364, 1000, 52, -374, 25, 43], [-473, 856, 1426, -2592, -1510, 2603, 613, -1066, -73, 154], [-1694, 3223, 4706, -9508, -4286, 9116, 1217, -3391, 12, 389], [-4279, 7642, 12948, -22913, -13787, 22555, 5615, -8897, -668, 1179], [-12969, 24017, 37117, -70761, -35882, 67564, 11944, -25039, -644, 2869]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 24, 25, -71, -11, 69, -9, -26, 7, 3], [-33, 61, 99, -188, -104, 196, 42, -87, -5, 16], [-176, 351, 461, -1037, -364, 1000, 52, -374, 25, 43], [-473, 856, 1426, -2592, -1510, 2603, 613, -1066, -73, 154], [-1694, 3223, 4706, -9508, -4286, 9116, 1217, -3391, 12, 389], [-4279, 7642, 12948, -22913, -13787, 22555, 5615, -8897, -668, 1179], [-12969, 24017, 37117, -70761, -35882, 67564, 11944, -25039, -644, 2869], [-31559, 55887, 95742, -166582, -102320, 162079, 41743, -62650, -4956, 7963]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-11, 24, 25, -71, -11, 69, -9, -26, 7, 3], [-33, 61, 99, -188, -104, 196, 42, -87, -5, 16], [-176, 351, 461, -1037, -364, 1000, 52, -374, 25, 43], [-473, 856, 1426, -2592, -1510, 2603, 613, -1066, -73, 154], [-1694, 3223, 4706, -9508, -4286, 9116, 1217, -3391, 12, 389], [-4279, 7642, 12948, -22913, -13787, 22555, 5615, -8897, -668, 1179], [-12969, 24017, 37117, -70761, -35882, 67564, 11944, -25039, -644, 2869], [-31559, 55887, 95742, -166582, -102320, 162079, 41743, -62650, -4956, 7963], [-87593, 159553, 254962, -469631, -254175, 447127, 90412, -165295, -6909, 18933]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp475422601 : Fact (Nat.Prime 475422601) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 1, 1]
  b' := [0, 4, 0, 0, 1]
  k := [1]
  f := [1, 8, 9, -11, 1, 17, 0, -4, 2, 1]
  g := [4, 2, 2, 1, 1, 1]
  h := [4, 2, 2, 1, 1, 1]
  a := [3, 3, 2, 3, 2]
  b := [2, 1, 4, 0, 0, 2, 2, 0, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD475422601 : CertificateDedekindCriterionLists l 475422601 where
  n := 2
  a' := [439990212, 374556115, 332227332, 383800794, 441754222, 192863882, 364527636, 331418020]
  b' := [273024477, 224356181, 319826037, 207991604, 327839418, 330019037, 9452280, 116883806, 16000509]
  k := [465484334, 312149017, 3083265, 346814745, 252681681, 388654546, 209684056, 138521588, 1]
  f := [163259424, 76102026, 21568147, 78499656, 115597732, 159652995, 103714700, 140600018, 108765558, 1]
  g := [460771667, 214784887, 60872387, 221551788, 326254731, 450593139, 292716914, 396819386, 306972093, 1]
  h := [168450505, 1]
  a := [133833576, 191358919, 212452255, 289299702, 306068060, 53503573, 91350399, 177740345, 136682505]
  b := [59063671, 452159542, 245550022, 262466951, 167612964, 441593439, 330068216, 41160474, 338740096]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 475422601]
  exp := ![1, 1]
  pdgood := [5, 475422601]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp475422601.out
  a := [-75525008129, -272838528702, 256279045934, 520513169676, -318177438264, -289802105310, 155848795699, 44010726058, -22502932040]
  b := [-34714675101, 22796255601, 113386700866, -54480954180, -114439229958, 50360524266, 43726339721, -19237705769, -5076160567, 2250293204]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 475422601 T_ofList CD475422601

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

end VoightMaximalOrderD10R52

namespace VoightMaximalOrderD10R55

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1513588058741, [1, -9, -4, 48, -14, -66, 39, 16, -12, -1, 1], 1⟩
local notation "l" => [1, -9, -4, 48, -14, -66, 39, 16, -12, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, 4, -48, 14, 66, -39, -16, 12, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, 4, -48, 14, 66, -39, -16, 12, 1], ![-1, 8, 13, -44, -34, 80, 27, -55, -4, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, 4, -48, 14, 66, -39, -16, 12, 1], ![-1, 8, 13, -44, -34, 80, 27, -55, -4, 13], ![-13, 116, 60, -611, 138, 824, -427, -181, 101, 9]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, 4, -48, 14, 66, -39, -16, 12, 1], ![-1, 8, 13, -44, -34, 80, 27, -55, -4, 13], ![-13, 116, 60, -611, 138, 824, -427, -181, 101, 9], ![-9, 68, 152, -372, -485, 732, 473, -571, -73, 110]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, 4, -48, 14, 66, -39, -16, 12, 1], ![-1, 8, 13, -44, -34, 80, 27, -55, -4, 13], ![-13, 116, 60, -611, 138, 824, -427, -181, 101, 9], ![-9, 68, 152, -372, -485, 732, 473, -571, -73, 110], ![-110, 981, 508, -5128, 1168, 6775, -3558, -1287, 749, 37]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, 4, -48, 14, 66, -39, -16, 12, 1], ![-1, 8, 13, -44, -34, 80, 27, -55, -4, 13], ![-13, 116, 60, -611, 138, 824, -427, -181, 101, 9], ![-9, 68, 152, -372, -485, 732, 473, -571, -73, 110], ![-110, 981, 508, -5128, 1168, 6775, -3558, -1287, 749, 37], ![-37, 223, 1129, -1268, -4610, 3610, 5332, -4150, -843, 786]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, 4, -48, 14, 66, -39, -16, 12, 1], ![-1, 8, 13, -44, -34, 80, 27, -55, -4, 13], ![-13, 116, 60, -611, 138, 824, -427, -181, 101, 9], ![-9, 68, 152, -372, -485, 732, 473, -571, -73, 110], ![-110, 981, 508, -5128, 1168, 6775, -3558, -1287, 749, 37], ![-37, 223, 1129, -1268, -4610, 3610, 5332, -4150, -843, 786], ![-786, 7037, 3367, -36599, 9736, 47266, -27044, -7244, 5282, -57]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, 4, -48, 14, 66, -39, -16, 12, 1], ![-1, 8, 13, -44, -34, 80, 27, -55, -4, 13], ![-13, 116, 60, -611, 138, 824, -427, -181, 101, 9], ![-9, 68, 152, -372, -485, 732, 473, -571, -73, 110], ![-110, 981, 508, -5128, 1168, 6775, -3558, -1287, 749, 37], ![-37, 223, 1129, -1268, -4610, 3610, 5332, -4150, -843, 786], ![-786, 7037, 3367, -36599, 9736, 47266, -27044, -7244, 5282, -57], ![57, -1299, 6809, 6103, -37397, 5974, 49489, -26132, -7928, 5225]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, 4, -48, 14, 66, -39, -16, 12, 1], ![-1, 8, 13, -44, -34, 80, 27, -55, -4, 13], ![-13, 116, 60, -611, 138, 824, -427, -181, 101, 9], ![-9, 68, 152, -372, -485, 732, 473, -571, -73, 110], ![-110, 981, 508, -5128, 1168, 6775, -3558, -1287, 749, 37], ![-37, 223, 1129, -1268, -4610, 3610, 5332, -4150, -843, 786], ![-786, 7037, 3367, -36599, 9736, 47266, -27044, -7244, 5282, -57], ![57, -1299, 6809, 6103, -37397, 5974, 49489, -26132, -7928, 5225], ![-5225, 47082, 19601, -243991, 79253, 307453, -197801, -34111, 36568, -2703]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-13, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-9, -13, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-9, -13, -1, -1], [-110, -9, -13, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-9, -13, -1, -1], [-110, -9, -13, -1, -1], [-37, -110, -9, -13, -1, -1]], ![[], [], [], [-1], [-1, -1], [-13, -1, -1], [-9, -13, -1, -1], [-110, -9, -13, -1, -1], [-37, -110, -9, -13, -1, -1], [-786, -37, -110, -9, -13, -1, -1]], ![[], [], [-1], [-1, -1], [-13, -1, -1], [-9, -13, -1, -1], [-110, -9, -13, -1, -1], [-37, -110, -9, -13, -1, -1], [-786, -37, -110, -9, -13, -1, -1], [57, -786, -37, -110, -9, -13, -1, -1]], ![[], [-1], [-1, -1], [-13, -1, -1], [-9, -13, -1, -1], [-110, -9, -13, -1, -1], [-37, -110, -9, -13, -1, -1], [-786, -37, -110, -9, -13, -1, -1], [57, -786, -37, -110, -9, -13, -1, -1], [-5225, 57, -786, -37, -110, -9, -13, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, 4, -48, 14, 66, -39, -16, 12, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, 4, -48, 14, 66, -39, -16, 12, 1], [-1, 8, 13, -44, -34, 80, 27, -55, -4, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, 4, -48, 14, 66, -39, -16, 12, 1], [-1, 8, 13, -44, -34, 80, 27, -55, -4, 13], [-13, 116, 60, -611, 138, 824, -427, -181, 101, 9]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, 4, -48, 14, 66, -39, -16, 12, 1], [-1, 8, 13, -44, -34, 80, 27, -55, -4, 13], [-13, 116, 60, -611, 138, 824, -427, -181, 101, 9], [-9, 68, 152, -372, -485, 732, 473, -571, -73, 110]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, 4, -48, 14, 66, -39, -16, 12, 1], [-1, 8, 13, -44, -34, 80, 27, -55, -4, 13], [-13, 116, 60, -611, 138, 824, -427, -181, 101, 9], [-9, 68, 152, -372, -485, 732, 473, -571, -73, 110], [-110, 981, 508, -5128, 1168, 6775, -3558, -1287, 749, 37]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, 4, -48, 14, 66, -39, -16, 12, 1], [-1, 8, 13, -44, -34, 80, 27, -55, -4, 13], [-13, 116, 60, -611, 138, 824, -427, -181, 101, 9], [-9, 68, 152, -372, -485, 732, 473, -571, -73, 110], [-110, 981, 508, -5128, 1168, 6775, -3558, -1287, 749, 37], [-37, 223, 1129, -1268, -4610, 3610, 5332, -4150, -843, 786]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, 4, -48, 14, 66, -39, -16, 12, 1], [-1, 8, 13, -44, -34, 80, 27, -55, -4, 13], [-13, 116, 60, -611, 138, 824, -427, -181, 101, 9], [-9, 68, 152, -372, -485, 732, 473, -571, -73, 110], [-110, 981, 508, -5128, 1168, 6775, -3558, -1287, 749, 37], [-37, 223, 1129, -1268, -4610, 3610, 5332, -4150, -843, 786], [-786, 7037, 3367, -36599, 9736, 47266, -27044, -7244, 5282, -57]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, 4, -48, 14, 66, -39, -16, 12, 1], [-1, 8, 13, -44, -34, 80, 27, -55, -4, 13], [-13, 116, 60, -611, 138, 824, -427, -181, 101, 9], [-9, 68, 152, -372, -485, 732, 473, -571, -73, 110], [-110, 981, 508, -5128, 1168, 6775, -3558, -1287, 749, 37], [-37, 223, 1129, -1268, -4610, 3610, 5332, -4150, -843, 786], [-786, 7037, 3367, -36599, 9736, 47266, -27044, -7244, 5282, -57], [57, -1299, 6809, 6103, -37397, 5974, 49489, -26132, -7928, 5225]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, 4, -48, 14, 66, -39, -16, 12, 1], [-1, 8, 13, -44, -34, 80, 27, -55, -4, 13], [-13, 116, 60, -611, 138, 824, -427, -181, 101, 9], [-9, 68, 152, -372, -485, 732, 473, -571, -73, 110], [-110, 981, 508, -5128, 1168, 6775, -3558, -1287, 749, 37], [-37, 223, 1129, -1268, -4610, 3610, 5332, -4150, -843, 786], [-786, 7037, 3367, -36599, 9736, 47266, -27044, -7244, 5282, -57], [57, -1299, 6809, 6103, -37397, 5974, 49489, -26132, -7928, 5225], [-5225, 47082, 19601, -243991, 79253, 307453, -197801, -34111, 36568, -2703]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp23 : Fact (Nat.Prime 23) := fact_iff.2 (by norm_num)
instance hp307 : Fact (Nat.Prime 307) := fact_iff.2 (by norm_num)

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 5
  a' := [3]
  b' := [4, 4]
  k := [1]
  f := [4, 7, 3, -3, 6, 12, -1, 3, 3, 1]
  g := [5, 2, 1]
  h := [9, 10, 0, 1, 10, 9, 0, 8, 1]
  a := [6, 7]
  b := [2, 5, 4, 10, 1, 10, 0, 9, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD23 : CertificateDedekindCriterionLists l 23 where
  n := 2
  a' := [3, 8, 7, 13, 7, 16, 3, 7]
  b' := [1, 17, 14, 20, 13, 13, 17, 12, 12]
  k := [8, 21, 13, 2, 20, 22, 11, 8, 1]
  f := [3, 6, 7, 0, 2, 7, 1, 6, 6, 1]
  g := [10, 17, 20, 4, 4, 13, 7, 21, 15, 1]
  h := [7, 1]
  a := [21, 20, 5, 10, 14, 6, 22, 7, 3]
  b := [3, 20, 10, 0, 15, 17, 3, 20, 20]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD307 : CertificateDedekindCriterionLists l 307 where
  n := 2
  a' := [153, 213, 17, 167, 49, 170, 42, 169]
  b' := [101, 5, 265, 9, 69, 114, 193, 227, 220]
  k := [69, 164, 188, 217, 1, 297, 248, 6, 1]
  f := [107, 54, 59, 96, 30, 18, 21, 111, 77, 1]
  g := [219, 109, 120, 196, 60, 36, 43, 227, 156, 1]
  h := [150, 1]
  a := [222, 190, 240, 137, 93, 290, 267, 120, 240]
  b := [92, 237, 289, 181, 280, 32, 91, 113, 67]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![11, 23, 307]
  exp := ![1, 1, 1]
  pdgood := [11, 23, 307]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp11.out
    exact hp23.out
    exact hp307.out
  a := [-1570589, -3593062, 20658865, 16917758, -36481630, -4321638, 13780179, 14798, -1454920]
  b := [-183140, 1334151, 2470379, -5268611, -4249826, 6198008, 806292, -1740145, -16029, 145492]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 23 T_ofList CD23
    exact satisfiesDedekindCriterion_of_certificate_lists T l 307 T_ofList CD307

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

end VoightMaximalOrderD10R55

namespace VoightMaximalOrderD10R57

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1537158528125, [-5, -20, 1, 61, 6, -63, 1, 27, -4, -4, 1], 1⟩
local notation "l" => [-5, -20, 1, 61, 6, -63, 1, 27, -4, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 20, -1, -61, -6, 63, -1, -27, 4, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 20, -1, -61, -6, 63, -1, -27, 4, 4], ![20, 85, 16, -245, -85, 246, 59, -109, -11, 20]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 20, -1, -61, -6, 63, -1, -27, 4, 4], ![20, 85, 16, -245, -85, 246, 59, -109, -11, 20], ![100, 420, 65, -1204, -365, 1175, 226, -481, -29, 69]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 20, -1, -61, -6, 63, -1, -27, 4, 4], ![20, 85, 16, -245, -85, 246, 59, -109, -11, 20], ![100, 420, 65, -1204, -365, 1175, 226, -481, -29, 69], ![345, 1480, 351, -4144, -1618, 3982, 1106, -1637, -205, 247]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 20, -1, -61, -6, 63, -1, -27, 4, 4], ![20, 85, 16, -245, -85, 246, 59, -109, -11, 20], ![100, 420, 65, -1204, -365, 1175, 226, -481, -29, 69], ![345, 1480, 351, -4144, -1618, 3982, 1106, -1637, -205, 247], ![1235, 5285, 1233, -14716, -5626, 13943, 3735, -5563, -649, 783]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 20, -1, -61, -6, 63, -1, -27, 4, 4], ![20, 85, 16, -245, -85, 246, 59, -109, -11, 20], ![100, 420, 65, -1204, -365, 1175, 226, -481, -29, 69], ![345, 1480, 351, -4144, -1618, 3982, 1106, -1637, -205, 247], ![1235, 5285, 1233, -14716, -5626, 13943, 3735, -5563, -649, 783], ![3915, 16895, 4502, -46530, -19414, 43703, 13160, -17406, -2431, 2483]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 20, -1, -61, -6, 63, -1, -27, 4, 4], ![20, 85, 16, -245, -85, 246, 59, -109, -11, 20], ![100, 420, 65, -1204, -365, 1175, 226, -481, -29, 69], ![345, 1480, 351, -4144, -1618, 3982, 1106, -1637, -205, 247], ![1235, 5285, 1233, -14716, -5626, 13943, 3735, -5563, -649, 783], ![3915, 16895, 4502, -46530, -19414, 43703, 13160, -17406, -2431, 2483], ![12415, 53575, 14412, -146961, -61428, 137015, 41220, -53881, -7474, 7501]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 20, -1, -61, -6, 63, -1, -27, 4, 4], ![20, 85, 16, -245, -85, 246, 59, -109, -11, 20], ![100, 420, 65, -1204, -365, 1175, 226, -481, -29, 69], ![345, 1480, 351, -4144, -1618, 3982, 1106, -1637, -205, 247], ![1235, 5285, 1233, -14716, -5626, 13943, 3735, -5563, -649, 783], ![3915, 16895, 4502, -46530, -19414, 43703, 13160, -17406, -2431, 2483], ![12415, 53575, 14412, -146961, -61428, 137015, 41220, -53881, -7474, 7501], ![37505, 162435, 46074, -443149, -191967, 411135, 129514, -161307, -23877, 22530]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 20, -1, -61, -6, 63, -1, -27, 4, 4], ![20, 85, 16, -245, -85, 246, 59, -109, -11, 20], ![100, 420, 65, -1204, -365, 1175, 226, -481, -29, 69], ![345, 1480, 351, -4144, -1618, 3982, 1106, -1637, -205, 247], ![1235, 5285, 1233, -14716, -5626, 13943, 3735, -5563, -649, 783], ![3915, 16895, 4502, -46530, -19414, 43703, 13160, -17406, -2431, 2483], ![12415, 53575, 14412, -146961, -61428, 137015, 41220, -53881, -7474, 7501], ![37505, 162435, 46074, -443149, -191967, 411135, 129514, -161307, -23877, 22530], ![112650, 488105, 139905, -1328256, -578329, 1227423, 388605, -478796, -71187, 66243]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1], [-247, -69, -20, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1], [-247, -69, -20, -4, -1], [-783, -247, -69, -20, -4, -1]], ![[], [], [], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1], [-247, -69, -20, -4, -1], [-783, -247, -69, -20, -4, -1], [-2483, -783, -247, -69, -20, -4, -1]], ![[], [], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1], [-247, -69, -20, -4, -1], [-783, -247, -69, -20, -4, -1], [-2483, -783, -247, -69, -20, -4, -1], [-7501, -2483, -783, -247, -69, -20, -4, -1]], ![[], [-1], [-4, -1], [-20, -4, -1], [-69, -20, -4, -1], [-247, -69, -20, -4, -1], [-783, -247, -69, -20, -4, -1], [-2483, -783, -247, -69, -20, -4, -1], [-7501, -2483, -783, -247, -69, -20, -4, -1], [-22530, -7501, -2483, -783, -247, -69, -20, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 20, -1, -61, -6, 63, -1, -27, 4, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 20, -1, -61, -6, 63, -1, -27, 4, 4], [20, 85, 16, -245, -85, 246, 59, -109, -11, 20]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 20, -1, -61, -6, 63, -1, -27, 4, 4], [20, 85, 16, -245, -85, 246, 59, -109, -11, 20], [100, 420, 65, -1204, -365, 1175, 226, -481, -29, 69]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 20, -1, -61, -6, 63, -1, -27, 4, 4], [20, 85, 16, -245, -85, 246, 59, -109, -11, 20], [100, 420, 65, -1204, -365, 1175, 226, -481, -29, 69], [345, 1480, 351, -4144, -1618, 3982, 1106, -1637, -205, 247]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 20, -1, -61, -6, 63, -1, -27, 4, 4], [20, 85, 16, -245, -85, 246, 59, -109, -11, 20], [100, 420, 65, -1204, -365, 1175, 226, -481, -29, 69], [345, 1480, 351, -4144, -1618, 3982, 1106, -1637, -205, 247], [1235, 5285, 1233, -14716, -5626, 13943, 3735, -5563, -649, 783]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 20, -1, -61, -6, 63, -1, -27, 4, 4], [20, 85, 16, -245, -85, 246, 59, -109, -11, 20], [100, 420, 65, -1204, -365, 1175, 226, -481, -29, 69], [345, 1480, 351, -4144, -1618, 3982, 1106, -1637, -205, 247], [1235, 5285, 1233, -14716, -5626, 13943, 3735, -5563, -649, 783], [3915, 16895, 4502, -46530, -19414, 43703, 13160, -17406, -2431, 2483]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 20, -1, -61, -6, 63, -1, -27, 4, 4], [20, 85, 16, -245, -85, 246, 59, -109, -11, 20], [100, 420, 65, -1204, -365, 1175, 226, -481, -29, 69], [345, 1480, 351, -4144, -1618, 3982, 1106, -1637, -205, 247], [1235, 5285, 1233, -14716, -5626, 13943, 3735, -5563, -649, 783], [3915, 16895, 4502, -46530, -19414, 43703, 13160, -17406, -2431, 2483], [12415, 53575, 14412, -146961, -61428, 137015, 41220, -53881, -7474, 7501]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 20, -1, -61, -6, 63, -1, -27, 4, 4], [20, 85, 16, -245, -85, 246, 59, -109, -11, 20], [100, 420, 65, -1204, -365, 1175, 226, -481, -29, 69], [345, 1480, 351, -4144, -1618, 3982, 1106, -1637, -205, 247], [1235, 5285, 1233, -14716, -5626, 13943, 3735, -5563, -649, 783], [3915, 16895, 4502, -46530, -19414, 43703, 13160, -17406, -2431, 2483], [12415, 53575, 14412, -146961, -61428, 137015, 41220, -53881, -7474, 7501], [37505, 162435, 46074, -443149, -191967, 411135, 129514, -161307, -23877, 22530]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 20, -1, -61, -6, 63, -1, -27, 4, 4], [20, 85, 16, -245, -85, 246, 59, -109, -11, 20], [100, 420, 65, -1204, -365, 1175, 226, -481, -29, 69], [345, 1480, 351, -4144, -1618, 3982, 1106, -1637, -205, 247], [1235, 5285, 1233, -14716, -5626, 13943, 3735, -5563, -649, 783], [3915, 16895, 4502, -46530, -19414, 43703, 13160, -17406, -2431, 2483], [12415, 53575, 14412, -146961, -61428, 137015, 41220, -53881, -7474, 7501], [37505, 162435, 46074, -443149, -191967, 411135, 129514, -161307, -23877, 22530], [112650, 488105, 139905, -1328256, -578329, 1227423, 388605, -478796, -71187, 66243]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp59 : Fact (Nat.Prime 59) := fact_iff.2 (by norm_num)
instance hp709 : Fact (Nat.Prime 709) := fact_iff.2 (by norm_num)
instance hp1069 : Fact (Nat.Prime 1069) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 1, 1]
  b' := [1, 4, 2, 0, 2]
  k := [1]
  f := [1, 4, 0, -11, 1, 15, 4, -3, 3, 2]
  g := [0, 1, 3, 1, 3, 1]
  h := [0, 1, 3, 1, 3, 1]
  a := [1, 4, 1]
  b := [2, 2, 4, 3, 1, 0, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [7, 3, 0, 7, 9, 5, 0, 9]
  b' := [7, 10, 2, 3, 6, 10, 0, 8, 10]
  k := [7, 10, 5, 5, 9, 7, 2, 3, 1]
  f := [1, 3, 2, -4, 0, 6, 0, -1, 2, 1]
  g := [3, 5, 9, 4, 1, 1, 0, 8, 5, 1]
  h := [2, 1]
  a := [8, 5, 7, 9, 7, 3, 8, 9, 8]
  b := [5, 4, 6, 9, 2, 4, 4, 4, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD59 : CertificateDedekindCriterionLists l 59 where
  n := 2
  a' := [19, 53, 54, 50, 5, 46, 16, 49]
  b' := [32, 53, 15, 23, 50, 39, 36, 33, 47]
  k := [11, 41, 43, 14, 10, 24, 39, 1, 1]
  f := [1, 26, 11, 3, 22, 6, 7, 3, 13, 1]
  g := [2, 56, 22, 8, 48, 9, 15, 7, 28, 1]
  h := [27, 1]
  a := [39, 55, 7, 4, 2, 30, 46, 44, 55]
  b := [40, 27, 54, 55, 30, 49, 36, 14, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD709 : CertificateDedekindCriterionLists l 709 where
  n := 2
  a' := [320, 636, 159, 221, 507, 171, 431, 571]
  b' := [700, 260, 563, 566, 511, 283, 679, 473, 488]
  k := [278, 654, 663, 403, 98, 318, 43, 523, 1]
  f := [62, 31, 2, 60, 14, 87, 89, 18, 79, 1]
  g := [483, 236, 13, 468, 104, 676, 686, 133, 614, 1]
  h := [91, 1]
  a := [53, 466, 576, 579, 7, 583, 70, 289, 271]
  b := [231, 323, 93, 665, 559, 24, 493, 60, 438]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1069 : CertificateDedekindCriterionLists l 1069 where
  n := 2
  a' := [181, 626, 486, 89, 813, 503, 592, 64]
  b' := [740, 898, 907, 412, 1005, 344, 918, 594, 468]
  k := [1053, 155, 298, 511, 797, 1031, 298, 806, 1]
  f := [41, 174, 163, 453, 351, 95, 43, 610, 250, 1]
  g := [66, 280, 262, 729, 564, 152, 69, 982, 401, 1]
  h := [664, 1]
  a := [782, 972, 161, 51, 389, 212, 798, 680, 372]
  b := [729, 753, 445, 0, 1059, 990, 737, 973, 697]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 5
  p := ![5, 11, 59, 709, 1069]
  exp := ![1, 1, 1, 1, 1]
  pdgood := [5, 11, 59, 709, 1069]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp11.out
    exact hp59.out
    exact hp709.out
    exact hp1069.out
  a := [137220065731, -351742177198, -397113317980, 809597485310, 215715481490, -567338091060, 45058293536, 118180066212, -29600855120]
  b := [-34427989115, -52727320343, 137592677543, 85638737950, -168524724853, -30382473034, 81326129302, -6409218252, -13002040826, 2960085512]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 59 T_ofList CD59
    exact satisfiesDedekindCriterion_of_certificate_lists T l 709 T_ofList CD709
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1069 T_ofList CD1069

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

end VoightMaximalOrderD10R57

end TraceEuclidean
