import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk180
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

namespace VoightMaximalOrderD10R160

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2808868878125, [-1, 6, 24, -2, -49, -8, 35, 6, -10, -1, 1], 1⟩
local notation "l" => [-1, 6, 24, -2, -49, -8, 35, 6, -10, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, -24, 2, 49, 8, -35, -6, 10, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, -24, 2, 49, 8, -35, -6, 10, 1], ![1, -5, -30, -22, 51, 57, -27, -41, 4, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, -24, 2, 49, 8, -35, -6, 10, 1], ![1, -5, -30, -22, 51, 57, -27, -41, 4, 11], ![11, -65, -269, -8, 517, 139, -328, -93, 69, 15]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, -24, 2, 49, 8, -35, -6, 10, 1], ![1, -5, -30, -22, 51, 57, -27, -41, 4, 11], ![11, -65, -269, -8, 517, 139, -328, -93, 69, 15], ![15, -79, -425, -239, 727, 637, -386, -418, 57, 84]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, -24, 2, 49, 8, -35, -6, 10, 1], ![1, -5, -30, -22, 51, 57, -27, -41, 4, 11], ![11, -65, -269, -8, 517, 139, -328, -93, 69, 15], ![15, -79, -425, -239, 727, 637, -386, -418, 57, 84], ![84, -489, -2095, -257, 3877, 1399, -2303, -890, 422, 141]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, -24, 2, 49, 8, -35, -6, 10, 1], ![1, -5, -30, -22, 51, 57, -27, -41, 4, 11], ![11, -65, -269, -8, 517, 139, -328, -93, 69, 15], ![15, -79, -425, -239, 727, 637, -386, -418, 57, 84], ![84, -489, -2095, -257, 3877, 1399, -2303, -890, 422, 141], ![141, -762, -3873, -1813, 6652, 5005, -3536, -3149, 520, 563]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, -24, 2, 49, 8, -35, -6, 10, 1], ![1, -5, -30, -22, 51, 57, -27, -41, 4, 11], ![11, -65, -269, -8, 517, 139, -328, -93, 69, 15], ![15, -79, -425, -239, 727, 637, -386, -418, 57, 84], ![84, -489, -2095, -257, 3877, 1399, -2303, -890, 422, 141], ![141, -762, -3873, -1813, 6652, 5005, -3536, -3149, 520, 563], ![563, -3237, -14274, -2747, 25774, 11156, -14700, -6914, 2481, 1083]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, -24, 2, 49, 8, -35, -6, 10, 1], ![1, -5, -30, -22, 51, 57, -27, -41, 4, 11], ![11, -65, -269, -8, 517, 139, -328, -93, 69, 15], ![15, -79, -425, -239, 727, 637, -386, -418, 57, 84], ![84, -489, -2095, -257, 3877, 1399, -2303, -890, 422, 141], ![141, -762, -3873, -1813, 6652, 5005, -3536, -3149, 520, 563], ![563, -3237, -14274, -2747, 25774, 11156, -14700, -6914, 2481, 1083], ![1083, -5935, -29229, -12108, 50320, 34438, -26749, -21198, 3916, 3564]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, -24, 2, 49, 8, -35, -6, 10, 1], ![1, -5, -30, -22, 51, 57, -27, -41, 4, 11], ![11, -65, -269, -8, 517, 139, -328, -93, 69, 15], ![15, -79, -425, -239, 727, 637, -386, -418, 57, 84], ![84, -489, -2095, -257, 3877, 1399, -2303, -890, 422, 141], ![141, -762, -3873, -1813, 6652, 5005, -3536, -3149, 520, 563], ![563, -3237, -14274, -2747, 25774, 11156, -14700, -6914, 2481, 1083], ![1083, -5935, -29229, -12108, 50320, 34438, -26749, -21198, 3916, 3564], ![3564, -20301, -91471, -22101, 162528, 78832, -90302, -48133, 14442, 7480]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-15, -11, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-15, -11, -1, -1], [-84, -15, -11, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-15, -11, -1, -1], [-84, -15, -11, -1, -1], [-141, -84, -15, -11, -1, -1]], ![[], [], [], [-1], [-1, -1], [-11, -1, -1], [-15, -11, -1, -1], [-84, -15, -11, -1, -1], [-141, -84, -15, -11, -1, -1], [-563, -141, -84, -15, -11, -1, -1]], ![[], [], [-1], [-1, -1], [-11, -1, -1], [-15, -11, -1, -1], [-84, -15, -11, -1, -1], [-141, -84, -15, -11, -1, -1], [-563, -141, -84, -15, -11, -1, -1], [-1083, -563, -141, -84, -15, -11, -1, -1]], ![[], [-1], [-1, -1], [-11, -1, -1], [-15, -11, -1, -1], [-84, -15, -11, -1, -1], [-141, -84, -15, -11, -1, -1], [-563, -141, -84, -15, -11, -1, -1], [-1083, -563, -141, -84, -15, -11, -1, -1], [-3564, -1083, -563, -141, -84, -15, -11, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, -24, 2, 49, 8, -35, -6, 10, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, -24, 2, 49, 8, -35, -6, 10, 1], [1, -5, -30, -22, 51, 57, -27, -41, 4, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, -24, 2, 49, 8, -35, -6, 10, 1], [1, -5, -30, -22, 51, 57, -27, -41, 4, 11], [11, -65, -269, -8, 517, 139, -328, -93, 69, 15]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, -24, 2, 49, 8, -35, -6, 10, 1], [1, -5, -30, -22, 51, 57, -27, -41, 4, 11], [11, -65, -269, -8, 517, 139, -328, -93, 69, 15], [15, -79, -425, -239, 727, 637, -386, -418, 57, 84]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, -24, 2, 49, 8, -35, -6, 10, 1], [1, -5, -30, -22, 51, 57, -27, -41, 4, 11], [11, -65, -269, -8, 517, 139, -328, -93, 69, 15], [15, -79, -425, -239, 727, 637, -386, -418, 57, 84], [84, -489, -2095, -257, 3877, 1399, -2303, -890, 422, 141]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, -24, 2, 49, 8, -35, -6, 10, 1], [1, -5, -30, -22, 51, 57, -27, -41, 4, 11], [11, -65, -269, -8, 517, 139, -328, -93, 69, 15], [15, -79, -425, -239, 727, 637, -386, -418, 57, 84], [84, -489, -2095, -257, 3877, 1399, -2303, -890, 422, 141], [141, -762, -3873, -1813, 6652, 5005, -3536, -3149, 520, 563]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, -24, 2, 49, 8, -35, -6, 10, 1], [1, -5, -30, -22, 51, 57, -27, -41, 4, 11], [11, -65, -269, -8, 517, 139, -328, -93, 69, 15], [15, -79, -425, -239, 727, 637, -386, -418, 57, 84], [84, -489, -2095, -257, 3877, 1399, -2303, -890, 422, 141], [141, -762, -3873, -1813, 6652, 5005, -3536, -3149, 520, 563], [563, -3237, -14274, -2747, 25774, 11156, -14700, -6914, 2481, 1083]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, -24, 2, 49, 8, -35, -6, 10, 1], [1, -5, -30, -22, 51, 57, -27, -41, 4, 11], [11, -65, -269, -8, 517, 139, -328, -93, 69, 15], [15, -79, -425, -239, 727, 637, -386, -418, 57, 84], [84, -489, -2095, -257, 3877, 1399, -2303, -890, 422, 141], [141, -762, -3873, -1813, 6652, 5005, -3536, -3149, 520, 563], [563, -3237, -14274, -2747, 25774, 11156, -14700, -6914, 2481, 1083], [1083, -5935, -29229, -12108, 50320, 34438, -26749, -21198, 3916, 3564]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, -24, 2, 49, 8, -35, -6, 10, 1], [1, -5, -30, -22, 51, 57, -27, -41, 4, 11], [11, -65, -269, -8, 517, 139, -328, -93, 69, 15], [15, -79, -425, -239, 727, 637, -386, -418, 57, 84], [84, -489, -2095, -257, 3877, 1399, -2303, -890, 422, 141], [141, -762, -3873, -1813, 6652, 5005, -3536, -3149, 520, 563], [563, -3237, -14274, -2747, 25774, 11156, -14700, -6914, 2481, 1083], [1083, -5935, -29229, -12108, 50320, 34438, -26749, -21198, 3916, 3564], [3564, -20301, -91471, -22101, 162528, 78832, -90302, -48133, 14442, 7480]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp898838041 : Fact (Nat.Prime 898838041) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 3]
  b' := [1, 4, 4, 4]
  k := [1]
  f := [1, 2, 0, 6, 17, 8, -2, 2, 4, 1]
  g := [2, 4, 2, 3, 2, 1]
  h := [2, 4, 2, 3, 2, 1]
  a := [3, 2, 0, 0, 4]
  b := [4, 3, 3, 1, 3, 3, 0, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD898838041 : CertificateDedekindCriterionLists l 898838041 where
  n := 2
  a' := [546497613, 280559457, 21330986, 821782056, 636924907, 37969115, 36837745, 856723874]
  b' := [201090716, 603190524, 870377538, 767967417, 502364719, 881618943, 57790761, 745539495, 703775606]
  k := [54028410, 848699687, 748490557, 393209596, 620349214, 30391262, 422027450, 759083028, 1]
  f := [69561253, 67574746, 22139839, 21894375, 67099474, 34924055, 25924068, 12747232, 64445086, 1]
  g := [894770062, 869217505, 284785903, 281628495, 863104065, 449229947, 333462646, 163968312, 828960534, 1]
  h := [69877506, 1]
  a := [488128909, 334703559, 144301892, 649362604, 554179082, 363796131, 543352132, 705495371, 7588269]
  b := [254662679, 69153629, 512422770, 18557089, 463820000, 12107209, 771689117, 271508866, 891249772]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 898838041]
  exp := ![1, 1]
  pdgood := [5, 898838041]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp898838041.out
  a := [-32502062327, -184411939596, 348870159756, 419207921412, -502390276405, -275917448850, 231131104039, 50488725826, -33359645040]
  b := [-4667978687, 39110568557, 55012688387, -105666677560, -78486271557, 89916506027, 37516214895, -29580388959, -5382469033, 3335964504]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 898838041 T_ofList CD898838041

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

end VoightMaximalOrderD10R160

namespace VoightMaximalOrderD10R176

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2902226190625, [1, 12, 28, -8, -60, -9, 41, 7, -11, -1, 1], 1⟩
local notation "l" => [1, 12, 28, -8, -60, -9, 41, 7, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -28, 8, 60, 9, -41, -7, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -28, 8, 60, 9, -41, -7, 11, 1], ![-1, -13, -40, -20, 68, 69, -32, -48, 4, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -28, 8, 60, 9, -41, -7, 11, 1], ![-1, -13, -40, -20, 68, 69, -32, -48, 4, 12], ![-12, -145, -349, 56, 700, 176, -423, -116, 84, 16]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -28, 8, 60, 9, -41, -7, 11, 1], ![-1, -13, -40, -20, 68, 69, -32, -48, 4, 12], ![-12, -145, -349, 56, 700, 176, -423, -116, 84, 16], ![-16, -204, -593, -221, 1016, 844, -480, -535, 60, 100]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -28, 8, 60, 9, -41, -7, 11, 1], ![-1, -13, -40, -20, 68, 69, -32, -48, 4, 12], ![-12, -145, -349, 56, 700, 176, -423, -116, 84, 16], ![-16, -204, -593, -221, 1016, 844, -480, -535, 60, 100], ![-100, -1216, -3004, 207, 5779, 1916, -3256, -1180, 565, 160]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -28, 8, 60, 9, -41, -7, 11, 1], ![-1, -13, -40, -20, 68, 69, -32, -48, 4, 12], ![-12, -145, -349, 56, 700, 176, -423, -116, 84, 16], ![-16, -204, -593, -221, 1016, 844, -480, -535, 60, 100], ![-100, -1216, -3004, 207, 5779, 1916, -3256, -1180, 565, 160], ![-160, -2020, -5696, -1724, 9807, 7219, -4644, -4376, 580, 725]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -28, 8, 60, 9, -41, -7, 11, 1], ![-1, -13, -40, -20, 68, 69, -32, -48, 4, 12], ![-12, -145, -349, 56, 700, 176, -423, -116, 84, 16], ![-16, -204, -593, -221, 1016, 844, -480, -535, 60, 100], ![-100, -1216, -3004, 207, 5779, 1916, -3256, -1180, 565, 160], ![-160, -2020, -5696, -1724, 9807, 7219, -4644, -4376, 580, 725], ![-725, -8860, -22320, 104, 41776, 16332, -22506, -9719, 3599, 1305]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -28, 8, 60, 9, -41, -7, 11, 1], ![-1, -13, -40, -20, 68, 69, -32, -48, 4, 12], ![-12, -145, -349, 56, 700, 176, -423, -116, 84, 16], ![-16, -204, -593, -221, 1016, 844, -480, -535, 60, 100], ![-100, -1216, -3004, 207, 5779, 1916, -3256, -1180, 565, 160], ![-160, -2020, -5696, -1724, 9807, 7219, -4644, -4376, 580, 725], ![-725, -8860, -22320, 104, 41776, 16332, -22506, -9719, 3599, 1305], ![-1305, -16385, -45400, -11880, 78404, 53521, -37173, -31641, 4636, 4904]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -28, 8, 60, 9, -41, -7, 11, 1], ![-1, -13, -40, -20, 68, 69, -32, -48, 4, 12], ![-12, -145, -349, 56, 700, 176, -423, -116, 84, 16], ![-16, -204, -593, -221, 1016, 844, -480, -535, 60, 100], ![-100, -1216, -3004, 207, 5779, 1916, -3256, -1180, 565, 160], ![-160, -2020, -5696, -1724, 9807, 7219, -4644, -4376, 580, 725], ![-725, -8860, -22320, 104, 41776, 16332, -22506, -9719, 3599, 1305], ![-1305, -16385, -45400, -11880, 78404, 53521, -37173, -31641, 4636, 4904], ![-4904, -60153, -153697, -6168, 282360, 122540, -147543, -71501, 22303, 9540]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-16, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-16, -12, -1, -1], [-100, -16, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-16, -12, -1, -1], [-100, -16, -12, -1, -1], [-160, -100, -16, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-16, -12, -1, -1], [-100, -16, -12, -1, -1], [-160, -100, -16, -12, -1, -1], [-725, -160, -100, -16, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-16, -12, -1, -1], [-100, -16, -12, -1, -1], [-160, -100, -16, -12, -1, -1], [-725, -160, -100, -16, -12, -1, -1], [-1305, -725, -160, -100, -16, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-16, -12, -1, -1], [-100, -16, -12, -1, -1], [-160, -100, -16, -12, -1, -1], [-725, -160, -100, -16, -12, -1, -1], [-1305, -725, -160, -100, -16, -12, -1, -1], [-4904, -1305, -725, -160, -100, -16, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -28, 8, 60, 9, -41, -7, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -28, 8, 60, 9, -41, -7, 11, 1], [-1, -13, -40, -20, 68, 69, -32, -48, 4, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -28, 8, 60, 9, -41, -7, 11, 1], [-1, -13, -40, -20, 68, 69, -32, -48, 4, 12], [-12, -145, -349, 56, 700, 176, -423, -116, 84, 16]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -28, 8, 60, 9, -41, -7, 11, 1], [-1, -13, -40, -20, 68, 69, -32, -48, 4, 12], [-12, -145, -349, 56, 700, 176, -423, -116, 84, 16], [-16, -204, -593, -221, 1016, 844, -480, -535, 60, 100]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -28, 8, 60, 9, -41, -7, 11, 1], [-1, -13, -40, -20, 68, 69, -32, -48, 4, 12], [-12, -145, -349, 56, 700, 176, -423, -116, 84, 16], [-16, -204, -593, -221, 1016, 844, -480, -535, 60, 100], [-100, -1216, -3004, 207, 5779, 1916, -3256, -1180, 565, 160]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -28, 8, 60, 9, -41, -7, 11, 1], [-1, -13, -40, -20, 68, 69, -32, -48, 4, 12], [-12, -145, -349, 56, 700, 176, -423, -116, 84, 16], [-16, -204, -593, -221, 1016, 844, -480, -535, 60, 100], [-100, -1216, -3004, 207, 5779, 1916, -3256, -1180, 565, 160], [-160, -2020, -5696, -1724, 9807, 7219, -4644, -4376, 580, 725]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -28, 8, 60, 9, -41, -7, 11, 1], [-1, -13, -40, -20, 68, 69, -32, -48, 4, 12], [-12, -145, -349, 56, 700, 176, -423, -116, 84, 16], [-16, -204, -593, -221, 1016, 844, -480, -535, 60, 100], [-100, -1216, -3004, 207, 5779, 1916, -3256, -1180, 565, 160], [-160, -2020, -5696, -1724, 9807, 7219, -4644, -4376, 580, 725], [-725, -8860, -22320, 104, 41776, 16332, -22506, -9719, 3599, 1305]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -28, 8, 60, 9, -41, -7, 11, 1], [-1, -13, -40, -20, 68, 69, -32, -48, 4, 12], [-12, -145, -349, 56, 700, 176, -423, -116, 84, 16], [-16, -204, -593, -221, 1016, 844, -480, -535, 60, 100], [-100, -1216, -3004, 207, 5779, 1916, -3256, -1180, 565, 160], [-160, -2020, -5696, -1724, 9807, 7219, -4644, -4376, 580, 725], [-725, -8860, -22320, 104, 41776, 16332, -22506, -9719, 3599, 1305], [-1305, -16385, -45400, -11880, 78404, 53521, -37173, -31641, 4636, 4904]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -28, 8, 60, 9, -41, -7, 11, 1], [-1, -13, -40, -20, 68, 69, -32, -48, 4, 12], [-12, -145, -349, 56, 700, 176, -423, -116, 84, 16], [-16, -204, -593, -221, 1016, 844, -480, -535, 60, 100], [-100, -1216, -3004, 207, 5779, 1916, -3256, -1180, 565, 160], [-160, -2020, -5696, -1724, 9807, 7219, -4644, -4376, 580, 725], [-725, -8860, -22320, 104, 41776, 16332, -22506, -9719, 3599, 1305], [-1305, -16385, -45400, -11880, 78404, 53521, -37173, -31641, 4636, 4904], [-4904, -60153, -153697, -6168, 282360, 122540, -147543, -71501, 22303, 9540]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp149 : Fact (Nat.Prime 149) := fact_iff.2 (by norm_num)
instance hp328051 : Fact (Nat.Prime 328051) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 3, 2]
  b' := [0, 1, 2, 1, 1]
  k := [1]
  f := [0, -2, -5, 2, 13, 3, -7, -1, 3, 1]
  g := [1, 1, 1, 0, 2, 1]
  h := [1, 1, 1, 0, 2, 1]
  a := [0, 2, 2, 3, 1]
  b := [1, 4, 4, 1, 0, 2, 3, 1, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD19 : CertificateDedekindCriterionLists l 19 where
  n := 2
  a' := [11, 18, 12, 6, 2, 1, 5, 10]
  b' := [15, 12, 18, 17, 6, 14, 5, 7, 1]
  k := [7, 6, 15, 9, 18, 10, 17, 4, 1]
  f := [4, 4, 5, 2, 4, 5, 4, 3, 5, 1]
  g := [11, 11, 16, 2, 2, 12, 15, 7, 11, 1]
  h := [7, 1]
  a := [1, 17, 16, 8, 8, 10, 9, 5, 8]
  b := [17, 11, 14, 9, 6, 2, 0, 5, 11]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD149 : CertificateDedekindCriterionLists l 149 where
  n := 2
  a' := [78, 81, 36, 88, 15, 126, 130, 137]
  b' := [68, 111, 127, 129, 25, 115, 57, 64, 51]
  k := [46, 49, 110, 101, 116, 98, 65, 17, 1]
  f := [31, 49, 96, 90, 95, 121, 103, 58, 8, 1]
  g := [33, 52, 102, 95, 100, 128, 109, 61, 8, 1]
  h := [140, 1]
  a := [22, 98, 28, 115, 101, 85, 70, 2, 35]
  b := [20, 65, 65, 70, 145, 36, 35, 147, 114]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD328051 : CertificateDedekindCriterionLists l 328051 where
  n := 2
  a' := [185945, 397, 195, 51322, 216921, 66511, 96868, 222108]
  b' := [225877, 291247, 118512, 79512, 65358, 143924, 34883, 138596, 194022]
  k := [290521, 312809, 111733, 7416, 25827, 187780, 306808, 193543, 1]
  f := [380, 31019, 174767, 159452, 68768, 166919, 13931, 126447, 68225, 1]
  g := [539, 43998, 247893, 226169, 97541, 236761, 19759, 179355, 96771, 1]
  h := [231279, 1]
  a := [2859, 146428, 95587, 247242, 146772, 246602, 268919, 197255, 3050]
  b := [170835, 94194, 174211, 27282, 197080, 28051, 217696, 262581, 325001]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 19, 149, 328051]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 19, 149, 328051]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp19.out
    exact hp149.out
    exact hp328051.out
  a := [-63533728751, -133609212200, 396883281576, 349487708496, -485998678292, -219339966670, 199136515640, 34543391736, -24911223840]
  b := [5681440888, 48154438957, 35423139131, -111978534922, -63983303836, 84902257740, 29740764606, -25272887906, -3703451412, 2491122384]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19 T_ofList CD19
    exact satisfiesDedekindCriterion_of_certificate_lists T l 149 T_ofList CD149
    exact satisfiesDedekindCriterion_of_certificate_lists T l 328051 T_ofList CD328051

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

end VoightMaximalOrderD10R176

namespace VoightMaximalOrderD10R179

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2915420815625, [1, 8, 14, -18, -45, 8, 39, 3, -11, -1, 1], 1⟩
local notation "l" => [1, 8, 14, -18, -45, 8, 39, 3, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -14, 18, 45, -8, -39, -3, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -14, 18, 45, -8, -39, -3, 11, 1], ![-1, -9, -22, 4, 63, 37, -47, -42, 8, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -14, 18, 45, -8, -39, -3, 11, 1], ![-1, -9, -22, 4, 63, 37, -47, -42, 8, 12], ![-12, -97, -177, 194, 544, -33, -431, -83, 90, 20]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -14, 18, 45, -8, -39, -3, 11, 1], ![-1, -9, -22, 4, 63, 37, -47, -42, 8, 12], ![-12, -97, -177, 194, 544, -33, -431, -83, 90, 20], ![-20, -172, -377, 183, 1094, 384, -813, -491, 137, 110]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -14, 18, 45, -8, -39, -3, 11, 1], ![-1, -9, -22, 4, 63, 37, -47, -42, 8, 12], ![-12, -97, -177, 194, 544, -33, -431, -83, 90, 20], ![-20, -172, -377, 183, 1094, 384, -813, -491, 137, 110], ![-110, -900, -1712, 1603, 5133, 214, -3906, -1143, 719, 247]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -14, 18, 45, -8, -39, -3, 11, 1], ![-1, -9, -22, 4, 63, 37, -47, -42, 8, 12], ![-12, -97, -177, 194, 544, -33, -431, -83, 90, 20], ![-20, -172, -377, 183, 1094, 384, -813, -491, 137, 110], ![-110, -900, -1712, 1603, 5133, 214, -3906, -1143, 719, 247], ![-247, -2086, -4358, 2734, 12718, 3157, -9419, -4647, 1574, 966]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -14, 18, 45, -8, -39, -3, 11, 1], ![-1, -9, -22, 4, 63, 37, -47, -42, 8, 12], ![-12, -97, -177, 194, 544, -33, -431, -83, 90, 20], ![-20, -172, -377, 183, 1094, 384, -813, -491, 137, 110], ![-110, -900, -1712, 1603, 5133, 214, -3906, -1143, 719, 247], ![-247, -2086, -4358, 2734, 12718, 3157, -9419, -4647, 1574, 966], ![-966, -7975, -15610, 13030, 46204, 4990, -34517, -12317, 5979, 2540]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -14, 18, 45, -8, -39, -3, 11, 1], ![-1, -9, -22, 4, 63, 37, -47, -42, 8, 12], ![-12, -97, -177, 194, 544, -33, -431, -83, 90, 20], ![-20, -172, -377, 183, 1094, 384, -813, -491, 137, 110], ![-110, -900, -1712, 1603, 5133, 214, -3906, -1143, 719, 247], ![-247, -2086, -4358, 2734, 12718, 3157, -9419, -4647, 1574, 966], ![-966, -7975, -15610, 13030, 46204, 4990, -34517, -12317, 5979, 2540], ![-2540, -21286, -43535, 30110, 127330, 25884, -94070, -42137, 15623, 8519]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -14, 18, 45, -8, -39, -3, 11, 1], ![-1, -9, -22, 4, 63, 37, -47, -42, 8, 12], ![-12, -97, -177, 194, 544, -33, -431, -83, 90, 20], ![-20, -172, -377, 183, 1094, 384, -813, -491, 137, 110], ![-110, -900, -1712, 1603, 5133, 214, -3906, -1143, 719, 247], ![-247, -2086, -4358, 2734, 12718, 3157, -9419, -4647, 1574, 966], ![-966, -7975, -15610, 13030, 46204, 4990, -34517, -12317, 5979, 2540], ![-2540, -21286, -43535, 30110, 127330, 25884, -94070, -42137, 15623, 8519], ![-8519, -70692, -140552, 109807, 413465, 59178, -306357, -119627, 51572, 24142]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-20, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-20, -12, -1, -1], [-110, -20, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-20, -12, -1, -1], [-110, -20, -12, -1, -1], [-247, -110, -20, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-20, -12, -1, -1], [-110, -20, -12, -1, -1], [-247, -110, -20, -12, -1, -1], [-966, -247, -110, -20, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-20, -12, -1, -1], [-110, -20, -12, -1, -1], [-247, -110, -20, -12, -1, -1], [-966, -247, -110, -20, -12, -1, -1], [-2540, -966, -247, -110, -20, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-20, -12, -1, -1], [-110, -20, -12, -1, -1], [-247, -110, -20, -12, -1, -1], [-966, -247, -110, -20, -12, -1, -1], [-2540, -966, -247, -110, -20, -12, -1, -1], [-8519, -2540, -966, -247, -110, -20, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -14, 18, 45, -8, -39, -3, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -14, 18, 45, -8, -39, -3, 11, 1], [-1, -9, -22, 4, 63, 37, -47, -42, 8, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -14, 18, 45, -8, -39, -3, 11, 1], [-1, -9, -22, 4, 63, 37, -47, -42, 8, 12], [-12, -97, -177, 194, 544, -33, -431, -83, 90, 20]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -14, 18, 45, -8, -39, -3, 11, 1], [-1, -9, -22, 4, 63, 37, -47, -42, 8, 12], [-12, -97, -177, 194, 544, -33, -431, -83, 90, 20], [-20, -172, -377, 183, 1094, 384, -813, -491, 137, 110]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -14, 18, 45, -8, -39, -3, 11, 1], [-1, -9, -22, 4, 63, 37, -47, -42, 8, 12], [-12, -97, -177, 194, 544, -33, -431, -83, 90, 20], [-20, -172, -377, 183, 1094, 384, -813, -491, 137, 110], [-110, -900, -1712, 1603, 5133, 214, -3906, -1143, 719, 247]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -14, 18, 45, -8, -39, -3, 11, 1], [-1, -9, -22, 4, 63, 37, -47, -42, 8, 12], [-12, -97, -177, 194, 544, -33, -431, -83, 90, 20], [-20, -172, -377, 183, 1094, 384, -813, -491, 137, 110], [-110, -900, -1712, 1603, 5133, 214, -3906, -1143, 719, 247], [-247, -2086, -4358, 2734, 12718, 3157, -9419, -4647, 1574, 966]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -14, 18, 45, -8, -39, -3, 11, 1], [-1, -9, -22, 4, 63, 37, -47, -42, 8, 12], [-12, -97, -177, 194, 544, -33, -431, -83, 90, 20], [-20, -172, -377, 183, 1094, 384, -813, -491, 137, 110], [-110, -900, -1712, 1603, 5133, 214, -3906, -1143, 719, 247], [-247, -2086, -4358, 2734, 12718, 3157, -9419, -4647, 1574, 966], [-966, -7975, -15610, 13030, 46204, 4990, -34517, -12317, 5979, 2540]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -14, 18, 45, -8, -39, -3, 11, 1], [-1, -9, -22, 4, 63, 37, -47, -42, 8, 12], [-12, -97, -177, 194, 544, -33, -431, -83, 90, 20], [-20, -172, -377, 183, 1094, 384, -813, -491, 137, 110], [-110, -900, -1712, 1603, 5133, 214, -3906, -1143, 719, 247], [-247, -2086, -4358, 2734, 12718, 3157, -9419, -4647, 1574, 966], [-966, -7975, -15610, 13030, 46204, 4990, -34517, -12317, 5979, 2540], [-2540, -21286, -43535, 30110, 127330, 25884, -94070, -42137, 15623, 8519]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -14, 18, 45, -8, -39, -3, 11, 1], [-1, -9, -22, 4, 63, 37, -47, -42, 8, 12], [-12, -97, -177, 194, 544, -33, -431, -83, 90, 20], [-20, -172, -377, 183, 1094, 384, -813, -491, 137, 110], [-110, -900, -1712, 1603, 5133, 214, -3906, -1143, 719, 247], [-247, -2086, -4358, 2734, 12718, 3157, -9419, -4647, 1574, 966], [-966, -7975, -15610, 13030, 46204, 4990, -34517, -12317, 5979, 2540], [-2540, -21286, -43535, 30110, 127330, 25884, -94070, -42137, 15623, 8519], [-8519, -70692, -140552, 109807, 413465, 59178, -306357, -119627, 51572, 24142]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp811 : Fact (Nat.Prime 811) := fact_iff.2 (by norm_num)
instance hp1150351 : Fact (Nat.Prime 1150351) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 3, 3]
  b' := [1, 4, 0, 2, 4]
  k := [1]
  f := [0, 0, 2, 10, 13, 2, -3, 1, 3, 1]
  g := [1, 4, 4, 0, 2, 1]
  h := [1, 4, 4, 0, 2, 1]
  a := [3, 3, 1, 2, 4]
  b := [1, 1, 1, 1, 4, 3, 1, 4, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD811 : CertificateDedekindCriterionLists l 811 where
  n := 2
  a' := [696, 367, 336, 189, 458, 496, 132, 316]
  b' := [175, 8, 311, 254, 312, 798, 360, 433, 55]
  k := [236, 490, 252, 173, 478, 263, 55, 177, 1]
  f := [73, 374, 686, 236, 547, 526, 209, 465, 79, 1]
  g := [82, 420, 770, 264, 614, 590, 234, 522, 88, 1]
  h := [722, 1]
  a := [331, 549, 585, 272, 753, 582, 618, 767, 86]
  b := [457, 62, 71, 303, 578, 223, 656, 7, 725]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1150351 : CertificateDedekindCriterionLists l 1150351 where
  n := 2
  a' := [385551, 303930, 764629, 590810, 145679, 686980, 430565, 2618]
  b' := [821360, 751113, 580969, 262959, 738446, 156837, 985651, 1076552, 638793]
  k := [63952, 575363, 186099, 149241, 317647, 805519, 778050, 710800, 1]
  f := [11899, 82974, 172640, 156502, 156257, 217622, 99189, 63544, 177787, 1]
  g := [62282, 434304, 903634, 819162, 817880, 1139078, 519172, 332601, 930575, 1]
  h := [219775, 1]
  a := [570012, 242436, 777219, 822603, 177550, 859593, 756517, 888815, 44261]
  b := [247109, 605228, 1022658, 1090823, 475329, 142386, 618913, 644840, 1106090]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 811, 1150351]
  exp := ![1, 1, 1]
  pdgood := [5, 811, 1150351]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp811.out
    exact hp1150351.out
  a := [-341418157223, 18517737120, 2092904739582, 474814116804, -2755142723615, -743585819184, 1099633674425, 188796483486, -137832905840]
  b := [43260353816, 187692201727, -47564372214, -546097772628, -74761334949, 473262313703, 100457617299, -139639138045, -20257977407, 13783290584]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 811 T_ofList CD811
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1150351 T_ofList CD1150351

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

end VoightMaximalOrderD10R179

namespace VoightMaximalOrderD10R182

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2954050015625, [1, -11, 30, 8, -59, 1, 40, -1, -11, 0, 1], 1⟩
local notation "l" => [1, -11, 30, 8, -59, 1, 40, -1, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 11, -30, -8, 59, -1, -40, 1, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 11, -30, -8, 59, -1, -40, 1, 11, 0], ![0, -1, 11, -30, -8, 59, -1, -40, 1, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 11, -30, -8, 59, -1, -40, 1, 11, 0], ![0, -1, 11, -30, -8, 59, -1, -40, 1, 11], ![-11, 121, -331, -77, 619, -19, -381, 10, 81, 1]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 11, -30, -8, 59, -1, -40, 1, 11, 0], ![0, -1, 11, -30, -8, 59, -1, -40, 1, 11], ![-11, 121, -331, -77, 619, -19, -381, 10, 81, 1], ![-1, 0, 91, -339, -18, 618, -59, -380, 21, 81]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 11, -30, -8, 59, -1, -40, 1, 11, 0], ![0, -1, 11, -30, -8, 59, -1, -40, 1, 11], ![-11, 121, -331, -77, 619, -19, -381, 10, 81, 1], ![-1, 0, 91, -339, -18, 618, -59, -380, 21, 81], ![-81, 890, -2430, -557, 4440, -99, -2622, 22, 511, 21]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 11, -30, -8, 59, -1, -40, 1, 11, 0], ![0, -1, 11, -30, -8, 59, -1, -40, 1, 11], ![-11, 121, -331, -77, 619, -19, -381, 10, 81, 1], ![-1, 0, 91, -339, -18, 618, -59, -380, 21, 81], ![-81, 890, -2430, -557, 4440, -99, -2622, 22, 511, 21], ![-21, 150, 260, -2598, 682, 4419, -939, -2601, 253, 511]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 11, -30, -8, 59, -1, -40, 1, 11, 0], ![0, -1, 11, -30, -8, 59, -1, -40, 1, 11], ![-11, 121, -331, -77, 619, -19, -381, 10, 81, 1], ![-1, 0, 91, -339, -18, 618, -59, -380, 21, 81], ![-81, 890, -2430, -557, 4440, -99, -2622, 22, 511, 21], ![-21, 150, 260, -2598, 682, 4419, -939, -2601, 253, 511], ![-511, 5600, -15180, -3828, 27551, 171, -16021, -428, 3020, 253]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 11, -30, -8, 59, -1, -40, 1, 11, 0], ![0, -1, 11, -30, -8, 59, -1, -40, 1, 11], ![-11, 121, -331, -77, 619, -19, -381, 10, 81, 1], ![-1, 0, 91, -339, -18, 618, -59, -380, 21, 81], ![-81, 890, -2430, -557, 4440, -99, -2622, 22, 511, 21], ![-21, 150, 260, -2598, 682, 4419, -939, -2601, 253, 511], ![-511, 5600, -15180, -3828, 27551, 171, -16021, -428, 3020, 253], ![-253, 2272, -1990, -17204, 11099, 27298, -9949, -15768, 2355, 3020]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 11, -30, -8, 59, -1, -40, 1, 11, 0], ![0, -1, 11, -30, -8, 59, -1, -40, 1, 11], ![-11, 121, -331, -77, 619, -19, -381, 10, 81, 1], ![-1, 0, 91, -339, -18, 618, -59, -380, 21, 81], ![-81, 890, -2430, -557, 4440, -99, -2622, 22, 511, 21], ![-21, 150, 260, -2598, 682, 4419, -939, -2601, 253, 511], ![-511, 5600, -15180, -3828, 27551, 171, -16021, -428, 3020, 253], ![-253, 2272, -1990, -17204, 11099, 27298, -9949, -15768, 2355, 3020], ![-3020, 32967, -88328, -26150, 160976, 8079, -93502, -6929, 17452, 2355]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1], [-81, -1, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1], [-81, -1, -11, 0, -1], [-21, -81, -1, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1], [-81, -1, -11, 0, -1], [-21, -81, -1, -11, 0, -1], [-511, -21, -81, -1, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1], [-81, -1, -11, 0, -1], [-21, -81, -1, -11, 0, -1], [-511, -21, -81, -1, -11, 0, -1], [-253, -511, -21, -81, -1, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1], [-81, -1, -11, 0, -1], [-21, -81, -1, -11, 0, -1], [-511, -21, -81, -1, -11, 0, -1], [-253, -511, -21, -81, -1, -11, 0, -1], [-3020, -253, -511, -21, -81, -1, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 11, -30, -8, 59, -1, -40, 1, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 11, -30, -8, 59, -1, -40, 1, 11, 0], [0, -1, 11, -30, -8, 59, -1, -40, 1, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 11, -30, -8, 59, -1, -40, 1, 11, 0], [0, -1, 11, -30, -8, 59, -1, -40, 1, 11], [-11, 121, -331, -77, 619, -19, -381, 10, 81, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 11, -30, -8, 59, -1, -40, 1, 11, 0], [0, -1, 11, -30, -8, 59, -1, -40, 1, 11], [-11, 121, -331, -77, 619, -19, -381, 10, 81, 1], [-1, 0, 91, -339, -18, 618, -59, -380, 21, 81]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 11, -30, -8, 59, -1, -40, 1, 11, 0], [0, -1, 11, -30, -8, 59, -1, -40, 1, 11], [-11, 121, -331, -77, 619, -19, -381, 10, 81, 1], [-1, 0, 91, -339, -18, 618, -59, -380, 21, 81], [-81, 890, -2430, -557, 4440, -99, -2622, 22, 511, 21]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 11, -30, -8, 59, -1, -40, 1, 11, 0], [0, -1, 11, -30, -8, 59, -1, -40, 1, 11], [-11, 121, -331, -77, 619, -19, -381, 10, 81, 1], [-1, 0, 91, -339, -18, 618, -59, -380, 21, 81], [-81, 890, -2430, -557, 4440, -99, -2622, 22, 511, 21], [-21, 150, 260, -2598, 682, 4419, -939, -2601, 253, 511]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 11, -30, -8, 59, -1, -40, 1, 11, 0], [0, -1, 11, -30, -8, 59, -1, -40, 1, 11], [-11, 121, -331, -77, 619, -19, -381, 10, 81, 1], [-1, 0, 91, -339, -18, 618, -59, -380, 21, 81], [-81, 890, -2430, -557, 4440, -99, -2622, 22, 511, 21], [-21, 150, 260, -2598, 682, 4419, -939, -2601, 253, 511], [-511, 5600, -15180, -3828, 27551, 171, -16021, -428, 3020, 253]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 11, -30, -8, 59, -1, -40, 1, 11, 0], [0, -1, 11, -30, -8, 59, -1, -40, 1, 11], [-11, 121, -331, -77, 619, -19, -381, 10, 81, 1], [-1, 0, 91, -339, -18, 618, -59, -380, 21, 81], [-81, 890, -2430, -557, 4440, -99, -2622, 22, 511, 21], [-21, 150, 260, -2598, 682, 4419, -939, -2601, 253, 511], [-511, 5600, -15180, -3828, 27551, 171, -16021, -428, 3020, 253], [-253, 2272, -1990, -17204, 11099, 27298, -9949, -15768, 2355, 3020]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 11, -30, -8, 59, -1, -40, 1, 11, 0], [0, -1, 11, -30, -8, 59, -1, -40, 1, 11], [-11, 121, -331, -77, 619, -19, -381, 10, 81, 1], [-1, 0, 91, -339, -18, 618, -59, -380, 21, 81], [-81, 890, -2430, -557, 4440, -99, -2622, 22, 511, 21], [-21, 150, 260, -2598, 682, 4419, -939, -2601, 253, 511], [-511, 5600, -15180, -3828, 27551, 171, -16021, -428, 3020, 253], [-253, 2272, -1990, -17204, 11099, 27298, -9949, -15768, 2355, 3020], [-3020, 32967, -88328, -26150, 160976, 8079, -93502, -6929, 17452, 2355]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp189059201 : Fact (Nat.Prime 189059201) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 4
  a' := [4, 1]
  b' := [0, 0, 1]
  k := [1, 0, 4, 3, 4, 1, 1]
  f := [3, 7, -2, 6, 19, 5, -2, 4, 4, 1]
  g := [4, 4, 3, 4, 1]
  h := [4, 2, 0, 4, 2, 1, 1]
  a := [2, 1, 2, 4]
  b := [0, 2, 2, 0, 2, 1, 0, 3, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD189059201 : CertificateDedekindCriterionLists l 189059201 where
  n := 2
  a' := [76592611, 159850965, 186332573, 35920044, 66870835, 135373894, 95555302, 117619597]
  b' := [65275706, 49651896, 177037050, 163706079, 173353449, 20018680, 78179390, 18152173, 154983779]
  k := [72176553, 172307277, 184631237, 138071128, 97974521, 38285460, 140229027, 66114736, 1]
  f := [111080530, 122574325, 844119, 68436903, 109046151, 90097858, 130876274, 142571120, 27277224, 1]
  g := [134618907, 148548279, 1022990, 82938937, 132153435, 109189928, 158609442, 172782469, 33057368, 1]
  h := [156001833, 1]
  a := [42613652, 140047681, 9421927, 24795741, 188844917, 150274407, 101282743, 169755909, 167373654]
  b := [82793727, 26835616, 26862680, 25860345, 155783005, 60736642, 169912359, 118009921, 21685547]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 189059201]
  exp := ![1, 1]
  pdgood := [5, 189059201]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp189059201.out
  a := [-43636732981, 16870719302, 180137281224, -40897267342, -192178360520, 19026931800, 72812596488, -1430442960, -8404952960]
  b := [-4052911726, 23063643503, -2544899252, -46187180846, 6886378101, 32369629796, -2469539220, -9130349300, 143044296, 840495296]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 189059201 T_ofList CD189059201

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

end VoightMaximalOrderD10R182

end TraceEuclidean
