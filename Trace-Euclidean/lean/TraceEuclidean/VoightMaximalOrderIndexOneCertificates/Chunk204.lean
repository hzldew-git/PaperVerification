import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk200
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

namespace VoightMaximalOrderD10R380

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4760523014144, [-1, -4, 6, 28, -3, -46, 0, 26, -4, -4, 1], 1⟩
local notation "l" => [-1, -4, 6, 28, -3, -46, 0, 26, -4, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -6, -28, 3, 46, 0, -26, 4, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -6, -28, 3, 46, 0, -26, 4, 4], ![4, 17, -20, -118, -16, 187, 46, -104, -10, 20]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -6, -28, 3, 46, 0, -26, 4, 4], ![4, 17, -20, -118, -16, 187, 46, -104, -10, 20], ![20, 84, -103, -580, -58, 904, 187, -474, -24, 70]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -6, -28, 3, 46, 0, -26, 4, 4], ![4, 17, -20, -118, -16, 187, 46, -104, -10, 20], ![20, 84, -103, -580, -58, 904, 187, -474, -24, 70], ![70, 300, -336, -2063, -370, 3162, 904, -1633, -194, 256]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -6, -28, 3, 46, 0, -26, 4, 4], ![4, 17, -20, -118, -16, 187, 46, -104, -10, 20], ![20, 84, -103, -580, -58, 904, 187, -474, -24, 70], ![70, 300, -336, -2063, -370, 3162, 904, -1633, -194, 256], ![256, 1094, -1236, -7504, -1295, 11406, 3162, -5752, -609, 830]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -6, -28, 3, 46, 0, -26, 4, 4], ![4, 17, -20, -118, -16, 187, 46, -104, -10, 20], ![20, 84, -103, -580, -58, 904, 187, -474, -24, 70], ![70, 300, -336, -2063, -370, 3162, 904, -1633, -194, 256], ![256, 1094, -1236, -7504, -1295, 11406, 3162, -5752, -609, 830], ![830, 3576, -3886, -24476, -5014, 36885, 11406, -18418, -2432, 2711]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -6, -28, 3, 46, 0, -26, 4, 4], ![4, 17, -20, -118, -16, 187, 46, -104, -10, 20], ![20, 84, -103, -580, -58, 904, 187, -474, -24, 70], ![70, 300, -336, -2063, -370, 3162, 904, -1633, -194, 256], ![256, 1094, -1236, -7504, -1295, 11406, 3162, -5752, -609, 830], ![830, 3576, -3886, -24476, -5014, 36885, 11406, -18418, -2432, 2711], ![2711, 11674, -12690, -79794, -16343, 119692, 36885, -59080, -7574, 8412]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -6, -28, 3, 46, 0, -26, 4, 4], ![4, 17, -20, -118, -16, 187, 46, -104, -10, 20], ![20, 84, -103, -580, -58, 904, 187, -474, -24, 70], ![70, 300, -336, -2063, -370, 3162, 904, -1633, -194, 256], ![256, 1094, -1236, -7504, -1295, 11406, 3162, -5752, -609, 830], ![830, 3576, -3886, -24476, -5014, 36885, 11406, -18418, -2432, 2711], ![2711, 11674, -12690, -79794, -16343, 119692, 36885, -59080, -7574, 8412], ![8412, 36359, -38798, -248226, -54558, 370609, 119692, -181827, -25432, 26074]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -6, -28, 3, 46, 0, -26, 4, 4], ![4, 17, -20, -118, -16, 187, 46, -104, -10, 20], ![20, 84, -103, -580, -58, 904, 187, -474, -24, 70], ![70, 300, -336, -2063, -370, 3162, 904, -1633, -194, 256], ![256, 1094, -1236, -7504, -1295, 11406, 3162, -5752, -609, 830], ![830, 3576, -3886, -24476, -5014, 36885, 11406, -18418, -2432, 2711], ![2711, 11674, -12690, -79794, -16343, 119692, 36885, -59080, -7574, 8412], ![8412, 36359, -38798, -248226, -54558, 370609, 119692, -181827, -25432, 26074], ![26074, 112708, -120085, -768870, -170004, 1144846, 370609, -558232, -77531, 78864]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-70, -20, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-70, -20, -4, -1], [-256, -70, -20, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-70, -20, -4, -1], [-256, -70, -20, -4, -1], [-830, -256, -70, -20, -4, -1]], ![[], [], [], [-1], [-4, -1], [-20, -4, -1], [-70, -20, -4, -1], [-256, -70, -20, -4, -1], [-830, -256, -70, -20, -4, -1], [-2711, -830, -256, -70, -20, -4, -1]], ![[], [], [-1], [-4, -1], [-20, -4, -1], [-70, -20, -4, -1], [-256, -70, -20, -4, -1], [-830, -256, -70, -20, -4, -1], [-2711, -830, -256, -70, -20, -4, -1], [-8412, -2711, -830, -256, -70, -20, -4, -1]], ![[], [-1], [-4, -1], [-20, -4, -1], [-70, -20, -4, -1], [-256, -70, -20, -4, -1], [-830, -256, -70, -20, -4, -1], [-2711, -830, -256, -70, -20, -4, -1], [-8412, -2711, -830, -256, -70, -20, -4, -1], [-26074, -8412, -2711, -830, -256, -70, -20, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -6, -28, 3, 46, 0, -26, 4, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -6, -28, 3, 46, 0, -26, 4, 4], [4, 17, -20, -118, -16, 187, 46, -104, -10, 20]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -6, -28, 3, 46, 0, -26, 4, 4], [4, 17, -20, -118, -16, 187, 46, -104, -10, 20], [20, 84, -103, -580, -58, 904, 187, -474, -24, 70]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -6, -28, 3, 46, 0, -26, 4, 4], [4, 17, -20, -118, -16, 187, 46, -104, -10, 20], [20, 84, -103, -580, -58, 904, 187, -474, -24, 70], [70, 300, -336, -2063, -370, 3162, 904, -1633, -194, 256]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -6, -28, 3, 46, 0, -26, 4, 4], [4, 17, -20, -118, -16, 187, 46, -104, -10, 20], [20, 84, -103, -580, -58, 904, 187, -474, -24, 70], [70, 300, -336, -2063, -370, 3162, 904, -1633, -194, 256], [256, 1094, -1236, -7504, -1295, 11406, 3162, -5752, -609, 830]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -6, -28, 3, 46, 0, -26, 4, 4], [4, 17, -20, -118, -16, 187, 46, -104, -10, 20], [20, 84, -103, -580, -58, 904, 187, -474, -24, 70], [70, 300, -336, -2063, -370, 3162, 904, -1633, -194, 256], [256, 1094, -1236, -7504, -1295, 11406, 3162, -5752, -609, 830], [830, 3576, -3886, -24476, -5014, 36885, 11406, -18418, -2432, 2711]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -6, -28, 3, 46, 0, -26, 4, 4], [4, 17, -20, -118, -16, 187, 46, -104, -10, 20], [20, 84, -103, -580, -58, 904, 187, -474, -24, 70], [70, 300, -336, -2063, -370, 3162, 904, -1633, -194, 256], [256, 1094, -1236, -7504, -1295, 11406, 3162, -5752, -609, 830], [830, 3576, -3886, -24476, -5014, 36885, 11406, -18418, -2432, 2711], [2711, 11674, -12690, -79794, -16343, 119692, 36885, -59080, -7574, 8412]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -6, -28, 3, 46, 0, -26, 4, 4], [4, 17, -20, -118, -16, 187, 46, -104, -10, 20], [20, 84, -103, -580, -58, 904, 187, -474, -24, 70], [70, 300, -336, -2063, -370, 3162, 904, -1633, -194, 256], [256, 1094, -1236, -7504, -1295, 11406, 3162, -5752, -609, 830], [830, 3576, -3886, -24476, -5014, 36885, 11406, -18418, -2432, 2711], [2711, 11674, -12690, -79794, -16343, 119692, 36885, -59080, -7574, 8412], [8412, 36359, -38798, -248226, -54558, 370609, 119692, -181827, -25432, 26074]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -6, -28, 3, 46, 0, -26, 4, 4], [4, 17, -20, -118, -16, 187, 46, -104, -10, 20], [20, 84, -103, -580, -58, 904, 187, -474, -24, 70], [70, 300, -336, -2063, -370, 3162, 904, -1633, -194, 256], [256, 1094, -1236, -7504, -1295, 11406, 3162, -5752, -609, 830], [830, 3576, -3886, -24476, -5014, 36885, 11406, -18418, -2432, 2711], [2711, 11674, -12690, -79794, -16343, 119692, 36885, -59080, -7574, 8412], [8412, 36359, -38798, -248226, -54558, 370609, 119692, -181827, -25432, 26074], [26074, 112708, -120085, -768870, -170004, 1144846, 370609, -558232, -77531, 78864]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp28559 : Fact (Nat.Prime 28559) := fact_iff.2 (by norm_num)
instance hp5087 : Fact (Nat.Prime 5087) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 1]
  b' := [1, 1, 0, 1]
  k := [1]
  f := [1, 2, -2, -14, 2, 24, 0, -12, 2, 2]
  g := [1, 0, 1, 0, 0, 1]
  h := [1, 0, 1, 0, 0, 1]
  a := [1]
  b := []
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD28559 : CertificateDedekindCriterionLists l 28559 where
  n := 2
  a' := [266, 20648, 25721, 27058, 13377, 17692, 28268, 4292]
  b' := [25158, 23267, 14691, 17321, 2399, 14586, 26464, 27361, 12216]
  k := [5212, 20733, 9381, 18488, 2666, 13192, 21079, 26387, 1]
  f := [899, 147, 863, 75, 910, 885, 594, 322, 1043, 1]
  g := [23685, 3851, 22733, 1955, 23973, 23294, 15628, 8469, 27471, 1]
  h := [1084, 1]
  a := [26940, 26454, 18968, 10175, 22576, 24331, 4088, 7664, 17752]
  b := [28026, 425, 19104, 14701, 1107, 25777, 10213, 3499, 10807]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD5087 : CertificateDedekindCriterionLists l 5087 where
  n := 2
  a' := [4514, 4814, 2894, 323, 3868, 4070, 5052, 4680]
  b' := [2727, 1799, 2336, 4801, 1496, 3809, 3633, 2383, 4567]
  k := [4373, 3583, 1317, 1411, 4906, 2552, 105, 626, 1]
  f := [1015, 4730, 728, 4229, 2317, 4477, 4772, 1228, 292, 1]
  g := [1082, 5042, 775, 4508, 2469, 4772, 5086, 1308, 311, 1]
  h := [4772, 1]
  a := [3897, 796, 1448, 1289, 3585, 4070, 4729, 1295, 1890]
  b := [1074, 2328, 1844, 5015, 105, 2362, 1160, 4093, 3197]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 28559, 5087]
  exp := ![2, 1, 1]
  pdgood := [2, 28559, 5087]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp28559.out
    exact hp5087.out
  a := [8435633792, -43965213520, -97305416444, 199332839676, 136862817374, -231066324042, 8561907240, 52526750802, -12536509420]
  b := [-2254188081, -4206894655, 20986384653, 21950753236, -44787052626, -19728821644, 33279463819, -1563298802, -5754135457, 1253650942]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 28559 T_ofList CD28559
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5087 T_ofList CD5087

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

end VoightMaximalOrderD10R380

namespace VoightMaximalOrderD10R385

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4811600403125, [1, -1, -21, 24, 38, -42, -20, 25, 1, -5, 1], 1⟩
local notation "l" => [1, -1, -21, 24, 38, -42, -20, 25, 1, -5, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 21, -24, -38, 42, 20, -25, -1, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 21, -24, -38, 42, 20, -25, -1, 5], ![-5, 4, 106, -99, -214, 172, 142, -105, -30, 24]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 21, -24, -38, 42, 20, -25, -1, 5], ![-5, 4, 106, -99, -214, 172, 142, -105, -30, 24], ![-24, 19, 508, -470, -1011, 794, 652, -458, -129, 90]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 21, -24, -38, 42, 20, -25, -1, 5], ![-5, 4, 106, -99, -214, 172, 142, -105, -30, 24], ![-24, 19, 508, -470, -1011, 794, 652, -458, -129, 90], ![-90, 66, 1909, -1652, -3890, 2769, 2594, -1598, -548, 321]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 21, -24, -38, 42, 20, -25, -1, 5], ![-5, 4, 106, -99, -214, 172, 142, -105, -30, 24], ![-24, 19, 508, -470, -1011, 794, 652, -458, -129, 90], ![-90, 66, 1909, -1652, -3890, 2769, 2594, -1598, -548, 321], ![-321, 231, 6807, -5795, -13850, 9592, 9189, -5431, -1919, 1057]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 21, -24, -38, 42, 20, -25, -1, 5], ![-5, 4, 106, -99, -214, 172, 142, -105, -30, 24], ![-24, 19, 508, -470, -1011, 794, 652, -458, -129, 90], ![-90, 66, 1909, -1652, -3890, 2769, 2594, -1598, -548, 321], ![-321, 231, 6807, -5795, -13850, 9592, 9189, -5431, -1919, 1057], ![-1057, 736, 22428, -18561, -45961, 30544, 30732, -17236, -6488, 3366]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 21, -24, -38, 42, 20, -25, -1, 5], ![-5, 4, 106, -99, -214, 172, 142, -105, -30, 24], ![-24, 19, 508, -470, -1011, 794, 652, -458, -129, 90], ![-90, 66, 1909, -1652, -3890, 2769, 2594, -1598, -548, 321], ![-321, 231, 6807, -5795, -13850, 9592, 9189, -5431, -1919, 1057], ![-1057, 736, 22428, -18561, -45961, 30544, 30732, -17236, -6488, 3366], ![-3366, 2309, 71422, -58356, -146469, 95411, 97864, -53418, -20602, 10342]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 21, -24, -38, 42, 20, -25, -1, 5], ![-5, 4, 106, -99, -214, 172, 142, -105, -30, 24], ![-24, 19, 508, -470, -1011, 794, 652, -458, -129, 90], ![-90, 66, 1909, -1652, -3890, 2769, 2594, -1598, -548, 321], ![-321, 231, 6807, -5795, -13850, 9592, 9189, -5431, -1919, 1057], ![-1057, 736, 22428, -18561, -45961, 30544, 30732, -17236, -6488, 3366], ![-3366, 2309, 71422, -58356, -146469, 95411, 97864, -53418, -20602, 10342], ![-10342, 6976, 219491, -176786, -451352, 287895, 302251, -160686, -63760, 31108]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 21, -24, -38, 42, 20, -25, -1, 5], ![-5, 4, 106, -99, -214, 172, 142, -105, -30, 24], ![-24, 19, 508, -470, -1011, 794, 652, -458, -129, 90], ![-90, 66, 1909, -1652, -3890, 2769, 2594, -1598, -548, 321], ![-321, 231, 6807, -5795, -13850, 9592, 9189, -5431, -1919, 1057], ![-1057, 736, 22428, -18561, -45961, 30544, 30732, -17236, -6488, 3366], ![-3366, 2309, 71422, -58356, -146469, 95411, 97864, -53418, -20602, 10342], ![-10342, 6976, 219491, -176786, -451352, 287895, 302251, -160686, -63760, 31108], ![-31108, 20766, 660244, -527101, -1358890, 855184, 910055, -475449, -191794, 91780]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-5, -1]], ![[], [], [], [], [], [], [], [-1], [-5, -1], [-24, -5, -1]], ![[], [], [], [], [], [], [-1], [-5, -1], [-24, -5, -1], [-90, -24, -5, -1]], ![[], [], [], [], [], [-1], [-5, -1], [-24, -5, -1], [-90, -24, -5, -1], [-321, -90, -24, -5, -1]], ![[], [], [], [], [-1], [-5, -1], [-24, -5, -1], [-90, -24, -5, -1], [-321, -90, -24, -5, -1], [-1057, -321, -90, -24, -5, -1]], ![[], [], [], [-1], [-5, -1], [-24, -5, -1], [-90, -24, -5, -1], [-321, -90, -24, -5, -1], [-1057, -321, -90, -24, -5, -1], [-3366, -1057, -321, -90, -24, -5, -1]], ![[], [], [-1], [-5, -1], [-24, -5, -1], [-90, -24, -5, -1], [-321, -90, -24, -5, -1], [-1057, -321, -90, -24, -5, -1], [-3366, -1057, -321, -90, -24, -5, -1], [-10342, -3366, -1057, -321, -90, -24, -5, -1]], ![[], [-1], [-5, -1], [-24, -5, -1], [-90, -24, -5, -1], [-321, -90, -24, -5, -1], [-1057, -321, -90, -24, -5, -1], [-3366, -1057, -321, -90, -24, -5, -1], [-10342, -3366, -1057, -321, -90, -24, -5, -1], [-31108, -10342, -3366, -1057, -321, -90, -24, -5, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 21, -24, -38, 42, 20, -25, -1, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 21, -24, -38, 42, 20, -25, -1, 5], [-5, 4, 106, -99, -214, 172, 142, -105, -30, 24]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 21, -24, -38, 42, 20, -25, -1, 5], [-5, 4, 106, -99, -214, 172, 142, -105, -30, 24], [-24, 19, 508, -470, -1011, 794, 652, -458, -129, 90]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 21, -24, -38, 42, 20, -25, -1, 5], [-5, 4, 106, -99, -214, 172, 142, -105, -30, 24], [-24, 19, 508, -470, -1011, 794, 652, -458, -129, 90], [-90, 66, 1909, -1652, -3890, 2769, 2594, -1598, -548, 321]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 21, -24, -38, 42, 20, -25, -1, 5], [-5, 4, 106, -99, -214, 172, 142, -105, -30, 24], [-24, 19, 508, -470, -1011, 794, 652, -458, -129, 90], [-90, 66, 1909, -1652, -3890, 2769, 2594, -1598, -548, 321], [-321, 231, 6807, -5795, -13850, 9592, 9189, -5431, -1919, 1057]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 21, -24, -38, 42, 20, -25, -1, 5], [-5, 4, 106, -99, -214, 172, 142, -105, -30, 24], [-24, 19, 508, -470, -1011, 794, 652, -458, -129, 90], [-90, 66, 1909, -1652, -3890, 2769, 2594, -1598, -548, 321], [-321, 231, 6807, -5795, -13850, 9592, 9189, -5431, -1919, 1057], [-1057, 736, 22428, -18561, -45961, 30544, 30732, -17236, -6488, 3366]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 21, -24, -38, 42, 20, -25, -1, 5], [-5, 4, 106, -99, -214, 172, 142, -105, -30, 24], [-24, 19, 508, -470, -1011, 794, 652, -458, -129, 90], [-90, 66, 1909, -1652, -3890, 2769, 2594, -1598, -548, 321], [-321, 231, 6807, -5795, -13850, 9592, 9189, -5431, -1919, 1057], [-1057, 736, 22428, -18561, -45961, 30544, 30732, -17236, -6488, 3366], [-3366, 2309, 71422, -58356, -146469, 95411, 97864, -53418, -20602, 10342]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 21, -24, -38, 42, 20, -25, -1, 5], [-5, 4, 106, -99, -214, 172, 142, -105, -30, 24], [-24, 19, 508, -470, -1011, 794, 652, -458, -129, 90], [-90, 66, 1909, -1652, -3890, 2769, 2594, -1598, -548, 321], [-321, 231, 6807, -5795, -13850, 9592, 9189, -5431, -1919, 1057], [-1057, 736, 22428, -18561, -45961, 30544, 30732, -17236, -6488, 3366], [-3366, 2309, 71422, -58356, -146469, 95411, 97864, -53418, -20602, 10342], [-10342, 6976, 219491, -176786, -451352, 287895, 302251, -160686, -63760, 31108]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 21, -24, -38, 42, 20, -25, -1, 5], [-5, 4, 106, -99, -214, 172, 142, -105, -30, 24], [-24, 19, 508, -470, -1011, 794, 652, -458, -129, 90], [-90, 66, 1909, -1652, -3890, 2769, 2594, -1598, -548, 321], [-321, 231, 6807, -5795, -13850, 9592, 9189, -5431, -1919, 1057], [-1057, 736, 22428, -18561, -45961, 30544, 30732, -17236, -6488, 3366], [-3366, 2309, 71422, -58356, -146469, 95411, 97864, -53418, -20602, 10342], [-10342, 6976, 219491, -176786, -451352, 287895, 302251, -160686, -63760, 31108], [-31108, 20766, 660244, -527101, -1358890, 855184, 910055, -475449, -191794, 91780]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp599 : Fact (Nat.Prime 599) := fact_iff.2 (by norm_num)
instance hp2570471 : Fact (Nat.Prime 2570471) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 3]
  b' := [3, 3, 3, 3, 3]
  k := [1]
  f := [3, 5, 6, 0, -4, 10, 7, -5, 1, 1]
  g := [4, 3, 0, 3, 0, 1]
  h := [4, 3, 0, 3, 0, 1]
  a := [1, 0, 1, 4, 1]
  b := [2, 1, 2, 4, 0, 2, 3, 0, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD599 : CertificateDedekindCriterionLists l 599 where
  n := 2
  a' := [89, 463, 23, 16, 346, 568, 288, 118]
  b' := [364, 366, 85, 397, 554, 242, 295, 61, 120]
  k := [466, 22, 264, 157, 203, 375, 58, 588, 1]
  f := [1, 3, 2, 1, 1, 1, 3, 1, 3, 1]
  g := [200, 532, 215, 136, 167, 130, 549, 25, 591, 1]
  h := [3, 1]
  a := [323, 437, 529, 592, 7, 90, 42, 409, 422]
  b := [232, 484, 86, 454, 594, 43, 198, 340, 177]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2570471 : CertificateDedekindCriterionLists l 2570471 where
  n := 2
  a' := [910227, 812760, 1302774, 703319, 1303674, 1317541, 2409210, 1717374]
  b' := [1587495, 233576, 1097278, 1144833, 2022585, 217592, 718172, 1578044, 1522828]
  k := [1796362, 1690076, 711630, 1921018, 240344, 1593516, 1123133, 2440579, 1]
  f := [635157, 1121635, 191408, 280559, 121441, 832141, 426080, 928592, 640975, 1]
  g := [1209212, 2135368, 364401, 534128, 231199, 1584230, 811170, 1767853, 1220287, 1]
  h := [1350179, 1]
  a := [67187, 1879321, 1388552, 2229423, 2111137, 147266, 2336762, 199373, 1638134]
  b := [723203, 287363, 1069181, 850536, 2045907, 182349, 753396, 866416, 932337]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 599, 2570471]
  exp := ![1, 1, 1]
  pdgood := [5, 599, 2570471]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp599.out
    exact hp2570471.out
  a := [6761752763, -38270118846, -53956535234, 124494855148, 74313646266, -123836217652, -11505253060, 39439688560, -8877029200]
  b := [-936807882, -5685940565, 13676111815, 18226737486, -27006450670, -13927312334, 18717288898, 1302718748, -4387820316, 887702920]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 599 T_ofList CD599
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2570471 T_ofList CD2570471

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

end VoightMaximalOrderD10R385

namespace VoightMaximalOrderD10R389

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4830104556973, [1, -12, 22, 26, -49, -22, 35, 8, -10, -1, 1], 1⟩
local notation "l" => [1, -12, 22, 26, -49, -22, 35, 8, -10, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 12, -22, -26, 49, 22, -35, -8, 10, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 12, -22, -26, 49, 22, -35, -8, 10, 1], ![-1, 11, -10, -48, 23, 71, -13, -43, 2, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 12, -22, -26, 49, 22, -35, -8, 10, 1], ![-1, 11, -10, -48, 23, 71, -13, -43, 2, 11], ![-11, 131, -231, -296, 491, 265, -314, -101, 67, 13]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 12, -22, -26, 49, 22, -35, -8, 10, 1], ![-1, 11, -10, -48, 23, 71, -13, -43, 2, 11], ![-11, 131, -231, -296, 491, 265, -314, -101, 67, 13], ![-13, 145, -155, -569, 341, 777, -190, -418, 29, 80]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 12, -22, -26, 49, 22, -35, -8, 10, 1], ![-1, 11, -10, -48, 23, 71, -13, -43, 2, 11], ![-11, 131, -231, -296, 491, 265, -314, -101, 67, 13], ![-13, 145, -155, -569, 341, 777, -190, -418, 29, 80], ![-80, 947, -1615, -2235, 3351, 2101, -2023, -830, 382, 109]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 12, -22, -26, 49, 22, -35, -8, 10, 1], ![-1, 11, -10, -48, 23, 71, -13, -43, 2, 11], ![-11, 131, -231, -296, 491, 265, -314, -101, 67, 13], ![-13, 145, -155, -569, 341, 777, -190, -418, 29, 80], ![-80, 947, -1615, -2235, 3351, 2101, -2023, -830, 382, 109], ![-109, 1228, -1451, -4449, 3106, 5749, -1714, -2895, 260, 491]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 12, -22, -26, 49, 22, -35, -8, 10, 1], ![-1, 11, -10, -48, 23, 71, -13, -43, 2, 11], ![-11, 131, -231, -296, 491, 265, -314, -101, 67, 13], ![-13, 145, -155, -569, 341, 777, -190, -418, 29, 80], ![-80, 947, -1615, -2235, 3351, 2101, -2023, -830, 382, 109], ![-109, 1228, -1451, -4449, 3106, 5749, -1714, -2895, 260, 491], ![-491, 5783, -9574, -14217, 19610, 13908, -11436, -5642, 2015, 751]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 12, -22, -26, 49, 22, -35, -8, 10, 1], ![-1, 11, -10, -48, 23, 71, -13, -43, 2, 11], ![-11, 131, -231, -296, 491, 265, -314, -101, 67, 13], ![-13, 145, -155, -569, 341, 777, -190, -418, 29, 80], ![-80, 947, -1615, -2235, 3351, 2101, -2023, -830, 382, 109], ![-109, 1228, -1451, -4449, 3106, 5749, -1714, -2895, 260, 491], ![-491, 5783, -9574, -14217, 19610, 13908, -11436, -5642, 2015, 751], ![-751, 8521, -10739, -29100, 22582, 36132, -12377, -17444, 1868, 2766]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 12, -22, -26, 49, 22, -35, -8, 10, 1], ![-1, 11, -10, -48, 23, 71, -13, -43, 2, 11], ![-11, 131, -231, -296, 491, 265, -314, -101, 67, 13], ![-13, 145, -155, -569, 341, 777, -190, -418, 29, 80], ![-80, 947, -1615, -2235, 3351, 2101, -2023, -830, 382, 109], ![-109, 1228, -1451, -4449, 3106, 5749, -1714, -2895, 260, 491], ![-491, 5783, -9574, -14217, 19610, 13908, -11436, -5642, 2015, 751], ![-751, 8521, -10739, -29100, 22582, 36132, -12377, -17444, 1868, 2766], ![-2766, 32441, -52331, -82655, 106434, 83434, -60678, -34505, 10216, 4634]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-80, -13, -11, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-80, -13, -11, -1, -1], [-109, -80, -13, -11, -1, -1]], ![[], [], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-80, -13, -11, -1, -1], [-109, -80, -13, -11, -1, -1], [-491, -109, -80, -13, -11, -1, -1]], ![[], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-80, -13, -11, -1, -1], [-109, -80, -13, -11, -1, -1], [-491, -109, -80, -13, -11, -1, -1], [-751, -491, -109, -80, -13, -11, -1, -1]], ![[], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-80, -13, -11, -1, -1], [-109, -80, -13, -11, -1, -1], [-491, -109, -80, -13, -11, -1, -1], [-751, -491, -109, -80, -13, -11, -1, -1], [-2766, -751, -491, -109, -80, -13, -11, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 12, -22, -26, 49, 22, -35, -8, 10, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 12, -22, -26, 49, 22, -35, -8, 10, 1], [-1, 11, -10, -48, 23, 71, -13, -43, 2, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 12, -22, -26, 49, 22, -35, -8, 10, 1], [-1, 11, -10, -48, 23, 71, -13, -43, 2, 11], [-11, 131, -231, -296, 491, 265, -314, -101, 67, 13]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 12, -22, -26, 49, 22, -35, -8, 10, 1], [-1, 11, -10, -48, 23, 71, -13, -43, 2, 11], [-11, 131, -231, -296, 491, 265, -314, -101, 67, 13], [-13, 145, -155, -569, 341, 777, -190, -418, 29, 80]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 12, -22, -26, 49, 22, -35, -8, 10, 1], [-1, 11, -10, -48, 23, 71, -13, -43, 2, 11], [-11, 131, -231, -296, 491, 265, -314, -101, 67, 13], [-13, 145, -155, -569, 341, 777, -190, -418, 29, 80], [-80, 947, -1615, -2235, 3351, 2101, -2023, -830, 382, 109]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 12, -22, -26, 49, 22, -35, -8, 10, 1], [-1, 11, -10, -48, 23, 71, -13, -43, 2, 11], [-11, 131, -231, -296, 491, 265, -314, -101, 67, 13], [-13, 145, -155, -569, 341, 777, -190, -418, 29, 80], [-80, 947, -1615, -2235, 3351, 2101, -2023, -830, 382, 109], [-109, 1228, -1451, -4449, 3106, 5749, -1714, -2895, 260, 491]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 12, -22, -26, 49, 22, -35, -8, 10, 1], [-1, 11, -10, -48, 23, 71, -13, -43, 2, 11], [-11, 131, -231, -296, 491, 265, -314, -101, 67, 13], [-13, 145, -155, -569, 341, 777, -190, -418, 29, 80], [-80, 947, -1615, -2235, 3351, 2101, -2023, -830, 382, 109], [-109, 1228, -1451, -4449, 3106, 5749, -1714, -2895, 260, 491], [-491, 5783, -9574, -14217, 19610, 13908, -11436, -5642, 2015, 751]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 12, -22, -26, 49, 22, -35, -8, 10, 1], [-1, 11, -10, -48, 23, 71, -13, -43, 2, 11], [-11, 131, -231, -296, 491, 265, -314, -101, 67, 13], [-13, 145, -155, -569, 341, 777, -190, -418, 29, 80], [-80, 947, -1615, -2235, 3351, 2101, -2023, -830, 382, 109], [-109, 1228, -1451, -4449, 3106, 5749, -1714, -2895, 260, 491], [-491, 5783, -9574, -14217, 19610, 13908, -11436, -5642, 2015, 751], [-751, 8521, -10739, -29100, 22582, 36132, -12377, -17444, 1868, 2766]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 12, -22, -26, 49, 22, -35, -8, 10, 1], [-1, 11, -10, -48, 23, 71, -13, -43, 2, 11], [-11, 131, -231, -296, 491, 265, -314, -101, 67, 13], [-13, 145, -155, -569, 341, 777, -190, -418, 29, 80], [-80, 947, -1615, -2235, 3351, 2101, -2023, -830, 382, 109], [-109, 1228, -1451, -4449, 3106, 5749, -1714, -2895, 260, 491], [-491, 5783, -9574, -14217, 19610, 13908, -11436, -5642, 2015, 751], [-751, 8521, -10739, -29100, 22582, 36132, -12377, -17444, 1868, 2766], [-2766, 32441, -52331, -82655, 106434, 83434, -60678, -34505, 10216, 4634]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp17 : Fact (Nat.Prime 17) := fact_iff.2 (by norm_num)
instance hp16713164557 : Fact (Nat.Prime 16713164557) := fact_iff.2 (by norm_num)

def CD17 : CertificateDedekindCriterionLists l 17 where
  n := 2
  a' := [7, 9, 10, 12, 2, 14, 3]
  b' := [3, 3, 2, 1, 1, 14, 16, 6]
  k := [9, 0, 7, 13, 3, 3, 1]
  f := [1, 9, 13, 4, 20, 19, 7, 3, 2, 1]
  g := [3, 16, 0, 13, 16, 8, 3, 1, 1]
  h := [6, 15, 1]
  a := [8, 8, 10, 11, 0, 13, 7, 12]
  b := [4, 16, 2, 12, 11, 13, 9, 15, 5]
  c := [11]
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD16713164557 : CertificateDedekindCriterionLists l 16713164557 where
  n := 2
  a' := [7063620039, 4257273065, 13988253888, 3008465729, 7086618816, 2901757642, 16703275046, 8212511598]
  b' := [12028883995, 4246140926, 4073413517, 12774894754, 8619894413, 3883832855, 15729130286, 14837923180, 10229608416]
  k := [9525660490, 5262918273, 7245365392, 2814969211, 3444049947, 12535655783, 7266640864, 9801374131, 1]
  f := [7963781228, 4014406544, 7020073411, 3940612211, 5391027411, 1046451705, 8500572364, 8432385433, 3463692077, 1]
  g := [11267745167, 5679878519, 9932517730, 5575468853, 7627623275, 1480597068, 12027236865, 11930760964, 4900687065, 1]
  h := [11812477491, 1]
  a := [6321655205, 1312079898, 1365445347, 12897155092, 2220475989, 14703012308, 2602851973, 1923933151, 5281890882]
  b := [92941400, 9824428977, 5266311953, 13867609638, 6726935605, 5140396550, 13668661526, 3912176288, 11431273675]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![17, 16713164557]
  exp := ![1, 1]
  pdgood := [17, 16713164557]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp17.out
    exact hp16713164557.out
  a := [-787026190063, -516224205340, 4184000447136, 2019252734056, -5393006679375, -1500436255630, 2313981519353, 286931122106, -314546637640]
  b := [-89262498961, 416711676761, 369746132363, -1145047973584, -486008495803, 940084249261, 224313284759, -294269087981, -31838578587, 31454663764]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 17 T_ofList CD17
    exact satisfiesDedekindCriterion_of_certificate_lists T l 16713164557 T_ofList CD16713164557

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

end VoightMaximalOrderD10R389

namespace VoightMaximalOrderD10R391

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4837216932845, [-1, -3, 9, 19, -24, -32, 26, 15, -9, -2, 1], 1⟩
local notation "l" => [-1, -3, 9, 19, -24, -32, 26, 15, -9, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -9, -19, 24, 32, -26, -15, 9, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -9, -19, 24, 32, -26, -15, 9, 2], ![2, 7, -15, -47, 29, 88, -20, -56, 3, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -9, -19, 24, 32, -26, -15, 9, 2], ![2, 7, -15, -47, 29, 88, -20, -56, 3, 13], ![13, 41, -110, -262, 265, 445, -250, -215, 61, 29]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -9, -19, 24, 32, -26, -15, 9, 2], ![2, 7, -15, -47, 29, 88, -20, -56, 3, 13], ![13, 41, -110, -262, 265, 445, -250, -215, 61, 29], ![29, 100, -220, -661, 434, 1193, -309, -685, 46, 119]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -9, -19, 24, 32, -26, -15, 9, 2], ![2, 7, -15, -47, 29, 88, -20, -56, 3, 13], ![13, 41, -110, -262, 265, 445, -250, -215, 61, 29], ![29, 100, -220, -661, 434, 1193, -309, -685, 46, 119], ![119, 386, -971, -2481, 2195, 4242, -1901, -2094, 386, 284]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -9, -19, 24, 32, -26, -15, 9, 2], ![2, 7, -15, -47, 29, 88, -20, -56, 3, 13], ![13, 41, -110, -262, 265, 445, -250, -215, 61, 29], ![29, 100, -220, -661, 434, 1193, -309, -685, 46, 119], ![119, 386, -971, -2481, 2195, 4242, -1901, -2094, 386, 284], ![284, 971, -2170, -6367, 4335, 11283, -3142, -6161, 462, 954]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -9, -19, 24, 32, -26, -15, 9, 2], ![2, 7, -15, -47, 29, 88, -20, -56, 3, 13], ![13, 41, -110, -262, 265, 445, -250, -215, 61, 29], ![29, 100, -220, -661, 434, 1193, -309, -685, 46, 119], ![119, 386, -971, -2481, 2195, 4242, -1901, -2094, 386, 284], ![284, 971, -2170, -6367, 4335, 11283, -3142, -6161, 462, 954], ![954, 3146, -7615, -20296, 16529, 34863, -13521, -17452, 2425, 2370]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -9, -19, 24, 32, -26, -15, 9, 2], ![2, 7, -15, -47, 29, 88, -20, -56, 3, 13], ![13, 41, -110, -262, 265, 445, -250, -215, 61, 29], ![29, 100, -220, -661, 434, 1193, -309, -685, 46, 119], ![119, 386, -971, -2481, 2195, 4242, -1901, -2094, 386, 284], ![284, 971, -2170, -6367, 4335, 11283, -3142, -6161, 462, 954], ![954, 3146, -7615, -20296, 16529, 34863, -13521, -17452, 2425, 2370], ![2370, 8064, -18184, -52645, 36584, 92369, -26757, -49071, 3878, 7165]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -9, -19, 24, 32, -26, -15, 9, 2], ![2, 7, -15, -47, 29, 88, -20, -56, 3, 13], ![13, 41, -110, -262, 265, 445, -250, -215, 61, 29], ![29, 100, -220, -661, 434, 1193, -309, -685, 46, 119], ![119, 386, -971, -2481, 2195, 4242, -1901, -2094, 386, 284], ![284, 971, -2170, -6367, 4335, 11283, -3142, -6161, 462, 954], ![954, 3146, -7615, -20296, 16529, 34863, -13521, -17452, 2425, 2370], ![2370, 8064, -18184, -52645, 36584, 92369, -26757, -49071, 3878, 7165], ![7165, 23865, -56421, -154319, 119315, 265864, -93921, -134232, 15414, 18208]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-29, -13, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-29, -13, -2, -1], [-119, -29, -13, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-29, -13, -2, -1], [-119, -29, -13, -2, -1], [-284, -119, -29, -13, -2, -1]], ![[], [], [], [-1], [-2, -1], [-13, -2, -1], [-29, -13, -2, -1], [-119, -29, -13, -2, -1], [-284, -119, -29, -13, -2, -1], [-954, -284, -119, -29, -13, -2, -1]], ![[], [], [-1], [-2, -1], [-13, -2, -1], [-29, -13, -2, -1], [-119, -29, -13, -2, -1], [-284, -119, -29, -13, -2, -1], [-954, -284, -119, -29, -13, -2, -1], [-2370, -954, -284, -119, -29, -13, -2, -1]], ![[], [-1], [-2, -1], [-13, -2, -1], [-29, -13, -2, -1], [-119, -29, -13, -2, -1], [-284, -119, -29, -13, -2, -1], [-954, -284, -119, -29, -13, -2, -1], [-2370, -954, -284, -119, -29, -13, -2, -1], [-7165, -2370, -954, -284, -119, -29, -13, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -9, -19, 24, 32, -26, -15, 9, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -9, -19, 24, 32, -26, -15, 9, 2], [2, 7, -15, -47, 29, 88, -20, -56, 3, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -9, -19, 24, 32, -26, -15, 9, 2], [2, 7, -15, -47, 29, 88, -20, -56, 3, 13], [13, 41, -110, -262, 265, 445, -250, -215, 61, 29]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -9, -19, 24, 32, -26, -15, 9, 2], [2, 7, -15, -47, 29, 88, -20, -56, 3, 13], [13, 41, -110, -262, 265, 445, -250, -215, 61, 29], [29, 100, -220, -661, 434, 1193, -309, -685, 46, 119]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -9, -19, 24, 32, -26, -15, 9, 2], [2, 7, -15, -47, 29, 88, -20, -56, 3, 13], [13, 41, -110, -262, 265, 445, -250, -215, 61, 29], [29, 100, -220, -661, 434, 1193, -309, -685, 46, 119], [119, 386, -971, -2481, 2195, 4242, -1901, -2094, 386, 284]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -9, -19, 24, 32, -26, -15, 9, 2], [2, 7, -15, -47, 29, 88, -20, -56, 3, 13], [13, 41, -110, -262, 265, 445, -250, -215, 61, 29], [29, 100, -220, -661, 434, 1193, -309, -685, 46, 119], [119, 386, -971, -2481, 2195, 4242, -1901, -2094, 386, 284], [284, 971, -2170, -6367, 4335, 11283, -3142, -6161, 462, 954]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -9, -19, 24, 32, -26, -15, 9, 2], [2, 7, -15, -47, 29, 88, -20, -56, 3, 13], [13, 41, -110, -262, 265, 445, -250, -215, 61, 29], [29, 100, -220, -661, 434, 1193, -309, -685, 46, 119], [119, 386, -971, -2481, 2195, 4242, -1901, -2094, 386, 284], [284, 971, -2170, -6367, 4335, 11283, -3142, -6161, 462, 954], [954, 3146, -7615, -20296, 16529, 34863, -13521, -17452, 2425, 2370]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -9, -19, 24, 32, -26, -15, 9, 2], [2, 7, -15, -47, 29, 88, -20, -56, 3, 13], [13, 41, -110, -262, 265, 445, -250, -215, 61, 29], [29, 100, -220, -661, 434, 1193, -309, -685, 46, 119], [119, 386, -971, -2481, 2195, 4242, -1901, -2094, 386, 284], [284, 971, -2170, -6367, 4335, 11283, -3142, -6161, 462, 954], [954, 3146, -7615, -20296, 16529, 34863, -13521, -17452, 2425, 2370], [2370, 8064, -18184, -52645, 36584, 92369, -26757, -49071, 3878, 7165]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -9, -19, 24, 32, -26, -15, 9, 2], [2, 7, -15, -47, 29, 88, -20, -56, 3, 13], [13, 41, -110, -262, 265, 445, -250, -215, 61, 29], [29, 100, -220, -661, 434, 1193, -309, -685, 46, 119], [119, 386, -971, -2481, 2195, 4242, -1901, -2094, 386, 284], [284, 971, -2170, -6367, 4335, 11283, -3142, -6161, 462, 954], [954, 3146, -7615, -20296, 16529, 34863, -13521, -17452, 2425, 2370], [2370, 8064, -18184, -52645, 36584, 92369, -26757, -49071, 3878, 7165], [7165, 23865, -56421, -154319, 119315, 265864, -93921, -134232, 15414, 18208]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp89417 : Fact (Nat.Prime 89417) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 2, 2, 4, 3, 0, 1, 2]
  b' := [0, 0, 4, 2, 2, 0, 3, 2, 2]
  k := [4, 4, 2, 1, 2, 3, 3, 1, 1]
  f := [1, 2, -1, -3, 6, 7, -5, -2, 3, 1]
  g := [4, 3, 1, 3, 3, 0, 1, 4, 2, 1]
  h := [1, 1]
  a := [2, 2, 1, 2, 1, 0, 1, 0, 3]
  b := [1, 4, 1, 1, 4, 1, 3, 2, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [7, 7, 0, 3, 7, 8, 10]
  b' := [9, 3, 10, 4, 5, 10, 4, 7]
  k := [6, 6, 9, 2, 1, 4, 1]
  f := [3, 9, 9, 7, 7, 10, 10, 6, 3, 1]
  g := [4, 8, 5, 6, 0, 9, 8, 1, 1]
  h := [8, 8, 1]
  a := [7, 1, 2, 2, 5, 10, 6, 8]
  b := [6, 10, 8, 8, 1, 10, 10, 0, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD89417 : CertificateDedekindCriterionLists l 89417 where
  n := 2
  a' := [54071, 86440, 3868, 81816, 68861, 3850, 58538]
  b' := [85141, 13294, 49493, 19353, 15864, 40425, 72059, 15037]
  k := [1247, 57831, 62945, 35765, 543, 16206, 1]
  f := [6920, 33410, 77862, 74089, 29188, 57555, 69974, 66439, 7369, 1]
  g := [12993, 40546, 76964, 7698, 41658, 36937, 68315, 8102, 1]
  h := [47623, 81313, 1]
  a := [11907, 1862, 27416, 33628, 87434, 76661, 52200, 9460]
  b := [1201, 14014, 28745, 55836, 71933, 9112, 22014, 86288, 79957]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 11, 89417]
  exp := ![1, 1, 1]
  pdgood := [5, 11, 89417]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp11.out
    exact hp89417.out
  a := [18778069, -187707708, -40022628, 934368916, -428165171, -652440412, 299672462, 113268034, -49932280]
  b := [-7898668, -3600841, 85703053, -17069316, -188323796, 81194315, 91568993, -38487258, -12325449, 4993228]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 89417 T_ofList CD89417

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

end VoightMaximalOrderD10R391

end TraceEuclidean
