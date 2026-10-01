import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk209
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

namespace VoightMaximalOrderD10R503

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5709052910848, [1, 1, -17, 10, 41, -31, -27, 26, 1, -5, 1], 1⟩
local notation "l" => [1, 1, -17, 10, 41, -31, -27, 26, 1, -5, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -1, 17, -10, -41, 31, 27, -26, -1, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -1, 17, -10, -41, 31, 27, -26, -1, 5], ![-5, -6, 84, -33, -215, 114, 166, -103, -31, 24]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -1, 17, -10, -41, 31, 27, -26, -1, 5], ![-5, -6, 84, -33, -215, 114, 166, -103, -31, 24], ![-24, -29, 402, -156, -1017, 529, 762, -458, -127, 89]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -1, 17, -10, -41, 31, 27, -26, -1, 5], ![-5, -6, 84, -33, -215, 114, 166, -103, -31, 24], ![-24, -29, 402, -156, -1017, 529, 762, -458, -127, 89], ![-89, -113, 1484, -488, -3805, 1742, 2932, -1552, -547, 318]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -1, 17, -10, -41, 31, 27, -26, -1, 5], ![-5, -6, 84, -33, -215, 114, 166, -103, -31, 24], ![-24, -29, 402, -156, -1017, 529, 762, -458, -127, 89], ![-89, -113, 1484, -488, -3805, 1742, 2932, -1552, -547, 318], ![-318, -407, 5293, -1696, -13526, 6053, 10328, -5336, -1870, 1043]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -1, 17, -10, -41, 31, 27, -26, -1, 5], ![-5, -6, 84, -33, -215, 114, 166, -103, -31, 24], ![-24, -29, 402, -156, -1017, 529, 762, -458, -127, 89], ![-89, -113, 1484, -488, -3805, 1742, 2932, -1552, -547, 318], ![-318, -407, 5293, -1696, -13526, 6053, 10328, -5336, -1870, 1043], ![-1043, -1361, 17324, -5137, -44459, 18807, 34214, -16790, -6379, 3345]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -1, 17, -10, -41, 31, 27, -26, -1, 5], ![-5, -6, 84, -33, -215, 114, 166, -103, -31, 24], ![-24, -29, 402, -156, -1017, 529, 762, -458, -127, 89], ![-89, -113, 1484, -488, -3805, 1742, 2932, -1552, -547, 318], ![-318, -407, 5293, -1696, -13526, 6053, 10328, -5336, -1870, 1043], ![-1043, -1361, 17324, -5137, -44459, 18807, 34214, -16790, -6379, 3345], ![-3345, -4388, 55504, -16126, -142282, 59236, 109122, -52756, -20135, 10346]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -1, 17, -10, -41, 31, 27, -26, -1, 5], ![-5, -6, 84, -33, -215, 114, 166, -103, -31, 24], ![-24, -29, 402, -156, -1017, 529, 762, -458, -127, 89], ![-89, -113, 1484, -488, -3805, 1742, 2932, -1552, -547, 318], ![-318, -407, 5293, -1696, -13526, 6053, 10328, -5336, -1870, 1043], ![-1043, -1361, 17324, -5137, -44459, 18807, 34214, -16790, -6379, 3345], ![-3345, -4388, 55504, -16126, -142282, 59236, 109122, -52756, -20135, 10346], ![-10346, -13691, 171494, -47956, -440312, 178444, 338578, -159874, -63102, 31595]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -1, 17, -10, -41, 31, 27, -26, -1, 5], ![-5, -6, 84, -33, -215, 114, 166, -103, -31, 24], ![-24, -29, 402, -156, -1017, 529, 762, -458, -127, 89], ![-89, -113, 1484, -488, -3805, 1742, 2932, -1552, -547, 318], ![-318, -407, 5293, -1696, -13526, 6053, 10328, -5336, -1870, 1043], ![-1043, -1361, 17324, -5137, -44459, 18807, 34214, -16790, -6379, 3345], ![-3345, -4388, 55504, -16126, -142282, 59236, 109122, -52756, -20135, 10346], ![-10346, -13691, 171494, -47956, -440312, 178444, 338578, -159874, -63102, 31595], ![-31595, -41941, 523424, -144456, -1343351, 539133, 1031509, -482892, -191469, 94873]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-5, -1]], ![[], [], [], [], [], [], [], [-1], [-5, -1], [-24, -5, -1]], ![[], [], [], [], [], [], [-1], [-5, -1], [-24, -5, -1], [-89, -24, -5, -1]], ![[], [], [], [], [], [-1], [-5, -1], [-24, -5, -1], [-89, -24, -5, -1], [-318, -89, -24, -5, -1]], ![[], [], [], [], [-1], [-5, -1], [-24, -5, -1], [-89, -24, -5, -1], [-318, -89, -24, -5, -1], [-1043, -318, -89, -24, -5, -1]], ![[], [], [], [-1], [-5, -1], [-24, -5, -1], [-89, -24, -5, -1], [-318, -89, -24, -5, -1], [-1043, -318, -89, -24, -5, -1], [-3345, -1043, -318, -89, -24, -5, -1]], ![[], [], [-1], [-5, -1], [-24, -5, -1], [-89, -24, -5, -1], [-318, -89, -24, -5, -1], [-1043, -318, -89, -24, -5, -1], [-3345, -1043, -318, -89, -24, -5, -1], [-10346, -3345, -1043, -318, -89, -24, -5, -1]], ![[], [-1], [-5, -1], [-24, -5, -1], [-89, -24, -5, -1], [-318, -89, -24, -5, -1], [-1043, -318, -89, -24, -5, -1], [-3345, -1043, -318, -89, -24, -5, -1], [-10346, -3345, -1043, -318, -89, -24, -5, -1], [-31595, -10346, -3345, -1043, -318, -89, -24, -5, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -1, 17, -10, -41, 31, 27, -26, -1, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -1, 17, -10, -41, 31, 27, -26, -1, 5], [-5, -6, 84, -33, -215, 114, 166, -103, -31, 24]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -1, 17, -10, -41, 31, 27, -26, -1, 5], [-5, -6, 84, -33, -215, 114, 166, -103, -31, 24], [-24, -29, 402, -156, -1017, 529, 762, -458, -127, 89]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -1, 17, -10, -41, 31, 27, -26, -1, 5], [-5, -6, 84, -33, -215, 114, 166, -103, -31, 24], [-24, -29, 402, -156, -1017, 529, 762, -458, -127, 89], [-89, -113, 1484, -488, -3805, 1742, 2932, -1552, -547, 318]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -1, 17, -10, -41, 31, 27, -26, -1, 5], [-5, -6, 84, -33, -215, 114, 166, -103, -31, 24], [-24, -29, 402, -156, -1017, 529, 762, -458, -127, 89], [-89, -113, 1484, -488, -3805, 1742, 2932, -1552, -547, 318], [-318, -407, 5293, -1696, -13526, 6053, 10328, -5336, -1870, 1043]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -1, 17, -10, -41, 31, 27, -26, -1, 5], [-5, -6, 84, -33, -215, 114, 166, -103, -31, 24], [-24, -29, 402, -156, -1017, 529, 762, -458, -127, 89], [-89, -113, 1484, -488, -3805, 1742, 2932, -1552, -547, 318], [-318, -407, 5293, -1696, -13526, 6053, 10328, -5336, -1870, 1043], [-1043, -1361, 17324, -5137, -44459, 18807, 34214, -16790, -6379, 3345]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -1, 17, -10, -41, 31, 27, -26, -1, 5], [-5, -6, 84, -33, -215, 114, 166, -103, -31, 24], [-24, -29, 402, -156, -1017, 529, 762, -458, -127, 89], [-89, -113, 1484, -488, -3805, 1742, 2932, -1552, -547, 318], [-318, -407, 5293, -1696, -13526, 6053, 10328, -5336, -1870, 1043], [-1043, -1361, 17324, -5137, -44459, 18807, 34214, -16790, -6379, 3345], [-3345, -4388, 55504, -16126, -142282, 59236, 109122, -52756, -20135, 10346]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -1, 17, -10, -41, 31, 27, -26, -1, 5], [-5, -6, 84, -33, -215, 114, 166, -103, -31, 24], [-24, -29, 402, -156, -1017, 529, 762, -458, -127, 89], [-89, -113, 1484, -488, -3805, 1742, 2932, -1552, -547, 318], [-318, -407, 5293, -1696, -13526, 6053, 10328, -5336, -1870, 1043], [-1043, -1361, 17324, -5137, -44459, 18807, 34214, -16790, -6379, 3345], [-3345, -4388, 55504, -16126, -142282, 59236, 109122, -52756, -20135, 10346], [-10346, -13691, 171494, -47956, -440312, 178444, 338578, -159874, -63102, 31595]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -1, 17, -10, -41, 31, 27, -26, -1, 5], [-5, -6, 84, -33, -215, 114, 166, -103, -31, 24], [-24, -29, 402, -156, -1017, 529, 762, -458, -127, 89], [-89, -113, 1484, -488, -3805, 1742, 2932, -1552, -547, 318], [-318, -407, 5293, -1696, -13526, 6053, 10328, -5336, -1870, 1043], [-1043, -1361, 17324, -5137, -44459, 18807, 34214, -16790, -6379, 3345], [-3345, -4388, 55504, -16126, -142282, 59236, 109122, -52756, -20135, 10346], [-10346, -13691, 171494, -47956, -440312, 178444, 338578, -159874, -63102, 31595], [-31595, -41941, 523424, -144456, -1343351, 539133, 1031509, -482892, -191469, 94873]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp23 : Fact (Nat.Prime 23) := fact_iff.2 (by norm_num)
instance hp563 : Fact (Nat.Prime 563) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 5
  a' := []
  b' := [1]
  k := [1]
  f := [0, 0, 9, -5, -20, 16, 14, -13, 0, 3]
  g := [1, 1, 1]
  h := [1, 0, 0, 0, 1, 0, 0, 0, 1]
  a := [1]
  b := [1, 1, 1, 1, 0, 1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD7 : CertificateDedekindCriterionLists l 7 where
  n := 2
  a' := [0, 1, 2, 5, 1, 1, 0, 4]
  b' := [1, 0, 1, 1, 4, 3, 6, 1, 5]
  k := [4, 6, 3, 0, 5, 1, 2, 3, 1]
  f := [2, 1, 3, 0, -5, 5, 4, -2, 3, 2]
  g := [5, 1, 1, 3, 1, 1, 0, 4, 6, 1]
  h := [3, 1]
  a := [5, 1, 2, 4, 6, 4, 4, 2, 4]
  b := [1, 4, 2, 4, 1, 3, 2, 4, 6]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD19 : CertificateDedekindCriterionLists l 19 where
  n := 2
  a' := [7, 6, 3, 1, 10, 5, 10, 8]
  b' := [7, 17, 12, 9, 15, 4, 10, 12, 16]
  k := [4, 1, 15, 1, 13, 0, 11, 15, 1]
  f := [8, 7, 3, 2, 0, 8, 4, 5, 3, 1]
  g := [17, 13, 3, 5, 4, 13, 4, 13, 5, 1]
  h := [9, 1]
  a := [1, 6, 15, 1, 12, 17, 12, 11, 10]
  b := [13, 17, 13, 0, 16, 15, 9, 9, 9]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD23 : CertificateDedekindCriterionLists l 23 where
  n := 2
  a' := [20, 8, 21, 19, 5, 1, 15]
  b' := [2, 8, 6, 6, 12, 1, 8, 1]
  k := [1, 3, 9, 21, 15, 20, 1]
  f := [0, 1, 3, 7, 13, 5, 5, 18, 19, 2]
  g := [1, 2, 7, 15, 3, 3, 19, 19, 1]
  h := [1, 22, 1]
  a := [3, 5, 3, 6, 2, 16, 2, 10]
  b := [1, 18, 12, 3, 8, 19, 0, 2, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD563 : CertificateDedekindCriterionLists l 563 where
  n := 2
  a' := [28, 250, 192, 300, 268, 174, 505]
  b' := [268, 108, 149, 357, 464, 445, 45, 148]
  k := [251, 455, 72, 71, 530, 560, 1]
  f := [153, 576, 650, 466, 706, 581, 484, 558, 559, 2]
  g := [292, 543, 205, 497, 400, 345, 265, 559, 1]
  h := [295, 562, 1]
  a := [289, 283, 385, 225, 220, 125, 439, 383]
  b := [427, 246, 238, 561, 408, 299, 284, 405, 360]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 5
  p := ![2, 7, 19, 23, 563]
  exp := ![1, 1, 1, 1, 1]
  pdgood := [2, 7, 19, 23, 563]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp7.out
    exact hp19.out
    exact hp23.out
    exact hp563.out
  a := [5802102, -76348446, -106566133, 254529734, 134771773, -269050592, 14027904, 64847680, -16211920]
  b := [-2357668, -9614368, 25391841, 34502983, -52663486, -24982119, 39238507, -1483850, -7295364, 1621192]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19 T_ofList CD19
    exact satisfiesDedekindCriterion_of_certificate_lists T l 23 T_ofList CD23
    exact satisfiesDedekindCriterion_of_certificate_lists T l 563 T_ofList CD563

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

end VoightMaximalOrderD10R503

namespace VoightMaximalOrderD10R505

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5727296403125, [1, -5, -4, 27, 8, -41, -2, 23, -3, -4, 1], 1⟩
local notation "l" => [1, -5, -4, 27, 8, -41, -2, 23, -3, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 4, -27, -8, 41, 2, -23, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 4, -27, -8, 41, 2, -23, 3, 4], ![-4, 19, 21, -104, -59, 156, 49, -90, -11, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 4, -27, -8, 41, 2, -23, 3, 4], ![-4, 19, 21, -104, -59, 156, 49, -90, -11, 19], ![-19, 91, 95, -492, -256, 720, 194, -388, -33, 65]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 4, -27, -8, 41, 2, -23, 3, 4], ![-4, 19, 21, -104, -59, 156, 49, -90, -11, 19], ![-19, 91, 95, -492, -256, 720, 194, -388, -33, 65], ![-65, 306, 351, -1660, -1012, 2409, 850, -1301, -193, 227]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 4, -27, -8, 41, 2, -23, 3, 4], ![-4, 19, 21, -104, -59, 156, 49, -90, -11, 19], ![-19, 91, 95, -492, -256, 720, 194, -388, -33, 65], ![-65, 306, 351, -1660, -1012, 2409, 850, -1301, -193, 227], ![-227, 1070, 1214, -5778, -3476, 8295, 2863, -4371, -620, 715]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 4, -27, -8, 41, 2, -23, 3, 4], ![-4, 19, 21, -104, -59, 156, 49, -90, -11, 19], ![-19, 91, 95, -492, -256, 720, 194, -388, -33, 65], ![-65, 306, 351, -1660, -1012, 2409, 850, -1301, -193, 227], ![-227, 1070, 1214, -5778, -3476, 8295, 2863, -4371, -620, 715], ![-715, 3348, 3930, -18091, -11498, 25839, 9725, -13582, -2226, 2240]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 4, -27, -8, 41, 2, -23, 3, 4], ![-4, 19, 21, -104, -59, 156, 49, -90, -11, 19], ![-19, 91, 95, -492, -256, 720, 194, -388, -33, 65], ![-65, 306, 351, -1660, -1012, 2409, 850, -1301, -193, 227], ![-227, 1070, 1214, -5778, -3476, 8295, 2863, -4371, -620, 715], ![-715, 3348, 3930, -18091, -11498, 25839, 9725, -13582, -2226, 2240], ![-2240, 10485, 12308, -56550, -36011, 80342, 30319, -41795, -6862, 6734]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 4, -27, -8, 41, 2, -23, 3, 4], ![-4, 19, 21, -104, -59, 156, 49, -90, -11, 19], ![-19, 91, 95, -492, -256, 720, 194, -388, -33, 65], ![-65, 306, 351, -1660, -1012, 2409, 850, -1301, -193, 227], ![-227, 1070, 1214, -5778, -3476, 8295, 2863, -4371, -620, 715], ![-715, 3348, 3930, -18091, -11498, 25839, 9725, -13582, -2226, 2240], ![-2240, 10485, 12308, -56550, -36011, 80342, 30319, -41795, -6862, 6734], ![-6734, 31430, 37421, -169510, -110422, 240083, 93810, -124563, -21593, 20074]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 4, -27, -8, 41, 2, -23, 3, 4], ![-4, 19, 21, -104, -59, 156, 49, -90, -11, 19], ![-19, 91, 95, -492, -256, 720, 194, -388, -33, 65], ![-65, 306, 351, -1660, -1012, 2409, 850, -1301, -193, 227], ![-227, 1070, 1214, -5778, -3476, 8295, 2863, -4371, -620, 715], ![-715, 3348, 3930, -18091, -11498, 25839, 9725, -13582, -2226, 2240], ![-2240, 10485, 12308, -56550, -36011, 80342, 30319, -41795, -6862, 6734], ![-6734, 31430, 37421, -169510, -110422, 240083, 93810, -124563, -21593, 20074], ![-20074, 93636, 111726, -504577, -330102, 712612, 280231, -367892, -64341, 58703]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-65, -19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-65, -19, -4, -1], [-227, -65, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-65, -19, -4, -1], [-227, -65, -19, -4, -1], [-715, -227, -65, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-65, -19, -4, -1], [-227, -65, -19, -4, -1], [-715, -227, -65, -19, -4, -1], [-2240, -715, -227, -65, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-65, -19, -4, -1], [-227, -65, -19, -4, -1], [-715, -227, -65, -19, -4, -1], [-2240, -715, -227, -65, -19, -4, -1], [-6734, -2240, -715, -227, -65, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-65, -19, -4, -1], [-227, -65, -19, -4, -1], [-715, -227, -65, -19, -4, -1], [-2240, -715, -227, -65, -19, -4, -1], [-6734, -2240, -715, -227, -65, -19, -4, -1], [-20074, -6734, -2240, -715, -227, -65, -19, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 4, -27, -8, 41, 2, -23, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 4, -27, -8, 41, 2, -23, 3, 4], [-4, 19, 21, -104, -59, 156, 49, -90, -11, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 4, -27, -8, 41, 2, -23, 3, 4], [-4, 19, 21, -104, -59, 156, 49, -90, -11, 19], [-19, 91, 95, -492, -256, 720, 194, -388, -33, 65]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 4, -27, -8, 41, 2, -23, 3, 4], [-4, 19, 21, -104, -59, 156, 49, -90, -11, 19], [-19, 91, 95, -492, -256, 720, 194, -388, -33, 65], [-65, 306, 351, -1660, -1012, 2409, 850, -1301, -193, 227]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 4, -27, -8, 41, 2, -23, 3, 4], [-4, 19, 21, -104, -59, 156, 49, -90, -11, 19], [-19, 91, 95, -492, -256, 720, 194, -388, -33, 65], [-65, 306, 351, -1660, -1012, 2409, 850, -1301, -193, 227], [-227, 1070, 1214, -5778, -3476, 8295, 2863, -4371, -620, 715]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 4, -27, -8, 41, 2, -23, 3, 4], [-4, 19, 21, -104, -59, 156, 49, -90, -11, 19], [-19, 91, 95, -492, -256, 720, 194, -388, -33, 65], [-65, 306, 351, -1660, -1012, 2409, 850, -1301, -193, 227], [-227, 1070, 1214, -5778, -3476, 8295, 2863, -4371, -620, 715], [-715, 3348, 3930, -18091, -11498, 25839, 9725, -13582, -2226, 2240]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 4, -27, -8, 41, 2, -23, 3, 4], [-4, 19, 21, -104, -59, 156, 49, -90, -11, 19], [-19, 91, 95, -492, -256, 720, 194, -388, -33, 65], [-65, 306, 351, -1660, -1012, 2409, 850, -1301, -193, 227], [-227, 1070, 1214, -5778, -3476, 8295, 2863, -4371, -620, 715], [-715, 3348, 3930, -18091, -11498, 25839, 9725, -13582, -2226, 2240], [-2240, 10485, 12308, -56550, -36011, 80342, 30319, -41795, -6862, 6734]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 4, -27, -8, 41, 2, -23, 3, 4], [-4, 19, 21, -104, -59, 156, 49, -90, -11, 19], [-19, 91, 95, -492, -256, 720, 194, -388, -33, 65], [-65, 306, 351, -1660, -1012, 2409, 850, -1301, -193, 227], [-227, 1070, 1214, -5778, -3476, 8295, 2863, -4371, -620, 715], [-715, 3348, 3930, -18091, -11498, 25839, 9725, -13582, -2226, 2240], [-2240, 10485, 12308, -56550, -36011, 80342, 30319, -41795, -6862, 6734], [-6734, 31430, 37421, -169510, -110422, 240083, 93810, -124563, -21593, 20074]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 4, -27, -8, 41, 2, -23, 3, 4], [-4, 19, 21, -104, -59, 156, 49, -90, -11, 19], [-19, 91, 95, -492, -256, 720, 194, -388, -33, 65], [-65, 306, 351, -1660, -1012, 2409, 850, -1301, -193, 227], [-227, 1070, 1214, -5778, -3476, 8295, 2863, -4371, -620, 715], [-715, 3348, 3930, -18091, -11498, 25839, 9725, -13582, -2226, 2240], [-2240, 10485, 12308, -56550, -36011, 80342, 30319, -41795, -6862, 6734], [-6734, 31430, 37421, -169510, -110422, 240083, 93810, -124563, -21593, 20074], [-20074, 93636, 111726, -504577, -330102, 712612, 280231, -367892, -64341, 58703]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp31 : Fact (Nat.Prime 31) := fact_iff.2 (by norm_num)
instance hp359 : Fact (Nat.Prime 359) := fact_iff.2 (by norm_num)
instance hp1361 : Fact (Nat.Prime 1361) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 2, 4]
  b' := [3, 0, 1, 0, 3]
  k := [1]
  f := [3, 1, 4, 1, 4, 13, 6, 1, 4, 2]
  g := [4, 0, 2, 4, 3, 1]
  h := [4, 0, 2, 4, 3, 1]
  a := [0, 3, 3, 4]
  b := [4, 4, 0, 1, 2, 4, 2, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [1, 1, 0, 10, 7, 1, 3]
  b' := [3, 4, 0, 1, 0, 8, 1, 1]
  k := [9, 8, 1, 1, 7, 0, 1]
  f := [1, 4, 6, 8, 10, 12, 8, 2, 8, 2]
  g := [3, 3, 8, 10, 5, 9, 0, 9, 1]
  h := [4, 9, 1]
  a := [10, 9, 4, 4, 8, 2, 5, 8]
  b := [8, 5, 10, 5, 8, 0, 3, 4, 6]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD31 : CertificateDedekindCriterionLists l 31 where
  n := 2
  a' := [21, 29, 3, 30, 28, 20, 0, 9]
  b' := [12, 21, 8, 26, 3, 25, 7, 14, 30]
  k := [8, 30, 27, 3, 6, 26, 24, 0, 1]
  f := [14, 10, 7, 19, 21, 17, 9, 22, 28, 2]
  g := [15, 10, 7, 21, 22, 16, 9, 24, 29, 1]
  h := [29, 1]
  a := [13, 15, 23, 19, 25, 20, 3, 0, 27]
  b := [21, 15, 15, 19, 12, 5, 22, 4, 8]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD359 : CertificateDedekindCriterionLists l 359 where
  n := 2
  a' := [235, 184, 236, 170, 93, 309, 42, 298]
  b' := [206, 36, 104, 42, 304, 198, 21, 352, 286]
  k := [266, 89, 197, 224, 274, 175, 45, 39, 1]
  f := [11, 144, 151, 22, 34, 124, 47, 46, 87, 1]
  g := [25, 327, 341, 48, 77, 281, 105, 104, 197, 1]
  h := [158, 1]
  a := [334, 193, 244, 315, 350, 100, 168, 275, 288]
  b := [169, 60, 150, 296, 136, 319, 12, 172, 71]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1361 : CertificateDedekindCriterionLists l 1361 where
  n := 2
  a' := [908, 438, 1017, 1316, 745, 981, 215, 653]
  b' := [377, 815, 106, 859, 1164, 654, 807, 1211, 986]
  k := [1187, 1009, 1003, 1248, 1351, 1309, 605, 1117, 1]
  f := [79, 101, 22, 93, 5, 49, 37, 112, 110, 1]
  g := [896, 1138, 240, 1053, 48, 555, 415, 1267, 1237, 1]
  h := [120, 1]
  a := [1003, 285, 379, 1000, 636, 361, 676, 1069, 228]
  b := [987, 431, 55, 954, 609, 47, 442, 19, 1133]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 5
  p := ![5, 11, 31, 359, 1361]
  exp := ![1, 1, 1, 1, 1]
  pdgood := [5, 11, 31, 359, 1361]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp11.out
    exact hp31.out
    exact hp359.out
    exact hp1361.out
  a := [3420905685, -11825950596, -88005596775, 132029841432, 92922468547, -157070112256, 1604820868, 41827359638, -10213155680]
  b := [517568878, -6614206009, 10455452131, 21778796301, -30446546440, -13777385219, 22870058369, -570871460, -4591262191, 1021315568]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 31 T_ofList CD31
    exact satisfiesDedekindCriterion_of_certificate_lists T l 359 T_ofList CD359
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1361 T_ofList CD1361

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

end VoightMaximalOrderD10R505

namespace VoightMaximalOrderD10R506

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5727669055525, [1, 15, 39, -20, -70, 8, 43, -1, -11, 0, 1], 1⟩
local notation "l" => [1, 15, 39, -20, -70, 8, 43, -1, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -15, -39, 20, 70, -8, -43, 1, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -15, -39, 20, 70, -8, -43, 1, 11, 0], ![0, -1, -15, -39, 20, 70, -8, -43, 1, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -15, -39, 20, 70, -8, -43, 1, 11, 0], ![0, -1, -15, -39, 20, 70, -8, -43, 1, 11], ![-11, -165, -430, 205, 731, -68, -403, 3, 78, 1]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -15, -39, 20, 70, -8, -43, 1, 11, 0], ![0, -1, -15, -39, 20, 70, -8, -43, 1, 11], ![-11, -165, -430, 205, 731, -68, -403, 3, 78, 1], ![-1, -26, -204, -410, 275, 723, -111, -402, 14, 78]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -15, -39, 20, 70, -8, -43, 1, 11, 0], ![0, -1, -15, -39, 20, 70, -8, -43, 1, 11], ![-11, -165, -430, 205, 731, -68, -403, 3, 78, 1], ![-1, -26, -204, -410, 275, 723, -111, -402, 14, 78], ![-78, -1171, -3068, 1356, 5050, -349, -2631, -33, 456, 14]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -15, -39, 20, 70, -8, -43, 1, 11, 0], ![0, -1, -15, -39, 20, 70, -8, -43, 1, 11], ![-11, -165, -430, 205, 731, -68, -403, 3, 78, 1], ![-1, -26, -204, -410, 275, 723, -111, -402, 14, 78], ![-78, -1171, -3068, 1356, 5050, -349, -2631, -33, 456, 14], ![-14, -288, -1717, -2788, 2336, 4938, -951, -2617, 121, 456]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -15, -39, 20, 70, -8, -43, 1, 11, 0], ![0, -1, -15, -39, 20, 70, -8, -43, 1, 11], ![-11, -165, -430, 205, 731, -68, -403, 3, 78, 1], ![-1, -26, -204, -410, 275, 723, -111, -402, 14, 78], ![-78, -1171, -3068, 1356, 5050, -349, -2631, -33, 456, 14], ![-14, -288, -1717, -2788, 2336, 4938, -951, -2617, 121, 456], ![-456, -6854, -18072, 7403, 29132, -1312, -14670, -495, 2399, 121]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -15, -39, 20, 70, -8, -43, 1, 11, 0], ![0, -1, -15, -39, 20, 70, -8, -43, 1, 11], ![-11, -165, -430, 205, 731, -68, -403, 3, 78, 1], ![-1, -26, -204, -410, 275, 723, -111, -402, 14, 78], ![-78, -1171, -3068, 1356, 5050, -349, -2631, -33, 456, 14], ![-14, -288, -1717, -2788, 2336, 4938, -951, -2617, 121, 456], ![-456, -6854, -18072, 7403, 29132, -1312, -14670, -495, 2399, 121], ![-121, -2271, -11573, -15652, 15873, 28164, -6515, -14549, 836, 2399]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -15, -39, 20, 70, -8, -43, 1, 11, 0], ![0, -1, -15, -39, 20, 70, -8, -43, 1, 11], ![-11, -165, -430, 205, 731, -68, -403, 3, 78, 1], ![-1, -26, -204, -410, 275, 723, -111, -402, 14, 78], ![-78, -1171, -3068, 1356, 5050, -349, -2631, -33, 456, 14], ![-14, -288, -1717, -2788, 2336, 4938, -951, -2617, 121, 456], ![-456, -6854, -18072, 7403, 29132, -1312, -14670, -495, 2399, 121], ![-121, -2271, -11573, -15652, 15873, 28164, -6515, -14549, 836, 2399], ![-2399, -36106, -95832, 36407, 152278, -3319, -74993, -4116, 11840, 836]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1], [-78, -1, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1], [-78, -1, -11, 0, -1], [-14, -78, -1, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1], [-78, -1, -11, 0, -1], [-14, -78, -1, -11, 0, -1], [-456, -14, -78, -1, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1], [-78, -1, -11, 0, -1], [-14, -78, -1, -11, 0, -1], [-456, -14, -78, -1, -11, 0, -1], [-121, -456, -14, -78, -1, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [-1, -11, 0, -1], [-78, -1, -11, 0, -1], [-14, -78, -1, -11, 0, -1], [-456, -14, -78, -1, -11, 0, -1], [-121, -456, -14, -78, -1, -11, 0, -1], [-2399, -121, -456, -14, -78, -1, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -15, -39, 20, 70, -8, -43, 1, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -15, -39, 20, 70, -8, -43, 1, 11, 0], [0, -1, -15, -39, 20, 70, -8, -43, 1, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -15, -39, 20, 70, -8, -43, 1, 11, 0], [0, -1, -15, -39, 20, 70, -8, -43, 1, 11], [-11, -165, -430, 205, 731, -68, -403, 3, 78, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -15, -39, 20, 70, -8, -43, 1, 11, 0], [0, -1, -15, -39, 20, 70, -8, -43, 1, 11], [-11, -165, -430, 205, 731, -68, -403, 3, 78, 1], [-1, -26, -204, -410, 275, 723, -111, -402, 14, 78]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -15, -39, 20, 70, -8, -43, 1, 11, 0], [0, -1, -15, -39, 20, 70, -8, -43, 1, 11], [-11, -165, -430, 205, 731, -68, -403, 3, 78, 1], [-1, -26, -204, -410, 275, 723, -111, -402, 14, 78], [-78, -1171, -3068, 1356, 5050, -349, -2631, -33, 456, 14]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -15, -39, 20, 70, -8, -43, 1, 11, 0], [0, -1, -15, -39, 20, 70, -8, -43, 1, 11], [-11, -165, -430, 205, 731, -68, -403, 3, 78, 1], [-1, -26, -204, -410, 275, 723, -111, -402, 14, 78], [-78, -1171, -3068, 1356, 5050, -349, -2631, -33, 456, 14], [-14, -288, -1717, -2788, 2336, 4938, -951, -2617, 121, 456]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -15, -39, 20, 70, -8, -43, 1, 11, 0], [0, -1, -15, -39, 20, 70, -8, -43, 1, 11], [-11, -165, -430, 205, 731, -68, -403, 3, 78, 1], [-1, -26, -204, -410, 275, 723, -111, -402, 14, 78], [-78, -1171, -3068, 1356, 5050, -349, -2631, -33, 456, 14], [-14, -288, -1717, -2788, 2336, 4938, -951, -2617, 121, 456], [-456, -6854, -18072, 7403, 29132, -1312, -14670, -495, 2399, 121]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -15, -39, 20, 70, -8, -43, 1, 11, 0], [0, -1, -15, -39, 20, 70, -8, -43, 1, 11], [-11, -165, -430, 205, 731, -68, -403, 3, 78, 1], [-1, -26, -204, -410, 275, 723, -111, -402, 14, 78], [-78, -1171, -3068, 1356, 5050, -349, -2631, -33, 456, 14], [-14, -288, -1717, -2788, 2336, 4938, -951, -2617, 121, 456], [-456, -6854, -18072, 7403, 29132, -1312, -14670, -495, 2399, 121], [-121, -2271, -11573, -15652, 15873, 28164, -6515, -14549, 836, 2399]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -15, -39, 20, 70, -8, -43, 1, 11, 0], [0, -1, -15, -39, 20, 70, -8, -43, 1, 11], [-11, -165, -430, 205, 731, -68, -403, 3, 78, 1], [-1, -26, -204, -410, 275, 723, -111, -402, 14, 78], [-78, -1171, -3068, 1356, 5050, -349, -2631, -33, 456, 14], [-14, -288, -1717, -2788, 2336, 4938, -951, -2617, 121, 456], [-456, -6854, -18072, 7403, 29132, -1312, -14670, -495, 2399, 121], [-121, -2271, -11573, -15652, 15873, 28164, -6515, -14549, 836, 2399], [-2399, -36106, -95832, 36407, 152278, -3319, -74993, -4116, 11840, 836]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp61 : Fact (Nat.Prime 61) := fact_iff.2 (by norm_num)
instance hp137 : Fact (Nat.Prime 137) := fact_iff.2 (by norm_num)
instance hp823 : Fact (Nat.Prime 823) := fact_iff.2 (by norm_num)
instance hp33311 : Fact (Nat.Prime 33311) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 3
  a' := [4, 0, 4, 1, 3, 2, 3]
  b' := [0, 1, 0, 1, 1, 1, 3, 4]
  k := [4, 2, 3, 4, 1, 4, 1, 2, 4, 2, 1, 2, 2, 2, 1]
  f := [3, 1, -3, 8, 17, 1, -7, 4, 4, 1]
  g := [4, 4, 4, 3, 2, 2, 1, 4, 1]
  h := [4, 1, 1]
  a := [3, 4, 1, 2, 1, 1, 1, 1]
  b := [3, 2, 3, 3, 1, 2, 1, 4, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD61 : CertificateDedekindCriterionLists l 61 where
  n := 2
  a' := [27, 17, 23, 40, 38, 55, 0, 28]
  b' := [5, 4, 22, 32, 19, 3, 44, 14, 24]
  k := [36, 57, 60, 22, 37, 1, 45, 41, 1]
  f := [9, 10, 8, 7, 6, 8, 4, 5, 9, 1]
  g := [55, 57, 47, 36, 26, 47, 24, 28, 51, 1]
  h := [10, 1]
  a := [55, 15, 46, 17, 50, 19, 6, 0, 7]
  b := [1, 22, 8, 34, 17, 32, 45, 50, 54]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD137 : CertificateDedekindCriterionLists l 137 where
  n := 2
  a' := [20, 103, 107, 130, 77, 18, 54, 44]
  b' := [111, 113, 33, 107, 83, 128, 37, 101, 56]
  k := [59, 71, 123, 130, 62, 18, 68, 98, 1]
  f := [79, 4, 46, 36, 69, 2, 71, 40, 32, 1]
  g := [123, 5, 72, 55, 106, 2, 111, 61, 49, 1]
  h := [88, 1]
  a := [27, 21, 32, 6, 95, 98, 30, 90]
  b := [74, 45, 75, 16, 109, 79, 130, 47]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD823 : CertificateDedekindCriterionLists l 823 where
  n := 2
  a' := [320, 797, 296, 680, 388, 35, 707, 331]
  b' := [61, 39, 97, 725, 145, 626, 694, 163, 329]
  k := [168, 410, 318, 599, 726, 171, 474, 481, 1]
  f := [155, 68, 98, 145, 99, 71, 119, 89, 136, 1]
  g := [746, 323, 470, 695, 472, 339, 571, 425, 652, 1]
  h := [171, 1]
  a := [344, 111, 537, 456, 384, 390, 803, 678, 61]
  b := [468, 481, 495, 334, 537, 612, 813, 347, 762]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD33311 : CertificateDedekindCriterionLists l 33311 where
  n := 2
  a' := [1795, 33230, 29123, 8657, 27441, 900, 11588, 30642]
  b' := [22620, 30904, 21324, 17976, 9027, 30945, 27991, 2394, 7699]
  k := [5539, 25421, 20551, 24399, 16981, 7580, 26378, 3431, 1]
  f := [3649, 7431, 13399, 8674, 10748, 2145, 11558, 8921, 8240, 1]
  g := [8136, 16568, 29874, 19338, 23963, 4781, 25770, 19889, 18371, 1]
  h := [14940, 1]
  a := [1350, 6044, 28719, 20011, 11305, 11920, 17112, 25752, 2257]
  b := [24431, 4354, 23337, 30092, 1767, 14184, 21849, 21880, 31054]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 5
  p := ![5, 61, 137, 823, 33311]
  exp := ![1, 1, 1, 1, 1]
  pdgood := [5, 61, 137, 823, 33311]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp61.out
    exact hp137.out
    exact hp823.out
    exact hp33311.out
  a := [-3722511648130, -1645694134272, 16188792445725, 5202152374648, -18695982347322, -3024058628306, 7534364726592, 480220586980, -965022445240]
  b := [324536363949, 2144635497880, 391012456515, -4616857374411, -873119951121, 3333120244020, 379103718609, -965741410612, -48022058698, 96502244524]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 61 T_ofList CD61
    exact satisfiesDedekindCriterion_of_certificate_lists T l 137 T_ofList CD137
    exact satisfiesDedekindCriterion_of_certificate_lists T l 823 T_ofList CD823
    exact satisfiesDedekindCriterion_of_certificate_lists T l 33311 T_ofList CD33311

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

end VoightMaximalOrderD10R506

namespace VoightMaximalOrderD10R511

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5750361503125, [-1, 1, 17, 10, -36, -19, 30, 9, -10, -1, 1], 1⟩
local notation "l" => [-1, 1, 17, 10, -36, -19, 30, 9, -10, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -17, -10, 36, 19, -30, -9, 10, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -17, -10, 36, 19, -30, -9, 10, 1], ![1, 0, -18, -27, 26, 55, -11, -39, 1, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -17, -10, 36, 19, -30, -9, 10, 1], ![1, 0, -18, -27, 26, 55, -11, -39, 1, 11], ![11, -10, -187, -128, 369, 235, -275, -110, 71, 12]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -17, -10, 36, 19, -30, -9, 10, 1], ![1, 0, -18, -27, 26, 55, -11, -39, 1, 11], ![11, -10, -187, -128, 369, 235, -275, -110, 71, 12], ![12, -1, -214, -307, 304, 597, -125, -383, 10, 83]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -17, -10, 36, 19, -30, -9, 10, 1], ![1, 0, -18, -27, 26, 55, -11, -39, 1, 11], ![11, -10, -187, -128, 369, 235, -275, -110, 71, 12], ![12, -1, -214, -307, 304, 597, -125, -383, 10, 83], ![83, -71, -1412, -1044, 2681, 1881, -1893, -872, 447, 93]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -17, -10, 36, 19, -30, -9, 10, 1], ![1, 0, -18, -27, 26, 55, -11, -39, 1, 11], ![11, -10, -187, -128, 369, 235, -275, -110, 71, 12], ![12, -1, -214, -307, 304, 597, -125, -383, 10, 83], ![83, -71, -1412, -1044, 2681, 1881, -1893, -872, 447, 93], ![93, -10, -1652, -2342, 2304, 4448, -909, -2730, 58, 540]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -17, -10, 36, 19, -30, -9, 10, 1], ![1, 0, -18, -27, 26, 55, -11, -39, 1, 11], ![11, -10, -187, -128, 369, 235, -275, -110, 71, 12], ![12, -1, -214, -307, 304, 597, -125, -383, 10, 83], ![83, -71, -1412, -1044, 2681, 1881, -1893, -872, 447, 93], ![93, -10, -1652, -2342, 2304, 4448, -909, -2730, 58, 540], ![540, -447, -9190, -7052, 17098, 12564, -11752, -5769, 2670, 598]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -17, -10, 36, 19, -30, -9, 10, 1], ![1, 0, -18, -27, 26, 55, -11, -39, 1, 11], ![11, -10, -187, -128, 369, 235, -275, -110, 71, 12], ![12, -1, -214, -307, 304, 597, -125, -383, 10, 83], ![83, -71, -1412, -1044, 2681, 1881, -1893, -872, 447, 93], ![93, -10, -1652, -2342, 2304, 4448, -909, -2730, 58, 540], ![540, -447, -9190, -7052, 17098, 12564, -11752, -5769, 2670, 598], ![598, -58, -10613, -15170, 14476, 28460, -5376, -17134, 211, 3268]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -17, -10, 36, 19, -30, -9, 10, 1], ![1, 0, -18, -27, 26, 55, -11, -39, 1, 11], ![11, -10, -187, -128, 369, 235, -275, -110, 71, 12], ![12, -1, -214, -307, 304, 597, -125, -383, 10, 83], ![83, -71, -1412, -1044, 2681, 1881, -1893, -872, 447, 93], ![93, -10, -1652, -2342, 2304, 4448, -909, -2730, 58, 540], ![540, -447, -9190, -7052, 17098, 12564, -11752, -5769, 2670, 598], ![598, -58, -10613, -15170, 14476, 28460, -5376, -17134, 211, 3268], ![3268, -2670, -55614, -43293, 102478, 76568, -69580, -34788, 15546, 3479]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-12, -11, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-12, -11, -1, -1], [-83, -12, -11, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-12, -11, -1, -1], [-83, -12, -11, -1, -1], [-93, -83, -12, -11, -1, -1]], ![[], [], [], [-1], [-1, -1], [-11, -1, -1], [-12, -11, -1, -1], [-83, -12, -11, -1, -1], [-93, -83, -12, -11, -1, -1], [-540, -93, -83, -12, -11, -1, -1]], ![[], [], [-1], [-1, -1], [-11, -1, -1], [-12, -11, -1, -1], [-83, -12, -11, -1, -1], [-93, -83, -12, -11, -1, -1], [-540, -93, -83, -12, -11, -1, -1], [-598, -540, -93, -83, -12, -11, -1, -1]], ![[], [-1], [-1, -1], [-11, -1, -1], [-12, -11, -1, -1], [-83, -12, -11, -1, -1], [-93, -83, -12, -11, -1, -1], [-540, -93, -83, -12, -11, -1, -1], [-598, -540, -93, -83, -12, -11, -1, -1], [-3268, -598, -540, -93, -83, -12, -11, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -17, -10, 36, 19, -30, -9, 10, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -17, -10, 36, 19, -30, -9, 10, 1], [1, 0, -18, -27, 26, 55, -11, -39, 1, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -17, -10, 36, 19, -30, -9, 10, 1], [1, 0, -18, -27, 26, 55, -11, -39, 1, 11], [11, -10, -187, -128, 369, 235, -275, -110, 71, 12]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -17, -10, 36, 19, -30, -9, 10, 1], [1, 0, -18, -27, 26, 55, -11, -39, 1, 11], [11, -10, -187, -128, 369, 235, -275, -110, 71, 12], [12, -1, -214, -307, 304, 597, -125, -383, 10, 83]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -17, -10, 36, 19, -30, -9, 10, 1], [1, 0, -18, -27, 26, 55, -11, -39, 1, 11], [11, -10, -187, -128, 369, 235, -275, -110, 71, 12], [12, -1, -214, -307, 304, 597, -125, -383, 10, 83], [83, -71, -1412, -1044, 2681, 1881, -1893, -872, 447, 93]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -17, -10, 36, 19, -30, -9, 10, 1], [1, 0, -18, -27, 26, 55, -11, -39, 1, 11], [11, -10, -187, -128, 369, 235, -275, -110, 71, 12], [12, -1, -214, -307, 304, 597, -125, -383, 10, 83], [83, -71, -1412, -1044, 2681, 1881, -1893, -872, 447, 93], [93, -10, -1652, -2342, 2304, 4448, -909, -2730, 58, 540]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -17, -10, 36, 19, -30, -9, 10, 1], [1, 0, -18, -27, 26, 55, -11, -39, 1, 11], [11, -10, -187, -128, 369, 235, -275, -110, 71, 12], [12, -1, -214, -307, 304, 597, -125, -383, 10, 83], [83, -71, -1412, -1044, 2681, 1881, -1893, -872, 447, 93], [93, -10, -1652, -2342, 2304, 4448, -909, -2730, 58, 540], [540, -447, -9190, -7052, 17098, 12564, -11752, -5769, 2670, 598]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -17, -10, 36, 19, -30, -9, 10, 1], [1, 0, -18, -27, 26, 55, -11, -39, 1, 11], [11, -10, -187, -128, 369, 235, -275, -110, 71, 12], [12, -1, -214, -307, 304, 597, -125, -383, 10, 83], [83, -71, -1412, -1044, 2681, 1881, -1893, -872, 447, 93], [93, -10, -1652, -2342, 2304, 4448, -909, -2730, 58, 540], [540, -447, -9190, -7052, 17098, 12564, -11752, -5769, 2670, 598], [598, -58, -10613, -15170, 14476, 28460, -5376, -17134, 211, 3268]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -17, -10, 36, 19, -30, -9, 10, 1], [1, 0, -18, -27, 26, 55, -11, -39, 1, 11], [11, -10, -187, -128, 369, 235, -275, -110, 71, 12], [12, -1, -214, -307, 304, 597, -125, -383, 10, 83], [83, -71, -1412, -1044, 2681, 1881, -1893, -872, 447, 93], [93, -10, -1652, -2342, 2304, 4448, -909, -2730, 58, 540], [540, -447, -9190, -7052, 17098, 12564, -11752, -5769, 2670, 598], [598, -58, -10613, -15170, 14476, 28460, -5376, -17134, 211, 3268], [3268, -2670, -55614, -43293, 102478, 76568, -69580, -34788, 15546, 3479]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1840115681 : Fact (Nat.Prime 1840115681) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 0, 4]
  b' := [0, 3, 0, 3, 2]
  k := [1]
  f := [2, 1, -2, 2, 11, 7, -3, 1, 4, 1]
  g := [3, 1, 1, 3, 2, 1]
  h := [3, 1, 1, 3, 2, 1]
  a := [4, 2, 1, 4]
  b := [1, 2, 2, 0, 0, 0, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1840115681 : CertificateDedekindCriterionLists l 1840115681 where
  n := 2
  a' := [1205324494, 1578759139, 1186825812, 1588905210, 1736868960, 151009348, 211420170, 1721557351]
  b' := [784228972, 382928858, 1218433040, 120827176, 822235777, 1043642690, 1838829897, 1124335527, 1444374233]
  k := [1593135246, 1529287599, 39046860, 181070576, 771505707, 1052084944, 874476494, 1444690687, 1]
  f := [652568143, 615229395, 662322097, 838088706, 634171368, 807445683, 736019324, 775984025, 438785565, 1]
  g := [1074282286, 1012813830, 1090339612, 1379693232, 1043996820, 1329247532, 1211662766, 1277454164, 722345343, 1]
  h := [1117770337, 1]
  a := [1166432504, 763178069, 672203650, 1070485711, 381047070, 849059274, 1531374820, 385138629, 224471833]
  b := [1611495645, 276797367, 213661335, 565695734, 305482634, 1141909482, 1391478487, 682434466, 1615643848]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 1840115681]
  exp := ![1, 1]
  pdgood := [5, 1840115681]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1840115681.out
  a := [-29237245509, -654199733194, 427219031925, 2418060397122, -1634182893927, -1679500719748, 1110361956846, 244759800390, -161871511700]
  b := [-20036667104, 56284193851, 265889360958, -209434866493, -479965168472, 312295239555, 230516045697, -142419743626, -26094695156, 16187151170]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1840115681 T_ofList CD1840115681

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

end VoightMaximalOrderD10R511

end TraceEuclidean
