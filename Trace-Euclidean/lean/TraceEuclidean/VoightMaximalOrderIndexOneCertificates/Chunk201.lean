import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk197
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

namespace VoightMaximalOrderD10R356

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4648184628125, [1, -7, -2, 31, -5, -42, 11, 20, -6, -3, 1], 1⟩
local notation "l" => [1, -7, -2, 31, -5, -42, 11, 20, -6, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 2, -31, 5, 42, -11, -20, 6, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 2, -31, 5, 42, -11, -20, 6, 3], ![-3, 20, 13, -91, -16, 131, 9, -71, -2, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 2, -31, 5, 42, -11, -20, 6, 3], ![-3, 20, 13, -91, -16, 131, 9, -71, -2, 15], ![-15, 102, 50, -452, -16, 614, -34, -291, 19, 43]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 2, -31, 5, 42, -11, -20, 6, 3], ![-3, 20, 13, -91, -16, 131, 9, -71, -2, 15], ![-15, 102, 50, -452, -16, 614, -34, -291, 19, 43], ![-43, 286, 188, -1283, -237, 1790, 141, -894, -33, 148]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 2, -31, 5, 42, -11, -20, 6, 3], ![-3, 20, 13, -91, -16, 131, 9, -71, -2, 15], ![-15, 102, 50, -452, -16, 614, -34, -291, 19, 43], ![-43, 286, 188, -1283, -237, 1790, 141, -894, -33, 148], ![-148, 993, 582, -4400, -543, 5979, 162, -2819, -6, 411]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 2, -31, 5, 42, -11, -20, 6, 3], ![-3, 20, 13, -91, -16, 131, 9, -71, -2, 15], ![-15, 102, 50, -452, -16, 614, -34, -291, 19, 43], ![-43, 286, 188, -1283, -237, 1790, 141, -894, -33, 148], ![-148, 993, 582, -4400, -543, 5979, 162, -2819, -6, 411], ![-411, 2729, 1815, -12159, -2345, 16719, 1458, -8058, -353, 1227]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 2, -31, 5, 42, -11, -20, 6, 3], ![-3, 20, 13, -91, -16, 131, 9, -71, -2, 15], ![-15, 102, 50, -452, -16, 614, -34, -291, 19, 43], ![-43, 286, 188, -1283, -237, 1790, 141, -894, -33, 148], ![-148, 993, 582, -4400, -543, 5979, 162, -2819, -6, 411], ![-411, 2729, 1815, -12159, -2345, 16719, 1458, -8058, -353, 1227], ![-1227, 8178, 5183, -36222, -6024, 49189, 3222, -23082, -696, 3328]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 2, -31, 5, 42, -11, -20, 6, 3], ![-3, 20, 13, -91, -16, 131, 9, -71, -2, 15], ![-15, 102, 50, -452, -16, 614, -34, -291, 19, 43], ![-43, 286, 188, -1283, -237, 1790, 141, -894, -33, 148], ![-148, 993, 582, -4400, -543, 5979, 162, -2819, -6, 411], ![-411, 2729, 1815, -12159, -2345, 16719, 1458, -8058, -353, 1227], ![-1227, 8178, 5183, -36222, -6024, 49189, 3222, -23082, -696, 3328], ![-3328, 22069, 14834, -97985, -19582, 133752, 12581, -63338, -3114, 9288]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 2, -31, 5, 42, -11, -20, 6, 3], ![-3, 20, 13, -91, -16, 131, 9, -71, -2, 15], ![-15, 102, 50, -452, -16, 614, -34, -291, 19, 43], ![-43, 286, 188, -1283, -237, 1790, 141, -894, -33, 148], ![-148, 993, 582, -4400, -543, 5979, 162, -2819, -6, 411], ![-411, 2729, 1815, -12159, -2345, 16719, 1458, -8058, -353, 1227], ![-1227, 8178, 5183, -36222, -6024, 49189, 3222, -23082, -696, 3328], ![-3328, 22069, 14834, -97985, -19582, 133752, 12581, -63338, -3114, 9288], ![-9288, 61688, 40645, -273094, -51545, 370514, 31584, -173179, -7610, 24750]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-43, -15, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-43, -15, -3, -1], [-148, -43, -15, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-43, -15, -3, -1], [-148, -43, -15, -3, -1], [-411, -148, -43, -15, -3, -1]], ![[], [], [], [-1], [-3, -1], [-15, -3, -1], [-43, -15, -3, -1], [-148, -43, -15, -3, -1], [-411, -148, -43, -15, -3, -1], [-1227, -411, -148, -43, -15, -3, -1]], ![[], [], [-1], [-3, -1], [-15, -3, -1], [-43, -15, -3, -1], [-148, -43, -15, -3, -1], [-411, -148, -43, -15, -3, -1], [-1227, -411, -148, -43, -15, -3, -1], [-3328, -1227, -411, -148, -43, -15, -3, -1]], ![[], [-1], [-3, -1], [-15, -3, -1], [-43, -15, -3, -1], [-148, -43, -15, -3, -1], [-411, -148, -43, -15, -3, -1], [-1227, -411, -148, -43, -15, -3, -1], [-3328, -1227, -411, -148, -43, -15, -3, -1], [-9288, -3328, -1227, -411, -148, -43, -15, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 2, -31, 5, 42, -11, -20, 6, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 2, -31, 5, 42, -11, -20, 6, 3], [-3, 20, 13, -91, -16, 131, 9, -71, -2, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 2, -31, 5, 42, -11, -20, 6, 3], [-3, 20, 13, -91, -16, 131, 9, -71, -2, 15], [-15, 102, 50, -452, -16, 614, -34, -291, 19, 43]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 2, -31, 5, 42, -11, -20, 6, 3], [-3, 20, 13, -91, -16, 131, 9, -71, -2, 15], [-15, 102, 50, -452, -16, 614, -34, -291, 19, 43], [-43, 286, 188, -1283, -237, 1790, 141, -894, -33, 148]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 2, -31, 5, 42, -11, -20, 6, 3], [-3, 20, 13, -91, -16, 131, 9, -71, -2, 15], [-15, 102, 50, -452, -16, 614, -34, -291, 19, 43], [-43, 286, 188, -1283, -237, 1790, 141, -894, -33, 148], [-148, 993, 582, -4400, -543, 5979, 162, -2819, -6, 411]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 2, -31, 5, 42, -11, -20, 6, 3], [-3, 20, 13, -91, -16, 131, 9, -71, -2, 15], [-15, 102, 50, -452, -16, 614, -34, -291, 19, 43], [-43, 286, 188, -1283, -237, 1790, 141, -894, -33, 148], [-148, 993, 582, -4400, -543, 5979, 162, -2819, -6, 411], [-411, 2729, 1815, -12159, -2345, 16719, 1458, -8058, -353, 1227]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 2, -31, 5, 42, -11, -20, 6, 3], [-3, 20, 13, -91, -16, 131, 9, -71, -2, 15], [-15, 102, 50, -452, -16, 614, -34, -291, 19, 43], [-43, 286, 188, -1283, -237, 1790, 141, -894, -33, 148], [-148, 993, 582, -4400, -543, 5979, 162, -2819, -6, 411], [-411, 2729, 1815, -12159, -2345, 16719, 1458, -8058, -353, 1227], [-1227, 8178, 5183, -36222, -6024, 49189, 3222, -23082, -696, 3328]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 2, -31, 5, 42, -11, -20, 6, 3], [-3, 20, 13, -91, -16, 131, 9, -71, -2, 15], [-15, 102, 50, -452, -16, 614, -34, -291, 19, 43], [-43, 286, 188, -1283, -237, 1790, 141, -894, -33, 148], [-148, 993, 582, -4400, -543, 5979, 162, -2819, -6, 411], [-411, 2729, 1815, -12159, -2345, 16719, 1458, -8058, -353, 1227], [-1227, 8178, 5183, -36222, -6024, 49189, 3222, -23082, -696, 3328], [-3328, 22069, 14834, -97985, -19582, 133752, 12581, -63338, -3114, 9288]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 2, -31, 5, 42, -11, -20, 6, 3], [-3, 20, 13, -91, -16, 131, 9, -71, -2, 15], [-15, 102, 50, -452, -16, 614, -34, -291, 19, 43], [-43, 286, 188, -1283, -237, 1790, 141, -894, -33, 148], [-148, 993, 582, -4400, -543, 5979, 162, -2819, -6, 411], [-411, 2729, 1815, -12159, -2345, 16719, 1458, -8058, -353, 1227], [-1227, 8178, 5183, -36222, -6024, 49189, 3222, -23082, -696, 3328], [-3328, 22069, 14834, -97985, -19582, 133752, 12581, -63338, -3114, 9288], [-9288, 61688, 40645, -273094, -51545, 370514, 31584, -173179, -7610, 24750]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1487419081 : Fact (Nat.Prime 1487419081) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4]
  b' := [3, 2, 4]
  k := [1]
  f := [0, 3, 4, -3, 8, 12, 3, -2, 3, 1]
  g := [1, 4, 1, 4, 1, 1]
  h := [1, 4, 1, 4, 1, 1]
  a := [2, 0, 3, 3, 1]
  b := [1, 0, 1, 4, 0, 1, 4, 0, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1487419081 : CertificateDedekindCriterionLists l 1487419081 where
  n := 2
  a' := [4084392, 426768673, 1197811722, 590967450, 719962918, 821823534, 1268518644, 336757468]
  b' := [1203951477, 1293226622, 979379972, 298932470, 1290319561, 879768885, 390355252, 694046089, 1119464011]
  k := [1234783233, 177956315, 1380326715, 1019980481, 1461603743, 326283796, 716980014, 272329364, 1]
  f := [307027921, 384174543, 507295697, 30052398, 471643463, 217657202, 165485513, 345773381, 359389674, 1]
  g := [751679786, 940553670, 1241984505, 73575652, 1154699078, 532878306, 405149194, 846538191, 879874221, 1]
  h := [607544857, 1]
  a := [1383432376, 928169807, 654509017, 519677857, 1221100730, 717330151, 1422903236, 1283003283, 959027371]
  b := [29787739, 282321293, 577527641, 1052478761, 189322148, 131375678, 825342132, 372223893, 528391710]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 1487419081]
  exp := ![1, 1]
  pdgood := [5, 1487419081]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1487419081.out
  a := [-185985454489, -385421255532, 1946145219384, 2223662614680, -2621719518239, -1884318152576, 1224200197696, 393422570070, -197887526500]
  b := [-27631792842, 146714871037, 265635528376, -465640535618, -523247793042, 418754279953, 287078909225, -150392735494, -45278882802, 19788752650]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1487419081 T_ofList CD1487419081

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

end VoightMaximalOrderD10R356

namespace VoightMaximalOrderD10R361

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4674980628125, [1, 7, 9, -19, -36, 14, 38, -2, -12, 0, 1], 1⟩
local notation "l" => [1, 7, 9, -19, -36, 14, 38, -2, -12, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -9, 19, 36, -14, -38, 2, 12, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -9, 19, 36, -14, -38, 2, 12, 0], ![0, -1, -7, -9, 19, 36, -14, -38, 2, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -9, 19, 36, -14, -38, 2, 12, 0], ![0, -1, -7, -9, 19, 36, -14, -38, 2, 12], ![-12, -84, -109, 221, 423, -149, -420, 10, 106, 2]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -9, 19, 36, -14, -38, 2, 12, 0], ![0, -1, -7, -9, 19, 36, -14, -38, 2, 12], ![-12, -84, -109, 221, 423, -149, -420, 10, 106, 2], ![-2, -26, -102, -71, 293, 395, -225, -416, 34, 106]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -9, 19, 36, -14, -38, 2, 12, 0], ![0, -1, -7, -9, 19, 36, -14, -38, 2, 12], ![-12, -84, -109, 221, 423, -149, -420, 10, 106, 2], ![-2, -26, -102, -71, 293, 395, -225, -416, 34, 106], ![-106, -744, -980, 1912, 3745, -1191, -3633, -13, 856, 34]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -9, 19, 36, -14, -38, 2, 12, 0], ![0, -1, -7, -9, 19, 36, -14, -38, 2, 12], ![-12, -84, -109, 221, 423, -149, -420, 10, 106, 2], ![-2, -26, -102, -71, 293, 395, -225, -416, 34, 106], ![-106, -744, -980, 1912, 3745, -1191, -3633, -13, 856, 34], ![-34, -344, -1050, -334, 3136, 3269, -2483, -3565, 395, 856]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -9, 19, 36, -14, -38, 2, 12, 0], ![0, -1, -7, -9, 19, 36, -14, -38, 2, 12], ![-12, -84, -109, 221, 423, -149, -420, 10, 106, 2], ![-2, -26, -102, -71, 293, 395, -225, -416, 34, 106], ![-106, -744, -980, 1912, 3745, -1191, -3633, -13, 856, 34], ![-34, -344, -1050, -334, 3136, 3269, -2483, -3565, 395, 856], ![-856, -6026, -8048, 15214, 30482, -8848, -29259, -771, 6707, 395]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -9, 19, 36, -14, -38, 2, 12, 0], ![0, -1, -7, -9, 19, 36, -14, -38, 2, 12], ![-12, -84, -109, 221, 423, -149, -420, 10, 106, 2], ![-2, -26, -102, -71, 293, 395, -225, -416, 34, 106], ![-106, -744, -980, 1912, 3745, -1191, -3633, -13, 856, 34], ![-34, -344, -1050, -334, 3136, 3269, -2483, -3565, 395, 856], ![-856, -6026, -8048, 15214, 30482, -8848, -29259, -771, 6707, 395], ![-395, -3621, -9581, -543, 29434, 24952, -23858, -28469, 3969, 6707]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -9, 19, 36, -14, -38, 2, 12, 0], ![0, -1, -7, -9, 19, 36, -14, -38, 2, 12], ![-12, -84, -109, 221, 423, -149, -420, 10, 106, 2], ![-2, -26, -102, -71, 293, 395, -225, -416, 34, 106], ![-106, -744, -980, 1912, 3745, -1191, -3633, -13, 856, 34], ![-34, -344, -1050, -334, 3136, 3269, -2483, -3565, 395, 856], ![-856, -6026, -8048, 15214, 30482, -8848, -29259, -771, 6707, 395], ![-395, -3621, -9581, -543, 29434, 24952, -23858, -28469, 3969, 6707], ![-6707, -47344, -63984, 117852, 240909, -64464, -229914, -10444, 52015, 3969]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-2, -12, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-2, -12, 0, -1], [-106, -2, -12, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-12, 0, -1], [-2, -12, 0, -1], [-106, -2, -12, 0, -1], [-34, -106, -2, -12, 0, -1]], ![[], [], [], [-1], [0, -1], [-12, 0, -1], [-2, -12, 0, -1], [-106, -2, -12, 0, -1], [-34, -106, -2, -12, 0, -1], [-856, -34, -106, -2, -12, 0, -1]], ![[], [], [-1], [0, -1], [-12, 0, -1], [-2, -12, 0, -1], [-106, -2, -12, 0, -1], [-34, -106, -2, -12, 0, -1], [-856, -34, -106, -2, -12, 0, -1], [-395, -856, -34, -106, -2, -12, 0, -1]], ![[], [-1], [0, -1], [-12, 0, -1], [-2, -12, 0, -1], [-106, -2, -12, 0, -1], [-34, -106, -2, -12, 0, -1], [-856, -34, -106, -2, -12, 0, -1], [-395, -856, -34, -106, -2, -12, 0, -1], [-6707, -395, -856, -34, -106, -2, -12, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -9, 19, 36, -14, -38, 2, 12, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -9, 19, 36, -14, -38, 2, 12, 0], [0, -1, -7, -9, 19, 36, -14, -38, 2, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -9, 19, 36, -14, -38, 2, 12, 0], [0, -1, -7, -9, 19, 36, -14, -38, 2, 12], [-12, -84, -109, 221, 423, -149, -420, 10, 106, 2]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -9, 19, 36, -14, -38, 2, 12, 0], [0, -1, -7, -9, 19, 36, -14, -38, 2, 12], [-12, -84, -109, 221, 423, -149, -420, 10, 106, 2], [-2, -26, -102, -71, 293, 395, -225, -416, 34, 106]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -9, 19, 36, -14, -38, 2, 12, 0], [0, -1, -7, -9, 19, 36, -14, -38, 2, 12], [-12, -84, -109, 221, 423, -149, -420, 10, 106, 2], [-2, -26, -102, -71, 293, 395, -225, -416, 34, 106], [-106, -744, -980, 1912, 3745, -1191, -3633, -13, 856, 34]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -9, 19, 36, -14, -38, 2, 12, 0], [0, -1, -7, -9, 19, 36, -14, -38, 2, 12], [-12, -84, -109, 221, 423, -149, -420, 10, 106, 2], [-2, -26, -102, -71, 293, 395, -225, -416, 34, 106], [-106, -744, -980, 1912, 3745, -1191, -3633, -13, 856, 34], [-34, -344, -1050, -334, 3136, 3269, -2483, -3565, 395, 856]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -9, 19, 36, -14, -38, 2, 12, 0], [0, -1, -7, -9, 19, 36, -14, -38, 2, 12], [-12, -84, -109, 221, 423, -149, -420, 10, 106, 2], [-2, -26, -102, -71, 293, 395, -225, -416, 34, 106], [-106, -744, -980, 1912, 3745, -1191, -3633, -13, 856, 34], [-34, -344, -1050, -334, 3136, 3269, -2483, -3565, 395, 856], [-856, -6026, -8048, 15214, 30482, -8848, -29259, -771, 6707, 395]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -9, 19, 36, -14, -38, 2, 12, 0], [0, -1, -7, -9, 19, 36, -14, -38, 2, 12], [-12, -84, -109, 221, 423, -149, -420, 10, 106, 2], [-2, -26, -102, -71, 293, 395, -225, -416, 34, 106], [-106, -744, -980, 1912, 3745, -1191, -3633, -13, 856, 34], [-34, -344, -1050, -334, 3136, 3269, -2483, -3565, 395, 856], [-856, -6026, -8048, 15214, 30482, -8848, -29259, -771, 6707, 395], [-395, -3621, -9581, -543, 29434, 24952, -23858, -28469, 3969, 6707]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -9, 19, 36, -14, -38, 2, 12, 0], [0, -1, -7, -9, 19, 36, -14, -38, 2, 12], [-12, -84, -109, 221, 423, -149, -420, 10, 106, 2], [-2, -26, -102, -71, 293, 395, -225, -416, 34, 106], [-106, -744, -980, 1912, 3745, -1191, -3633, -13, 856, 34], [-34, -344, -1050, -334, 3136, 3269, -2483, -3565, 395, 856], [-856, -6026, -8048, 15214, 30482, -8848, -29259, -771, 6707, 395], [-395, -3621, -9581, -543, 29434, 24952, -23858, -28469, 3969, 6707], [-6707, -47344, -63984, 117852, 240909, -64464, -229914, -10444, 52015, 3969]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1495993801 : Fact (Nat.Prime 1495993801) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 1]
  b' := [1, 1, 4, 2, 2]
  k := [1]
  f := [0, -1, 0, 7, 12, 4, -4, 2, 4]
  g := [1, 1, 4, 4, 0, 1]
  h := [1, 1, 4, 4, 0, 1]
  a := [3, 0, 0, 3]
  b := [1, 2, 4, 3, 0, 4, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1495993801 : CertificateDedekindCriterionLists l 1495993801 where
  n := 2
  a' := [782155247, 1240230096, 83387277, 407589586, 1338291088, 1252987815, 399533960, 183701551]
  b' := [634049228, 1130372210, 1205486468, 1021461161, 456351019, 824454914, 488318459, 644793302, 145810250]
  k := [268115034, 1219234144, 221739562, 1043714153, 305080094, 1494045929, 629803679, 1388492988, 1]
  f := [432396154, 477840384, 656693946, 113083637, 611474180, 8267739, 573451264, 379759236, 372067222, 1]
  g := [806815265, 891610418, 1225336291, 211004661, 1140959969, 15426912, 1070012370, 708599152, 694246494, 1]
  h := [801747307, 1]
  a := [387520731, 827631920, 359142191, 1355505548, 953365464, 1425578426, 1024658002, 462653837, 130611474]
  b := [1299125748, 1152636166, 107790602, 677918098, 28886559, 753148346, 560541936, 675107426, 1365382327]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 1495993801]
  exp := ![1, 1]
  pdgood := [5, 1495993801]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1495993801.out
  a := [-6559407303465, -7382163592704, 63600753545440, 43903239257246, -126754419580438, -33653160269142, 60186793425148, 4727219482890, -6623955775580]
  b := [938126753210, 5201676165597, 993158755271, -19084120600062, -6554013334647, 22210724220998, 4102411356273, -7608428728654, -472721948289, 662395577558]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1495993801 T_ofList CD1495993801

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

end VoightMaximalOrderD10R361

namespace VoightMaximalOrderD10R362

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4678913433357, [1, -5, -3, 30, -2, -44, 13, 21, -9, -2, 1], 1⟩
local notation "l" => [1, -5, -3, 30, -2, -44, 13, 21, -9, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -30, 2, 44, -13, -21, 9, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -30, 2, 44, -13, -21, 9, 2], ![-2, 9, 11, -57, -26, 90, 18, -55, -3, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -30, 2, 44, -13, -21, 9, 2], ![-2, 9, 11, -57, -26, 90, 18, -55, -3, 13], ![-13, 63, 48, -379, -31, 546, -79, -255, 62, 23]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -30, 2, 44, -13, -21, 9, 2], ![-2, 9, 11, -57, -26, 90, 18, -55, -3, 13], ![-13, 63, 48, -379, -31, 546, -79, -255, 62, 23], ![-23, 102, 132, -642, -333, 981, 247, -562, -48, 108]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -30, 2, 44, -13, -21, 9, 2], ![-2, 9, 11, -57, -26, 90, 18, -55, -3, 13], ![-13, 63, 48, -379, -31, 546, -79, -255, 62, 23], ![-23, 102, 132, -642, -333, 981, 247, -562, -48, 108], ![-108, 517, 426, -3108, -426, 4419, -423, -2021, 410, 168]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -30, 2, 44, -13, -21, 9, 2], ![-2, 9, 11, -57, -26, 90, 18, -55, -3, 13], ![-13, 63, 48, -379, -31, 546, -79, -255, 62, 23], ![-23, 102, 132, -642, -333, 981, 247, -562, -48, 108], ![-108, 517, 426, -3108, -426, 4419, -423, -2021, 410, 168], ![-168, 732, 1021, -4614, -2772, 6966, 2235, -3951, -509, 746]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -30, 2, 44, -13, -21, 9, 2], ![-2, 9, 11, -57, -26, 90, 18, -55, -3, 13], ![-13, 63, 48, -379, -31, 546, -79, -255, 62, 23], ![-23, 102, 132, -642, -333, 981, 247, -562, -48, 108], ![-108, 517, 426, -3108, -426, 4419, -423, -2021, 410, 168], ![-168, 732, 1021, -4614, -2772, 6966, 2235, -3951, -509, 746], ![-746, 3562, 2970, -21359, -3122, 30052, -2732, -13431, 2763, 983]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -30, 2, 44, -13, -21, 9, 2], ![-2, 9, 11, -57, -26, 90, 18, -55, -3, 13], ![-13, 63, 48, -379, -31, 546, -79, -255, 62, 23], ![-23, 102, 132, -642, -333, 981, 247, -562, -48, 108], ![-108, 517, 426, -3108, -426, 4419, -423, -2021, 410, 168], ![-168, 732, 1021, -4614, -2772, 6966, 2235, -3951, -509, 746], ![-746, 3562, 2970, -21359, -3122, 30052, -2732, -13431, 2763, 983], ![-983, 4169, 6511, -26520, -19393, 40130, 17273, -23375, -4584, 4729]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -30, 2, 44, -13, -21, 9, 2], ![-2, 9, 11, -57, -26, 90, 18, -55, -3, 13], ![-13, 63, 48, -379, -31, 546, -79, -255, 62, 23], ![-23, 102, 132, -642, -333, 981, 247, -562, -48, 108], ![-108, 517, 426, -3108, -426, 4419, -423, -2021, 410, 168], ![-168, 732, 1021, -4614, -2772, 6966, 2235, -3951, -509, 746], ![-746, 3562, 2970, -21359, -3122, 30052, -2732, -13431, 2763, 983], ![-983, 4169, 6511, -26520, -19393, 40130, 17273, -23375, -4584, 4729], ![-4729, 22662, 18356, -135359, -17062, 188683, -21347, -82036, 19186, 4874]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-23, -13, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-23, -13, -2, -1], [-108, -23, -13, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-23, -13, -2, -1], [-108, -23, -13, -2, -1], [-168, -108, -23, -13, -2, -1]], ![[], [], [], [-1], [-2, -1], [-13, -2, -1], [-23, -13, -2, -1], [-108, -23, -13, -2, -1], [-168, -108, -23, -13, -2, -1], [-746, -168, -108, -23, -13, -2, -1]], ![[], [], [-1], [-2, -1], [-13, -2, -1], [-23, -13, -2, -1], [-108, -23, -13, -2, -1], [-168, -108, -23, -13, -2, -1], [-746, -168, -108, -23, -13, -2, -1], [-983, -746, -168, -108, -23, -13, -2, -1]], ![[], [-1], [-2, -1], [-13, -2, -1], [-23, -13, -2, -1], [-108, -23, -13, -2, -1], [-168, -108, -23, -13, -2, -1], [-746, -168, -108, -23, -13, -2, -1], [-983, -746, -168, -108, -23, -13, -2, -1], [-4729, -983, -746, -168, -108, -23, -13, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -30, 2, 44, -13, -21, 9, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -30, 2, 44, -13, -21, 9, 2], [-2, 9, 11, -57, -26, 90, 18, -55, -3, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -30, 2, 44, -13, -21, 9, 2], [-2, 9, 11, -57, -26, 90, 18, -55, -3, 13], [-13, 63, 48, -379, -31, 546, -79, -255, 62, 23]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -30, 2, 44, -13, -21, 9, 2], [-2, 9, 11, -57, -26, 90, 18, -55, -3, 13], [-13, 63, 48, -379, -31, 546, -79, -255, 62, 23], [-23, 102, 132, -642, -333, 981, 247, -562, -48, 108]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -30, 2, 44, -13, -21, 9, 2], [-2, 9, 11, -57, -26, 90, 18, -55, -3, 13], [-13, 63, 48, -379, -31, 546, -79, -255, 62, 23], [-23, 102, 132, -642, -333, 981, 247, -562, -48, 108], [-108, 517, 426, -3108, -426, 4419, -423, -2021, 410, 168]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -30, 2, 44, -13, -21, 9, 2], [-2, 9, 11, -57, -26, 90, 18, -55, -3, 13], [-13, 63, 48, -379, -31, 546, -79, -255, 62, 23], [-23, 102, 132, -642, -333, 981, 247, -562, -48, 108], [-108, 517, 426, -3108, -426, 4419, -423, -2021, 410, 168], [-168, 732, 1021, -4614, -2772, 6966, 2235, -3951, -509, 746]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -30, 2, 44, -13, -21, 9, 2], [-2, 9, 11, -57, -26, 90, 18, -55, -3, 13], [-13, 63, 48, -379, -31, 546, -79, -255, 62, 23], [-23, 102, 132, -642, -333, 981, 247, -562, -48, 108], [-108, 517, 426, -3108, -426, 4419, -423, -2021, 410, 168], [-168, 732, 1021, -4614, -2772, 6966, 2235, -3951, -509, 746], [-746, 3562, 2970, -21359, -3122, 30052, -2732, -13431, 2763, 983]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -30, 2, 44, -13, -21, 9, 2], [-2, 9, 11, -57, -26, 90, 18, -55, -3, 13], [-13, 63, 48, -379, -31, 546, -79, -255, 62, 23], [-23, 102, 132, -642, -333, 981, 247, -562, -48, 108], [-108, 517, 426, -3108, -426, 4419, -423, -2021, 410, 168], [-168, 732, 1021, -4614, -2772, 6966, 2235, -3951, -509, 746], [-746, 3562, 2970, -21359, -3122, 30052, -2732, -13431, 2763, 983], [-983, 4169, 6511, -26520, -19393, 40130, 17273, -23375, -4584, 4729]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -30, 2, 44, -13, -21, 9, 2], [-2, 9, 11, -57, -26, 90, 18, -55, -3, 13], [-13, 63, 48, -379, -31, 546, -79, -255, 62, 23], [-23, 102, 132, -642, -333, 981, 247, -562, -48, 108], [-108, 517, 426, -3108, -426, 4419, -423, -2021, 410, 168], [-168, 732, 1021, -4614, -2772, 6966, 2235, -3951, -509, 746], [-746, 3562, 2970, -21359, -3122, 30052, -2732, -13431, 2763, 983], [-983, 4169, 6511, -26520, -19393, 40130, 17273, -23375, -4584, 4729], [-4729, 22662, 18356, -135359, -17062, 188683, -21347, -82036, 19186, 4874]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp286519 : Fact (Nat.Prime 286519) := fact_iff.2 (by norm_num)
instance hp1814467 : Fact (Nat.Prime 1814467) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 2
  a' := [0, 0, 1, 2, 2]
  b' := [1, 2, 0, 1, 0, 2]
  k := [1, 1, 1, 1, 1, 1, 1]
  f := [0, 2, 2, -9, 2, 16, -3, -6, 4, 1]
  g := [1, 1, 2, 2, 2, 2, 2, 1, 1]
  h := [1, 0, 1]
  a := [1, 2, 0, 0, 1, 2]
  b := [1, 0, 1, 2, 1, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD286519 : CertificateDedekindCriterionLists l 286519 where
  n := 2
  a' := [256682, 262977, 249282, 45245, 53554, 182388, 117510, 204581]
  b' := [73193, 184341, 257825, 86724, 124810, 35411, 273008, 53646, 136446]
  k := [172628, 129004, 153434, 5127, 105350, 249701, 116022, 52096, 1]
  f := [117211, 38422, 242533, 107332, 19963, 180307, 177304, 19366, 23679, 1]
  g := [128933, 42264, 266788, 118065, 21959, 198339, 195035, 21302, 26047, 1]
  h := [260470, 1]
  a := [181807, 126104, 182891, 113344, 176894, 190650, 286491, 253049, 212279]
  b := [54423, 62697, 16968, 144027, 122083, 176410, 130785, 155816, 74240]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1814467 : CertificateDedekindCriterionLists l 1814467 where
  n := 2
  a' := [70821, 205662, 1748283, 1166189, 653037, 265694, 843240, 1203966]
  b' := [155549, 160428, 532219, 760161, 929736, 1175724, 983198, 223974, 1680693]
  k := [1761148, 1363160, 872916, 62967, 656161, 477845, 666003, 277038, 1]
  f := [800987, 1072155, 1034239, 763815, 680439, 1221927, 464077, 1237049, 127944, 1]
  g := [867190, 1160770, 1119720, 826945, 736678, 1322921, 502433, 1339293, 138518, 1]
  h := [1675947, 1]
  a := [457649, 846699, 1595809, 608958, 668447, 1622150, 1441986, 346721, 412083]
  b := [129243, 1327537, 1349518, 1616288, 1700491, 1519048, 1460854, 483654, 1402384]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![3, 286519, 1814467]
  exp := ![1, 1, 1]
  pdgood := [3, 286519, 1814467]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp286519.out
    exact hp1814467.out
  a := [-14570438728216, -62764580982932, 92786647234087, 188212534736452, -186495668334134, -139876252653998, 118656538360640, 16729146853040, -15436469730800]
  b := [-3226015307867, 5888740901070, 24929409043789, -23664354207033, -42293691208959, 31115034371748, 21474676610703, -14865348360856, -1981644079920, 1543646973080]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 286519 T_ofList CD286519
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1814467 T_ofList CD1814467

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

end VoightMaximalOrderD10R362

namespace VoightMaximalOrderD10R363

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4680561913309, [17, -48, -29, 126, 20, -112, -5, 39, -3, -5, 1], 1⟩
local notation "l" => [17, -48, -29, 126, 20, -112, -5, 39, -3, -5, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-17, 48, 29, -126, -20, 112, 5, -39, 3, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-17, 48, 29, -126, -20, 112, 5, -39, 3, 5], ![-85, 223, 193, -601, -226, 540, 137, -190, -24, 28]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-17, 48, 29, -126, -20, 112, 5, -39, 3, 5], ![-85, 223, 193, -601, -226, 540, 137, -190, -24, 28], ![-476, 1259, 1035, -3335, -1161, 2910, 680, -955, -106, 116]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-17, 48, 29, -126, -20, 112, 5, -39, 3, 5], ![-85, 223, 193, -601, -226, 540, 137, -190, -24, 28], ![-476, 1259, 1035, -3335, -1161, 2910, 680, -955, -106, 116], ![-1972, 5092, 4623, -13581, -5655, 11831, 3490, -3844, -607, 474]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-17, 48, 29, -126, -20, 112, 5, -39, 3, 5], ![-85, 223, 193, -601, -226, 540, 137, -190, -24, 28], ![-476, 1259, 1035, -3335, -1161, 2910, 680, -955, -106, 116], ![-1972, 5092, 4623, -13581, -5655, 11831, 3490, -3844, -607, 474], ![-8058, 20780, 18838, -55101, -23061, 47433, 14201, -14996, -2422, 1763]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-17, 48, 29, -126, -20, 112, 5, -39, 3, 5], ![-85, 223, 193, -601, -226, 540, 137, -190, -24, 28], ![-476, 1259, 1035, -3335, -1161, 2910, 680, -955, -106, 116], ![-1972, 5092, 4623, -13581, -5655, 11831, 3490, -3844, -607, 474], ![-8058, 20780, 18838, -55101, -23061, 47433, 14201, -14996, -2422, 1763], ![-29971, 76566, 71907, -203300, -90361, 174395, 56248, -54556, -9707, 6393]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-17, 48, 29, -126, -20, 112, 5, -39, 3, 5], ![-85, 223, 193, -601, -226, 540, 137, -190, -24, 28], ![-476, 1259, 1035, -3335, -1161, 2910, 680, -955, -106, 116], ![-1972, 5092, 4623, -13581, -5655, 11831, 3490, -3844, -607, 474], ![-8058, 20780, 18838, -55101, -23061, 47433, 14201, -14996, -2422, 1763], ![-29971, 76566, 71907, -203300, -90361, 174395, 56248, -54556, -9707, 6393], ![-108681, 276893, 261963, -733611, -331160, 625655, 206360, -193079, -35377, 22258]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-17, 48, 29, -126, -20, 112, 5, -39, 3, 5], ![-85, 223, 193, -601, -226, 540, 137, -190, -24, 28], ![-476, 1259, 1035, -3335, -1161, 2910, 680, -955, -106, 116], ![-1972, 5092, 4623, -13581, -5655, 11831, 3490, -3844, -607, 474], ![-8058, 20780, 18838, -55101, -23061, 47433, 14201, -14996, -2422, 1763], ![-29971, 76566, 71907, -203300, -90361, 174395, 56248, -54556, -9707, 6393], ![-108681, 276893, 261963, -733611, -331160, 625655, 206360, -193079, -35377, 22258], ![-378386, 959703, 922375, -2542545, -1178771, 2161736, 736945, -661702, -126305, 75913]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-17, 48, 29, -126, -20, 112, 5, -39, 3, 5], ![-85, 223, 193, -601, -226, 540, 137, -190, -24, 28], ![-476, 1259, 1035, -3335, -1161, 2910, 680, -955, -106, 116], ![-1972, 5092, 4623, -13581, -5655, 11831, 3490, -3844, -607, 474], ![-8058, 20780, 18838, -55101, -23061, 47433, 14201, -14996, -2422, 1763], ![-29971, 76566, 71907, -203300, -90361, 174395, 56248, -54556, -9707, 6393], ![-108681, 276893, 261963, -733611, -331160, 625655, 206360, -193079, -35377, 22258], ![-378386, 959703, 922375, -2542545, -1178771, 2161736, 736945, -661702, -126305, 75913], ![-1290521, 3265438, 3161180, -8642663, -4060805, 7323485, 2541301, -2223662, -433963, 253260]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-5, -1]], ![[], [], [], [], [], [], [], [-1], [-5, -1], [-28, -5, -1]], ![[], [], [], [], [], [], [-1], [-5, -1], [-28, -5, -1], [-116, -28, -5, -1]], ![[], [], [], [], [], [-1], [-5, -1], [-28, -5, -1], [-116, -28, -5, -1], [-474, -116, -28, -5, -1]], ![[], [], [], [], [-1], [-5, -1], [-28, -5, -1], [-116, -28, -5, -1], [-474, -116, -28, -5, -1], [-1763, -474, -116, -28, -5, -1]], ![[], [], [], [-1], [-5, -1], [-28, -5, -1], [-116, -28, -5, -1], [-474, -116, -28, -5, -1], [-1763, -474, -116, -28, -5, -1], [-6393, -1763, -474, -116, -28, -5, -1]], ![[], [], [-1], [-5, -1], [-28, -5, -1], [-116, -28, -5, -1], [-474, -116, -28, -5, -1], [-1763, -474, -116, -28, -5, -1], [-6393, -1763, -474, -116, -28, -5, -1], [-22258, -6393, -1763, -474, -116, -28, -5, -1]], ![[], [-1], [-5, -1], [-28, -5, -1], [-116, -28, -5, -1], [-474, -116, -28, -5, -1], [-1763, -474, -116, -28, -5, -1], [-6393, -1763, -474, -116, -28, -5, -1], [-22258, -6393, -1763, -474, -116, -28, -5, -1], [-75913, -22258, -6393, -1763, -474, -116, -28, -5, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-17, 48, 29, -126, -20, 112, 5, -39, 3, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-17, 48, 29, -126, -20, 112, 5, -39, 3, 5], [-85, 223, 193, -601, -226, 540, 137, -190, -24, 28]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-17, 48, 29, -126, -20, 112, 5, -39, 3, 5], [-85, 223, 193, -601, -226, 540, 137, -190, -24, 28], [-476, 1259, 1035, -3335, -1161, 2910, 680, -955, -106, 116]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-17, 48, 29, -126, -20, 112, 5, -39, 3, 5], [-85, 223, 193, -601, -226, 540, 137, -190, -24, 28], [-476, 1259, 1035, -3335, -1161, 2910, 680, -955, -106, 116], [-1972, 5092, 4623, -13581, -5655, 11831, 3490, -3844, -607, 474]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-17, 48, 29, -126, -20, 112, 5, -39, 3, 5], [-85, 223, 193, -601, -226, 540, 137, -190, -24, 28], [-476, 1259, 1035, -3335, -1161, 2910, 680, -955, -106, 116], [-1972, 5092, 4623, -13581, -5655, 11831, 3490, -3844, -607, 474], [-8058, 20780, 18838, -55101, -23061, 47433, 14201, -14996, -2422, 1763]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-17, 48, 29, -126, -20, 112, 5, -39, 3, 5], [-85, 223, 193, -601, -226, 540, 137, -190, -24, 28], [-476, 1259, 1035, -3335, -1161, 2910, 680, -955, -106, 116], [-1972, 5092, 4623, -13581, -5655, 11831, 3490, -3844, -607, 474], [-8058, 20780, 18838, -55101, -23061, 47433, 14201, -14996, -2422, 1763], [-29971, 76566, 71907, -203300, -90361, 174395, 56248, -54556, -9707, 6393]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-17, 48, 29, -126, -20, 112, 5, -39, 3, 5], [-85, 223, 193, -601, -226, 540, 137, -190, -24, 28], [-476, 1259, 1035, -3335, -1161, 2910, 680, -955, -106, 116], [-1972, 5092, 4623, -13581, -5655, 11831, 3490, -3844, -607, 474], [-8058, 20780, 18838, -55101, -23061, 47433, 14201, -14996, -2422, 1763], [-29971, 76566, 71907, -203300, -90361, 174395, 56248, -54556, -9707, 6393], [-108681, 276893, 261963, -733611, -331160, 625655, 206360, -193079, -35377, 22258]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-17, 48, 29, -126, -20, 112, 5, -39, 3, 5], [-85, 223, 193, -601, -226, 540, 137, -190, -24, 28], [-476, 1259, 1035, -3335, -1161, 2910, 680, -955, -106, 116], [-1972, 5092, 4623, -13581, -5655, 11831, 3490, -3844, -607, 474], [-8058, 20780, 18838, -55101, -23061, 47433, 14201, -14996, -2422, 1763], [-29971, 76566, 71907, -203300, -90361, 174395, 56248, -54556, -9707, 6393], [-108681, 276893, 261963, -733611, -331160, 625655, 206360, -193079, -35377, 22258], [-378386, 959703, 922375, -2542545, -1178771, 2161736, 736945, -661702, -126305, 75913]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-17, 48, 29, -126, -20, 112, 5, -39, 3, 5], [-85, 223, 193, -601, -226, 540, 137, -190, -24, 28], [-476, 1259, 1035, -3335, -1161, 2910, 680, -955, -106, 116], [-1972, 5092, 4623, -13581, -5655, 11831, 3490, -3844, -607, 474], [-8058, 20780, 18838, -55101, -23061, 47433, 14201, -14996, -2422, 1763], [-29971, 76566, 71907, -203300, -90361, 174395, 56248, -54556, -9707, 6393], [-108681, 276893, 261963, -733611, -331160, 625655, 206360, -193079, -35377, 22258], [-378386, 959703, 922375, -2542545, -1178771, 2161736, 736945, -661702, -126305, 75913], [-1290521, 3265438, 3161180, -8642663, -4060805, 7323485, 2541301, -2223662, -433963, 253260]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp23 : Fact (Nat.Prime 23) := fact_iff.2 (by norm_num)
instance hp61 : Fact (Nat.Prime 61) := fact_iff.2 (by norm_num)
instance hp347 : Fact (Nat.Prime 347) := fact_iff.2 (by norm_num)
instance hp397 : Fact (Nat.Prime 397) := fact_iff.2 (by norm_num)

def CD23 : CertificateDedekindCriterionLists l 23 where
  n := 2
  a' := [20, 5, 0, 12, 16, 2, 4, 20]
  b' := [1, 19, 22, 17, 8, 19, 16, 5, 8]
  k := [11, 14, 14, 19, 18, 10, 8, 0, 1]
  f := [2, 11, 3, -5, 7, 12, 6, 2, 4, 1]
  g := [7, 22, 2, 1, 20, 16, 13, 8, 9, 1]
  h := [9, 1]
  a := [1, 6, 11, 8, 11, 0, 13, 15, 3]
  b := [13, 15, 15, 14, 7, 20, 14, 0, 20]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD61 : CertificateDedekindCriterionLists l 61 where
  n := 2
  a' := [60, 38, 3, 48, 6, 25, 26]
  b' := [16, 22, 11, 38, 26, 44, 56, 12]
  k := [28, 39, 37, 12, 6, 33, 1]
  f := [13, 51, 44, 17, 8, 23, 20, 6, 10, 1]
  g := [54, 53, 25, 4, 21, 27, 4, 14, 1]
  h := [15, 42, 1]
  a := [54, 58, 55, 10, 16, 43, 44, 18]
  b := [13, 7, 5, 18, 55, 41, 4, 28, 43]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD347 : CertificateDedekindCriterionLists l 347 where
  n := 2
  a' := [255, 288, 322, 182, 34, 62, 77, 160]
  b' := [136, 305, 99, 342, 93, 29, 19, 283, 175]
  k := [303, 214, 72, 105, 118, 217, 231, 265, 1]
  f := [25, 131, 129, 76, 84, 195, 161, 121, 80, 1]
  g := [41, 214, 210, 124, 137, 318, 262, 197, 130, 1]
  h := [212, 1]
  a := [213, 124, 231, 216, 286, 38, 290, 181, 144]
  b := [251, 185, 257, 189, 25, 313, 131, 79, 203]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD397 : CertificateDedekindCriterionLists l 397 where
  n := 2
  a' := [288, 68, 45, 142, 257, 90, 160]
  b' := [151, 202, 250, 225, 86, 188, 195, 377]
  k := [213, 377, 234, 396, 23, 237, 1]
  f := [83, 308, 330, 296, 198, 262, 30, 54, 81, 1]
  g := [317, 334, 370, 146, 365, 29, 34, 116, 1]
  h := [104, 276, 1]
  a := [369, 250, 76, 187, 255, 341, 293, 370]
  b := [95, 310, 208, 24, 126, 170, 180, 350, 27]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![23, 61, 347, 397]
  exp := ![1, 1, 1, 1]
  pdgood := [23, 61, 347, 397]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp23.out
    exact hp61.out
    exact hp347.out
    exact hp397.out
  a := [1946875061, 236356892, -17428633177, 11351063416, 17899584673, -12978665766, -3233628038, 3725227440, -647880680]
  b := [685491670, -2691467763, 1065202290, 5076607599, -3279141753, -2860574921, 2047242737, 324978182, -404916778, 64788068]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 23 T_ofList CD23
    exact satisfiesDedekindCriterion_of_certificate_lists T l 61 T_ofList CD61
    exact satisfiesDedekindCriterion_of_certificate_lists T l 347 T_ofList CD347
    exact satisfiesDedekindCriterion_of_certificate_lists T l 397 T_ofList CD397

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

end VoightMaximalOrderD10R363

end TraceEuclidean
