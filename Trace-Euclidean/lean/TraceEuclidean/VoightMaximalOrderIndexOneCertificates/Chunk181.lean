import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk177
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

namespace VoightMaximalOrderD10R137

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2529518215625, [-1, -5, 13, 51, -20, -58, 17, 23, -7, -3, 1], 1⟩
local notation "l" => [-1, -5, 13, 51, -20, -58, 17, 23, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -13, -51, 20, 58, -17, -23, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -13, -51, 20, 58, -17, -23, 7, 3], ![3, 16, -34, -166, 9, 194, 7, -86, -2, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -13, -51, 20, 58, -17, -23, 7, 3], ![3, 16, -34, -166, 9, 194, 7, -86, -2, 16], ![16, 83, -192, -850, 154, 937, -78, -361, 26, 46]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -13, -51, 20, 58, -17, -23, 7, 3], ![3, 16, -34, -166, 9, 194, 7, -86, -2, 16], ![16, 83, -192, -850, 154, 937, -78, -361, 26, 46], ![46, 246, -515, -2538, 70, 2822, 155, -1136, -39, 164]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -13, -51, 20, 58, -17, -23, 7, 3], ![3, 16, -34, -166, 9, 194, 7, -86, -2, 16], ![16, 83, -192, -850, 154, 937, -78, -361, 26, 46], ![46, 246, -515, -2538, 70, 2822, 155, -1136, -39, 164], ![164, 866, -1886, -8879, 742, 9582, 34, -3617, 12, 453]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -13, -51, 20, 58, -17, -23, 7, 3], ![3, 16, -34, -166, 9, 194, 7, -86, -2, 16], ![16, 83, -192, -850, 154, 937, -78, -361, 26, 46], ![46, 246, -515, -2538, 70, 2822, 155, -1136, -39, 164], ![164, 866, -1886, -8879, 742, 9582, 34, -3617, 12, 453], ![453, 2429, -5023, -24989, 181, 27016, 1881, -10385, -446, 1371]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -13, -51, 20, 58, -17, -23, 7, 3], ![3, 16, -34, -166, 9, 194, 7, -86, -2, 16], ![16, 83, -192, -850, 154, 937, -78, -361, 26, 46], ![46, 246, -515, -2538, 70, 2822, 155, -1136, -39, 164], ![164, 866, -1886, -8879, 742, 9582, 34, -3617, 12, 453], ![453, 2429, -5023, -24989, 181, 27016, 1881, -10385, -446, 1371], ![1371, 7308, -15394, -74944, 2431, 79699, 3709, -29652, -788, 3667]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -13, -51, 20, 58, -17, -23, 7, 3], ![3, 16, -34, -166, 9, 194, 7, -86, -2, 16], ![16, 83, -192, -850, 154, 937, -78, -361, 26, 46], ![46, 246, -515, -2538, 70, 2822, 155, -1136, -39, 164], ![164, 866, -1886, -8879, 742, 9582, 34, -3617, 12, 453], ![453, 2429, -5023, -24989, 181, 27016, 1881, -10385, -446, 1371], ![1371, 7308, -15394, -74944, 2431, 79699, 3709, -29652, -788, 3667], ![3667, 19706, -40363, -202411, -1604, 215117, 17360, -80632, -3983, 10213]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -13, -51, 20, 58, -17, -23, 7, 3], ![3, 16, -34, -166, 9, 194, 7, -86, -2, 16], ![16, 83, -192, -850, 154, 937, -78, -361, 26, 46], ![46, 246, -515, -2538, 70, 2822, 155, -1136, -39, 164], ![164, 866, -1886, -8879, 742, 9582, 34, -3617, 12, 453], ![453, 2429, -5023, -24989, 181, 27016, 1881, -10385, -446, 1371], ![1371, 7308, -15394, -74944, 2431, 79699, 3709, -29652, -788, 3667], ![3667, 19706, -40363, -202411, -1604, 215117, 17360, -80632, -3983, 10213], ![10213, 54732, -113063, -561226, 1849, 590750, 41496, -217539, -9141, 26656]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-164, -46, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-164, -46, -16, -3, -1], [-453, -164, -46, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-164, -46, -16, -3, -1], [-453, -164, -46, -16, -3, -1], [-1371, -453, -164, -46, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-164, -46, -16, -3, -1], [-453, -164, -46, -16, -3, -1], [-1371, -453, -164, -46, -16, -3, -1], [-3667, -1371, -453, -164, -46, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-164, -46, -16, -3, -1], [-453, -164, -46, -16, -3, -1], [-1371, -453, -164, -46, -16, -3, -1], [-3667, -1371, -453, -164, -46, -16, -3, -1], [-10213, -3667, -1371, -453, -164, -46, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -13, -51, 20, 58, -17, -23, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -13, -51, 20, 58, -17, -23, 7, 3], [3, 16, -34, -166, 9, 194, 7, -86, -2, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -13, -51, 20, 58, -17, -23, 7, 3], [3, 16, -34, -166, 9, 194, 7, -86, -2, 16], [16, 83, -192, -850, 154, 937, -78, -361, 26, 46]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -13, -51, 20, 58, -17, -23, 7, 3], [3, 16, -34, -166, 9, 194, 7, -86, -2, 16], [16, 83, -192, -850, 154, 937, -78, -361, 26, 46], [46, 246, -515, -2538, 70, 2822, 155, -1136, -39, 164]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -13, -51, 20, 58, -17, -23, 7, 3], [3, 16, -34, -166, 9, 194, 7, -86, -2, 16], [16, 83, -192, -850, 154, 937, -78, -361, 26, 46], [46, 246, -515, -2538, 70, 2822, 155, -1136, -39, 164], [164, 866, -1886, -8879, 742, 9582, 34, -3617, 12, 453]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -13, -51, 20, 58, -17, -23, 7, 3], [3, 16, -34, -166, 9, 194, 7, -86, -2, 16], [16, 83, -192, -850, 154, 937, -78, -361, 26, 46], [46, 246, -515, -2538, 70, 2822, 155, -1136, -39, 164], [164, 866, -1886, -8879, 742, 9582, 34, -3617, 12, 453], [453, 2429, -5023, -24989, 181, 27016, 1881, -10385, -446, 1371]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -13, -51, 20, 58, -17, -23, 7, 3], [3, 16, -34, -166, 9, 194, 7, -86, -2, 16], [16, 83, -192, -850, 154, 937, -78, -361, 26, 46], [46, 246, -515, -2538, 70, 2822, 155, -1136, -39, 164], [164, 866, -1886, -8879, 742, 9582, 34, -3617, 12, 453], [453, 2429, -5023, -24989, 181, 27016, 1881, -10385, -446, 1371], [1371, 7308, -15394, -74944, 2431, 79699, 3709, -29652, -788, 3667]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -13, -51, 20, 58, -17, -23, 7, 3], [3, 16, -34, -166, 9, 194, 7, -86, -2, 16], [16, 83, -192, -850, 154, 937, -78, -361, 26, 46], [46, 246, -515, -2538, 70, 2822, 155, -1136, -39, 164], [164, 866, -1886, -8879, 742, 9582, 34, -3617, 12, 453], [453, 2429, -5023, -24989, 181, 27016, 1881, -10385, -446, 1371], [1371, 7308, -15394, -74944, 2431, 79699, 3709, -29652, -788, 3667], [3667, 19706, -40363, -202411, -1604, 215117, 17360, -80632, -3983, 10213]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -13, -51, 20, 58, -17, -23, 7, 3], [3, 16, -34, -166, 9, 194, 7, -86, -2, 16], [16, 83, -192, -850, 154, 937, -78, -361, 26, 46], [46, 246, -515, -2538, 70, 2822, 155, -1136, -39, 164], [164, 866, -1886, -8879, 742, 9582, 34, -3617, 12, 453], [453, 2429, -5023, -24989, 181, 27016, 1881, -10385, -446, 1371], [1371, 7308, -15394, -74944, 2431, 79699, 3709, -29652, -788, 3667], [3667, 19706, -40363, -202411, -1604, 215117, 17360, -80632, -3983, 10213], [10213, 54732, -113063, -561226, 1849, 590750, 41496, -217539, -9141, 26656]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp809445829 : Fact (Nat.Prime 809445829) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 2, 3]
  b' := [4, 3, 2, 4, 3]
  k := [1]
  f := [2, 1, 1, -9, 7, 14, -2, -3, 2, 1]
  g := [3, 0, 3, 1, 1, 1]
  h := [3, 0, 3, 1, 1, 1]
  a := [1, 4, 3, 3, 4]
  b := [3, 2, 0, 4, 0, 2, 4, 3, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD809445829 : CertificateDedekindCriterionLists l 809445829 where
  n := 2
  a' := [698447694, 147204704, 488031501, 741684738, 638723667, 699073642, 780279991, 649230537]
  b' := [550494552, 155904744, 396648697, 223112348, 223058140, 253291431, 597759442, 182190031, 197678550]
  k := [641694453, 253634267, 745971285, 714298940, 374146885, 767546672, 333287696, 437618242, 1]
  f := [32892109, 17075946, 104382643, 46309551, 14313294, 167268822, 145482009, 68217286, 143213049, 1]
  g := [143208205, 74346572, 454469214, 201626098, 62318324, 728267918, 633410805, 297009686, 623532034, 1]
  h := [185913792, 1]
  a := [410575887, 284186048, 32225241, 439026899, 511704711, 673980525, 50648264, 468811971, 115282160]
  b := [183032861, 692454735, 29040660, 696590286, 440521419, 169505030, 132431980, 353603363, 694163669]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 809445829]
  exp := ![1, 1]
  pdgood := [5, 809445829]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp809445829.out
  a := [2706945870, -50372084038, -652322347, 121055505104, -20499248986, -86695125054, 24687447548, 17217561072, -6015224160]
  b := [-1350835003, 343128922, 17989327072, -1257743463, -26483224259, 4529202584, 12765879684, -3281582462, -1902212832, 601522416]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 809445829 T_ofList CD809445829

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

end VoightMaximalOrderD10R137

namespace VoightMaximalOrderD10R138

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2532033378125, [-1, -5, 9, 31, -15, -43, 13, 20, -6, -3, 1], 1⟩
local notation "l" => [-1, -5, 9, 31, -15, -43, 13, 20, -6, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -9, -31, 15, 43, -13, -20, 6, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -9, -31, 15, 43, -13, -20, 6, 3], ![3, 16, -22, -102, 14, 144, 4, -73, -2, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -9, -31, 15, 43, -13, -20, 6, 3], ![3, 16, -22, -102, 14, 144, 4, -73, -2, 15], ![15, 78, -119, -487, 123, 659, -51, -296, 17, 43]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -9, -31, 15, 43, -13, -20, 6, 3], ![3, 16, -22, -102, 14, 144, 4, -73, -2, 15], ![15, 78, -119, -487, 123, 659, -51, -296, 17, 43], ![43, 230, -309, -1452, 158, 1972, 100, -911, -38, 146]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -9, -31, 15, 43, -13, -20, 6, 3], ![3, 16, -22, -102, 14, 144, 4, -73, -2, 15], ![15, 78, -119, -487, 123, 659, -51, -296, 17, 43], ![43, 230, -309, -1452, 158, 1972, 100, -911, -38, 146], ![146, 773, -1084, -4835, 738, 6436, 74, -2820, -35, 400]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -9, -31, 15, 43, -13, -20, 6, 3], ![3, 16, -22, -102, 14, 144, 4, -73, -2, 15], ![15, 78, -119, -487, 123, 659, -51, -296, 17, 43], ![43, 230, -309, -1452, 158, 1972, 100, -911, -38, 146], ![146, 773, -1084, -4835, 738, 6436, 74, -2820, -35, 400], ![400, 2146, -2827, -13484, 1165, 17938, 1236, -7926, -420, 1165]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -9, -31, 15, 43, -13, -20, 6, 3], ![3, 16, -22, -102, 14, 144, 4, -73, -2, 15], ![15, 78, -119, -487, 123, 659, -51, -296, 17, 43], ![43, 230, -309, -1452, 158, 1972, 100, -911, -38, 146], ![146, 773, -1084, -4835, 738, 6436, 74, -2820, -35, 400], ![400, 2146, -2827, -13484, 1165, 17938, 1236, -7926, -420, 1165], ![1165, 6225, -8339, -38942, 3991, 51260, 2793, -22064, -936, 3075]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -9, -31, 15, 43, -13, -20, 6, 3], ![3, 16, -22, -102, 14, 144, 4, -73, -2, 15], ![15, 78, -119, -487, 123, 659, -51, -296, 17, 43], ![43, 230, -309, -1452, 158, 1972, 100, -911, -38, 146], ![146, 773, -1084, -4835, 738, 6436, 74, -2820, -35, 400], ![400, 2146, -2827, -13484, 1165, 17938, 1236, -7926, -420, 1165], ![1165, 6225, -8339, -38942, 3991, 51260, 2793, -22064, -936, 3075], ![3075, 16540, -21450, -103664, 7183, 136216, 11285, -58707, -3614, 8289]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -9, -31, 15, 43, -13, -20, 6, 3], ![3, 16, -22, -102, 14, 144, 4, -73, -2, 15], ![15, 78, -119, -487, 123, 659, -51, -296, 17, 43], ![43, 230, -309, -1452, 158, 1972, 100, -911, -38, 146], ![146, 773, -1084, -4835, 738, 6436, 74, -2820, -35, 400], ![400, 2146, -2827, -13484, 1165, 17938, 1236, -7926, -420, 1165], ![1165, 6225, -8339, -38942, 3991, 51260, 2793, -22064, -936, 3075], ![3075, 16540, -21450, -103664, 7183, 136216, 11285, -58707, -3614, 8289], ![8289, 44520, -58061, -278409, 20671, 363610, 28459, -154495, -8973, 21253]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-43, -15, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-43, -15, -3, -1], [-146, -43, -15, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-43, -15, -3, -1], [-146, -43, -15, -3, -1], [-400, -146, -43, -15, -3, -1]], ![[], [], [], [-1], [-3, -1], [-15, -3, -1], [-43, -15, -3, -1], [-146, -43, -15, -3, -1], [-400, -146, -43, -15, -3, -1], [-1165, -400, -146, -43, -15, -3, -1]], ![[], [], [-1], [-3, -1], [-15, -3, -1], [-43, -15, -3, -1], [-146, -43, -15, -3, -1], [-400, -146, -43, -15, -3, -1], [-1165, -400, -146, -43, -15, -3, -1], [-3075, -1165, -400, -146, -43, -15, -3, -1]], ![[], [-1], [-3, -1], [-15, -3, -1], [-43, -15, -3, -1], [-146, -43, -15, -3, -1], [-400, -146, -43, -15, -3, -1], [-1165, -400, -146, -43, -15, -3, -1], [-3075, -1165, -400, -146, -43, -15, -3, -1], [-8289, -3075, -1165, -400, -146, -43, -15, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -9, -31, 15, 43, -13, -20, 6, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -9, -31, 15, 43, -13, -20, 6, 3], [3, 16, -22, -102, 14, 144, 4, -73, -2, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -9, -31, 15, 43, -13, -20, 6, 3], [3, 16, -22, -102, 14, 144, 4, -73, -2, 15], [15, 78, -119, -487, 123, 659, -51, -296, 17, 43]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -9, -31, 15, 43, -13, -20, 6, 3], [3, 16, -22, -102, 14, 144, 4, -73, -2, 15], [15, 78, -119, -487, 123, 659, -51, -296, 17, 43], [43, 230, -309, -1452, 158, 1972, 100, -911, -38, 146]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -9, -31, 15, 43, -13, -20, 6, 3], [3, 16, -22, -102, 14, 144, 4, -73, -2, 15], [15, 78, -119, -487, 123, 659, -51, -296, 17, 43], [43, 230, -309, -1452, 158, 1972, 100, -911, -38, 146], [146, 773, -1084, -4835, 738, 6436, 74, -2820, -35, 400]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -9, -31, 15, 43, -13, -20, 6, 3], [3, 16, -22, -102, 14, 144, 4, -73, -2, 15], [15, 78, -119, -487, 123, 659, -51, -296, 17, 43], [43, 230, -309, -1452, 158, 1972, 100, -911, -38, 146], [146, 773, -1084, -4835, 738, 6436, 74, -2820, -35, 400], [400, 2146, -2827, -13484, 1165, 17938, 1236, -7926, -420, 1165]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -9, -31, 15, 43, -13, -20, 6, 3], [3, 16, -22, -102, 14, 144, 4, -73, -2, 15], [15, 78, -119, -487, 123, 659, -51, -296, 17, 43], [43, 230, -309, -1452, 158, 1972, 100, -911, -38, 146], [146, 773, -1084, -4835, 738, 6436, 74, -2820, -35, 400], [400, 2146, -2827, -13484, 1165, 17938, 1236, -7926, -420, 1165], [1165, 6225, -8339, -38942, 3991, 51260, 2793, -22064, -936, 3075]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -9, -31, 15, 43, -13, -20, 6, 3], [3, 16, -22, -102, 14, 144, 4, -73, -2, 15], [15, 78, -119, -487, 123, 659, -51, -296, 17, 43], [43, 230, -309, -1452, 158, 1972, 100, -911, -38, 146], [146, 773, -1084, -4835, 738, 6436, 74, -2820, -35, 400], [400, 2146, -2827, -13484, 1165, 17938, 1236, -7926, -420, 1165], [1165, 6225, -8339, -38942, 3991, 51260, 2793, -22064, -936, 3075], [3075, 16540, -21450, -103664, 7183, 136216, 11285, -58707, -3614, 8289]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -9, -31, 15, 43, -13, -20, 6, 3], [3, 16, -22, -102, 14, 144, 4, -73, -2, 15], [15, 78, -119, -487, 123, 659, -51, -296, 17, 43], [43, 230, -309, -1452, 158, 1972, 100, -911, -38, 146], [146, 773, -1084, -4835, 738, 6436, 74, -2820, -35, 400], [400, 2146, -2827, -13484, 1165, 17938, 1236, -7926, -420, 1165], [1165, 6225, -8339, -38942, 3991, 51260, 2793, -22064, -936, 3075], [3075, 16540, -21450, -103664, 7183, 136216, 11285, -58707, -3614, 8289], [8289, 44520, -58061, -278409, 20671, 363610, 28459, -154495, -8973, 21253]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp810250681 : Fact (Nat.Prime 810250681) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 2]
  b' := [3, 3, 4, 2]
  k := [1]
  f := [1, 1, -1, -3, 4, 11, 1, -2, 3, 1]
  g := [2, 0, 1, 4, 1, 1]
  h := [2, 0, 1, 4, 1, 1]
  a := [1, 4, 3, 2, 3]
  b := [0, 0, 2, 1, 2, 1, 2, 2, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD810250681 : CertificateDedekindCriterionLists l 810250681 where
  n := 2
  a' := [744552599, 190951765, 675994398, 656951888, 366339542, 101364996, 564478904, 194163736]
  b' := [563196587, 306077020, 658033437, 586745667, 333305195, 236998022, 502652933, 472532924, 68454105]
  k := [264445605, 39191612, 789774808, 279728677, 630235095, 508899468, 513165031, 185994847, 1]
  f := [674692961, 270358216, 139088693, 209727113, 623968396, 92936769, 166540021, 547267273, 82323540, 1]
  g := [762172115, 305412246, 157122616, 236919853, 704870718, 104986738, 188133221, 618224702, 92997422, 1]
  h := [717253256, 1]
  a := [594866007, 98558265, 465393723, 635125203, 507651022, 362075082, 247186779, 225750764, 688641283]
  b := [751264058, 19044865, 322341698, 141172142, 563635449, 726971577, 642748455, 498137949, 121609398]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 810250681]
  exp := ![1, 1]
  pdgood := [5, 810250681]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp810250681.out
  a := [2185274545, -31493925920, -10344305340, 104963100382, -9597880572, -79301048390, 19533935232, 16661000820, -5569603400]
  b := [-1247305590, -376789485, 12939955049, 754541622, -21926310278, 2509671734, 11382099446, -2573053782, -1833188184, 556960340]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 810250681 T_ofList CD810250681

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

end VoightMaximalOrderD10R138

namespace VoightMaximalOrderD10R139

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2535939715625, [-1, -17, 34, 40, -63, -32, 41, 10, -11, -1, 1], 1⟩
local notation "l" => [-1, -17, 34, 40, -63, -32, 41, 10, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 17, -34, -40, 63, 32, -41, -10, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 17, -34, -40, 63, 32, -41, -10, 11, 1], ![1, 18, -17, -74, 23, 95, -9, -51, 1, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 17, -34, -40, 63, 32, -41, -10, 11, 1], ![1, 18, -17, -74, 23, 95, -9, -51, 1, 12], ![12, 205, -390, -497, 682, 407, -397, -129, 81, 13]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 17, -34, -40, 63, 32, -41, -10, 11, 1], ![1, 18, -17, -74, 23, 95, -9, -51, 1, 12], ![12, 205, -390, -497, 682, 407, -397, -129, 81, 13], ![13, 233, -237, -910, 322, 1098, -126, -527, 14, 94]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 17, -34, -40, 63, 32, -41, -10, 11, 1], ![1, 18, -17, -74, 23, 95, -9, -51, 1, 12], ![12, 205, -390, -497, 682, 407, -397, -129, 81, 13], ![13, 233, -237, -910, 322, 1098, -126, -527, 14, 94], ![94, 1611, -2963, -3997, 5012, 3330, -2756, -1066, 507, 108]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 17, -34, -40, 63, 32, -41, -10, 11, 1], ![1, 18, -17, -74, 23, 95, -9, -51, 1, 12], ![12, 205, -390, -497, 682, 407, -397, -129, 81, 13], ![13, 233, -237, -910, 322, 1098, -126, -527, 14, 94], ![94, 1611, -2963, -3997, 5012, 3330, -2756, -1066, 507, 108], ![108, 1930, -2061, -7283, 2807, 8468, -1098, -3836, 122, 615]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 17, -34, -40, 63, 32, -41, -10, 11, 1], ![1, 18, -17, -74, 23, 95, -9, -51, 1, 12], ![12, 205, -390, -497, 682, 407, -397, -129, 81, 13], ![13, 233, -237, -910, 322, 1098, -126, -527, 14, 94], ![94, 1611, -2963, -3997, 5012, 3330, -2756, -1066, 507, 108], ![108, 1930, -2061, -7283, 2807, 8468, -1098, -3836, 122, 615], ![615, 10563, -18980, -26661, 31462, 22487, -16747, -7248, 2929, 737]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 17, -34, -40, 63, 32, -41, -10, 11, 1], ![1, 18, -17, -74, 23, 95, -9, -51, 1, 12], ![12, 205, -390, -497, 682, 407, -397, -129, 81, 13], ![13, 233, -237, -910, 322, 1098, -126, -527, 14, 94], ![94, 1611, -2963, -3997, 5012, 3330, -2756, -1066, 507, 108], ![108, 1930, -2061, -7283, 2807, 8468, -1098, -3836, 122, 615], ![615, 10563, -18980, -26661, 31462, 22487, -16747, -7248, 2929, 737], ![737, 13144, -14495, -48460, 19770, 55046, -7730, -24117, 859, 3666]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 17, -34, -40, 63, 32, -41, -10, 11, 1], ![1, 18, -17, -74, 23, 95, -9, -51, 1, 12], ![12, 205, -390, -497, 682, 407, -397, -129, 81, 13], ![13, 233, -237, -910, 322, 1098, -126, -527, 14, 94], ![94, 1611, -2963, -3997, 5012, 3330, -2756, -1066, 507, 108], ![108, 1930, -2061, -7283, 2807, 8468, -1098, -3836, 122, 615], ![615, 10563, -18980, -26661, 31462, 22487, -16747, -7248, 2929, 737], ![737, 13144, -14495, -48460, 19770, 55046, -7730, -24117, 859, 3666], ![3666, 63059, -111500, -161135, 182498, 137082, -95260, -44390, 16209, 4525]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-13, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-13, -12, -1, -1], [-94, -13, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-13, -12, -1, -1], [-94, -13, -12, -1, -1], [-108, -94, -13, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-13, -12, -1, -1], [-94, -13, -12, -1, -1], [-108, -94, -13, -12, -1, -1], [-615, -108, -94, -13, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-13, -12, -1, -1], [-94, -13, -12, -1, -1], [-108, -94, -13, -12, -1, -1], [-615, -108, -94, -13, -12, -1, -1], [-737, -615, -108, -94, -13, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-13, -12, -1, -1], [-94, -13, -12, -1, -1], [-108, -94, -13, -12, -1, -1], [-615, -108, -94, -13, -12, -1, -1], [-737, -615, -108, -94, -13, -12, -1, -1], [-3666, -737, -615, -108, -94, -13, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 17, -34, -40, 63, 32, -41, -10, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 17, -34, -40, 63, 32, -41, -10, 11, 1], [1, 18, -17, -74, 23, 95, -9, -51, 1, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 17, -34, -40, 63, 32, -41, -10, 11, 1], [1, 18, -17, -74, 23, 95, -9, -51, 1, 12], [12, 205, -390, -497, 682, 407, -397, -129, 81, 13]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 17, -34, -40, 63, 32, -41, -10, 11, 1], [1, 18, -17, -74, 23, 95, -9, -51, 1, 12], [12, 205, -390, -497, 682, 407, -397, -129, 81, 13], [13, 233, -237, -910, 322, 1098, -126, -527, 14, 94]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 17, -34, -40, 63, 32, -41, -10, 11, 1], [1, 18, -17, -74, 23, 95, -9, -51, 1, 12], [12, 205, -390, -497, 682, 407, -397, -129, 81, 13], [13, 233, -237, -910, 322, 1098, -126, -527, 14, 94], [94, 1611, -2963, -3997, 5012, 3330, -2756, -1066, 507, 108]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 17, -34, -40, 63, 32, -41, -10, 11, 1], [1, 18, -17, -74, 23, 95, -9, -51, 1, 12], [12, 205, -390, -497, 682, 407, -397, -129, 81, 13], [13, 233, -237, -910, 322, 1098, -126, -527, 14, 94], [94, 1611, -2963, -3997, 5012, 3330, -2756, -1066, 507, 108], [108, 1930, -2061, -7283, 2807, 8468, -1098, -3836, 122, 615]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 17, -34, -40, 63, 32, -41, -10, 11, 1], [1, 18, -17, -74, 23, 95, -9, -51, 1, 12], [12, 205, -390, -497, 682, 407, -397, -129, 81, 13], [13, 233, -237, -910, 322, 1098, -126, -527, 14, 94], [94, 1611, -2963, -3997, 5012, 3330, -2756, -1066, 507, 108], [108, 1930, -2061, -7283, 2807, 8468, -1098, -3836, 122, 615], [615, 10563, -18980, -26661, 31462, 22487, -16747, -7248, 2929, 737]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 17, -34, -40, 63, 32, -41, -10, 11, 1], [1, 18, -17, -74, 23, 95, -9, -51, 1, 12], [12, 205, -390, -497, 682, 407, -397, -129, 81, 13], [13, 233, -237, -910, 322, 1098, -126, -527, 14, 94], [94, 1611, -2963, -3997, 5012, 3330, -2756, -1066, 507, 108], [108, 1930, -2061, -7283, 2807, 8468, -1098, -3836, 122, 615], [615, 10563, -18980, -26661, 31462, 22487, -16747, -7248, 2929, 737], [737, 13144, -14495, -48460, 19770, 55046, -7730, -24117, 859, 3666]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 17, -34, -40, 63, 32, -41, -10, 11, 1], [1, 18, -17, -74, 23, 95, -9, -51, 1, 12], [12, 205, -390, -497, 682, 407, -397, -129, 81, 13], [13, 233, -237, -910, 322, 1098, -126, -527, 14, 94], [94, 1611, -2963, -3997, 5012, 3330, -2756, -1066, 507, 108], [108, 1930, -2061, -7283, 2807, 8468, -1098, -3836, 122, 615], [615, 10563, -18980, -26661, 31462, 22487, -16747, -7248, 2929, 737], [737, 13144, -14495, -48460, 19770, 55046, -7730, -24117, 859, 3666], [3666, 63059, -111500, -161135, 182498, 137082, -95260, -44390, 16209, 4525]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp811500709 : Fact (Nat.Prime 811500709) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 1, 4]
  b' := [4, 1, 0, 2, 2]
  k := [1]
  f := [2, 7, -5, -8, 15, 10, -7, -2, 3, 1]
  g := [3, 3, 0, 0, 2, 1]
  h := [3, 3, 0, 0, 2, 1]
  a := [4, 1, 2, 2, 1]
  b := [1, 4, 4, 4, 1, 4, 0, 2, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD811500709 : CertificateDedekindCriterionLists l 811500709 where
  n := 2
  a' := [786040704, 416758899, 793609115, 465849670, 369601252, 199950986, 140825928, 364771282]
  b' := [749708020, 460786893, 50575601, 810156032, 24586118, 687810072, 467897183, 273448749, 49636603]
  k := [592836547, 582527894, 642814614, 663269398, 261646550, 637219197, 306084776, 422283442, 1]
  f := [155047298, 158330404, 164095182, 80510363, 144199627, 46480899, 134374423, 104893850, 147938902, 1]
  g := [646533457, 660223714, 684262326, 335721057, 601299631, 193821216, 560329404, 437398032, 616892075, 1]
  h := [194608633, 1]
  a := [661141096, 742360270, 294889837, 745085265, 206299165, 173216765, 32150380, 715944223, 704627478]
  b := [764668147, 544384622, 532135936, 759847076, 135038590, 460950061, 518393515, 342909276, 106873231]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 811500709]
  exp := ![1, 1]
  pdgood := [5, 811500709]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp811500709.out
  a := [-156419044388, 525987045582, 1417019200463, -1459684825530, -2345968462127, 869489459478, 1165850463613, -123295699774, -156924995240]
  b := [8962443579, 161328404258, -213601280325, -495697537713, 282635875439, 463938704781, -102599299088, -153753827269, 10760320025, 15692499524]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 811500709 T_ofList CD811500709

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

end VoightMaximalOrderD10R139

namespace VoightMaximalOrderD10R140

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2542111578125, [1, -6, -4, 36, 2, -57, 12, 24, -7, -3, 1], 1⟩
local notation "l" => [1, -6, -4, 36, 2, -57, 12, 24, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 4, -36, -2, 57, -12, -24, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 4, -36, -2, 57, -12, -24, 7, 3], ![-3, 17, 18, -104, -42, 169, 21, -84, -3, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 4, -36, -2, 57, -12, -24, 7, 3], ![-3, 17, 18, -104, -42, 169, 21, -84, -3, 16], ![-16, 93, 81, -558, -136, 870, -23, -363, 28, 45]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 4, -36, -2, 57, -12, -24, 7, 3], ![-3, 17, 18, -104, -42, 169, 21, -84, -3, 16], ![-16, 93, 81, -558, -136, 870, -23, -363, 28, 45], ![-45, 254, 273, -1539, -648, 2429, 330, -1103, -48, 163]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 4, -36, -2, 57, -12, -24, 7, 3], ![-3, 17, 18, -104, -42, 169, 21, -84, -3, 16], ![-16, 93, 81, -558, -136, 870, -23, -363, 28, 45], ![-45, 254, 273, -1539, -648, 2429, 330, -1103, -48, 163], ![-163, 933, 906, -5595, -1865, 8643, 473, -3582, 38, 441]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 4, -36, -2, 57, -12, -24, 7, 3], ![-3, 17, 18, -104, -42, 169, 21, -84, -3, 16], ![-16, 93, 81, -558, -136, 870, -23, -363, 28, 45], ![-45, 254, 273, -1539, -648, 2429, 330, -1103, -48, 163], ![-163, 933, 906, -5595, -1865, 8643, 473, -3582, 38, 441], ![-441, 2483, 2697, -14970, -6477, 23272, 3351, -10111, -495, 1361]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 4, -36, -2, 57, -12, -24, 7, 3], ![-3, 17, 18, -104, -42, 169, 21, -84, -3, 16], ![-16, 93, 81, -558, -136, 870, -23, -363, 28, 45], ![-45, 254, 273, -1539, -648, 2429, 330, -1103, -48, 163], ![-163, 933, 906, -5595, -1865, 8643, 473, -3582, 38, 441], ![-441, 2483, 2697, -14970, -6477, 23272, 3351, -10111, -495, 1361], ![-1361, 7725, 7927, -46299, -17692, 71100, 6940, -29313, -584, 3588]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 4, -36, -2, 57, -12, -24, 7, 3], ![-3, 17, 18, -104, -42, 169, 21, -84, -3, 16], ![-16, 93, 81, -558, -136, 870, -23, -363, 28, 45], ![-45, 254, 273, -1539, -648, 2429, 330, -1103, -48, 163], ![-163, 933, 906, -5595, -1865, 8643, 473, -3582, 38, 441], ![-441, 2483, 2697, -14970, -6477, 23272, 3351, -10111, -495, 1361], ![-1361, 7725, 7927, -46299, -17692, 71100, 6940, -29313, -584, 3588], ![-3588, 20167, 22077, -121241, -53475, 186824, 28044, -79172, -4197, 10180]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 4, -36, -2, 57, -12, -24, 7, 3], ![-3, 17, 18, -104, -42, 169, 21, -84, -3, 16], ![-16, 93, 81, -558, -136, 870, -23, -363, 28, 45], ![-45, 254, 273, -1539, -648, 2429, 330, -1103, -48, 163], ![-163, 933, 906, -5595, -1865, 8643, 473, -3582, 38, 441], ![-441, 2483, 2697, -14970, -6477, 23272, 3351, -10111, -495, 1361], ![-1361, 7725, 7927, -46299, -17692, 71100, 6940, -29313, -584, 3588], ![-3588, 20167, 22077, -121241, -53475, 186824, 28044, -79172, -4197, 10180], ![-10180, 57492, 60887, -344403, -141601, 526785, 64664, -216276, -7912, 26343]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-163, -45, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-163, -45, -16, -3, -1], [-441, -163, -45, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-163, -45, -16, -3, -1], [-441, -163, -45, -16, -3, -1], [-1361, -441, -163, -45, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-163, -45, -16, -3, -1], [-441, -163, -45, -16, -3, -1], [-1361, -441, -163, -45, -16, -3, -1], [-3588, -1361, -441, -163, -45, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-163, -45, -16, -3, -1], [-441, -163, -45, -16, -3, -1], [-1361, -441, -163, -45, -16, -3, -1], [-3588, -1361, -441, -163, -45, -16, -3, -1], [-10180, -3588, -1361, -441, -163, -45, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 4, -36, -2, 57, -12, -24, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 4, -36, -2, 57, -12, -24, 7, 3], [-3, 17, 18, -104, -42, 169, 21, -84, -3, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 4, -36, -2, 57, -12, -24, 7, 3], [-3, 17, 18, -104, -42, 169, 21, -84, -3, 16], [-16, 93, 81, -558, -136, 870, -23, -363, 28, 45]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 4, -36, -2, 57, -12, -24, 7, 3], [-3, 17, 18, -104, -42, 169, 21, -84, -3, 16], [-16, 93, 81, -558, -136, 870, -23, -363, 28, 45], [-45, 254, 273, -1539, -648, 2429, 330, -1103, -48, 163]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 4, -36, -2, 57, -12, -24, 7, 3], [-3, 17, 18, -104, -42, 169, 21, -84, -3, 16], [-16, 93, 81, -558, -136, 870, -23, -363, 28, 45], [-45, 254, 273, -1539, -648, 2429, 330, -1103, -48, 163], [-163, 933, 906, -5595, -1865, 8643, 473, -3582, 38, 441]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 4, -36, -2, 57, -12, -24, 7, 3], [-3, 17, 18, -104, -42, 169, 21, -84, -3, 16], [-16, 93, 81, -558, -136, 870, -23, -363, 28, 45], [-45, 254, 273, -1539, -648, 2429, 330, -1103, -48, 163], [-163, 933, 906, -5595, -1865, 8643, 473, -3582, 38, 441], [-441, 2483, 2697, -14970, -6477, 23272, 3351, -10111, -495, 1361]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 4, -36, -2, 57, -12, -24, 7, 3], [-3, 17, 18, -104, -42, 169, 21, -84, -3, 16], [-16, 93, 81, -558, -136, 870, -23, -363, 28, 45], [-45, 254, 273, -1539, -648, 2429, 330, -1103, -48, 163], [-163, 933, 906, -5595, -1865, 8643, 473, -3582, 38, 441], [-441, 2483, 2697, -14970, -6477, 23272, 3351, -10111, -495, 1361], [-1361, 7725, 7927, -46299, -17692, 71100, 6940, -29313, -584, 3588]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 4, -36, -2, 57, -12, -24, 7, 3], [-3, 17, 18, -104, -42, 169, 21, -84, -3, 16], [-16, 93, 81, -558, -136, 870, -23, -363, 28, 45], [-45, 254, 273, -1539, -648, 2429, 330, -1103, -48, 163], [-163, 933, 906, -5595, -1865, 8643, 473, -3582, 38, 441], [-441, 2483, 2697, -14970, -6477, 23272, 3351, -10111, -495, 1361], [-1361, 7725, 7927, -46299, -17692, 71100, 6940, -29313, -584, 3588], [-3588, 20167, 22077, -121241, -53475, 186824, 28044, -79172, -4197, 10180]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 4, -36, -2, 57, -12, -24, 7, 3], [-3, 17, 18, -104, -42, 169, 21, -84, -3, 16], [-16, 93, 81, -558, -136, 870, -23, -363, 28, 45], [-45, 254, 273, -1539, -648, 2429, 330, -1103, -48, 163], [-163, 933, 906, -5595, -1865, 8643, 473, -3582, 38, 441], [-441, 2483, 2697, -14970, -6477, 23272, 3351, -10111, -495, 1361], [-1361, 7725, 7927, -46299, -17692, 71100, 6940, -29313, -584, 3588], [-3588, 20167, 22077, -121241, -53475, 186824, 28044, -79172, -4197, 10180], [-10180, 57492, 60887, -344403, -141601, 526785, 64664, -216276, -7912, 26343]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp3320309 : Fact (Nat.Prime 3320309) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 4
  a' := [3, 2]
  b' := [4, 2, 2]
  k := [1, 1, 4, 3, 4, 0, 1]
  f := [1, 2, 2, -3, 3, 15, 2, 0, 5, 2]
  g := [2, 0, 2, 3, 1]
  h := [3, 2, 0, 4, 4, 4, 1]
  a := [0, 1, 1, 1]
  b := [3, 2, 3, 1, 2, 0, 0, 4, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD7 : CertificateDedekindCriterionLists l 7 where
  n := 2
  a' := [2, 4, 4, 3, 3, 0, 2]
  b' := [2, 0, 0, 2, 5, 0, 3, 5]
  k := [2, 5, 6, 6, 6, 0, 1]
  f := [1, 2, 2, -4, 1, 10, 0, -2, 2, 1]
  g := [4, 0, 3, 1, 2, 4, 1, 2, 1]
  h := [2, 2, 1]
  a := [3, 1, 2, 1, 0, 4, 4]
  b := [3, 0, 4, 4, 3, 5, 3, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3320309 : CertificateDedekindCriterionLists l 3320309 where
  n := 2
  a' := [2569837, 3317921, 891991, 1552646, 1037547, 1595626, 1529307, 1576119]
  b' := [1512673, 2269840, 2181729, 2407364, 2740699, 1710796, 1738679, 726283, 2038415]
  k := [1515641, 416076, 2338378, 2886874, 268008, 3136860, 1141982, 1049300, 1]
  f := [840865, 113996, 391389, 573969, 182346, 1000040, 125069, 518507, 747175, 1]
  g := [2458762, 333332, 1144455, 1678334, 533194, 2924203, 365710, 1516159, 2184803, 1]
  h := [1135503, 1]
  a := [1842485, 1449785, 897956, 1339669, 2623094, 1197911, 496538, 3011300, 1888765]
  b := [1821386, 2968298, 3108107, 885417, 3270664, 451595, 1579241, 3019156, 1431544]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 7, 3320309]
  exp := ![1, 1, 1]
  pdgood := [5, 7, 3320309]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp7.out
    exact hp3320309.out
  a := [-118293887, -1226652396, -431223854, 5933377200, -1432907447, -3918449946, 1298794939, 659869572, -244325060]
  b := [-39084117, -34036023, 575511603, 96015622, -1241755992, 250818671, 565718688, -164079245, -73316709, 24432506]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3320309 T_ofList CD3320309

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

end VoightMaximalOrderD10R140

end TraceEuclidean
