import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk187
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

namespace VoightMaximalOrderD10R247

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3598895940625, [-1, -3, 7, 17, -20, -27, 22, 14, -9, -2, 1], 1⟩
local notation "l" => [-1, -3, 7, 17, -20, -27, 22, 14, -9, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -7, -17, 20, 27, -22, -14, 9, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -7, -17, 20, 27, -22, -14, 9, 2], ![2, 7, -11, -41, 23, 74, -17, -50, 4, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -7, -17, 20, 27, -22, -14, 9, 2], ![2, 7, -11, -41, 23, 74, -17, -50, 4, 13], ![13, 41, -84, -232, 219, 374, -212, -199, 67, 30]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -7, -17, 20, 27, -22, -14, 9, 2], ![2, 7, -11, -41, 23, 74, -17, -50, 4, 13], ![13, 41, -84, -232, 219, 374, -212, -199, 67, 30], ![30, 103, -169, -594, 368, 1029, -286, -632, 71, 127]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -7, -17, 20, 27, -22, -14, 9, 2], ![2, 7, -11, -41, 23, 74, -17, -50, 4, 13], ![13, 41, -84, -232, 219, 374, -212, -199, 67, 30], ![30, 103, -169, -594, 368, 1029, -286, -632, 71, 127], ![127, 411, -786, -2328, 1946, 3797, -1765, -2064, 511, 325]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -7, -17, 20, 27, -22, -14, 9, 2], ![2, 7, -11, -41, 23, 74, -17, -50, 4, 13], ![13, 41, -84, -232, 219, 374, -212, -199, 67, 30], ![30, 103, -169, -594, 368, 1029, -286, -632, 71, 127], ![127, 411, -786, -2328, 1946, 3797, -1765, -2064, 511, 325], ![325, 1102, -1864, -6311, 4172, 10721, -3353, -6315, 861, 1161]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -7, -17, 20, 27, -22, -14, 9, 2], ![2, 7, -11, -41, 23, 74, -17, -50, 4, 13], ![13, 41, -84, -232, 219, 374, -212, -199, 67, 30], ![30, 103, -169, -594, 368, 1029, -286, -632, 71, 127], ![127, 411, -786, -2328, 1946, 3797, -1765, -2064, 511, 325], ![325, 1102, -1864, -6311, 4172, 10721, -3353, -6315, 861, 1161], ![1161, 3808, -7025, -21601, 16909, 35519, -14821, -19607, 4134, 3183]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -7, -17, 20, 27, -22, -14, 9, 2], ![2, 7, -11, -41, 23, 74, -17, -50, 4, 13], ![13, 41, -84, -232, 219, 374, -212, -199, 67, 30], ![30, 103, -169, -594, 368, 1029, -286, -632, 71, 127], ![127, 411, -786, -2328, 1946, 3797, -1765, -2064, 511, 325], ![325, 1102, -1864, -6311, 4172, 10721, -3353, -6315, 861, 1161], ![1161, 3808, -7025, -21601, 16909, 35519, -14821, -19607, 4134, 3183], ![3183, 10710, -18473, -61136, 42059, 102850, -34507, -59383, 9040, 10500]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -7, -17, 20, 27, -22, -14, 9, 2], ![2, 7, -11, -41, 23, 74, -17, -50, 4, 13], ![13, 41, -84, -232, 219, 374, -212, -199, 67, 30], ![30, 103, -169, -594, 368, 1029, -286, -632, 71, 127], ![127, 411, -786, -2328, 1946, 3797, -1765, -2064, 511, 325], ![325, 1102, -1864, -6311, 4172, 10721, -3353, -6315, 861, 1161], ![1161, 3808, -7025, -21601, 16909, 35519, -14821, -19607, 4134, 3183], ![3183, 10710, -18473, -61136, 42059, 102850, -34507, -59383, 9040, 10500], ![10500, 34683, -62790, -196973, 148864, 325559, -128150, -181507, 35117, 30040]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-127, -30, -13, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-127, -30, -13, -2, -1], [-325, -127, -30, -13, -2, -1]], ![[], [], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-127, -30, -13, -2, -1], [-325, -127, -30, -13, -2, -1], [-1161, -325, -127, -30, -13, -2, -1]], ![[], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-127, -30, -13, -2, -1], [-325, -127, -30, -13, -2, -1], [-1161, -325, -127, -30, -13, -2, -1], [-3183, -1161, -325, -127, -30, -13, -2, -1]], ![[], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-127, -30, -13, -2, -1], [-325, -127, -30, -13, -2, -1], [-1161, -325, -127, -30, -13, -2, -1], [-3183, -1161, -325, -127, -30, -13, -2, -1], [-10500, -3183, -1161, -325, -127, -30, -13, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -7, -17, 20, 27, -22, -14, 9, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -7, -17, 20, 27, -22, -14, 9, 2], [2, 7, -11, -41, 23, 74, -17, -50, 4, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -7, -17, 20, 27, -22, -14, 9, 2], [2, 7, -11, -41, 23, 74, -17, -50, 4, 13], [13, 41, -84, -232, 219, 374, -212, -199, 67, 30]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -7, -17, 20, 27, -22, -14, 9, 2], [2, 7, -11, -41, 23, 74, -17, -50, 4, 13], [13, 41, -84, -232, 219, 374, -212, -199, 67, 30], [30, 103, -169, -594, 368, 1029, -286, -632, 71, 127]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -7, -17, 20, 27, -22, -14, 9, 2], [2, 7, -11, -41, 23, 74, -17, -50, 4, 13], [13, 41, -84, -232, 219, 374, -212, -199, 67, 30], [30, 103, -169, -594, 368, 1029, -286, -632, 71, 127], [127, 411, -786, -2328, 1946, 3797, -1765, -2064, 511, 325]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -7, -17, 20, 27, -22, -14, 9, 2], [2, 7, -11, -41, 23, 74, -17, -50, 4, 13], [13, 41, -84, -232, 219, 374, -212, -199, 67, 30], [30, 103, -169, -594, 368, 1029, -286, -632, 71, 127], [127, 411, -786, -2328, 1946, 3797, -1765, -2064, 511, 325], [325, 1102, -1864, -6311, 4172, 10721, -3353, -6315, 861, 1161]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -7, -17, 20, 27, -22, -14, 9, 2], [2, 7, -11, -41, 23, 74, -17, -50, 4, 13], [13, 41, -84, -232, 219, 374, -212, -199, 67, 30], [30, 103, -169, -594, 368, 1029, -286, -632, 71, 127], [127, 411, -786, -2328, 1946, 3797, -1765, -2064, 511, 325], [325, 1102, -1864, -6311, 4172, 10721, -3353, -6315, 861, 1161], [1161, 3808, -7025, -21601, 16909, 35519, -14821, -19607, 4134, 3183]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -7, -17, 20, 27, -22, -14, 9, 2], [2, 7, -11, -41, 23, 74, -17, -50, 4, 13], [13, 41, -84, -232, 219, 374, -212, -199, 67, 30], [30, 103, -169, -594, 368, 1029, -286, -632, 71, 127], [127, 411, -786, -2328, 1946, 3797, -1765, -2064, 511, 325], [325, 1102, -1864, -6311, 4172, 10721, -3353, -6315, 861, 1161], [1161, 3808, -7025, -21601, 16909, 35519, -14821, -19607, 4134, 3183], [3183, 10710, -18473, -61136, 42059, 102850, -34507, -59383, 9040, 10500]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -7, -17, 20, 27, -22, -14, 9, 2], [2, 7, -11, -41, 23, 74, -17, -50, 4, 13], [13, 41, -84, -232, 219, 374, -212, -199, 67, 30], [30, 103, -169, -594, 368, 1029, -286, -632, 71, 127], [127, 411, -786, -2328, 1946, 3797, -1765, -2064, 511, 325], [325, 1102, -1864, -6311, 4172, 10721, -3353, -6315, 861, 1161], [1161, 3808, -7025, -21601, 16909, 35519, -14821, -19607, 4134, 3183], [3183, 10710, -18473, -61136, 42059, 102850, -34507, -59383, 9040, 10500], [10500, 34683, -62790, -196973, 148864, 325559, -128150, -181507, 35117, 30040]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1151646701 : Fact (Nat.Prime 1151646701) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 0, 2]
  b' := [4, 1, 1, 2, 3]
  k := [1]
  f := [1, 3, 2, -1, 8, 11, 0, -2, 5, 2]
  g := [2, 3, 2, 0, 4, 1]
  h := [2, 3, 2, 0, 4, 1]
  a := [4, 4, 2, 3, 2]
  b := [1, 3, 1, 4, 2, 1, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1151646701 : CertificateDedekindCriterionLists l 1151646701 where
  n := 2
  a' := [201169680, 988764144, 40655494, 487587430, 834151289, 962766331, 964697131, 107207041]
  b' := [856825097, 1096643000, 781610266, 743453706, 32673324, 675060587, 22260113, 71101818, 1011774063]
  k := [511328305, 949174005, 1120260198, 552920048, 145581703, 153552776, 273205738, 663566326, 1]
  f := [460710231, 198249761, 810322449, 94619629, 811626545, 629590339, 687570034, 180654568, 236198234, 1]
  g := [647150890, 278477664, 1138244516, 132910390, 1140076355, 884373561, 965816535, 253762031, 331783162, 1]
  h := [819863537, 1]
  a := [830176088, 1014227976, 427873028, 533875766, 1088632319, 619637814, 405659744, 233262891, 963712937]
  b := [181483363, 674136130, 342163468, 265310394, 631503547, 1023583722, 291211107, 767206935, 187933764]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 1151646701]
  exp := ![1, 1]
  pdgood := [5, 1151646701]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1151646701.out
  a := [-113375032441, 197915475108, 3207558156683, 1648821985510, -5576305086134, -2017211871556, 2845209794154, 466281120746, -367351127720]
  b := [35872266312, 214807116861, 80618469624, -866474483871, -443872057443, 933826463764, 317904897913, -354543200588, -53975134629, 36735112772]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1151646701 T_ofList CD1151646701

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

end VoightMaximalOrderD10R247

namespace VoightMaximalOrderD10R250

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3621268234432, [1, -7, -3, 37, -9, -44, 18, 17, -8, -2, 1], 1⟩
local notation "l" => [1, -7, -3, 37, -9, -44, 18, 17, -8, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 3, -37, 9, 44, -18, -17, 8, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 3, -37, 9, 44, -18, -17, 8, 2], ![-2, 13, 13, -71, -19, 97, 8, -52, -1, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 3, -37, 9, 44, -18, -17, 8, 2], ![-2, 13, 13, -71, -19, 97, 8, -52, -1, 12], ![-12, 82, 49, -431, 37, 509, -119, -196, 44, 23]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 3, -37, 9, 44, -18, -17, 8, 2], ![-2, 13, 13, -71, -19, 97, 8, -52, -1, 12], ![-12, 82, 49, -431, 37, 509, -119, -196, 44, 23], ![-23, 149, 151, -802, -224, 1049, 95, -510, -12, 90]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 3, -37, 9, 44, -18, -17, 8, 2], ![-2, 13, 13, -71, -19, 97, 8, -52, -1, 12], ![-12, 82, 49, -431, 37, 509, -119, -196, 44, 23], ![-23, 149, 151, -802, -224, 1049, 95, -510, -12, 90], ![-90, 607, 419, -3179, 8, 3736, -571, -1435, 210, 168]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 3, -37, 9, 44, -18, -17, 8, 2], ![-2, 13, 13, -71, -19, 97, 8, -52, -1, 12], ![-12, 82, 49, -431, 37, 509, -119, -196, 44, 23], ![-23, 149, 151, -802, -224, 1049, 95, -510, -12, 90], ![-90, 607, 419, -3179, 8, 3736, -571, -1435, 210, 168], ![-168, 1086, 1111, -5797, -1667, 7400, 712, -3427, -91, 546]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 3, -37, 9, 44, -18, -17, 8, 2], ![-2, 13, 13, -71, -19, 97, 8, -52, -1, 12], ![-12, 82, 49, -431, 37, 509, -119, -196, 44, 23], ![-23, 149, 151, -802, -224, 1049, 95, -510, -12, 90], ![-90, 607, 419, -3179, 8, 3736, -571, -1435, 210, 168], ![-168, 1086, 1111, -5797, -1667, 7400, 712, -3427, -91, 546], ![-546, 3654, 2724, -19091, -883, 22357, -2428, -8570, 941, 1001]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 3, -37, 9, 44, -18, -17, 8, 2], ![-2, 13, 13, -71, -19, 97, 8, -52, -1, 12], ![-12, 82, 49, -431, 37, 509, -119, -196, 44, 23], ![-23, 149, 151, -802, -224, 1049, 95, -510, -12, 90], ![-90, 607, 419, -3179, 8, 3736, -571, -1435, 210, 168], ![-168, 1086, 1111, -5797, -1667, 7400, 712, -3427, -91, 546], ![-546, 3654, 2724, -19091, -883, 22357, -2428, -8570, 941, 1001], ![-1001, 6461, 6657, -34313, -10082, 43161, 4339, -19445, -562, 2943]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 3, -37, 9, 44, -18, -17, 8, 2], ![-2, 13, 13, -71, -19, 97, 8, -52, -1, 12], ![-12, 82, 49, -431, 37, 509, -119, -196, 44, 23], ![-23, 149, 151, -802, -224, 1049, 95, -510, -12, 90], ![-90, 607, 419, -3179, 8, 3736, -571, -1435, 210, 168], ![-168, 1086, 1111, -5797, -1667, 7400, 712, -3427, -91, 546], ![-546, 3654, 2724, -19091, -883, 22357, -2428, -8570, 941, 1001], ![-1001, 6461, 6657, -34313, -10082, 43161, 4339, -19445, -562, 2943], ![-2943, 19600, 15290, -102234, -7826, 119410, -9813, -45692, 4099, 5324]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-12, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-12, -2, -1], [-23, -12, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-12, -2, -1], [-23, -12, -2, -1], [-90, -23, -12, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-12, -2, -1], [-23, -12, -2, -1], [-90, -23, -12, -2, -1], [-168, -90, -23, -12, -2, -1]], ![[], [], [], [-1], [-2, -1], [-12, -2, -1], [-23, -12, -2, -1], [-90, -23, -12, -2, -1], [-168, -90, -23, -12, -2, -1], [-546, -168, -90, -23, -12, -2, -1]], ![[], [], [-1], [-2, -1], [-12, -2, -1], [-23, -12, -2, -1], [-90, -23, -12, -2, -1], [-168, -90, -23, -12, -2, -1], [-546, -168, -90, -23, -12, -2, -1], [-1001, -546, -168, -90, -23, -12, -2, -1]], ![[], [-1], [-2, -1], [-12, -2, -1], [-23, -12, -2, -1], [-90, -23, -12, -2, -1], [-168, -90, -23, -12, -2, -1], [-546, -168, -90, -23, -12, -2, -1], [-1001, -546, -168, -90, -23, -12, -2, -1], [-2943, -1001, -546, -168, -90, -23, -12, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 3, -37, 9, 44, -18, -17, 8, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 3, -37, 9, 44, -18, -17, 8, 2], [-2, 13, 13, -71, -19, 97, 8, -52, -1, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 3, -37, 9, 44, -18, -17, 8, 2], [-2, 13, 13, -71, -19, 97, 8, -52, -1, 12], [-12, 82, 49, -431, 37, 509, -119, -196, 44, 23]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 3, -37, 9, 44, -18, -17, 8, 2], [-2, 13, 13, -71, -19, 97, 8, -52, -1, 12], [-12, 82, 49, -431, 37, 509, -119, -196, 44, 23], [-23, 149, 151, -802, -224, 1049, 95, -510, -12, 90]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 3, -37, 9, 44, -18, -17, 8, 2], [-2, 13, 13, -71, -19, 97, 8, -52, -1, 12], [-12, 82, 49, -431, 37, 509, -119, -196, 44, 23], [-23, 149, 151, -802, -224, 1049, 95, -510, -12, 90], [-90, 607, 419, -3179, 8, 3736, -571, -1435, 210, 168]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 3, -37, 9, 44, -18, -17, 8, 2], [-2, 13, 13, -71, -19, 97, 8, -52, -1, 12], [-12, 82, 49, -431, 37, 509, -119, -196, 44, 23], [-23, 149, 151, -802, -224, 1049, 95, -510, -12, 90], [-90, 607, 419, -3179, 8, 3736, -571, -1435, 210, 168], [-168, 1086, 1111, -5797, -1667, 7400, 712, -3427, -91, 546]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 3, -37, 9, 44, -18, -17, 8, 2], [-2, 13, 13, -71, -19, 97, 8, -52, -1, 12], [-12, 82, 49, -431, 37, 509, -119, -196, 44, 23], [-23, 149, 151, -802, -224, 1049, 95, -510, -12, 90], [-90, 607, 419, -3179, 8, 3736, -571, -1435, 210, 168], [-168, 1086, 1111, -5797, -1667, 7400, 712, -3427, -91, 546], [-546, 3654, 2724, -19091, -883, 22357, -2428, -8570, 941, 1001]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 3, -37, 9, 44, -18, -17, 8, 2], [-2, 13, 13, -71, -19, 97, 8, -52, -1, 12], [-12, 82, 49, -431, 37, 509, -119, -196, 44, 23], [-23, 149, 151, -802, -224, 1049, 95, -510, -12, 90], [-90, 607, 419, -3179, 8, 3736, -571, -1435, 210, 168], [-168, 1086, 1111, -5797, -1667, 7400, 712, -3427, -91, 546], [-546, 3654, 2724, -19091, -883, 22357, -2428, -8570, 941, 1001], [-1001, 6461, 6657, -34313, -10082, 43161, 4339, -19445, -562, 2943]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 3, -37, 9, 44, -18, -17, 8, 2], [-2, 13, 13, -71, -19, 97, 8, -52, -1, 12], [-12, 82, 49, -431, 37, 509, -119, -196, 44, 23], [-23, 149, 151, -802, -224, 1049, 95, -510, -12, 90], [-90, 607, 419, -3179, 8, 3736, -571, -1435, 210, 168], [-168, 1086, 1111, -5797, -1667, 7400, 712, -3427, -91, 546], [-546, 3654, 2724, -19091, -883, 22357, -2428, -8570, 941, 1001], [-1001, 6461, 6657, -34313, -10082, 43161, 4339, -19445, -562, 2943], [-2943, 19600, 15290, -102234, -7826, 119410, -9813, -45692, 4099, 5324]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp17 : Fact (Nat.Prime 17) := fact_iff.2 (by norm_num)
instance hp53 : Fact (Nat.Prime 53) := fact_iff.2 (by norm_num)
instance hp191 : Fact (Nat.Prime 191) := fact_iff.2 (by norm_num)
instance hp197 : Fact (Nat.Prime 197) := fact_iff.2 (by norm_num)
instance hp1669 : Fact (Nat.Prime 1669) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 0, 0, 1]
  b' := [1, 1, 0, 0, 0, 1]
  k := [1, 1, 0, 0, 1]
  f := [0, 4, 2, -17, 5, 23, -8, -8, 5, 1]
  g := [1, 0, 1, 1, 0, 1, 0, 1]
  h := [1, 1, 0, 1]
  a := [0, 1, 0, 1, 1]
  b := [1, 0, 1, 1, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD17 : CertificateDedekindCriterionLists l 17 where
  n := 2
  a' := [12, 7, 10, 2, 13, 12, 7, 16]
  b' := [11, 7, 0, 13, 12, 15, 8, 14, 2]
  k := [4, 5, 9, 11, 6, 8, 12, 16, 1]
  f := [7, 6, 5, 4, 5, 4, 0, 1, 4, 1]
  g := [15, 10, 9, 12, 8, 2, 2, 4, 7, 1]
  h := [8, 1]
  a := [9, 1, 11, 8, 3, 11, 5, 6, 15]
  b := [14, 7, 9, 4, 7, 4, 15, 5, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD53 : CertificateDedekindCriterionLists l 53 where
  n := 2
  a' := [29, 25, 32, 38, 26, 29, 26, 35]
  b' := [46, 33, 9, 26, 28, 16, 25, 8, 2]
  k := [40, 51, 31, 45, 51, 46, 12, 47, 1]
  f := [1, 2, 1, 0, 2, 3, 1, 0, 2, 1]
  g := [27, 36, 7, 15, 41, 37, 17, 0, 49, 1]
  h := [2, 1]
  a := [14, 30, 12, 31, 8, 14, 36, 37, 26]
  b := [27, 7, 6, 27, 45, 35, 19, 19, 27]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD191 : CertificateDedekindCriterionLists l 191 where
  n := 2
  a' := [133, 58, 101, 120, 91, 139, 71, 178]
  b' := [131, 85, 0, 21, 145, 83, 135, 172, 150]
  k := [108, 170, 109, 29, 1, 44, 183, 128, 1]
  f := [31, 90, 101, 89, 103, 5, 120, 51, 42, 1]
  g := [47, 136, 152, 134, 155, 6, 182, 76, 63, 1]
  h := [126, 1]
  a := [190, 44, 171, 27, 119, 144, 131, 80, 4]
  b := [21, 95, 80, 142, 163, 77, 177, 4, 187]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD197 : CertificateDedekindCriterionLists l 197 where
  n := 2
  a' := [126, 51, 155, 148, 183, 171, 149, 116]
  b' := [51, 153, 21, 107, 144, 109, 64, 175, 9]
  k := [169, 136, 98, 27, 127, 65, 180, 13, 1]
  f := [6, 62, 88, 89, 74, 62, 44, 84, 49, 1]
  g := [13, 134, 189, 191, 158, 132, 94, 181, 104, 1]
  h := [91, 1]
  a := [190, 90, 191, 187, 102, 147, 93, 72, 138]
  b := [170, 58, 143, 173, 34, 164, 133, 32, 59]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1669 : CertificateDedekindCriterionLists l 1669 where
  n := 2
  a' := [1606, 306, 455, 1106, 1598, 219, 794, 1606]
  b' := [718, 597, 1350, 1240, 208, 310, 476, 641, 7]
  k := [1324, 1604, 1614, 794, 674, 598, 853, 685, 1]
  f := [248, 330, 384, 272, 373, 162, 148, 15, 346, 1]
  g := [843, 1120, 1303, 922, 1266, 548, 502, 50, 1176, 1]
  h := [491, 1]
  a := [960, 1668, 1388, 703, 1336, 1241, 873, 1099, 1057]
  b := [1640, 647, 1579, 329, 552, 534, 1125, 1655, 612]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 6
  p := ![2, 17, 53, 191, 197, 1669]
  exp := ![1, 1, 1, 1, 1, 1]
  pdgood := [2, 17, 53, 191, 197, 1669]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp17.out
    exact hp53.out
    exact hp191.out
    exact hp197.out
    exact hp1669.out
  a := [-282700122631, -926905370243, 3273579437124, 2579762922514, -5911268322965, -1698724635855, 2972962048170, 284113939476, -429549395370]
  b := [-56552107851, 198758305040, 448597656431, -944002822926, -685289020010, 1026815449421, 297560879031, -375805607520, -37002381855, 42954939537]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 17 T_ofList CD17
    exact satisfiesDedekindCriterion_of_certificate_lists T l 53 T_ofList CD53
    exact satisfiesDedekindCriterion_of_certificate_lists T l 191 T_ofList CD191
    exact satisfiesDedekindCriterion_of_certificate_lists T l 197 T_ofList CD197
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1669 T_ofList CD1669

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

end VoightMaximalOrderD10R250

namespace VoightMaximalOrderD10R252

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3665024164864, [-1, 6, 33, 16, -53, -30, 32, 14, -9, -2, 1], 1⟩
local notation "l" => [-1, 6, 33, 16, -53, -30, 32, 14, -9, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, -33, -16, 53, 30, -32, -14, 9, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, -33, -16, 53, 30, -32, -14, 9, 2], ![2, -11, -72, -65, 90, 113, -34, -60, 4, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, -33, -16, 53, 30, -32, -14, 9, 2], ![2, -11, -72, -65, 90, 113, -34, -60, 4, 13], ![13, -76, -440, -280, 624, 480, -303, -216, 57, 30]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, -33, -16, 53, 30, -32, -14, 9, 2], ![2, -11, -72, -65, 90, 113, -34, -60, 4, 13], ![13, -76, -440, -280, 624, 480, -303, -216, 57, 30], ![30, -167, -1066, -920, 1310, 1524, -480, -723, 54, 117]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, -33, -16, 53, 30, -32, -14, 9, 2], ![2, -11, -72, -65, 90, 113, -34, -60, 4, 13], ![13, -76, -440, -280, 624, 480, -303, -216, 57, 30], ![30, -167, -1066, -920, 1310, 1524, -480, -723, 54, 117], ![117, -672, -4028, -2938, 5281, 4820, -2220, -2118, 330, 288]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, -33, -16, 53, 30, -32, -14, 9, 2], ![2, -11, -72, -65, 90, 113, -34, -60, 4, 13], ![13, -76, -440, -280, 624, 480, -303, -216, 57, 30], ![30, -167, -1066, -920, 1310, 1524, -480, -723, 54, 117], ![117, -672, -4028, -2938, 5281, 4820, -2220, -2118, 330, 288], ![288, -1611, -10176, -8636, 12326, 13921, -4396, -6252, 474, 906]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, -33, -16, 53, 30, -32, -14, 9, 2], ![2, -11, -72, -65, 90, 113, -34, -60, 4, 13], ![13, -76, -440, -280, 624, 480, -303, -216, 57, 30], ![30, -167, -1066, -920, 1310, 1524, -480, -723, 54, 117], ![117, -672, -4028, -2938, 5281, 4820, -2220, -2118, 330, 288], ![288, -1611, -10176, -8636, 12326, 13921, -4396, -6252, 474, 906], ![906, -5148, -31509, -24672, 39382, 39506, -15071, -17080, 1902, 2286]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, -33, -16, 53, 30, -32, -14, 9, 2], ![2, -11, -72, -65, 90, 113, -34, -60, 4, 13], ![13, -76, -440, -280, 624, 480, -303, -216, 57, 30], ![30, -167, -1066, -920, 1310, 1524, -480, -723, 54, 117], ![117, -672, -4028, -2938, 5281, 4820, -2220, -2118, 330, 288], ![288, -1611, -10176, -8636, 12326, 13921, -4396, -6252, 474, 906], ![906, -5148, -31509, -24672, 39382, 39506, -15071, -17080, 1902, 2286], ![2286, -12810, -80586, -68085, 96486, 107962, -33646, -47075, 3494, 6474]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, -33, -16, 53, 30, -32, -14, 9, 2], ![2, -11, -72, -65, 90, 113, -34, -60, 4, 13], ![13, -76, -440, -280, 624, 480, -303, -216, 57, 30], ![30, -167, -1066, -920, 1310, 1524, -480, -723, 54, 117], ![117, -672, -4028, -2938, 5281, 4820, -2220, -2118, 330, 288], ![288, -1611, -10176, -8636, 12326, 13921, -4396, -6252, 474, 906], ![906, -5148, -31509, -24672, 39382, 39506, -15071, -17080, 1902, 2286], ![2286, -12810, -80586, -68085, 96486, 107962, -33646, -47075, 3494, 6474], ![6474, -36558, -226452, -184170, 275037, 290706, -99206, -124282, 11191, 16442]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-117, -30, -13, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-117, -30, -13, -2, -1], [-288, -117, -30, -13, -2, -1]], ![[], [], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-117, -30, -13, -2, -1], [-288, -117, -30, -13, -2, -1], [-906, -288, -117, -30, -13, -2, -1]], ![[], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-117, -30, -13, -2, -1], [-288, -117, -30, -13, -2, -1], [-906, -288, -117, -30, -13, -2, -1], [-2286, -906, -288, -117, -30, -13, -2, -1]], ![[], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-117, -30, -13, -2, -1], [-288, -117, -30, -13, -2, -1], [-906, -288, -117, -30, -13, -2, -1], [-2286, -906, -288, -117, -30, -13, -2, -1], [-6474, -2286, -906, -288, -117, -30, -13, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, -33, -16, 53, 30, -32, -14, 9, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, -33, -16, 53, 30, -32, -14, 9, 2], [2, -11, -72, -65, 90, 113, -34, -60, 4, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, -33, -16, 53, 30, -32, -14, 9, 2], [2, -11, -72, -65, 90, 113, -34, -60, 4, 13], [13, -76, -440, -280, 624, 480, -303, -216, 57, 30]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, -33, -16, 53, 30, -32, -14, 9, 2], [2, -11, -72, -65, 90, 113, -34, -60, 4, 13], [13, -76, -440, -280, 624, 480, -303, -216, 57, 30], [30, -167, -1066, -920, 1310, 1524, -480, -723, 54, 117]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, -33, -16, 53, 30, -32, -14, 9, 2], [2, -11, -72, -65, 90, 113, -34, -60, 4, 13], [13, -76, -440, -280, 624, 480, -303, -216, 57, 30], [30, -167, -1066, -920, 1310, 1524, -480, -723, 54, 117], [117, -672, -4028, -2938, 5281, 4820, -2220, -2118, 330, 288]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, -33, -16, 53, 30, -32, -14, 9, 2], [2, -11, -72, -65, 90, 113, -34, -60, 4, 13], [13, -76, -440, -280, 624, 480, -303, -216, 57, 30], [30, -167, -1066, -920, 1310, 1524, -480, -723, 54, 117], [117, -672, -4028, -2938, 5281, 4820, -2220, -2118, 330, 288], [288, -1611, -10176, -8636, 12326, 13921, -4396, -6252, 474, 906]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, -33, -16, 53, 30, -32, -14, 9, 2], [2, -11, -72, -65, 90, 113, -34, -60, 4, 13], [13, -76, -440, -280, 624, 480, -303, -216, 57, 30], [30, -167, -1066, -920, 1310, 1524, -480, -723, 54, 117], [117, -672, -4028, -2938, 5281, 4820, -2220, -2118, 330, 288], [288, -1611, -10176, -8636, 12326, 13921, -4396, -6252, 474, 906], [906, -5148, -31509, -24672, 39382, 39506, -15071, -17080, 1902, 2286]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, -33, -16, 53, 30, -32, -14, 9, 2], [2, -11, -72, -65, 90, 113, -34, -60, 4, 13], [13, -76, -440, -280, 624, 480, -303, -216, 57, 30], [30, -167, -1066, -920, 1310, 1524, -480, -723, 54, 117], [117, -672, -4028, -2938, 5281, 4820, -2220, -2118, 330, 288], [288, -1611, -10176, -8636, 12326, 13921, -4396, -6252, 474, 906], [906, -5148, -31509, -24672, 39382, 39506, -15071, -17080, 1902, 2286], [2286, -12810, -80586, -68085, 96486, 107962, -33646, -47075, 3494, 6474]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, -33, -16, 53, 30, -32, -14, 9, 2], [2, -11, -72, -65, 90, 113, -34, -60, 4, 13], [13, -76, -440, -280, 624, 480, -303, -216, 57, 30], [30, -167, -1066, -920, 1310, 1524, -480, -723, 54, 117], [117, -672, -4028, -2938, 5281, 4820, -2220, -2118, 330, 288], [288, -1611, -10176, -8636, 12326, 13921, -4396, -6252, 474, 906], [906, -5148, -31509, -24672, 39382, 39506, -15071, -17080, 1902, 2286], [2286, -12810, -80586, -68085, 96486, 107962, -33646, -47075, 3494, 6474], [6474, -36558, -226452, -184170, 275037, 290706, -99206, -124282, 11191, 16442]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp123418109 : Fact (Nat.Prime 123418109) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [0, 0, 1]
  b' := [1, 0, 1, 1]
  k := [1]
  f := [1, -2, -15, -7, 28, 17, -14, -6, 5, 2]
  g := [1, 1, 1, 0, 1, 1]
  h := [1, 1, 1, 0, 1, 1]
  a := [0, 1, 1, 1, 1]
  b := [1, 0, 0, 0, 0, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 2
  a' := [19, 9, 27, 7, 14, 27, 4, 3]
  b' := [26, 12, 27, 19, 13, 23, 28, 2, 19]
  k := [4, 23, 2, 8, 24, 28, 7, 15, 1]
  f := [5, 6, 1, 4, 4, 5, 2, 2, 5, 1]
  g := [24, 26, 6, 21, 7, 18, 12, 10, 21, 1]
  h := [6, 1]
  a := [15, 18, 19, 28, 11, 13, 3, 13, 11]
  b := [9, 19, 14, 20, 27, 28, 19, 18, 18]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD123418109 : CertificateDedekindCriterionLists l 123418109 where
  n := 2
  a' := [8982235, 88470610, 112536858, 110387776, 85364797, 32657639, 65963590, 73435802]
  b' := [22769273, 110052871, 64161254, 34918515, 82145978, 36202589, 87861882, 65203449, 87832329]
  k := [1190286, 21204507, 91449905, 63221879, 63179020, 111981386, 72092033, 28438183, 1]
  f := [12399507, 20124873, 39265303, 16651603, 20862830, 19427181, 21412742, 37259150, 29216335, 1]
  g := [32224151, 52301026, 102043657, 43274603, 54218847, 50487846, 55647972, 96830016, 75928145, 1]
  h := [47489962, 1]
  a := [73370300, 33301087, 104760032, 76639472, 37989853, 29203365, 113811547, 28735857, 10985419]
  b := [61613052, 52533208, 45524411, 8939286, 104145418, 63433127, 33432539, 98835570, 112432690]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 29, 123418109]
  exp := ![1, 1, 1]
  pdgood := [2, 29, 123418109]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp29.out
    exact hp123418109.out
  a := [-22812125216, -165627591096, 93327261930, 470891522586, -135838240224, -354706285752, 109871284086, 74618579310, -26530205850]
  b := [-2608979149, 23906297339, 64551385902, -36560810127, -101442181623, 31150986117, 50793060168, -15225281286, -7992462048, 2653020585]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
    exact satisfiesDedekindCriterion_of_certificate_lists T l 123418109 T_ofList CD123418109

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

end VoightMaximalOrderD10R252

namespace VoightMaximalOrderD10R259

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3728399528125, [-1, -5, 7, 26, -12, -37, 12, 19, -6, -3, 1], 1⟩
local notation "l" => [-1, -5, 7, 26, -12, -37, 12, 19, -6, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -7, -26, 12, 37, -12, -19, 6, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -7, -26, 12, 37, -12, -19, 6, 3], ![3, 16, -16, -85, 10, 123, 1, -69, -1, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -7, -26, 12, 37, -12, -19, 6, 3], ![3, 16, -16, -85, 10, 123, 1, -69, -1, 15], ![15, 78, -89, -406, 95, 565, -57, -284, 21, 44]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -7, -26, 12, 37, -12, -19, 6, 3], ![3, 16, -16, -85, 10, 123, 1, -69, -1, 15], ![15, 78, -89, -406, 95, 565, -57, -284, 21, 44], ![44, 235, -230, -1233, 122, 1723, 37, -893, -20, 153]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -7, -26, 12, 37, -12, -19, 6, 3], ![3, 16, -16, -85, 10, 123, 1, -69, -1, 15], ![15, 78, -89, -406, 95, 565, -57, -284, 21, 44], ![44, 235, -230, -1233, 122, 1723, 37, -893, -20, 153], ![153, 809, -836, -4208, 603, 5783, -113, -2870, 25, 439]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -7, -26, 12, 37, -12, -19, 6, 3], ![3, 16, -16, -85, 10, 123, 1, -69, -1, 15], ![15, 78, -89, -406, 95, 565, -57, -284, 21, 44], ![44, 235, -230, -1233, 122, 1723, 37, -893, -20, 153], ![153, 809, -836, -4208, 603, 5783, -113, -2870, 25, 439], ![439, 2348, -2264, -12250, 1060, 16846, 515, -8454, -236, 1342]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -7, -26, 12, 37, -12, -19, 6, 3], ![3, 16, -16, -85, 10, 123, 1, -69, -1, 15], ![15, 78, -89, -406, 95, 565, -57, -284, 21, 44], ![44, 235, -230, -1233, 122, 1723, 37, -893, -20, 153], ![153, 809, -836, -4208, 603, 5783, -113, -2870, 25, 439], ![439, 2348, -2264, -12250, 1060, 16846, 515, -8454, -236, 1342], ![1342, 7149, -7046, -37156, 3854, 50714, 742, -24983, -402, 3790]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -7, -26, 12, 37, -12, -19, 6, 3], ![3, 16, -16, -85, 10, 123, 1, -69, -1, 15], ![15, 78, -89, -406, 95, 565, -57, -284, 21, 44], ![44, 235, -230, -1233, 122, 1723, 37, -893, -20, 153], ![153, 809, -836, -4208, 603, 5783, -113, -2870, 25, 439], ![439, 2348, -2264, -12250, 1060, 16846, 515, -8454, -236, 1342], ![1342, 7149, -7046, -37156, 3854, 50714, 742, -24983, -402, 3790], ![3790, 20292, -19381, -105586, 8324, 144084, 5234, -71268, -2243, 10968]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -7, -26, 12, 37, -12, -19, 6, 3], ![3, 16, -16, -85, 10, 123, 1, -69, -1, 15], ![15, 78, -89, -406, 95, 565, -57, -284, 21, 44], ![44, 235, -230, -1233, 122, 1723, 37, -893, -20, 153], ![153, 809, -836, -4208, 603, 5783, -113, -2870, 25, 439], ![439, 2348, -2264, -12250, 1060, 16846, 515, -8454, -236, 1342], ![1342, 7149, -7046, -37156, 3854, 50714, 742, -24983, -402, 3790], ![3790, 20292, -19381, -105586, 8324, 144084, 5234, -71268, -2243, 10968], ![10968, 58630, -56484, -304549, 26030, 414140, 12468, -203158, -5460, 30661]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1], [-153, -44, -15, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1], [-153, -44, -15, -3, -1], [-439, -153, -44, -15, -3, -1]], ![[], [], [], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1], [-153, -44, -15, -3, -1], [-439, -153, -44, -15, -3, -1], [-1342, -439, -153, -44, -15, -3, -1]], ![[], [], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1], [-153, -44, -15, -3, -1], [-439, -153, -44, -15, -3, -1], [-1342, -439, -153, -44, -15, -3, -1], [-3790, -1342, -439, -153, -44, -15, -3, -1]], ![[], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1], [-153, -44, -15, -3, -1], [-439, -153, -44, -15, -3, -1], [-1342, -439, -153, -44, -15, -3, -1], [-3790, -1342, -439, -153, -44, -15, -3, -1], [-10968, -3790, -1342, -439, -153, -44, -15, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -7, -26, 12, 37, -12, -19, 6, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -7, -26, 12, 37, -12, -19, 6, 3], [3, 16, -16, -85, 10, 123, 1, -69, -1, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -7, -26, 12, 37, -12, -19, 6, 3], [3, 16, -16, -85, 10, 123, 1, -69, -1, 15], [15, 78, -89, -406, 95, 565, -57, -284, 21, 44]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -7, -26, 12, 37, -12, -19, 6, 3], [3, 16, -16, -85, 10, 123, 1, -69, -1, 15], [15, 78, -89, -406, 95, 565, -57, -284, 21, 44], [44, 235, -230, -1233, 122, 1723, 37, -893, -20, 153]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -7, -26, 12, 37, -12, -19, 6, 3], [3, 16, -16, -85, 10, 123, 1, -69, -1, 15], [15, 78, -89, -406, 95, 565, -57, -284, 21, 44], [44, 235, -230, -1233, 122, 1723, 37, -893, -20, 153], [153, 809, -836, -4208, 603, 5783, -113, -2870, 25, 439]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -7, -26, 12, 37, -12, -19, 6, 3], [3, 16, -16, -85, 10, 123, 1, -69, -1, 15], [15, 78, -89, -406, 95, 565, -57, -284, 21, 44], [44, 235, -230, -1233, 122, 1723, 37, -893, -20, 153], [153, 809, -836, -4208, 603, 5783, -113, -2870, 25, 439], [439, 2348, -2264, -12250, 1060, 16846, 515, -8454, -236, 1342]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -7, -26, 12, 37, -12, -19, 6, 3], [3, 16, -16, -85, 10, 123, 1, -69, -1, 15], [15, 78, -89, -406, 95, 565, -57, -284, 21, 44], [44, 235, -230, -1233, 122, 1723, 37, -893, -20, 153], [153, 809, -836, -4208, 603, 5783, -113, -2870, 25, 439], [439, 2348, -2264, -12250, 1060, 16846, 515, -8454, -236, 1342], [1342, 7149, -7046, -37156, 3854, 50714, 742, -24983, -402, 3790]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -7, -26, 12, 37, -12, -19, 6, 3], [3, 16, -16, -85, 10, 123, 1, -69, -1, 15], [15, 78, -89, -406, 95, 565, -57, -284, 21, 44], [44, 235, -230, -1233, 122, 1723, 37, -893, -20, 153], [153, 809, -836, -4208, 603, 5783, -113, -2870, 25, 439], [439, 2348, -2264, -12250, 1060, 16846, 515, -8454, -236, 1342], [1342, 7149, -7046, -37156, 3854, 50714, 742, -24983, -402, 3790], [3790, 20292, -19381, -105586, 8324, 144084, 5234, -71268, -2243, 10968]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -7, -26, 12, 37, -12, -19, 6, 3], [3, 16, -16, -85, 10, 123, 1, -69, -1, 15], [15, 78, -89, -406, 95, 565, -57, -284, 21, 44], [44, 235, -230, -1233, 122, 1723, 37, -893, -20, 153], [153, 809, -836, -4208, 603, 5783, -113, -2870, 25, 439], [439, 2348, -2264, -12250, 1060, 16846, 515, -8454, -236, 1342], [1342, 7149, -7046, -37156, 3854, 50714, 742, -24983, -402, 3790], [3790, 20292, -19381, -105586, 8324, 144084, 5234, -71268, -2243, 10968], [10968, 58630, -56484, -304549, 26030, 414140, 12468, -203158, -5460, 30661]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp149 : Fact (Nat.Prime 149) := fact_iff.2 (by norm_num)
instance hp2269 : Fact (Nat.Prime 2269) := fact_iff.2 (by norm_num)
instance hp3529 : Fact (Nat.Prime 3529) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 1, 1]
  b' := [3, 3, 2, 4, 1]
  k := [1]
  f := [1, 1, 1, -2, 5, 13, 2, -1, 3, 1]
  g := [2, 0, 3, 4, 1, 1]
  h := [2, 0, 3, 4, 1, 1]
  a := [0, 3, 1, 0, 4]
  b := [3, 1, 1, 3, 3, 3, 2, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD149 : CertificateDedekindCriterionLists l 149 where
  n := 2
  a' := [10, 73, 59, 50, 65, 9, 12, 66]
  b' := [104, 57, 33, 42, 68, 1, 114, 84, 92]
  k := [29, 117, 114, 73, 100, 134, 90, 78, 1]
  f := [21, 31, 28, 15, 11, 9, 15, 14, 26, 1]
  g := [92, 133, 119, 63, 46, 37, 65, 60, 112, 1]
  h := [34, 1]
  a := [71, 24, 132, 117, 72, 90, 1, 130, 143]
  b := [0, 37, 128, 22, 111, 92, 6, 99, 6]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2269 : CertificateDedekindCriterionLists l 2269 where
  n := 2
  a' := [288, 821, 864, 55, 2023, 196, 682, 1436]
  b' := [1286, 1263, 1180, 712, 226, 378, 22, 2149, 1101]
  k := [158, 438, 1657, 601, 1744, 242, 1957, 975, 1]
  f := [1689, 1202, 156, 368, 729, 1094, 618, 1312, 382, 1]
  g := [2153, 1531, 198, 469, 929, 1394, 787, 1672, 486, 1]
  h := [1780, 1]
  a := [262, 61, 1226, 1321, 330, 1310, 724, 119, 2264]
  b := [1448, 787, 2021, 22, 656, 1343, 1637, 1630, 5]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3529 : CertificateDedekindCriterionLists l 3529 where
  n := 2
  a' := [3432, 1049, 297, 796, 1703, 3006, 1939, 3384]
  b' := [398, 2335, 2405, 3442, 1592, 2821, 2769, 191, 3153]
  k := [1080, 3447, 1888, 1814, 194, 1374, 2980, 3475, 1]
  f := [1439, 1278, 1109, 1151, 1640, 1761, 1652, 814, 881, 1]
  g := [2837, 2518, 2185, 2268, 3232, 3470, 3255, 1603, 1736, 1]
  h := [1790, 1]
  a := [711, 2126, 1537, 3047, 2310, 408, 1529, 2536, 361]
  b := [3396, 181, 3406, 3146, 180, 978, 3089, 2625, 3168]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 149, 2269, 3529]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 149, 2269, 3529]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp149.out
    exact hp2269.out
    exact hp3529.out
  a := [70562286725, -324679652106, -661652933585, 1742287371974, 307594486057, -1664545527184, 293124048870, 382235936042, -115014268260]
  b := [-15305545194, -48481882847, 181281663240, 123772355733, -381516265190, -23279016865, 238655532223, -40963194726, -41674021652, 11501426826]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 149 T_ofList CD149
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2269 T_ofList CD2269
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3529 T_ofList CD3529

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

end VoightMaximalOrderD10R259

end TraceEuclidean
