import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk174
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

namespace VoightMaximalOrderD10R112

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2171372122873, [1, 11, 32, 3, -69, -23, 46, 10, -12, -1, 1], 1⟩
local notation "l" => [1, 11, 32, 3, -69, -23, 46, 10, -12, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -32, -3, 69, 23, -46, -10, 12, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -32, -3, 69, 23, -46, -10, 12, 1], ![-1, -12, -43, -35, 66, 92, -23, -56, 2, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -32, -3, 69, 23, -46, -10, 12, 1], ![-1, -12, -43, -35, 66, 92, -23, -56, 2, 13], ![-13, -144, -428, -82, 862, 365, -506, -153, 100, 15]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -32, -3, 69, 23, -46, -10, 12, 1], ![-1, -12, -43, -35, 66, 92, -23, -56, 2, 13], ![-13, -144, -428, -82, 862, 365, -506, -153, 100, 15], ![-15, -178, -624, -473, 953, 1207, -325, -656, 27, 115]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -32, -3, 69, 23, -46, -10, 12, 1], ![-1, -12, -43, -35, 66, 92, -23, -56, 2, 13], ![-13, -144, -428, -82, 862, 365, -506, -153, 100, 15], ![-15, -178, -624, -473, 953, 1207, -325, -656, 27, 115], ![-115, -1280, -3858, -969, 7462, 3598, -4083, -1475, 724, 142]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -32, -3, 69, 23, -46, -10, 12, 1], ![-1, -12, -43, -35, 66, 92, -23, -56, 2, 13], ![-13, -144, -428, -82, 862, 365, -506, -153, 100, 15], ![-15, -178, -624, -473, 953, 1207, -325, -656, 27, 115], ![-115, -1280, -3858, -969, 7462, 3598, -4083, -1475, 724, 142], ![-142, -1677, -5824, -4284, 8829, 10728, -2934, -5503, 229, 866]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -32, -3, 69, 23, -46, -10, 12, 1], ![-1, -12, -43, -35, 66, 92, -23, -56, 2, 13], ![-13, -144, -428, -82, 862, 365, -506, -153, 100, 15], ![-15, -178, -624, -473, 953, 1207, -325, -656, 27, 115], ![-115, -1280, -3858, -969, 7462, 3598, -4083, -1475, 724, 142], ![-142, -1677, -5824, -4284, 8829, 10728, -2934, -5503, 229, 866], ![-866, -9668, -29389, -8422, 55470, 28747, -29108, -11594, 4889, 1095]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -32, -3, 69, 23, -46, -10, 12, 1], ![-1, -12, -43, -35, 66, 92, -23, -56, 2, 13], ![-13, -144, -428, -82, 862, 365, -506, -153, 100, 15], ![-15, -178, -624, -473, 953, 1207, -325, -656, 27, 115], ![-115, -1280, -3858, -969, 7462, 3598, -4083, -1475, 724, 142], ![-142, -1677, -5824, -4284, 8829, 10728, -2934, -5503, 229, 866], ![-866, -9668, -29389, -8422, 55470, 28747, -29108, -11594, 4889, 1095], ![-1095, -12911, -44708, -32674, 67133, 80655, -21623, -40058, 1546, 5984]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -32, -3, 69, 23, -46, -10, 12, 1], ![-1, -12, -43, -35, 66, 92, -23, -56, 2, 13], ![-13, -144, -428, -82, 862, 365, -506, -153, 100, 15], ![-15, -178, -624, -473, 953, 1207, -325, -656, 27, 115], ![-115, -1280, -3858, -969, 7462, 3598, -4083, -1475, 724, 142], ![-142, -1677, -5824, -4284, 8829, 10728, -2934, -5503, 229, 866], ![-866, -9668, -29389, -8422, 55470, 28747, -29108, -11594, 4889, 1095], ![-1095, -12911, -44708, -32674, 67133, 80655, -21623, -40058, 1546, 5984], ![-5984, -66919, -204399, -62660, 380222, 204765, -194609, -81463, 31750, 7530]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-13, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-15, -13, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-15, -13, -1, -1], [-115, -15, -13, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-15, -13, -1, -1], [-115, -15, -13, -1, -1], [-142, -115, -15, -13, -1, -1]], ![[], [], [], [-1], [-1, -1], [-13, -1, -1], [-15, -13, -1, -1], [-115, -15, -13, -1, -1], [-142, -115, -15, -13, -1, -1], [-866, -142, -115, -15, -13, -1, -1]], ![[], [], [-1], [-1, -1], [-13, -1, -1], [-15, -13, -1, -1], [-115, -15, -13, -1, -1], [-142, -115, -15, -13, -1, -1], [-866, -142, -115, -15, -13, -1, -1], [-1095, -866, -142, -115, -15, -13, -1, -1]], ![[], [-1], [-1, -1], [-13, -1, -1], [-15, -13, -1, -1], [-115, -15, -13, -1, -1], [-142, -115, -15, -13, -1, -1], [-866, -142, -115, -15, -13, -1, -1], [-1095, -866, -142, -115, -15, -13, -1, -1], [-5984, -1095, -866, -142, -115, -15, -13, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -32, -3, 69, 23, -46, -10, 12, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -32, -3, 69, 23, -46, -10, 12, 1], [-1, -12, -43, -35, 66, 92, -23, -56, 2, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -32, -3, 69, 23, -46, -10, 12, 1], [-1, -12, -43, -35, 66, 92, -23, -56, 2, 13], [-13, -144, -428, -82, 862, 365, -506, -153, 100, 15]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -32, -3, 69, 23, -46, -10, 12, 1], [-1, -12, -43, -35, 66, 92, -23, -56, 2, 13], [-13, -144, -428, -82, 862, 365, -506, -153, 100, 15], [-15, -178, -624, -473, 953, 1207, -325, -656, 27, 115]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -32, -3, 69, 23, -46, -10, 12, 1], [-1, -12, -43, -35, 66, 92, -23, -56, 2, 13], [-13, -144, -428, -82, 862, 365, -506, -153, 100, 15], [-15, -178, -624, -473, 953, 1207, -325, -656, 27, 115], [-115, -1280, -3858, -969, 7462, 3598, -4083, -1475, 724, 142]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -32, -3, 69, 23, -46, -10, 12, 1], [-1, -12, -43, -35, 66, 92, -23, -56, 2, 13], [-13, -144, -428, -82, 862, 365, -506, -153, 100, 15], [-15, -178, -624, -473, 953, 1207, -325, -656, 27, 115], [-115, -1280, -3858, -969, 7462, 3598, -4083, -1475, 724, 142], [-142, -1677, -5824, -4284, 8829, 10728, -2934, -5503, 229, 866]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -32, -3, 69, 23, -46, -10, 12, 1], [-1, -12, -43, -35, 66, 92, -23, -56, 2, 13], [-13, -144, -428, -82, 862, 365, -506, -153, 100, 15], [-15, -178, -624, -473, 953, 1207, -325, -656, 27, 115], [-115, -1280, -3858, -969, 7462, 3598, -4083, -1475, 724, 142], [-142, -1677, -5824, -4284, 8829, 10728, -2934, -5503, 229, 866], [-866, -9668, -29389, -8422, 55470, 28747, -29108, -11594, 4889, 1095]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -32, -3, 69, 23, -46, -10, 12, 1], [-1, -12, -43, -35, 66, 92, -23, -56, 2, 13], [-13, -144, -428, -82, 862, 365, -506, -153, 100, 15], [-15, -178, -624, -473, 953, 1207, -325, -656, 27, 115], [-115, -1280, -3858, -969, 7462, 3598, -4083, -1475, 724, 142], [-142, -1677, -5824, -4284, 8829, 10728, -2934, -5503, 229, 866], [-866, -9668, -29389, -8422, 55470, 28747, -29108, -11594, 4889, 1095], [-1095, -12911, -44708, -32674, 67133, 80655, -21623, -40058, 1546, 5984]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -32, -3, 69, 23, -46, -10, 12, 1], [-1, -12, -43, -35, 66, 92, -23, -56, 2, 13], [-13, -144, -428, -82, 862, 365, -506, -153, 100, 15], [-15, -178, -624, -473, 953, 1207, -325, -656, 27, 115], [-115, -1280, -3858, -969, 7462, 3598, -4083, -1475, 724, 142], [-142, -1677, -5824, -4284, 8829, 10728, -2934, -5503, 229, 866], [-866, -9668, -29389, -8422, 55470, 28747, -29108, -11594, 4889, 1095], [-1095, -12911, -44708, -32674, 67133, 80655, -21623, -40058, 1546, 5984], [-5984, -66919, -204399, -62660, 380222, 204765, -194609, -81463, 31750, 7530]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp73 : Fact (Nat.Prime 73) := fact_iff.2 (by norm_num)
instance hp193 : Fact (Nat.Prime 193) := fact_iff.2 (by norm_num)
instance hp1453 : Fact (Nat.Prime 1453) := fact_iff.2 (by norm_num)

def CD73 : CertificateDedekindCriterionLists l 73 where
  n := 2
  a' := [57, 22, 6, 18, 43, 64, 22]
  b' := [58, 21, 52, 46, 11, 52, 71, 52]
  k := [2, 51, 69, 55, 32, 59, 1]
  f := [32, 24, 54, 57, 33, 53, 84, 65, 19, 1]
  g := [41, 0, 69, 21, 24, 49, 71, 29, 1]
  h := [57, 43, 1]
  a := [67, 47, 62, 25, 31, 33, 10, 4]
  b := [51, 6, 26, 20, 45, 48, 26, 30, 69]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD193 : CertificateDedekindCriterionLists l 193 where
  n := 2
  a' := [115, 146, 170, 27, 104, 104, 159, 18]
  b' := [112, 102, 39, 3, 138, 168, 98, 186, 191]
  k := [101, 76, 62, 176, 136, 152, 147, 98, 1]
  f := [28, 2, 23, 9, 2, 34, 28, 30, 36, 1]
  g := [115, 6, 95, 35, 6, 139, 113, 121, 145, 1]
  h := [47, 1]
  a := [148, 111, 83, 75, 9, 47, 188, 89]
  b := [16, 129, 76, 56, 175, 112, 56, 104]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1453 : CertificateDedekindCriterionLists l 1453 where
  n := 2
  a' := [128, 1232, 1028, 1320, 1339, 1408, 551]
  b' := [221, 278, 1343, 119, 514, 1009, 1376, 476]
  k := [528, 144, 463, 1127, 466, 334, 1]
  f := [72, 373, 729, 687, 677, 624, 207, 347, 344, 1]
  g := [233, 917, 1217, 706, 1309, 388, 184, 893, 1]
  h := [449, 559, 1]
  a := [248, 984, 593, 592, 1429, 379, 1118, 470]
  b := [759, 1020, 375, 946, 1418, 168, 945, 1184, 983]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![73, 193, 1453]
  exp := ![1, 1, 1]
  pdgood := [73, 193, 1453]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp73.out
    exact hp193.out
    exact hp1453.out
  a := [-518141626, 902490746, 5813652041, -4494794066, -12683234570, 2891748594, 6495140104, -410750940, -812735800]
  b := [48964813, 151210828, -843517684, -1876557697, 1153304849, 2501134066, -342836432, -855992734, 32947736, 81273580]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 73 T_ofList CD73
    exact satisfiesDedekindCriterion_of_certificate_lists T l 193 T_ofList CD193
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1453 T_ofList CD1453

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

end VoightMaximalOrderD10R112

namespace VoightMaximalOrderD10R116

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2195004550000, [1, -6, 5, 22, -27, -25, 31, 11, -11, -1, 1], 1⟩
local notation "l" => [1, -6, 5, 22, -27, -25, 31, 11, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -5, -22, 27, 25, -31, -11, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -5, -22, 27, 25, -31, -11, 11, 1], ![-1, 5, 1, -27, 5, 52, -6, -42, 0, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -5, -22, 27, 25, -31, -11, 11, 1], ![-1, 5, 1, -27, 5, 52, -6, -42, 0, 12], ![-12, 71, -55, -263, 297, 305, -320, -138, 90, 12]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -5, -22, 27, 25, -31, -11, 11, 1], ![-1, 5, 1, -27, 5, 52, -6, -42, 0, 12], ![-12, 71, -55, -263, 297, 305, -320, -138, 90, 12], ![-12, 60, 11, -319, 61, 597, -67, -452, -6, 102]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -5, -22, 27, 25, -31, -11, 11, 1], ![-1, 5, 1, -27, 5, 52, -6, -42, 0, 12], ![-12, 71, -55, -263, 297, 305, -320, -138, 90, 12], ![-12, 60, 11, -319, 61, 597, -67, -452, -6, 102], ![-102, 600, -450, -2233, 2435, 2611, -2565, -1189, 670, 96]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -5, -22, 27, 25, -31, -11, 11, 1], ![-1, 5, 1, -27, 5, 52, -6, -42, 0, 12], ![-12, 71, -55, -263, 297, 305, -320, -138, 90, 12], ![-12, 60, 11, -319, 61, 597, -67, -452, -6, 102], ![-102, 600, -450, -2233, 2435, 2611, -2565, -1189, 670, 96], ![-96, 474, 120, -2562, 359, 4835, -365, -3621, -133, 766]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -5, -22, 27, 25, -31, -11, 11, 1], ![-1, 5, 1, -27, 5, 52, -6, -42, 0, 12], ![-12, 71, -55, -263, 297, 305, -320, -138, 90, 12], ![-12, 60, 11, -319, 61, 597, -67, -452, -6, 102], ![-102, 600, -450, -2233, 2435, 2611, -2565, -1189, 670, 96], ![-96, 474, 120, -2562, 359, 4835, -365, -3621, -133, 766], ![-766, 4500, -3356, -16732, 18120, 19509, -18911, -8791, 4805, 633]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -5, -22, 27, 25, -31, -11, 11, 1], ![-1, 5, 1, -27, 5, 52, -6, -42, 0, 12], ![-12, 71, -55, -263, 297, 305, -320, -138, 90, 12], ![-12, 60, 11, -319, 61, 597, -67, -452, -6, 102], ![-102, 600, -450, -2233, 2435, 2611, -2565, -1189, 670, 96], ![-96, 474, 120, -2562, 359, 4835, -365, -3621, -133, 766], ![-766, 4500, -3356, -16732, 18120, 19509, -18911, -8791, 4805, 633], ![-633, 3032, 1335, -17282, 359, 33945, -114, -25874, -1828, 5438]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -5, -22, 27, 25, -31, -11, 11, 1], ![-1, 5, 1, -27, 5, 52, -6, -42, 0, 12], ![-12, 71, -55, -263, 297, 305, -320, -138, 90, 12], ![-12, 60, 11, -319, 61, 597, -67, -452, -6, 102], ![-102, 600, -450, -2233, 2435, 2611, -2565, -1189, 670, 96], ![-96, 474, 120, -2562, 359, 4835, -365, -3621, -133, 766], ![-766, 4500, -3356, -16732, 18120, 19509, -18911, -8791, 4805, 633], ![-633, 3032, 1335, -17282, 359, 33945, -114, -25874, -1828, 5438], ![-5438, 31995, -24158, -118301, 129544, 136309, -134633, -59932, 33944, 3610]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-12, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-12, -12, -1, -1], [-102, -12, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-12, -12, -1, -1], [-102, -12, -12, -1, -1], [-96, -102, -12, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-12, -12, -1, -1], [-102, -12, -12, -1, -1], [-96, -102, -12, -12, -1, -1], [-766, -96, -102, -12, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-12, -12, -1, -1], [-102, -12, -12, -1, -1], [-96, -102, -12, -12, -1, -1], [-766, -96, -102, -12, -12, -1, -1], [-633, -766, -96, -102, -12, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-12, -12, -1, -1], [-102, -12, -12, -1, -1], [-96, -102, -12, -12, -1, -1], [-766, -96, -102, -12, -12, -1, -1], [-633, -766, -96, -102, -12, -12, -1, -1], [-5438, -633, -766, -96, -102, -12, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -5, -22, 27, 25, -31, -11, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -5, -22, 27, 25, -31, -11, 11, 1], [-1, 5, 1, -27, 5, 52, -6, -42, 0, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -5, -22, 27, 25, -31, -11, 11, 1], [-1, 5, 1, -27, 5, 52, -6, -42, 0, 12], [-12, 71, -55, -263, 297, 305, -320, -138, 90, 12]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -5, -22, 27, 25, -31, -11, 11, 1], [-1, 5, 1, -27, 5, 52, -6, -42, 0, 12], [-12, 71, -55, -263, 297, 305, -320, -138, 90, 12], [-12, 60, 11, -319, 61, 597, -67, -452, -6, 102]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -5, -22, 27, 25, -31, -11, 11, 1], [-1, 5, 1, -27, 5, 52, -6, -42, 0, 12], [-12, 71, -55, -263, 297, 305, -320, -138, 90, 12], [-12, 60, 11, -319, 61, 597, -67, -452, -6, 102], [-102, 600, -450, -2233, 2435, 2611, -2565, -1189, 670, 96]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -5, -22, 27, 25, -31, -11, 11, 1], [-1, 5, 1, -27, 5, 52, -6, -42, 0, 12], [-12, 71, -55, -263, 297, 305, -320, -138, 90, 12], [-12, 60, 11, -319, 61, 597, -67, -452, -6, 102], [-102, 600, -450, -2233, 2435, 2611, -2565, -1189, 670, 96], [-96, 474, 120, -2562, 359, 4835, -365, -3621, -133, 766]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -5, -22, 27, 25, -31, -11, 11, 1], [-1, 5, 1, -27, 5, 52, -6, -42, 0, 12], [-12, 71, -55, -263, 297, 305, -320, -138, 90, 12], [-12, 60, 11, -319, 61, 597, -67, -452, -6, 102], [-102, 600, -450, -2233, 2435, 2611, -2565, -1189, 670, 96], [-96, 474, 120, -2562, 359, 4835, -365, -3621, -133, 766], [-766, 4500, -3356, -16732, 18120, 19509, -18911, -8791, 4805, 633]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -5, -22, 27, 25, -31, -11, 11, 1], [-1, 5, 1, -27, 5, 52, -6, -42, 0, 12], [-12, 71, -55, -263, 297, 305, -320, -138, 90, 12], [-12, 60, 11, -319, 61, 597, -67, -452, -6, 102], [-102, 600, -450, -2233, 2435, 2611, -2565, -1189, 670, 96], [-96, 474, 120, -2562, 359, 4835, -365, -3621, -133, 766], [-766, 4500, -3356, -16732, 18120, 19509, -18911, -8791, 4805, 633], [-633, 3032, 1335, -17282, 359, 33945, -114, -25874, -1828, 5438]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -5, -22, 27, 25, -31, -11, 11, 1], [-1, 5, 1, -27, 5, 52, -6, -42, 0, 12], [-12, 71, -55, -263, 297, 305, -320, -138, 90, 12], [-12, 60, 11, -319, 61, 597, -67, -452, -6, 102], [-102, 600, -450, -2233, 2435, 2611, -2565, -1189, 670, 96], [-96, 474, 120, -2562, 359, 4835, -365, -3621, -133, 766], [-766, 4500, -3356, -16732, 18120, 19509, -18911, -8791, 4805, 633], [-633, 3032, 1335, -17282, 359, 33945, -114, -25874, -1828, 5438], [-5438, 31995, -24158, -118301, 129544, 136309, -134633, -59932, 33944, 3610]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp3271 : Fact (Nat.Prime 3271) := fact_iff.2 (by norm_num)
instance hp13421 : Fact (Nat.Prime 13421) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [0, 0, 1]
  b' := [1, 0, 1, 1, 0, 0, 1]
  k := [1, 0, 0, 0, 0, 1, 1]
  f := [0, 4, -1, -10, 14, 13, -15, -5, 6, 1]
  g := [1, 1, 1, 0, 0, 1, 0, 0, 1]
  h := [1, 1, 1]
  a := [0, 1, 0, 1, 1, 1, 1]
  b := [1, 1, 0, 0, 0, 0, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 1, 3]
  b' := [4, 2, 2, 1, 4]
  k := [1]
  f := [0, 2, 1, -2, 8, 7, -3, -1, 3, 1]
  g := [1, 2, 3, 0, 2, 1]
  h := [1, 2, 3, 0, 2, 1]
  a := [2, 2, 4, 4]
  b := [1, 4, 3, 1, 3, 1, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3271 : CertificateDedekindCriterionLists l 3271 where
  n := 2
  a' := [9, 2026, 2015, 2843, 1685, 3211, 2440, 924]
  b' := [1358, 2729, 2887, 682, 1987, 2542, 2551, 179, 2078]
  k := [2154, 1619, 3059, 1141, 254, 487, 386, 2832, 1]
  f := [47, 12, 66, 72, 78, 150, 218, 160, 205, 1]
  g := [702, 176, 985, 1071, 1160, 2235, 3246, 2375, 3051, 1]
  h := [219, 1]
  a := [2452, 1429, 1397, 1279, 555, 2014, 2740, 2551, 1531]
  b := [819, 1889, 2008, 3083, 2198, 2965, 1739, 974, 1740]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD13421 : CertificateDedekindCriterionLists l 13421 where
  n := 2
  a' := [1028, 9269, 9402, 10941, 10997, 9725, 7304, 588]
  b' := [9184, 5676, 12620, 12219, 5205, 8513, 2015, 3423, 8882]
  k := [974, 6327, 13146, 4723, 5377, 4993, 1873, 10475, 1]
  f := [7066, 6109, 6543, 5473, 6510, 5837, 3031, 7495, 3194, 1]
  g := [11589, 10018, 10730, 8975, 10676, 9572, 4970, 12292, 5237, 1]
  h := [8183, 1]
  a := [9751, 11389, 1757, 2280, 3874, 5297, 4050, 4095, 8812]
  b := [1090, 8229, 2072, 824, 10614, 6695, 1521, 1260, 4609]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![2, 5, 3271, 13421]
  exp := ![1, 1, 1, 1]
  pdgood := [2, 5, 3271, 13421]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp5.out
    exact hp3271.out
    exact hp13421.out
  a := [-46817714776, -42031539172, 389279746118, 94871706790, -675195607299, -112582083295, 304518874111, 13945325125, -33986888350]
  b := [-7876119281, 26685592779, 25735410419, -101955013483, -29530806244, 112996395813, 18717005816, -38095431592, -1734401396, 3398688835]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3271 T_ofList CD3271
    exact satisfiesDedekindCriterion_of_certificate_lists T l 13421 T_ofList CD13421

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

end VoightMaximalOrderD10R116

namespace VoightMaximalOrderD10R117

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2195670595544, [-2, 0, 17, -2, -39, 3, 32, -1, -10, 0, 1], 1⟩
local notation "l" => [-2, 0, 17, -2, -39, 3, 32, -1, -10, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 0, -17, 2, 39, -3, -32, 1, 10, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 0, -17, 2, 39, -3, -32, 1, 10, 0], ![0, 2, 0, -17, 2, 39, -3, -32, 1, 10]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 0, -17, 2, 39, -3, -32, 1, 10, 0], ![0, 2, 0, -17, 2, 39, -3, -32, 1, 10], ![20, 0, -168, 20, 373, -28, -281, 7, 68, 1]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 0, -17, 2, 39, -3, -32, 1, 10, 0], ![0, 2, 0, -17, 2, 39, -3, -32, 1, 10], ![20, 0, -168, 20, 373, -28, -281, 7, 68, 1], ![2, 20, -17, -166, 59, 370, -60, -280, 17, 68]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 0, -17, 2, 39, -3, -32, 1, 10, 0], ![0, 2, 0, -17, 2, 39, -3, -32, 1, 10], ![20, 0, -168, 20, 373, -28, -281, 7, 68, 1], ![2, 20, -17, -166, 59, 370, -60, -280, 17, 68], ![136, 2, -1136, 119, 2486, -145, -1806, 8, 400, 17]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 0, -17, 2, 39, -3, -32, 1, 10, 0], ![0, 2, 0, -17, 2, 39, -3, -32, 1, 10], ![20, 0, -168, 20, 373, -28, -281, 7, 68, 1], ![2, 20, -17, -166, 59, 370, -60, -280, 17, 68], ![136, 2, -1136, 119, 2486, -145, -1806, 8, 400, 17], ![34, 136, -287, -1102, 782, 2435, -689, -1789, 178, 400]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 0, -17, 2, 39, -3, -32, 1, 10, 0], ![0, 2, 0, -17, 2, 39, -3, -32, 1, 10], ![20, 0, -168, 20, 373, -28, -281, 7, 68, 1], ![2, 20, -17, -166, 59, 370, -60, -280, 17, 68], ![136, 2, -1136, 119, 2486, -145, -1806, 8, 400, 17], ![34, 136, -287, -1102, 782, 2435, -689, -1789, 178, 400], ![800, 34, -6664, 513, 14498, -418, -10365, -289, 2211, 178]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 0, -17, 2, 39, -3, -32, 1, 10, 0], ![0, 2, 0, -17, 2, 39, -3, -32, 1, 10], ![20, 0, -168, 20, 373, -28, -281, 7, 68, 1], ![2, 20, -17, -166, 59, 370, -60, -280, 17, 68], ![136, 2, -1136, 119, 2486, -145, -1806, 8, 400, 17], ![34, 136, -287, -1102, 782, 2435, -689, -1789, 178, 400], ![800, 34, -6664, 513, 14498, -418, -10365, -289, 2211, 178], ![356, 800, -2992, -6308, 7455, 13964, -6114, -10187, 1491, 2211]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![2, 0, -17, 2, 39, -3, -32, 1, 10, 0], ![0, 2, 0, -17, 2, 39, -3, -32, 1, 10], ![20, 0, -168, 20, 373, -28, -281, 7, 68, 1], ![2, 20, -17, -166, 59, 370, -60, -280, 17, 68], ![136, 2, -1136, 119, 2486, -145, -1806, 8, 400, 17], ![34, 136, -287, -1102, 782, 2435, -689, -1789, 178, 400], ![800, 34, -6664, 513, 14498, -418, -10365, -289, 2211, 178], ![356, 800, -2992, -6308, 7455, 13964, -6114, -10187, 1491, 2211], ![4422, 356, -36787, 1430, 79921, 822, -56788, -3903, 11923, 1491]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-10, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-68, -1, -10, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-68, -1, -10, 0, -1], [-17, -68, -1, -10, 0, -1]], ![[], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-68, -1, -10, 0, -1], [-17, -68, -1, -10, 0, -1], [-400, -17, -68, -1, -10, 0, -1]], ![[], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-68, -1, -10, 0, -1], [-17, -68, -1, -10, 0, -1], [-400, -17, -68, -1, -10, 0, -1], [-178, -400, -17, -68, -1, -10, 0, -1]], ![[], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-68, -1, -10, 0, -1], [-17, -68, -1, -10, 0, -1], [-400, -17, -68, -1, -10, 0, -1], [-178, -400, -17, -68, -1, -10, 0, -1], [-2211, -178, -400, -17, -68, -1, -10, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 0, -17, 2, 39, -3, -32, 1, 10, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 0, -17, 2, 39, -3, -32, 1, 10, 0], [0, 2, 0, -17, 2, 39, -3, -32, 1, 10]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 0, -17, 2, 39, -3, -32, 1, 10, 0], [0, 2, 0, -17, 2, 39, -3, -32, 1, 10], [20, 0, -168, 20, 373, -28, -281, 7, 68, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 0, -17, 2, 39, -3, -32, 1, 10, 0], [0, 2, 0, -17, 2, 39, -3, -32, 1, 10], [20, 0, -168, 20, 373, -28, -281, 7, 68, 1], [2, 20, -17, -166, 59, 370, -60, -280, 17, 68]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 0, -17, 2, 39, -3, -32, 1, 10, 0], [0, 2, 0, -17, 2, 39, -3, -32, 1, 10], [20, 0, -168, 20, 373, -28, -281, 7, 68, 1], [2, 20, -17, -166, 59, 370, -60, -280, 17, 68], [136, 2, -1136, 119, 2486, -145, -1806, 8, 400, 17]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 0, -17, 2, 39, -3, -32, 1, 10, 0], [0, 2, 0, -17, 2, 39, -3, -32, 1, 10], [20, 0, -168, 20, 373, -28, -281, 7, 68, 1], [2, 20, -17, -166, 59, 370, -60, -280, 17, 68], [136, 2, -1136, 119, 2486, -145, -1806, 8, 400, 17], [34, 136, -287, -1102, 782, 2435, -689, -1789, 178, 400]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 0, -17, 2, 39, -3, -32, 1, 10, 0], [0, 2, 0, -17, 2, 39, -3, -32, 1, 10], [20, 0, -168, 20, 373, -28, -281, 7, 68, 1], [2, 20, -17, -166, 59, 370, -60, -280, 17, 68], [136, 2, -1136, 119, 2486, -145, -1806, 8, 400, 17], [34, 136, -287, -1102, 782, 2435, -689, -1789, 178, 400], [800, 34, -6664, 513, 14498, -418, -10365, -289, 2211, 178]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 0, -17, 2, 39, -3, -32, 1, 10, 0], [0, 2, 0, -17, 2, 39, -3, -32, 1, 10], [20, 0, -168, 20, 373, -28, -281, 7, 68, 1], [2, 20, -17, -166, 59, 370, -60, -280, 17, 68], [136, 2, -1136, 119, 2486, -145, -1806, 8, 400, 17], [34, 136, -287, -1102, 782, 2435, -689, -1789, 178, 400], [800, 34, -6664, 513, 14498, -418, -10365, -289, 2211, 178], [356, 800, -2992, -6308, 7455, 13964, -6114, -10187, 1491, 2211]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [2, 0, -17, 2, 39, -3, -32, 1, 10, 0], [0, 2, 0, -17, 2, 39, -3, -32, 1, 10], [20, 0, -168, 20, 373, -28, -281, 7, 68, 1], [2, 20, -17, -166, 59, 370, -60, -280, 17, 68], [136, 2, -1136, 119, 2486, -145, -1806, 8, 400, 17], [34, 136, -287, -1102, 782, 2435, -689, -1789, 178, 400], [800, 34, -6664, 513, 14498, -418, -10365, -289, 2211, 178], [356, 800, -2992, -6308, 7455, 13964, -6114, -10187, 1491, 2211], [4422, 356, -36787, 1430, 79921, 822, -56788, -3903, 11923, 1491]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp103 : Fact (Nat.Prime 103) := fact_iff.2 (by norm_num)
instance hp2664648781 : Fact (Nat.Prime 2664648781) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [0, 0, 1, 0, 0, 0, 1]
  b' := [1, 0, 1, 1, 1, 0, 0, 1]
  k := [1, 0, 1, 1, 0, 1, 0, 0, 1]
  f := [1, 0, -8, 1, 20, -1, -16, 1, 5]
  g := [0, 1, 0, 1, 1, 0, 1, 0, 0, 1]
  h := [0, 1]
  a := [1, 0, 0, 1, 1, 0, 1]
  b := [0, 0, 0, 1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD103 : CertificateDedekindCriterionLists l 103 where
  n := 2
  a' := [52, 100, 13, 87, 58, 2, 7, 36]
  b' := [59, 100, 0, 63, 31, 90, 1, 28, 99]
  k := [43, 11, 54, 43, 2, 94, 21, 25, 1]
  f := [11, 23, 22, 32, 8, 24, 34, 27, 25, 1]
  g := [29, 60, 57, 83, 18, 63, 89, 69, 64, 1]
  h := [39, 1]
  a := [66, 46, 70, 52, 54, 65, 16, 4, 82]
  b := [78, 21, 24, 96, 87, 45, 71, 1, 21]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2664648781 : CertificateDedekindCriterionLists l 2664648781 where
  n := 2
  a' := [1562017982, 437008962, 1919254042, 121765161, 373072807, 1241067308, 700405894, 2419677080]
  b' := [2061313582, 506351829, 1974917260, 932320807, 1464590174, 2305331521, 2341552386, 6887060, 1211507425]
  k := [258690174, 684098847, 141734895, 2402078924, 232453431, 798289926, 1998399016, 1936696319, 1]
  f := [247611665, 328640590, 32436182, 77417337, 50284708, 133256928, 2863983, 212315480, 314259099, 1]
  g := [1812750573, 2405958607, 237463392, 566767813, 368131416, 975566205, 20967050, 1554349259, 2300672550, 1]
  h := [363976231, 1]
  a := [2304900477, 1560871639, 115715693, 2284862979, 2084934205, 1132840296, 2024164474, 1323564688, 123243568]
  b := [1801757811, 1130999502, 134376982, 843974195, 1155058517, 134831626, 2554430323, 2352210924, 2541405213]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 103, 2664648781]
  exp := ![2, 1, 1]
  pdgood := [2, 103, 2664648781]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp103.out
    exact hp2664648781.out
  a := [-548917648886, 8022904581404, 25606115963436, -15322190235021, -44995024677364, 7090781680843, 21533927280380, -596124717720, -2870196168690]
  b := [471935563612, 1863983686459, -2450757164984, -7695827095099, 2745488149613, 7869941408300, -914408996689, -2727431961776, 59612471772, 287019616869]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 103 T_ofList CD103
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2664648781 T_ofList CD2664648781

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

end VoightMaximalOrderD10R117

namespace VoightMaximalOrderD10R118

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2197821606893, [-1, -2, 10, 21, -18, -37, 18, 21, -10, -2, 1], 1⟩
local notation "l" => [-1, -2, 10, 21, -18, -37, 18, 21, -10, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -21, 18, 37, -18, -21, 10, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -21, 18, 37, -18, -21, 10, 2], ![2, 5, -18, -52, 15, 92, 1, -60, -1, 14]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -21, 18, 37, -18, -21, 10, 2], ![2, 5, -18, -52, 15, 92, 1, -60, -1, 14], ![14, 30, -135, -312, 200, 533, -160, -293, 80, 27]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -21, 18, 37, -18, -21, 10, 2], ![2, 5, -18, -52, 15, 92, 1, -60, -1, 14], ![14, 30, -135, -312, 200, 533, -160, -293, 80, 27], ![27, 68, -240, -702, 174, 1199, 47, -727, -23, 134]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -21, 18, 37, -18, -21, 10, 2], ![2, 5, -18, -52, 15, 92, 1, -60, -1, 14], ![14, 30, -135, -312, 200, 533, -160, -293, 80, 27], ![27, 68, -240, -702, 174, 1199, 47, -727, -23, 134], ![134, 295, -1272, -3054, 1710, 5132, -1213, -2767, 613, 245]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -21, 18, 37, -18, -21, 10, 2], ![2, 5, -18, -52, 15, 92, 1, -60, -1, 14], ![14, 30, -135, -312, 200, 533, -160, -293, 80, 27], ![27, 68, -240, -702, 174, 1199, 47, -727, -23, 134], ![134, 295, -1272, -3054, 1710, 5132, -1213, -2767, 613, 245], ![245, 624, -2155, -6417, 1356, 10775, 722, -6358, -317, 1103]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -21, 18, 37, -18, -21, 10, 2], ![2, 5, -18, -52, 15, 92, 1, -60, -1, 14], ![14, 30, -135, -312, 200, 533, -160, -293, 80, 27], ![27, 68, -240, -702, 174, 1199, 47, -727, -23, 134], ![134, 295, -1272, -3054, 1710, 5132, -1213, -2767, 613, 245], ![245, 624, -2155, -6417, 1356, 10775, 722, -6358, -317, 1103], ![1103, 2451, -10406, -25318, 13437, 42167, -9079, -22441, 4672, 1889]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -21, 18, 37, -18, -21, 10, 2], ![2, 5, -18, -52, 15, 92, 1, -60, -1, 14], ![14, 30, -135, -312, 200, 533, -160, -293, 80, 27], ![27, 68, -240, -702, 174, 1199, 47, -727, -23, 134], ![134, 295, -1272, -3054, 1710, 5132, -1213, -2767, 613, 245], ![245, 624, -2155, -6417, 1356, 10775, 722, -6358, -317, 1103], ![1103, 2451, -10406, -25318, 13437, 42167, -9079, -22441, 4672, 1889], ![1889, 4881, -16439, -50075, 8684, 83330, 8165, -48748, -3551, 8450]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -21, 18, 37, -18, -21, 10, 2], ![2, 5, -18, -52, 15, 92, 1, -60, -1, 14], ![14, 30, -135, -312, 200, 533, -160, -293, 80, 27], ![27, 68, -240, -702, 174, 1199, 47, -727, -23, 134], ![134, 295, -1272, -3054, 1710, 5132, -1213, -2767, 613, 245], ![245, 624, -2155, -6417, 1356, 10775, 722, -6358, -317, 1103], ![1103, 2451, -10406, -25318, 13437, 42167, -9079, -22441, 4672, 1889], ![1889, 4881, -16439, -50075, 8684, 83330, 8165, -48748, -3551, 8450], ![8450, 18789, -79619, -193889, 102025, 321334, -68770, -169285, 35752, 13349]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-27, -14, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-27, -14, -2, -1], [-134, -27, -14, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-27, -14, -2, -1], [-134, -27, -14, -2, -1], [-245, -134, -27, -14, -2, -1]], ![[], [], [], [-1], [-2, -1], [-14, -2, -1], [-27, -14, -2, -1], [-134, -27, -14, -2, -1], [-245, -134, -27, -14, -2, -1], [-1103, -245, -134, -27, -14, -2, -1]], ![[], [], [-1], [-2, -1], [-14, -2, -1], [-27, -14, -2, -1], [-134, -27, -14, -2, -1], [-245, -134, -27, -14, -2, -1], [-1103, -245, -134, -27, -14, -2, -1], [-1889, -1103, -245, -134, -27, -14, -2, -1]], ![[], [-1], [-2, -1], [-14, -2, -1], [-27, -14, -2, -1], [-134, -27, -14, -2, -1], [-245, -134, -27, -14, -2, -1], [-1103, -245, -134, -27, -14, -2, -1], [-1889, -1103, -245, -134, -27, -14, -2, -1], [-8450, -1889, -1103, -245, -134, -27, -14, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -21, 18, 37, -18, -21, 10, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -21, 18, 37, -18, -21, 10, 2], [2, 5, -18, -52, 15, 92, 1, -60, -1, 14]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -21, 18, 37, -18, -21, 10, 2], [2, 5, -18, -52, 15, 92, 1, -60, -1, 14], [14, 30, -135, -312, 200, 533, -160, -293, 80, 27]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -21, 18, 37, -18, -21, 10, 2], [2, 5, -18, -52, 15, 92, 1, -60, -1, 14], [14, 30, -135, -312, 200, 533, -160, -293, 80, 27], [27, 68, -240, -702, 174, 1199, 47, -727, -23, 134]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -21, 18, 37, -18, -21, 10, 2], [2, 5, -18, -52, 15, 92, 1, -60, -1, 14], [14, 30, -135, -312, 200, 533, -160, -293, 80, 27], [27, 68, -240, -702, 174, 1199, 47, -727, -23, 134], [134, 295, -1272, -3054, 1710, 5132, -1213, -2767, 613, 245]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -21, 18, 37, -18, -21, 10, 2], [2, 5, -18, -52, 15, 92, 1, -60, -1, 14], [14, 30, -135, -312, 200, 533, -160, -293, 80, 27], [27, 68, -240, -702, 174, 1199, 47, -727, -23, 134], [134, 295, -1272, -3054, 1710, 5132, -1213, -2767, 613, 245], [245, 624, -2155, -6417, 1356, 10775, 722, -6358, -317, 1103]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -21, 18, 37, -18, -21, 10, 2], [2, 5, -18, -52, 15, 92, 1, -60, -1, 14], [14, 30, -135, -312, 200, 533, -160, -293, 80, 27], [27, 68, -240, -702, 174, 1199, 47, -727, -23, 134], [134, 295, -1272, -3054, 1710, 5132, -1213, -2767, 613, 245], [245, 624, -2155, -6417, 1356, 10775, 722, -6358, -317, 1103], [1103, 2451, -10406, -25318, 13437, 42167, -9079, -22441, 4672, 1889]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -21, 18, 37, -18, -21, 10, 2], [2, 5, -18, -52, 15, 92, 1, -60, -1, 14], [14, 30, -135, -312, 200, 533, -160, -293, 80, 27], [27, 68, -240, -702, 174, 1199, 47, -727, -23, 134], [134, 295, -1272, -3054, 1710, 5132, -1213, -2767, 613, 245], [245, 624, -2155, -6417, 1356, 10775, 722, -6358, -317, 1103], [1103, 2451, -10406, -25318, 13437, 42167, -9079, -22441, 4672, 1889], [1889, 4881, -16439, -50075, 8684, 83330, 8165, -48748, -3551, 8450]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -21, 18, 37, -18, -21, 10, 2], [2, 5, -18, -52, 15, 92, 1, -60, -1, 14], [14, 30, -135, -312, 200, 533, -160, -293, 80, 27], [27, 68, -240, -702, 174, 1199, 47, -727, -23, 134], [134, 295, -1272, -3054, 1710, 5132, -1213, -2767, 613, 245], [245, 624, -2155, -6417, 1356, 10775, 722, -6358, -317, 1103], [1103, 2451, -10406, -25318, 13437, 42167, -9079, -22441, 4672, 1889], [1889, 4881, -16439, -50075, 8684, 83330, 8165, -48748, -3551, 8450], [8450, 18789, -79619, -193889, 102025, 321334, -68770, -169285, 35752, 13349]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp10253 : Fact (Nat.Prime 10253) := fact_iff.2 (by norm_num)

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 5
  a' := [2]
  b' := [9, 10]
  k := [1]
  f := [1, 6, 5, 1, 6, 14, 6, 5, 4, 1]
  g := [10, 4, 1]
  h := [1, 6, 4, 1, 4, 10, 4, 5, 1]
  a := [5, 8]
  b := [4, 10, 7, 6, 3, 4, 7, 6, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD10253 : CertificateDedekindCriterionLists l 10253 where
  n := 2
  a' := [9518, 8368, 3612, 7096, 8830, 6110, 8593, 3105]
  b' := [4712, 1871, 1203, 3132, 6856, 6642, 9786, 933, 9908]
  k := [1, 2474, 4931, 1068, 10024, 9185, 4931, 7779, 1]
  f := [149, 298, 833, 283, 616, 285, 406, 297, 1087, 1]
  g := [1236, 2471, 6908, 2342, 5108, 2360, 3366, 2461, 9015, 1]
  h := [1236, 1]
  a := [2369, 9729, 1852, 8153, 6144, 9899, 1060, 1994, 4105]
  b := [7877, 6150, 9237, 3624, 4077, 6176, 3589, 9677, 6148]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![11, 10253]
  exp := ![1, 1]
  pdgood := [11, 10253]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp11.out
    exact hp10253.out
  a := [3271879, -41215608, -15087925, 151923884, -15303786, -144575950, 55313296, 18404040, -8063200]
  b := [-1692331, 412615, 15936689, 690851, -31321720, 4469720, 20271671, -7066164, -2001668, 806320]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 10253 T_ofList CD10253

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

end VoightMaximalOrderD10R118

end TraceEuclidean
