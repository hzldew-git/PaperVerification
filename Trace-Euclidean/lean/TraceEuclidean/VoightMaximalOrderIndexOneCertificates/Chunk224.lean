import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk220
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

namespace VoightMaximalOrderD10R623

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6494915440625, [-1, 5, 48, 81, -11, -85, -4, 34, -2, -5, 1], 1⟩
local notation "l" => [-1, 5, 48, 81, -11, -85, -4, 34, -2, -5, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -5, -48, -81, 11, 85, 4, -34, 2, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -5, -48, -81, 11, 85, 4, -34, 2, 5], ![5, -24, -245, -453, -26, 436, 105, -166, -24, 27]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -5, -48, -81, 11, 85, 4, -34, 2, 5], ![5, -24, -245, -453, -26, 436, 105, -166, -24, 27], ![27, -130, -1320, -2432, -156, 2269, 544, -813, -112, 111]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -5, -48, -81, 11, 85, 4, -34, 2, 5], ![5, -24, -245, -453, -26, 436, 105, -166, -24, 27], ![27, -130, -1320, -2432, -156, 2269, 544, -813, -112, 111], ![111, -528, -5458, -10311, -1211, 9279, 2713, -3230, -591, 443]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -5, -48, -81, 11, 85, 4, -34, 2, 5], ![5, -24, -245, -453, -26, 436, 105, -166, -24, 27], ![27, -130, -1320, -2432, -156, 2269, 544, -813, -112, 111], ![111, -528, -5458, -10311, -1211, 9279, 2713, -3230, -591, 443], ![443, -2104, -21792, -41341, -5438, 36444, 11051, -12349, -2344, 1624]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -5, -48, -81, 11, 85, 4, -34, 2, 5], ![5, -24, -245, -453, -26, 436, 105, -166, -24, 27], ![27, -130, -1320, -2432, -156, 2269, 544, -813, -112, 111], ![111, -528, -5458, -10311, -1211, 9279, 2713, -3230, -591, 443], ![443, -2104, -21792, -41341, -5438, 36444, 11051, -12349, -2344, 1624], ![1624, -7677, -80056, -153336, -23477, 132602, 42940, -44165, -9101, 5776]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -5, -48, -81, 11, 85, 4, -34, 2, 5], ![5, -24, -245, -453, -26, 436, 105, -166, -24, 27], ![27, -130, -1320, -2432, -156, 2269, 544, -813, -112, 111], ![111, -528, -5458, -10311, -1211, 9279, 2713, -3230, -591, 443], ![443, -2104, -21792, -41341, -5438, 36444, 11051, -12349, -2344, 1624], ![1624, -7677, -80056, -153336, -23477, 132602, 42940, -44165, -9101, 5776], ![5776, -27256, -284925, -547912, -89800, 467483, 155706, -153444, -32613, 19779]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -5, -48, -81, 11, 85, 4, -34, 2, 5], ![5, -24, -245, -453, -26, 436, 105, -166, -24, 27], ![27, -130, -1320, -2432, -156, 2269, 544, -813, -112, 111], ![111, -528, -5458, -10311, -1211, 9279, 2713, -3230, -591, 443], ![443, -2104, -21792, -41341, -5438, 36444, 11051, -12349, -2344, 1624], ![1624, -7677, -80056, -153336, -23477, 132602, 42940, -44165, -9101, 5776], ![5776, -27256, -284925, -547912, -89800, 467483, 155706, -153444, -32613, 19779], ![19779, -93119, -976648, -1887024, -330343, 1591415, 546599, -516780, -113886, 66282]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -5, -48, -81, 11, 85, 4, -34, 2, 5], ![5, -24, -245, -453, -26, 436, 105, -166, -24, 27], ![27, -130, -1320, -2432, -156, 2269, 544, -813, -112, 111], ![111, -528, -5458, -10311, -1211, 9279, 2713, -3230, -591, 443], ![443, -2104, -21792, -41341, -5438, 36444, 11051, -12349, -2344, 1624], ![1624, -7677, -80056, -153336, -23477, 132602, 42940, -44165, -9101, 5776], ![5776, -27256, -284925, -547912, -89800, 467483, 155706, -153444, -32613, 19779], ![19779, -93119, -976648, -1887024, -330343, 1591415, 546599, -516780, -113886, 66282], ![66282, -311631, -3274655, -6345490, -1157922, 5303627, 1856543, -1706989, -384216, 217524]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-5, -1]], ![[], [], [], [], [], [], [], [-1], [-5, -1], [-27, -5, -1]], ![[], [], [], [], [], [], [-1], [-5, -1], [-27, -5, -1], [-111, -27, -5, -1]], ![[], [], [], [], [], [-1], [-5, -1], [-27, -5, -1], [-111, -27, -5, -1], [-443, -111, -27, -5, -1]], ![[], [], [], [], [-1], [-5, -1], [-27, -5, -1], [-111, -27, -5, -1], [-443, -111, -27, -5, -1], [-1624, -443, -111, -27, -5, -1]], ![[], [], [], [-1], [-5, -1], [-27, -5, -1], [-111, -27, -5, -1], [-443, -111, -27, -5, -1], [-1624, -443, -111, -27, -5, -1], [-5776, -1624, -443, -111, -27, -5, -1]], ![[], [], [-1], [-5, -1], [-27, -5, -1], [-111, -27, -5, -1], [-443, -111, -27, -5, -1], [-1624, -443, -111, -27, -5, -1], [-5776, -1624, -443, -111, -27, -5, -1], [-19779, -5776, -1624, -443, -111, -27, -5, -1]], ![[], [-1], [-5, -1], [-27, -5, -1], [-111, -27, -5, -1], [-443, -111, -27, -5, -1], [-1624, -443, -111, -27, -5, -1], [-5776, -1624, -443, -111, -27, -5, -1], [-19779, -5776, -1624, -443, -111, -27, -5, -1], [-66282, -19779, -5776, -1624, -443, -111, -27, -5, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -5, -48, -81, 11, 85, 4, -34, 2, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -5, -48, -81, 11, 85, 4, -34, 2, 5], [5, -24, -245, -453, -26, 436, 105, -166, -24, 27]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -5, -48, -81, 11, 85, 4, -34, 2, 5], [5, -24, -245, -453, -26, 436, 105, -166, -24, 27], [27, -130, -1320, -2432, -156, 2269, 544, -813, -112, 111]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -5, -48, -81, 11, 85, 4, -34, 2, 5], [5, -24, -245, -453, -26, 436, 105, -166, -24, 27], [27, -130, -1320, -2432, -156, 2269, 544, -813, -112, 111], [111, -528, -5458, -10311, -1211, 9279, 2713, -3230, -591, 443]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -5, -48, -81, 11, 85, 4, -34, 2, 5], [5, -24, -245, -453, -26, 436, 105, -166, -24, 27], [27, -130, -1320, -2432, -156, 2269, 544, -813, -112, 111], [111, -528, -5458, -10311, -1211, 9279, 2713, -3230, -591, 443], [443, -2104, -21792, -41341, -5438, 36444, 11051, -12349, -2344, 1624]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -5, -48, -81, 11, 85, 4, -34, 2, 5], [5, -24, -245, -453, -26, 436, 105, -166, -24, 27], [27, -130, -1320, -2432, -156, 2269, 544, -813, -112, 111], [111, -528, -5458, -10311, -1211, 9279, 2713, -3230, -591, 443], [443, -2104, -21792, -41341, -5438, 36444, 11051, -12349, -2344, 1624], [1624, -7677, -80056, -153336, -23477, 132602, 42940, -44165, -9101, 5776]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -5, -48, -81, 11, 85, 4, -34, 2, 5], [5, -24, -245, -453, -26, 436, 105, -166, -24, 27], [27, -130, -1320, -2432, -156, 2269, 544, -813, -112, 111], [111, -528, -5458, -10311, -1211, 9279, 2713, -3230, -591, 443], [443, -2104, -21792, -41341, -5438, 36444, 11051, -12349, -2344, 1624], [1624, -7677, -80056, -153336, -23477, 132602, 42940, -44165, -9101, 5776], [5776, -27256, -284925, -547912, -89800, 467483, 155706, -153444, -32613, 19779]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -5, -48, -81, 11, 85, 4, -34, 2, 5], [5, -24, -245, -453, -26, 436, 105, -166, -24, 27], [27, -130, -1320, -2432, -156, 2269, 544, -813, -112, 111], [111, -528, -5458, -10311, -1211, 9279, 2713, -3230, -591, 443], [443, -2104, -21792, -41341, -5438, 36444, 11051, -12349, -2344, 1624], [1624, -7677, -80056, -153336, -23477, 132602, 42940, -44165, -9101, 5776], [5776, -27256, -284925, -547912, -89800, 467483, 155706, -153444, -32613, 19779], [19779, -93119, -976648, -1887024, -330343, 1591415, 546599, -516780, -113886, 66282]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -5, -48, -81, 11, 85, 4, -34, 2, 5], [5, -24, -245, -453, -26, 436, 105, -166, -24, 27], [27, -130, -1320, -2432, -156, 2269, 544, -813, -112, 111], [111, -528, -5458, -10311, -1211, 9279, 2713, -3230, -591, 443], [443, -2104, -21792, -41341, -5438, 36444, 11051, -12349, -2344, 1624], [1624, -7677, -80056, -153336, -23477, 132602, 42940, -44165, -9101, 5776], [5776, -27256, -284925, -547912, -89800, 467483, 155706, -153444, -32613, 19779], [19779, -93119, -976648, -1887024, -330343, 1591415, 546599, -516780, -113886, 66282], [66282, -311631, -3274655, -6345490, -1157922, 5303627, 1856543, -1706989, -384216, 217524]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp431 : Fact (Nat.Prime 431) := fact_iff.2 (by norm_num)
instance hp4822211 : Fact (Nat.Prime 4822211) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 1]
  b' := [2, 0, 4, 2, 2]
  k := [1]
  f := [1, -1, -8, -13, 3, 21, 4, -6, 2, 1]
  g := [2, 0, 2, 4, 0, 1]
  h := [2, 0, 2, 4, 0, 1]
  a := [4, 1, 4, 0, 1]
  b := [1, 4, 1, 1, 2, 2, 1, 3, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD431 : CertificateDedekindCriterionLists l 431 where
  n := 2
  a' := [62, 105, 110, 238, 239, 120, 120, 301]
  b' := [231, 74, 174, 147, 287, 35, 210, 338, 206]
  k := [214, 31, 271, 283, 28, 15, 148, 224, 1]
  f := [15, 77, 59, 96, 23, 59, 73, 85, 77, 1]
  g := [64, 328, 249, 408, 94, 250, 309, 360, 325, 1]
  h := [101, 1]
  a := [353, 151, 174, 191, 302, 28, 99, 314, 244]
  b := [254, 245, 131, 406, 68, 227, 187, 289, 187]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD4822211 : CertificateDedekindCriterionLists l 4822211 where
  n := 2
  a' := [2640977, 343530, 2767672, 2286546, 3137769, 3458925, 4648606, 832787]
  b' := [3820179, 2389455, 1976963, 1628457, 2998767, 1251529, 1329089, 1016809, 2050673]
  k := [3613751, 2947498, 2614166, 4576435, 2463492, 3865263, 1767419, 2472246, 1]
  f := [727811, 180339, 394225, 891219, 522113, 643585, 164406, 1012369, 888684, 1]
  g := [2986994, 740123, 1617930, 3657632, 2142790, 2641322, 674733, 4154842, 3647226, 1]
  h := [1174980, 1]
  a := [4290426, 231637, 2860722, 4016378, 1114670, 1591240, 3534684, 1390899, 682842]
  b := [2811330, 2857738, 2486283, 758434, 4634888, 2246819, 1372718, 4529067, 4139369]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 431, 4822211]
  exp := ![1, 1, 1]
  pdgood := [5, 431, 4822211]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp431.out
    exact hp4822211.out
  a := [-117637795920, -1847042747358, -1235562129375, 3713064412686, 1334501072930, -2456775267538, -59395101686, 525377921740, -107307541840]
  b := [-21449186243, 160053622314, 698654065296, 234000743371, -783589200325, -196270471438, 354837766616, 3771907668, -57903169266, 10730754184]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 431 T_ofList CD431
    exact satisfiesDedekindCriterion_of_certificate_lists T l 4822211 T_ofList CD4822211

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

end VoightMaximalOrderD10R623

namespace VoightMaximalOrderD10R636

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6618025278125, [-1, -7, 5, 32, -12, -48, 17, 25, -11, -2, 1], 1⟩
local notation "l" => [-1, -7, 5, 32, -12, -48, 17, 25, -11, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -5, -32, 12, 48, -17, -25, 11, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -5, -32, 12, 48, -17, -25, 11, 2], ![2, 15, -3, -69, -8, 108, 14, -67, -3, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -5, -32, 12, 48, -17, -25, 11, 2], ![2, 15, -3, -69, -8, 108, 14, -67, -3, 15], ![15, 107, -60, -483, 111, 712, -147, -361, 98, 27]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -5, -32, 12, 48, -17, -25, 11, 2], ![2, 15, -3, -69, -8, 108, 14, -67, -3, 15], ![15, 107, -60, -483, 111, 712, -147, -361, 98, 27], ![27, 204, -28, -924, -159, 1407, 253, -822, -64, 152]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -5, -32, 12, 48, -17, -25, 11, 2], ![2, 15, -3, -69, -8, 108, 14, -67, -3, 15], ![15, 107, -60, -483, 111, 712, -147, -361, 98, 27], ![27, 204, -28, -924, -159, 1407, 253, -822, -64, 152], ![152, 1091, -556, -4892, 900, 7137, -1177, -3547, 850, 240]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -5, -32, 12, 48, -17, -25, 11, 2], ![2, 15, -3, -69, -8, 108, 14, -67, -3, 15], ![15, 107, -60, -483, 111, 712, -147, -361, 98, 27], ![27, 204, -28, -924, -159, 1407, 253, -822, -64, 152], ![152, 1091, -556, -4892, 900, 7137, -1177, -3547, 850, 240], ![240, 1832, -109, -8236, -2012, 12420, 3057, -7177, -907, 1330]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -5, -32, 12, 48, -17, -25, 11, 2], ![2, 15, -3, -69, -8, 108, 14, -67, -3, 15], ![15, 107, -60, -483, 111, 712, -147, -361, 98, 27], ![27, 204, -28, -924, -159, 1407, 253, -822, -64, 152], ![152, 1091, -556, -4892, 900, 7137, -1177, -3547, 850, 240], ![240, 1832, -109, -8236, -2012, 12420, 3057, -7177, -907, 1330], ![1330, 9550, -4818, -42669, 7724, 61828, -10190, -30193, 7453, 1753]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -5, -32, 12, 48, -17, -25, 11, 2], ![2, 15, -3, -69, -8, 108, 14, -67, -3, 15], ![15, 107, -60, -483, 111, 712, -147, -361, 98, 27], ![27, 204, -28, -924, -159, 1407, 253, -822, -64, 152], ![152, 1091, -556, -4892, 900, 7137, -1177, -3547, 850, 240], ![240, 1832, -109, -8236, -2012, 12420, 3057, -7177, -907, 1330], ![1330, 9550, -4818, -42669, 7724, 61828, -10190, -30193, 7453, 1753], ![1753, 13601, 785, -60914, -21633, 91868, 32027, -54015, -10910, 10959]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -5, -32, 12, 48, -17, -25, 11, 2], ![2, 15, -3, -69, -8, 108, 14, -67, -3, 15], ![15, 107, -60, -483, 111, 712, -147, -361, 98, 27], ![27, 204, -28, -924, -159, 1407, 253, -822, -64, 152], ![152, 1091, -556, -4892, 900, 7137, -1177, -3547, 850, 240], ![240, 1832, -109, -8236, -2012, 12420, 3057, -7177, -907, 1330], ![1330, 9550, -4818, -42669, 7724, 61828, -10190, -30193, 7453, 1753], ![1753, 13601, 785, -60914, -21633, 91868, 32027, -54015, -10910, 10959], ![10959, 78466, -41194, -349903, 70594, 504399, -94435, -241948, 66534, 11008]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-15, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-15, -2, -1], [-27, -15, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-15, -2, -1], [-27, -15, -2, -1], [-152, -27, -15, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-15, -2, -1], [-27, -15, -2, -1], [-152, -27, -15, -2, -1], [-240, -152, -27, -15, -2, -1]], ![[], [], [], [-1], [-2, -1], [-15, -2, -1], [-27, -15, -2, -1], [-152, -27, -15, -2, -1], [-240, -152, -27, -15, -2, -1], [-1330, -240, -152, -27, -15, -2, -1]], ![[], [], [-1], [-2, -1], [-15, -2, -1], [-27, -15, -2, -1], [-152, -27, -15, -2, -1], [-240, -152, -27, -15, -2, -1], [-1330, -240, -152, -27, -15, -2, -1], [-1753, -1330, -240, -152, -27, -15, -2, -1]], ![[], [-1], [-2, -1], [-15, -2, -1], [-27, -15, -2, -1], [-152, -27, -15, -2, -1], [-240, -152, -27, -15, -2, -1], [-1330, -240, -152, -27, -15, -2, -1], [-1753, -1330, -240, -152, -27, -15, -2, -1], [-10959, -1753, -1330, -240, -152, -27, -15, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -5, -32, 12, 48, -17, -25, 11, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -5, -32, 12, 48, -17, -25, 11, 2], [2, 15, -3, -69, -8, 108, 14, -67, -3, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -5, -32, 12, 48, -17, -25, 11, 2], [2, 15, -3, -69, -8, 108, 14, -67, -3, 15], [15, 107, -60, -483, 111, 712, -147, -361, 98, 27]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -5, -32, 12, 48, -17, -25, 11, 2], [2, 15, -3, -69, -8, 108, 14, -67, -3, 15], [15, 107, -60, -483, 111, 712, -147, -361, 98, 27], [27, 204, -28, -924, -159, 1407, 253, -822, -64, 152]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -5, -32, 12, 48, -17, -25, 11, 2], [2, 15, -3, -69, -8, 108, 14, -67, -3, 15], [15, 107, -60, -483, 111, 712, -147, -361, 98, 27], [27, 204, -28, -924, -159, 1407, 253, -822, -64, 152], [152, 1091, -556, -4892, 900, 7137, -1177, -3547, 850, 240]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -5, -32, 12, 48, -17, -25, 11, 2], [2, 15, -3, -69, -8, 108, 14, -67, -3, 15], [15, 107, -60, -483, 111, 712, -147, -361, 98, 27], [27, 204, -28, -924, -159, 1407, 253, -822, -64, 152], [152, 1091, -556, -4892, 900, 7137, -1177, -3547, 850, 240], [240, 1832, -109, -8236, -2012, 12420, 3057, -7177, -907, 1330]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -5, -32, 12, 48, -17, -25, 11, 2], [2, 15, -3, -69, -8, 108, 14, -67, -3, 15], [15, 107, -60, -483, 111, 712, -147, -361, 98, 27], [27, 204, -28, -924, -159, 1407, 253, -822, -64, 152], [152, 1091, -556, -4892, 900, 7137, -1177, -3547, 850, 240], [240, 1832, -109, -8236, -2012, 12420, 3057, -7177, -907, 1330], [1330, 9550, -4818, -42669, 7724, 61828, -10190, -30193, 7453, 1753]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -5, -32, 12, 48, -17, -25, 11, 2], [2, 15, -3, -69, -8, 108, 14, -67, -3, 15], [15, 107, -60, -483, 111, 712, -147, -361, 98, 27], [27, 204, -28, -924, -159, 1407, 253, -822, -64, 152], [152, 1091, -556, -4892, 900, 7137, -1177, -3547, 850, 240], [240, 1832, -109, -8236, -2012, 12420, 3057, -7177, -907, 1330], [1330, 9550, -4818, -42669, 7724, 61828, -10190, -30193, 7453, 1753], [1753, 13601, 785, -60914, -21633, 91868, 32027, -54015, -10910, 10959]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -5, -32, 12, 48, -17, -25, 11, 2], [2, 15, -3, -69, -8, 108, 14, -67, -3, 15], [15, 107, -60, -483, 111, 712, -147, -361, 98, 27], [27, 204, -28, -924, -159, 1407, 253, -822, -64, 152], [152, 1091, -556, -4892, 900, 7137, -1177, -3547, 850, 240], [240, 1832, -109, -8236, -2012, 12420, 3057, -7177, -907, 1330], [1330, 9550, -4818, -42669, 7724, 61828, -10190, -30193, 7453, 1753], [1753, 13601, 785, -60914, -21633, 91868, 32027, -54015, -10910, 10959], [10959, 78466, -41194, -349903, 70594, 504399, -94435, -241948, 66534, 11008]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp79 : Fact (Nat.Prime 79) := fact_iff.2 (by norm_num)
instance hp26807191 : Fact (Nat.Prime 26807191) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 4, 4]
  b' := [1, 0, 2, 3, 1]
  k := [1]
  f := [1, 3, 3, 0, 12, 20, 7, 3, 7, 2]
  g := [2, 2, 4, 4, 4, 1]
  h := [2, 2, 4, 4, 4, 1]
  a := [4, 2, 2, 2, 2]
  b := [1, 2, 1, 1, 0, 1, 0, 3, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD79 : CertificateDedekindCriterionLists l 79 where
  n := 2
  a' := [2, 51, 38, 19, 29, 17, 65, 31]
  b' := [69, 11, 48, 22, 37, 45, 17, 18, 58]
  k := [15, 29, 61, 62, 33, 45, 12, 18, 1]
  f := [7, 36, 45, 64, 43, 51, 4, 60, 8, 1]
  g := [8, 41, 51, 73, 48, 57, 4, 69, 8, 1]
  h := [69, 1]
  a := [1, 61, 60, 8, 67, 59, 53, 53, 45]
  b := [19, 62, 58, 7, 53, 22, 36, 26, 34]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD26807191 : CertificateDedekindCriterionLists l 26807191 where
  n := 2
  a' := [7471906, 2340281, 15885068, 7215052, 26197557, 2672834, 12862688, 22488624]
  b' := [17370661, 20140510, 19006230, 14814230, 6827666, 9359584, 9000202, 21957883, 24308455]
  k := [3561653, 18421888, 5677293, 1386618, 15114040, 22758487, 23375931, 1669951, 1]
  f := [12281783, 8890878, 10123920, 6944694, 9582255, 6270462, 12042830, 7581838, 6675790, 1]
  g := [26195408, 18963057, 21592972, 14812106, 20437673, 13374059, 25685752, 16171049, 14238570, 1]
  h := [12568619, 1]
  a := [16158762, 14832251, 15433291, 10270013, 24925657, 26185306, 7871861, 11625059, 18653716]
  b := [26191812, 12514838, 7940798, 17730454, 19747585, 22488799, 9700280, 23740281, 8153475]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 79, 26807191]
  exp := ![1, 1, 1]
  pdgood := [5, 79, 26807191]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp79.out
    exact hp26807191.out
  a := [567232651026, -1629932205100, -5815345394355, 12441074767036, 5785391790394, -17365048495606, 5300498030864, 1984590557104, -782357254280]
  b := [-82545927353, -452307946516, 1087649370591, 1383608879157, -3020290305877, -590821640516, 2439132833981, -690641449040, -214106200796, 78235725428]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 79 T_ofList CD79
    exact satisfiesDedekindCriterion_of_certificate_lists T l 26807191 T_ofList CD26807191

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

end VoightMaximalOrderD10R636

namespace VoightMaximalOrderD10R637

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6620046084325, [1, -7, 11, 16, -42, -5, 37, 0, -11, 0, 1], 1⟩
local notation "l" => [1, -7, 11, 16, -42, -5, 37, 0, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -11, -16, 42, 5, -37, 0, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -11, -16, 42, 5, -37, 0, 11, 0], ![0, -1, 7, -11, -16, 42, 5, -37, 0, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -11, -16, 42, 5, -37, 0, 11, 0], ![0, -1, 7, -11, -16, 42, 5, -37, 0, 11], ![-11, 77, -122, -169, 451, 39, -365, 5, 84, 0]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -11, -16, 42, 5, -37, 0, 11, 0], ![0, -1, 7, -11, -16, 42, 5, -37, 0, 11], ![-11, 77, -122, -169, 451, 39, -365, 5, 84, 0], ![0, -11, 77, -122, -169, 451, 39, -365, 5, 84]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -11, -16, 42, 5, -37, 0, 11, 0], ![0, -1, 7, -11, -16, 42, 5, -37, 0, 11], ![-11, 77, -122, -169, 451, 39, -365, 5, 84, 0], ![0, -11, 77, -122, -169, 451, 39, -365, 5, 84], ![-84, 588, -935, -1267, 3406, 251, -2657, 39, 559, 5]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -11, -16, 42, 5, -37, 0, 11, 0], ![0, -1, 7, -11, -16, 42, 5, -37, 0, 11], ![-11, 77, -122, -169, 451, 39, -365, 5, 84, 0], ![0, -11, 77, -122, -169, 451, 39, -365, 5, 84], ![-84, 588, -935, -1267, 3406, 251, -2657, 39, 559, 5], ![-5, -49, 533, -1015, -1057, 3431, 66, -2657, 94, 559]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -11, -16, 42, 5, -37, 0, 11, 0], ![0, -1, 7, -11, -16, 42, 5, -37, 0, 11], ![-11, 77, -122, -169, 451, 39, -365, 5, 84, 0], ![0, -11, 77, -122, -169, 451, 39, -365, 5, 84], ![-84, 588, -935, -1267, 3406, 251, -2657, 39, 559, 5], ![-5, -49, 533, -1015, -1057, 3431, 66, -2657, 94, 559], ![-559, 3908, -6198, -8411, 22463, 1738, -17252, 66, 3492, 94]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -11, -16, 42, 5, -37, 0, 11, 0], ![0, -1, 7, -11, -16, 42, 5, -37, 0, 11], ![-11, 77, -122, -169, 451, 39, -365, 5, 84, 0], ![0, -11, 77, -122, -169, 451, 39, -365, 5, 84], ![-84, 588, -935, -1267, 3406, 251, -2657, 39, 559, 5], ![-5, -49, 533, -1015, -1057, 3431, 66, -2657, 94, 559], ![-559, 3908, -6198, -8411, 22463, 1738, -17252, 66, 3492, 94], ![-94, 99, 2874, -7702, -4463, 22933, -1740, -17252, 1100, 3492]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -11, -16, 42, 5, -37, 0, 11, 0], ![0, -1, 7, -11, -16, 42, 5, -37, 0, 11], ![-11, 77, -122, -169, 451, 39, -365, 5, 84, 0], ![0, -11, 77, -122, -169, 451, 39, -365, 5, 84], ![-84, 588, -935, -1267, 3406, 251, -2657, 39, 559, 5], ![-5, -49, 533, -1015, -1057, 3431, 66, -2657, 94, 559], ![-559, 3908, -6198, -8411, 22463, 1738, -17252, 66, 3492, 94], ![-94, 99, 2874, -7702, -4463, 22933, -1740, -17252, 1100, 3492], ![-3492, 24350, -38313, -52998, 138962, 12997, -106271, -1740, 21160, 1100]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [0, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [0, -11, 0, -1], [-84, 0, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [0, -11, 0, -1], [-84, 0, -11, 0, -1], [-5, -84, 0, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [0, -11, 0, -1], [-84, 0, -11, 0, -1], [-5, -84, 0, -11, 0, -1], [-559, -5, -84, 0, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [0, -11, 0, -1], [-84, 0, -11, 0, -1], [-5, -84, 0, -11, 0, -1], [-559, -5, -84, 0, -11, 0, -1], [-94, -559, -5, -84, 0, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [0, -11, 0, -1], [-84, 0, -11, 0, -1], [-5, -84, 0, -11, 0, -1], [-559, -5, -84, 0, -11, 0, -1], [-94, -559, -5, -84, 0, -11, 0, -1], [-3492, -94, -559, -5, -84, 0, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -11, -16, 42, 5, -37, 0, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -11, -16, 42, 5, -37, 0, 11, 0], [0, -1, 7, -11, -16, 42, 5, -37, 0, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -11, -16, 42, 5, -37, 0, 11, 0], [0, -1, 7, -11, -16, 42, 5, -37, 0, 11], [-11, 77, -122, -169, 451, 39, -365, 5, 84, 0]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -11, -16, 42, 5, -37, 0, 11, 0], [0, -1, 7, -11, -16, 42, 5, -37, 0, 11], [-11, 77, -122, -169, 451, 39, -365, 5, 84, 0], [0, -11, 77, -122, -169, 451, 39, -365, 5, 84]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -11, -16, 42, 5, -37, 0, 11, 0], [0, -1, 7, -11, -16, 42, 5, -37, 0, 11], [-11, 77, -122, -169, 451, 39, -365, 5, 84, 0], [0, -11, 77, -122, -169, 451, 39, -365, 5, 84], [-84, 588, -935, -1267, 3406, 251, -2657, 39, 559, 5]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -11, -16, 42, 5, -37, 0, 11, 0], [0, -1, 7, -11, -16, 42, 5, -37, 0, 11], [-11, 77, -122, -169, 451, 39, -365, 5, 84, 0], [0, -11, 77, -122, -169, 451, 39, -365, 5, 84], [-84, 588, -935, -1267, 3406, 251, -2657, 39, 559, 5], [-5, -49, 533, -1015, -1057, 3431, 66, -2657, 94, 559]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -11, -16, 42, 5, -37, 0, 11, 0], [0, -1, 7, -11, -16, 42, 5, -37, 0, 11], [-11, 77, -122, -169, 451, 39, -365, 5, 84, 0], [0, -11, 77, -122, -169, 451, 39, -365, 5, 84], [-84, 588, -935, -1267, 3406, 251, -2657, 39, 559, 5], [-5, -49, 533, -1015, -1057, 3431, 66, -2657, 94, 559], [-559, 3908, -6198, -8411, 22463, 1738, -17252, 66, 3492, 94]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -11, -16, 42, 5, -37, 0, 11, 0], [0, -1, 7, -11, -16, 42, 5, -37, 0, 11], [-11, 77, -122, -169, 451, 39, -365, 5, 84, 0], [0, -11, 77, -122, -169, 451, 39, -365, 5, 84], [-84, 588, -935, -1267, 3406, 251, -2657, 39, 559, 5], [-5, -49, 533, -1015, -1057, 3431, 66, -2657, 94, 559], [-559, 3908, -6198, -8411, 22463, 1738, -17252, 66, 3492, 94], [-94, 99, 2874, -7702, -4463, 22933, -1740, -17252, 1100, 3492]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -11, -16, 42, 5, -37, 0, 11, 0], [0, -1, 7, -11, -16, 42, 5, -37, 0, 11], [-11, 77, -122, -169, 451, 39, -365, 5, 84, 0], [0, -11, 77, -122, -169, 451, 39, -365, 5, 84], [-84, 588, -935, -1267, 3406, 251, -2657, 39, 559, 5], [-5, -49, 533, -1015, -1057, 3431, 66, -2657, 94, 559], [-559, 3908, -6198, -8411, 22463, 1738, -17252, 66, 3492, 94], [-94, 99, 2874, -7702, -4463, 22933, -1740, -17252, 1100, 3492], [-3492, 24350, -38313, -52998, 138962, 12997, -106271, -1740, 21160, 1100]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp67 : Fact (Nat.Prime 67) := fact_iff.2 (by norm_num)
instance hp73379 : Fact (Nat.Prime 73379) := fact_iff.2 (by norm_num)
instance hp53861 : Fact (Nat.Prime 53861) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 3
  a' := [4, 4, 0, 0, 1, 3, 2]
  b' := [0, 4, 1, 1, 4, 2, 1, 1]
  k := [4, 2, 3, 3, 3, 4, 0, 0, 3, 2, 3, 1, 2, 3, 1]
  f := [3, 7, 1, -1, 10, 3, -5, 2, 4, 1]
  g := [4, 3, 0, 2, 0, 2, 1, 1, 1]
  h := [4, 4, 1]
  a := [2, 4, 0, 4, 0, 3, 4, 2]
  b := [0, 1, 3, 3, 0, 0, 4, 0, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD67 : CertificateDedekindCriterionLists l 67 where
  n := 2
  a' := [20, 1, 60, 62, 58, 4, 57, 14]
  b' := [38, 24, 26, 6, 35, 14, 44, 23, 58]
  k := [26, 2, 21, 23, 40, 55, 2, 53, 1]
  f := [5, 5, 2, 5, 5, 3, 0, 4, 7, 1]
  g := [48, 40, 15, 48, 35, 23, 2, 38, 60, 1]
  h := [7, 1]
  a := [52, 35, 51, 57, 10, 64, 3, 32, 39]
  b := [63, 18, 17, 61, 46, 61, 1, 25, 28]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD73379 : CertificateDedekindCriterionLists l 73379 where
  n := 2
  a' := [36566, 33606, 42738, 40838, 35881, 6451, 47489, 44473]
  b' := [59645, 28241, 8890, 675, 10166, 35529, 64216, 65699, 11365]
  k := [9401, 41159, 33136, 29546, 28483, 4296, 1995, 63516, 1]
  f := [12588, 31415, 20596, 4845, 5312, 4354, 26399, 28121, 18014, 1]
  g := [22193, 55385, 36310, 8541, 9365, 7676, 46542, 49577, 31758, 1]
  h := [41621, 1]
  a := [44784, 33988, 63782, 41163, 14974, 11198, 3423, 13052, 70304]
  b := [12526, 49375, 48442, 44641, 24295, 60654, 71421, 63831, 3075]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD53861 : CertificateDedekindCriterionLists l 53861 where
  n := 2
  a' := [49520, 46780, 19456, 13552, 6716, 22573, 38516, 1687]
  b' := [40005, 43511, 39677, 17007, 21590, 43757, 45108, 7093, 47689]
  k := [23002, 29999, 39354, 38938, 52852, 26100, 20246, 27770, 1]
  f := [9619, 35523, 14514, 31130, 33432, 23128, 8127, 18329, 10306, 1]
  g := [12960, 47861, 19554, 41942, 45043, 31160, 10949, 24695, 13885, 1]
  h := [39976, 1]
  a := [2627, 49562, 32804, 44660, 31660, 47436, 7083, 36831, 45788]
  b := [24615, 24841, 6013, 4707, 31988, 11680, 4002, 47120, 8073]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 67, 73379, 53861]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 67, 73379, 53861]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp67.out
    exact hp73379.out
    exact hp53861.out
  a := [-760215753200632, 364193921015412, 6052586270644911, -2397896476082514, -8716945507595348, 1434989886669376, 3619807986538168, -166327468179270, -419079184480460]
  b := [-108791394631071, 470327644505182, 38010967878953, -1604913823290263, 374872301065652, 1476952199674842, -180091031666377, -454178219239518, 16632746817927, 41907918448046]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 67 T_ofList CD67
    exact satisfiesDedekindCriterion_of_certificate_lists T l 73379 T_ofList CD73379
    exact satisfiesDedekindCriterion_of_certificate_lists T l 53861 T_ofList CD53861

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

end VoightMaximalOrderD10R637

namespace VoightMaximalOrderD10R640

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6656628272269, [1, 8, 12, -24, -40, 21, 37, -4, -11, 0, 1], 1⟩
local notation "l" => [1, 8, 12, -24, -40, 21, 37, -4, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -12, 24, 40, -21, -37, 4, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -12, 24, 40, -21, -37, 4, 11, 0], ![0, -1, -8, -12, 24, 40, -21, -37, 4, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -12, 24, 40, -21, -37, 4, 11, 0], ![0, -1, -8, -12, 24, 40, -21, -37, 4, 11], ![-11, -88, -133, 256, 428, -207, -367, 23, 84, 4]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -12, 24, 40, -21, -37, 4, 11, 0], ![0, -1, -8, -12, 24, 40, -21, -37, 4, 11], ![-11, -88, -133, 256, 428, -207, -367, 23, 84, 4], ![-4, -43, -136, -37, 416, 344, -355, -351, 67, 84]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -12, 24, 40, -21, -37, 4, 11, 0], ![0, -1, -8, -12, 24, 40, -21, -37, 4, 11], ![-11, -88, -133, 256, 428, -207, -367, 23, 84, 4], ![-4, -43, -136, -37, 416, 344, -355, -351, 67, 84], ![-84, -676, -1051, 1880, 3323, -1348, -2764, -19, 573, 67]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -12, 24, 40, -21, -37, 4, 11, 0], ![0, -1, -8, -12, 24, 40, -21, -37, 4, 11], ![-11, -88, -133, 256, 428, -207, -367, 23, 84, 4], ![-4, -43, -136, -37, 416, 344, -355, -351, 67, 84], ![-84, -676, -1051, 1880, 3323, -1348, -2764, -19, 573, 67], ![-67, -620, -1480, 557, 4560, 1916, -3827, -2496, 718, 573]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -12, 24, 40, -21, -37, 4, 11, 0], ![0, -1, -8, -12, 24, 40, -21, -37, 4, 11], ![-11, -88, -133, 256, 428, -207, -367, 23, 84, 4], ![-4, -43, -136, -37, 416, 344, -355, -351, 67, 84], ![-84, -676, -1051, 1880, 3323, -1348, -2764, -19, 573, 67], ![-67, -620, -1480, 557, 4560, 1916, -3827, -2496, 718, 573], ![-573, -4651, -7496, 12272, 23477, -7473, -19285, -1535, 3807, 718]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -12, 24, 40, -21, -37, 4, 11, 0], ![0, -1, -8, -12, 24, 40, -21, -37, 4, 11], ![-11, -88, -133, 256, 428, -207, -367, 23, 84, 4], ![-4, -43, -136, -37, 416, 344, -355, -351, 67, 84], ![-84, -676, -1051, 1880, 3323, -1348, -2764, -19, 573, 67], ![-67, -620, -1480, 557, 4560, 1916, -3827, -2496, 718, 573], ![-573, -4651, -7496, 12272, 23477, -7473, -19285, -1535, 3807, 718], ![-718, -6317, -13267, 9736, 40992, 8399, -34039, -16413, 6363, 3807]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -12, 24, 40, -21, -37, 4, 11, 0], ![0, -1, -8, -12, 24, 40, -21, -37, 4, 11], ![-11, -88, -133, 256, 428, -207, -367, 23, 84, 4], ![-4, -43, -136, -37, 416, 344, -355, -351, 67, 84], ![-84, -676, -1051, 1880, 3323, -1348, -2764, -19, 573, 67], ![-67, -620, -1480, 557, 4560, 1916, -3827, -2496, 718, 573], ![-573, -4651, -7496, 12272, 23477, -7473, -19285, -1535, 3807, 718], ![-718, -6317, -13267, 9736, 40992, 8399, -34039, -16413, 6363, 3807], ![-3807, -31174, -52001, 78101, 162016, -38955, -132460, -18811, 25464, 6363]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-4, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-4, -11, 0, -1], [-84, -4, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [-4, -11, 0, -1], [-84, -4, -11, 0, -1], [-67, -84, -4, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [-4, -11, 0, -1], [-84, -4, -11, 0, -1], [-67, -84, -4, -11, 0, -1], [-573, -67, -84, -4, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [-4, -11, 0, -1], [-84, -4, -11, 0, -1], [-67, -84, -4, -11, 0, -1], [-573, -67, -84, -4, -11, 0, -1], [-718, -573, -67, -84, -4, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [-4, -11, 0, -1], [-84, -4, -11, 0, -1], [-67, -84, -4, -11, 0, -1], [-573, -67, -84, -4, -11, 0, -1], [-718, -573, -67, -84, -4, -11, 0, -1], [-3807, -718, -573, -67, -84, -4, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -12, 24, 40, -21, -37, 4, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -12, 24, 40, -21, -37, 4, 11, 0], [0, -1, -8, -12, 24, 40, -21, -37, 4, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -12, 24, 40, -21, -37, 4, 11, 0], [0, -1, -8, -12, 24, 40, -21, -37, 4, 11], [-11, -88, -133, 256, 428, -207, -367, 23, 84, 4]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -12, 24, 40, -21, -37, 4, 11, 0], [0, -1, -8, -12, 24, 40, -21, -37, 4, 11], [-11, -88, -133, 256, 428, -207, -367, 23, 84, 4], [-4, -43, -136, -37, 416, 344, -355, -351, 67, 84]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -12, 24, 40, -21, -37, 4, 11, 0], [0, -1, -8, -12, 24, 40, -21, -37, 4, 11], [-11, -88, -133, 256, 428, -207, -367, 23, 84, 4], [-4, -43, -136, -37, 416, 344, -355, -351, 67, 84], [-84, -676, -1051, 1880, 3323, -1348, -2764, -19, 573, 67]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -12, 24, 40, -21, -37, 4, 11, 0], [0, -1, -8, -12, 24, 40, -21, -37, 4, 11], [-11, -88, -133, 256, 428, -207, -367, 23, 84, 4], [-4, -43, -136, -37, 416, 344, -355, -351, 67, 84], [-84, -676, -1051, 1880, 3323, -1348, -2764, -19, 573, 67], [-67, -620, -1480, 557, 4560, 1916, -3827, -2496, 718, 573]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -12, 24, 40, -21, -37, 4, 11, 0], [0, -1, -8, -12, 24, 40, -21, -37, 4, 11], [-11, -88, -133, 256, 428, -207, -367, 23, 84, 4], [-4, -43, -136, -37, 416, 344, -355, -351, 67, 84], [-84, -676, -1051, 1880, 3323, -1348, -2764, -19, 573, 67], [-67, -620, -1480, 557, 4560, 1916, -3827, -2496, 718, 573], [-573, -4651, -7496, 12272, 23477, -7473, -19285, -1535, 3807, 718]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -12, 24, 40, -21, -37, 4, 11, 0], [0, -1, -8, -12, 24, 40, -21, -37, 4, 11], [-11, -88, -133, 256, 428, -207, -367, 23, 84, 4], [-4, -43, -136, -37, 416, 344, -355, -351, 67, 84], [-84, -676, -1051, 1880, 3323, -1348, -2764, -19, 573, 67], [-67, -620, -1480, 557, 4560, 1916, -3827, -2496, 718, 573], [-573, -4651, -7496, 12272, 23477, -7473, -19285, -1535, 3807, 718], [-718, -6317, -13267, 9736, 40992, 8399, -34039, -16413, 6363, 3807]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -12, 24, 40, -21, -37, 4, 11, 0], [0, -1, -8, -12, 24, 40, -21, -37, 4, 11], [-11, -88, -133, 256, 428, -207, -367, 23, 84, 4], [-4, -43, -136, -37, 416, 344, -355, -351, 67, 84], [-84, -676, -1051, 1880, 3323, -1348, -2764, -19, 573, 67], [-67, -620, -1480, 557, 4560, 1916, -3827, -2496, 718, 573], [-573, -4651, -7496, 12272, 23477, -7473, -19285, -1535, 3807, 718], [-718, -6317, -13267, 9736, 40992, 8399, -34039, -16413, 6363, 3807], [-3807, -31174, -52001, 78101, 162016, -38955, -132460, -18811, 25464, 6363]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp17 : Fact (Nat.Prime 17) := fact_iff.2 (by norm_num)
instance hp23033315821 : Fact (Nat.Prime 23033315821) := fact_iff.2 (by norm_num)

def CD17 : CertificateDedekindCriterionLists l 17 where
  n := 2
  a' := [0, 13, 8, 14, 16, 0, 5]
  b' := [8, 8, 12, 12, 0, 13, 13, 10]
  k := [1, 5, 14, 16, 15, 14, 1]
  f := [0, 1, 9, 11, 8, 1, 4, 3, 5, 1]
  g := [1, 15, 14, 8, 2, 10, 3, 7, 1]
  h := [1, 10, 1]
  a := [3, 8, 4, 10, 7, 6, 10, 13]
  b := [1, 16, 0, 16, 16, 0, 2, 16, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD23033315821 : CertificateDedekindCriterionLists l 23033315821 where
  n := 2
  a' := [17876791455, 1197714240, 22173519503, 2420317319, 8790142949, 16004657070, 13966685410, 20619332455]
  b' := [8498681262, 4219309668, 18142196745, 21396728587, 17199796434, 7816578661, 18315809209, 3053258174, 268220374]
  k := [2986721611, 101212350, 10945485932, 5088655184, 7127851973, 13386818934, 12978422979, 8369934075, 1]
  f := [2332656713, 3047174293, 2177908921, 4000658442, 6325036817, 6838648743, 6569143373, 3820942653, 4997954321, 1]
  g := [7328298438, 9573034251, 6842141174, 12568509908, 19870801033, 21484369567, 20637688711, 12003912926, 15701624948, 1]
  h := [7331690873, 1]
  a := [12990929130, 12380684241, 12280030147, 21893165602, 15628477530, 4867975259, 21223071167, 16831226576, 3928358283]
  b := [14436185673, 652041172, 4655271837, 12629167355, 11918137427, 7796379994, 22680066849, 8019373393, 19104957538]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![17, 23033315821]
  exp := ![1, 1]
  pdgood := [17, 23033315821]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp17.out
    exact hp23033315821.out
  a := [-10443128407427, 10360522117936, 61077262593540, -24303898266984, -88388593620368, 4750972986266, 36054563048756, 811500865800, -4198802557520]
  b := [1354336847048, 5085052601541, -5396613512179, -15867392817986, 5560540653555, 14953589370430, -800423415053, -4529192867530, -81150086580, 419880255752]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 17 T_ofList CD17
    exact satisfiesDedekindCriterion_of_certificate_lists T l 23033315821 T_ofList CD23033315821

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

end VoightMaximalOrderD10R640

end TraceEuclidean
