import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk182
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

namespace VoightMaximalOrderD10R195

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3171756563776, [-1, 1, 12, -1, -34, -2, 32, 3, -11, -1, 1], 1⟩
local notation "l" => [-1, 1, 12, -1, -34, -2, 32, 3, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -12, 1, 34, 2, -32, -3, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -12, 1, 34, 2, -32, -3, 11, 1], ![1, 0, -13, -11, 35, 36, -30, -35, 8, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -12, 1, 34, 2, -32, -3, 11, 1], ![1, 0, -13, -11, 35, 36, -30, -35, 8, 12], ![12, -11, -144, -1, 397, 59, -348, -66, 97, 20]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -12, 1, 34, 2, -32, -3, 11, 1], ![1, 0, -13, -11, 35, 36, -30, -35, 8, 12], ![12, -11, -144, -1, 397, 59, -348, -66, 97, 20], ![20, -8, -251, -124, 679, 437, -581, -408, 154, 117]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -12, 1, 34, 2, -32, -3, 11, 1], ![1, 0, -13, -11, 35, 36, -30, -35, 8, 12], ![12, -11, -144, -1, 397, 59, -348, -66, 97, 20], ![20, -8, -251, -124, 679, 437, -581, -408, 154, 117], ![117, -97, -1412, -134, 3854, 913, -3307, -932, 879, 271]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -12, 1, 34, 2, -32, -3, 11, 1], ![1, 0, -13, -11, 35, 36, -30, -35, 8, 12], ![12, -11, -144, -1, 397, 59, -348, -66, 97, 20], ![20, -8, -251, -124, 679, 437, -581, -408, 154, 117], ![117, -97, -1412, -134, 3854, 913, -3307, -932, 879, 271], ![271, -154, -3349, -1141, 9080, 4396, -7759, -4120, 2049, 1150]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -12, 1, 34, 2, -32, -3, 11, 1], ![1, 0, -13, -11, 35, 36, -30, -35, 8, 12], ![12, -11, -144, -1, 397, 59, -348, -66, 97, 20], ![20, -8, -251, -124, 679, 437, -581, -408, 154, 117], ![117, -97, -1412, -134, 3854, 913, -3307, -932, 879, 271], ![271, -154, -3349, -1141, 9080, 4396, -7759, -4120, 2049, 1150], ![1150, -879, -13954, -2199, 37959, 11380, -32404, -11209, 8530, 3199]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -12, 1, 34, 2, -32, -3, 11, 1], ![1, 0, -13, -11, 35, 36, -30, -35, 8, 12], ![12, -11, -144, -1, 397, 59, -348, -66, 97, 20], ![20, -8, -251, -124, 679, 437, -581, -408, 154, 117], ![117, -97, -1412, -134, 3854, 913, -3307, -932, 879, 271], ![271, -154, -3349, -1141, 9080, 4396, -7759, -4120, 2049, 1150], ![1150, -879, -13954, -2199, 37959, 11380, -32404, -11209, 8530, 3199], ![3199, -2049, -39267, -10755, 106567, 44357, -90988, -42001, 23980, 11729]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -12, 1, 34, 2, -32, -3, 11, 1], ![1, 0, -13, -11, 35, 36, -30, -35, 8, 12], ![12, -11, -144, -1, 397, 59, -348, -66, 97, 20], ![20, -8, -251, -124, 679, 437, -581, -408, 154, 117], ![117, -97, -1412, -134, 3854, 913, -3307, -932, 879, 271], ![271, -154, -3349, -1141, 9080, 4396, -7759, -4120, 2049, 1150], ![1150, -879, -13954, -2199, 37959, 11380, -32404, -11209, 8530, 3199], ![3199, -2049, -39267, -10755, 106567, 44357, -90988, -42001, 23980, 11729], ![11729, -8530, -142797, -27538, 388031, 130025, -330971, -126175, 87018, 35709]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-20, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-20, -12, -1, -1], [-117, -20, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-20, -12, -1, -1], [-117, -20, -12, -1, -1], [-271, -117, -20, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-20, -12, -1, -1], [-117, -20, -12, -1, -1], [-271, -117, -20, -12, -1, -1], [-1150, -271, -117, -20, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-20, -12, -1, -1], [-117, -20, -12, -1, -1], [-271, -117, -20, -12, -1, -1], [-1150, -271, -117, -20, -12, -1, -1], [-3199, -1150, -271, -117, -20, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-20, -12, -1, -1], [-117, -20, -12, -1, -1], [-271, -117, -20, -12, -1, -1], [-1150, -271, -117, -20, -12, -1, -1], [-3199, -1150, -271, -117, -20, -12, -1, -1], [-11729, -3199, -1150, -271, -117, -20, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -12, 1, 34, 2, -32, -3, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -12, 1, 34, 2, -32, -3, 11, 1], [1, 0, -13, -11, 35, 36, -30, -35, 8, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -12, 1, 34, 2, -32, -3, 11, 1], [1, 0, -13, -11, 35, 36, -30, -35, 8, 12], [12, -11, -144, -1, 397, 59, -348, -66, 97, 20]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -12, 1, 34, 2, -32, -3, 11, 1], [1, 0, -13, -11, 35, 36, -30, -35, 8, 12], [12, -11, -144, -1, 397, 59, -348, -66, 97, 20], [20, -8, -251, -124, 679, 437, -581, -408, 154, 117]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -12, 1, 34, 2, -32, -3, 11, 1], [1, 0, -13, -11, 35, 36, -30, -35, 8, 12], [12, -11, -144, -1, 397, 59, -348, -66, 97, 20], [20, -8, -251, -124, 679, 437, -581, -408, 154, 117], [117, -97, -1412, -134, 3854, 913, -3307, -932, 879, 271]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -12, 1, 34, 2, -32, -3, 11, 1], [1, 0, -13, -11, 35, 36, -30, -35, 8, 12], [12, -11, -144, -1, 397, 59, -348, -66, 97, 20], [20, -8, -251, -124, 679, 437, -581, -408, 154, 117], [117, -97, -1412, -134, 3854, 913, -3307, -932, 879, 271], [271, -154, -3349, -1141, 9080, 4396, -7759, -4120, 2049, 1150]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -12, 1, 34, 2, -32, -3, 11, 1], [1, 0, -13, -11, 35, 36, -30, -35, 8, 12], [12, -11, -144, -1, 397, 59, -348, -66, 97, 20], [20, -8, -251, -124, 679, 437, -581, -408, 154, 117], [117, -97, -1412, -134, 3854, 913, -3307, -932, 879, 271], [271, -154, -3349, -1141, 9080, 4396, -7759, -4120, 2049, 1150], [1150, -879, -13954, -2199, 37959, 11380, -32404, -11209, 8530, 3199]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -12, 1, 34, 2, -32, -3, 11, 1], [1, 0, -13, -11, 35, 36, -30, -35, 8, 12], [12, -11, -144, -1, 397, 59, -348, -66, 97, 20], [20, -8, -251, -124, 679, 437, -581, -408, 154, 117], [117, -97, -1412, -134, 3854, 913, -3307, -932, 879, 271], [271, -154, -3349, -1141, 9080, 4396, -7759, -4120, 2049, 1150], [1150, -879, -13954, -2199, 37959, 11380, -32404, -11209, 8530, 3199], [3199, -2049, -39267, -10755, 106567, 44357, -90988, -42001, 23980, 11729]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -12, 1, 34, 2, -32, -3, 11, 1], [1, 0, -13, -11, 35, 36, -30, -35, 8, 12], [12, -11, -144, -1, 397, 59, -348, -66, 97, 20], [20, -8, -251, -124, 679, 437, -581, -408, 154, 117], [117, -97, -1412, -134, 3854, 913, -3307, -932, 879, 271], [271, -154, -3349, -1141, 9080, 4396, -7759, -4120, 2049, 1150], [1150, -879, -13954, -2199, 37959, 11380, -32404, -11209, 8530, 3199], [3199, -2049, -39267, -10755, 106567, 44357, -90988, -42001, 23980, 11729], [11729, -8530, -142797, -27538, 388031, 130025, -330971, -126175, 87018, 35709]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp47 : Fact (Nat.Prime 47) := fact_iff.2 (by norm_num)
instance hp229 : Fact (Nat.Prime 229) := fact_iff.2 (by norm_num)
instance hp313 : Fact (Nat.Prime 313) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 1]
  b' := [0, 1, 1, 1, 1, 0, 1]
  k := [1, 1, 1, 0, 0, 1, 1]
  f := [1, 0, -5, 1, 18, 2, -15, -1, 6, 1]
  g := [1, 0, 1, 0, 1, 1, 0, 0, 1]
  h := [1, 1, 1]
  a := [1, 0, 1, 0, 1, 1, 0, 1]
  b := [0, 0, 0, 1, 0, 1, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD47 : CertificateDedekindCriterionLists l 47 where
  n := 2
  a' := [5, 11, 31, 30, 14, 19, 40]
  b' := [28, 4, 30, 11, 20, 43, 25, 42]
  k := [45, 16, 35, 42, 19, 45, 1]
  f := [23, 25, 11, 15, 12, 15, 36, 36, 13, 1]
  g := [40, 8, 11, 16, 5, 21, 45, 22, 1]
  h := [27, 24, 1]
  a := [20, 0, 15, 9, 28, 15, 42, 1]
  b := [32, 14, 6, 40, 10, 43, 33, 14, 46]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD229 : CertificateDedekindCriterionLists l 229 where
  n := 2
  a' := [213, 207, 98, 79, 174, 70, 43, 39]
  b' := [115, 213, 189, 72, 54, 99, 120, 114, 72]
  k := [134, 80, 186, 36, 17, 129, 216, 177, 1]
  f := [129, 70, 9, 115, 78, 132, 87, 22, 54, 1]
  g := [211, 113, 14, 188, 126, 215, 141, 35, 88, 1]
  h := [140, 1]
  a := [34, 108, 33, 131, 43, 135, 145, 215, 131]
  b := [180, 77, 101, 172, 85, 204, 33, 117, 98]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD313 : CertificateDedekindCriterionLists l 313 where
  n := 2
  a' := [90, 205, 102, 220, 118, 103, 299]
  b' := [37, 146, 268, 282, 273, 223, 10, 80]
  k := [274, 254, 3, 268, 262, 76, 1]
  f := [21, 63, 44, 34, 60, 75, 94, 111, 74, 1]
  g := [124, 96, 44, 101, 128, 156, 206, 194, 1]
  h := [53, 118, 1]
  a := [222, 86, 203, 71, 145, 108, 138, 48]
  b := [76, 147, 28, 1, 55, 204, 11, 301, 265]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![2, 47, 229, 313]
  exp := ![2, 1, 1, 1]
  pdgood := [2, 47, 229, 313]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp47.out
    exact hp229.out
    exact hp313.out
  a := [-417361011, -8911591104, 18625704562, 19408137473, -33773434273, -13192439166, 17094111774, 2992421799, -2118804710]
  b := [-403885735, 1199027547, 2557309465, -5402639331, -3427730587, 5868270360, 1743001585, -2164693238, -320430227, 211880471]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 47 T_ofList CD47
    exact satisfiesDedekindCriterion_of_certificate_lists T l 229 T_ofList CD229
    exact satisfiesDedekindCriterion_of_certificate_lists T l 313 T_ofList CD313

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

end VoightMaximalOrderD10R195

namespace VoightMaximalOrderD10R198

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3195947414061, [1, -7, 1, 31, -11, -40, 13, 19, -6, -3, 1], 1⟩
local notation "l" => [1, -7, 1, 31, -11, -40, 13, 19, -6, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -1, -31, 11, 40, -13, -19, 6, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -1, -31, 11, 40, -13, -19, 6, 3], ![-3, 20, 4, -94, 2, 131, 1, -70, -1, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -1, -31, 11, 40, -13, -19, 6, 3], ![-3, 20, 4, -94, 2, 131, 1, -70, -1, 15], ![-15, 102, 5, -461, 71, 602, -64, -284, 20, 44]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -1, -31, 11, 40, -13, -19, 6, 3], ![-3, 20, 4, -94, 2, 131, 1, -70, -1, 15], ![-15, 102, 5, -461, 71, 602, -64, -284, 20, 44], ![-44, 293, 58, -1359, 23, 1831, 30, -900, -20, 152]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -1, -31, 11, 40, -13, -19, 6, 3], ![-3, 20, 4, -94, 2, 131, 1, -70, -1, 15], ![-15, 102, 5, -461, 71, 602, -64, -284, 20, 44], ![-44, 293, 58, -1359, 23, 1831, 30, -900, -20, 152], ![-152, 1020, 141, -4654, 313, 6103, -145, -2858, 12, 436]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -1, -31, 11, 40, -13, -19, 6, 3], ![-3, 20, 4, -94, 2, 131, 1, -70, -1, 15], ![-15, 102, 5, -461, 71, 602, -64, -284, 20, 44], ![-44, 293, 58, -1359, 23, 1831, 30, -900, -20, 152], ![-152, 1020, 141, -4654, 313, 6103, -145, -2858, 12, 436], ![-436, 2900, 584, -13375, 142, 17753, 435, -8429, -242, 1320]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -1, -31, 11, 40, -13, -19, 6, 3], ![-3, 20, 4, -94, 2, 131, 1, -70, -1, 15], ![-15, 102, 5, -461, 71, 602, -64, -284, 20, 44], ![-44, 293, 58, -1359, 23, 1831, 30, -900, -20, 152], ![-152, 1020, 141, -4654, 313, 6103, -145, -2858, 12, 436], ![-436, 2900, 584, -13375, 142, 17753, 435, -8429, -242, 1320], ![-1320, 8804, 1580, -40336, 1145, 52942, 593, -24645, -509, 3718]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -1, -31, 11, 40, -13, -19, 6, 3], ![-3, 20, 4, -94, 2, 131, 1, -70, -1, 15], ![-15, 102, 5, -461, 71, 602, -64, -284, 20, 44], ![-44, 293, 58, -1359, 23, 1831, 30, -900, -20, 152], ![-152, 1020, 141, -4654, 313, 6103, -145, -2858, 12, 436], ![-436, 2900, 584, -13375, 142, 17753, 435, -8429, -242, 1320], ![-1320, 8804, 1580, -40336, 1145, 52942, 593, -24645, -509, 3718], ![-3718, 24706, 5086, -113678, 562, 149865, 4608, -70049, -2337, 10645]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, -1, -31, 11, 40, -13, -19, 6, 3], ![-3, 20, 4, -94, 2, 131, 1, -70, -1, 15], ![-15, 102, 5, -461, 71, 602, -64, -284, 20, 44], ![-44, 293, 58, -1359, 23, 1831, 30, -900, -20, 152], ![-152, 1020, 141, -4654, 313, 6103, -145, -2858, 12, 436], ![-436, 2900, 584, -13375, 142, 17753, 435, -8429, -242, 1320], ![-1320, 8804, 1580, -40336, 1145, 52942, 593, -24645, -509, 3718], ![-3718, 24706, 5086, -113678, 562, 149865, 4608, -70049, -2337, 10645], ![-10645, 70797, 14061, -324909, 3417, 426362, 11480, -197647, -6179, 29598]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1], [-152, -44, -15, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1], [-152, -44, -15, -3, -1], [-436, -152, -44, -15, -3, -1]], ![[], [], [], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1], [-152, -44, -15, -3, -1], [-436, -152, -44, -15, -3, -1], [-1320, -436, -152, -44, -15, -3, -1]], ![[], [], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1], [-152, -44, -15, -3, -1], [-436, -152, -44, -15, -3, -1], [-1320, -436, -152, -44, -15, -3, -1], [-3718, -1320, -436, -152, -44, -15, -3, -1]], ![[], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1], [-152, -44, -15, -3, -1], [-436, -152, -44, -15, -3, -1], [-1320, -436, -152, -44, -15, -3, -1], [-3718, -1320, -436, -152, -44, -15, -3, -1], [-10645, -3718, -1320, -436, -152, -44, -15, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -1, -31, 11, 40, -13, -19, 6, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -1, -31, 11, 40, -13, -19, 6, 3], [-3, 20, 4, -94, 2, 131, 1, -70, -1, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -1, -31, 11, 40, -13, -19, 6, 3], [-3, 20, 4, -94, 2, 131, 1, -70, -1, 15], [-15, 102, 5, -461, 71, 602, -64, -284, 20, 44]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -1, -31, 11, 40, -13, -19, 6, 3], [-3, 20, 4, -94, 2, 131, 1, -70, -1, 15], [-15, 102, 5, -461, 71, 602, -64, -284, 20, 44], [-44, 293, 58, -1359, 23, 1831, 30, -900, -20, 152]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -1, -31, 11, 40, -13, -19, 6, 3], [-3, 20, 4, -94, 2, 131, 1, -70, -1, 15], [-15, 102, 5, -461, 71, 602, -64, -284, 20, 44], [-44, 293, 58, -1359, 23, 1831, 30, -900, -20, 152], [-152, 1020, 141, -4654, 313, 6103, -145, -2858, 12, 436]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -1, -31, 11, 40, -13, -19, 6, 3], [-3, 20, 4, -94, 2, 131, 1, -70, -1, 15], [-15, 102, 5, -461, 71, 602, -64, -284, 20, 44], [-44, 293, 58, -1359, 23, 1831, 30, -900, -20, 152], [-152, 1020, 141, -4654, 313, 6103, -145, -2858, 12, 436], [-436, 2900, 584, -13375, 142, 17753, 435, -8429, -242, 1320]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -1, -31, 11, 40, -13, -19, 6, 3], [-3, 20, 4, -94, 2, 131, 1, -70, -1, 15], [-15, 102, 5, -461, 71, 602, -64, -284, 20, 44], [-44, 293, 58, -1359, 23, 1831, 30, -900, -20, 152], [-152, 1020, 141, -4654, 313, 6103, -145, -2858, 12, 436], [-436, 2900, 584, -13375, 142, 17753, 435, -8429, -242, 1320], [-1320, 8804, 1580, -40336, 1145, 52942, 593, -24645, -509, 3718]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -1, -31, 11, 40, -13, -19, 6, 3], [-3, 20, 4, -94, 2, 131, 1, -70, -1, 15], [-15, 102, 5, -461, 71, 602, -64, -284, 20, 44], [-44, 293, 58, -1359, 23, 1831, 30, -900, -20, 152], [-152, 1020, 141, -4654, 313, 6103, -145, -2858, 12, 436], [-436, 2900, 584, -13375, 142, 17753, 435, -8429, -242, 1320], [-1320, 8804, 1580, -40336, 1145, 52942, 593, -24645, -509, 3718], [-3718, 24706, 5086, -113678, 562, 149865, 4608, -70049, -2337, 10645]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, -1, -31, 11, 40, -13, -19, 6, 3], [-3, 20, 4, -94, 2, 131, 1, -70, -1, 15], [-15, 102, 5, -461, 71, 602, -64, -284, 20, 44], [-44, 293, 58, -1359, 23, 1831, 30, -900, -20, 152], [-152, 1020, 141, -4654, 313, 6103, -145, -2858, 12, 436], [-436, 2900, 584, -13375, 142, 17753, 435, -8429, -242, 1320], [-1320, 8804, 1580, -40336, 1145, 52942, 593, -24645, -509, 3718], [-3718, 24706, 5086, -113678, 562, 149865, 4608, -70049, -2337, 10645], [-10645, 70797, 14061, -324909, 3417, 426362, 11480, -197647, -6179, 29598]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp118368422743 : Fact (Nat.Prime 118368422743) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 2
  a' := [2, 1]
  b' := [0, 2, 2]
  k := [1, 2, 0, 1, 1]
  f := [1, 3, 1, -8, 5, 15, -2, -5, 3, 2]
  g := [2, 1, 1, 2, 1, 1, 2, 1]
  h := [2, 0, 1, 1]
  a := [0, 0, 1, 0, 2, 1]
  b := [2, 2, 2, 2, 1, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD118368422743 : CertificateDedekindCriterionLists l 118368422743 where
  n := 2
  a' := [4610657818, 7974945677, 29579704416, 65578481017, 14019317464, 70807090220, 98075218304, 54917321382]
  b' := [102655430721, 63964371695, 88802519516, 25779156443, 84605793388, 7216760295, 35808961463, 28387032391, 112266498145]
  k := [39170722397, 74713705031, 93657725222, 84019185578, 40286301124, 11030340726, 86284172501, 35347547529, 1]
  f := [86852872718, 63570353055, 71006463780, 2673324996, 37782001115, 45963412008, 17033320073, 42996990664, 15034875045, 1]
  g := [102097158675, 74728126079, 83469411806, 3142542989, 44413441285, 54030841147, 20022982865, 50543757978, 17673773763, 1]
  h := [100694648977, 1]
  a := [19298519296, 71477501935, 19524671458, 76857320364, 99281910299, 22128237994, 47024026532, 29071005256, 93057847068]
  b := [30505886273, 109720292449, 107736335046, 110592965329, 48713048704, 71949310709, 74008036317, 92578977594, 25310575675]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![3, 118368422743]
  exp := ![1, 1]
  pdgood := [3, 118368422743]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp118368422743.out
  a := [-806197458733, -2884462538058, 4559832724294, 10367692594024, -5856489153845, -8794790661120, 3401171464193, 2126461311336, -797374499780]
  b := [-165900389566, 346731270563, 1315657049065, -1035825833346, -2316045045239, 965834211661, 1315879329492, -436595581535, -236567366127, 79737449978]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 118368422743 T_ofList CD118368422743

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

end VoightMaximalOrderD10R198

namespace VoightMaximalOrderD10R199

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3207174374725, [-5, -5, 30, 18, -58, -24, 43, 14, -11, -2, 1], 1⟩
local notation "l" => [-5, -5, 30, 18, -58, -24, 43, 14, -11, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 5, -30, -18, 58, 24, -43, -14, 11, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 5, -30, -18, 58, 24, -43, -14, 11, 2], ![10, 15, -55, -66, 98, 106, -62, -71, 8, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 5, -30, -18, 58, 24, -43, -14, 11, 2], ![10, 15, -55, -66, 98, 106, -62, -71, 8, 15], ![75, 85, -435, -325, 804, 458, -539, -272, 94, 38]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 5, -30, -18, 58, 24, -43, -14, 11, 2], ![10, 15, -55, -66, 98, 106, -62, -71, 8, 15], ![75, 85, -435, -325, 804, 458, -539, -272, 94, 38], ![190, 265, -1055, -1119, 1879, 1716, -1176, -1071, 146, 170]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 5, -30, -18, 58, 24, -43, -14, 11, 2], ![10, 15, -55, -66, 98, 106, -62, -71, 8, 15], ![75, 85, -435, -325, 804, 458, -539, -272, 94, 38], ![190, 265, -1055, -1119, 1879, 1716, -1176, -1071, 146, 170], ![850, 1040, -4835, -4115, 8741, 5959, -5594, -3556, 799, 486]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 5, -30, -18, 58, 24, -43, -14, 11, 2], ![10, 15, -55, -66, 98, 106, -62, -71, 8, 15], ![75, 85, -435, -325, 804, 458, -539, -272, 94, 38], ![190, 265, -1055, -1119, 1879, 1716, -1176, -1071, 146, 170], ![850, 1040, -4835, -4115, 8741, 5959, -5594, -3556, 799, 486], ![2430, 3280, -13540, -13583, 24073, 20405, -14939, -12398, 1790, 1771]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 5, -30, -18, 58, 24, -43, -14, 11, 2], ![10, 15, -55, -66, 98, 106, -62, -71, 8, 15], ![75, 85, -435, -325, 804, 458, -539, -272, 94, 38], ![190, 265, -1055, -1119, 1879, 1716, -1176, -1071, 146, 170], ![850, 1040, -4835, -4115, 8741, 5959, -5594, -3556, 799, 486], ![2430, 3280, -13540, -13583, 24073, 20405, -14939, -12398, 1790, 1771], ![8855, 11285, -49850, -45418, 89135, 66577, -55748, -39733, 7083, 5332]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 5, -30, -18, 58, 24, -43, -14, 11, 2], ![10, 15, -55, -66, 98, 106, -62, -71, 8, 15], ![75, 85, -435, -325, 804, 458, -539, -272, 94, 38], ![190, 265, -1055, -1119, 1879, 1716, -1176, -1071, 146, 170], ![850, 1040, -4835, -4115, 8741, 5959, -5594, -3556, 799, 486], ![2430, 3280, -13540, -13583, 24073, 20405, -14939, -12398, 1790, 1771], ![8855, 11285, -49850, -45418, 89135, 66577, -55748, -39733, 7083, 5332], ![26660, 35515, -148675, -145826, 263838, 217103, -162699, -130396, 18919, 17747]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 5, -30, -18, 58, 24, -43, -14, 11, 2], ![10, 15, -55, -66, 98, 106, -62, -71, 8, 15], ![75, 85, -435, -325, 804, 458, -539, -272, 94, 38], ![190, 265, -1055, -1119, 1879, 1716, -1176, -1071, 146, 170], ![850, 1040, -4835, -4115, 8741, 5959, -5594, -3556, 799, 486], ![2430, 3280, -13540, -13583, 24073, 20405, -14939, -12398, 1790, 1771], ![8855, 11285, -49850, -45418, 89135, 66577, -55748, -39733, 7083, 5332], ![26660, 35515, -148675, -145826, 263838, 217103, -162699, -130396, 18919, 17747], ![88735, 115395, -496895, -468121, 883500, 689766, -546018, -411157, 64821, 54413]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-15, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-15, -2, -1], [-38, -15, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-15, -2, -1], [-38, -15, -2, -1], [-170, -38, -15, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-15, -2, -1], [-38, -15, -2, -1], [-170, -38, -15, -2, -1], [-486, -170, -38, -15, -2, -1]], ![[], [], [], [-1], [-2, -1], [-15, -2, -1], [-38, -15, -2, -1], [-170, -38, -15, -2, -1], [-486, -170, -38, -15, -2, -1], [-1771, -486, -170, -38, -15, -2, -1]], ![[], [], [-1], [-2, -1], [-15, -2, -1], [-38, -15, -2, -1], [-170, -38, -15, -2, -1], [-486, -170, -38, -15, -2, -1], [-1771, -486, -170, -38, -15, -2, -1], [-5332, -1771, -486, -170, -38, -15, -2, -1]], ![[], [-1], [-2, -1], [-15, -2, -1], [-38, -15, -2, -1], [-170, -38, -15, -2, -1], [-486, -170, -38, -15, -2, -1], [-1771, -486, -170, -38, -15, -2, -1], [-5332, -1771, -486, -170, -38, -15, -2, -1], [-17747, -5332, -1771, -486, -170, -38, -15, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 5, -30, -18, 58, 24, -43, -14, 11, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 5, -30, -18, 58, 24, -43, -14, 11, 2], [10, 15, -55, -66, 98, 106, -62, -71, 8, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 5, -30, -18, 58, 24, -43, -14, 11, 2], [10, 15, -55, -66, 98, 106, -62, -71, 8, 15], [75, 85, -435, -325, 804, 458, -539, -272, 94, 38]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 5, -30, -18, 58, 24, -43, -14, 11, 2], [10, 15, -55, -66, 98, 106, -62, -71, 8, 15], [75, 85, -435, -325, 804, 458, -539, -272, 94, 38], [190, 265, -1055, -1119, 1879, 1716, -1176, -1071, 146, 170]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 5, -30, -18, 58, 24, -43, -14, 11, 2], [10, 15, -55, -66, 98, 106, -62, -71, 8, 15], [75, 85, -435, -325, 804, 458, -539, -272, 94, 38], [190, 265, -1055, -1119, 1879, 1716, -1176, -1071, 146, 170], [850, 1040, -4835, -4115, 8741, 5959, -5594, -3556, 799, 486]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 5, -30, -18, 58, 24, -43, -14, 11, 2], [10, 15, -55, -66, 98, 106, -62, -71, 8, 15], [75, 85, -435, -325, 804, 458, -539, -272, 94, 38], [190, 265, -1055, -1119, 1879, 1716, -1176, -1071, 146, 170], [850, 1040, -4835, -4115, 8741, 5959, -5594, -3556, 799, 486], [2430, 3280, -13540, -13583, 24073, 20405, -14939, -12398, 1790, 1771]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 5, -30, -18, 58, 24, -43, -14, 11, 2], [10, 15, -55, -66, 98, 106, -62, -71, 8, 15], [75, 85, -435, -325, 804, 458, -539, -272, 94, 38], [190, 265, -1055, -1119, 1879, 1716, -1176, -1071, 146, 170], [850, 1040, -4835, -4115, 8741, 5959, -5594, -3556, 799, 486], [2430, 3280, -13540, -13583, 24073, 20405, -14939, -12398, 1790, 1771], [8855, 11285, -49850, -45418, 89135, 66577, -55748, -39733, 7083, 5332]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 5, -30, -18, 58, 24, -43, -14, 11, 2], [10, 15, -55, -66, 98, 106, -62, -71, 8, 15], [75, 85, -435, -325, 804, 458, -539, -272, 94, 38], [190, 265, -1055, -1119, 1879, 1716, -1176, -1071, 146, 170], [850, 1040, -4835, -4115, 8741, 5959, -5594, -3556, 799, 486], [2430, 3280, -13540, -13583, 24073, 20405, -14939, -12398, 1790, 1771], [8855, 11285, -49850, -45418, 89135, 66577, -55748, -39733, 7083, 5332], [26660, 35515, -148675, -145826, 263838, 217103, -162699, -130396, 18919, 17747]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 5, -30, -18, 58, 24, -43, -14, 11, 2], [10, 15, -55, -66, 98, 106, -62, -71, 8, 15], [75, 85, -435, -325, 804, 458, -539, -272, 94, 38], [190, 265, -1055, -1119, 1879, 1716, -1176, -1071, 146, 170], [850, 1040, -4835, -4115, 8741, 5959, -5594, -3556, 799, 486], [2430, 3280, -13540, -13583, 24073, 20405, -14939, -12398, 1790, 1771], [8855, 11285, -49850, -45418, 89135, 66577, -55748, -39733, 7083, 5332], [26660, 35515, -148675, -145826, 263838, 217103, -162699, -130396, 18919, 17747], [88735, 115395, -496895, -468121, 883500, 689766, -546018, -411157, 64821, 54413]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp43 : Fact (Nat.Prime 43) := fact_iff.2 (by norm_num)
instance hp2983418023 : Fact (Nat.Prime 2983418023) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 3
  a' := [2, 2, 1, 0, 4, 4, 3]
  b' := [2, 2, 2, 1, 2, 0, 1, 4]
  k := [4, 2, 0, 2, 2, 1, 1, 0, 0, 2, 1, 2, 2, 1, 1]
  f := [1, 1, -6, -3, 12, 5, -8, -2, 3, 1]
  g := [0, 3, 2, 1, 3, 4, 4, 3, 1]
  h := [0, 0, 1]
  a := [1, 2, 1, 4, 3, 4, 1, 3]
  b := [4, 0, 2, 4, 0, 0, 4, 4, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD43 : CertificateDedekindCriterionLists l 43 where
  n := 2
  a' := [1, 33, 13, 2, 0, 19, 12, 37]
  b' := [40, 26, 6, 29, 40, 2, 22, 12, 15]
  k := [15, 18, 36, 33, 22, 12, 34, 18, 1]
  f := [17, 6, 1, 5, 23, 25, 12, 20, 7, 1]
  g := [22, 7, 2, 7, 28, 31, 16, 26, 8, 1]
  h := [33, 1]
  a := [25, 42, 19, 40, 3, 21, 24, 35, 34]
  b := [12, 39, 12, 37, 25, 30, 29, 42, 9]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2983418023 : CertificateDedekindCriterionLists l 2983418023 where
  n := 2
  a' := [655625296, 2827763546, 784191253, 697648264, 549850993, 349658146, 71953661, 2220465235]
  b' := [2849085986, 2430672302, 825704143, 2961160998, 257472099, 2247720311, 734472845, 446015040, 84772532]
  k := [1301669819, 2529633862, 1347306322, 1504615268, 375062055, 494190337, 2173823823, 235168417, 1]
  f := [188001567, 962593629, 50852668, 1099581288, 1032750078, 149954255, 701162673, 755681693, 741220208, 1]
  g := [408177818, 2089926022, 110408286, 2387345478, 2242245529, 325571756, 1522322683, 1640691135, 1609293219, 1]
  h := [1374124802, 1]
  a := [1295229240, 897229447, 638928208, 2332747773, 589690210, 2075581582, 779277663, 159337514, 1718051713]
  b := [2475750076, 299770356, 731260922, 181971918, 2080685525, 310120498, 438180508, 2831346369, 1265366310]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 43, 2983418023]
  exp := ![1, 1, 1]
  pdgood := [5, 43, 2983418023]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp43.out
    exact hp2983418023.out
  a := [-135795136958784, 1453124057395936, 3340399832168968, -2006334351355768, -5846450284076380, -495965538857944, 2032745935465360, 216809873664272, -211952227486740]
  b := [135666849983795, 310673279368388, -415013379071966, -1024014600422296, 260089562444152, 988015310248066, 99803557334030, -253198166309856, -25920031916162, 21195222748674]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 43 T_ofList CD43
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2983418023 T_ofList CD2983418023

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

end VoightMaximalOrderD10R199

namespace VoightMaximalOrderD10R202

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3222676028125, [-1, -4, 7, 37, 11, -49, -13, 27, 0, -5, 1], 1⟩
local notation "l" => [-1, -4, 7, 37, 11, -49, -13, 27, 0, -5, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -37, -11, 49, 13, -27, 0, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -37, -11, 49, 13, -27, 0, 5], ![5, 21, -31, -192, -92, 234, 114, -122, -27, 25]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -37, -11, 49, 13, -27, 0, 5], ![5, 21, -31, -192, -92, 234, 114, -122, -27, 25], ![25, 105, -154, -956, -467, 1133, 559, -561, -122, 98]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -37, -11, 49, 13, -27, 0, 5], ![5, 21, -31, -192, -92, 234, 114, -122, -27, 25], ![25, 105, -154, -956, -467, 1133, 559, -561, -122, 98], ![98, 417, -581, -3780, -2034, 4335, 2407, -2087, -561, 368]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -37, -11, 49, 13, -27, 0, 5], ![5, 21, -31, -192, -92, 234, 114, -122, -27, 25], ![25, 105, -154, -956, -467, 1133, 559, -561, -122, 98], ![98, 417, -581, -3780, -2034, 4335, 2407, -2087, -561, 368], ![368, 1570, -2159, -14197, -7828, 15998, 9119, -7529, -2087, 1279]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -37, -11, 49, 13, -27, 0, 5], ![5, 21, -31, -192, -92, 234, 114, -122, -27, 25], ![25, 105, -154, -956, -467, 1133, 559, -561, -122, 98], ![98, 417, -581, -3780, -2034, 4335, 2407, -2087, -561, 368], ![368, 1570, -2159, -14197, -7828, 15998, 9119, -7529, -2087, 1279], ![1279, 5484, -7383, -49482, -28266, 54843, 32625, -25414, -7529, 4308]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -37, -11, 49, 13, -27, 0, 5], ![5, 21, -31, -192, -92, 234, 114, -122, -27, 25], ![25, 105, -154, -956, -467, 1133, 559, -561, -122, 98], ![98, 417, -581, -3780, -2034, 4335, 2407, -2087, -561, 368], ![368, 1570, -2159, -14197, -7828, 15998, 9119, -7529, -2087, 1279], ![1279, 5484, -7383, -49482, -28266, 54843, 32625, -25414, -7529, 4308], ![4308, 18511, -24672, -166779, -96870, 182826, 110847, -83691, -25414, 14011]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -37, -11, 49, 13, -27, 0, 5], ![5, 21, -31, -192, -92, 234, 114, -122, -27, 25], ![25, 105, -154, -956, -467, 1133, 559, -561, -122, 98], ![98, 417, -581, -3780, -2034, 4335, 2407, -2087, -561, 368], ![368, 1570, -2159, -14197, -7828, 15998, 9119, -7529, -2087, 1279], ![1279, 5484, -7383, -49482, -28266, 54843, 32625, -25414, -7529, 4308], ![4308, 18511, -24672, -166779, -96870, 182826, 110847, -83691, -25414, 14011], ![14011, 60352, -79566, -543079, -320900, 589669, 364969, -267450, -83691, 44641]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -7, -37, -11, 49, 13, -27, 0, 5], ![5, 21, -31, -192, -92, 234, 114, -122, -27, 25], ![25, 105, -154, -956, -467, 1133, 559, -561, -122, 98], ![98, 417, -581, -3780, -2034, 4335, 2407, -2087, -561, 368], ![368, 1570, -2159, -14197, -7828, 15998, 9119, -7529, -2087, 1279], ![1279, 5484, -7383, -49482, -28266, 54843, 32625, -25414, -7529, 4308], ![4308, 18511, -24672, -166779, -96870, 182826, 110847, -83691, -25414, 14011], ![14011, 60352, -79566, -543079, -320900, 589669, 364969, -267450, -83691, 44641], ![44641, 192575, -252135, -1731283, -1034130, 1866509, 1170002, -840338, -267450, 139514]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-5, -1]], ![[], [], [], [], [], [], [], [-1], [-5, -1], [-25, -5, -1]], ![[], [], [], [], [], [], [-1], [-5, -1], [-25, -5, -1], [-98, -25, -5, -1]], ![[], [], [], [], [], [-1], [-5, -1], [-25, -5, -1], [-98, -25, -5, -1], [-368, -98, -25, -5, -1]], ![[], [], [], [], [-1], [-5, -1], [-25, -5, -1], [-98, -25, -5, -1], [-368, -98, -25, -5, -1], [-1279, -368, -98, -25, -5, -1]], ![[], [], [], [-1], [-5, -1], [-25, -5, -1], [-98, -25, -5, -1], [-368, -98, -25, -5, -1], [-1279, -368, -98, -25, -5, -1], [-4308, -1279, -368, -98, -25, -5, -1]], ![[], [], [-1], [-5, -1], [-25, -5, -1], [-98, -25, -5, -1], [-368, -98, -25, -5, -1], [-1279, -368, -98, -25, -5, -1], [-4308, -1279, -368, -98, -25, -5, -1], [-14011, -4308, -1279, -368, -98, -25, -5, -1]], ![[], [-1], [-5, -1], [-25, -5, -1], [-98, -25, -5, -1], [-368, -98, -25, -5, -1], [-1279, -368, -98, -25, -5, -1], [-4308, -1279, -368, -98, -25, -5, -1], [-14011, -4308, -1279, -368, -98, -25, -5, -1], [-44641, -14011, -4308, -1279, -368, -98, -25, -5, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -37, -11, 49, 13, -27, 0, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -37, -11, 49, 13, -27, 0, 5], [5, 21, -31, -192, -92, 234, 114, -122, -27, 25]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -37, -11, 49, 13, -27, 0, 5], [5, 21, -31, -192, -92, 234, 114, -122, -27, 25], [25, 105, -154, -956, -467, 1133, 559, -561, -122, 98]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -37, -11, 49, 13, -27, 0, 5], [5, 21, -31, -192, -92, 234, 114, -122, -27, 25], [25, 105, -154, -956, -467, 1133, 559, -561, -122, 98], [98, 417, -581, -3780, -2034, 4335, 2407, -2087, -561, 368]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -37, -11, 49, 13, -27, 0, 5], [5, 21, -31, -192, -92, 234, 114, -122, -27, 25], [25, 105, -154, -956, -467, 1133, 559, -561, -122, 98], [98, 417, -581, -3780, -2034, 4335, 2407, -2087, -561, 368], [368, 1570, -2159, -14197, -7828, 15998, 9119, -7529, -2087, 1279]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -37, -11, 49, 13, -27, 0, 5], [5, 21, -31, -192, -92, 234, 114, -122, -27, 25], [25, 105, -154, -956, -467, 1133, 559, -561, -122, 98], [98, 417, -581, -3780, -2034, 4335, 2407, -2087, -561, 368], [368, 1570, -2159, -14197, -7828, 15998, 9119, -7529, -2087, 1279], [1279, 5484, -7383, -49482, -28266, 54843, 32625, -25414, -7529, 4308]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -37, -11, 49, 13, -27, 0, 5], [5, 21, -31, -192, -92, 234, 114, -122, -27, 25], [25, 105, -154, -956, -467, 1133, 559, -561, -122, 98], [98, 417, -581, -3780, -2034, 4335, 2407, -2087, -561, 368], [368, 1570, -2159, -14197, -7828, 15998, 9119, -7529, -2087, 1279], [1279, 5484, -7383, -49482, -28266, 54843, 32625, -25414, -7529, 4308], [4308, 18511, -24672, -166779, -96870, 182826, 110847, -83691, -25414, 14011]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -37, -11, 49, 13, -27, 0, 5], [5, 21, -31, -192, -92, 234, 114, -122, -27, 25], [25, 105, -154, -956, -467, 1133, 559, -561, -122, 98], [98, 417, -581, -3780, -2034, 4335, 2407, -2087, -561, 368], [368, 1570, -2159, -14197, -7828, 15998, 9119, -7529, -2087, 1279], [1279, 5484, -7383, -49482, -28266, 54843, 32625, -25414, -7529, 4308], [4308, 18511, -24672, -166779, -96870, 182826, 110847, -83691, -25414, 14011], [14011, 60352, -79566, -543079, -320900, 589669, 364969, -267450, -83691, 44641]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -7, -37, -11, 49, 13, -27, 0, 5], [5, 21, -31, -192, -92, 234, 114, -122, -27, 25], [25, 105, -154, -956, -467, 1133, 559, -561, -122, 98], [98, 417, -581, -3780, -2034, 4335, 2407, -2087, -561, 368], [368, 1570, -2159, -14197, -7828, 15998, 9119, -7529, -2087, 1279], [1279, 5484, -7383, -49482, -28266, 54843, 32625, -25414, -7529, 4308], [4308, 18511, -24672, -166779, -96870, 182826, 110847, -83691, -25414, 14011], [14011, 60352, -79566, -543079, -320900, 589669, 364969, -267450, -83691, 44641], [44641, 192575, -252135, -1731283, -1034130, 1866509, 1170002, -840338, -267450, 139514]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp17 : Fact (Nat.Prime 17) := fact_iff.2 (by norm_num)
instance hp3568361 : Fact (Nat.Prime 3568361) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1]
  b' := [3, 3, 3, 4, 2]
  k := [1]
  f := [2, 2, 0, -7, -2, 11, 3, -5, 0, 1]
  g := [3, 1, 1, 0, 0, 1]
  h := [3, 1, 1, 0, 0, 1]
  a := [4, 1, 3, 3, 2]
  b := [1, 3, 1, 4, 0, 0, 2, 2, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD17 : CertificateDedekindCriterionLists l 17 where
  n := 2
  a' := [12, 9, 12, 16, 3, 13, 8]
  b' := [14, 12, 10, 15, 16, 11, 13, 16]
  k := [4, 10, 6, 5, 5, 9, 1]
  f := [1, 6, 7, 8, 9, 13, 6, 6, 2, 1]
  g := [8, 9, 14, 12, 15, 5, 12, 2, 1]
  h := [2, 10, 1]
  a := [13, 9, 15, 2, 7, 4, 5, 9]
  b := [7, 11, 0, 8, 3, 8, 16, 12, 8]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3568361 : CertificateDedekindCriterionLists l 3568361 where
  n := 2
  a' := [1081966, 3306222, 2638939, 2466130, 631621, 2048968, 3486103, 2211374]
  b' := [567164, 3139802, 1849279, 1545883, 2769472, 685024, 775059, 321404, 1340230]
  k := [1478125, 439544, 1074330, 1925257, 224221, 2371040, 435735, 2514404, 1]
  f := [361177, 172467, 164582, 261530, 276629, 288465, 33679, 326815, 449152, 1]
  g := [2445671, 1167837, 1114447, 1770920, 1873160, 1953306, 228050, 2212992, 3041380, 1]
  h := [526976, 1]
  a := [634796, 3026449, 732891, 1109234, 529619, 613215, 1042617, 3080481, 2721268]
  b := [287807, 802470, 567847, 242621, 2083871, 3211201, 1589504, 1034885, 847093]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 17, 3568361]
  exp := ![1, 1, 1]
  pdgood := [5, 17, 3568361]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp17.out
    exact hp3568361.out
  a := [6744599811, -39609923824, -103449636673, 120054758504, 164838436771, -154726821212, -29727771690, 47546596140, -9295144480]
  b := [-1761977624, -3009040539, 17848861709, 26094515767, -28686976616, -25800511653, 22802010911, 3258699468, -5219416838, 929514448]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 17 T_ofList CD17
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3568361 T_ofList CD3568361

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

end VoightMaximalOrderD10R202

end TraceEuclidean
