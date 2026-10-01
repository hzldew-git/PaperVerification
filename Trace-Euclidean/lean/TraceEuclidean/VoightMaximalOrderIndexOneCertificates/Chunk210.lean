import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk206
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

namespace VoightMaximalOrderD10R466

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5404032653125, [1, 7, 8, -22, -38, 14, 37, -2, -11, 0, 1], 1⟩
local notation "l" => [1, 7, 8, -22, -38, 14, 37, -2, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -8, 22, 38, -14, -37, 2, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -8, 22, 38, -14, -37, 2, 11, 0], ![0, -1, -7, -8, 22, 38, -14, -37, 2, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -8, 22, 38, -14, -37, 2, 11, 0], ![0, -1, -7, -8, 22, 38, -14, -37, 2, 11], ![-11, -77, -89, 235, 410, -132, -369, 8, 84, 2]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -8, 22, 38, -14, -37, 2, 11, 0], ![0, -1, -7, -8, 22, 38, -14, -37, 2, 11], ![-11, -77, -89, 235, 410, -132, -369, 8, 84, 2], ![-2, -25, -93, -45, 311, 382, -206, -365, 30, 84]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -8, 22, 38, -14, -37, 2, 11, 0], ![0, -1, -7, -8, 22, 38, -14, -37, 2, 11], ![-11, -77, -89, 235, 410, -132, -369, 8, 84, 2], ![-2, -25, -93, -45, 311, 382, -206, -365, 30, 84], ![-84, -590, -697, 1755, 3147, -865, -2726, -38, 559, 30]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -8, 22, 38, -14, -37, 2, 11, 0], ![0, -1, -7, -8, 22, 38, -14, -37, 2, 11], ![-11, -77, -89, 235, 410, -132, -369, 8, 84, 2], ![-2, -25, -93, -45, 311, 382, -206, -365, 30, 84], ![-84, -590, -697, 1755, 3147, -865, -2726, -38, 559, 30], ![-30, -294, -830, -37, 2895, 2727, -1975, -2666, 292, 559]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -8, 22, 38, -14, -37, 2, 11, 0], ![0, -1, -7, -8, 22, 38, -14, -37, 2, 11], ![-11, -77, -89, 235, 410, -132, -369, 8, 84, 2], ![-2, -25, -93, -45, 311, 382, -206, -365, 30, 84], ![-84, -590, -697, 1755, 3147, -865, -2726, -38, 559, 30], ![-30, -294, -830, -37, 2895, 2727, -1975, -2666, 292, 559], ![-559, -3943, -4766, 11468, 21205, -4931, -17956, -857, 3483, 292]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -8, 22, 38, -14, -37, 2, 11, 0], ![0, -1, -7, -8, 22, 38, -14, -37, 2, 11], ![-11, -77, -89, 235, 410, -132, -369, 8, 84, 2], ![-2, -25, -93, -45, 311, 382, -206, -365, 30, 84], ![-84, -590, -697, 1755, 3147, -865, -2726, -38, 559, 30], ![-30, -294, -830, -37, 2895, 2727, -1975, -2666, 292, 559], ![-559, -3943, -4766, 11468, 21205, -4931, -17956, -857, 3483, 292], ![-292, -2603, -6279, 1658, 22564, 17117, -15735, -17372, 2355, 3483]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -7, -8, 22, 38, -14, -37, 2, 11, 0], ![0, -1, -7, -8, 22, 38, -14, -37, 2, 11], ![-11, -77, -89, 235, 410, -132, -369, 8, 84, 2], ![-2, -25, -93, -45, 311, 382, -206, -365, 30, 84], ![-84, -590, -697, 1755, 3147, -865, -2726, -38, 559, 30], ![-30, -294, -830, -37, 2895, 2727, -1975, -2666, 292, 559], ![-559, -3943, -4766, 11468, 21205, -4931, -17956, -857, 3483, 292], ![-292, -2603, -6279, 1658, 22564, 17117, -15735, -17372, 2355, 3483], ![-3483, -24673, -30467, 70347, 134012, -26198, -111754, -8769, 20941, 2355]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-84, -2, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-84, -2, -11, 0, -1], [-30, -84, -2, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-84, -2, -11, 0, -1], [-30, -84, -2, -11, 0, -1], [-559, -30, -84, -2, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-84, -2, -11, 0, -1], [-30, -84, -2, -11, 0, -1], [-559, -30, -84, -2, -11, 0, -1], [-292, -559, -30, -84, -2, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-84, -2, -11, 0, -1], [-30, -84, -2, -11, 0, -1], [-559, -30, -84, -2, -11, 0, -1], [-292, -559, -30, -84, -2, -11, 0, -1], [-3483, -292, -559, -30, -84, -2, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -8, 22, 38, -14, -37, 2, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -8, 22, 38, -14, -37, 2, 11, 0], [0, -1, -7, -8, 22, 38, -14, -37, 2, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -8, 22, 38, -14, -37, 2, 11, 0], [0, -1, -7, -8, 22, 38, -14, -37, 2, 11], [-11, -77, -89, 235, 410, -132, -369, 8, 84, 2]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -8, 22, 38, -14, -37, 2, 11, 0], [0, -1, -7, -8, 22, 38, -14, -37, 2, 11], [-11, -77, -89, 235, 410, -132, -369, 8, 84, 2], [-2, -25, -93, -45, 311, 382, -206, -365, 30, 84]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -8, 22, 38, -14, -37, 2, 11, 0], [0, -1, -7, -8, 22, 38, -14, -37, 2, 11], [-11, -77, -89, 235, 410, -132, -369, 8, 84, 2], [-2, -25, -93, -45, 311, 382, -206, -365, 30, 84], [-84, -590, -697, 1755, 3147, -865, -2726, -38, 559, 30]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -8, 22, 38, -14, -37, 2, 11, 0], [0, -1, -7, -8, 22, 38, -14, -37, 2, 11], [-11, -77, -89, 235, 410, -132, -369, 8, 84, 2], [-2, -25, -93, -45, 311, 382, -206, -365, 30, 84], [-84, -590, -697, 1755, 3147, -865, -2726, -38, 559, 30], [-30, -294, -830, -37, 2895, 2727, -1975, -2666, 292, 559]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -8, 22, 38, -14, -37, 2, 11, 0], [0, -1, -7, -8, 22, 38, -14, -37, 2, 11], [-11, -77, -89, 235, 410, -132, -369, 8, 84, 2], [-2, -25, -93, -45, 311, 382, -206, -365, 30, 84], [-84, -590, -697, 1755, 3147, -865, -2726, -38, 559, 30], [-30, -294, -830, -37, 2895, 2727, -1975, -2666, 292, 559], [-559, -3943, -4766, 11468, 21205, -4931, -17956, -857, 3483, 292]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -8, 22, 38, -14, -37, 2, 11, 0], [0, -1, -7, -8, 22, 38, -14, -37, 2, 11], [-11, -77, -89, 235, 410, -132, -369, 8, 84, 2], [-2, -25, -93, -45, 311, 382, -206, -365, 30, 84], [-84, -590, -697, 1755, 3147, -865, -2726, -38, 559, 30], [-30, -294, -830, -37, 2895, 2727, -1975, -2666, 292, 559], [-559, -3943, -4766, 11468, 21205, -4931, -17956, -857, 3483, 292], [-292, -2603, -6279, 1658, 22564, 17117, -15735, -17372, 2355, 3483]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -7, -8, 22, 38, -14, -37, 2, 11, 0], [0, -1, -7, -8, 22, 38, -14, -37, 2, 11], [-11, -77, -89, 235, 410, -132, -369, 8, 84, 2], [-2, -25, -93, -45, 311, 382, -206, -365, 30, 84], [-84, -590, -697, 1755, 3147, -865, -2726, -38, 559, 30], [-30, -294, -830, -37, 2895, 2727, -1975, -2666, 292, 559], [-559, -3943, -4766, 11468, 21205, -4931, -17956, -857, 3483, 292], [-292, -2603, -6279, 1658, 22564, 17117, -15735, -17372, 2355, 3483], [-3483, -24673, -30467, 70347, 134012, -26198, -111754, -8769, 20941, 2355]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1609 : Fact (Nat.Prime 1609) := fact_iff.2 (by norm_num)
instance hp1074761 : Fact (Nat.Prime 1074761) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 3]
  b' := [2, 1, 0, 2, 2]
  k := [1]
  f := [3, 5, 8, 14, 14, 2, -5, 2, 3]
  g := [4, 4, 4, 2, 0, 1]
  h := [4, 4, 4, 2, 0, 1]
  a := [0, 0, 3, 4, 4]
  b := [4, 1, 4, 0, 4, 2, 0, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1609 : CertificateDedekindCriterionLists l 1609 where
  n := 2
  a' := [959, 784, 1393, 600, 437, 418, 633, 925]
  b' := [1354, 65, 339, 1184, 1449, 1475, 820, 573, 76]
  k := [824, 1315, 1099, 597, 356, 142, 608, 1592, 1]
  f := [287, 780, 101, 274, 205, 790, 245, 641, 403, 1]
  g := [568, 1543, 198, 542, 405, 1563, 483, 1268, 796, 1]
  h := [813, 1]
  a := [331, 121, 1340, 5, 190, 1136, 1076, 1476, 1310]
  b := [252, 1607, 582, 1039, 493, 331, 107, 83, 299]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1074761 : CertificateDedekindCriterionLists l 1074761 where
  n := 2
  a' := [385934, 248475, 227991, 52695, 823289, 892164, 895198, 408821]
  b' := [222875, 322640, 909621, 1030997, 779476, 531048, 915490, 751114, 432247]
  k := [737500, 975139, 711600, 421777, 604619, 240377, 199606, 382101, 1]
  f := [112329, 202322, 82904, 241105, 91805, 147821, 27093, 21438, 234729, 1]
  g := [348589, 627862, 257273, 748217, 284895, 458730, 84076, 66528, 728431, 1]
  h := [346330, 1]
  a := [819090, 1018548, 654356, 376349, 538076, 280528, 784802, 871763, 81081]
  b := [952709, 204874, 485548, 262464, 857653, 66035, 568490, 581415, 993680]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 1609, 1074761]
  exp := ![1, 1, 1]
  pdgood := [5, 1609, 1074761]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1609.out
    exact hp1074761.out
  a := [-1944023132516, -1369175715936, 20152943113872, 11138734265376, -35414213513936, -7878651630544, 15347402742220, 1259028553480, -1843736075300]
  b := [278952797823, 1502013268340, -91122239902, -5861826061768, -1602963706578, 6152648017554, 954227280302, -1940362210788, -125902855348, 184373607530]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1609 T_ofList CD1609
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1074761 T_ofList CD1074761

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

end VoightMaximalOrderD10R466

namespace VoightMaximalOrderD10R470

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5446988234752, [1, 6, 5, -24, -34, 22, 38, -4, -12, 0, 1], 1⟩
local notation "l" => [1, 6, 5, -24, -34, 22, 38, -4, -12, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -5, 24, 34, -22, -38, 4, 12, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -5, 24, 34, -22, -38, 4, 12, 0], ![0, -1, -6, -5, 24, 34, -22, -38, 4, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -5, 24, 34, -22, -38, 4, 12, 0], ![0, -1, -6, -5, 24, 34, -22, -38, 4, 12], ![-12, -72, -61, 282, 403, -240, -422, 26, 106, 4]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -5, 24, 34, -22, -38, 4, 12, 0], ![0, -1, -6, -5, 24, 34, -22, -38, 4, 12], ![-12, -72, -61, 282, 403, -240, -422, 26, 106, 4], ![-4, -36, -92, 35, 418, 315, -392, -406, 74, 106]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -5, 24, 34, -22, -38, 4, 12, 0], ![0, -1, -6, -5, 24, 34, -22, -38, 4, 12], ![-12, -72, -61, 282, 403, -240, -422, 26, 106, 4], ![-4, -36, -92, 35, 418, 315, -392, -406, 74, 106], ![-106, -640, -566, 2452, 3639, -1914, -3713, 32, 866, 74]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -5, 24, 34, -22, -38, 4, 12, 0], ![0, -1, -6, -5, 24, 34, -22, -38, 4, 12], ![-12, -72, -61, 282, 403, -240, -422, 26, 106, 4], ![-4, -36, -92, 35, 418, 315, -392, -406, 74, 106], ![-106, -640, -566, 2452, 3639, -1914, -3713, 32, 866, 74], ![-74, -550, -1010, 1210, 4968, 2011, -4726, -3417, 920, 866]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -5, 24, 34, -22, -38, 4, 12, 0], ![0, -1, -6, -5, 24, 34, -22, -38, 4, 12], ![-12, -72, -61, 282, 403, -240, -422, 26, 106, 4], ![-4, -36, -92, 35, 418, 315, -392, -406, 74, 106], ![-106, -640, -566, 2452, 3639, -1914, -3713, 32, 866, 74], ![-74, -550, -1010, 1210, 4968, 2011, -4726, -3417, 920, 866], ![-866, -5270, -4880, 19774, 30654, -14084, -30897, -1262, 6975, 920]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -5, 24, 34, -22, -38, 4, 12, 0], ![0, -1, -6, -5, 24, 34, -22, -38, 4, 12], ![-12, -72, -61, 282, 403, -240, -422, 26, 106, 4], ![-4, -36, -92, 35, 418, 315, -392, -406, 74, 106], ![-106, -640, -566, 2452, 3639, -1914, -3713, 32, 866, 74], ![-74, -550, -1010, 1210, 4968, 2011, -4726, -3417, 920, 866], ![-866, -5270, -4880, 19774, 30654, -14084, -30897, -1262, 6975, 920], ![-920, -6386, -9870, 17200, 51054, 10414, -49044, -27217, 9778, 6975]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -5, 24, 34, -22, -38, 4, 12, 0], ![0, -1, -6, -5, 24, 34, -22, -38, 4, 12], ![-12, -72, -61, 282, 403, -240, -422, 26, 106, 4], ![-4, -36, -92, 35, 418, 315, -392, -406, 74, 106], ![-106, -640, -566, 2452, 3639, -1914, -3713, 32, 866, 74], ![-74, -550, -1010, 1210, 4968, 2011, -4726, -3417, 920, 866], ![-866, -5270, -4880, 19774, 30654, -14084, -30897, -1262, 6975, 920], ![-920, -6386, -9870, 17200, 51054, 10414, -49044, -27217, 9778, 6975], ![-6975, -42770, -41261, 157530, 254350, -102396, -254636, -21144, 56483, 9778]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1], [-106, -4, -12, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1], [-106, -4, -12, 0, -1], [-74, -106, -4, -12, 0, -1]], ![[], [], [], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1], [-106, -4, -12, 0, -1], [-74, -106, -4, -12, 0, -1], [-866, -74, -106, -4, -12, 0, -1]], ![[], [], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1], [-106, -4, -12, 0, -1], [-74, -106, -4, -12, 0, -1], [-866, -74, -106, -4, -12, 0, -1], [-920, -866, -74, -106, -4, -12, 0, -1]], ![[], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1], [-106, -4, -12, 0, -1], [-74, -106, -4, -12, 0, -1], [-866, -74, -106, -4, -12, 0, -1], [-920, -866, -74, -106, -4, -12, 0, -1], [-6975, -920, -866, -74, -106, -4, -12, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -5, 24, 34, -22, -38, 4, 12, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -5, 24, 34, -22, -38, 4, 12, 0], [0, -1, -6, -5, 24, 34, -22, -38, 4, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -5, 24, 34, -22, -38, 4, 12, 0], [0, -1, -6, -5, 24, 34, -22, -38, 4, 12], [-12, -72, -61, 282, 403, -240, -422, 26, 106, 4]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -5, 24, 34, -22, -38, 4, 12, 0], [0, -1, -6, -5, 24, 34, -22, -38, 4, 12], [-12, -72, -61, 282, 403, -240, -422, 26, 106, 4], [-4, -36, -92, 35, 418, 315, -392, -406, 74, 106]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -5, 24, 34, -22, -38, 4, 12, 0], [0, -1, -6, -5, 24, 34, -22, -38, 4, 12], [-12, -72, -61, 282, 403, -240, -422, 26, 106, 4], [-4, -36, -92, 35, 418, 315, -392, -406, 74, 106], [-106, -640, -566, 2452, 3639, -1914, -3713, 32, 866, 74]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -5, 24, 34, -22, -38, 4, 12, 0], [0, -1, -6, -5, 24, 34, -22, -38, 4, 12], [-12, -72, -61, 282, 403, -240, -422, 26, 106, 4], [-4, -36, -92, 35, 418, 315, -392, -406, 74, 106], [-106, -640, -566, 2452, 3639, -1914, -3713, 32, 866, 74], [-74, -550, -1010, 1210, 4968, 2011, -4726, -3417, 920, 866]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -5, 24, 34, -22, -38, 4, 12, 0], [0, -1, -6, -5, 24, 34, -22, -38, 4, 12], [-12, -72, -61, 282, 403, -240, -422, 26, 106, 4], [-4, -36, -92, 35, 418, 315, -392, -406, 74, 106], [-106, -640, -566, 2452, 3639, -1914, -3713, 32, 866, 74], [-74, -550, -1010, 1210, 4968, 2011, -4726, -3417, 920, 866], [-866, -5270, -4880, 19774, 30654, -14084, -30897, -1262, 6975, 920]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -5, 24, 34, -22, -38, 4, 12, 0], [0, -1, -6, -5, 24, 34, -22, -38, 4, 12], [-12, -72, -61, 282, 403, -240, -422, 26, 106, 4], [-4, -36, -92, 35, 418, 315, -392, -406, 74, 106], [-106, -640, -566, 2452, 3639, -1914, -3713, 32, 866, 74], [-74, -550, -1010, 1210, 4968, 2011, -4726, -3417, 920, 866], [-866, -5270, -4880, 19774, 30654, -14084, -30897, -1262, 6975, 920], [-920, -6386, -9870, 17200, 51054, 10414, -49044, -27217, 9778, 6975]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -5, 24, 34, -22, -38, 4, 12, 0], [0, -1, -6, -5, 24, 34, -22, -38, 4, 12], [-12, -72, -61, 282, 403, -240, -422, 26, 106, 4], [-4, -36, -92, 35, 418, 315, -392, -406, 74, 106], [-106, -640, -566, 2452, 3639, -1914, -3713, 32, 866, 74], [-74, -550, -1010, 1210, 4968, 2011, -4726, -3417, 920, 866], [-866, -5270, -4880, 19774, 30654, -14084, -30897, -1262, 6975, 920], [-920, -6386, -9870, 17200, 51054, 10414, -49044, -27217, 9778, 6975], [-6975, -42770, -41261, 157530, 254350, -102396, -254636, -21144, 56483, 9778]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp23 : Fact (Nat.Prime 23) := fact_iff.2 (by norm_num)
instance hp7227343 : Fact (Nat.Prime 7227343) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1]
  b' := [0, 1]
  k := [1]
  f := [0, -2, -2, 12, 17, -10, -18, 2, 6]
  g := [1, 1, 0, 0, 0, 1]
  h := [1, 1, 0, 0, 0, 1]
  a := [1, 1, 1, 1, 1]
  b := [1, 1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD23 : CertificateDedekindCriterionLists l 23 where
  n := 2
  a' := [4, 13, 13, 3, 13, 15, 2, 12]
  b' := [5, 14, 16, 12, 9, 9, 1, 17, 14]
  k := [8, 3, 8, 15, 8, 11, 20, 9, 1]
  f := [3, 2, 4, 8, 3, 4, 3, 5, 6, 1]
  g := [10, 6, 13, 21, 2, 16, 13, 14, 16, 1]
  h := [7, 1]
  a := [12, 13, 14, 21, 9, 1, 2, 2, 11]
  b := [8, 5, 21, 0, 10, 0, 13, 16, 12]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD7227343 : CertificateDedekindCriterionLists l 7227343 where
  n := 2
  a' := [3564706, 6103686, 4009447, 3475642, 619264, 5751003, 429122, 6928984]
  b' := [2441752, 7215585, 2099776, 6210214, 5937630, 831709, 163848, 3930576, 33151]
  k := [1639298, 5675644, 7192514, 7101116, 1468952, 4109326, 3183228, 5561705, 1]
  f := [75558, 264449, 316905, 536120, 678392, 676666, 277775, 122269, 736852, 1]
  g := [655705, 2294932, 2750152, 4652536, 5887194, 5872214, 2410571, 1061068, 6394524, 1]
  h := [832819, 1]
  a := [2669642, 1973847, 6859118, 4853080, 4689374, 6587517, 4900102, 6495441, 6026719]
  b := [3253716, 503898, 592932, 2956633, 2412831, 5317276, 4033833, 5127955, 1200624]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 23, 7227343]
  exp := ![2, 1, 1]
  pdgood := [2, 23, 7227343]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp23.out
    exact hp7227343.out
  a := [-153469310446, 128912764324, 1484684761270, -129110000762, -2358533652088, -172090922192, 1015817681918, 52368979110, -109083575730]
  b := [25689037667, 89168786947, -88815325405, -384135133706, 55588071374, 400412362990, 16687618118, -127761826367, -5236897911, 10908357573]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 23 T_ofList CD23
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7227343 T_ofList CD7227343

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

end VoightMaximalOrderD10R470

namespace VoightMaximalOrderD10R471

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5467489192972, [1, -5, -6, 36, -8, -50, 21, 19, -9, -2, 1], 1⟩
local notation "l" => [1, -5, -6, 36, -8, -50, 21, 19, -9, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -36, 8, 50, -21, -19, 9, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -36, 8, 50, -21, -19, 9, 2], ![-2, 9, 17, -66, -20, 108, 8, -59, -1, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -36, 8, 50, -21, -19, 9, 2], ![-2, 9, 17, -66, -20, 108, 8, -59, -1, 13], ![-13, 63, 87, -451, 38, 630, -165, -239, 58, 25]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -36, 8, 50, -21, -19, 9, 2], ![-2, 9, 17, -66, -20, 108, 8, -59, -1, 13], ![-13, 63, 87, -451, 38, 630, -165, -239, 58, 25], ![-25, 112, 213, -813, -251, 1288, 105, -640, -14, 108]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -36, 8, 50, -21, -19, 9, 2], ![-2, 9, 17, -66, -20, 108, 8, -59, -1, 13], ![-13, 63, 87, -451, 38, 630, -165, -239, 58, 25], ![-25, 112, 213, -813, -251, 1288, 105, -640, -14, 108], ![-108, 515, 760, -3675, 51, 5149, -980, -1947, 332, 202]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -36, 8, 50, -21, -19, 9, 2], ![-2, 9, 17, -66, -20, 108, 8, -59, -1, 13], ![-13, 63, 87, -451, 38, 630, -165, -239, 58, 25], ![-25, 112, 213, -813, -251, 1288, 105, -640, -14, 108], ![-108, 515, 760, -3675, 51, 5149, -980, -1947, 332, 202], ![-202, 902, 1727, -6512, -2059, 10151, 907, -4818, -129, 736]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -36, 8, 50, -21, -19, 9, 2], ![-2, 9, 17, -66, -20, 108, 8, -59, -1, 13], ![-13, 63, 87, -451, 38, 630, -165, -239, 58, 25], ![-25, 112, 213, -813, -251, 1288, 105, -640, -14, 108], ![-108, 515, 760, -3675, 51, 5149, -980, -1947, 332, 202], ![-202, 902, 1727, -6512, -2059, 10151, 907, -4818, -129, 736], ![-736, 3478, 5318, -24769, -624, 34741, -5305, -13077, 1806, 1343]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -36, 8, 50, -21, -19, 9, 2], ![-2, 9, 17, -66, -20, 108, 8, -59, -1, 13], ![-13, 63, 87, -451, 38, 630, -165, -239, 58, 25], ![-25, 112, 213, -813, -251, 1288, 105, -640, -14, 108], ![-108, 515, 760, -3675, 51, 5149, -980, -1947, 332, 202], ![-202, 902, 1727, -6512, -2059, 10151, 907, -4818, -129, 736], ![-736, 3478, 5318, -24769, -624, 34741, -5305, -13077, 1806, 1343], ![-1343, 5979, 11536, -43030, -14025, 66526, 6538, -30822, -990, 4492]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -36, 8, 50, -21, -19, 9, 2], ![-2, 9, 17, -66, -20, 108, 8, -59, -1, 13], ![-13, 63, 87, -451, 38, 630, -165, -239, 58, 25], ![-25, 112, 213, -813, -251, 1288, 105, -640, -14, 108], ![-108, 515, 760, -3675, 51, 5149, -980, -1947, 332, 202], ![-202, 902, 1727, -6512, -2059, 10151, 907, -4818, -129, 736], ![-736, 3478, 5318, -24769, -624, 34741, -5305, -13077, 1806, 1343], ![-1343, 5979, 11536, -43030, -14025, 66526, 6538, -30822, -990, 4492], ![-4492, 21117, 32931, -150176, -7094, 210575, -27806, -78810, 9606, 7994]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-25, -13, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-25, -13, -2, -1], [-108, -25, -13, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-25, -13, -2, -1], [-108, -25, -13, -2, -1], [-202, -108, -25, -13, -2, -1]], ![[], [], [], [-1], [-2, -1], [-13, -2, -1], [-25, -13, -2, -1], [-108, -25, -13, -2, -1], [-202, -108, -25, -13, -2, -1], [-736, -202, -108, -25, -13, -2, -1]], ![[], [], [-1], [-2, -1], [-13, -2, -1], [-25, -13, -2, -1], [-108, -25, -13, -2, -1], [-202, -108, -25, -13, -2, -1], [-736, -202, -108, -25, -13, -2, -1], [-1343, -736, -202, -108, -25, -13, -2, -1]], ![[], [-1], [-2, -1], [-13, -2, -1], [-25, -13, -2, -1], [-108, -25, -13, -2, -1], [-202, -108, -25, -13, -2, -1], [-736, -202, -108, -25, -13, -2, -1], [-1343, -736, -202, -108, -25, -13, -2, -1], [-4492, -1343, -736, -202, -108, -25, -13, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -36, 8, 50, -21, -19, 9, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -36, 8, 50, -21, -19, 9, 2], [-2, 9, 17, -66, -20, 108, 8, -59, -1, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -36, 8, 50, -21, -19, 9, 2], [-2, 9, 17, -66, -20, 108, 8, -59, -1, 13], [-13, 63, 87, -451, 38, 630, -165, -239, 58, 25]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -36, 8, 50, -21, -19, 9, 2], [-2, 9, 17, -66, -20, 108, 8, -59, -1, 13], [-13, 63, 87, -451, 38, 630, -165, -239, 58, 25], [-25, 112, 213, -813, -251, 1288, 105, -640, -14, 108]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -36, 8, 50, -21, -19, 9, 2], [-2, 9, 17, -66, -20, 108, 8, -59, -1, 13], [-13, 63, 87, -451, 38, 630, -165, -239, 58, 25], [-25, 112, 213, -813, -251, 1288, 105, -640, -14, 108], [-108, 515, 760, -3675, 51, 5149, -980, -1947, 332, 202]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -36, 8, 50, -21, -19, 9, 2], [-2, 9, 17, -66, -20, 108, 8, -59, -1, 13], [-13, 63, 87, -451, 38, 630, -165, -239, 58, 25], [-25, 112, 213, -813, -251, 1288, 105, -640, -14, 108], [-108, 515, 760, -3675, 51, 5149, -980, -1947, 332, 202], [-202, 902, 1727, -6512, -2059, 10151, 907, -4818, -129, 736]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -36, 8, 50, -21, -19, 9, 2], [-2, 9, 17, -66, -20, 108, 8, -59, -1, 13], [-13, 63, 87, -451, 38, 630, -165, -239, 58, 25], [-25, 112, 213, -813, -251, 1288, 105, -640, -14, 108], [-108, 515, 760, -3675, 51, 5149, -980, -1947, 332, 202], [-202, 902, 1727, -6512, -2059, 10151, 907, -4818, -129, 736], [-736, 3478, 5318, -24769, -624, 34741, -5305, -13077, 1806, 1343]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -36, 8, 50, -21, -19, 9, 2], [-2, 9, 17, -66, -20, 108, 8, -59, -1, 13], [-13, 63, 87, -451, 38, 630, -165, -239, 58, 25], [-25, 112, 213, -813, -251, 1288, 105, -640, -14, 108], [-108, 515, 760, -3675, 51, 5149, -980, -1947, 332, 202], [-202, 902, 1727, -6512, -2059, 10151, 907, -4818, -129, 736], [-736, 3478, 5318, -24769, -624, 34741, -5305, -13077, 1806, 1343], [-1343, 5979, 11536, -43030, -14025, 66526, 6538, -30822, -990, 4492]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -36, 8, 50, -21, -19, 9, 2], [-2, 9, 17, -66, -20, 108, 8, -59, -1, 13], [-13, 63, 87, -451, 38, 630, -165, -239, 58, 25], [-25, 112, 213, -813, -251, 1288, 105, -640, -14, 108], [-108, 515, 760, -3675, 51, 5149, -980, -1947, 332, 202], [-202, 902, 1727, -6512, -2059, 10151, 907, -4818, -129, 736], [-736, 3478, 5318, -24769, -624, 34741, -5305, -13077, 1806, 1343], [-1343, 5979, 11536, -43030, -14025, 66526, 6538, -30822, -990, 4492], [-4492, 21117, 32931, -150176, -7094, 210575, -27806, -78810, 9606, 7994]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp1123 : Fact (Nat.Prime 1123) := fact_iff.2 (by norm_num)
instance hp1217161441 : Fact (Nat.Prime 1217161441) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 0, 0, 0, 0, 1]
  b' := [1, 1, 0, 0, 1, 0, 1, 1]
  k := [1, 1, 1, 1, 1, 1, 0, 0, 1]
  f := [0, 3, 3, -18, 4, 25, -10, -9, 5, 2]
  g := [1, 0, 0, 0, 0, 0, 1, 0, 1, 1]
  h := [1, 1]
  a := [0, 0, 0, 0, 0, 0, 0, 1]
  b := [1, 0, 0, 0, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1123 : CertificateDedekindCriterionLists l 1123 where
  n := 2
  a' := [1007, 342, 55, 1024, 25, 434, 1062, 247]
  b' := [1067, 749, 367, 363, 614, 138, 321, 1114, 846]
  k := [522, 613, 875, 218, 523, 621, 1029, 76, 1]
  f := [945, 192, 172, 226, 34, 975, 887, 301, 36, 1]
  g := [979, 198, 178, 234, 35, 1010, 918, 311, 37, 1]
  h := [1084, 1]
  a := [249, 707, 995, 326, 229, 250, 679, 31, 696]
  b := [823, 1120, 727, 281, 877, 281, 774, 665, 427]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1217161441 : CertificateDedekindCriterionLists l 1217161441 where
  n := 2
  a' := [760605191, 204210006, 232259859, 931858589, 590424699, 1203726997, 1125093256, 901285340]
  b' := [35158063, 722472615, 558168038, 445562919, 586313273, 539860516, 30123557, 732831510, 576057985]
  k := [1000813869, 183129296, 1111635830, 1103434521, 616988283, 492016654, 210437153, 175462375, 1]
  f := [308496931, 112643716, 482634158, 186803589, 282044598, 3762540, 277701664, 178605328, 297966826, 1]
  g := [720919471, 263234540, 1127856801, 436537062, 659103614, 8792593, 648954711, 417378733, 696311907, 1]
  h := [520849532, 1]
  a := [194904181, 1029875434, 115479580, 138323826, 281362554, 781894579, 726584995, 1102922832, 994004458]
  b := [518603107, 681018062, 74611466, 938272906, 215478590, 759024798, 960992150, 716975026, 223156983]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 1123, 1217161441]
  exp := ![1, 1, 1]
  pdgood := [2, 1123, 1217161441]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp1123.out
    exact hp1217161441.out
  a := [-17614388753974, -85344716560389, 242098550916236, 303971837474999, -391642986082824, -177531247287735, 181799954970134, 24605061766250, -23436770026850]
  b := [-4069626670092, 10312549450117, 42247638494137, -58311776152195, -69139361757011, 65008684663309, 27575665014685, -22750236587488, -2929241577162, 2343677002685]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1123 T_ofList CD1123
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1217161441 T_ofList CD1217161441

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

end VoightMaximalOrderD10R471

namespace VoightMaximalOrderD10R473

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5478329903125, [-5, 5, 49, 1, -79, -13, 45, 7, -11, -1, 1], 1⟩
local notation "l" => [-5, 5, 49, 1, -79, -13, 45, 7, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -5, -49, -1, 79, 13, -45, -7, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -5, -49, -1, 79, 13, -45, -7, 11, 1], ![5, 0, -54, -50, 78, 92, -32, -52, 4, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -5, -49, -1, 79, 13, -45, -7, 11, 1], ![5, 0, -54, -50, 78, 92, -32, -52, 4, 12], ![60, -55, -588, -66, 898, 234, -448, -116, 80, 16]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -5, -49, -1, 79, 13, -45, -7, 11, 1], ![5, 0, -54, -50, 78, 92, -32, -52, 4, 12], ![60, -55, -588, -66, 898, 234, -448, -116, 80, 16], ![80, -20, -839, -604, 1198, 1106, -486, -560, 60, 96]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -5, -49, -1, 79, 13, -45, -7, 11, 1], ![5, 0, -54, -50, 78, 92, -32, -52, 4, 12], ![60, -55, -588, -66, 898, 234, -448, -116, 80, 16], ![80, -20, -839, -604, 1198, 1106, -486, -560, 60, 96], ![480, -400, -4724, -935, 6980, 2446, -3214, -1158, 496, 156]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -5, -49, -1, 79, 13, -45, -7, 11, 1], ![5, 0, -54, -50, 78, 92, -32, -52, 4, 12], ![60, -55, -588, -66, 898, 234, -448, -116, 80, 16], ![80, -20, -839, -604, 1198, 1106, -486, -560, 60, 96], ![480, -400, -4724, -935, 6980, 2446, -3214, -1158, 496, 156], ![780, -300, -8044, -4880, 11389, 9008, -4574, -4306, 558, 652]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -5, -49, -1, 79, 13, -45, -7, 11, 1], ![5, 0, -54, -50, 78, 92, -32, -52, 4, 12], ![60, -55, -588, -66, 898, 234, -448, -116, 80, 16], ![80, -20, -839, -604, 1198, 1106, -486, -560, 60, 96], ![480, -400, -4724, -935, 6980, 2446, -3214, -1158, 496, 156], ![780, -300, -8044, -4880, 11389, 9008, -4574, -4306, 558, 652], ![3260, -2480, -32248, -8696, 46628, 19865, -20332, -9138, 2866, 1210]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -5, -49, -1, 79, 13, -45, -7, 11, 1], ![5, 0, -54, -50, 78, 92, -32, -52, 4, 12], ![60, -55, -588, -66, 898, 234, -448, -116, 80, 16], ![80, -20, -839, -604, 1198, 1106, -486, -560, 60, 96], ![480, -400, -4724, -935, 6980, 2446, -3214, -1158, 496, 156], ![780, -300, -8044, -4880, 11389, 9008, -4574, -4306, 558, 652], ![3260, -2480, -32248, -8696, 46628, 19865, -20332, -9138, 2866, 1210], ![6050, -2790, -61770, -33458, 86894, 62358, -34585, -28802, 4172, 4076]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -5, -49, -1, 79, 13, -45, -7, 11, 1], ![5, 0, -54, -50, 78, 92, -32, -52, 4, 12], ![60, -55, -588, -66, 898, 234, -448, -116, 80, 16], ![80, -20, -839, -604, 1198, 1106, -486, -560, 60, 96], ![480, -400, -4724, -935, 6980, 2446, -3214, -1158, 496, 156], ![780, -300, -8044, -4880, 11389, 9008, -4574, -4306, 558, 652], ![3260, -2480, -32248, -8696, 46628, 19865, -20332, -9138, 2866, 1210], ![6050, -2790, -61770, -33458, 86894, 62358, -34585, -28802, 4172, 4076], ![20380, -14330, -202514, -65846, 288546, 139882, -121062, -63117, 16034, 8248]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-16, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-16, -12, -1, -1], [-96, -16, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-16, -12, -1, -1], [-96, -16, -12, -1, -1], [-156, -96, -16, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-16, -12, -1, -1], [-96, -16, -12, -1, -1], [-156, -96, -16, -12, -1, -1], [-652, -156, -96, -16, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-16, -12, -1, -1], [-96, -16, -12, -1, -1], [-156, -96, -16, -12, -1, -1], [-652, -156, -96, -16, -12, -1, -1], [-1210, -652, -156, -96, -16, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-16, -12, -1, -1], [-96, -16, -12, -1, -1], [-156, -96, -16, -12, -1, -1], [-652, -156, -96, -16, -12, -1, -1], [-1210, -652, -156, -96, -16, -12, -1, -1], [-4076, -1210, -652, -156, -96, -16, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -5, -49, -1, 79, 13, -45, -7, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -5, -49, -1, 79, 13, -45, -7, 11, 1], [5, 0, -54, -50, 78, 92, -32, -52, 4, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -5, -49, -1, 79, 13, -45, -7, 11, 1], [5, 0, -54, -50, 78, 92, -32, -52, 4, 12], [60, -55, -588, -66, 898, 234, -448, -116, 80, 16]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -5, -49, -1, 79, 13, -45, -7, 11, 1], [5, 0, -54, -50, 78, 92, -32, -52, 4, 12], [60, -55, -588, -66, 898, 234, -448, -116, 80, 16], [80, -20, -839, -604, 1198, 1106, -486, -560, 60, 96]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -5, -49, -1, 79, 13, -45, -7, 11, 1], [5, 0, -54, -50, 78, 92, -32, -52, 4, 12], [60, -55, -588, -66, 898, 234, -448, -116, 80, 16], [80, -20, -839, -604, 1198, 1106, -486, -560, 60, 96], [480, -400, -4724, -935, 6980, 2446, -3214, -1158, 496, 156]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -5, -49, -1, 79, 13, -45, -7, 11, 1], [5, 0, -54, -50, 78, 92, -32, -52, 4, 12], [60, -55, -588, -66, 898, 234, -448, -116, 80, 16], [80, -20, -839, -604, 1198, 1106, -486, -560, 60, 96], [480, -400, -4724, -935, 6980, 2446, -3214, -1158, 496, 156], [780, -300, -8044, -4880, 11389, 9008, -4574, -4306, 558, 652]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -5, -49, -1, 79, 13, -45, -7, 11, 1], [5, 0, -54, -50, 78, 92, -32, -52, 4, 12], [60, -55, -588, -66, 898, 234, -448, -116, 80, 16], [80, -20, -839, -604, 1198, 1106, -486, -560, 60, 96], [480, -400, -4724, -935, 6980, 2446, -3214, -1158, 496, 156], [780, -300, -8044, -4880, 11389, 9008, -4574, -4306, 558, 652], [3260, -2480, -32248, -8696, 46628, 19865, -20332, -9138, 2866, 1210]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -5, -49, -1, 79, 13, -45, -7, 11, 1], [5, 0, -54, -50, 78, 92, -32, -52, 4, 12], [60, -55, -588, -66, 898, 234, -448, -116, 80, 16], [80, -20, -839, -604, 1198, 1106, -486, -560, 60, 96], [480, -400, -4724, -935, 6980, 2446, -3214, -1158, 496, 156], [780, -300, -8044, -4880, 11389, 9008, -4574, -4306, 558, 652], [3260, -2480, -32248, -8696, 46628, 19865, -20332, -9138, 2866, 1210], [6050, -2790, -61770, -33458, 86894, 62358, -34585, -28802, 4172, 4076]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -5, -49, -1, 79, 13, -45, -7, 11, 1], [5, 0, -54, -50, 78, 92, -32, -52, 4, 12], [60, -55, -588, -66, 898, 234, -448, -116, 80, 16], [80, -20, -839, -604, 1198, 1106, -486, -560, 60, 96], [480, -400, -4724, -935, 6980, 2446, -3214, -1158, 496, 156], [780, -300, -8044, -4880, 11389, 9008, -4574, -4306, 558, 652], [3260, -2480, -32248, -8696, 46628, 19865, -20332, -9138, 2866, 1210], [6050, -2790, -61770, -33458, 86894, 62358, -34585, -28802, 4172, 4076], [20380, -14330, -202514, -65846, 288546, 139882, -121062, -63117, 16034, 8248]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp359 : Fact (Nat.Prime 359) := fact_iff.2 (by norm_num)
instance hp4883191 : Fact (Nat.Prime 4883191) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 2, 3]
  b' := [2, 3, 3, 4, 4]
  k := [1]
  f := [1, -1, -8, 1, 16, 5, -7, -1, 3, 1]
  g := [0, 3, 1, 0, 2, 1]
  h := [0, 3, 1, 0, 2, 1]
  a := [1, 1, 2, 0, 2]
  b := [0, 4, 0, 4, 4, 1, 4, 3, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD359 : CertificateDedekindCriterionLists l 359 where
  n := 2
  a' := [44, 81, 59, 317, 30, 98, 126, 154]
  b' := [272, 148, 107, 344, 115, 51, 280, 124, 302]
  k := [77, 101, 177, 336, 261, 109, 104, 33, 1]
  f := [121, 148, 308, 200, 198, 194, 130, 249, 16, 1]
  g := [127, 155, 323, 209, 207, 203, 136, 261, 16, 1]
  h := [342, 1]
  a := [357, 169, 107, 241, 192, 76, 30, 137, 302]
  b := [180, 252, 207, 223, 297, 323, 4, 222, 57]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD4883191 : CertificateDedekindCriterionLists l 4883191 where
  n := 2
  a' := [4300168, 2573134, 1160981, 3716909, 4319637, 535117, 4805679, 1835089]
  b' := [71358, 2217216, 893872, 2051195, 4674635, 2774871, 1365693, 1857815, 338678]
  k := [1835981, 3793658, 2639987, 4451090, 1663390, 1878661, 4753399, 1848306, 1]
  f := [736145, 210770, 827538, 7048, 125646, 837361, 1177487, 649549, 1045900, 1]
  g := [2368945, 678265, 2663051, 22679, 404334, 2694662, 3789200, 2090273, 3365748, 1]
  h := [1517442, 1]
  a := [4427510, 4084601, 1811408, 4460448, 3407707, 1445000, 1588513, 380665, 4306646]
  b := [1733250, 4416044, 1884812, 1128033, 1173411, 4475523, 2539558, 3985884, 576545]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 359, 4883191]
  exp := ![1, 1, 1]
  pdgood := [5, 359, 4883191]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp359.out
    exact hp4883191.out
  a := [-6282559409, -85671704646, 72183212870, 240017388412, -127922473470, -157896819476, 73158111976, 29367331896, -13117309840]
  b := [-4529493840, 9388934027, 38118589099, -30348324490, -51012228610, 27263333330, 22143216314, -10026001832, -3067906288, 1311730984]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 359 T_ofList CD359
    exact satisfiesDedekindCriterion_of_certificate_lists T l 4883191 T_ofList CD4883191

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

end VoightMaximalOrderD10R473

end TraceEuclidean
