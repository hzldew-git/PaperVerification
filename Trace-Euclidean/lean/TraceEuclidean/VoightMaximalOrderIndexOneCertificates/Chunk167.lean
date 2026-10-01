import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk163
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

namespace VoightMaximalOrderD10R4

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨645863308453, [-1, 3, 23, 14, -43, -31, 29, 15, -9, -2, 1], 1⟩
local notation "l" => [-1, 3, 23, 14, -43, -31, 29, 15, -9, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -23, -14, 43, 31, -29, -15, 9, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -23, -14, 43, 31, -29, -15, 9, 2], ![2, -5, -49, -51, 72, 105, -27, -59, 3, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -23, -14, 43, 31, -29, -15, 9, 2], ![2, -5, -49, -51, 72, 105, -27, -59, 3, 13], ![13, -37, -304, -231, 508, 475, -272, -222, 58, 29]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -23, -14, 43, 31, -29, -15, 9, 2], ![2, -5, -49, -51, 72, 105, -27, -59, 3, 13], ![13, -37, -304, -231, 508, 475, -272, -222, 58, 29], ![29, -74, -704, -710, 1016, 1407, -366, -707, 39, 116]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -23, -14, 43, 31, -29, -15, 9, 2], ![2, -5, -49, -51, 72, 105, -27, -59, 3, 13], ![13, -37, -304, -231, 508, 475, -272, -222, 58, 29], ![29, -74, -704, -710, 1016, 1407, -366, -707, 39, 116], ![116, -319, -2742, -2328, 4278, 4612, -1957, -2106, 337, 271]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -23, -14, 43, 31, -29, -15, 9, 2], ![2, -5, -49, -51, 72, 105, -27, -59, 3, 13], ![13, -37, -304, -231, 508, 475, -272, -222, 58, 29], ![29, -74, -704, -710, 1016, 1407, -366, -707, 39, 116], ![116, -319, -2742, -2328, 4278, 4612, -1957, -2106, 337, 271], ![271, -697, -6552, -6536, 9325, 12679, -3247, -6022, 333, 879]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -23, -14, 43, 31, -29, -15, 9, 2], ![2, -5, -49, -51, 72, 105, -27, -59, 3, 13], ![13, -37, -304, -231, 508, 475, -272, -222, 58, 29], ![29, -74, -704, -710, 1016, 1407, -366, -707, 39, 116], ![116, -319, -2742, -2328, 4278, 4612, -1957, -2106, 337, 271], ![271, -697, -6552, -6536, 9325, 12679, -3247, -6022, 333, 879], ![879, -2366, -20914, -18858, 31261, 36574, -12812, -16432, 1889, 2091]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -23, -14, 43, 31, -29, -15, 9, 2], ![2, -5, -49, -51, 72, 105, -27, -59, 3, 13], ![13, -37, -304, -231, 508, 475, -272, -222, 58, 29], ![29, -74, -704, -710, 1016, 1407, -366, -707, 39, 116], ![116, -319, -2742, -2328, 4278, 4612, -1957, -2106, 337, 271], ![271, -697, -6552, -6536, 9325, 12679, -3247, -6022, 333, 879], ![879, -2366, -20914, -18858, 31261, 36574, -12812, -16432, 1889, 2091], ![2091, -5394, -50459, -50188, 71055, 96082, -24065, -44177, 2387, 6071]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -23, -14, 43, 31, -29, -15, 9, 2], ![2, -5, -49, -51, 72, 105, -27, -59, 3, 13], ![13, -37, -304, -231, 508, 475, -272, -222, 58, 29], ![29, -74, -704, -710, 1016, 1407, -366, -707, 39, 116], ![116, -319, -2742, -2328, 4278, 4612, -1957, -2106, 337, 271], ![271, -697, -6552, -6536, 9325, 12679, -3247, -6022, 333, 879], ![879, -2366, -20914, -18858, 31261, 36574, -12812, -16432, 1889, 2091], ![2091, -5394, -50459, -50188, 71055, 96082, -24065, -44177, 2387, 6071], ![6071, -16122, -145027, -135453, 210865, 259256, -79977, -115130, 10462, 14529]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-29, -13, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-29, -13, -2, -1], [-116, -29, -13, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-29, -13, -2, -1], [-116, -29, -13, -2, -1], [-271, -116, -29, -13, -2, -1]], ![[], [], [], [-1], [-2, -1], [-13, -2, -1], [-29, -13, -2, -1], [-116, -29, -13, -2, -1], [-271, -116, -29, -13, -2, -1], [-879, -271, -116, -29, -13, -2, -1]], ![[], [], [-1], [-2, -1], [-13, -2, -1], [-29, -13, -2, -1], [-116, -29, -13, -2, -1], [-271, -116, -29, -13, -2, -1], [-879, -271, -116, -29, -13, -2, -1], [-2091, -879, -271, -116, -29, -13, -2, -1]], ![[], [-1], [-2, -1], [-13, -2, -1], [-29, -13, -2, -1], [-116, -29, -13, -2, -1], [-271, -116, -29, -13, -2, -1], [-879, -271, -116, -29, -13, -2, -1], [-2091, -879, -271, -116, -29, -13, -2, -1], [-6071, -2091, -879, -271, -116, -29, -13, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -23, -14, 43, 31, -29, -15, 9, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -23, -14, 43, 31, -29, -15, 9, 2], [2, -5, -49, -51, 72, 105, -27, -59, 3, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -23, -14, 43, 31, -29, -15, 9, 2], [2, -5, -49, -51, 72, 105, -27, -59, 3, 13], [13, -37, -304, -231, 508, 475, -272, -222, 58, 29]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -23, -14, 43, 31, -29, -15, 9, 2], [2, -5, -49, -51, 72, 105, -27, -59, 3, 13], [13, -37, -304, -231, 508, 475, -272, -222, 58, 29], [29, -74, -704, -710, 1016, 1407, -366, -707, 39, 116]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -23, -14, 43, 31, -29, -15, 9, 2], [2, -5, -49, -51, 72, 105, -27, -59, 3, 13], [13, -37, -304, -231, 508, 475, -272, -222, 58, 29], [29, -74, -704, -710, 1016, 1407, -366, -707, 39, 116], [116, -319, -2742, -2328, 4278, 4612, -1957, -2106, 337, 271]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -23, -14, 43, 31, -29, -15, 9, 2], [2, -5, -49, -51, 72, 105, -27, -59, 3, 13], [13, -37, -304, -231, 508, 475, -272, -222, 58, 29], [29, -74, -704, -710, 1016, 1407, -366, -707, 39, 116], [116, -319, -2742, -2328, 4278, 4612, -1957, -2106, 337, 271], [271, -697, -6552, -6536, 9325, 12679, -3247, -6022, 333, 879]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -23, -14, 43, 31, -29, -15, 9, 2], [2, -5, -49, -51, 72, 105, -27, -59, 3, 13], [13, -37, -304, -231, 508, 475, -272, -222, 58, 29], [29, -74, -704, -710, 1016, 1407, -366, -707, 39, 116], [116, -319, -2742, -2328, 4278, 4612, -1957, -2106, 337, 271], [271, -697, -6552, -6536, 9325, 12679, -3247, -6022, 333, 879], [879, -2366, -20914, -18858, 31261, 36574, -12812, -16432, 1889, 2091]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -23, -14, 43, 31, -29, -15, 9, 2], [2, -5, -49, -51, 72, 105, -27, -59, 3, 13], [13, -37, -304, -231, 508, 475, -272, -222, 58, 29], [29, -74, -704, -710, 1016, 1407, -366, -707, 39, 116], [116, -319, -2742, -2328, 4278, 4612, -1957, -2106, 337, 271], [271, -697, -6552, -6536, 9325, 12679, -3247, -6022, 333, 879], [879, -2366, -20914, -18858, 31261, 36574, -12812, -16432, 1889, 2091], [2091, -5394, -50459, -50188, 71055, 96082, -24065, -44177, 2387, 6071]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -23, -14, 43, 31, -29, -15, 9, 2], [2, -5, -49, -51, 72, 105, -27, -59, 3, 13], [13, -37, -304, -231, 508, 475, -272, -222, 58, 29], [29, -74, -704, -710, 1016, 1407, -366, -707, 39, 116], [116, -319, -2742, -2328, 4278, 4612, -1957, -2106, 337, 271], [271, -697, -6552, -6536, 9325, 12679, -3247, -6022, 333, 879], [879, -2366, -20914, -18858, 31261, 36574, -12812, -16432, 1889, 2091], [2091, -5394, -50459, -50188, 71055, 96082, -24065, -44177, 2387, 6071], [6071, -16122, -145027, -135453, 210865, 259256, -79977, -115130, 10462, 14529]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp23 : Fact (Nat.Prime 23) := fact_iff.2 (by norm_num)
instance hp131 : Fact (Nat.Prime 131) := fact_iff.2 (by norm_num)

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 5
  a' := [3]
  b' := [8, 4]
  k := [1]
  f := [3, 7, 7, 6, 13, 8, 4, 5, 4, 1]
  g := [8, 4, 1]
  h := [4, 8, 8, 5, 9, 2, 7, 5, 1]
  a := [2, 4]
  b := [9, 6, 3, 1, 8, 8, 1, 9, 7]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD23 : CertificateDedekindCriterionLists l 23 where
  n := 2
  a' := [4, 4, 8, 2, 9, 5, 5, 13]
  b' := [0, 10, 18, 20, 4, 12, 14, 19, 19]
  k := [10, 21, 7, 16, 2, 11, 0, 6, 1]
  f := [5, 15, 13, 10, 9, 5, 8, 18, 3, 1]
  g := [6, 18, 16, 12, 8, 4, 11, 22, 2, 1]
  h := [19, 1]
  a := [1, 19, 1, 11, 4, 14, 21, 13, 19]
  b := [7, 22, 22, 10, 18, 14, 11, 14, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD131 : CertificateDedekindCriterionLists l 131 where
  n := 2
  a' := [110, 8, 94, 93, 5, 66, 127, 23]
  b' := [47, 0, 23, 69, 100, 62, 92, 52, 12]
  k := [29, 112, 12, 83, 55, 38, 30, 123, 1]
  f := [2, 3, 1, 3, 4, 2, 3, 1, 3, 1]
  g := [87, 103, 17, 130, 117, 38, 128, 6, 126, 1]
  h := [3, 1]
  a := [117, 1, 69, 120, 42, 76, 92, 87, 57]
  b := [44, 114, 123, 105, 49, 90, 99, 112, 74]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![11, 23, 131]
  exp := ![1, 1, 1]
  pdgood := [11, 23, 131]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp11.out
    exact hp23.out
    exact hp131.out
  a := [-2068142, -28495926, 9974459, 103289272, -33446024, -73180120, 26831324, 12899896, -5066220]
  b := [-678333, 2970606, 11623871, -6136871, -20939146, 7051344, 10221533, -3519438, -1391314, 506622]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 23 T_ofList CD23
    exact satisfiesDedekindCriterion_of_certificate_lists T l 131 T_ofList CD131

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

end VoightMaximalOrderD10R4

namespace VoightMaximalOrderD10R7

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨782566688557, [-1, -4, 11, 29, -20, -40, 15, 19, -6, -3, 1], 1⟩
local notation "l" => [-1, -4, 11, 29, -20, -40, 15, 19, -6, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -11, -29, 20, 40, -15, -19, 6, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -11, -29, 20, 40, -15, -19, 6, 3], ![3, 13, -29, -98, 31, 140, -5, -72, -1, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -11, -29, 20, 40, -15, -19, 6, 3], ![3, 13, -29, -98, 31, 140, -5, -72, -1, 15], ![15, 63, -152, -464, 202, 631, -85, -290, 18, 44]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -11, -29, 20, 40, -15, -19, 6, 3], ![3, 13, -29, -98, 31, 140, -5, -72, -1, 15], ![15, 63, -152, -464, 202, 631, -85, -290, 18, 44], ![44, 191, -421, -1428, 416, 1962, -29, -921, -26, 150]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -11, -29, 20, 40, -15, -19, 6, 3], ![3, 13, -29, -98, 31, 140, -5, -72, -1, 15], ![15, 63, -152, -464, 202, 631, -85, -290, 18, 44], ![44, 191, -421, -1428, 416, 1962, -29, -921, -26, 150], ![150, 644, -1459, -4771, 1572, 6416, -288, -2879, -21, 424]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -11, -29, 20, 40, -15, -19, 6, 3], ![3, 13, -29, -98, 31, 140, -5, -72, -1, 15], ![15, 63, -152, -464, 202, 631, -85, -290, 18, 44], ![44, 191, -421, -1428, 416, 1962, -29, -921, -26, 150], ![150, 644, -1459, -4771, 1572, 6416, -288, -2879, -21, 424], ![424, 1846, -4020, -13755, 3709, 18532, 56, -8344, -335, 1251]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -11, -29, 20, 40, -15, -19, 6, 3], ![3, 13, -29, -98, 31, 140, -5, -72, -1, 15], ![15, 63, -152, -464, 202, 631, -85, -290, 18, 44], ![44, 191, -421, -1428, 416, 1962, -29, -921, -26, 150], ![150, 644, -1459, -4771, 1572, 6416, -288, -2879, -21, 424], ![424, 1846, -4020, -13755, 3709, 18532, 56, -8344, -335, 1251], ![1251, 5428, -11915, -40299, 11265, 53749, -233, -23713, -838, 3418]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -11, -29, 20, 40, -15, -19, 6, 3], ![3, 13, -29, -98, 31, 140, -5, -72, -1, 15], ![15, 63, -152, -464, 202, 631, -85, -290, 18, 44], ![44, 191, -421, -1428, 416, 1962, -29, -921, -26, 150], ![150, 644, -1459, -4771, 1572, 6416, -288, -2879, -21, 424], ![424, 1846, -4020, -13755, 3709, 18532, 56, -8344, -335, 1251], ![1251, 5428, -11915, -40299, 11265, 53749, -233, -23713, -838, 3418], ![3418, 14923, -32170, -111037, 28061, 147985, 2479, -65175, -3205, 9416]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -11, -29, 20, 40, -15, -19, 6, 3], ![3, 13, -29, -98, 31, 140, -5, -72, -1, 15], ![15, 63, -152, -464, 202, 631, -85, -290, 18, 44], ![44, 191, -421, -1428, 416, 1962, -29, -921, -26, 150], ![150, 644, -1459, -4771, 1572, 6416, -288, -2879, -21, 424], ![424, 1846, -4020, -13755, 3709, 18532, 56, -8344, -335, 1251], ![1251, 5428, -11915, -40299, 11265, 53749, -233, -23713, -838, 3418], ![3418, 14923, -32170, -111037, 28061, 147985, 2479, -65175, -3205, 9416], ![9416, 41082, -88653, -305234, 77283, 404701, 6745, -176425, -8679, 25043]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1], [-150, -44, -15, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1], [-150, -44, -15, -3, -1], [-424, -150, -44, -15, -3, -1]], ![[], [], [], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1], [-150, -44, -15, -3, -1], [-424, -150, -44, -15, -3, -1], [-1251, -424, -150, -44, -15, -3, -1]], ![[], [], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1], [-150, -44, -15, -3, -1], [-424, -150, -44, -15, -3, -1], [-1251, -424, -150, -44, -15, -3, -1], [-3418, -1251, -424, -150, -44, -15, -3, -1]], ![[], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1], [-150, -44, -15, -3, -1], [-424, -150, -44, -15, -3, -1], [-1251, -424, -150, -44, -15, -3, -1], [-3418, -1251, -424, -150, -44, -15, -3, -1], [-9416, -3418, -1251, -424, -150, -44, -15, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -11, -29, 20, 40, -15, -19, 6, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -11, -29, 20, 40, -15, -19, 6, 3], [3, 13, -29, -98, 31, 140, -5, -72, -1, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -11, -29, 20, 40, -15, -19, 6, 3], [3, 13, -29, -98, 31, 140, -5, -72, -1, 15], [15, 63, -152, -464, 202, 631, -85, -290, 18, 44]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -11, -29, 20, 40, -15, -19, 6, 3], [3, 13, -29, -98, 31, 140, -5, -72, -1, 15], [15, 63, -152, -464, 202, 631, -85, -290, 18, 44], [44, 191, -421, -1428, 416, 1962, -29, -921, -26, 150]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -11, -29, 20, 40, -15, -19, 6, 3], [3, 13, -29, -98, 31, 140, -5, -72, -1, 15], [15, 63, -152, -464, 202, 631, -85, -290, 18, 44], [44, 191, -421, -1428, 416, 1962, -29, -921, -26, 150], [150, 644, -1459, -4771, 1572, 6416, -288, -2879, -21, 424]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -11, -29, 20, 40, -15, -19, 6, 3], [3, 13, -29, -98, 31, 140, -5, -72, -1, 15], [15, 63, -152, -464, 202, 631, -85, -290, 18, 44], [44, 191, -421, -1428, 416, 1962, -29, -921, -26, 150], [150, 644, -1459, -4771, 1572, 6416, -288, -2879, -21, 424], [424, 1846, -4020, -13755, 3709, 18532, 56, -8344, -335, 1251]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -11, -29, 20, 40, -15, -19, 6, 3], [3, 13, -29, -98, 31, 140, -5, -72, -1, 15], [15, 63, -152, -464, 202, 631, -85, -290, 18, 44], [44, 191, -421, -1428, 416, 1962, -29, -921, -26, 150], [150, 644, -1459, -4771, 1572, 6416, -288, -2879, -21, 424], [424, 1846, -4020, -13755, 3709, 18532, 56, -8344, -335, 1251], [1251, 5428, -11915, -40299, 11265, 53749, -233, -23713, -838, 3418]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -11, -29, 20, 40, -15, -19, 6, 3], [3, 13, -29, -98, 31, 140, -5, -72, -1, 15], [15, 63, -152, -464, 202, 631, -85, -290, 18, 44], [44, 191, -421, -1428, 416, 1962, -29, -921, -26, 150], [150, 644, -1459, -4771, 1572, 6416, -288, -2879, -21, 424], [424, 1846, -4020, -13755, 3709, 18532, 56, -8344, -335, 1251], [1251, 5428, -11915, -40299, 11265, 53749, -233, -23713, -838, 3418], [3418, 14923, -32170, -111037, 28061, 147985, 2479, -65175, -3205, 9416]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -11, -29, 20, 40, -15, -19, 6, 3], [3, 13, -29, -98, 31, 140, -5, -72, -1, 15], [15, 63, -152, -464, 202, 631, -85, -290, 18, 44], [44, 191, -421, -1428, 416, 1962, -29, -921, -26, 150], [150, 644, -1459, -4771, 1572, 6416, -288, -2879, -21, 424], [424, 1846, -4020, -13755, 3709, 18532, 56, -8344, -335, 1251], [1251, 5428, -11915, -40299, 11265, 53749, -233, -23713, -838, 3418], [3418, 14923, -32170, -111037, 28061, 147985, 2479, -65175, -3205, 9416], [9416, 41082, -88653, -305234, 77283, 404701, 6745, -176425, -8679, 25043]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp17 : Fact (Nat.Prime 17) := fact_iff.2 (by norm_num)
instance hp157 : Fact (Nat.Prime 157) := fact_iff.2 (by norm_num)
instance hp4153 : Fact (Nat.Prime 4153) := fact_iff.2 (by norm_num)

def CD17 : CertificateDedekindCriterionLists l 17 where
  n := 2
  a' := [9, 2, 2, 1, 9, 15, 5]
  b' := [5, 14, 14, 8, 2, 6, 15, 10]
  k := [4, 14, 0, 2, 15, 13, 1]
  f := [1, 6, 8, 5, 4, 11, 7, 8, 4, 1]
  g := [8, 13, 11, 1, 14, 10, 15, 5, 1]
  h := [2, 9, 1]
  a := [12, 3, 11, 14, 10, 6, 0, 7]
  b := [5, 8, 7, 16, 9, 12, 8, 7, 10]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD157 : CertificateDedekindCriterionLists l 157 where
  n := 2
  a' := [78, 153, 117, 78, 83, 100, 85, 81]
  b' := [148, 93, 152, 102, 98, 63, 16, 69, 148]
  k := [82, 22, 153, 0, 56, 111, 72, 38, 1]
  f := [17, 38, 39, 57, 41, 22, 18, 29, 36, 1]
  g := [46, 102, 104, 153, 108, 57, 48, 78, 96, 1]
  h := [58, 1]
  a := [147, 97, 76, 4, 109, 19, 68, 58, 102]
  b := [130, 63, 81, 91, 79, 133, 63, 96, 55]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD4153 : CertificateDedekindCriterionLists l 4153 where
  n := 2
  a' := [2768, 3598, 3976, 4044, 3014, 3296, 2945]
  b' := [2581, 1082, 3700, 442, 3887, 1409, 2161, 151]
  k := [569, 1731, 570, 2510, 2281, 3301, 1]
  f := [388, 2913, 3463, 3508, 4761, 2837, 1082, 1733, 994, 1]
  g := [523, 3502, 1825, 3246, 3782, 753, 846, 1649, 1]
  h := [3081, 2501, 1]
  a := [640, 3076, 1737, 1111, 914, 1440, 2891, 3738]
  b := [1026, 3125, 3720, 2670, 579, 1582, 3020, 3535, 415]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![17, 157, 4153]
  exp := ![1, 1, 1]
  pdgood := [17, 157, 4153]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp17.out
    exact hp157.out
    exact hp4153.out
  a := [4108899, -102978276, -19523603, 318723392, 2722903, -269886174, 43443788, 67916182, -20128660]
  b := [-3798314, 744943, 40642506, 2144587, -69444448, 2635205, 39594069, -6352754, -7395478, 2012866]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 17 T_ofList CD17
    exact satisfiesDedekindCriterion_of_certificate_lists T l 157 T_ofList CD157
    exact satisfiesDedekindCriterion_of_certificate_lists T l 4153 T_ofList CD4153

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

end VoightMaximalOrderD10R7

namespace VoightMaximalOrderD10R9

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨822624971833, [-1, 3, 12, -10, -32, 10, 29, -3, -10, 0, 1], 1⟩
local notation "l" => [-1, 3, 12, -10, -32, 10, 29, -3, -10, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -12, 10, 32, -10, -29, 3, 10, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -12, 10, 32, -10, -29, 3, 10, 0], ![0, 1, -3, -12, 10, 32, -10, -29, 3, 10]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -12, 10, 32, -10, -29, 3, 10, 0], ![0, 1, -3, -12, 10, 32, -10, -29, 3, 10], ![10, -30, -119, 97, 308, -90, -258, 20, 71, 3]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -12, 10, 32, -10, -29, 3, 10, 0], ![0, 1, -3, -12, 10, 32, -10, -29, 3, 10], ![10, -30, -119, 97, 308, -90, -258, 20, 71, 3], ![3, 1, -66, -89, 193, 278, -177, -249, 50, 71]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -12, 10, 32, -10, -29, 3, 10, 0], ![0, 1, -3, -12, 10, 32, -10, -29, 3, 10], ![10, -30, -119, 97, 308, -90, -258, 20, 71, 3], ![3, 1, -66, -89, 193, 278, -177, -249, 50, 71], ![71, -210, -851, 644, 2183, -517, -1781, 36, 461, 50]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -12, 10, 32, -10, -29, 3, 10, 0], ![0, 1, -3, -12, 10, 32, -10, -29, 3, 10], ![10, -30, -119, 97, 308, -90, -258, 20, 71, 3], ![3, 1, -66, -89, 193, 278, -177, -249, 50, 71], ![71, -210, -851, 644, 2183, -517, -1781, 36, 461, 50], ![50, -79, -810, -351, 2244, 1683, -1967, -1631, 536, 461]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -12, 10, 32, -10, -29, 3, 10, 0], ![0, 1, -3, -12, 10, 32, -10, -29, 3, 10], ![10, -30, -119, 97, 308, -90, -258, 20, 71, 3], ![3, 1, -66, -89, 193, 278, -177, -249, 50, 71], ![71, -210, -851, 644, 2183, -517, -1781, 36, 461, 50], ![50, -79, -810, -351, 2244, 1683, -1967, -1631, 536, 461], ![461, -1333, -5611, 3800, 14401, -2366, -11686, -584, 2979, 536]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -12, 10, 32, -10, -29, 3, 10, 0], ![0, 1, -3, -12, 10, 32, -10, -29, 3, 10], ![10, -30, -119, 97, 308, -90, -258, 20, 71, 3], ![3, 1, -66, -89, 193, 278, -177, -249, 50, 71], ![71, -210, -851, 644, 2183, -517, -1781, 36, 461, 50], ![50, -79, -810, -351, 2244, 1683, -1967, -1631, 536, 461], ![461, -1333, -5611, 3800, 14401, -2366, -11686, -584, 2979, 536], ![536, -1147, -7765, -251, 20952, 9041, -17910, -10078, 4776, 2979]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -12, 10, 32, -10, -29, 3, 10, 0], ![0, 1, -3, -12, 10, 32, -10, -29, 3, 10], ![10, -30, -119, 97, 308, -90, -258, 20, 71, 3], ![3, 1, -66, -89, 193, 278, -177, -249, 50, 71], ![71, -210, -851, 644, 2183, -517, -1781, 36, 461, 50], ![50, -79, -810, -351, 2244, 1683, -1967, -1631, 536, 461], ![461, -1333, -5611, 3800, 14401, -2366, -11686, -584, 2979, 536], ![536, -1147, -7765, -251, 20952, 9041, -17910, -10078, 4776, 2979], ![2979, -8401, -36895, 22025, 95077, -8838, -77350, -8973, 19712, 4776]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-10, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-10, 0, -1], [-3, -10, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-10, 0, -1], [-3, -10, 0, -1], [-71, -3, -10, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-10, 0, -1], [-3, -10, 0, -1], [-71, -3, -10, 0, -1], [-50, -71, -3, -10, 0, -1]], ![[], [], [], [-1], [0, -1], [-10, 0, -1], [-3, -10, 0, -1], [-71, -3, -10, 0, -1], [-50, -71, -3, -10, 0, -1], [-461, -50, -71, -3, -10, 0, -1]], ![[], [], [-1], [0, -1], [-10, 0, -1], [-3, -10, 0, -1], [-71, -3, -10, 0, -1], [-50, -71, -3, -10, 0, -1], [-461, -50, -71, -3, -10, 0, -1], [-536, -461, -50, -71, -3, -10, 0, -1]], ![[], [-1], [0, -1], [-10, 0, -1], [-3, -10, 0, -1], [-71, -3, -10, 0, -1], [-50, -71, -3, -10, 0, -1], [-461, -50, -71, -3, -10, 0, -1], [-536, -461, -50, -71, -3, -10, 0, -1], [-2979, -536, -461, -50, -71, -3, -10, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -12, 10, 32, -10, -29, 3, 10, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -12, 10, 32, -10, -29, 3, 10, 0], [0, 1, -3, -12, 10, 32, -10, -29, 3, 10]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -12, 10, 32, -10, -29, 3, 10, 0], [0, 1, -3, -12, 10, 32, -10, -29, 3, 10], [10, -30, -119, 97, 308, -90, -258, 20, 71, 3]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -12, 10, 32, -10, -29, 3, 10, 0], [0, 1, -3, -12, 10, 32, -10, -29, 3, 10], [10, -30, -119, 97, 308, -90, -258, 20, 71, 3], [3, 1, -66, -89, 193, 278, -177, -249, 50, 71]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -12, 10, 32, -10, -29, 3, 10, 0], [0, 1, -3, -12, 10, 32, -10, -29, 3, 10], [10, -30, -119, 97, 308, -90, -258, 20, 71, 3], [3, 1, -66, -89, 193, 278, -177, -249, 50, 71], [71, -210, -851, 644, 2183, -517, -1781, 36, 461, 50]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -12, 10, 32, -10, -29, 3, 10, 0], [0, 1, -3, -12, 10, 32, -10, -29, 3, 10], [10, -30, -119, 97, 308, -90, -258, 20, 71, 3], [3, 1, -66, -89, 193, 278, -177, -249, 50, 71], [71, -210, -851, 644, 2183, -517, -1781, 36, 461, 50], [50, -79, -810, -351, 2244, 1683, -1967, -1631, 536, 461]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -12, 10, 32, -10, -29, 3, 10, 0], [0, 1, -3, -12, 10, 32, -10, -29, 3, 10], [10, -30, -119, 97, 308, -90, -258, 20, 71, 3], [3, 1, -66, -89, 193, 278, -177, -249, 50, 71], [71, -210, -851, 644, 2183, -517, -1781, 36, 461, 50], [50, -79, -810, -351, 2244, 1683, -1967, -1631, 536, 461], [461, -1333, -5611, 3800, 14401, -2366, -11686, -584, 2979, 536]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -12, 10, 32, -10, -29, 3, 10, 0], [0, 1, -3, -12, 10, 32, -10, -29, 3, 10], [10, -30, -119, 97, 308, -90, -258, 20, 71, 3], [3, 1, -66, -89, 193, 278, -177, -249, 50, 71], [71, -210, -851, 644, 2183, -517, -1781, 36, 461, 50], [50, -79, -810, -351, 2244, 1683, -1967, -1631, 536, 461], [461, -1333, -5611, 3800, 14401, -2366, -11686, -584, 2979, 536], [536, -1147, -7765, -251, 20952, 9041, -17910, -10078, 4776, 2979]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -12, 10, 32, -10, -29, 3, 10, 0], [0, 1, -3, -12, 10, 32, -10, -29, 3, 10], [10, -30, -119, 97, 308, -90, -258, 20, 71, 3], [3, 1, -66, -89, 193, 278, -177, -249, 50, 71], [71, -210, -851, 644, 2183, -517, -1781, 36, 461, 50], [50, -79, -810, -351, 2244, 1683, -1967, -1631, 536, 461], [461, -1333, -5611, 3800, 14401, -2366, -11686, -584, 2979, 536], [536, -1147, -7765, -251, 20952, 9041, -17910, -10078, 4776, 2979], [2979, -8401, -36895, 22025, 95077, -8838, -77350, -8973, 19712, 4776]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp79 : Fact (Nat.Prime 79) := fact_iff.2 (by norm_num)
instance hp38569 : Fact (Nat.Prime 38569) := fact_iff.2 (by norm_num)

def CD7 : CertificateDedekindCriterionLists l 7 where
  n := 2
  a' := [5, 1, 2, 3, 3, 6, 1, 4]
  b' := [5, 0, 4, 3, 3, 6, 1, 5, 5]
  k := [5, 1, 6, 0, 1, 5, 2, 3, 1]
  f := [1, 0, 0, 4, 6, 0, -3, 1, 3, 1]
  g := [3, 0, 6, 6, 2, 4, 2, 1, 5, 1]
  h := [2, 1]
  a := [6, 1, 4, 3, 0, 0, 1, 1, 5]
  b := [3, 2, 2, 2, 0, 5, 0, 2, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD79 : CertificateDedekindCriterionLists l 79 where
  n := 2
  a' := [28, 67, 67, 24, 12, 3, 60, 52]
  b' := [17, 76, 36, 2, 33, 62, 74, 51, 3]
  k := [33, 16, 21, 55, 71, 4, 33, 30, 1]
  f := [47, 25, 14, 53, 15, 9, 50, 47, 13, 1]
  g := [58, 30, 17, 65, 17, 11, 62, 57, 15, 1]
  h := [64, 1]
  a := [25, 35, 2, 43, 57, 43, 55, 2, 51]
  b := [7, 9, 55, 33, 24, 13, 35, 21, 28]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD38569 : CertificateDedekindCriterionLists l 38569 where
  n := 2
  a' := [5756, 1703, 13336, 31013, 15307, 7171, 5215]
  b' := [26508, 27918, 9326, 20905, 4567, 33359, 17061, 33096]
  k := [8558, 12849, 12674, 11272, 2048, 16466, 1]
  f := [1069, 17301, 42136, 29281, 7264, 7565, 20209, 29708, 6477, 1]
  g := [1732, 25824, 35360, 2379, 8736, 1124, 31310, 8233, 1]
  h := [23805, 30336, 1]
  a := [28206, 26530, 23035, 35074, 22687, 18323, 20649, 11099]
  b := [20737, 19768, 11133, 28578, 23886, 914, 23144, 30419, 27470]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![7, 79, 38569]
  exp := ![1, 1, 1]
  pdgood := [7, 79, 38569]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp7.out
    exact hp79.out
    exact hp38569.out
  a := [-140876800, -754677186, 2739851973, 1129722850, -4481920688, -626371734, 2206961940, 163983040, -291818760]
  b := [-39849381, 208112786, 168072279, -777848907, -154231526, 775942676, 69170093, -279059946, -16398304, 29181876]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T l 79 T_ofList CD79
    exact satisfiesDedekindCriterion_of_certificate_lists T l 38569 T_ofList CD38569

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

end VoightMaximalOrderD10R9

namespace VoightMaximalOrderD10R10

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨823301450757, [1, -1, -18, 27, 27, -46, -8, 25, -3, -4, 1], 1⟩
local notation "l" => [1, -1, -18, 27, 27, -46, -8, 25, -3, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 18, -27, -27, 46, 8, -25, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 18, -27, -27, 46, 8, -25, 3, 4], ![-4, 3, 73, -90, -135, 157, 78, -92, -13, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 18, -27, -27, 46, 8, -25, 3, 4], ![-4, 3, 73, -90, -135, 157, 78, -92, -13, 19], ![-19, 15, 345, -440, -603, 739, 309, -397, -35, 63]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 18, -27, -27, 46, 8, -25, 3, 4], ![-4, 3, 73, -90, -135, 157, 78, -92, -13, 19], ![-19, 15, 345, -440, -603, 739, 309, -397, -35, 63], ![-63, 44, 1149, -1356, -2141, 2295, 1243, -1266, -208, 217]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 18, -27, -27, 46, 8, -25, 3, 4], ![-4, 3, 73, -90, -135, 157, 78, -92, -13, 19], ![-19, 15, 345, -440, -603, 739, 309, -397, -35, 63], ![-63, 44, 1149, -1356, -2141, 2295, 1243, -1266, -208, 217], ![-217, 154, 3950, -4710, -7215, 7841, 4031, -4182, -615, 660]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 18, -27, -27, 46, 8, -25, 3, 4], ![-4, 3, 73, -90, -135, 157, 78, -92, -13, 19], ![-19, 15, 345, -440, -603, 739, 309, -397, -35, 63], ![-63, 44, 1149, -1356, -2141, 2295, 1243, -1266, -208, 217], ![-217, 154, 3950, -4710, -7215, 7841, 4031, -4182, -615, 660], ![-660, 443, 12034, -13870, -22530, 23145, 13121, -12469, -2202, 2025]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 18, -27, -27, 46, 8, -25, 3, 4], ![-4, 3, 73, -90, -135, 157, 78, -92, -13, 19], ![-19, 15, 345, -440, -603, 739, 309, -397, -35, 63], ![-63, 44, 1149, -1356, -2141, 2295, 1243, -1266, -208, 217], ![-217, 154, 3950, -4710, -7215, 7841, 4031, -4182, -615, 660], ![-660, 443, 12034, -13870, -22530, 23145, 13121, -12469, -2202, 2025], ![-2025, 1365, 36893, -42641, -68545, 70620, 39345, -37504, -6394, 5898]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 18, -27, -27, 46, 8, -25, 3, 4], ![-4, 3, 73, -90, -135, 157, 78, -92, -13, 19], ![-19, 15, 345, -440, -603, 739, 309, -397, -35, 63], ![-63, 44, 1149, -1356, -2141, 2295, 1243, -1266, -208, 217], ![-217, 154, 3950, -4710, -7215, 7841, 4031, -4182, -615, 660], ![-660, 443, 12034, -13870, -22530, 23145, 13121, -12469, -2202, 2025], ![-2025, 1365, 36893, -42641, -68545, 70620, 39345, -37504, -6394, 5898], ![-5898, 3873, 107529, -122353, -201887, 202763, 117804, -108105, -19810, 17198]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 18, -27, -27, 46, 8, -25, 3, 4], ![-4, 3, 73, -90, -135, 157, 78, -92, -13, 19], ![-19, 15, 345, -440, -603, 739, 309, -397, -35, 63], ![-63, 44, 1149, -1356, -2141, 2295, 1243, -1266, -208, 217], ![-217, 154, 3950, -4710, -7215, 7841, 4031, -4182, -615, 660], ![-660, 443, 12034, -13870, -22530, 23145, 13121, -12469, -2202, 2025], ![-2025, 1365, 36893, -42641, -68545, 70620, 39345, -37504, -6394, 5898], ![-5898, 3873, 107529, -122353, -201887, 202763, 117804, -108105, -19810, 17198], ![-17198, 11300, 313437, -356817, -586699, 589221, 340347, -312146, -56511, 48982]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-63, -19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-63, -19, -4, -1], [-217, -63, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-63, -19, -4, -1], [-217, -63, -19, -4, -1], [-660, -217, -63, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-63, -19, -4, -1], [-217, -63, -19, -4, -1], [-660, -217, -63, -19, -4, -1], [-2025, -660, -217, -63, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-63, -19, -4, -1], [-217, -63, -19, -4, -1], [-660, -217, -63, -19, -4, -1], [-2025, -660, -217, -63, -19, -4, -1], [-5898, -2025, -660, -217, -63, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-63, -19, -4, -1], [-217, -63, -19, -4, -1], [-660, -217, -63, -19, -4, -1], [-2025, -660, -217, -63, -19, -4, -1], [-5898, -2025, -660, -217, -63, -19, -4, -1], [-17198, -5898, -2025, -660, -217, -63, -19, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 18, -27, -27, 46, 8, -25, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 18, -27, -27, 46, 8, -25, 3, 4], [-4, 3, 73, -90, -135, 157, 78, -92, -13, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 18, -27, -27, 46, 8, -25, 3, 4], [-4, 3, 73, -90, -135, 157, 78, -92, -13, 19], [-19, 15, 345, -440, -603, 739, 309, -397, -35, 63]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 18, -27, -27, 46, 8, -25, 3, 4], [-4, 3, 73, -90, -135, 157, 78, -92, -13, 19], [-19, 15, 345, -440, -603, 739, 309, -397, -35, 63], [-63, 44, 1149, -1356, -2141, 2295, 1243, -1266, -208, 217]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 18, -27, -27, 46, 8, -25, 3, 4], [-4, 3, 73, -90, -135, 157, 78, -92, -13, 19], [-19, 15, 345, -440, -603, 739, 309, -397, -35, 63], [-63, 44, 1149, -1356, -2141, 2295, 1243, -1266, -208, 217], [-217, 154, 3950, -4710, -7215, 7841, 4031, -4182, -615, 660]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 18, -27, -27, 46, 8, -25, 3, 4], [-4, 3, 73, -90, -135, 157, 78, -92, -13, 19], [-19, 15, 345, -440, -603, 739, 309, -397, -35, 63], [-63, 44, 1149, -1356, -2141, 2295, 1243, -1266, -208, 217], [-217, 154, 3950, -4710, -7215, 7841, 4031, -4182, -615, 660], [-660, 443, 12034, -13870, -22530, 23145, 13121, -12469, -2202, 2025]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 18, -27, -27, 46, 8, -25, 3, 4], [-4, 3, 73, -90, -135, 157, 78, -92, -13, 19], [-19, 15, 345, -440, -603, 739, 309, -397, -35, 63], [-63, 44, 1149, -1356, -2141, 2295, 1243, -1266, -208, 217], [-217, 154, 3950, -4710, -7215, 7841, 4031, -4182, -615, 660], [-660, 443, 12034, -13870, -22530, 23145, 13121, -12469, -2202, 2025], [-2025, 1365, 36893, -42641, -68545, 70620, 39345, -37504, -6394, 5898]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 18, -27, -27, 46, 8, -25, 3, 4], [-4, 3, 73, -90, -135, 157, 78, -92, -13, 19], [-19, 15, 345, -440, -603, 739, 309, -397, -35, 63], [-63, 44, 1149, -1356, -2141, 2295, 1243, -1266, -208, 217], [-217, 154, 3950, -4710, -7215, 7841, 4031, -4182, -615, 660], [-660, 443, 12034, -13870, -22530, 23145, 13121, -12469, -2202, 2025], [-2025, 1365, 36893, -42641, -68545, 70620, 39345, -37504, -6394, 5898], [-5898, 3873, 107529, -122353, -201887, 202763, 117804, -108105, -19810, 17198]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 18, -27, -27, 46, 8, -25, 3, 4], [-4, 3, 73, -90, -135, 157, 78, -92, -13, 19], [-19, 15, 345, -440, -603, 739, 309, -397, -35, 63], [-63, 44, 1149, -1356, -2141, 2295, 1243, -1266, -208, 217], [-217, 154, 3950, -4710, -7215, 7841, 4031, -4182, -615, 660], [-660, 443, 12034, -13870, -22530, 23145, 13121, -12469, -2202, 2025], [-2025, 1365, 36893, -42641, -68545, 70620, 39345, -37504, -6394, 5898], [-5898, 3873, 107529, -122353, -201887, 202763, 117804, -108105, -19810, 17198], [-17198, 11300, 313437, -356817, -586699, 589221, 340347, -312146, -56511, 48982]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp37 : Fact (Nat.Prime 37) := fact_iff.2 (by norm_num)
instance hp2617 : Fact (Nat.Prime 2617) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 2
  a' := [1, 0, 1, 1, 0, 2]
  b' := [1, 2, 2, 1, 0, 0, 2]
  k := [1, 0, 1, 0, 0, 1, 1]
  f := [1, 3, 8, -7, -7, 18, 5, -7, 2, 2]
  g := [2, 2, 0, 2, 1, 2, 1, 0, 1]
  h := [2, 2, 1]
  a := [1, 1, 2, 2, 2, 2]
  b := [0, 1, 2, 0, 1, 1, 2]
  c := [0, 0, 1]
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD19 : CertificateDedekindCriterionLists l 19 where
  n := 2
  a' := [4, 1, 1, 17, 2, 13]
  b' := [9, 10, 5, 14, 10, 11, 15]
  k := [7, 11, 4, 13, 3, 16, 1]
  f := [5, 7, 5, 8, 8, 8, 7, 6, 4, 1]
  g := [8, 5, 2, 13, 5, 4, 7, 6, 1]
  h := [12, 9, 1]
  a := [12, 8, 10, 8, 5, 3, 0, 8]
  b := [14, 9, 1, 3, 7, 13, 4, 16, 11]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD37 : CertificateDedekindCriterionLists l 37 where
  n := 2
  a' := [17, 19, 16, 22, 19, 32, 23, 6]
  b' := [13, 22, 26, 24, 12, 7, 13, 28, 24]
  k := [21, 25, 11, 15, 20, 12, 25, 30, 1]
  f := [7, 2, 13, 8, 4, 2, 17, 18, 8, 1]
  g := [13, 3, 23, 15, 8, 1, 31, 33, 13, 1]
  h := [20, 1]
  a := [14, 10, 9, 23, 7, 14, 22, 19, 15]
  b := [21, 36, 11, 28, 1, 8, 26, 19, 22]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2617 : CertificateDedekindCriterionLists l 2617 where
  n := 2
  a' := [1555, 1588, 1965, 71, 1358, 35, 2394]
  b' := [1271, 116, 1412, 1792, 1430, 1810, 491, 355]
  k := [850, 1064, 306, 1815, 1639, 1368, 1]
  f := [29, 819, 1693, 372, 728, 2066, 1706, 1029, 504, 1]
  g := [78, 2048, 489, 28, 1902, 1782, 1050, 682, 1]
  h := [973, 1931, 1]
  a := [2541, 2283, 1720, 551, 286, 871, 2098, 2305]
  b := [2142, 980, 1257, 2072, 2371, 265, 1969, 2557, 312]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![3, 19, 37, 2617]
  exp := ![1, 1, 1, 1]
  pdgood := [3, 19, 37, 2617]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp19.out
    exact hp37.out
    exact hp2617.out
  a := [-59076397, -2373159380, 3371475253, 9463032372, -7633175029, -8761819988, 4683263948, 1942154570, -863092500]
  b := [-64595650, 11360417, 1166787117, -847109395, -2363508701, 1179971345, 1390319452, -566711082, -228739157, 86309250]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19 T_ofList CD19
    exact satisfiesDedekindCriterion_of_certificate_lists T l 37 T_ofList CD37
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2617 T_ofList CD2617

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

end VoightMaximalOrderD10R10

end TraceEuclidean
