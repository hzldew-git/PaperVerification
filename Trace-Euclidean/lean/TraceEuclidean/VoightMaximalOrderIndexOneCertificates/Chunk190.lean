import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk186
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

namespace VoightMaximalOrderD10R240

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3539956128125, [5, -5, -31, 36, 42, -56, -11, 27, -3, -4, 1], 1⟩
local notation "l" => [5, -5, -31, 36, 42, -56, -11, 27, -3, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 31, -36, -42, 56, 11, -27, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 31, -36, -42, 56, 11, -27, 3, 4], ![-20, 15, 129, -113, -204, 182, 100, -97, -15, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 31, -36, -42, 56, 11, -27, 3, 4], ![-20, 15, 129, -113, -204, 182, 100, -97, -15, 19], ![-95, 75, 604, -555, -911, 860, 391, -413, -40, 61]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 31, -36, -42, 56, 11, -27, 3, 4], ![-20, 15, 129, -113, -204, 182, 100, -97, -15, 19], ![-95, 75, 604, -555, -911, 860, 391, -413, -40, 61], ![-305, 210, 1966, -1592, -3117, 2505, 1531, -1256, -230, 204]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 31, -36, -42, 56, 11, -27, 3, 4], ![-20, 15, 129, -113, -204, 182, 100, -97, -15, 19], ![-95, 75, 604, -555, -911, 860, 391, -413, -40, 61], ![-305, 210, 1966, -1592, -3117, 2505, 1531, -1256, -230, 204], ![-1020, 715, 6534, -5378, -10160, 8307, 4749, -3977, -644, 586]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 31, -36, -42, 56, 11, -27, 3, 4], ![-20, 15, 129, -113, -204, 182, 100, -97, -15, 19], ![-95, 75, 604, -555, -911, 860, 391, -413, -40, 61], ![-305, 210, 1966, -1592, -3117, 2505, 1531, -1256, -230, 204], ![-1020, 715, 6534, -5378, -10160, 8307, 4749, -3977, -644, 586], ![-2930, 1910, 18881, -14562, -29990, 22656, 14753, -11073, -2219, 1700]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 31, -36, -42, 56, 11, -27, 3, 4], ![-20, 15, 129, -113, -204, 182, 100, -97, -15, 19], ![-95, 75, 604, -555, -911, 860, 391, -413, -40, 61], ![-305, 210, 1966, -1592, -3117, 2505, 1531, -1256, -230, 204], ![-1020, 715, 6534, -5378, -10160, 8307, 4749, -3977, -644, 586], ![-2930, 1910, 18881, -14562, -29990, 22656, 14753, -11073, -2219, 1700], ![-8500, 5570, 54610, -42319, -85962, 65210, 41356, -31147, -5973, 4581]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 31, -36, -42, 56, 11, -27, 3, 4], ![-20, 15, 129, -113, -204, 182, 100, -97, -15, 19], ![-95, 75, 604, -555, -911, 860, 391, -413, -40, 61], ![-305, 210, 1966, -1592, -3117, 2505, 1531, -1256, -230, 204], ![-1020, 715, 6534, -5378, -10160, 8307, 4749, -3977, -644, 586], ![-2930, 1910, 18881, -14562, -29990, 22656, 14753, -11073, -2219, 1700], ![-8500, 5570, 54610, -42319, -85962, 65210, 41356, -31147, -5973, 4581], ![-22905, 14405, 147581, -110306, -234721, 170574, 115601, -82331, -17404, 12351]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 5, 31, -36, -42, 56, 11, -27, 3, 4], ![-20, 15, 129, -113, -204, 182, 100, -97, -15, 19], ![-95, 75, 604, -555, -911, 860, 391, -413, -40, 61], ![-305, 210, 1966, -1592, -3117, 2505, 1531, -1256, -230, 204], ![-1020, 715, 6534, -5378, -10160, 8307, 4749, -3977, -644, 586], ![-2930, 1910, 18881, -14562, -29990, 22656, 14753, -11073, -2219, 1700], ![-8500, 5570, 54610, -42319, -85962, 65210, 41356, -31147, -5973, 4581], ![-22905, 14405, 147581, -110306, -234721, 170574, 115601, -82331, -17404, 12351], ![-61755, 38850, 397286, -297055, -629048, 456935, 306435, -217876, -45278, 32000]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1], [-204, -61, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1], [-204, -61, -19, -4, -1], [-586, -204, -61, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1], [-204, -61, -19, -4, -1], [-586, -204, -61, -19, -4, -1], [-1700, -586, -204, -61, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1], [-204, -61, -19, -4, -1], [-586, -204, -61, -19, -4, -1], [-1700, -586, -204, -61, -19, -4, -1], [-4581, -1700, -586, -204, -61, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1], [-204, -61, -19, -4, -1], [-586, -204, -61, -19, -4, -1], [-1700, -586, -204, -61, -19, -4, -1], [-4581, -1700, -586, -204, -61, -19, -4, -1], [-12351, -4581, -1700, -586, -204, -61, -19, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 31, -36, -42, 56, 11, -27, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 31, -36, -42, 56, 11, -27, 3, 4], [-20, 15, 129, -113, -204, 182, 100, -97, -15, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 31, -36, -42, 56, 11, -27, 3, 4], [-20, 15, 129, -113, -204, 182, 100, -97, -15, 19], [-95, 75, 604, -555, -911, 860, 391, -413, -40, 61]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 31, -36, -42, 56, 11, -27, 3, 4], [-20, 15, 129, -113, -204, 182, 100, -97, -15, 19], [-95, 75, 604, -555, -911, 860, 391, -413, -40, 61], [-305, 210, 1966, -1592, -3117, 2505, 1531, -1256, -230, 204]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 31, -36, -42, 56, 11, -27, 3, 4], [-20, 15, 129, -113, -204, 182, 100, -97, -15, 19], [-95, 75, 604, -555, -911, 860, 391, -413, -40, 61], [-305, 210, 1966, -1592, -3117, 2505, 1531, -1256, -230, 204], [-1020, 715, 6534, -5378, -10160, 8307, 4749, -3977, -644, 586]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 31, -36, -42, 56, 11, -27, 3, 4], [-20, 15, 129, -113, -204, 182, 100, -97, -15, 19], [-95, 75, 604, -555, -911, 860, 391, -413, -40, 61], [-305, 210, 1966, -1592, -3117, 2505, 1531, -1256, -230, 204], [-1020, 715, 6534, -5378, -10160, 8307, 4749, -3977, -644, 586], [-2930, 1910, 18881, -14562, -29990, 22656, 14753, -11073, -2219, 1700]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 31, -36, -42, 56, 11, -27, 3, 4], [-20, 15, 129, -113, -204, 182, 100, -97, -15, 19], [-95, 75, 604, -555, -911, 860, 391, -413, -40, 61], [-305, 210, 1966, -1592, -3117, 2505, 1531, -1256, -230, 204], [-1020, 715, 6534, -5378, -10160, 8307, 4749, -3977, -644, 586], [-2930, 1910, 18881, -14562, -29990, 22656, 14753, -11073, -2219, 1700], [-8500, 5570, 54610, -42319, -85962, 65210, 41356, -31147, -5973, 4581]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 31, -36, -42, 56, 11, -27, 3, 4], [-20, 15, 129, -113, -204, 182, 100, -97, -15, 19], [-95, 75, 604, -555, -911, 860, 391, -413, -40, 61], [-305, 210, 1966, -1592, -3117, 2505, 1531, -1256, -230, 204], [-1020, 715, 6534, -5378, -10160, 8307, 4749, -3977, -644, 586], [-2930, 1910, 18881, -14562, -29990, 22656, 14753, -11073, -2219, 1700], [-8500, 5570, 54610, -42319, -85962, 65210, 41356, -31147, -5973, 4581], [-22905, 14405, 147581, -110306, -234721, 170574, 115601, -82331, -17404, 12351]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 5, 31, -36, -42, 56, 11, -27, 3, 4], [-20, 15, 129, -113, -204, 182, 100, -97, -15, 19], [-95, 75, 604, -555, -911, 860, 391, -413, -40, 61], [-305, 210, 1966, -1592, -3117, 2505, 1531, -1256, -230, 204], [-1020, 715, 6534, -5378, -10160, 8307, 4749, -3977, -644, 586], [-2930, 1910, 18881, -14562, -29990, 22656, 14753, -11073, -2219, 1700], [-8500, 5570, 54610, -42319, -85962, 65210, 41356, -31147, -5973, 4581], [-22905, 14405, 147581, -110306, -234721, 170574, 115601, -82331, -17404, 12351], [-61755, 38850, 397286, -297055, -629048, 456935, 306435, -217876, -45278, 32000]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp2791 : Fact (Nat.Prime 2791) := fact_iff.2 (by norm_num)
instance hp405871 : Fact (Nat.Prime 405871) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 3]
  b' := [3, 2, 4, 1]
  k := [1]
  f := [-1, 1, 7, -4, -2, 20, 11, 1, 4, 2]
  g := [0, 2, 4, 4, 3, 1]
  h := [0, 2, 4, 4, 3, 1]
  a := [4, 1, 4, 0, 2]
  b := [1, 3, 2, 4, 1, 3, 4, 4, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2791 : CertificateDedekindCriterionLists l 2791 where
  n := 2
  a' := [489, 1956, 2127, 549, 643, 2788, 517, 118]
  b' := [372, 2372, 1011, 1704, 2554, 1773, 67, 462, 297]
  k := [1387, 2419, 337, 1455, 374, 611, 342, 2413, 1]
  f := [174, 108, 84, 114, 109, 14, 25, 149, 175, 1]
  g := [2597, 1598, 1245, 1695, 1618, 200, 372, 2222, 2600, 1]
  h := [187, 1]
  a := [819, 2260, 2420, 252, 1171, 2454, 2002, 1499, 2180]
  b := [1123, 598, 623, 2752, 2671, 1935, 1595, 1638, 611]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD405871 : CertificateDedekindCriterionLists l 405871 where
  n := 2
  a' := [355048, 141389, 286000, 177759, 370268, 34581, 43046, 104436]
  b' := [165438, 193439, 200070, 387859, 303297, 237922, 262606, 113048, 394267]
  k := [164126, 35245, 55547, 67437, 319987, 225971, 288656, 366798, 1]
  f := [79105, 53403, 12058, 81832, 129991, 51829, 115546, 141173, 100526, 1]
  g := [144318, 97427, 21998, 149293, 237153, 94555, 210800, 257553, 183397, 1]
  h := [222470, 1]
  a := [26306, 235808, 340861, 379820, 281810, 196993, 91538, 193804, 14972]
  b := [390746, 318607, 171590, 346586, 225333, 59950, 116316, 209032, 390899]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 2791, 405871]
  exp := ![1, 1, 1]
  pdgood := [5, 2791, 405871]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp2791.out
    exact hp405871.out
  a := [-11258598064, -170016886312, 33196767917, 438411133724, -137165071160, -294363969826, 109727799704, 56026374000, -22565659400]
  b := [-12391384025, -5105126338, 68666633877, 169662665, -96609236013, 19894736994, 44794549815, -13335119528, -6505263776, 2256565940]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2791 T_ofList CD2791
    exact satisfiesDedekindCriterion_of_certificate_lists T l 405871 T_ofList CD405871

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

end VoightMaximalOrderD10R240

namespace VoightMaximalOrderD10R242

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3567655918981, [1, -2, -11, 20, 27, -37, -18, 24, 1, -5, 1], 1⟩
local notation "l" => [1, -2, -11, 20, 27, -37, -18, 24, 1, -5, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 11, -20, -27, 37, 18, -24, -1, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 11, -20, -27, 37, 18, -24, -1, 5], ![-5, 9, 57, -89, -155, 158, 127, -102, -29, 24]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 11, -20, -27, 37, 18, -24, -1, 5], ![-5, 9, 57, -89, -155, 158, 127, -102, -29, 24], ![-24, 43, 273, -423, -737, 733, 590, -449, -126, 91]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 11, -20, -27, 37, 18, -24, -1, 5], ![-5, 9, 57, -89, -155, 158, 127, -102, -29, 24], ![-24, 43, 273, -423, -737, 733, 590, -449, -126, 91], ![-91, 158, 1044, -1547, -2880, 2630, 2371, -1594, -540, 329]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 11, -20, -27, 37, 18, -24, -1, 5], ![-5, 9, 57, -89, -155, 158, 127, -102, -29, 24], ![-24, 43, 273, -423, -737, 733, 590, -449, -126, 91], ![-91, 158, 1044, -1547, -2880, 2630, 2371, -1594, -540, 329], ![-329, 567, 3777, -5536, -10430, 9293, 8552, -5525, -1923, 1105]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 11, -20, -27, 37, 18, -24, -1, 5], ![-5, 9, 57, -89, -155, 158, 127, -102, -29, 24], ![-24, 43, 273, -423, -737, 733, 590, -449, -126, 91], ![-91, 158, 1044, -1547, -2880, 2630, 2371, -1594, -540, 329], ![-329, 567, 3777, -5536, -10430, 9293, 8552, -5525, -1923, 1105], ![-1105, 1881, 12722, -18323, -35371, 30455, 29183, -17968, -6630, 3602]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 11, -20, -27, 37, 18, -24, -1, 5], ![-5, 9, 57, -89, -155, 158, 127, -102, -29, 24], ![-24, 43, 273, -423, -737, 733, 590, -449, -126, 91], ![-91, 158, 1044, -1547, -2880, 2630, 2371, -1594, -540, 329], ![-329, 567, 3777, -5536, -10430, 9293, 8552, -5525, -1923, 1105], ![-1105, 1881, 12722, -18323, -35371, 30455, 29183, -17968, -6630, 3602], ![-3602, 6099, 41503, -59318, -115577, 97903, 95291, -57265, -21570, 11380]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 11, -20, -27, 37, 18, -24, -1, 5], ![-5, 9, 57, -89, -155, 158, 127, -102, -29, 24], ![-24, 43, 273, -423, -737, 733, 590, -449, -126, 91], ![-91, 158, 1044, -1547, -2880, 2630, 2371, -1594, -540, 329], ![-329, 567, 3777, -5536, -10430, 9293, 8552, -5525, -1923, 1105], ![-1105, 1881, 12722, -18323, -35371, 30455, 29183, -17968, -6630, 3602], ![-3602, 6099, 41503, -59318, -115577, 97903, 95291, -57265, -21570, 11380], ![-11380, 19158, 131279, -186097, -366578, 305483, 302743, -177829, -68645, 35330]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 11, -20, -27, 37, 18, -24, -1, 5], ![-5, 9, 57, -89, -155, 158, 127, -102, -29, 24], ![-24, 43, 273, -423, -737, 733, 590, -449, -126, 91], ![-91, 158, 1044, -1547, -2880, 2630, 2371, -1594, -540, 329], ![-329, 567, 3777, -5536, -10430, 9293, 8552, -5525, -1923, 1105], ![-1105, 1881, 12722, -18323, -35371, 30455, 29183, -17968, -6630, 3602], ![-3602, 6099, 41503, -59318, -115577, 97903, 95291, -57265, -21570, 11380], ![-11380, 19158, 131279, -186097, -366578, 305483, 302743, -177829, -68645, 35330], ![-35330, 59280, 407788, -575321, -1140007, 940632, 941423, -545177, -213159, 108005]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-5, -1]], ![[], [], [], [], [], [], [], [-1], [-5, -1], [-24, -5, -1]], ![[], [], [], [], [], [], [-1], [-5, -1], [-24, -5, -1], [-91, -24, -5, -1]], ![[], [], [], [], [], [-1], [-5, -1], [-24, -5, -1], [-91, -24, -5, -1], [-329, -91, -24, -5, -1]], ![[], [], [], [], [-1], [-5, -1], [-24, -5, -1], [-91, -24, -5, -1], [-329, -91, -24, -5, -1], [-1105, -329, -91, -24, -5, -1]], ![[], [], [], [-1], [-5, -1], [-24, -5, -1], [-91, -24, -5, -1], [-329, -91, -24, -5, -1], [-1105, -329, -91, -24, -5, -1], [-3602, -1105, -329, -91, -24, -5, -1]], ![[], [], [-1], [-5, -1], [-24, -5, -1], [-91, -24, -5, -1], [-329, -91, -24, -5, -1], [-1105, -329, -91, -24, -5, -1], [-3602, -1105, -329, -91, -24, -5, -1], [-11380, -3602, -1105, -329, -91, -24, -5, -1]], ![[], [-1], [-5, -1], [-24, -5, -1], [-91, -24, -5, -1], [-329, -91, -24, -5, -1], [-1105, -329, -91, -24, -5, -1], [-3602, -1105, -329, -91, -24, -5, -1], [-11380, -3602, -1105, -329, -91, -24, -5, -1], [-35330, -11380, -3602, -1105, -329, -91, -24, -5, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 11, -20, -27, 37, 18, -24, -1, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 11, -20, -27, 37, 18, -24, -1, 5], [-5, 9, 57, -89, -155, 158, 127, -102, -29, 24]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 11, -20, -27, 37, 18, -24, -1, 5], [-5, 9, 57, -89, -155, 158, 127, -102, -29, 24], [-24, 43, 273, -423, -737, 733, 590, -449, -126, 91]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 11, -20, -27, 37, 18, -24, -1, 5], [-5, 9, 57, -89, -155, 158, 127, -102, -29, 24], [-24, 43, 273, -423, -737, 733, 590, -449, -126, 91], [-91, 158, 1044, -1547, -2880, 2630, 2371, -1594, -540, 329]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 11, -20, -27, 37, 18, -24, -1, 5], [-5, 9, 57, -89, -155, 158, 127, -102, -29, 24], [-24, 43, 273, -423, -737, 733, 590, -449, -126, 91], [-91, 158, 1044, -1547, -2880, 2630, 2371, -1594, -540, 329], [-329, 567, 3777, -5536, -10430, 9293, 8552, -5525, -1923, 1105]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 11, -20, -27, 37, 18, -24, -1, 5], [-5, 9, 57, -89, -155, 158, 127, -102, -29, 24], [-24, 43, 273, -423, -737, 733, 590, -449, -126, 91], [-91, 158, 1044, -1547, -2880, 2630, 2371, -1594, -540, 329], [-329, 567, 3777, -5536, -10430, 9293, 8552, -5525, -1923, 1105], [-1105, 1881, 12722, -18323, -35371, 30455, 29183, -17968, -6630, 3602]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 11, -20, -27, 37, 18, -24, -1, 5], [-5, 9, 57, -89, -155, 158, 127, -102, -29, 24], [-24, 43, 273, -423, -737, 733, 590, -449, -126, 91], [-91, 158, 1044, -1547, -2880, 2630, 2371, -1594, -540, 329], [-329, 567, 3777, -5536, -10430, 9293, 8552, -5525, -1923, 1105], [-1105, 1881, 12722, -18323, -35371, 30455, 29183, -17968, -6630, 3602], [-3602, 6099, 41503, -59318, -115577, 97903, 95291, -57265, -21570, 11380]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 11, -20, -27, 37, 18, -24, -1, 5], [-5, 9, 57, -89, -155, 158, 127, -102, -29, 24], [-24, 43, 273, -423, -737, 733, 590, -449, -126, 91], [-91, 158, 1044, -1547, -2880, 2630, 2371, -1594, -540, 329], [-329, 567, 3777, -5536, -10430, 9293, 8552, -5525, -1923, 1105], [-1105, 1881, 12722, -18323, -35371, 30455, 29183, -17968, -6630, 3602], [-3602, 6099, 41503, -59318, -115577, 97903, 95291, -57265, -21570, 11380], [-11380, 19158, 131279, -186097, -366578, 305483, 302743, -177829, -68645, 35330]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 11, -20, -27, 37, 18, -24, -1, 5], [-5, 9, 57, -89, -155, 158, 127, -102, -29, 24], [-24, 43, 273, -423, -737, 733, 590, -449, -126, 91], [-91, 158, 1044, -1547, -2880, 2630, 2371, -1594, -540, 329], [-329, 567, 3777, -5536, -10430, 9293, 8552, -5525, -1923, 1105], [-1105, 1881, 12722, -18323, -35371, 30455, 29183, -17968, -6630, 3602], [-3602, 6099, 41503, -59318, -115577, 97903, 95291, -57265, -21570, 11380], [-11380, 19158, 131279, -186097, -366578, 305483, 302743, -177829, -68645, 35330], [-35330, 59280, 407788, -575321, -1140007, 940632, 941423, -545177, -213159, 108005]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp229 : Fact (Nat.Prime 229) := fact_iff.2 (by norm_num)
instance hp1621 : Fact (Nat.Prime 1621) := fact_iff.2 (by norm_num)

def CD7 : CertificateDedekindCriterionLists l 7 where
  n := 2
  a' := [1, 0, 6, 3, 5, 2, 2]
  b' := [3, 3, 3, 0, 1, 2, 1, 5]
  k := [2, 3, 4, 2, 4, 2, 1]
  f := [1, 2, 3, -2, -2, 7, 5, -2, 1, 1]
  g := [4, 6, 3, 0, 5, 6, 6, 2, 1]
  h := [2, 0, 1]
  a := [2, 0, 3, 3, 0, 2, 5, 5]
  b := [5, 2, 5, 2, 0, 3, 5, 0, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [9, 10, 6, 10, 7, 0, 1]
  b' := [0, 9, 7, 0, 4, 8, 4, 4]
  k := [3, 10, 2, 4, 8, 10, 1]
  f := [4, 10, 8, 7, 5, 5, 9, 11, 8, 2]
  g := [5, 7, 1, 9, 0, 1, 8, 8, 1]
  h := [9, 9, 1]
  a := [1, 3, 3, 4, 10, 6, 5, 8]
  b := [6, 7, 1, 4, 4, 4, 7, 10, 6]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD229 : CertificateDedekindCriterionLists l 229 where
  n := 2
  a' := [14, 53, 132, 94, 193, 202, 25, 223]
  b' := [20, 94, 121, 195, 33, 181, 21, 136, 77]
  k := [203, 174, 9, 104, 189, 84, 126, 88, 1]
  f := [19, 38, 30, 63, 40, 53, 54, 47, 47, 1]
  g := [64, 127, 99, 211, 132, 176, 179, 156, 156, 1]
  h := [68, 1]
  a := [30, 8, 90, 64, 145, 201, 37, 45, 205]
  b := [9, 216, 88, 118, 184, 126, 209, 87, 24]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1621 : CertificateDedekindCriterionLists l 1621 where
  n := 2
  a' := [1175, 712, 949, 286, 773, 1006, 1043]
  b' := [719, 1614, 1202, 1258, 681, 1154, 936, 1288]
  k := [1456, 1208, 606, 179, 185, 285, 1]
  f := [359, 914, 746, 1001, 1207, 1524, 438, 170, 128, 1]
  g := [795, 421, 802, 599, 1464, 422, 117, 140, 1]
  h := [732, 1476, 1]
  a := [522, 349, 972, 597, 699, 37, 1190, 35]
  b := [900, 1241, 300, 441, 870, 840, 597, 851, 1586]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![7, 11, 229, 1621]
  exp := ![1, 1, 1, 1]
  pdgood := [7, 11, 229, 1621]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp7.out
    exact hp11.out
    exact hp229.out
    exact hp1621.out
  a := [-673046663, -9552532092, -4327227279, 27028955852, 6251614164, -22173447660, 977712591, 5552314440, -1345179180]
  b := [-350814878, -244255725, 3253041734, 1595030845, -5408369816, -1232783010, 3185863239, -95917269, -622490403, 134517918]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 229 T_ofList CD229
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1621 T_ofList CD1621

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

end VoightMaximalOrderD10R242

namespace VoightMaximalOrderD10R244

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3582703010701, [-1, 0, 10, -1, -28, 3, 28, -1, -10, 0, 1], 1⟩
local notation "l" => [-1, 0, 10, -1, -28, 3, 28, -1, -10, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -10, 1, 28, -3, -28, 1, 10, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -10, 1, 28, -3, -28, 1, 10, 0], ![0, 1, 0, -10, 1, 28, -3, -28, 1, 10]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -10, 1, 28, -3, -28, 1, 10, 0], ![0, 1, 0, -10, 1, 28, -3, -28, 1, 10], ![10, 0, -99, 10, 270, -29, -252, 7, 72, 1]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -10, 1, 28, -3, -28, 1, 10, 0], ![0, 1, 0, -10, 1, 28, -3, -28, 1, 10], ![10, 0, -99, 10, 270, -29, -252, 7, 72, 1], ![1, 10, -10, -98, 38, 267, -57, -251, 17, 72]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -10, 1, 28, -3, -28, 1, 10, 0], ![0, 1, 0, -10, 1, 28, -3, -28, 1, 10], ![10, 0, -99, 10, 270, -29, -252, 7, 72, 1], ![1, 10, -10, -98, 38, 267, -57, -251, 17, 72], ![72, 1, -710, 62, 1918, -178, -1749, 15, 469, 17]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -10, 1, 28, -3, -28, 1, 10, 0], ![0, 1, 0, -10, 1, 28, -3, -28, 1, 10], ![10, 0, -99, 10, 270, -29, -252, 7, 72, 1], ![1, 10, -10, -98, 38, 267, -57, -251, 17, 72], ![72, 1, -710, 62, 1918, -178, -1749, 15, 469, 17], ![17, 72, -169, -693, 538, 1867, -654, -1732, 185, 469]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -10, 1, 28, -3, -28, 1, 10, 0], ![0, 1, 0, -10, 1, 28, -3, -28, 1, 10], ![10, 0, -99, 10, 270, -29, -252, 7, 72, 1], ![1, 10, -10, -98, 38, 267, -57, -251, 17, 72], ![72, 1, -710, 62, 1918, -178, -1749, 15, 469, 17], ![17, 72, -169, -693, 538, 1867, -654, -1732, 185, 469], ![469, 17, -4618, 300, 12439, -869, -11265, -185, 2958, 185]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -10, 1, 28, -3, -28, 1, 10, 0], ![0, 1, 0, -10, 1, 28, -3, -28, 1, 10], ![10, 0, -99, 10, 270, -29, -252, 7, 72, 1], ![1, 10, -10, -98, 38, 267, -57, -251, 17, 72], ![72, 1, -710, 62, 1918, -178, -1749, 15, 469, 17], ![17, 72, -169, -693, 538, 1867, -654, -1732, 185, 469], ![469, 17, -4618, 300, 12439, -869, -11265, -185, 2958, 185], ![185, 469, -1833, -4433, 5480, 11884, -6049, -11080, 1665, 2958]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -10, 1, 28, -3, -28, 1, 10, 0], ![0, 1, 0, -10, 1, 28, -3, -28, 1, 10], ![10, 0, -99, 10, 270, -29, -252, 7, 72, 1], ![1, 10, -10, -98, 38, 267, -57, -251, 17, 72], ![72, 1, -710, 62, 1918, -178, -1749, 15, 469, 17], ![17, 72, -169, -693, 538, 1867, -654, -1732, 185, 469], ![469, 17, -4618, 300, 12439, -869, -11265, -185, 2958, 185], ![185, 469, -1833, -4433, 5480, 11884, -6049, -11080, 1665, 2958], ![2958, 185, -29111, 1125, 78391, -3394, -70940, -3091, 18500, 1665]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-10, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-72, -1, -10, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-72, -1, -10, 0, -1], [-17, -72, -1, -10, 0, -1]], ![[], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-72, -1, -10, 0, -1], [-17, -72, -1, -10, 0, -1], [-469, -17, -72, -1, -10, 0, -1]], ![[], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-72, -1, -10, 0, -1], [-17, -72, -1, -10, 0, -1], [-469, -17, -72, -1, -10, 0, -1], [-185, -469, -17, -72, -1, -10, 0, -1]], ![[], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-72, -1, -10, 0, -1], [-17, -72, -1, -10, 0, -1], [-469, -17, -72, -1, -10, 0, -1], [-185, -469, -17, -72, -1, -10, 0, -1], [-2958, -185, -469, -17, -72, -1, -10, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -10, 1, 28, -3, -28, 1, 10, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -10, 1, 28, -3, -28, 1, 10, 0], [0, 1, 0, -10, 1, 28, -3, -28, 1, 10]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -10, 1, 28, -3, -28, 1, 10, 0], [0, 1, 0, -10, 1, 28, -3, -28, 1, 10], [10, 0, -99, 10, 270, -29, -252, 7, 72, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -10, 1, 28, -3, -28, 1, 10, 0], [0, 1, 0, -10, 1, 28, -3, -28, 1, 10], [10, 0, -99, 10, 270, -29, -252, 7, 72, 1], [1, 10, -10, -98, 38, 267, -57, -251, 17, 72]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -10, 1, 28, -3, -28, 1, 10, 0], [0, 1, 0, -10, 1, 28, -3, -28, 1, 10], [10, 0, -99, 10, 270, -29, -252, 7, 72, 1], [1, 10, -10, -98, 38, 267, -57, -251, 17, 72], [72, 1, -710, 62, 1918, -178, -1749, 15, 469, 17]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -10, 1, 28, -3, -28, 1, 10, 0], [0, 1, 0, -10, 1, 28, -3, -28, 1, 10], [10, 0, -99, 10, 270, -29, -252, 7, 72, 1], [1, 10, -10, -98, 38, 267, -57, -251, 17, 72], [72, 1, -710, 62, 1918, -178, -1749, 15, 469, 17], [17, 72, -169, -693, 538, 1867, -654, -1732, 185, 469]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -10, 1, 28, -3, -28, 1, 10, 0], [0, 1, 0, -10, 1, 28, -3, -28, 1, 10], [10, 0, -99, 10, 270, -29, -252, 7, 72, 1], [1, 10, -10, -98, 38, 267, -57, -251, 17, 72], [72, 1, -710, 62, 1918, -178, -1749, 15, 469, 17], [17, 72, -169, -693, 538, 1867, -654, -1732, 185, 469], [469, 17, -4618, 300, 12439, -869, -11265, -185, 2958, 185]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -10, 1, 28, -3, -28, 1, 10, 0], [0, 1, 0, -10, 1, 28, -3, -28, 1, 10], [10, 0, -99, 10, 270, -29, -252, 7, 72, 1], [1, 10, -10, -98, 38, 267, -57, -251, 17, 72], [72, 1, -710, 62, 1918, -178, -1749, 15, 469, 17], [17, 72, -169, -693, 538, 1867, -654, -1732, 185, 469], [469, 17, -4618, 300, 12439, -869, -11265, -185, 2958, 185], [185, 469, -1833, -4433, 5480, 11884, -6049, -11080, 1665, 2958]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -10, 1, 28, -3, -28, 1, 10, 0], [0, 1, 0, -10, 1, 28, -3, -28, 1, 10], [10, 0, -99, 10, 270, -29, -252, 7, 72, 1], [1, 10, -10, -98, 38, 267, -57, -251, 17, 72], [72, 1, -710, 62, 1918, -178, -1749, 15, 469, 17], [17, 72, -169, -693, 538, 1867, -654, -1732, 185, 469], [469, 17, -4618, 300, 12439, -869, -11265, -185, 2958, 185], [185, 469, -1833, -4433, 5480, 11884, -6049, -11080, 1665, 2958], [2958, 185, -29111, 1125, 78391, -3394, -70940, -3091, 18500, 1665]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp41 : Fact (Nat.Prime 41) := fact_iff.2 (by norm_num)
instance hp61 : Fact (Nat.Prime 61) := fact_iff.2 (by norm_num)
instance hp149 : Fact (Nat.Prime 149) := fact_iff.2 (by norm_num)
instance hp397 : Fact (Nat.Prime 397) := fact_iff.2 (by norm_num)

def CD41 : CertificateDedekindCriterionLists l 41 where
  n := 2
  a' := [17, 34, 26, 14, 18, 40, 11, 19]
  b' := [29, 0, 11, 31, 28, 1, 33, 10, 7]
  k := [1, 18, 28, 31, 40, 10, 28, 23, 1]
  f := [2, 9, 6, 5, 6, 2, 3, 7, 8, 1]
  g := [9, 40, 24, 20, 22, 7, 16, 30, 32, 1]
  h := [9, 1]
  a := [35, 21, 40, 15, 20, 4, 38, 32, 36]
  b := [6, 2, 13, 29, 5, 24, 27, 12, 5]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD61 : CertificateDedekindCriterionLists l 61 where
  n := 2
  a' := [26, 60, 41, 4, 54, 16, 34]
  b' := [17, 8, 46, 20, 46, 50, 22, 11]
  k := [60, 46, 7, 33, 54, 46, 1]
  f := [1, 38, 55, 55, 70, 56, 48, 43, 16, 1]
  g := [1, 38, 32, 35, 48, 26, 32, 23, 1]
  h := [60, 38, 1]
  a := [13, 31, 13, 30, 55, 39, 51, 28]
  b := [49, 53, 2, 35, 0, 44, 16, 23, 33]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD149 : CertificateDedekindCriterionLists l 149 where
  n := 2
  a' := [22, 40, 57, 44, 141, 25, 146, 109]
  b' := [73, 61, 96, 91, 10, 90, 145, 146, 21]
  k := [1, 88, 136, 137, 2, 12, 136, 61, 1]
  f := [13, 44, 34, 17, 23, 25, 11, 41, 32, 1]
  g := [44, 148, 112, 55, 76, 83, 36, 138, 105, 1]
  h := [44, 1]
  a := [28, 10, 64, 58, 0, 69, 58, 97, 10]
  b := [29, 95, 125, 45, 45, 37, 32, 37, 139]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD397 : CertificateDedekindCriterionLists l 397 where
  n := 2
  a' := [107, 22, 281, 264, 222, 377, 187]
  b' := [247, 313, 309, 126, 369, 38, 355, 324]
  k := [396, 385, 297, 13, 100, 385, 1]
  f := [1, 6, 27, 169, 277, 232, 31, 391, 7, 1]
  g := [1, 6, 27, 169, 275, 228, 27, 391, 1]
  h := [396, 6, 1]
  a := [312, 279, 369, 253, 171, 114, 205, 264]
  b := [86, 112, 37, 83, 67, 185, 30, 333, 133]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![41, 61, 149, 397]
  exp := ![1, 1, 1, 1]
  pdgood := [41, 61, 149, 397]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp41.out
    exact hp61.out
    exact hp149.out
    exact hp397.out
  a := [-147941653, 5143099220, 12308828647, -19613725628, -33925799026, 11409012822, 19688109480, -1279747260, -2613731560]
  b := [257154961, 727985503, -2010367367, -4218370137, 3618381468, 6037218232, -1475262681, -2491557260, 127974726, 261373156]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 41 T_ofList CD41
    exact satisfiesDedekindCriterion_of_certificate_lists T l 61 T_ofList CD61
    exact satisfiesDedekindCriterion_of_certificate_lists T l 149 T_ofList CD149
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

end VoightMaximalOrderD10R244

namespace VoightMaximalOrderD10R246

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨3594788065625, [-1, 13, -50, 58, 32, -83, 11, 29, -8, -3, 1], 1⟩
local notation "l" => [-1, 13, -50, 58, 32, -83, 11, 29, -8, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -13, 50, -58, -32, 83, -11, -29, 8, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -13, 50, -58, -32, 83, -11, -29, 8, 3], ![3, -38, 137, -124, -154, 217, 50, -98, -5, 17]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -13, 50, -58, -32, 83, -11, -29, 8, 3], ![3, -38, 137, -124, -154, 217, 50, -98, -5, 17], ![17, -218, 812, -849, -668, 1257, 30, -443, 38, 46]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -13, 50, -58, -32, 83, -11, -29, 8, 3], ![3, -38, 137, -124, -154, 217, 50, -98, -5, 17], ![17, -218, 812, -849, -668, 1257, 30, -443, 38, 46], ![46, -581, 2082, -1856, -2321, 3150, 751, -1304, -75, 176]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -13, 50, -58, -32, 83, -11, -29, 8, 3], ![3, -38, 137, -124, -154, 217, 50, -98, -5, 17], ![17, -218, 812, -849, -668, 1257, 30, -443, 38, 46], ![46, -581, 2082, -1856, -2321, 3150, 751, -1304, -75, 176], ![176, -2242, 8219, -8126, -7488, 12287, 1214, -4353, 104, 453]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -13, 50, -58, -32, 83, -11, -29, 8, 3], ![3, -38, 137, -124, -154, 217, 50, -98, -5, 17], ![17, -218, 812, -849, -668, 1257, 30, -443, 38, 46], ![46, -581, 2082, -1856, -2321, 3150, 751, -1304, -75, 176], ![176, -2242, 8219, -8126, -7488, 12287, 1214, -4353, 104, 453], ![453, -5713, 20408, -18055, -22622, 30111, 7304, -11923, -729, 1463]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -13, 50, -58, -32, 83, -11, -29, 8, 3], ![3, -38, 137, -124, -154, 217, 50, -98, -5, 17], ![17, -218, 812, -849, -668, 1257, 30, -443, 38, 46], ![46, -581, 2082, -1856, -2321, 3150, 751, -1304, -75, 176], ![176, -2242, 8219, -8126, -7488, 12287, 1214, -4353, 104, 453], ![453, -5713, 20408, -18055, -22622, 30111, 7304, -11923, -729, 1463], ![1463, -18566, 67437, -64446, -64871, 98807, 14018, -35123, -219, 3660]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -13, 50, -58, -32, 83, -11, -29, 8, 3], ![3, -38, 137, -124, -154, 217, 50, -98, -5, 17], ![17, -218, 812, -849, -668, 1257, 30, -443, 38, 46], ![46, -581, 2082, -1856, -2321, 3150, 751, -1304, -75, 176], ![176, -2242, 8219, -8126, -7488, 12287, 1214, -4353, 104, 453], ![453, -5713, 20408, -18055, -22622, 30111, 7304, -11923, -729, 1463], ![1463, -18566, 67437, -64446, -64871, 98807, 14018, -35123, -219, 3660], ![3660, -46117, 164434, -144843, -181566, 238909, 58547, -92122, -5843, 10761]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -13, 50, -58, -32, 83, -11, -29, 8, 3], ![3, -38, 137, -124, -154, 217, 50, -98, -5, 17], ![17, -218, 812, -849, -668, 1257, 30, -443, 38, 46], ![46, -581, 2082, -1856, -2321, 3150, 751, -1304, -75, 176], ![176, -2242, 8219, -8126, -7488, 12287, 1214, -4353, 104, 453], ![453, -5713, 20408, -18055, -22622, 30111, 7304, -11923, -729, 1463], ![1463, -18566, 67437, -64446, -64871, 98807, 14018, -35123, -219, 3660], ![3660, -46117, 164434, -144843, -181566, 238909, 58547, -92122, -5843, 10761], ![10761, -136233, 491933, -459704, -489195, 711597, 120538, -253522, -6034, 26440]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-46, -17, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-46, -17, -3, -1], [-176, -46, -17, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-46, -17, -3, -1], [-176, -46, -17, -3, -1], [-453, -176, -46, -17, -3, -1]], ![[], [], [], [-1], [-3, -1], [-17, -3, -1], [-46, -17, -3, -1], [-176, -46, -17, -3, -1], [-453, -176, -46, -17, -3, -1], [-1463, -453, -176, -46, -17, -3, -1]], ![[], [], [-1], [-3, -1], [-17, -3, -1], [-46, -17, -3, -1], [-176, -46, -17, -3, -1], [-453, -176, -46, -17, -3, -1], [-1463, -453, -176, -46, -17, -3, -1], [-3660, -1463, -453, -176, -46, -17, -3, -1]], ![[], [-1], [-3, -1], [-17, -3, -1], [-46, -17, -3, -1], [-176, -46, -17, -3, -1], [-453, -176, -46, -17, -3, -1], [-1463, -453, -176, -46, -17, -3, -1], [-3660, -1463, -453, -176, -46, -17, -3, -1], [-10761, -3660, -1463, -453, -176, -46, -17, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -13, 50, -58, -32, 83, -11, -29, 8, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -13, 50, -58, -32, 83, -11, -29, 8, 3], [3, -38, 137, -124, -154, 217, 50, -98, -5, 17]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -13, 50, -58, -32, 83, -11, -29, 8, 3], [3, -38, 137, -124, -154, 217, 50, -98, -5, 17], [17, -218, 812, -849, -668, 1257, 30, -443, 38, 46]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -13, 50, -58, -32, 83, -11, -29, 8, 3], [3, -38, 137, -124, -154, 217, 50, -98, -5, 17], [17, -218, 812, -849, -668, 1257, 30, -443, 38, 46], [46, -581, 2082, -1856, -2321, 3150, 751, -1304, -75, 176]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -13, 50, -58, -32, 83, -11, -29, 8, 3], [3, -38, 137, -124, -154, 217, 50, -98, -5, 17], [17, -218, 812, -849, -668, 1257, 30, -443, 38, 46], [46, -581, 2082, -1856, -2321, 3150, 751, -1304, -75, 176], [176, -2242, 8219, -8126, -7488, 12287, 1214, -4353, 104, 453]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -13, 50, -58, -32, 83, -11, -29, 8, 3], [3, -38, 137, -124, -154, 217, 50, -98, -5, 17], [17, -218, 812, -849, -668, 1257, 30, -443, 38, 46], [46, -581, 2082, -1856, -2321, 3150, 751, -1304, -75, 176], [176, -2242, 8219, -8126, -7488, 12287, 1214, -4353, 104, 453], [453, -5713, 20408, -18055, -22622, 30111, 7304, -11923, -729, 1463]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -13, 50, -58, -32, 83, -11, -29, 8, 3], [3, -38, 137, -124, -154, 217, 50, -98, -5, 17], [17, -218, 812, -849, -668, 1257, 30, -443, 38, 46], [46, -581, 2082, -1856, -2321, 3150, 751, -1304, -75, 176], [176, -2242, 8219, -8126, -7488, 12287, 1214, -4353, 104, 453], [453, -5713, 20408, -18055, -22622, 30111, 7304, -11923, -729, 1463], [1463, -18566, 67437, -64446, -64871, 98807, 14018, -35123, -219, 3660]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -13, 50, -58, -32, 83, -11, -29, 8, 3], [3, -38, 137, -124, -154, 217, 50, -98, -5, 17], [17, -218, 812, -849, -668, 1257, 30, -443, 38, 46], [46, -581, 2082, -1856, -2321, 3150, 751, -1304, -75, 176], [176, -2242, 8219, -8126, -7488, 12287, 1214, -4353, 104, 453], [453, -5713, 20408, -18055, -22622, 30111, 7304, -11923, -729, 1463], [1463, -18566, 67437, -64446, -64871, 98807, 14018, -35123, -219, 3660], [3660, -46117, 164434, -144843, -181566, 238909, 58547, -92122, -5843, 10761]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -13, 50, -58, -32, 83, -11, -29, 8, 3], [3, -38, 137, -124, -154, 217, 50, -98, -5, 17], [17, -218, 812, -849, -668, 1257, 30, -443, 38, 46], [46, -581, 2082, -1856, -2321, 3150, 751, -1304, -75, 176], [176, -2242, 8219, -8126, -7488, 12287, 1214, -4353, 104, 453], [453, -5713, 20408, -18055, -22622, 30111, 7304, -11923, -729, 1463], [1463, -18566, 67437, -64446, -64871, 98807, 14018, -35123, -219, 3660], [3660, -46117, 164434, -144843, -181566, 238909, 58547, -92122, -5843, 10761], [10761, -136233, 491933, -459704, -489195, 711597, 120538, -253522, -6034, 26440]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp60543799 : Fact (Nat.Prime 60543799) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4]
  b' := [4, 0, 4]
  k := [1]
  f := [1, -1, 14, -6, 0, 23, 2, -3, 3, 1]
  g := [2, 2, 4, 3, 1, 1]
  h := [2, 2, 4, 3, 1, 1]
  a := [2, 3, 3, 3, 1]
  b := [2, 0, 2, 0, 4, 0, 4, 0, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD19 : CertificateDedekindCriterionLists l 19 where
  n := 2
  a' := [17, 3, 17, 16, 7, 8, 18, 10]
  b' := [0, 17, 4, 13, 10, 3, 5, 8, 1]
  k := [14, 13, 9, 7, 13, 12, 16, 12, 1]
  f := [1, 0, 4, -2, 0, 7, 1, -1, 2, 1]
  g := [9, 2, 12, 4, 14, 18, 6, 2, 14, 1]
  h := [2, 1]
  a := [13, 6, 16, 2, 16, 16, 11, 15, 2]
  b := [5, 13, 4, 7, 10, 0, 10, 9, 17]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD60543799 : CertificateDedekindCriterionLists l 60543799 where
  n := 2
  a' := [30834479, 54688050, 7810163, 49738941, 10677224, 47517853, 56928754, 18409924]
  b' := [14376408, 20050586, 31880904, 4809193, 28983052, 9540742, 53019425, 19634220, 24862808]
  k := [35381177, 33252658, 15179925, 8430750, 56107623, 54683308, 23525213, 15064160, 1]
  f := [2189745, 3724034, 19071846, 15203907, 3490530, 9350845, 15790992, 3906273, 14198904, 1]
  g := [5830103, 9915082, 50777979, 40479754, 9293386, 24896227, 42042844, 10400284, 37803978, 1]
  h := [22739818, 1]
  a := [52022759, 4735730, 27672649, 52117479, 48661962, 13751272, 760763, 46599400, 49127300]
  b := [42483763, 59226595, 41063027, 47619415, 41625239, 19272634, 31750578, 1026760, 11416499]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 19, 60543799]
  exp := ![1, 1, 1]
  pdgood := [5, 19, 60543799]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp19.out
    exact hp60543799.out
  a := [556599207616, -2578026521222, 180047743403, 5587799518132, -2069556807446, -2694359468614, 1131485039480, 356946373846, -155133628180]
  b := [43257759117, -422156946810, 906292933287, 46977512133, -1154104595327, 323960122784, 393639722192, -139827317124, -40348646230, 15513362818]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19 T_ofList CD19
    exact satisfiesDedekindCriterion_of_certificate_lists T l 60543799 T_ofList CD60543799

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

end VoightMaximalOrderD10R246

end TraceEuclidean
