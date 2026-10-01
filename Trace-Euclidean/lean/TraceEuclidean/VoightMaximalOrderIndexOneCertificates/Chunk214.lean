import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk210
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

namespace VoightMaximalOrderD10R512

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5751248003125, [1, 0, -16, 8, 50, -47, -17, 28, -3, -4, 1], 1⟩
local notation "l" => [1, 0, -16, 8, 50, -47, -17, 28, -3, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 16, -8, -50, 47, 17, -28, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 16, -8, -50, 47, 17, -28, 3, 4], ![-4, -1, 64, -16, -208, 138, 115, -95, -16, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 16, -8, -50, 47, 17, -28, 3, 4], ![-4, -1, 64, -16, -208, 138, 115, -95, -16, 19], ![-19, -4, 303, -88, -966, 685, 461, -417, -38, 60]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 16, -8, -50, 47, 17, -28, 3, 4], ![-4, -1, 64, -16, -208, 138, 115, -95, -16, 19], ![-19, -4, 303, -88, -966, 685, 461, -417, -38, 60], ![-60, -19, 956, -177, -3088, 1854, 1705, -1219, -237, 202]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 16, -8, -50, 47, 17, -28, 3, 4], ![-4, -1, 64, -16, -208, 138, 115, -95, -16, 19], ![-19, -4, 303, -88, -966, 685, 461, -417, -38, 60], ![-60, -19, 956, -177, -3088, 1854, 1705, -1219, -237, 202], ![-202, -60, 3213, -660, -10277, 6406, 5288, -3951, -613, 571]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 16, -8, -50, 47, 17, -28, 3, 4], ![-4, -1, 64, -16, -208, 138, 115, -95, -16, 19], ![-19, -4, 303, -88, -966, 685, 461, -417, -38, 60], ![-60, -19, 956, -177, -3088, 1854, 1705, -1219, -237, 202], ![-202, -60, 3213, -660, -10277, 6406, 5288, -3951, -613, 571], ![-571, -202, 9076, -1355, -29210, 16560, 16113, -10700, -2238, 1671]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 16, -8, -50, 47, 17, -28, 3, 4], ![-4, -1, 64, -16, -208, 138, 115, -95, -16, 19], ![-19, -4, 303, -88, -966, 685, 461, -417, -38, 60], ![-60, -19, 956, -177, -3088, 1854, 1705, -1219, -237, 202], ![-202, -60, 3213, -660, -10277, 6406, 5288, -3951, -613, 571], ![-571, -202, 9076, -1355, -29210, 16560, 16113, -10700, -2238, 1671], ![-1671, -571, 26534, -4292, -84905, 49327, 44967, -30675, -5687, 4446]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 16, -8, -50, 47, 17, -28, 3, 4], ![-4, -1, 64, -16, -208, 138, 115, -95, -16, 19], ![-19, -4, 303, -88, -966, 685, 461, -417, -38, 60], ![-60, -19, 956, -177, -3088, 1854, 1705, -1219, -237, 202], ![-202, -60, 3213, -660, -10277, 6406, 5288, -3951, -613, 571], ![-571, -202, 9076, -1355, -29210, 16560, 16113, -10700, -2238, 1671], ![-1671, -571, 26534, -4292, -84905, 49327, 44967, -30675, -5687, 4446], ![-4446, -1671, 70565, -9034, -226592, 124057, 124909, -79521, -17337, 12097]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 16, -8, -50, 47, 17, -28, 3, 4], ![-4, -1, 64, -16, -208, 138, 115, -95, -16, 19], ![-19, -4, 303, -88, -966, 685, 461, -417, -38, 60], ![-60, -19, 956, -177, -3088, 1854, 1705, -1219, -237, 202], ![-202, -60, 3213, -660, -10277, 6406, 5288, -3951, -613, 571], ![-571, -202, 9076, -1355, -29210, 16560, 16113, -10700, -2238, 1671], ![-1671, -571, 26534, -4292, -84905, 49327, 44967, -30675, -5687, 4446], ![-4446, -1671, 70565, -9034, -226592, 124057, 124909, -79521, -17337, 12097], ![-12097, -4446, 191881, -26211, -613884, 341967, 329706, -213807, -43230, 31051]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-60, -19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-60, -19, -4, -1], [-202, -60, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-60, -19, -4, -1], [-202, -60, -19, -4, -1], [-571, -202, -60, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-60, -19, -4, -1], [-202, -60, -19, -4, -1], [-571, -202, -60, -19, -4, -1], [-1671, -571, -202, -60, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-60, -19, -4, -1], [-202, -60, -19, -4, -1], [-571, -202, -60, -19, -4, -1], [-1671, -571, -202, -60, -19, -4, -1], [-4446, -1671, -571, -202, -60, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-60, -19, -4, -1], [-202, -60, -19, -4, -1], [-571, -202, -60, -19, -4, -1], [-1671, -571, -202, -60, -19, -4, -1], [-4446, -1671, -571, -202, -60, -19, -4, -1], [-12097, -4446, -1671, -571, -202, -60, -19, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 16, -8, -50, 47, 17, -28, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 16, -8, -50, 47, 17, -28, 3, 4], [-4, -1, 64, -16, -208, 138, 115, -95, -16, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 16, -8, -50, 47, 17, -28, 3, 4], [-4, -1, 64, -16, -208, 138, 115, -95, -16, 19], [-19, -4, 303, -88, -966, 685, 461, -417, -38, 60]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 16, -8, -50, 47, 17, -28, 3, 4], [-4, -1, 64, -16, -208, 138, 115, -95, -16, 19], [-19, -4, 303, -88, -966, 685, 461, -417, -38, 60], [-60, -19, 956, -177, -3088, 1854, 1705, -1219, -237, 202]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 16, -8, -50, 47, 17, -28, 3, 4], [-4, -1, 64, -16, -208, 138, 115, -95, -16, 19], [-19, -4, 303, -88, -966, 685, 461, -417, -38, 60], [-60, -19, 956, -177, -3088, 1854, 1705, -1219, -237, 202], [-202, -60, 3213, -660, -10277, 6406, 5288, -3951, -613, 571]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 16, -8, -50, 47, 17, -28, 3, 4], [-4, -1, 64, -16, -208, 138, 115, -95, -16, 19], [-19, -4, 303, -88, -966, 685, 461, -417, -38, 60], [-60, -19, 956, -177, -3088, 1854, 1705, -1219, -237, 202], [-202, -60, 3213, -660, -10277, 6406, 5288, -3951, -613, 571], [-571, -202, 9076, -1355, -29210, 16560, 16113, -10700, -2238, 1671]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 16, -8, -50, 47, 17, -28, 3, 4], [-4, -1, 64, -16, -208, 138, 115, -95, -16, 19], [-19, -4, 303, -88, -966, 685, 461, -417, -38, 60], [-60, -19, 956, -177, -3088, 1854, 1705, -1219, -237, 202], [-202, -60, 3213, -660, -10277, 6406, 5288, -3951, -613, 571], [-571, -202, 9076, -1355, -29210, 16560, 16113, -10700, -2238, 1671], [-1671, -571, 26534, -4292, -84905, 49327, 44967, -30675, -5687, 4446]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 16, -8, -50, 47, 17, -28, 3, 4], [-4, -1, 64, -16, -208, 138, 115, -95, -16, 19], [-19, -4, 303, -88, -966, 685, 461, -417, -38, 60], [-60, -19, 956, -177, -3088, 1854, 1705, -1219, -237, 202], [-202, -60, 3213, -660, -10277, 6406, 5288, -3951, -613, 571], [-571, -202, 9076, -1355, -29210, 16560, 16113, -10700, -2238, 1671], [-1671, -571, 26534, -4292, -84905, 49327, 44967, -30675, -5687, 4446], [-4446, -1671, 70565, -9034, -226592, 124057, 124909, -79521, -17337, 12097]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 16, -8, -50, 47, 17, -28, 3, 4], [-4, -1, 64, -16, -208, 138, 115, -95, -16, 19], [-19, -4, 303, -88, -966, 685, 461, -417, -38, 60], [-60, -19, 956, -177, -3088, 1854, 1705, -1219, -237, 202], [-202, -60, 3213, -660, -10277, 6406, 5288, -3951, -613, 571], [-571, -202, 9076, -1355, -29210, 16560, 16113, -10700, -2238, 1671], [-1671, -571, 26534, -4292, -84905, 49327, 44967, -30675, -5687, 4446], [-4446, -1671, 70565, -9034, -226592, 124057, 124909, -79521, -17337, 12097], [-12097, -4446, 191881, -26211, -613884, 341967, 329706, -213807, -43230, 31051]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp2039 : Fact (Nat.Prime 2039) := fact_iff.2 (by norm_num)
instance hp902599 : Fact (Nat.Prime 902599) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 1]
  b' := [1, 4, 1, 2]
  k := [1]
  f := [0, 0, 4, 0, -8, 13, 9, 0, 4, 2]
  g := [1, 0, 2, 4, 3, 1]
  h := [1, 0, 2, 4, 3, 1]
  a := [3, 0, 3, 4, 4]
  b := [1, 0, 1, 1, 2, 3, 0, 0, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2039 : CertificateDedekindCriterionLists l 2039 where
  n := 2
  a' := [866, 1666, 288, 884, 2017, 1749, 197, 401]
  b' := [96, 754, 1021, 75, 938, 105, 1555, 220, 182]
  k := [699, 1650, 812, 173, 1017, 373, 148, 969, 1]
  f := [384, 351, 37, 331, 497, 2, 464, 199, 393, 1]
  g := [1469, 1340, 139, 1266, 1899, 4, 1775, 758, 1502, 1]
  h := [533, 1]
  a := [787, 743, 1528, 471, 916, 1281, 1635, 187, 1238]
  b := [591, 797, 1921, 557, 712, 1200, 708, 508, 801]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD902599 : CertificateDedekindCriterionLists l 902599 where
  n := 2
  a' := [840502, 415835, 180560, 640496, 472862, 379920, 656943, 109933]
  b' := [247467, 875938, 708646, 39211, 100598, 397778, 186943, 683595, 88074]
  k := [413556, 419660, 287358, 749566, 367519, 83188, 846295, 422466, 1]
  f := [415581, 374593, 103621, 407900, 316799, 651282, 623657, 230800, 161797, 1]
  g := [542555, 489043, 135280, 532527, 413591, 850270, 814204, 301316, 211231, 1]
  h := [691364, 1]
  a := [781531, 539802, 816432, 167156, 179792, 638527, 257121, 103007, 642597]
  b := [626618, 275746, 449818, 704139, 127478, 67469, 854370, 870484, 260002]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 2039, 902599]
  exp := ![1, 1, 1]
  pdgood := [5, 2039, 902599]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp2039.out
    exact hp902599.out
  a := [9201996805, -276345304512, -188268631872, 1806358202384, -610884831108, -1500521699878, 632534298428, 277499462880, -121207643600]
  b := [-8635790766, -16961236223, 130227225827, 75417740258, -419873405197, 84891885942, 233127025731, -76879810622, -32598252032, 12120764360]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2039 T_ofList CD2039
    exact satisfiesDedekindCriterion_of_certificate_lists T l 902599 T_ofList CD902599

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

end VoightMaximalOrderD10R512

namespace VoightMaximalOrderD10R514

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5759421800000, [-1, 1, 19, 18, -38, -34, 30, 17, -10, -2, 1], 1⟩
local notation "l" => [-1, 1, 19, 18, -38, -34, 30, 17, -10, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -19, -18, 38, 34, -30, -17, 10, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -19, -18, 38, 34, -30, -17, 10, 2], ![2, -1, -39, -55, 58, 106, -26, -64, 3, 14]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -19, -18, 38, 34, -30, -17, 10, 2], ![2, -1, -39, -55, 58, 106, -26, -64, 3, 14], ![14, -12, -267, -291, 477, 534, -314, -264, 76, 31]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -19, -18, 38, 34, -30, -17, 10, 2], ![2, -1, -39, -55, 58, 106, -26, -64, 3, 14], ![14, -12, -267, -291, 477, 534, -314, -264, 76, 31], ![31, -17, -601, -825, 887, 1531, -396, -841, 46, 138]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -19, -18, 38, 34, -30, -17, 10, 2], ![2, -1, -39, -55, 58, 106, -26, -64, 3, 14], ![14, -12, -267, -291, 477, 534, -314, -264, 76, 31], ![31, -17, -601, -825, 887, 1531, -396, -841, 46, 138], ![138, -107, -2639, -3085, 4419, 5579, -2609, -2742, 539, 322]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -19, -18, 38, 34, -30, -17, 10, 2], ![2, -1, -39, -55, 58, 106, -26, -64, 3, 14], ![14, -12, -267, -291, 477, 534, -314, -264, 76, 31], ![31, -17, -601, -825, 887, 1531, -396, -841, 46, 138], ![138, -107, -2639, -3085, 4419, 5579, -2609, -2742, 539, 322], ![322, -184, -6225, -8435, 9151, 15367, -4081, -8083, 478, 1183]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -19, -18, 38, 34, -30, -17, 10, 2], ![2, -1, -39, -55, 58, 106, -26, -64, 3, 14], ![14, -12, -267, -291, 477, 534, -314, -264, 76, 31], ![31, -17, -601, -825, 887, 1531, -396, -841, 46, 138], ![138, -107, -2639, -3085, 4419, 5579, -2609, -2742, 539, 322], ![322, -184, -6225, -8435, 9151, 15367, -4081, -8083, 478, 1183], ![1183, -861, -22661, -27519, 36519, 49373, -20123, -24192, 3747, 2844]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -19, -18, 38, 34, -30, -17, 10, 2], ![2, -1, -39, -55, 58, 106, -26, -64, 3, 14], ![14, -12, -267, -291, 477, 534, -314, -264, 76, 31], ![31, -17, -601, -825, 887, 1531, -396, -841, 46, 138], ![138, -107, -2639, -3085, 4419, 5579, -2609, -2742, 539, 322], ![322, -184, -6225, -8435, 9151, 15367, -4081, -8083, 478, 1183], ![1183, -861, -22661, -27519, 36519, 49373, -20123, -24192, 3747, 2844], ![2844, -1661, -54897, -73853, 80553, 133215, -35947, -68471, 4248, 9435]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -19, -18, 38, 34, -30, -17, 10, 2], ![2, -1, -39, -55, 58, 106, -26, -64, 3, 14], ![14, -12, -267, -291, 477, 534, -314, -264, 76, 31], ![31, -17, -601, -825, 887, 1531, -396, -841, 46, 138], ![138, -107, -2639, -3085, 4419, 5579, -2609, -2742, 539, 322], ![322, -184, -6225, -8435, 9151, 15367, -4081, -8083, 478, 1183], ![1183, -861, -22661, -27519, 36519, 49373, -20123, -24192, 3747, 2844], ![2844, -1661, -54897, -73853, 80553, 133215, -35947, -68471, 4248, 9435], ![9435, -6591, -180926, -224727, 284677, 401343, -149835, -196342, 25879, 23118]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-31, -14, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-31, -14, -2, -1], [-138, -31, -14, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-31, -14, -2, -1], [-138, -31, -14, -2, -1], [-322, -138, -31, -14, -2, -1]], ![[], [], [], [-1], [-2, -1], [-14, -2, -1], [-31, -14, -2, -1], [-138, -31, -14, -2, -1], [-322, -138, -31, -14, -2, -1], [-1183, -322, -138, -31, -14, -2, -1]], ![[], [], [-1], [-2, -1], [-14, -2, -1], [-31, -14, -2, -1], [-138, -31, -14, -2, -1], [-322, -138, -31, -14, -2, -1], [-1183, -322, -138, -31, -14, -2, -1], [-2844, -1183, -322, -138, -31, -14, -2, -1]], ![[], [-1], [-2, -1], [-14, -2, -1], [-31, -14, -2, -1], [-138, -31, -14, -2, -1], [-322, -138, -31, -14, -2, -1], [-1183, -322, -138, -31, -14, -2, -1], [-2844, -1183, -322, -138, -31, -14, -2, -1], [-9435, -2844, -1183, -322, -138, -31, -14, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -19, -18, 38, 34, -30, -17, 10, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -19, -18, 38, 34, -30, -17, 10, 2], [2, -1, -39, -55, 58, 106, -26, -64, 3, 14]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -19, -18, 38, 34, -30, -17, 10, 2], [2, -1, -39, -55, 58, 106, -26, -64, 3, 14], [14, -12, -267, -291, 477, 534, -314, -264, 76, 31]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -19, -18, 38, 34, -30, -17, 10, 2], [2, -1, -39, -55, 58, 106, -26, -64, 3, 14], [14, -12, -267, -291, 477, 534, -314, -264, 76, 31], [31, -17, -601, -825, 887, 1531, -396, -841, 46, 138]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -19, -18, 38, 34, -30, -17, 10, 2], [2, -1, -39, -55, 58, 106, -26, -64, 3, 14], [14, -12, -267, -291, 477, 534, -314, -264, 76, 31], [31, -17, -601, -825, 887, 1531, -396, -841, 46, 138], [138, -107, -2639, -3085, 4419, 5579, -2609, -2742, 539, 322]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -19, -18, 38, 34, -30, -17, 10, 2], [2, -1, -39, -55, 58, 106, -26, -64, 3, 14], [14, -12, -267, -291, 477, 534, -314, -264, 76, 31], [31, -17, -601, -825, 887, 1531, -396, -841, 46, 138], [138, -107, -2639, -3085, 4419, 5579, -2609, -2742, 539, 322], [322, -184, -6225, -8435, 9151, 15367, -4081, -8083, 478, 1183]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -19, -18, 38, 34, -30, -17, 10, 2], [2, -1, -39, -55, 58, 106, -26, -64, 3, 14], [14, -12, -267, -291, 477, 534, -314, -264, 76, 31], [31, -17, -601, -825, 887, 1531, -396, -841, 46, 138], [138, -107, -2639, -3085, 4419, 5579, -2609, -2742, 539, 322], [322, -184, -6225, -8435, 9151, 15367, -4081, -8083, 478, 1183], [1183, -861, -22661, -27519, 36519, 49373, -20123, -24192, 3747, 2844]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -19, -18, 38, 34, -30, -17, 10, 2], [2, -1, -39, -55, 58, 106, -26, -64, 3, 14], [14, -12, -267, -291, 477, 534, -314, -264, 76, 31], [31, -17, -601, -825, 887, 1531, -396, -841, 46, 138], [138, -107, -2639, -3085, 4419, 5579, -2609, -2742, 539, 322], [322, -184, -6225, -8435, 9151, 15367, -4081, -8083, 478, 1183], [1183, -861, -22661, -27519, 36519, 49373, -20123, -24192, 3747, 2844], [2844, -1661, -54897, -73853, 80553, 133215, -35947, -68471, 4248, 9435]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -19, -18, 38, 34, -30, -17, 10, 2], [2, -1, -39, -55, 58, 106, -26, -64, 3, 14], [14, -12, -267, -291, 477, 534, -314, -264, 76, 31], [31, -17, -601, -825, 887, 1531, -396, -841, 46, 138], [138, -107, -2639, -3085, 4419, 5579, -2609, -2742, 539, 322], [322, -184, -6225, -8435, 9151, 15367, -4081, -8083, 478, 1183], [1183, -861, -22661, -27519, 36519, 49373, -20123, -24192, 3747, 2844], [2844, -1661, -54897, -73853, 80553, 133215, -35947, -68471, 4248, 9435], [9435, -6591, -180926, -224727, 284677, 401343, -149835, -196342, 25879, 23118]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp31 : Fact (Nat.Prime 31) := fact_iff.2 (by norm_num)
instance hp84449 : Fact (Nat.Prime 84449) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1]
  b' := [0, 1, 1]
  k := [1, 1, 0, 1, 1, 0, 1]
  f := [1, 0, -9, -9, 19, 17, -15, -8, 6, 2]
  g := [1, 0, 0, 0, 0, 0, 0, 1, 1]
  h := [1, 1, 1]
  a := [0, 0, 0, 0, 1, 1, 1, 1]
  b := [1, 0, 0, 0, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 0, 1]
  b' := [1, 4, 2, 2, 4]
  k := [1]
  f := [2, 1, 0, 0, 15, 12, 0, 1, 6, 2]
  g := [3, 1, 3, 2, 4, 1]
  h := [3, 1, 3, 2, 4, 1]
  a := [0, 3, 2, 2, 3]
  b := [2, 4, 1, 4, 3, 4, 0, 2, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [5, 7, 9, 1, 8, 8, 0, 9]
  b' := [0, 1, 6, 0, 0, 3, 5, 7, 10]
  k := [7, 9, 1, 10, 2, 3, 1, 8, 1]
  f := [5, 4, 1, 2, 4, 8, 3, 2, 3, 1]
  g := [9, 6, 4, 6, 0, 9, 9, 5, 3, 1]
  h := [6, 1]
  a := [9, 5, 8, 10, 7, 2, 4, 0, 4]
  b := [0, 3, 5, 2, 7, 8, 8, 0, 7]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD31 : CertificateDedekindCriterionLists l 31 where
  n := 2
  a' := [17, 22, 5, 8, 18, 17, 14, 12]
  b' := [7, 2, 15, 3, 8, 22, 20, 30, 9]
  k := [6, 27, 24, 0, 0, 18, 12, 10, 1]
  f := [21, 25, 6, 19, 2, 14, 6, 11, 4, 1]
  g := [26, 30, 7, 24, 0, 16, 8, 14, 4, 1]
  h := [25, 1]
  a := [23, 0, 28, 30, 13, 7, 16, 15, 17]
  b := [22, 30, 15, 2, 9, 23, 4, 16, 14]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD84449 : CertificateDedekindCriterionLists l 84449 where
  n := 2
  a' := [39801, 71972, 39091, 64338, 47787, 39528, 21381, 4482]
  b' := [26697, 26034, 75771, 12509, 57897, 65159, 83286, 20786, 83951]
  k := [70455, 46507, 80060, 76674, 12297, 4245, 72828, 79544, 1]
  f := [34097, 17983, 28632, 33275, 17063, 39102, 8942, 43488, 21041, 1]
  g := [64452, 33991, 54121, 62897, 32252, 73912, 16901, 82203, 39771, 1]
  h := [44676, 1]
  a := [59586, 55859, 54621, 18605, 83053, 39397, 27368, 65822, 17187]
  b := [46088, 991, 16484, 74492, 56760, 19746, 83845, 11549, 67262]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 5
  p := ![2, 5, 11, 31, 84449]
  exp := ![2, 1, 1, 1, 1]
  pdgood := [2, 5, 11, 31, 84449]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp5.out
    exact hp11.out
    exact hp31.out
    exact hp84449.out
  a := [-837398290668, -30007902229507, 19057723792659, 86400824133588, -42713443837869, -59189062820145, 27132094103134, 8861902029780, -3908940922450]
  b := [-836822348488, 2628745303705, 10272278822420, -6929426688620, -16965270269156, 7868284386650, 8260568262106, -3458481427416, -964369021427, 390894092245]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 31 T_ofList CD31
    exact satisfiesDedekindCriterion_of_certificate_lists T l 84449 T_ofList CD84449

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

end VoightMaximalOrderD10R514

namespace VoightMaximalOrderD10R515

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5770540778125, [-1, 2, 13, -6, -40, -2, 34, 5, -10, -1, 1], 1⟩
local notation "l" => [-1, 2, 13, -6, -40, -2, 34, 5, -10, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -13, 6, 40, 2, -34, -5, 10, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -13, 6, 40, 2, -34, -5, 10, 1], ![1, -1, -15, -7, 46, 42, -32, -39, 5, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -13, 6, 40, 2, -34, -5, 10, 1], ![1, -1, -15, -7, 46, 42, -32, -39, 5, 11], ![11, -21, -144, 51, 433, 68, -332, -87, 71, 16]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -13, 6, 40, 2, -34, -5, 10, 1], ![1, -1, -15, -7, 46, 42, -32, -39, 5, 11], ![11, -21, -144, 51, 433, 68, -332, -87, 71, 16], ![16, -21, -229, -48, 691, 465, -476, -412, 73, 87]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -13, 6, 40, 2, -34, -5, 10, 1], ![1, -1, -15, -7, 46, 42, -32, -39, 5, 11], ![11, -21, -144, 51, 433, 68, -332, -87, 71, 16], ![16, -21, -229, -48, 691, 465, -476, -412, 73, 87], ![87, -158, -1152, 293, 3432, 865, -2493, -911, 458, 160]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -13, 6, 40, 2, -34, -5, 10, 1], ![1, -1, -15, -7, 46, 42, -32, -39, 5, 11], ![11, -21, -144, 51, 433, 68, -332, -87, 71, 16], ![16, -21, -229, -48, 691, 465, -476, -412, 73, 87], ![87, -158, -1152, 293, 3432, 865, -2493, -911, 458, 160], ![160, -233, -2238, -192, 6693, 3752, -4575, -3293, 689, 618]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -13, 6, 40, 2, -34, -5, 10, 1], ![1, -1, -15, -7, 46, 42, -32, -39, 5, 11], ![11, -21, -144, 51, 433, 68, -332, -87, 71, 16], ![16, -21, -229, -48, 691, 465, -476, -412, 73, 87], ![87, -158, -1152, 293, 3432, 865, -2493, -911, 458, 160], ![160, -233, -2238, -192, 6693, 3752, -4575, -3293, 689, 618], ![618, -1076, -8267, 1470, 24528, 7929, -17260, -7665, 2887, 1307]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -13, 6, 40, 2, -34, -5, 10, 1], ![1, -1, -15, -7, 46, 42, -32, -39, 5, 11], ![11, -21, -144, 51, 433, 68, -332, -87, 71, 16], ![16, -21, -229, -48, 691, 465, -476, -412, 73, 87], ![87, -158, -1152, 293, 3432, 865, -2493, -911, 458, 160], ![160, -233, -2238, -192, 6693, 3752, -4575, -3293, 689, 618], ![618, -1076, -8267, 1470, 24528, 7929, -17260, -7665, 2887, 1307], ![1307, -1996, -18067, -425, 53750, 27142, -36509, -23795, 5405, 4194]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -2, -13, 6, 40, 2, -34, -5, 10, 1], ![1, -1, -15, -7, 46, 42, -32, -39, 5, 11], ![11, -21, -144, 51, 433, 68, -332, -87, 71, 16], ![16, -21, -229, -48, 691, 465, -476, -412, 73, 87], ![87, -158, -1152, 293, 3432, 865, -2493, -911, 458, 160], ![160, -233, -2238, -192, 6693, 3752, -4575, -3293, 689, 618], ![618, -1076, -8267, 1470, 24528, 7929, -17260, -7665, 2887, 1307], ![1307, -1996, -18067, -425, 53750, 27142, -36509, -23795, 5405, 4194], ![4194, -7081, -56518, 7097, 167335, 62138, -115454, -57479, 18145, 9599]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-16, -11, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-16, -11, -1, -1], [-87, -16, -11, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-16, -11, -1, -1], [-87, -16, -11, -1, -1], [-160, -87, -16, -11, -1, -1]], ![[], [], [], [-1], [-1, -1], [-11, -1, -1], [-16, -11, -1, -1], [-87, -16, -11, -1, -1], [-160, -87, -16, -11, -1, -1], [-618, -160, -87, -16, -11, -1, -1]], ![[], [], [-1], [-1, -1], [-11, -1, -1], [-16, -11, -1, -1], [-87, -16, -11, -1, -1], [-160, -87, -16, -11, -1, -1], [-618, -160, -87, -16, -11, -1, -1], [-1307, -618, -160, -87, -16, -11, -1, -1]], ![[], [-1], [-1, -1], [-11, -1, -1], [-16, -11, -1, -1], [-87, -16, -11, -1, -1], [-160, -87, -16, -11, -1, -1], [-618, -160, -87, -16, -11, -1, -1], [-1307, -618, -160, -87, -16, -11, -1, -1], [-4194, -1307, -618, -160, -87, -16, -11, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -13, 6, 40, 2, -34, -5, 10, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -13, 6, 40, 2, -34, -5, 10, 1], [1, -1, -15, -7, 46, 42, -32, -39, 5, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -13, 6, 40, 2, -34, -5, 10, 1], [1, -1, -15, -7, 46, 42, -32, -39, 5, 11], [11, -21, -144, 51, 433, 68, -332, -87, 71, 16]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -13, 6, 40, 2, -34, -5, 10, 1], [1, -1, -15, -7, 46, 42, -32, -39, 5, 11], [11, -21, -144, 51, 433, 68, -332, -87, 71, 16], [16, -21, -229, -48, 691, 465, -476, -412, 73, 87]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -13, 6, 40, 2, -34, -5, 10, 1], [1, -1, -15, -7, 46, 42, -32, -39, 5, 11], [11, -21, -144, 51, 433, 68, -332, -87, 71, 16], [16, -21, -229, -48, 691, 465, -476, -412, 73, 87], [87, -158, -1152, 293, 3432, 865, -2493, -911, 458, 160]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -13, 6, 40, 2, -34, -5, 10, 1], [1, -1, -15, -7, 46, 42, -32, -39, 5, 11], [11, -21, -144, 51, 433, 68, -332, -87, 71, 16], [16, -21, -229, -48, 691, 465, -476, -412, 73, 87], [87, -158, -1152, 293, 3432, 865, -2493, -911, 458, 160], [160, -233, -2238, -192, 6693, 3752, -4575, -3293, 689, 618]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -13, 6, 40, 2, -34, -5, 10, 1], [1, -1, -15, -7, 46, 42, -32, -39, 5, 11], [11, -21, -144, 51, 433, 68, -332, -87, 71, 16], [16, -21, -229, -48, 691, 465, -476, -412, 73, 87], [87, -158, -1152, 293, 3432, 865, -2493, -911, 458, 160], [160, -233, -2238, -192, 6693, 3752, -4575, -3293, 689, 618], [618, -1076, -8267, 1470, 24528, 7929, -17260, -7665, 2887, 1307]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -13, 6, 40, 2, -34, -5, 10, 1], [1, -1, -15, -7, 46, 42, -32, -39, 5, 11], [11, -21, -144, 51, 433, 68, -332, -87, 71, 16], [16, -21, -229, -48, 691, 465, -476, -412, 73, 87], [87, -158, -1152, 293, 3432, 865, -2493, -911, 458, 160], [160, -233, -2238, -192, 6693, 3752, -4575, -3293, 689, 618], [618, -1076, -8267, 1470, 24528, 7929, -17260, -7665, 2887, 1307], [1307, -1996, -18067, -425, 53750, 27142, -36509, -23795, 5405, 4194]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -2, -13, 6, 40, 2, -34, -5, 10, 1], [1, -1, -15, -7, 46, 42, -32, -39, 5, 11], [11, -21, -144, 51, 433, 68, -332, -87, 71, 16], [16, -21, -229, -48, 691, 465, -476, -412, 73, 87], [87, -158, -1152, 293, 3432, 865, -2493, -911, 458, 160], [160, -233, -2238, -192, 6693, 3752, -4575, -3293, 689, 618], [618, -1076, -8267, 1470, 24528, 7929, -17260, -7665, 2887, 1307], [1307, -1996, -18067, -425, 53750, 27142, -36509, -23795, 5405, 4194], [4194, -7081, -56518, 7097, 167335, 62138, -115454, -57479, 18145, 9599]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1301 : Fact (Nat.Prime 1301) := fact_iff.2 (by norm_num)
instance hp1419349 : Fact (Nat.Prime 1419349) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 0, 4]
  b' := [1, 3, 4, 3, 2]
  k := [1]
  f := [2, 2, 3, 8, 16, 8, -1, 3, 4, 1]
  g := [3, 2, 4, 3, 2, 1]
  h := [3, 2, 4, 3, 2, 1]
  a := [0, 4, 1, 3, 3]
  b := [2, 1, 0, 0, 2, 0, 0, 1, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1301 : CertificateDedekindCriterionLists l 1301 where
  n := 2
  a' := [243, 340, 834, 825, 812, 722, 463, 1274]
  b' := [811, 954, 230, 126, 1245, 1007, 42, 935, 3]
  k := [193, 150, 461, 380, 52, 765, 253, 282, 1]
  f := [259, 425, 243, 13, 324, 172, 291, 267, 310, 1]
  g := [662, 1085, 619, 32, 828, 438, 743, 681, 791, 1]
  h := [509, 1]
  a := [279, 1015, 41, 218, 908, 1014, 1224, 1001, 144]
  b := [1070, 842, 719, 767, 769, 1265, 1147, 611, 1157]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1419349 : CertificateDedekindCriterionLists l 1419349 where
  n := 2
  a' := [44854, 733000, 1063855, 1121206, 79119, 1096229, 1366016, 650099]
  b' := [945244, 603526, 464080, 670041, 394874, 686420, 1266146, 417308, 716294]
  k := [1403923, 869711, 1409637, 329033, 282627, 1156235, 903535, 551963, 1]
  f := [540272, 75250, 45622, 1075059, 554719, 898789, 71639, 549627, 222319, 1]
  g := [670681, 93413, 56634, 1334553, 688614, 1115735, 88930, 682294, 275981, 1]
  h := [1143367, 1]
  a := [677652, 747064, 1176512, 922544, 786854, 695033, 229480, 1345572, 891268]
  b := [1158444, 837657, 1369052, 658610, 58033, 808354, 369561, 913289, 528081]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 1301, 1419349]
  exp := ![1, 1, 1]
  pdgood := [5, 1301, 1419349]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1301.out
    exact hp1419349.out
  a := [-30799013251, -239835323614, 772622482927, 675633837980, -1211063233615, -539832013368, 538983864992, 107726645100, -75283820200]
  b := [-10783074003, 51061313483, 65495409903, -222807427831, -121752870120, 212222612353, 72996889647, -68555438470, -11525502712, 7528382020]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1301 T_ofList CD1301
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1419349 T_ofList CD1419349

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

end VoightMaximalOrderD10R515

namespace VoightMaximalOrderD10R516

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5774248589825, [1, -4, -6, 27, 8, -43, -1, 23, -3, -4, 1], 1⟩
local notation "l" => [1, -4, -6, 27, 8, -43, -1, 23, -3, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 6, -27, -8, 43, 1, -23, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 6, -27, -8, 43, 1, -23, 3, 4], ![-4, 15, 28, -102, -59, 164, 47, -91, -11, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 6, -27, -8, 43, 1, -23, 3, 4], ![-4, 15, 28, -102, -59, 164, 47, -91, -11, 19], ![-19, 72, 129, -485, -254, 758, 183, -390, -34, 65]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 6, -27, -8, 43, 1, -23, 3, 4], ![-4, 15, 28, -102, -59, 164, 47, -91, -11, 19], ![-19, 72, 129, -485, -254, 758, 183, -390, -34, 65], ![-65, 241, 462, -1626, -1005, 2541, 823, -1312, -195, 226]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 6, -27, -8, 43, 1, -23, 3, 4], ![-4, 15, 28, -102, -59, 164, 47, -91, -11, 19], ![-19, 72, 129, -485, -254, 758, 183, -390, -34, 65], ![-65, 241, 462, -1626, -1005, 2541, 823, -1312, -195, 226], ![-226, 839, 1597, -5640, -3434, 8713, 2767, -4375, -634, 709]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 6, -27, -8, 43, 1, -23, 3, 4], ![-4, 15, 28, -102, -59, 164, 47, -91, -11, 19], ![-19, 72, 129, -485, -254, 758, 183, -390, -34, 65], ![-65, 241, 462, -1626, -1005, 2541, 823, -1312, -195, 226], ![-226, 839, 1597, -5640, -3434, 8713, 2767, -4375, -634, 709], ![-709, 2610, 5093, -17546, -11312, 27053, 9422, -13540, -2248, 2202]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 6, -27, -8, 43, 1, -23, 3, 4], ![-4, 15, 28, -102, -59, 164, 47, -91, -11, 19], ![-19, 72, 129, -485, -254, 758, 183, -390, -34, 65], ![-65, 241, 462, -1626, -1005, 2541, 823, -1312, -195, 226], ![-226, 839, 1597, -5640, -3434, 8713, 2767, -4375, -634, 709], ![-709, 2610, 5093, -17546, -11312, 27053, 9422, -13540, -2248, 2202], ![-2202, 8099, 15822, -54361, -35162, 83374, 29255, -41224, -6934, 6560]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 6, -27, -8, 43, 1, -23, 3, 4], ![-4, 15, 28, -102, -59, 164, 47, -91, -11, 19], ![-19, 72, 129, -485, -254, 758, 183, -390, -34, 65], ![-65, 241, 462, -1626, -1005, 2541, 823, -1312, -195, 226], ![-226, 839, 1597, -5640, -3434, 8713, 2767, -4375, -634, 709], ![-709, 2610, 5093, -17546, -11312, 27053, 9422, -13540, -2248, 2202], ![-2202, 8099, 15822, -54361, -35162, 83374, 29255, -41224, -6934, 6560], ![-6560, 24038, 47459, -161298, -106841, 246918, 89934, -121625, -21544, 19306]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 6, -27, -8, 43, 1, -23, 3, 4], ![-4, 15, 28, -102, -59, 164, 47, -91, -11, 19], ![-19, 72, 129, -485, -254, 758, 183, -390, -34, 65], ![-65, 241, 462, -1626, -1005, 2541, 823, -1312, -195, 226], ![-226, 839, 1597, -5640, -3434, 8713, 2767, -4375, -634, 709], ![-709, 2610, 5093, -17546, -11312, 27053, 9422, -13540, -2248, 2202], ![-2202, 8099, 15822, -54361, -35162, 83374, 29255, -41224, -6934, 6560], ![-6560, 24038, 47459, -161298, -106841, 246918, 89934, -121625, -21544, 19306], ![-19306, 70664, 139874, -473803, -315746, 723317, 266224, -354104, -63707, 55680]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-65, -19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-65, -19, -4, -1], [-226, -65, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-65, -19, -4, -1], [-226, -65, -19, -4, -1], [-709, -226, -65, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-65, -19, -4, -1], [-226, -65, -19, -4, -1], [-709, -226, -65, -19, -4, -1], [-2202, -709, -226, -65, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-65, -19, -4, -1], [-226, -65, -19, -4, -1], [-709, -226, -65, -19, -4, -1], [-2202, -709, -226, -65, -19, -4, -1], [-6560, -2202, -709, -226, -65, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-65, -19, -4, -1], [-226, -65, -19, -4, -1], [-709, -226, -65, -19, -4, -1], [-2202, -709, -226, -65, -19, -4, -1], [-6560, -2202, -709, -226, -65, -19, -4, -1], [-19306, -6560, -2202, -709, -226, -65, -19, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 6, -27, -8, 43, 1, -23, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 6, -27, -8, 43, 1, -23, 3, 4], [-4, 15, 28, -102, -59, 164, 47, -91, -11, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 6, -27, -8, 43, 1, -23, 3, 4], [-4, 15, 28, -102, -59, 164, 47, -91, -11, 19], [-19, 72, 129, -485, -254, 758, 183, -390, -34, 65]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 6, -27, -8, 43, 1, -23, 3, 4], [-4, 15, 28, -102, -59, 164, 47, -91, -11, 19], [-19, 72, 129, -485, -254, 758, 183, -390, -34, 65], [-65, 241, 462, -1626, -1005, 2541, 823, -1312, -195, 226]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 6, -27, -8, 43, 1, -23, 3, 4], [-4, 15, 28, -102, -59, 164, 47, -91, -11, 19], [-19, 72, 129, -485, -254, 758, 183, -390, -34, 65], [-65, 241, 462, -1626, -1005, 2541, 823, -1312, -195, 226], [-226, 839, 1597, -5640, -3434, 8713, 2767, -4375, -634, 709]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 6, -27, -8, 43, 1, -23, 3, 4], [-4, 15, 28, -102, -59, 164, 47, -91, -11, 19], [-19, 72, 129, -485, -254, 758, 183, -390, -34, 65], [-65, 241, 462, -1626, -1005, 2541, 823, -1312, -195, 226], [-226, 839, 1597, -5640, -3434, 8713, 2767, -4375, -634, 709], [-709, 2610, 5093, -17546, -11312, 27053, 9422, -13540, -2248, 2202]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 6, -27, -8, 43, 1, -23, 3, 4], [-4, 15, 28, -102, -59, 164, 47, -91, -11, 19], [-19, 72, 129, -485, -254, 758, 183, -390, -34, 65], [-65, 241, 462, -1626, -1005, 2541, 823, -1312, -195, 226], [-226, 839, 1597, -5640, -3434, 8713, 2767, -4375, -634, 709], [-709, 2610, 5093, -17546, -11312, 27053, 9422, -13540, -2248, 2202], [-2202, 8099, 15822, -54361, -35162, 83374, 29255, -41224, -6934, 6560]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 6, -27, -8, 43, 1, -23, 3, 4], [-4, 15, 28, -102, -59, 164, 47, -91, -11, 19], [-19, 72, 129, -485, -254, 758, 183, -390, -34, 65], [-65, 241, 462, -1626, -1005, 2541, 823, -1312, -195, 226], [-226, 839, 1597, -5640, -3434, 8713, 2767, -4375, -634, 709], [-709, 2610, 5093, -17546, -11312, 27053, 9422, -13540, -2248, 2202], [-2202, 8099, 15822, -54361, -35162, 83374, 29255, -41224, -6934, 6560], [-6560, 24038, 47459, -161298, -106841, 246918, 89934, -121625, -21544, 19306]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 6, -27, -8, 43, 1, -23, 3, 4], [-4, 15, 28, -102, -59, 164, 47, -91, -11, 19], [-19, 72, 129, -485, -254, 758, 183, -390, -34, 65], [-65, 241, 462, -1626, -1005, 2541, 823, -1312, -195, 226], [-226, 839, 1597, -5640, -3434, 8713, 2767, -4375, -634, 709], [-709, 2610, 5093, -17546, -11312, 27053, 9422, -13540, -2248, 2202], [-2202, 8099, 15822, -54361, -35162, 83374, 29255, -41224, -6934, 6560], [-6560, 24038, 47459, -161298, -106841, 246918, 89934, -121625, -21544, 19306], [-19306, 70664, 139874, -473803, -315746, 723317, 266224, -354104, -63707, 55680]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp47 : Fact (Nat.Prime 47) := fact_iff.2 (by norm_num)
instance hp1583 : Fact (Nat.Prime 1583) := fact_iff.2 (by norm_num)
instance hp3104393 : Fact (Nat.Prime 3104393) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 0, 1, 2, 1, 2, 4]
  b' := [0, 1, 2, 2, 4, 1, 1, 2]
  k := [1, 4, 3, 2, 1, 4, 1]
  f := [0, 1, 2, -4, 0, 10, 1, -4, 1, 1]
  g := [1, 0, 3, 4, 1, 2, 1, 0, 1]
  h := [1, 1, 1]
  a := [3, 3, 0, 1, 1, 0, 2, 2]
  b := [1, 2, 3, 1, 3, 3, 3, 1, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD47 : CertificateDedekindCriterionLists l 47 where
  n := 2
  a' := [25, 37, 2, 19, 39, 27, 7, 35]
  b' := [31, 8, 30, 20, 42, 29, 21, 29, 17]
  k := [27, 3, 30, 35, 46, 31, 23, 30, 1]
  f := [7, 15, 7, 29, 4, 24, 11, 19, 9, 1]
  g := [11, 23, 10, 46, 5, 36, 16, 30, 13, 1]
  h := [30, 1]
  a := [26, 20, 37, 37, 4, 15, 9, 1, 22]
  b := [22, 34, 21, 24, 3, 11, 33, 40, 25]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1583 : CertificateDedekindCriterionLists l 1583 where
  n := 2
  a' := [422, 624, 1229, 883, 77, 579, 551, 863]
  b' := [820, 750, 1133, 104, 501, 976, 153, 346, 80]
  k := [885, 170, 932, 39, 754, 1325, 1372, 1085, 1]
  f := [22, 21, 131, 167, 167, 55, 226, 41, 208, 1]
  g := [141, 134, 839, 1067, 1066, 348, 1447, 257, 1332, 1]
  h := [247, 1]
  a := [947, 797, 1565, 1005, 884, 848, 492, 766, 1374]
  b := [582, 641, 770, 777, 775, 676, 1354, 185, 209]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3104393 : CertificateDedekindCriterionLists l 3104393 where
  n := 2
  a' := [1977296, 1127236, 2076334, 1008779, 425897, 1742732, 1335557, 1027591]
  b' := [1216056, 2601656, 1806400, 487922, 2612339, 807573, 2567245, 791142, 1610486]
  k := [2479794, 2674023, 3094524, 1275621, 1314248, 1861755, 814714, 2762237, 1]
  f := [132971, 15765, 572, 94675, 104895, 82883, 106992, 141587, 161649, 1]
  g := [2412929, 286062, 10378, 1717999, 1903444, 1504007, 1941498, 2569266, 2933313, 1]
  h := [171076, 1]
  a := [1844377, 2283069, 375204, 2726884, 22265, 2315373, 2767239, 854841, 1135331]
  b := [829850, 293736, 231238, 1927036, 1420544, 1727009, 2693895, 2763458, 1969062]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 47, 1583, 3104393]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 47, 1583, 3104393]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp47.out
    exact hp1583.out
    exact hp3104393.out
  a := [-7395641283859, -49006526248728, 24548841584938, 149874387594812, -31304251633370, -114411261884708, 26110446593684, 25440537246540, -7747731965800]
  b := [-2137622750456, 1556877973045, 18279703954882, -3904348893324, -30879749239491, 4422684114568, 16587632082514, -3173960490530, -2853963003286, 774773196580]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 47 T_ofList CD47
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1583 T_ofList CD1583
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3104393 T_ofList CD3104393

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

end VoightMaximalOrderD10R516

end TraceEuclidean
