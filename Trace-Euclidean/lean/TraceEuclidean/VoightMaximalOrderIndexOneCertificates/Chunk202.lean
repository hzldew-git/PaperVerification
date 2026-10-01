import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk198
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

namespace VoightMaximalOrderD10R365

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4700113505433, [3, -21, 24, 44, -57, -33, 40, 10, -11, -1, 1], 1⟩
local notation "l" => [3, -21, 24, 44, -57, -33, 40, 10, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 21, -24, -44, 57, 33, -40, -10, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 21, -24, -44, 57, 33, -40, -10, 11, 1], ![-3, 18, -3, -68, 13, 90, -7, -50, 1, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 21, -24, -44, 57, 33, -40, -10, 11, 1], ![-3, 18, -3, -68, 13, 90, -7, -50, 1, 12], ![-36, 249, -270, -531, 616, 409, -390, -127, 82, 13]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 21, -24, -44, 57, 33, -40, -10, 11, 1], ![-3, 18, -3, -68, 13, 90, -7, -50, 1, 12], ![-36, 249, -270, -531, 616, 409, -390, -127, 82, 13], ![-39, 237, -63, -842, 210, 1045, -111, -520, 16, 95]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 21, -24, -44, 57, 33, -40, -10, 11, 1], ![-3, 18, -3, -68, 13, 90, -7, -50, 1, 12], ![-36, 249, -270, -531, 616, 409, -390, -127, 82, 13], ![-39, 237, -63, -842, 210, 1045, -111, -520, 16, 95], ![-285, 1956, -2043, -4243, 4573, 3345, -2755, -1061, 525, 111]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 21, -24, -44, 57, 33, -40, -10, 11, 1], ![-3, 18, -3, -68, 13, 90, -7, -50, 1, 12], ![-36, 249, -270, -531, 616, 409, -390, -127, 82, 13], ![-39, 237, -63, -842, 210, 1045, -111, -520, 16, 95], ![-285, 1956, -2043, -4243, 4573, 3345, -2755, -1061, 525, 111], ![-333, 2046, -708, -6927, 2084, 8236, -1095, -3865, 160, 636]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 21, -24, -44, 57, 33, -40, -10, 11, 1], ![-3, 18, -3, -68, 13, 90, -7, -50, 1, 12], ![-36, 249, -270, -531, 616, 409, -390, -127, 82, 13], ![-39, 237, -63, -842, 210, 1045, -111, -520, 16, 95], ![-285, 1956, -2043, -4243, 4573, 3345, -2755, -1061, 525, 111], ![-333, 2046, -708, -6927, 2084, 8236, -1095, -3865, 160, 636], ![-1908, 13023, -13218, -28692, 29325, 23072, -17204, -7455, 3131, 796]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 21, -24, -44, 57, 33, -40, -10, 11, 1], ![-3, 18, -3, -68, 13, 90, -7, -50, 1, 12], ![-36, 249, -270, -531, 616, 409, -390, -127, 82, 13], ![-39, 237, -63, -842, 210, 1045, -111, -520, 16, 95], ![-285, 1956, -2043, -4243, 4573, 3345, -2755, -1061, 525, 111], ![-333, 2046, -708, -6927, 2084, 8236, -1095, -3865, 160, 636], ![-1908, 13023, -13218, -28692, 29325, 23072, -17204, -7455, 3131, 796], ![-2388, 14808, -6081, -48242, 16680, 55593, -8768, -25164, 1301, 3927]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 21, -24, -44, 57, 33, -40, -10, 11, 1], ![-3, 18, -3, -68, 13, 90, -7, -50, 1, 12], ![-36, 249, -270, -531, 616, 409, -390, -127, 82, 13], ![-39, 237, -63, -842, 210, 1045, -111, -520, 16, 95], ![-285, 1956, -2043, -4243, 4573, 3345, -2755, -1061, 525, 111], ![-333, 2046, -708, -6927, 2084, 8236, -1095, -3865, 160, 636], ![-1908, 13023, -13218, -28692, 29325, 23072, -17204, -7455, 3131, 796], ![-2388, 14808, -6081, -48242, 16680, 55593, -8768, -25164, 1301, 3927], ![-11781, 80079, -79440, -178869, 175597, 146271, -101487, -48038, 18033, 5228]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-13, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-13, -12, -1, -1], [-95, -13, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-13, -12, -1, -1], [-95, -13, -12, -1, -1], [-111, -95, -13, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-13, -12, -1, -1], [-95, -13, -12, -1, -1], [-111, -95, -13, -12, -1, -1], [-636, -111, -95, -13, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-13, -12, -1, -1], [-95, -13, -12, -1, -1], [-111, -95, -13, -12, -1, -1], [-636, -111, -95, -13, -12, -1, -1], [-796, -636, -111, -95, -13, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-13, -12, -1, -1], [-95, -13, -12, -1, -1], [-111, -95, -13, -12, -1, -1], [-636, -111, -95, -13, -12, -1, -1], [-796, -636, -111, -95, -13, -12, -1, -1], [-3927, -796, -636, -111, -95, -13, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 21, -24, -44, 57, 33, -40, -10, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 21, -24, -44, 57, 33, -40, -10, 11, 1], [-3, 18, -3, -68, 13, 90, -7, -50, 1, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 21, -24, -44, 57, 33, -40, -10, 11, 1], [-3, 18, -3, -68, 13, 90, -7, -50, 1, 12], [-36, 249, -270, -531, 616, 409, -390, -127, 82, 13]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 21, -24, -44, 57, 33, -40, -10, 11, 1], [-3, 18, -3, -68, 13, 90, -7, -50, 1, 12], [-36, 249, -270, -531, 616, 409, -390, -127, 82, 13], [-39, 237, -63, -842, 210, 1045, -111, -520, 16, 95]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 21, -24, -44, 57, 33, -40, -10, 11, 1], [-3, 18, -3, -68, 13, 90, -7, -50, 1, 12], [-36, 249, -270, -531, 616, 409, -390, -127, 82, 13], [-39, 237, -63, -842, 210, 1045, -111, -520, 16, 95], [-285, 1956, -2043, -4243, 4573, 3345, -2755, -1061, 525, 111]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 21, -24, -44, 57, 33, -40, -10, 11, 1], [-3, 18, -3, -68, 13, 90, -7, -50, 1, 12], [-36, 249, -270, -531, 616, 409, -390, -127, 82, 13], [-39, 237, -63, -842, 210, 1045, -111, -520, 16, 95], [-285, 1956, -2043, -4243, 4573, 3345, -2755, -1061, 525, 111], [-333, 2046, -708, -6927, 2084, 8236, -1095, -3865, 160, 636]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 21, -24, -44, 57, 33, -40, -10, 11, 1], [-3, 18, -3, -68, 13, 90, -7, -50, 1, 12], [-36, 249, -270, -531, 616, 409, -390, -127, 82, 13], [-39, 237, -63, -842, 210, 1045, -111, -520, 16, 95], [-285, 1956, -2043, -4243, 4573, 3345, -2755, -1061, 525, 111], [-333, 2046, -708, -6927, 2084, 8236, -1095, -3865, 160, 636], [-1908, 13023, -13218, -28692, 29325, 23072, -17204, -7455, 3131, 796]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 21, -24, -44, 57, 33, -40, -10, 11, 1], [-3, 18, -3, -68, 13, 90, -7, -50, 1, 12], [-36, 249, -270, -531, 616, 409, -390, -127, 82, 13], [-39, 237, -63, -842, 210, 1045, -111, -520, 16, 95], [-285, 1956, -2043, -4243, 4573, 3345, -2755, -1061, 525, 111], [-333, 2046, -708, -6927, 2084, 8236, -1095, -3865, 160, 636], [-1908, 13023, -13218, -28692, 29325, 23072, -17204, -7455, 3131, 796], [-2388, 14808, -6081, -48242, 16680, 55593, -8768, -25164, 1301, 3927]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 21, -24, -44, 57, 33, -40, -10, 11, 1], [-3, 18, -3, -68, 13, 90, -7, -50, 1, 12], [-36, 249, -270, -531, 616, 409, -390, -127, 82, 13], [-39, 237, -63, -842, 210, 1045, -111, -520, 16, 95], [-285, 1956, -2043, -4243, 4573, 3345, -2755, -1061, 525, 111], [-333, 2046, -708, -6927, 2084, 8236, -1095, -3865, 160, 636], [-1908, 13023, -13218, -28692, 29325, 23072, -17204, -7455, 3131, 796], [-2388, 14808, -6081, -48242, 16680, 55593, -8768, -25164, 1301, 3927], [-11781, 80079, -79440, -178869, 175597, 146271, -101487, -48038, 18033, 5228]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp174078277979 : Fact (Nat.Prime 174078277979) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 3
  a' := [0, 0, 0, 2]
  b' := [2, 0, 0, 2, 2]
  k := [1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1]
  f := [-1, 7, -8, -14, 19, 11, -13, -3, 4, 1]
  g := [0, 2, 0, 0, 1, 1, 1, 2, 1]
  h := [0, 0, 1]
  a := [2, 1, 2, 1, 0, 0, 2, 1]
  b := [1, 1, 1, 1, 1, 1, 1, 2, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD174078277979 : CertificateDedekindCriterionLists l 174078277979 where
  n := 2
  a' := [119611543390, 140306171172, 22239398645, 56402438305, 113466151848, 37564475375, 155561033158, 12328679504]
  b' := [23436420827, 96352365544, 9458445320, 75057238581, 5993107694, 96261990243, 150558765224, 116693157792, 75998270268]
  k := [93009848953, 126566817312, 116060994353, 37783436030, 97786113015, 50927677405, 93366311723, 40385091150, 1]
  f := [42098824521, 3825127752, 2992952533, 36319984312, 42649548351, 7851437826, 30379162512, 20507415883, 41177296228, 1]
  g := [109631478633, 9961190511, 7794084880, 94582535958, 111065643801, 20446289130, 79111769597, 53404301705, 107231684564, 1]
  h := [66846593414, 1]
  a := [109544559156, 35783074969, 105223869162, 52108106376, 109108145655, 72396355058, 29888911318, 57646291546, 132133897321]
  b := [172289745259, 17490425029, 87718027000, 112104768033, 173287403634, 82301114652, 9937282770, 67317671376, 41944380658]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![3, 174078277979]
  exp := ![1, 1]
  pdgood := [3, 174078277979]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp174078277979.out
  a := [-9886254563286, 12931874264370, 68338788706557, -50323351390496, -105803555725014, 33790947462944, 52343260975702, -4597151578106, -6866057427060]
  b := [-1437190405895, 8448658530436, -4190315574675, -22330840212937, 9422376413215, 20598290745994, -3867900109104, -6852624764148, 391054583540, 686605742706]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 174078277979 T_ofList CD174078277979

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

end VoightMaximalOrderD10R365

namespace VoightMaximalOrderD10R367

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4708554509312, [1, -4, -12, 26, 28, -56, -5, 28, -4, -4, 1], 1⟩
local notation "l" => [1, -4, -12, 26, 28, -56, -5, 28, -4, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -26, -28, 56, 5, -28, 4, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -26, -28, 56, 5, -28, 4, 4], ![-4, 15, 52, -92, -138, 196, 76, -107, -12, 20]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -26, -28, 56, 5, -28, 4, 4], ![-4, 15, 52, -92, -138, 196, 76, -107, -12, 20], ![-20, 76, 255, -468, -652, 982, 296, -484, -27, 68]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -26, -28, 56, 5, -28, 4, 4], ![-4, 15, 52, -92, -138, 196, 76, -107, -12, 20], ![-20, 76, 255, -468, -652, 982, 296, -484, -27, 68], ![-68, 252, 892, -1513, -2372, 3156, 1322, -1608, -212, 245]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -26, -28, 56, 5, -28, 4, 4], ![-4, 15, 52, -92, -138, 196, 76, -107, -12, 20], ![-20, 76, 255, -468, -652, 982, 296, -484, -27, 68], ![-68, 252, 892, -1513, -2372, 3156, 1322, -1608, -212, 245], ![-245, 912, 3192, -5478, -8373, 11348, 4381, -5538, -628, 768]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -26, -28, 56, 5, -28, 4, 4], ![-4, 15, 52, -92, -138, 196, 76, -107, -12, 20], ![-20, 76, 255, -468, -652, 982, 296, -484, -27, 68], ![-68, 252, 892, -1513, -2372, 3156, 1322, -1608, -212, 245], ![-245, 912, 3192, -5478, -8373, 11348, 4381, -5538, -628, 768], ![-768, 2827, 10128, -16776, -26982, 34635, 15188, -17123, -2466, 2444]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -26, -28, 56, 5, -28, 4, 4], ![-4, 15, 52, -92, -138, 196, 76, -107, -12, 20], ![-20, 76, 255, -468, -652, 982, 296, -484, -27, 68], ![-68, 252, 892, -1513, -2372, 3156, 1322, -1608, -212, 245], ![-245, 912, 3192, -5478, -8373, 11348, 4381, -5538, -628, 768], ![-768, 2827, 10128, -16776, -26982, 34635, 15188, -17123, -2466, 2444], ![-2444, 9008, 32155, -53416, -85208, 109882, 46855, -53244, -7347, 7310]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -26, -28, 56, 5, -28, 4, 4], ![-4, 15, 52, -92, -138, 196, 76, -107, -12, 20], ![-20, 76, 255, -468, -652, 982, 296, -484, -27, 68], ![-68, 252, 892, -1513, -2372, 3156, 1322, -1608, -212, 245], ![-245, 912, 3192, -5478, -8373, 11348, 4381, -5538, -628, 768], ![-768, 2827, 10128, -16776, -26982, 34635, 15188, -17123, -2466, 2444], ![-2444, 9008, 32155, -53416, -85208, 109882, 46855, -53244, -7347, 7310], ![-7310, 26796, 96728, -157905, -258096, 324152, 146432, -157825, -24004, 21893]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 12, -26, -28, 56, 5, -28, 4, 4], ![-4, 15, 52, -92, -138, 196, 76, -107, -12, 20], ![-20, 76, 255, -468, -652, 982, 296, -484, -27, 68], ![-68, 252, 892, -1513, -2372, 3156, 1322, -1608, -212, 245], ![-245, 912, 3192, -5478, -8373, 11348, 4381, -5538, -628, 768], ![-768, 2827, 10128, -16776, -26982, 34635, 15188, -17123, -2466, 2444], ![-2444, 9008, 32155, -53416, -85208, 109882, 46855, -53244, -7347, 7310], ![-7310, 26796, 96728, -157905, -258096, 324152, 146432, -157825, -24004, 21893], ![-21893, 80262, 289512, -472490, -770909, 967912, 433617, -466572, -70253, 63568]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-68, -20, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-68, -20, -4, -1], [-245, -68, -20, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-68, -20, -4, -1], [-245, -68, -20, -4, -1], [-768, -245, -68, -20, -4, -1]], ![[], [], [], [-1], [-4, -1], [-20, -4, -1], [-68, -20, -4, -1], [-245, -68, -20, -4, -1], [-768, -245, -68, -20, -4, -1], [-2444, -768, -245, -68, -20, -4, -1]], ![[], [], [-1], [-4, -1], [-20, -4, -1], [-68, -20, -4, -1], [-245, -68, -20, -4, -1], [-768, -245, -68, -20, -4, -1], [-2444, -768, -245, -68, -20, -4, -1], [-7310, -2444, -768, -245, -68, -20, -4, -1]], ![[], [-1], [-4, -1], [-20, -4, -1], [-68, -20, -4, -1], [-245, -68, -20, -4, -1], [-768, -245, -68, -20, -4, -1], [-2444, -768, -245, -68, -20, -4, -1], [-7310, -2444, -768, -245, -68, -20, -4, -1], [-21893, -7310, -2444, -768, -245, -68, -20, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -26, -28, 56, 5, -28, 4, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -26, -28, 56, 5, -28, 4, 4], [-4, 15, 52, -92, -138, 196, 76, -107, -12, 20]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -26, -28, 56, 5, -28, 4, 4], [-4, 15, 52, -92, -138, 196, 76, -107, -12, 20], [-20, 76, 255, -468, -652, 982, 296, -484, -27, 68]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -26, -28, 56, 5, -28, 4, 4], [-4, 15, 52, -92, -138, 196, 76, -107, -12, 20], [-20, 76, 255, -468, -652, 982, 296, -484, -27, 68], [-68, 252, 892, -1513, -2372, 3156, 1322, -1608, -212, 245]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -26, -28, 56, 5, -28, 4, 4], [-4, 15, 52, -92, -138, 196, 76, -107, -12, 20], [-20, 76, 255, -468, -652, 982, 296, -484, -27, 68], [-68, 252, 892, -1513, -2372, 3156, 1322, -1608, -212, 245], [-245, 912, 3192, -5478, -8373, 11348, 4381, -5538, -628, 768]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -26, -28, 56, 5, -28, 4, 4], [-4, 15, 52, -92, -138, 196, 76, -107, -12, 20], [-20, 76, 255, -468, -652, 982, 296, -484, -27, 68], [-68, 252, 892, -1513, -2372, 3156, 1322, -1608, -212, 245], [-245, 912, 3192, -5478, -8373, 11348, 4381, -5538, -628, 768], [-768, 2827, 10128, -16776, -26982, 34635, 15188, -17123, -2466, 2444]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -26, -28, 56, 5, -28, 4, 4], [-4, 15, 52, -92, -138, 196, 76, -107, -12, 20], [-20, 76, 255, -468, -652, 982, 296, -484, -27, 68], [-68, 252, 892, -1513, -2372, 3156, 1322, -1608, -212, 245], [-245, 912, 3192, -5478, -8373, 11348, 4381, -5538, -628, 768], [-768, 2827, 10128, -16776, -26982, 34635, 15188, -17123, -2466, 2444], [-2444, 9008, 32155, -53416, -85208, 109882, 46855, -53244, -7347, 7310]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -26, -28, 56, 5, -28, 4, 4], [-4, 15, 52, -92, -138, 196, 76, -107, -12, 20], [-20, 76, 255, -468, -652, 982, 296, -484, -27, 68], [-68, 252, 892, -1513, -2372, 3156, 1322, -1608, -212, 245], [-245, 912, 3192, -5478, -8373, 11348, 4381, -5538, -628, 768], [-768, 2827, 10128, -16776, -26982, 34635, 15188, -17123, -2466, 2444], [-2444, 9008, 32155, -53416, -85208, 109882, 46855, -53244, -7347, 7310], [-7310, 26796, 96728, -157905, -258096, 324152, 146432, -157825, -24004, 21893]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 12, -26, -28, 56, 5, -28, 4, 4], [-4, 15, 52, -92, -138, 196, 76, -107, -12, 20], [-20, 76, 255, -468, -652, 982, 296, -484, -27, 68], [-68, 252, 892, -1513, -2372, 3156, 1322, -1608, -212, 245], [-245, 912, 3192, -5478, -8373, 11348, 4381, -5538, -628, 768], [-768, 2827, 10128, -16776, -26982, 34635, 15188, -17123, -2466, 2444], [-2444, 9008, 32155, -53416, -85208, 109882, 46855, -53244, -7347, 7310], [-7310, 26796, 96728, -157905, -258096, 324152, 146432, -157825, -24004, 21893], [-21893, 80262, 289512, -472490, -770909, 967912, 433617, -466572, -70253, 63568]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp251 : Fact (Nat.Prime 251) := fact_iff.2 (by norm_num)
instance hp18319513 : Fact (Nat.Prime 18319513) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1]
  b' := [0, 1]
  k := [1]
  f := [0, 2, 6, -12, -14, 29, 3, -14, 3, 2]
  g := [1, 0, 0, 1, 0, 1]
  h := [1, 0, 0, 1, 0, 1]
  a := [1]
  b := [1, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD251 : CertificateDedekindCriterionLists l 251 where
  n := 2
  a' := [85, 50, 104, 202, 49, 25, 161, 56]
  b' := [143, 125, 247, 96, 237, 147, 94, 210, 189]
  k := [17, 159, 6, 211, 209, 245, 165, 35, 1]
  f := [19, 23, 18, 14, 11, 32, 70, 47, 60, 1]
  g := [45, 54, 42, 33, 26, 75, 165, 110, 141, 1]
  h := [106, 1]
  a := [106, 220, 148, 200, 158, 96, 38, 5, 120]
  b := [223, 171, 206, 2, 82, 34, 86, 177, 131]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD18319513 : CertificateDedekindCriterionLists l 18319513 where
  n := 2
  a' := [608935, 6836602, 13762803, 8098948, 4011072, 13135251, 1436471, 9013723]
  b' := [14090169, 761166, 12429014, 6296836, 2535020, 5525770, 2005453, 2802215, 7140481]
  k := [6870978, 12636754, 16721206, 17070591, 14125369, 7011887, 1499573, 18120707, 1]
  f := [66848, 92931, 33313, 30633, 65764, 1053, 1033, 36565, 98862, 1]
  g := [12320025, 17126974, 6139383, 5645572, 12120188, 193945, 190379, 6738894, 18220108, 1]
  h := [99401, 1]
  a := [9123079, 12355302, 17958713, 1488328, 4118021, 1111358, 8516691, 10161, 16421391]
  b := [3475298, 13718696, 14217750, 11483382, 10924654, 8170005, 17843035, 15508367, 1898122]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 251, 18319513]
  exp := ![1, 1, 1]
  pdgood := [2, 251, 18319513]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp251.out
    exact hp18319513.out
  a := [-70974820838, -637778887772, 404350420090, 4389243459458, -1333157391996, -3319888553192, 1019701735098, 617763086696, -207976904460]
  b := [-20042804091, 31786923441, 370234734888, -17801144133, -958556246279, 188952016994, 491522836362, -123846476641, -70095384848, 20797690446]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 251 T_ofList CD251
    exact satisfiesDedekindCriterion_of_certificate_lists T l 18319513 T_ofList CD18319513

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

end VoightMaximalOrderD10R367

namespace VoightMaximalOrderD10R369

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4710313315625, [1, -4, -9, 33, 5, -46, 8, 21, -6, -3, 1], 1⟩
local notation "l" => [1, -4, -9, 33, 5, -46, 8, 21, -6, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 9, -33, -5, 46, -8, -21, 6, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 9, -33, -5, 46, -8, -21, 6, 3], ![-3, 11, 31, -90, -48, 133, 22, -71, -3, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 9, -33, -5, 46, -8, -21, 6, 3], ![-3, 11, 31, -90, -48, 133, 22, -71, -3, 15], ![-15, 57, 146, -464, -165, 642, 13, -293, 19, 42]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 9, -33, -5, 46, -8, -21, 6, 3], ![-3, 11, 31, -90, -48, 133, 22, -71, -3, 15], ![-15, 57, 146, -464, -165, 642, 13, -293, 19, 42], ![-42, 153, 435, -1240, -674, 1767, 306, -869, -41, 145]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 9, -33, -5, 46, -8, -21, 6, 3], ![-3, 11, 31, -90, -48, 133, 22, -71, -3, 15], ![-15, 57, 146, -464, -165, 642, 13, -293, 19, 42], ![-42, 153, 435, -1240, -674, 1767, 306, -869, -41, 145], ![-145, 538, 1458, -4350, -1965, 5996, 607, -2739, 1, 394]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 9, -33, -5, 46, -8, -21, 6, 3], ![-3, 11, 31, -90, -48, 133, 22, -71, -3, 15], ![-15, 57, 146, -464, -165, 642, 13, -293, 19, 42], ![-42, 153, 435, -1240, -674, 1767, 306, -869, -41, 145], ![-145, 538, 1458, -4350, -1965, 5996, 607, -2739, 1, 394], ![-394, 1431, 4084, -11544, -6320, 16159, 2844, -7667, -375, 1183]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 9, -33, -5, 46, -8, -21, 6, 3], ![-3, 11, 31, -90, -48, 133, 22, -71, -3, 15], ![-15, 57, 146, -464, -165, 642, 13, -293, 19, 42], ![-42, 153, 435, -1240, -674, 1767, 306, -869, -41, 145], ![-145, 538, 1458, -4350, -1965, 5996, 607, -2739, 1, 394], ![-394, 1431, 4084, -11544, -6320, 16159, 2844, -7667, -375, 1183], ![-1183, 4338, 12078, -34955, -17459, 48098, 6695, -21999, -569, 3174]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 9, -33, -5, 46, -8, -21, 6, 3], ![-3, 11, 31, -90, -48, 133, 22, -71, -3, 15], ![-15, 57, 146, -464, -165, 642, 13, -293, 19, 42], ![-42, 153, 435, -1240, -674, 1767, 306, -869, -41, 145], ![-145, 538, 1458, -4350, -1965, 5996, 607, -2739, 1, 394], ![-394, 1431, 4084, -11544, -6320, 16159, 2844, -7667, -375, 1183], ![-1183, 4338, 12078, -34955, -17459, 48098, 6695, -21999, -569, 3174], ![-3174, 11513, 32904, -92664, -50825, 128545, 22706, -59959, -2955, 8953]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 9, -33, -5, 46, -8, -21, 6, 3], ![-3, 11, 31, -90, -48, 133, 22, -71, -3, 15], ![-15, 57, 146, -464, -165, 642, 13, -293, 19, 42], ![-42, 153, 435, -1240, -674, 1767, 306, -869, -41, 145], ![-145, 538, 1458, -4350, -1965, 5996, 607, -2739, 1, 394], ![-394, 1431, 4084, -11544, -6320, 16159, 2844, -7667, -375, 1183], ![-1183, 4338, 12078, -34955, -17459, 48098, 6695, -21999, -569, 3174], ![-3174, 11513, 32904, -92664, -50825, 128545, 22706, -59959, -2955, 8953], ![-8953, 32638, 92090, -262545, -137429, 361013, 56921, -165307, -6241, 23904]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1], [-145, -42, -15, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1], [-145, -42, -15, -3, -1], [-394, -145, -42, -15, -3, -1]], ![[], [], [], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1], [-145, -42, -15, -3, -1], [-394, -145, -42, -15, -3, -1], [-1183, -394, -145, -42, -15, -3, -1]], ![[], [], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1], [-145, -42, -15, -3, -1], [-394, -145, -42, -15, -3, -1], [-1183, -394, -145, -42, -15, -3, -1], [-3174, -1183, -394, -145, -42, -15, -3, -1]], ![[], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1], [-145, -42, -15, -3, -1], [-394, -145, -42, -15, -3, -1], [-1183, -394, -145, -42, -15, -3, -1], [-3174, -1183, -394, -145, -42, -15, -3, -1], [-8953, -3174, -1183, -394, -145, -42, -15, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 9, -33, -5, 46, -8, -21, 6, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 9, -33, -5, 46, -8, -21, 6, 3], [-3, 11, 31, -90, -48, 133, 22, -71, -3, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 9, -33, -5, 46, -8, -21, 6, 3], [-3, 11, 31, -90, -48, 133, 22, -71, -3, 15], [-15, 57, 146, -464, -165, 642, 13, -293, 19, 42]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 9, -33, -5, 46, -8, -21, 6, 3], [-3, 11, 31, -90, -48, 133, 22, -71, -3, 15], [-15, 57, 146, -464, -165, 642, 13, -293, 19, 42], [-42, 153, 435, -1240, -674, 1767, 306, -869, -41, 145]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 9, -33, -5, 46, -8, -21, 6, 3], [-3, 11, 31, -90, -48, 133, 22, -71, -3, 15], [-15, 57, 146, -464, -165, 642, 13, -293, 19, 42], [-42, 153, 435, -1240, -674, 1767, 306, -869, -41, 145], [-145, 538, 1458, -4350, -1965, 5996, 607, -2739, 1, 394]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 9, -33, -5, 46, -8, -21, 6, 3], [-3, 11, 31, -90, -48, 133, 22, -71, -3, 15], [-15, 57, 146, -464, -165, 642, 13, -293, 19, 42], [-42, 153, 435, -1240, -674, 1767, 306, -869, -41, 145], [-145, 538, 1458, -4350, -1965, 5996, 607, -2739, 1, 394], [-394, 1431, 4084, -11544, -6320, 16159, 2844, -7667, -375, 1183]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 9, -33, -5, 46, -8, -21, 6, 3], [-3, 11, 31, -90, -48, 133, 22, -71, -3, 15], [-15, 57, 146, -464, -165, 642, 13, -293, 19, 42], [-42, 153, 435, -1240, -674, 1767, 306, -869, -41, 145], [-145, 538, 1458, -4350, -1965, 5996, 607, -2739, 1, 394], [-394, 1431, 4084, -11544, -6320, 16159, 2844, -7667, -375, 1183], [-1183, 4338, 12078, -34955, -17459, 48098, 6695, -21999, -569, 3174]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 9, -33, -5, 46, -8, -21, 6, 3], [-3, 11, 31, -90, -48, 133, 22, -71, -3, 15], [-15, 57, 146, -464, -165, 642, 13, -293, 19, 42], [-42, 153, 435, -1240, -674, 1767, 306, -869, -41, 145], [-145, 538, 1458, -4350, -1965, 5996, 607, -2739, 1, 394], [-394, 1431, 4084, -11544, -6320, 16159, 2844, -7667, -375, 1183], [-1183, 4338, 12078, -34955, -17459, 48098, 6695, -21999, -569, 3174], [-3174, 11513, 32904, -92664, -50825, 128545, 22706, -59959, -2955, 8953]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 9, -33, -5, 46, -8, -21, 6, 3], [-3, 11, 31, -90, -48, 133, 22, -71, -3, 15], [-15, 57, 146, -464, -165, 642, 13, -293, 19, 42], [-42, 153, 435, -1240, -674, 1767, 306, -869, -41, 145], [-145, 538, 1458, -4350, -1965, 5996, 607, -2739, 1, 394], [-394, 1431, 4084, -11544, -6320, 16159, 2844, -7667, -375, 1183], [-1183, 4338, 12078, -34955, -17459, 48098, 6695, -21999, -569, 3174], [-3174, 11513, 32904, -92664, -50825, 128545, 22706, -59959, -2955, 8953], [-8953, 32638, 92090, -262545, -137429, 361013, 56921, -165307, -6241, 23904]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp41 : Fact (Nat.Prime 41) := fact_iff.2 (by norm_num)
instance hp36763421 : Fact (Nat.Prime 36763421) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 3]
  b' := [2, 3, 2, 3]
  k := [1]
  f := [3, 4, 9, 3, 7, 18, 4, -1, 3, 1]
  g := [4, 2, 4, 4, 1, 1]
  h := [4, 2, 4, 4, 1, 1]
  a := [4, 2, 0, 2, 1]
  b := [1, 4, 1, 3, 2, 3, 3, 1, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD41 : CertificateDedekindCriterionLists l 41 where
  n := 2
  a' := [12, 5, 17, 22, 27, 14, 15, 2]
  b' := [19, 35, 36, 30, 25, 40, 20, 12, 18]
  k := [32, 30, 20, 0, 12, 12, 3, 3, 1]
  f := [25, 23, 11, 18, 5, 17, 3, 32, 1, 1]
  g := [27, 24, 11, 20, 5, 17, 3, 35, 0, 1]
  h := [38, 1]
  a := [4, 2, 21, 30, 30, 10, 2, 28, 14]
  b := [10, 39, 22, 31, 10, 29, 12, 40, 27]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD36763421 : CertificateDedekindCriterionLists l 36763421 where
  n := 2
  a' := [24176425, 35577699, 22064603, 18051091, 24923219, 13942684, 36030891, 8768501]
  b' := [34776483, 5134431, 12440719, 30761153, 16616265, 34847456, 21022468, 15891258, 27619494]
  k := [4869070, 6229875, 21523167, 16915010, 22065894, 12724936, 26734404, 7961849, 1]
  f := [29280879, 9664642, 21029306, 6801796, 24728748, 8735292, 5489439, 4396635, 3549849, 1]
  g := [32836588, 10838262, 23582989, 7627768, 27731671, 9796057, 6156046, 4930538, 3980923, 1]
  h := [32782495, 1]
  a := [29597147, 2805972, 4549828, 1836567, 17566415, 23865746, 20472442, 12981785, 22673827]
  b := [1003364, 30735625, 7904805, 14305707, 32975441, 7757758, 23924477, 14157669, 14089594]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 41, 36763421]
  exp := ![1, 1, 1]
  pdgood := [5, 41, 36763421]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp41.out
    exact hp36763421.out
  a := [-50592405751, -329838769896, 906542616907, 1139913948382, -1826308031484, -993161337732, 968740529090, 220893405682, -148839577460]
  b := [-14532226764, 33527733715, 159759922936, -258583622577, -299696101357, 306958108666, 164338720146, -120164005808, -26554527892, 14883957746]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 41 T_ofList CD41
    exact satisfiesDedekindCriterion_of_certificate_lists T l 36763421 T_ofList CD36763421

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

end VoightMaximalOrderD10R369

namespace VoightMaximalOrderD10R372

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4721262565625, [-1, -2, 12, 23, -27, -35, 25, 16, -9, -2, 1], 1⟩
local notation "l" => [-1, -2, 12, 23, -27, -35, 25, 16, -9, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -23, 27, 35, -25, -16, 9, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -23, 27, 35, -25, -16, 9, 2], ![2, 5, -22, -58, 31, 97, -15, -57, 2, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -23, 27, 35, -25, -16, 9, 2], ![2, 5, -22, -58, 31, 97, -15, -57, 2, 13], ![13, 28, -151, -321, 293, 486, -228, -223, 60, 28]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -23, 27, 35, -25, -16, 9, 2], ![2, 5, -22, -58, 31, 97, -15, -57, 2, 13], ![13, 28, -151, -321, 293, 486, -228, -223, 60, 28], ![28, 69, -308, -795, 435, 1273, -214, -676, 29, 116]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -23, 27, 35, -25, -16, 9, 2], ![2, 5, -22, -58, 31, 97, -15, -57, 2, 13], ![13, 28, -151, -321, 293, 486, -228, -223, 60, 28], ![28, 69, -308, -795, 435, 1273, -214, -676, 29, 116], ![116, 260, -1323, -2976, 2337, 4495, -1627, -2070, 368, 261]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -23, 27, 35, -25, -16, 9, 2], ![2, 5, -22, -58, 31, 97, -15, -57, 2, 13], ![13, 28, -151, -321, 293, 486, -228, -223, 60, 28], ![28, 69, -308, -795, 435, 1273, -214, -676, 29, 116], ![116, 260, -1323, -2976, 2337, 4495, -1627, -2070, 368, 261], ![261, 638, -2872, -7326, 4071, 11472, -2030, -5803, 279, 890]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -23, 27, 35, -25, -16, 9, 2], ![2, 5, -22, -58, 31, 97, -15, -57, 2, 13], ![13, 28, -151, -321, 293, 486, -228, -223, 60, 28], ![28, 69, -308, -795, 435, 1273, -214, -676, 29, 116], ![116, 260, -1323, -2976, 2337, 4495, -1627, -2070, 368, 261], ![261, 638, -2872, -7326, 4071, 11472, -2030, -5803, 279, 890], ![890, 2041, -10042, -23342, 16704, 35221, -10778, -16270, 2207, 2059]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -23, 27, 35, -25, -16, 9, 2], ![2, 5, -22, -58, 31, 97, -15, -57, 2, 13], ![13, 28, -151, -321, 293, 486, -228, -223, 60, 28], ![28, 69, -308, -795, 435, 1273, -214, -676, 29, 116], ![116, 260, -1323, -2976, 2337, 4495, -1627, -2070, 368, 261], ![261, 638, -2872, -7326, 4071, 11472, -2030, -5803, 279, 890], ![890, 2041, -10042, -23342, 16704, 35221, -10778, -16270, 2207, 2059], ![2059, 5008, -22667, -57399, 32251, 88769, -16254, -43722, 2261, 6325]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -23, 27, 35, -25, -16, 9, 2], ![2, 5, -22, -58, 31, 97, -15, -57, 2, 13], ![13, 28, -151, -321, 293, 486, -228, -223, 60, 28], ![28, 69, -308, -795, 435, 1273, -214, -676, 29, 116], ![116, 260, -1323, -2976, 2337, 4495, -1627, -2070, 368, 261], ![261, 638, -2872, -7326, 4071, 11472, -2030, -5803, 279, 890], ![890, 2041, -10042, -23342, 16704, 35221, -10778, -16270, 2207, 2059], ![2059, 5008, -22667, -57399, 32251, 88769, -16254, -43722, 2261, 6325], ![6325, 14709, -70892, -168142, 113376, 253626, -69356, -117454, 13203, 14911]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-28, -13, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-28, -13, -2, -1], [-116, -28, -13, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-28, -13, -2, -1], [-116, -28, -13, -2, -1], [-261, -116, -28, -13, -2, -1]], ![[], [], [], [-1], [-2, -1], [-13, -2, -1], [-28, -13, -2, -1], [-116, -28, -13, -2, -1], [-261, -116, -28, -13, -2, -1], [-890, -261, -116, -28, -13, -2, -1]], ![[], [], [-1], [-2, -1], [-13, -2, -1], [-28, -13, -2, -1], [-116, -28, -13, -2, -1], [-261, -116, -28, -13, -2, -1], [-890, -261, -116, -28, -13, -2, -1], [-2059, -890, -261, -116, -28, -13, -2, -1]], ![[], [-1], [-2, -1], [-13, -2, -1], [-28, -13, -2, -1], [-116, -28, -13, -2, -1], [-261, -116, -28, -13, -2, -1], [-890, -261, -116, -28, -13, -2, -1], [-2059, -890, -261, -116, -28, -13, -2, -1], [-6325, -2059, -890, -261, -116, -28, -13, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -23, 27, 35, -25, -16, 9, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -23, 27, 35, -25, -16, 9, 2], [2, 5, -22, -58, 31, 97, -15, -57, 2, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -23, 27, 35, -25, -16, 9, 2], [2, 5, -22, -58, 31, 97, -15, -57, 2, 13], [13, 28, -151, -321, 293, 486, -228, -223, 60, 28]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -23, 27, 35, -25, -16, 9, 2], [2, 5, -22, -58, 31, 97, -15, -57, 2, 13], [13, 28, -151, -321, 293, 486, -228, -223, 60, 28], [28, 69, -308, -795, 435, 1273, -214, -676, 29, 116]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -23, 27, 35, -25, -16, 9, 2], [2, 5, -22, -58, 31, 97, -15, -57, 2, 13], [13, 28, -151, -321, 293, 486, -228, -223, 60, 28], [28, 69, -308, -795, 435, 1273, -214, -676, 29, 116], [116, 260, -1323, -2976, 2337, 4495, -1627, -2070, 368, 261]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -23, 27, 35, -25, -16, 9, 2], [2, 5, -22, -58, 31, 97, -15, -57, 2, 13], [13, 28, -151, -321, 293, 486, -228, -223, 60, 28], [28, 69, -308, -795, 435, 1273, -214, -676, 29, 116], [116, 260, -1323, -2976, 2337, 4495, -1627, -2070, 368, 261], [261, 638, -2872, -7326, 4071, 11472, -2030, -5803, 279, 890]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -23, 27, 35, -25, -16, 9, 2], [2, 5, -22, -58, 31, 97, -15, -57, 2, 13], [13, 28, -151, -321, 293, 486, -228, -223, 60, 28], [28, 69, -308, -795, 435, 1273, -214, -676, 29, 116], [116, 260, -1323, -2976, 2337, 4495, -1627, -2070, 368, 261], [261, 638, -2872, -7326, 4071, 11472, -2030, -5803, 279, 890], [890, 2041, -10042, -23342, 16704, 35221, -10778, -16270, 2207, 2059]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -23, 27, 35, -25, -16, 9, 2], [2, 5, -22, -58, 31, 97, -15, -57, 2, 13], [13, 28, -151, -321, 293, 486, -228, -223, 60, 28], [28, 69, -308, -795, 435, 1273, -214, -676, 29, 116], [116, 260, -1323, -2976, 2337, 4495, -1627, -2070, 368, 261], [261, 638, -2872, -7326, 4071, 11472, -2030, -5803, 279, 890], [890, 2041, -10042, -23342, 16704, 35221, -10778, -16270, 2207, 2059], [2059, 5008, -22667, -57399, 32251, 88769, -16254, -43722, 2261, 6325]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -23, 27, 35, -25, -16, 9, 2], [2, 5, -22, -58, 31, 97, -15, -57, 2, 13], [13, 28, -151, -321, 293, 486, -228, -223, 60, 28], [28, 69, -308, -795, 435, 1273, -214, -676, 29, 116], [116, 260, -1323, -2976, 2337, 4495, -1627, -2070, 368, 261], [261, 638, -2872, -7326, 4071, 11472, -2030, -5803, 279, 890], [890, 2041, -10042, -23342, 16704, 35221, -10778, -16270, 2207, 2059], [2059, 5008, -22667, -57399, 32251, 88769, -16254, -43722, 2261, 6325], [6325, 14709, -70892, -168142, 113376, 253626, -69356, -117454, 13203, 14911]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp2539 : Fact (Nat.Prime 2539) := fact_iff.2 (by norm_num)
instance hp595039 : Fact (Nat.Prime 595039) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 0, 4]
  b' := [2, 1, 4, 4, 1]
  k := [1]
  f := [2, 4, 3, -1, 12, 13, 1, -2, 5, 2]
  g := [3, 3, 3, 0, 4, 1]
  h := [3, 3, 3, 0, 4, 1]
  a := [1, 1, 0, 4, 2]
  b := [3, 0, 3, 2, 4, 3, 2, 3, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2539 : CertificateDedekindCriterionLists l 2539 where
  n := 2
  a' := [1768, 842, 1910, 545, 484, 634, 1047, 509]
  b' := [1236, 769, 1738, 627, 427, 1251, 1885, 989, 1354]
  k := [489, 1398, 1224, 1853, 1120, 107, 955, 583, 1]
  f := [162, 136, 530, 500, 687, 601, 512, 697, 601, 1]
  g := [421, 353, 1377, 1298, 1784, 1560, 1329, 1810, 1560, 1]
  h := [977, 1]
  a := [607, 2293, 1606, 2166, 1185, 1506, 711, 213, 1800]
  b := [659, 124, 1534, 1364, 1781, 1600, 2121, 2006, 739]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD595039 : CertificateDedekindCriterionLists l 595039 where
  n := 2
  a' := [156185, 77711, 454862, 135560, 28467, 20343, 577047, 396941]
  b' := [449625, 184286, 407023, 364418, 125024, 48329, 10860, 230596, 484819]
  k := [255230, 302391, 501328, 432191, 19556, 523730, 65223, 211894, 1]
  f := [361094, 23312, 468267, 140051, 360754, 370160, 382398, 448901, 87083, 1]
  g := [439315, 28361, 569704, 170388, 438901, 450344, 465233, 546142, 105946, 1]
  h := [489091, 1]
  a := [241964, 446027, 399585, 376041, 235648, 582178, 459816, 428477, 9989]
  b := [5887, 222085, 92200, 336226, 111951, 403500, 540128, 556745, 585050]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 2539, 595039]
  exp := ![1, 1, 1]
  pdgood := [5, 2539, 595039]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp2539.out
    exact hp595039.out
  a := [2323809204003, -34312895256052, 12947328812956, 90797971186808, -42998406133758, -58112740340142, 27475050458256, 9294888055184, -4290179850380]
  b := [-1165681612054, 844459079375, 11699579410229, -5024281884536, -17844057133888, 7734320535444, 8141949366999, -3488286132404, -1015292402526, 429017985038]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2539 T_ofList CD2539
    exact satisfiesDedekindCriterion_of_certificate_lists T l 595039 T_ofList CD595039

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

end VoightMaximalOrderD10R372

end TraceEuclidean
