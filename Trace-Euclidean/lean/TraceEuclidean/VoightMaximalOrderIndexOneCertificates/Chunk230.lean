import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk226
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

namespace VoightMaximalOrderD10R726

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7186256755712, [-5, 16, 31, -46, -60, 38, 47, -8, -13, 0, 1], 1⟩
local notation "l" => [-5, 16, 31, -46, -60, 38, 47, -8, -13, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -16, -31, 46, 60, -38, -47, 8, 13, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -16, -31, 46, 60, -38, -47, 8, 13, 0], ![0, 5, -16, -31, 46, 60, -38, -47, 8, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -16, -31, 46, 60, -38, -47, 8, 13, 0], ![0, 5, -16, -31, 46, 60, -38, -47, 8, 13], ![65, -208, -398, 582, 749, -448, -551, 66, 122, 8]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -16, -31, 46, 60, -38, -47, 8, 13, 0], ![0, 5, -16, -31, 46, 60, -38, -47, 8, 13], ![65, -208, -398, 582, 749, -448, -551, 66, 122, 8], ![40, -63, -456, -30, 1062, 445, -824, -487, 170, 122]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -16, -31, 46, 60, -38, -47, 8, 13, 0], ![0, 5, -16, -31, 46, 60, -38, -47, 8, 13], ![65, -208, -398, 582, 749, -448, -551, 66, 122, 8], ![40, -63, -456, -30, 1062, 445, -824, -487, 170, 122], ![610, -1912, -3845, 5156, 7290, -3574, -5289, 152, 1099, 170]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -16, -31, 46, 60, -38, -47, 8, 13, 0], ![0, 5, -16, -31, 46, 60, -38, -47, 8, 13], ![65, -208, -398, 582, 749, -448, -551, 66, 122, 8], ![40, -63, -456, -30, 1062, 445, -824, -487, 170, 122], ![610, -1912, -3845, 5156, 7290, -3574, -5289, 152, 1099, 170], ![850, -2110, -7182, 3975, 15356, 830, -11564, -3929, 2362, 1099]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -16, -31, 46, 60, -38, -47, 8, 13, 0], ![0, 5, -16, -31, 46, 60, -38, -47, 8, 13], ![65, -208, -398, 582, 749, -448, -551, 66, 122, 8], ![40, -63, -456, -30, 1062, 445, -824, -487, 170, 122], ![610, -1912, -3845, 5156, 7290, -3574, -5289, 152, 1099, 170], ![850, -2110, -7182, 3975, 15356, 830, -11564, -3929, 2362, 1099], ![5495, -16734, -36179, 43372, 69915, -26406, -50823, -2772, 10358, 2362]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -16, -31, 46, 60, -38, -47, 8, 13, 0], ![0, 5, -16, -31, 46, 60, -38, -47, 8, 13], ![65, -208, -398, 582, 749, -448, -551, 66, 122, 8], ![40, -63, -456, -30, 1062, 445, -824, -487, 170, 122], ![610, -1912, -3845, 5156, 7290, -3574, -5289, 152, 1099, 170], ![850, -2110, -7182, 3975, 15356, 830, -11564, -3929, 2362, 1099], ![5495, -16734, -36179, 43372, 69915, -26406, -50823, -2772, 10358, 2362], ![11810, -32297, -89956, 72473, 185092, -19841, -137420, -31927, 27934, 10358]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, -16, -31, 46, 60, -38, -47, 8, 13, 0], ![0, 5, -16, -31, 46, 60, -38, -47, 8, 13], ![65, -208, -398, 582, 749, -448, -551, 66, 122, 8], ![40, -63, -456, -30, 1062, 445, -824, -487, 170, 122], ![610, -1912, -3845, 5156, 7290, -3574, -5289, 152, 1099, 170], ![850, -2110, -7182, 3975, 15356, 830, -11564, -3929, 2362, 1099], ![5495, -16734, -36179, 43372, 69915, -26406, -50823, -2772, 10358, 2362], ![11810, -32297, -89956, 72473, 185092, -19841, -137420, -31927, 27934, 10358], ![51790, -153918, -353395, 386512, 693953, -208512, -506667, -54556, 102727, 27934]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-13, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-13, 0, -1], [-8, -13, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-13, 0, -1], [-8, -13, 0, -1], [-122, -8, -13, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-13, 0, -1], [-8, -13, 0, -1], [-122, -8, -13, 0, -1], [-170, -122, -8, -13, 0, -1]], ![[], [], [], [-1], [0, -1], [-13, 0, -1], [-8, -13, 0, -1], [-122, -8, -13, 0, -1], [-170, -122, -8, -13, 0, -1], [-1099, -170, -122, -8, -13, 0, -1]], ![[], [], [-1], [0, -1], [-13, 0, -1], [-8, -13, 0, -1], [-122, -8, -13, 0, -1], [-170, -122, -8, -13, 0, -1], [-1099, -170, -122, -8, -13, 0, -1], [-2362, -1099, -170, -122, -8, -13, 0, -1]], ![[], [-1], [0, -1], [-13, 0, -1], [-8, -13, 0, -1], [-122, -8, -13, 0, -1], [-170, -122, -8, -13, 0, -1], [-1099, -170, -122, -8, -13, 0, -1], [-2362, -1099, -170, -122, -8, -13, 0, -1], [-10358, -2362, -1099, -170, -122, -8, -13, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -16, -31, 46, 60, -38, -47, 8, 13, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -16, -31, 46, 60, -38, -47, 8, 13, 0], [0, 5, -16, -31, 46, 60, -38, -47, 8, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -16, -31, 46, 60, -38, -47, 8, 13, 0], [0, 5, -16, -31, 46, 60, -38, -47, 8, 13], [65, -208, -398, 582, 749, -448, -551, 66, 122, 8]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -16, -31, 46, 60, -38, -47, 8, 13, 0], [0, 5, -16, -31, 46, 60, -38, -47, 8, 13], [65, -208, -398, 582, 749, -448, -551, 66, 122, 8], [40, -63, -456, -30, 1062, 445, -824, -487, 170, 122]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -16, -31, 46, 60, -38, -47, 8, 13, 0], [0, 5, -16, -31, 46, 60, -38, -47, 8, 13], [65, -208, -398, 582, 749, -448, -551, 66, 122, 8], [40, -63, -456, -30, 1062, 445, -824, -487, 170, 122], [610, -1912, -3845, 5156, 7290, -3574, -5289, 152, 1099, 170]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -16, -31, 46, 60, -38, -47, 8, 13, 0], [0, 5, -16, -31, 46, 60, -38, -47, 8, 13], [65, -208, -398, 582, 749, -448, -551, 66, 122, 8], [40, -63, -456, -30, 1062, 445, -824, -487, 170, 122], [610, -1912, -3845, 5156, 7290, -3574, -5289, 152, 1099, 170], [850, -2110, -7182, 3975, 15356, 830, -11564, -3929, 2362, 1099]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -16, -31, 46, 60, -38, -47, 8, 13, 0], [0, 5, -16, -31, 46, 60, -38, -47, 8, 13], [65, -208, -398, 582, 749, -448, -551, 66, 122, 8], [40, -63, -456, -30, 1062, 445, -824, -487, 170, 122], [610, -1912, -3845, 5156, 7290, -3574, -5289, 152, 1099, 170], [850, -2110, -7182, 3975, 15356, 830, -11564, -3929, 2362, 1099], [5495, -16734, -36179, 43372, 69915, -26406, -50823, -2772, 10358, 2362]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -16, -31, 46, 60, -38, -47, 8, 13, 0], [0, 5, -16, -31, 46, 60, -38, -47, 8, 13], [65, -208, -398, 582, 749, -448, -551, 66, 122, 8], [40, -63, -456, -30, 1062, 445, -824, -487, 170, 122], [610, -1912, -3845, 5156, 7290, -3574, -5289, 152, 1099, 170], [850, -2110, -7182, 3975, 15356, 830, -11564, -3929, 2362, 1099], [5495, -16734, -36179, 43372, 69915, -26406, -50823, -2772, 10358, 2362], [11810, -32297, -89956, 72473, 185092, -19841, -137420, -31927, 27934, 10358]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, -16, -31, 46, 60, -38, -47, 8, 13, 0], [0, 5, -16, -31, 46, 60, -38, -47, 8, 13], [65, -208, -398, 582, 749, -448, -551, 66, 122, 8], [40, -63, -456, -30, 1062, 445, -824, -487, 170, 122], [610, -1912, -3845, 5156, 7290, -3574, -5289, 152, 1099, 170], [850, -2110, -7182, 3975, 15356, 830, -11564, -3929, 2362, 1099], [5495, -16734, -36179, 43372, 69915, -26406, -50823, -2772, 10358, 2362], [11810, -32297, -89956, 72473, 185092, -19841, -137420, -31927, 27934, 10358], [51790, -153918, -353395, 386512, 693953, -208512, -506667, -54556, 102727, 27934]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp7017828863 : Fact (Nat.Prime 7017828863) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 1]
  b' := [0, 1, 1, 1]
  k := [1]
  f := [3, -7, -15, 24, 32, -17, -22, 5, 8, 1]
  g := [1, 1, 0, 1, 1, 1]
  h := [1, 1, 0, 1, 1, 1]
  a := [0, 0, 1, 1]
  b := [1, 1, 0, 1, 1, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD7017828863 : CertificateDedekindCriterionLists l 7017828863 where
  n := 2
  a' := [3975473140, 1528330686, 2056041894, 2565096041, 1187342470, 6353263831, 3116410455, 731892908]
  b' := [4030805046, 4279406845, 5587046577, 1346182793, 3452602138, 5503394144, 4966675691, 60573745, 3037713616]
  k := [597728739, 2739895691, 1104091374, 1146245999, 6351658217, 4005047796, 4998026637, 5647046058, 1]
  f := [1744547181, 1609958389, 3616694779, 1788597496, 3076291054, 343965848, 115310012, 2393815984, 1687518939, 1]
  g := [2918941547, 2693750264, 6051381566, 2992645654, 5147188832, 575516795, 192934412, 4005285158, 2823523029, 1]
  h := [4194305834, 1]
  a := [6975386786, 2842972489, 2298406166, 1465234731, 2210684842, 2288699764, 484302105, 3492055952, 2423519682]
  b := [3166078335, 1258664440, 5277227320, 2714137744, 6309606239, 715751604, 5941215142, 3119702193, 4594309181]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![2, 7017828863]
  exp := ![1, 1]
  pdgood := [2, 7017828863]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp7017828863.out
  a := [-153406416038, -408219671688, 1940436455764, 660028912650, -3436315116016, -682350524964, 1522609341252, 199066433730, -176403341430]
  b := [-47062276404, 208204089701, 99128013612, -678590177910, -75936701076, 641929531084, 77655523323, -198125802897, -19906643373, 17640334143]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7017828863 T_ofList CD7017828863

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

end VoightMaximalOrderD10R726

namespace VoightMaximalOrderD10R728

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7199495659072, [2, -4, -14, 30, 21, -58, 5, 26, -7, -3, 1], 1⟩
local notation "l" => [2, -4, -14, 30, 21, -58, 5, 26, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-2, 4, 14, -30, -21, 58, -5, -26, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-2, 4, 14, -30, -21, 58, -5, -26, 7, 3], ![-6, 10, 46, -76, -93, 153, 43, -83, -5, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-2, 4, 14, -30, -21, 58, -5, -26, 7, 3], ![-6, 10, 46, -76, -93, 153, 43, -83, -5, 16], ![-32, 58, 234, -434, -412, 835, 73, -373, 29, 43]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-2, 4, 14, -30, -21, 58, -5, -26, 7, 3], ![-6, 10, 46, -76, -93, 153, 43, -83, -5, 16], ![-32, 58, 234, -434, -412, 835, 73, -373, 29, 43], ![-86, 140, 660, -1056, -1337, 2082, 620, -1045, -72, 158]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-2, 4, 14, -30, -21, 58, -5, -26, 7, 3], ![-6, 10, 46, -76, -93, 153, 43, -83, -5, 16], ![-32, 58, 234, -434, -412, 835, 73, -373, 29, 43], ![-86, 140, 660, -1056, -1337, 2082, 620, -1045, -72, 158], ![-316, 546, 2352, -4080, -4374, 7827, 1292, -3488, 61, 402]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-2, 4, 14, -30, -21, 58, -5, -26, 7, 3], ![-6, 10, 46, -76, -93, 153, 43, -83, -5, 16], ![-32, 58, 234, -434, -412, 835, 73, -373, 29, 43], ![-86, 140, 660, -1056, -1337, 2082, 620, -1045, -72, 158], ![-316, 546, 2352, -4080, -4374, 7827, 1292, -3488, 61, 402], ![-804, 1292, 6174, -9708, -12522, 18942, 5817, -9160, -674, 1267]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-2, 4, 14, -30, -21, 58, -5, -26, 7, 3], ![-6, 10, 46, -76, -93, 153, 43, -83, -5, 16], ![-32, 58, 234, -434, -412, 835, 73, -373, 29, 43], ![-86, 140, 660, -1056, -1337, 2082, 620, -1045, -72, 158], ![-316, 546, 2352, -4080, -4374, 7827, 1292, -3488, 61, 402], ![-804, 1292, 6174, -9708, -12522, 18942, 5817, -9160, -674, 1267], ![-2534, 4264, 19030, -31836, -36315, 60964, 12607, -27125, -291, 3127]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-2, 4, 14, -30, -21, 58, -5, -26, 7, 3], ![-6, 10, 46, -76, -93, 153, 43, -83, -5, 16], ![-32, 58, 234, -434, -412, 835, 73, -373, 29, 43], ![-86, 140, 660, -1056, -1337, 2082, 620, -1045, -72, 158], ![-316, 546, 2352, -4080, -4374, 7827, 1292, -3488, 61, 402], ![-804, 1292, 6174, -9708, -12522, 18942, 5817, -9160, -674, 1267], ![-2534, 4264, 19030, -31836, -36315, 60964, 12607, -27125, -291, 3127], ![-6254, 9974, 48042, -74780, -97503, 145051, 45329, -68695, -5236, 9090]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-2, 4, 14, -30, -21, 58, -5, -26, 7, 3], ![-6, 10, 46, -76, -93, 153, 43, -83, -5, 16], ![-32, 58, 234, -434, -412, 835, 73, -373, 29, 43], ![-86, 140, 660, -1056, -1337, 2082, 620, -1045, -72, 158], ![-316, 546, 2352, -4080, -4374, 7827, 1292, -3488, 61, 402], ![-804, 1292, 6174, -9708, -12522, 18942, 5817, -9160, -674, 1267], ![-2534, 4264, 19030, -31836, -36315, 60964, 12607, -27125, -291, 3127], ![-6254, 9974, 48042, -74780, -97503, 145051, 45329, -68695, -5236, 9090], ![-18180, 30106, 137234, -224658, -265670, 429717, 99601, -191011, -5065, 22034]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1], [-158, -43, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1], [-158, -43, -16, -3, -1], [-402, -158, -43, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1], [-158, -43, -16, -3, -1], [-402, -158, -43, -16, -3, -1], [-1267, -402, -158, -43, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1], [-158, -43, -16, -3, -1], [-402, -158, -43, -16, -3, -1], [-1267, -402, -158, -43, -16, -3, -1], [-3127, -1267, -402, -158, -43, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-43, -16, -3, -1], [-158, -43, -16, -3, -1], [-402, -158, -43, -16, -3, -1], [-1267, -402, -158, -43, -16, -3, -1], [-3127, -1267, -402, -158, -43, -16, -3, -1], [-9090, -3127, -1267, -402, -158, -43, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-2, 4, 14, -30, -21, 58, -5, -26, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-2, 4, 14, -30, -21, 58, -5, -26, 7, 3], [-6, 10, 46, -76, -93, 153, 43, -83, -5, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-2, 4, 14, -30, -21, 58, -5, -26, 7, 3], [-6, 10, 46, -76, -93, 153, 43, -83, -5, 16], [-32, 58, 234, -434, -412, 835, 73, -373, 29, 43]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-2, 4, 14, -30, -21, 58, -5, -26, 7, 3], [-6, 10, 46, -76, -93, 153, 43, -83, -5, 16], [-32, 58, 234, -434, -412, 835, 73, -373, 29, 43], [-86, 140, 660, -1056, -1337, 2082, 620, -1045, -72, 158]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-2, 4, 14, -30, -21, 58, -5, -26, 7, 3], [-6, 10, 46, -76, -93, 153, 43, -83, -5, 16], [-32, 58, 234, -434, -412, 835, 73, -373, 29, 43], [-86, 140, 660, -1056, -1337, 2082, 620, -1045, -72, 158], [-316, 546, 2352, -4080, -4374, 7827, 1292, -3488, 61, 402]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-2, 4, 14, -30, -21, 58, -5, -26, 7, 3], [-6, 10, 46, -76, -93, 153, 43, -83, -5, 16], [-32, 58, 234, -434, -412, 835, 73, -373, 29, 43], [-86, 140, 660, -1056, -1337, 2082, 620, -1045, -72, 158], [-316, 546, 2352, -4080, -4374, 7827, 1292, -3488, 61, 402], [-804, 1292, 6174, -9708, -12522, 18942, 5817, -9160, -674, 1267]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-2, 4, 14, -30, -21, 58, -5, -26, 7, 3], [-6, 10, 46, -76, -93, 153, 43, -83, -5, 16], [-32, 58, 234, -434, -412, 835, 73, -373, 29, 43], [-86, 140, 660, -1056, -1337, 2082, 620, -1045, -72, 158], [-316, 546, 2352, -4080, -4374, 7827, 1292, -3488, 61, 402], [-804, 1292, 6174, -9708, -12522, 18942, 5817, -9160, -674, 1267], [-2534, 4264, 19030, -31836, -36315, 60964, 12607, -27125, -291, 3127]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-2, 4, 14, -30, -21, 58, -5, -26, 7, 3], [-6, 10, 46, -76, -93, 153, 43, -83, -5, 16], [-32, 58, 234, -434, -412, 835, 73, -373, 29, 43], [-86, 140, 660, -1056, -1337, 2082, 620, -1045, -72, 158], [-316, 546, 2352, -4080, -4374, 7827, 1292, -3488, 61, 402], [-804, 1292, 6174, -9708, -12522, 18942, 5817, -9160, -674, 1267], [-2534, 4264, 19030, -31836, -36315, 60964, 12607, -27125, -291, 3127], [-6254, 9974, 48042, -74780, -97503, 145051, 45329, -68695, -5236, 9090]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-2, 4, 14, -30, -21, 58, -5, -26, 7, 3], [-6, 10, 46, -76, -93, 153, 43, -83, -5, 16], [-32, 58, 234, -434, -412, 835, 73, -373, 29, 43], [-86, 140, 660, -1056, -1337, 2082, 620, -1045, -72, 158], [-316, 546, 2352, -4080, -4374, 7827, 1292, -3488, 61, 402], [-804, 1292, 6174, -9708, -12522, 18942, 5817, -9160, -674, 1267], [-2534, 4264, 19030, -31836, -36315, 60964, 12607, -27125, -291, 3127], [-6254, 9974, 48042, -74780, -97503, 145051, 45329, -68695, -5236, 9090], [-18180, 30106, 137234, -224658, -265670, 429717, 99601, -191011, -5065, 22034]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp323243 : Fact (Nat.Prime 323243) := fact_iff.2 (by norm_num)
instance hp348011 : Fact (Nat.Prime 348011) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 4
  a' := [0, 0, 1]
  b' := [1, 0, 1, 1]
  k := [1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1]
  f := [-1, 2, 7, -15, -10, 29, -2, -13, 4, 2]
  g := [0, 1, 0, 1, 0, 1, 1, 1]
  h := [0, 0, 0, 1]
  a := [1, 1, 1]
  b := [1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD323243 : CertificateDedekindCriterionLists l 323243 where
  n := 2
  a' := [99884, 107526, 237628, 122947, 35684, 30036, 33348, 56694]
  b' := [146888, 125495, 289674, 180832, 172983, 184804, 180721, 24059, 209196]
  k := [148070, 146386, 39203, 286813, 209985, 215392, 292453, 189477, 1]
  f := [191683, 197472, 82169, 107374, 210905, 213837, 222790, 154273, 66971, 1]
  g := [271157, 279345, 116236, 151892, 298348, 302495, 315160, 218235, 94737, 1]
  h := [228503, 1]
  a := [249225, 110000, 61224, 126132, 266051, 201490, 81984, 107144, 212744]
  b := [107092, 134620, 240690, 309427, 231071, 34803, 288399, 178, 110499]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD348011 : CertificateDedekindCriterionLists l 348011 where
  n := 2
  a' := [236707, 133522, 134072, 288155, 199389, 123888, 240264, 200274]
  b' := [91499, 243167, 122371, 190765, 158836, 120285, 124254, 118676, 93751]
  k := [180459, 297993, 337076, 24263, 185267, 156709, 64376, 323635, 1]
  f := [137018, 1800, 81763, 18603, 31671, 111890, 138056, 111095, 86575, 1]
  g := [256100, 3363, 152823, 34770, 59196, 209133, 258039, 207646, 161816, 1]
  h := [186192, 1]
  a := [334868, 327823, 17815, 109332, 99617, 198869, 124728, 65100, 187419]
  b := [257033, 344855, 43225, 341618, 230326, 125325, 284897, 122159, 160592]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 323243, 348011]
  exp := ![2, 1, 1]
  pdgood := [2, 323243, 348011]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp323243.out
    exact hp348011.out
  a := [-143132655351758, -1294462848247544, 596496871368840, 4225309824673230, -1829667442141390, -2635813954338204, 1183107672370235, 390398934256460, -176916104241300]
  b := [-71678819795552, -2347030203150, 497331343685247, -66099706378202, -887720419511333, 279722464904876, 388059606470497, -145697258246657, -44347376552885, 17691610424130]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 323243 T_ofList CD323243
    exact satisfiesDedekindCriterion_of_certificate_lists T l 348011 T_ofList CD348011

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

end VoightMaximalOrderD10R728

namespace VoightMaximalOrderD10R733

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7234594161664, [1, -14, 7, 48, -24, -50, 25, 18, -9, -2, 1], 1⟩
local notation "l" => [1, -14, 7, 48, -24, -50, 25, 18, -9, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, -7, -48, 24, 50, -25, -18, 9, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, -7, -48, 24, 50, -25, -18, 9, 2], ![-2, 27, 0, -103, 0, 124, 0, -61, 0, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, -7, -48, 24, 50, -25, -18, 9, 2], ![-2, 27, 0, -103, 0, 124, 0, -61, 0, 13], ![-13, 180, -64, -624, 209, 650, -201, -234, 56, 26]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, -7, -48, 24, 50, -25, -18, 9, 2], ![-2, 27, 0, -103, 0, 124, 0, -61, 0, 13], ![-13, 180, -64, -624, 209, 650, -201, -234, 56, 26], ![-26, 351, -2, -1312, 0, 1509, 0, -669, 0, 108]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, -7, -48, 24, 50, -25, -18, 9, 2], ![-2, 27, 0, -103, 0, 124, 0, -61, 0, 13], ![-13, 180, -64, -624, 209, 650, -201, -234, 56, 26], ![-26, 351, -2, -1312, 0, 1509, 0, -669, 0, 108], ![-108, 1486, -405, -5186, 1280, 5400, -1191, -1944, 303, 216]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, -7, -48, 24, 50, -25, -18, 9, 2], ![-2, 27, 0, -103, 0, 124, 0, -61, 0, 13], ![-13, 180, -64, -624, 209, 650, -201, -234, 56, 26], ![-26, 351, -2, -1312, 0, 1509, 0, -669, 0, 108], ![-108, 1486, -405, -5186, 1280, 5400, -1191, -1944, 303, 216], ![-216, 2916, -26, -10773, -2, 12080, 0, -5079, 0, 735]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, -7, -48, 24, 50, -25, -18, 9, 2], ![-2, 27, 0, -103, 0, 124, 0, -61, 0, 13], ![-13, 180, -64, -624, 209, 650, -201, -234, 56, 26], ![-26, 351, -2, -1312, 0, 1509, 0, -669, 0, 108], ![-108, 1486, -405, -5186, 1280, 5400, -1191, -1944, 303, 216], ![-216, 2916, -26, -10773, -2, 12080, 0, -5079, 0, 735], ![-735, 10074, -2229, -35306, 6867, 36748, -6295, -13230, 1536, 1470]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, -7, -48, 24, 50, -25, -18, 9, 2], ![-2, 27, 0, -103, 0, 124, 0, -61, 0, 13], ![-13, 180, -64, -624, 209, 650, -201, -234, 56, 26], ![-26, 351, -2, -1312, 0, 1509, 0, -669, 0, 108], ![-108, 1486, -405, -5186, 1280, 5400, -1191, -1944, 303, 216], ![-216, 2916, -26, -10773, -2, 12080, 0, -5079, 0, 735], ![-735, 10074, -2229, -35306, 6867, 36748, -6295, -13230, 1536, 1470], ![-1470, 19845, -216, -72789, -26, 80367, -2, -32755, 0, 4476]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 14, -7, -48, 24, 50, -25, -18, 9, 2], ![-2, 27, 0, -103, 0, 124, 0, -61, 0, 13], ![-13, 180, -64, -624, 209, 650, -201, -234, 56, 26], ![-26, 351, -2, -1312, 0, 1509, 0, -669, 0, 108], ![-108, 1486, -405, -5186, 1280, 5400, -1191, -1944, 303, 216], ![-216, 2916, -26, -10773, -2, 12080, 0, -5079, 0, 735], ![-735, 10074, -2229, -35306, 6867, 36748, -6295, -13230, 1536, 1470], ![-1470, 19845, -216, -72789, -26, 80367, -2, -32755, 0, 4476], ![-4476, 61194, -11487, -215064, 34635, 223774, -31533, -80570, 7529, 8952]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-26, -13, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-26, -13, -2, -1], [-108, -26, -13, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-26, -13, -2, -1], [-108, -26, -13, -2, -1], [-216, -108, -26, -13, -2, -1]], ![[], [], [], [-1], [-2, -1], [-13, -2, -1], [-26, -13, -2, -1], [-108, -26, -13, -2, -1], [-216, -108, -26, -13, -2, -1], [-735, -216, -108, -26, -13, -2, -1]], ![[], [], [-1], [-2, -1], [-13, -2, -1], [-26, -13, -2, -1], [-108, -26, -13, -2, -1], [-216, -108, -26, -13, -2, -1], [-735, -216, -108, -26, -13, -2, -1], [-1470, -735, -216, -108, -26, -13, -2, -1]], ![[], [-1], [-2, -1], [-13, -2, -1], [-26, -13, -2, -1], [-108, -26, -13, -2, -1], [-216, -108, -26, -13, -2, -1], [-735, -216, -108, -26, -13, -2, -1], [-1470, -735, -216, -108, -26, -13, -2, -1], [-4476, -1470, -735, -216, -108, -26, -13, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, -7, -48, 24, 50, -25, -18, 9, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, -7, -48, 24, 50, -25, -18, 9, 2], [-2, 27, 0, -103, 0, 124, 0, -61, 0, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, -7, -48, 24, 50, -25, -18, 9, 2], [-2, 27, 0, -103, 0, 124, 0, -61, 0, 13], [-13, 180, -64, -624, 209, 650, -201, -234, 56, 26]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, -7, -48, 24, 50, -25, -18, 9, 2], [-2, 27, 0, -103, 0, 124, 0, -61, 0, 13], [-13, 180, -64, -624, 209, 650, -201, -234, 56, 26], [-26, 351, -2, -1312, 0, 1509, 0, -669, 0, 108]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, -7, -48, 24, 50, -25, -18, 9, 2], [-2, 27, 0, -103, 0, 124, 0, -61, 0, 13], [-13, 180, -64, -624, 209, 650, -201, -234, 56, 26], [-26, 351, -2, -1312, 0, 1509, 0, -669, 0, 108], [-108, 1486, -405, -5186, 1280, 5400, -1191, -1944, 303, 216]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, -7, -48, 24, 50, -25, -18, 9, 2], [-2, 27, 0, -103, 0, 124, 0, -61, 0, 13], [-13, 180, -64, -624, 209, 650, -201, -234, 56, 26], [-26, 351, -2, -1312, 0, 1509, 0, -669, 0, 108], [-108, 1486, -405, -5186, 1280, 5400, -1191, -1944, 303, 216], [-216, 2916, -26, -10773, -2, 12080, 0, -5079, 0, 735]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, -7, -48, 24, 50, -25, -18, 9, 2], [-2, 27, 0, -103, 0, 124, 0, -61, 0, 13], [-13, 180, -64, -624, 209, 650, -201, -234, 56, 26], [-26, 351, -2, -1312, 0, 1509, 0, -669, 0, 108], [-108, 1486, -405, -5186, 1280, 5400, -1191, -1944, 303, 216], [-216, 2916, -26, -10773, -2, 12080, 0, -5079, 0, 735], [-735, 10074, -2229, -35306, 6867, 36748, -6295, -13230, 1536, 1470]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, -7, -48, 24, 50, -25, -18, 9, 2], [-2, 27, 0, -103, 0, 124, 0, -61, 0, 13], [-13, 180, -64, -624, 209, 650, -201, -234, 56, 26], [-26, 351, -2, -1312, 0, 1509, 0, -669, 0, 108], [-108, 1486, -405, -5186, 1280, 5400, -1191, -1944, 303, 216], [-216, 2916, -26, -10773, -2, 12080, 0, -5079, 0, 735], [-735, 10074, -2229, -35306, 6867, 36748, -6295, -13230, 1536, 1470], [-1470, 19845, -216, -72789, -26, 80367, -2, -32755, 0, 4476]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 14, -7, -48, 24, 50, -25, -18, 9, 2], [-2, 27, 0, -103, 0, 124, 0, -61, 0, 13], [-13, 180, -64, -624, 209, 650, -201, -234, 56, 26], [-26, 351, -2, -1312, 0, 1509, 0, -669, 0, 108], [-108, 1486, -405, -5186, 1280, 5400, -1191, -1944, 303, 216], [-216, 2916, -26, -10773, -2, 12080, 0, -5079, 0, 735], [-735, 10074, -2229, -35306, 6867, 36748, -6295, -13230, 1536, 1470], [-1470, 19845, -216, -72789, -26, 80367, -2, -32755, 0, 4476], [-4476, 61194, -11487, -215064, 34635, 223774, -31533, -80570, 7529, 8952]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp7065033361 : Fact (Nat.Prime 7065033361) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 1]
  b' := [0, 1, 1, 1]
  k := [1]
  f := [0, 8, -3, -23, 14, 27, -11, -8, 6, 2]
  g := [1, 1, 0, 1, 1, 1]
  h := [1, 1, 0, 1, 1, 1]
  a := [0, 1, 0, 0, 1]
  b := [1, 1, 1, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD7065033361 : CertificateDedekindCriterionLists l 7065033361 where
  n := 2
  a' := [1399306153, 3153520278, 5025200110, 915362239, 3888655811, 2209700272, 1587093456, 2718013280]
  b' := [5606444864, 3333088748, 6647154703, 3051622012, 7018756548, 5761678780, 7047477177, 4655374112, 1268005938]
  k := [2396421370, 3498142215, 5525215699, 2401710197, 1161845448, 2315191289, 166868374, 3881760737, 1]
  f := [107138561, 1143458280, 155963491, 1522336138, 59002019, 479225009, 252465122, 1312668173, 1233066717, 1]
  g := [475571902, 5075638724, 692298394, 6757420352, 261901053, 2127207486, 1120654571, 5826735900, 5473397048, 1]
  h := [1591636311, 1]
  a := [3898631251, 2473895253, 2176532686, 702897952, 4371082097, 6953641529, 4391143709, 4306871999, 4417901780]
  b := [13162186, 6973178335, 2213492689, 3748623836, 981855468, 3384674687, 1990904558, 2018445229, 2647131581]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![2, 7065033361]
  exp := ![1, 1]
  pdgood := [2, 7065033361]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp7065033361.out
  a := [26269287690, -101543314166, -212030899828, 653395063070, -120655485982, -434144525278, 165962339530, 68834847232, -30469331040]
  b := [867087212, -32655294347, 75796210714, 31963890164, -141189956633, 29891493890, 61821405504, -21800912513, -7492871344, 3046933104]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7065033361 T_ofList CD7065033361

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

end VoightMaximalOrderD10R733

namespace VoightMaximalOrderD10R736

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7254832767381, [-1, -14, 10, 48, -28, -47, 26, 17, -9, -2, 1], 1⟩
local notation "l" => [-1, -14, 10, 48, -28, -47, 26, 17, -9, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -10, -48, 28, 47, -26, -17, 9, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -10, -48, 28, 47, -26, -17, 9, 2], ![2, 29, -6, -106, 8, 122, -5, -60, 1, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -10, -48, 28, 47, -26, -17, 9, 2], ![2, 29, -6, -106, 8, 122, -5, -60, 1, 13], ![13, 184, -101, -630, 258, 619, -216, -226, 57, 27]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -10, -48, 28, 47, -26, -17, 9, 2], ![2, 29, -6, -106, 8, 122, -5, -60, 1, 13], ![13, 184, -101, -630, 258, 619, -216, -226, 57, 27], ![27, 391, -86, -1397, 126, 1527, -83, -675, 17, 111]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -10, -48, 28, 47, -26, -17, 9, 2], ![2, 29, -6, -106, 8, 122, -5, -60, 1, 13], ![13, 184, -101, -630, 258, 619, -216, -226, 57, 27], ![27, 391, -86, -1397, 126, 1527, -83, -675, 17, 111], ![111, 1581, -719, -5414, 1711, 5343, -1359, -1970, 324, 239]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -10, -48, 28, 47, -26, -17, 9, 2], ![2, 29, -6, -106, 8, 122, -5, -60, 1, 13], ![13, 184, -101, -630, 258, 619, -216, -226, 57, 27], ![27, 391, -86, -1397, 126, 1527, -83, -675, 17, 111], ![111, 1581, -719, -5414, 1711, 5343, -1359, -1970, 324, 239], ![239, 3457, -809, -12191, 1278, 12944, -871, -5422, 181, 802]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -10, -48, 28, 47, -26, -17, 9, 2], ![2, 29, -6, -106, 8, 122, -5, -60, 1, 13], ![13, 184, -101, -630, 258, 619, -216, -226, 57, 27], ![27, 391, -86, -1397, 126, 1527, -83, -675, 17, 111], ![111, 1581, -719, -5414, 1711, 5343, -1359, -1970, 324, 239], ![239, 3457, -809, -12191, 1278, 12944, -871, -5422, 181, 802], ![802, 11467, -4563, -39305, 10265, 38972, -7908, -14505, 1796, 1785]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -10, -48, 28, 47, -26, -17, 9, 2], ![2, 29, -6, -106, 8, 122, -5, -60, 1, 13], ![13, 184, -101, -630, 258, 619, -216, -226, 57, 27], ![27, 391, -86, -1397, 126, 1527, -83, -675, 17, 111], ![111, 1581, -719, -5414, 1711, 5343, -1359, -1970, 324, 239], ![239, 3457, -809, -12191, 1278, 12944, -871, -5422, 181, 802], ![802, 11467, -4563, -39305, 10265, 38972, -7908, -14505, 1796, 1785], ![1785, 25792, -6383, -90243, 10675, 94160, -7438, -38253, 1560, 5366]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -10, -48, 28, 47, -26, -17, 9, 2], ![2, 29, -6, -106, 8, 122, -5, -60, 1, 13], ![13, 184, -101, -630, 258, 619, -216, -226, 57, 27], ![27, 391, -86, -1397, 126, 1527, -83, -675, 17, 111], ![111, 1581, -719, -5414, 1711, 5343, -1359, -1970, 324, 239], ![239, 3457, -809, -12191, 1278, 12944, -871, -5422, 181, 802], ![802, 11467, -4563, -39305, 10265, 38972, -7908, -14505, 1796, 1785], ![1785, 25792, -6383, -90243, 10675, 94160, -7438, -38253, 1560, 5366], ![5366, 76909, -27868, -263951, 60005, 262877, -45356, -98660, 10041, 12292]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-27, -13, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-27, -13, -2, -1], [-111, -27, -13, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-27, -13, -2, -1], [-111, -27, -13, -2, -1], [-239, -111, -27, -13, -2, -1]], ![[], [], [], [-1], [-2, -1], [-13, -2, -1], [-27, -13, -2, -1], [-111, -27, -13, -2, -1], [-239, -111, -27, -13, -2, -1], [-802, -239, -111, -27, -13, -2, -1]], ![[], [], [-1], [-2, -1], [-13, -2, -1], [-27, -13, -2, -1], [-111, -27, -13, -2, -1], [-239, -111, -27, -13, -2, -1], [-802, -239, -111, -27, -13, -2, -1], [-1785, -802, -239, -111, -27, -13, -2, -1]], ![[], [-1], [-2, -1], [-13, -2, -1], [-27, -13, -2, -1], [-111, -27, -13, -2, -1], [-239, -111, -27, -13, -2, -1], [-802, -239, -111, -27, -13, -2, -1], [-1785, -802, -239, -111, -27, -13, -2, -1], [-5366, -1785, -802, -239, -111, -27, -13, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -10, -48, 28, 47, -26, -17, 9, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -10, -48, 28, 47, -26, -17, 9, 2], [2, 29, -6, -106, 8, 122, -5, -60, 1, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -10, -48, 28, 47, -26, -17, 9, 2], [2, 29, -6, -106, 8, 122, -5, -60, 1, 13], [13, 184, -101, -630, 258, 619, -216, -226, 57, 27]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -10, -48, 28, 47, -26, -17, 9, 2], [2, 29, -6, -106, 8, 122, -5, -60, 1, 13], [13, 184, -101, -630, 258, 619, -216, -226, 57, 27], [27, 391, -86, -1397, 126, 1527, -83, -675, 17, 111]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -10, -48, 28, 47, -26, -17, 9, 2], [2, 29, -6, -106, 8, 122, -5, -60, 1, 13], [13, 184, -101, -630, 258, 619, -216, -226, 57, 27], [27, 391, -86, -1397, 126, 1527, -83, -675, 17, 111], [111, 1581, -719, -5414, 1711, 5343, -1359, -1970, 324, 239]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -10, -48, 28, 47, -26, -17, 9, 2], [2, 29, -6, -106, 8, 122, -5, -60, 1, 13], [13, 184, -101, -630, 258, 619, -216, -226, 57, 27], [27, 391, -86, -1397, 126, 1527, -83, -675, 17, 111], [111, 1581, -719, -5414, 1711, 5343, -1359, -1970, 324, 239], [239, 3457, -809, -12191, 1278, 12944, -871, -5422, 181, 802]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -10, -48, 28, 47, -26, -17, 9, 2], [2, 29, -6, -106, 8, 122, -5, -60, 1, 13], [13, 184, -101, -630, 258, 619, -216, -226, 57, 27], [27, 391, -86, -1397, 126, 1527, -83, -675, 17, 111], [111, 1581, -719, -5414, 1711, 5343, -1359, -1970, 324, 239], [239, 3457, -809, -12191, 1278, 12944, -871, -5422, 181, 802], [802, 11467, -4563, -39305, 10265, 38972, -7908, -14505, 1796, 1785]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -10, -48, 28, 47, -26, -17, 9, 2], [2, 29, -6, -106, 8, 122, -5, -60, 1, 13], [13, 184, -101, -630, 258, 619, -216, -226, 57, 27], [27, 391, -86, -1397, 126, 1527, -83, -675, 17, 111], [111, 1581, -719, -5414, 1711, 5343, -1359, -1970, 324, 239], [239, 3457, -809, -12191, 1278, 12944, -871, -5422, 181, 802], [802, 11467, -4563, -39305, 10265, 38972, -7908, -14505, 1796, 1785], [1785, 25792, -6383, -90243, 10675, 94160, -7438, -38253, 1560, 5366]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -10, -48, 28, 47, -26, -17, 9, 2], [2, 29, -6, -106, 8, 122, -5, -60, 1, 13], [13, 184, -101, -630, 258, 619, -216, -226, 57, 27], [27, 391, -86, -1397, 126, 1527, -83, -675, 17, 111], [111, 1581, -719, -5414, 1711, 5343, -1359, -1970, 324, 239], [239, 3457, -809, -12191, 1278, 12944, -871, -5422, 181, 802], [802, 11467, -4563, -39305, 10265, 38972, -7908, -14505, 1796, 1785], [1785, 25792, -6383, -90243, 10675, 94160, -7438, -38253, 1560, 5366], [5366, 76909, -27868, -263951, 60005, 262877, -45356, -98660, 10041, 12292]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp163 : Fact (Nat.Prime 163) := fact_iff.2 (by norm_num)
instance hp1648450981 : Fact (Nat.Prime 1648450981) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 3
  a' := [2, 1, 0, 2, 2, 1, 2]
  b' := [1, 2, 0, 2, 1, 0, 0, 2]
  k := [1, 1, 2, 0, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1]
  f := [1, 6, -2, -14, 12, 18, -7, -4, 5, 2]
  g := [2, 0, 2, 2, 2, 1, 1, 2, 1]
  h := [1, 2, 1]
  a := [2, 2, 0, 2, 2, 0, 2, 1]
  b := [1, 2, 1, 0, 0, 0, 0, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD163 : CertificateDedekindCriterionLists l 163 where
  n := 2
  a' := [83, 70, 11, 5, 101, 117, 20, 1]
  b' := [98, 11, 133, 90, 114, 134, 82, 97, 18]
  k := [37, 75, 79, 106, 29, 111, 86, 65, 1]
  f := [43, 16, 35, 34, 10, 42, 1, 32, 34, 1]
  g := [146, 51, 118, 114, 31, 141, 1, 109, 113, 1]
  h := [48, 1]
  a := [60, 98, 111, 130, 118, 45, 84, 122, 105]
  b := [75, 2, 141, 132, 66, 87, 113, 23, 58]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1648450981 : CertificateDedekindCriterionLists l 1648450981 where
  n := 2
  a' := [1203147414, 1041564156, 1138406210, 737430666, 1171432788, 224847, 1313450237, 202941105]
  b' := [850681116, 247314756, 386878059, 319260370, 1351746189, 1038654973, 296509661, 1124891315, 1076418309]
  k := [623246926, 1522585418, 1413162664, 1454220901, 1531392208, 546381207, 1142937657, 401694193, 1]
  f := [510725722, 57310664, 435583114, 480704626, 131396996, 326106541, 366421797, 93436233, 387641555, 1]
  g := [1350554217, 151551321, 1151848411, 1271166951, 347463929, 862350465, 968959426, 247081148, 1025072586, 1]
  h := [623378393, 1]
  a := [1607364866, 299671356, 1169121906, 1318060612, 151327268, 337127813, 1117100756, 1570134915, 472091770]
  b := [995055868, 1539651707, 161730101, 798409963, 900267660, 793234939, 368079546, 617656958, 1176359211]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![3, 163, 1648450981]
  exp := ![1, 1, 1]
  pdgood := [3, 163, 1648450981]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp163.out
    exact hp1648450981.out
  a := [-158772666640817, 105608774932344, 1713829903286938, 29410708077308, -2644768461187700, -233518207121932, 1173983746760620, 71895305291416, -149912773917520]
  b := [11283326722222, 167348220891681, 13691717648976, -534270288216964, -87300535629073, 467317943065758, 58942870345032, -148341627736418, -10187786007492, 14991277391752]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 163 T_ofList CD163
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1648450981 T_ofList CD1648450981

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

end VoightMaximalOrderD10R736

end TraceEuclidean
