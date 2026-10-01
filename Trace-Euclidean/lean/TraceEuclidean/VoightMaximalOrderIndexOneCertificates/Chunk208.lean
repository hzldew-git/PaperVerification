import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk204
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

namespace VoightMaximalOrderD10R442

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5250218535793, [-1, -2, 11, 16, -33, -21, 31, 8, -10, -1, 1], 1⟩
local notation "l" => [-1, -2, 11, 16, -33, -21, 31, 8, -10, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -11, -16, 33, 21, -31, -8, 10, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -11, -16, 33, 21, -31, -8, 10, 1], ![1, 3, -9, -27, 17, 54, -10, -39, 2, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -11, -16, 33, 21, -31, -8, 10, 1], ![1, 3, -9, -27, 17, 54, -10, -39, 2, 11], ![11, 23, -118, -185, 336, 248, -287, -98, 71, 13]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -11, -16, 33, 21, -31, -8, 10, 1], ![1, 3, -9, -27, 17, 54, -10, -39, 2, 11], ![11, 23, -118, -185, 336, 248, -287, -98, 71, 13], ![13, 37, -120, -326, 244, 609, -155, -391, 32, 84]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -11, -16, 33, 21, -31, -8, 10, 1], ![1, 3, -9, -27, 17, 54, -10, -39, 2, 11], ![11, 23, -118, -185, 336, 248, -287, -98, 71, 13], ![13, 37, -120, -326, 244, 609, -155, -391, 32, 84], ![84, 181, -887, -1464, 2446, 2008, -1995, -827, 449, 116]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -11, -16, 33, 21, -31, -8, 10, 1], ![1, 3, -9, -27, 17, 54, -10, -39, 2, 11], ![11, 23, -118, -185, 336, 248, -287, -98, 71, 13], ![13, 37, -120, -326, 244, 609, -155, -391, 32, 84], ![84, 181, -887, -1464, 2446, 2008, -1995, -827, 449, 116], ![116, 316, -1095, -2743, 2364, 4882, -1588, -2923, 333, 565]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -11, -16, 33, 21, -31, -8, 10, 1], ![1, 3, -9, -27, 17, 54, -10, -39, 2, 11], ![11, 23, -118, -185, 336, 248, -287, -98, 71, 13], ![13, 37, -120, -326, 244, 609, -155, -391, 32, 84], ![84, 181, -887, -1464, 2446, 2008, -1995, -827, 449, 116], ![116, 316, -1095, -2743, 2364, 4882, -1588, -2923, 333, 565], ![565, 1246, -5899, -10135, 15902, 14229, -12633, -6108, 2727, 898]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -11, -16, 33, 21, -31, -8, 10, 1], ![1, 3, -9, -27, 17, 54, -10, -39, 2, 11], ![11, 23, -118, -185, 336, 248, -287, -98, 71, 13], ![13, 37, -120, -326, 244, 609, -155, -391, 32, 84], ![84, 181, -887, -1464, 2446, 2008, -1995, -827, 449, 116], ![116, 316, -1095, -2743, 2364, 4882, -1588, -2923, 333, 565], ![565, 1246, -5899, -10135, 15902, 14229, -12633, -6108, 2727, 898], ![898, 2361, -8632, -20267, 19499, 34760, -13609, -19817, 2872, 3625]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -11, -16, 33, 21, -31, -8, 10, 1], ![1, 3, -9, -27, 17, 54, -10, -39, 2, 11], ![11, 23, -118, -185, 336, 248, -287, -98, 71, 13], ![13, 37, -120, -326, 244, 609, -155, -391, 32, 84], ![84, 181, -887, -1464, 2446, 2008, -1995, -827, 449, 116], ![116, 316, -1095, -2743, 2364, 4882, -1588, -2923, 333, 565], ![565, 1246, -5899, -10135, 15902, 14229, -12633, -6108, 2727, 898], ![898, 2361, -8632, -20267, 19499, 34760, -13609, -19817, 2872, 3625], ![3625, 8148, -37514, -66632, 99358, 95624, -77615, -42609, 16433, 6497]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-84, -13, -11, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-84, -13, -11, -1, -1], [-116, -84, -13, -11, -1, -1]], ![[], [], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-84, -13, -11, -1, -1], [-116, -84, -13, -11, -1, -1], [-565, -116, -84, -13, -11, -1, -1]], ![[], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-84, -13, -11, -1, -1], [-116, -84, -13, -11, -1, -1], [-565, -116, -84, -13, -11, -1, -1], [-898, -565, -116, -84, -13, -11, -1, -1]], ![[], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-84, -13, -11, -1, -1], [-116, -84, -13, -11, -1, -1], [-565, -116, -84, -13, -11, -1, -1], [-898, -565, -116, -84, -13, -11, -1, -1], [-3625, -898, -565, -116, -84, -13, -11, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -11, -16, 33, 21, -31, -8, 10, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -11, -16, 33, 21, -31, -8, 10, 1], [1, 3, -9, -27, 17, 54, -10, -39, 2, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -11, -16, 33, 21, -31, -8, 10, 1], [1, 3, -9, -27, 17, 54, -10, -39, 2, 11], [11, 23, -118, -185, 336, 248, -287, -98, 71, 13]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -11, -16, 33, 21, -31, -8, 10, 1], [1, 3, -9, -27, 17, 54, -10, -39, 2, 11], [11, 23, -118, -185, 336, 248, -287, -98, 71, 13], [13, 37, -120, -326, 244, 609, -155, -391, 32, 84]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -11, -16, 33, 21, -31, -8, 10, 1], [1, 3, -9, -27, 17, 54, -10, -39, 2, 11], [11, 23, -118, -185, 336, 248, -287, -98, 71, 13], [13, 37, -120, -326, 244, 609, -155, -391, 32, 84], [84, 181, -887, -1464, 2446, 2008, -1995, -827, 449, 116]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -11, -16, 33, 21, -31, -8, 10, 1], [1, 3, -9, -27, 17, 54, -10, -39, 2, 11], [11, 23, -118, -185, 336, 248, -287, -98, 71, 13], [13, 37, -120, -326, 244, 609, -155, -391, 32, 84], [84, 181, -887, -1464, 2446, 2008, -1995, -827, 449, 116], [116, 316, -1095, -2743, 2364, 4882, -1588, -2923, 333, 565]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -11, -16, 33, 21, -31, -8, 10, 1], [1, 3, -9, -27, 17, 54, -10, -39, 2, 11], [11, 23, -118, -185, 336, 248, -287, -98, 71, 13], [13, 37, -120, -326, 244, 609, -155, -391, 32, 84], [84, 181, -887, -1464, 2446, 2008, -1995, -827, 449, 116], [116, 316, -1095, -2743, 2364, 4882, -1588, -2923, 333, 565], [565, 1246, -5899, -10135, 15902, 14229, -12633, -6108, 2727, 898]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -11, -16, 33, 21, -31, -8, 10, 1], [1, 3, -9, -27, 17, 54, -10, -39, 2, 11], [11, 23, -118, -185, 336, 248, -287, -98, 71, 13], [13, 37, -120, -326, 244, 609, -155, -391, 32, 84], [84, 181, -887, -1464, 2446, 2008, -1995, -827, 449, 116], [116, 316, -1095, -2743, 2364, 4882, -1588, -2923, 333, 565], [565, 1246, -5899, -10135, 15902, 14229, -12633, -6108, 2727, 898], [898, 2361, -8632, -20267, 19499, 34760, -13609, -19817, 2872, 3625]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -11, -16, 33, 21, -31, -8, 10, 1], [1, 3, -9, -27, 17, 54, -10, -39, 2, 11], [11, 23, -118, -185, 336, 248, -287, -98, 71, 13], [13, 37, -120, -326, 244, 609, -155, -391, 32, 84], [84, 181, -887, -1464, 2446, 2008, -1995, -827, 449, 116], [116, 316, -1095, -2743, 2364, 4882, -1588, -2923, 333, 565], [565, 1246, -5899, -10135, 15902, 14229, -12633, -6108, 2727, 898], [898, 2361, -8632, -20267, 19499, 34760, -13609, -19817, 2872, 3625], [3625, 8148, -37514, -66632, 99358, 95624, -77615, -42609, 16433, 6497]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp337 : Fact (Nat.Prime 337) := fact_iff.2 (by norm_num)
instance hp1621 : Fact (Nat.Prime 1621) := fact_iff.2 (by norm_num)

def CD7 : CertificateDedekindCriterionLists l 7 where
  n := 2
  a' := [6, 5, 1, 5, 4, 1]
  b' := [1, 2, 2, 6, 4, 6, 6]
  k := [5, 6, 6, 4, 3, 2, 1]
  f := [3, 5, 4, 2, 7, 8, 1, 4, 4, 1]
  g := [4, 5, 5, 3, 1, 6, 5, 4, 1]
  h := [5, 2, 1]
  a := [6, 2, 5, 1, 1, 4, 2, 1]
  b := [1, 2, 5, 3, 3, 2, 4, 5, 6]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [5, 4, 10, 6, 1, 8, 8]
  b' := [7, 1, 8, 10, 5, 6, 4, 10]
  k := [8, 1, 2, 2, 7, 9, 1]
  f := [1, 4, 4, 4, 8, 7, 3, 5, 4, 1]
  g := [5, 6, 7, 6, 6, 7, 8, 4, 1]
  h := [2, 6, 1]
  a := [5, 0, 0, 1, 8, 2, 3, 1]
  b := [8, 4, 2, 9, 10, 4, 1, 8, 10]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD337 : CertificateDedekindCriterionLists l 337 where
  n := 2
  a' := [194, 99, 231, 328, 118, 241, 263, 109]
  b' := [268, 129, 118, 193, 263, 237, 209, 307, 250]
  k := [48, 149, 80, 294, 146, 46, 249, 98, 1]
  f := [113, 91, 83, 7, 51, 81, 8, 41, 77, 1]
  g := [320, 255, 233, 18, 144, 228, 21, 116, 217, 1]
  h := [119, 1]
  a := [221, 22, 259, 271, 245, 152, 19, 205, 158]
  b := [2, 150, 2, 102, 227, 90, 279, 10, 179]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1621 : CertificateDedekindCriterionLists l 1621 where
  n := 2
  a' := [1234, 1251, 559, 1277, 269, 1481, 306]
  b' := [843, 705, 295, 1591, 1121, 1074, 264, 367]
  k := [165, 558, 1101, 127, 1598, 78, 1]
  f := [436, 824, 674, 841, 932, 1178, 1270, 955, 405, 1]
  g := [795, 813, 523, 1079, 763, 1485, 1027, 849, 1]
  h := [889, 771, 1]
  a := [964, 700, 253, 881, 802, 1439, 977, 269]
  b := [762, 1410, 1279, 1451, 710, 1534, 1570, 126, 1352]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![7, 11, 337, 1621]
  exp := ![1, 1, 1, 1]
  pdgood := [7, 11, 337, 1621]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp7.out
    exact hp11.out
    exact hp337.out
    exact hp1621.out
  a := [183784677, -3090391602, 3403573063, 6805603984, -7083580681, -3537485446, 3419182194, 541710684, -452080160]
  b := [-112924003, 119247091, 1000962723, -1007747115, -1303652545, 1221399115, 488454447, -430985866, -58691870, 45208016]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 337 T_ofList CD337
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

end VoightMaximalOrderD10R442

namespace VoightMaximalOrderD10R444

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5266247865344, [1, 16, 29, -28, -63, 14, 42, -2, -11, 0, 1], 1⟩
local notation "l" => [1, 16, 29, -28, -63, 14, 42, -2, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -16, -29, 28, 63, -14, -42, 2, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -16, -29, 28, 63, -14, -42, 2, 11, 0], ![0, -1, -16, -29, 28, 63, -14, -42, 2, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -16, -29, 28, 63, -14, -42, 2, 11, 0], ![0, -1, -16, -29, 28, 63, -14, -42, 2, 11], ![-11, -176, -320, 292, 664, -126, -399, 8, 79, 2]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -16, -29, 28, 63, -14, -42, 2, 11, 0], ![0, -1, -16, -29, 28, 63, -14, -42, 2, 11], ![-11, -176, -320, 292, 664, -126, -399, 8, 79, 2], ![-2, -43, -234, -264, 418, 636, -210, -395, 30, 79]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -16, -29, 28, 63, -14, -42, 2, 11, 0], ![0, -1, -16, -29, 28, 63, -14, -42, 2, 11], ![-11, -176, -320, 292, 664, -126, -399, 8, 79, 2], ![-2, -43, -234, -264, 418, 636, -210, -395, 30, 79], ![-79, -1266, -2334, 1978, 4713, -688, -2682, -52, 474, 30]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -16, -29, 28, 63, -14, -42, 2, 11, 0], ![0, -1, -16, -29, 28, 63, -14, -42, 2, 11], ![-11, -176, -320, 292, 664, -126, -399, 8, 79, 2], ![-2, -43, -234, -264, 418, 636, -210, -395, 30, 79], ![-79, -1266, -2334, 1978, 4713, -688, -2682, -52, 474, 30], ![-30, -559, -2136, -1494, 3868, 4293, -1948, -2622, 278, 474]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -16, -29, 28, 63, -14, -42, 2, 11, 0], ![0, -1, -16, -29, 28, 63, -14, -42, 2, 11], ![-11, -176, -320, 292, 664, -126, -399, 8, 79, 2], ![-2, -43, -234, -264, 418, 636, -210, -395, 30, 79], ![-79, -1266, -2334, 1978, 4713, -688, -2682, -52, 474, 30], ![-30, -559, -2136, -1494, 3868, 4293, -1948, -2622, 278, 474], ![-474, -7614, -14305, 11136, 28368, -2768, -15615, -1000, 2592, 278]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -16, -29, 28, 63, -14, -42, 2, 11, 0], ![0, -1, -16, -29, 28, 63, -14, -42, 2, 11], ![-11, -176, -320, 292, 664, -126, -399, 8, 79, 2], ![-2, -43, -234, -264, 418, 636, -210, -395, 30, 79], ![-79, -1266, -2334, 1978, 4713, -688, -2682, -52, 474, 30], ![-30, -559, -2136, -1494, 3868, 4293, -1948, -2622, 278, 474], ![-474, -7614, -14305, 11136, 28368, -2768, -15615, -1000, 2592, 278], ![-278, -4922, -15676, -6521, 28650, 24476, -14444, -15059, 2058, 2592]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -16, -29, 28, 63, -14, -42, 2, 11, 0], ![0, -1, -16, -29, 28, 63, -14, -42, 2, 11], ![-11, -176, -320, 292, 664, -126, -399, 8, 79, 2], ![-2, -43, -234, -264, 418, 636, -210, -395, 30, 79], ![-79, -1266, -2334, 1978, 4713, -688, -2682, -52, 474, 30], ![-30, -559, -2136, -1494, 3868, 4293, -1948, -2622, 278, 474], ![-474, -7614, -14305, 11136, 28368, -2768, -15615, -1000, 2592, 278], ![-278, -4922, -15676, -6521, 28650, 24476, -14444, -15059, 2058, 2592], ![-2592, -41750, -80090, 56900, 156775, -7638, -84388, -9260, 13453, 2058]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-79, -2, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-79, -2, -11, 0, -1], [-30, -79, -2, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-79, -2, -11, 0, -1], [-30, -79, -2, -11, 0, -1], [-474, -30, -79, -2, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-79, -2, -11, 0, -1], [-30, -79, -2, -11, 0, -1], [-474, -30, -79, -2, -11, 0, -1], [-278, -474, -30, -79, -2, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-79, -2, -11, 0, -1], [-30, -79, -2, -11, 0, -1], [-474, -30, -79, -2, -11, 0, -1], [-278, -474, -30, -79, -2, -11, 0, -1], [-2592, -278, -474, -30, -79, -2, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -16, -29, 28, 63, -14, -42, 2, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -16, -29, 28, 63, -14, -42, 2, 11, 0], [0, -1, -16, -29, 28, 63, -14, -42, 2, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -16, -29, 28, 63, -14, -42, 2, 11, 0], [0, -1, -16, -29, 28, 63, -14, -42, 2, 11], [-11, -176, -320, 292, 664, -126, -399, 8, 79, 2]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -16, -29, 28, 63, -14, -42, 2, 11, 0], [0, -1, -16, -29, 28, 63, -14, -42, 2, 11], [-11, -176, -320, 292, 664, -126, -399, 8, 79, 2], [-2, -43, -234, -264, 418, 636, -210, -395, 30, 79]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -16, -29, 28, 63, -14, -42, 2, 11, 0], [0, -1, -16, -29, 28, 63, -14, -42, 2, 11], [-11, -176, -320, 292, 664, -126, -399, 8, 79, 2], [-2, -43, -234, -264, 418, 636, -210, -395, 30, 79], [-79, -1266, -2334, 1978, 4713, -688, -2682, -52, 474, 30]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -16, -29, 28, 63, -14, -42, 2, 11, 0], [0, -1, -16, -29, 28, 63, -14, -42, 2, 11], [-11, -176, -320, 292, 664, -126, -399, 8, 79, 2], [-2, -43, -234, -264, 418, 636, -210, -395, 30, 79], [-79, -1266, -2334, 1978, 4713, -688, -2682, -52, 474, 30], [-30, -559, -2136, -1494, 3868, 4293, -1948, -2622, 278, 474]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -16, -29, 28, 63, -14, -42, 2, 11, 0], [0, -1, -16, -29, 28, 63, -14, -42, 2, 11], [-11, -176, -320, 292, 664, -126, -399, 8, 79, 2], [-2, -43, -234, -264, 418, 636, -210, -395, 30, 79], [-79, -1266, -2334, 1978, 4713, -688, -2682, -52, 474, 30], [-30, -559, -2136, -1494, 3868, 4293, -1948, -2622, 278, 474], [-474, -7614, -14305, 11136, 28368, -2768, -15615, -1000, 2592, 278]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -16, -29, 28, 63, -14, -42, 2, 11, 0], [0, -1, -16, -29, 28, 63, -14, -42, 2, 11], [-11, -176, -320, 292, 664, -126, -399, 8, 79, 2], [-2, -43, -234, -264, 418, 636, -210, -395, 30, 79], [-79, -1266, -2334, 1978, 4713, -688, -2682, -52, 474, 30], [-30, -559, -2136, -1494, 3868, 4293, -1948, -2622, 278, 474], [-474, -7614, -14305, 11136, 28368, -2768, -15615, -1000, 2592, 278], [-278, -4922, -15676, -6521, 28650, 24476, -14444, -15059, 2058, 2592]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -16, -29, 28, 63, -14, -42, 2, 11, 0], [0, -1, -16, -29, 28, 63, -14, -42, 2, 11], [-11, -176, -320, 292, 664, -126, -399, 8, 79, 2], [-2, -43, -234, -264, 418, 636, -210, -395, 30, 79], [-79, -1266, -2334, 1978, 4713, -688, -2682, -52, 474, 30], [-30, -559, -2136, -1494, 3868, 4293, -1948, -2622, 278, 474], [-474, -7614, -14305, 11136, 28368, -2768, -15615, -1000, 2592, 278], [-278, -4922, -15676, -6521, 28650, 24476, -14444, -15059, 2058, 2592], [-2592, -41750, -80090, 56900, 156775, -7638, -84388, -9260, 13453, 2058]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp179 : Fact (Nat.Prime 179) := fact_iff.2 (by norm_num)
instance hp1997 : Fact (Nat.Prime 1997) := fact_iff.2 (by norm_num)
instance hp14387 : Fact (Nat.Prime 14387) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [0, 0, 1]
  b' := [1, 0, 1, 1]
  k := [1]
  f := [0, -7, -13, 15, 33, -5, -19, 2, 6, 1]
  g := [1, 1, 1, 0, 1, 1]
  h := [1, 1, 1, 0, 1, 1]
  a := [0, 1, 1, 0, 1]
  b := [1, 1, 1, 0, 0, 1, 0, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD179 : CertificateDedekindCriterionLists l 179 where
  n := 2
  a' := [99, 38, 18, 144, 178, 135, 167, 103]
  b' := [124, 137, 107, 99, 114, 35, 172, 106, 88]
  k := [80, 159, 4, 11, 55, 107, 130, 176, 1]
  f := [61, 26, 84, 57, 3, 64, 63, 19, 45, 1]
  g := [120, 50, 165, 110, 4, 126, 123, 36, 88, 1]
  h := [91, 1]
  a := [81, 38, 32, 121, 152, 81, 11, 171, 174]
  b := [108, 121, 57, 89, 173, 80, 43, 151, 5]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1997 : CertificateDedekindCriterionLists l 1997 where
  n := 2
  a' := [1865, 570, 1072, 678, 1558, 1956, 750, 1944]
  b' := [1815, 1285, 753, 209, 395, 958, 650, 0, 1781]
  k := [918, 1666, 1964, 1261, 1465, 129, 113, 104, 1]
  f := [187, 153, 1349, 289, 942, 729, 238, 678, 51, 1]
  g := [192, 157, 1385, 296, 967, 748, 244, 696, 52, 1]
  h := [1945, 1]
  a := [12, 624, 1370, 1449, 1325, 174, 1641, 1795, 721]
  b := [810, 1279, 213, 1802, 700, 752, 1601, 923, 1276]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD14387 : CertificateDedekindCriterionLists l 14387 where
  n := 2
  a' := [4669, 7586, 2825, 12236, 6205, 2806, 7772, 2898]
  b' := [5666, 2192, 10535, 1192, 10917, 10897, 12715, 4010, 14065]
  k := [6640, 7353, 629, 9888, 1169, 8413, 7163, 12238, 1]
  f := [7537, 1025, 8171, 4414, 4090, 7526, 471, 4124, 3517, 1]
  g := [13115, 1782, 14218, 7679, 7116, 13095, 818, 7176, 6119, 1]
  h := [8268, 1]
  a := [9666, 4523, 7313, 212, 1997, 630, 6057, 8605, 10484]
  b := [597, 8269, 3747, 7398, 9833, 5315, 8413, 7398, 3903]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![2, 179, 1997, 14387]
  exp := ![1, 1, 1, 1]
  pdgood := [2, 179, 1997, 14387]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp179.out
    exact hp1997.out
    exact hp14387.out
  a := [-24305890886, -23532891814, 150999299990, 62780251746, -178176344686, -42533886292, 71695284506, 7758497500, -9306962570]
  b := [2161970703, 17939552826, 4469329992, -42772638674, -10613334638, 31673524492, 5401840325, -9217060216, -775849750, 930696257]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 179 T_ofList CD179
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1997 T_ofList CD1997
    exact satisfiesDedekindCriterion_of_certificate_lists T l 14387 T_ofList CD14387

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

end VoightMaximalOrderD10R444

namespace VoightMaximalOrderD10R446

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5307624753125, [1, -2, -15, 22, 45, -78, 6, 30, -8, -3, 1], 1⟩
local notation "l" => [1, -2, -15, 22, 45, -78, 6, 30, -8, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 15, -22, -45, 78, -6, -30, 8, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 15, -22, -45, 78, -6, -30, 8, 3], ![-3, 5, 47, -51, -157, 189, 60, -96, -6, 17]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 15, -22, -45, 78, -6, -30, 8, 3], ![-3, 5, 47, -51, -157, 189, 60, -96, -6, 17], ![-17, 31, 260, -327, -816, 1169, 87, -450, 40, 45]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 15, -22, -45, 78, -6, -30, 8, 3], ![-3, 5, 47, -51, -157, 189, 60, -96, -6, 17], ![-17, 31, 260, -327, -816, 1169, 87, -450, 40, 45], ![-45, 73, 706, -730, -2352, 2694, 899, -1263, -90, 175]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 15, -22, -45, 78, -6, -30, 8, 3], ![-3, 5, 47, -51, -157, 189, 60, -96, -6, 17], ![-17, 31, 260, -327, -816, 1169, 87, -450, 40, 45], ![-45, 73, 706, -730, -2352, 2694, 899, -1263, -90, 175], ![-175, 305, 2698, -3144, -8605, 11298, 1644, -4351, 137, 435]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 15, -22, -45, 78, -6, -30, 8, 3], ![-3, 5, 47, -51, -157, 189, 60, -96, -6, 17], ![-17, 31, 260, -327, -816, 1169, 87, -450, 40, 45], ![-45, 73, 706, -730, -2352, 2694, 899, -1263, -90, 175], ![-175, 305, 2698, -3144, -8605, 11298, 1644, -4351, 137, 435], ![-435, 695, 6830, -6872, -22719, 25325, 8688, -11406, -871, 1442]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 15, -22, -45, 78, -6, -30, 8, 3], ![-3, 5, 47, -51, -157, 189, 60, -96, -6, 17], ![-17, 31, 260, -327, -816, 1169, 87, -450, 40, 45], ![-45, 73, 706, -730, -2352, 2694, 899, -1263, -90, 175], ![-175, 305, 2698, -3144, -8605, 11298, 1644, -4351, 137, 435], ![-435, 695, 6830, -6872, -22719, 25325, 8688, -11406, -871, 1442], ![-1442, 2449, 22325, -24894, -71762, 89757, 16673, -34572, 130, 3455]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 15, -22, -45, 78, -6, -30, 8, 3], ![-3, 5, 47, -51, -157, 189, 60, -96, -6, 17], ![-17, 31, 260, -327, -816, 1169, 87, -450, 40, 45], ![-45, 73, 706, -730, -2352, 2694, 899, -1263, -90, 175], ![-175, 305, 2698, -3144, -8605, 11298, 1644, -4351, 137, 435], ![-435, 695, 6830, -6872, -22719, 25325, 8688, -11406, -871, 1442], ![-1442, 2449, 22325, -24894, -71762, 89757, 16673, -34572, 130, 3455], ![-3455, 5468, 54274, -53685, -180369, 197728, 69027, -86977, -6932, 10495]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 15, -22, -45, 78, -6, -30, 8, 3], ![-3, 5, 47, -51, -157, 189, 60, -96, -6, 17], ![-17, 31, 260, -327, -816, 1169, 87, -450, 40, 45], ![-45, 73, 706, -730, -2352, 2694, 899, -1263, -90, 175], ![-175, 305, 2698, -3144, -8605, 11298, 1644, -4351, 137, 435], ![-435, 695, 6830, -6872, -22719, 25325, 8688, -11406, -871, 1442], ![-1442, 2449, 22325, -24894, -71762, 89757, 16673, -34572, 130, 3455], ![-3455, 5468, 54274, -53685, -180369, 197728, 69027, -86977, -6932, 10495], ![-10495, 17535, 162893, -176616, -525960, 638241, 134758, -245823, -3017, 24553]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-45, -17, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-45, -17, -3, -1], [-175, -45, -17, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-45, -17, -3, -1], [-175, -45, -17, -3, -1], [-435, -175, -45, -17, -3, -1]], ![[], [], [], [-1], [-3, -1], [-17, -3, -1], [-45, -17, -3, -1], [-175, -45, -17, -3, -1], [-435, -175, -45, -17, -3, -1], [-1442, -435, -175, -45, -17, -3, -1]], ![[], [], [-1], [-3, -1], [-17, -3, -1], [-45, -17, -3, -1], [-175, -45, -17, -3, -1], [-435, -175, -45, -17, -3, -1], [-1442, -435, -175, -45, -17, -3, -1], [-3455, -1442, -435, -175, -45, -17, -3, -1]], ![[], [-1], [-3, -1], [-17, -3, -1], [-45, -17, -3, -1], [-175, -45, -17, -3, -1], [-435, -175, -45, -17, -3, -1], [-1442, -435, -175, -45, -17, -3, -1], [-3455, -1442, -435, -175, -45, -17, -3, -1], [-10495, -3455, -1442, -435, -175, -45, -17, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 15, -22, -45, 78, -6, -30, 8, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 15, -22, -45, 78, -6, -30, 8, 3], [-3, 5, 47, -51, -157, 189, 60, -96, -6, 17]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 15, -22, -45, 78, -6, -30, 8, 3], [-3, 5, 47, -51, -157, 189, 60, -96, -6, 17], [-17, 31, 260, -327, -816, 1169, 87, -450, 40, 45]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 15, -22, -45, 78, -6, -30, 8, 3], [-3, 5, 47, -51, -157, 189, 60, -96, -6, 17], [-17, 31, 260, -327, -816, 1169, 87, -450, 40, 45], [-45, 73, 706, -730, -2352, 2694, 899, -1263, -90, 175]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 15, -22, -45, 78, -6, -30, 8, 3], [-3, 5, 47, -51, -157, 189, 60, -96, -6, 17], [-17, 31, 260, -327, -816, 1169, 87, -450, 40, 45], [-45, 73, 706, -730, -2352, 2694, 899, -1263, -90, 175], [-175, 305, 2698, -3144, -8605, 11298, 1644, -4351, 137, 435]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 15, -22, -45, 78, -6, -30, 8, 3], [-3, 5, 47, -51, -157, 189, 60, -96, -6, 17], [-17, 31, 260, -327, -816, 1169, 87, -450, 40, 45], [-45, 73, 706, -730, -2352, 2694, 899, -1263, -90, 175], [-175, 305, 2698, -3144, -8605, 11298, 1644, -4351, 137, 435], [-435, 695, 6830, -6872, -22719, 25325, 8688, -11406, -871, 1442]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 15, -22, -45, 78, -6, -30, 8, 3], [-3, 5, 47, -51, -157, 189, 60, -96, -6, 17], [-17, 31, 260, -327, -816, 1169, 87, -450, 40, 45], [-45, 73, 706, -730, -2352, 2694, 899, -1263, -90, 175], [-175, 305, 2698, -3144, -8605, 11298, 1644, -4351, 137, 435], [-435, 695, 6830, -6872, -22719, 25325, 8688, -11406, -871, 1442], [-1442, 2449, 22325, -24894, -71762, 89757, 16673, -34572, 130, 3455]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 15, -22, -45, 78, -6, -30, 8, 3], [-3, 5, 47, -51, -157, 189, 60, -96, -6, 17], [-17, 31, 260, -327, -816, 1169, 87, -450, 40, 45], [-45, 73, 706, -730, -2352, 2694, 899, -1263, -90, 175], [-175, 305, 2698, -3144, -8605, 11298, 1644, -4351, 137, 435], [-435, 695, 6830, -6872, -22719, 25325, 8688, -11406, -871, 1442], [-1442, 2449, 22325, -24894, -71762, 89757, 16673, -34572, 130, 3455], [-3455, 5468, 54274, -53685, -180369, 197728, 69027, -86977, -6932, 10495]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 15, -22, -45, 78, -6, -30, 8, 3], [-3, 5, 47, -51, -157, 189, 60, -96, -6, 17], [-17, 31, 260, -327, -816, 1169, 87, -450, 40, 45], [-45, 73, 706, -730, -2352, 2694, 899, -1263, -90, 175], [-175, 305, 2698, -3144, -8605, 11298, 1644, -4351, 137, 435], [-435, 695, 6830, -6872, -22719, 25325, 8688, -11406, -871, 1442], [-1442, 2449, 22325, -24894, -71762, 89757, 16673, -34572, 130, 3455], [-3455, 5468, 54274, -53685, -180369, 197728, 69027, -86977, -6932, 10495], [-10495, 17535, 162893, -176616, -525960, 638241, 134758, -245823, -3017, 24553]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp4241 : Fact (Nat.Prime 4241) := fact_iff.2 (by norm_num)
instance hp400481 : Fact (Nat.Prime 400481) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 2, 4]
  b' := [3, 0, 2, 2, 4]
  k := [1]
  f := [0, 2, 7, 0, -3, 20, 3, -4, 3, 1]
  g := [1, 4, 2, 3, 1, 1]
  h := [1, 4, 2, 3, 1, 1]
  a := [2, 1]
  b := [1, 2, 4, 0, 1, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD4241 : CertificateDedekindCriterionLists l 4241 where
  n := 2
  a' := [1214, 3511, 4032, 2473, 2758, 3269, 4093, 2888]
  b' := [1196, 478, 1068, 231, 61, 2643, 870, 2694, 1564]
  k := [2967, 1336, 889, 2483, 3520, 4008, 3611, 869, 1]
  f := [3709, 1336, 3503, 3587, 2697, 2983, 2713, 1953, 389, 1]
  g := [4134, 1488, 3904, 3997, 3005, 3324, 3023, 2176, 433, 1]
  h := [3805, 1]
  a := [2702, 3393, 546, 4071, 1215, 2228, 4179, 2570, 161]
  b := [240, 3439, 306, 1209, 363, 1483, 3722, 273, 4080]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD400481 : CertificateDedekindCriterionLists l 400481 where
  n := 2
  a' := [250357, 355559, 286383, 29153, 250021, 233809, 7062, 299369]
  b' := [15664, 210405, 174434, 14450, 111359, 196116, 251343, 107867, 278222]
  k := [111703, 168519, 65529, 373402, 333064, 188301, 217437, 340700, 1]
  f := [20998, 9446, 913, 5478, 12434, 7589, 11727, 27566, 27659, 1]
  g := [281351, 126557, 12229, 73399, 166600, 101679, 157126, 369350, 370589, 1]
  h := [29889, 1]
  a := [235552, 369105, 335334, 395882, 334609, 7886, 282308, 189914, 154515]
  b := [171970, 316443, 303453, 105782, 137989, 203105, 200442, 398407, 245966]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 4241, 400481]
  exp := ![1, 1, 1]
  pdgood := [5, 4241, 400481]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp4241.out
    exact hp400481.out
  a := [4763580067, -81122032826, -381315505415, 1211438356974, -287474665162, -684880302154, 263170612295, 89365514656, -38231595980]
  b := [-1864309769, -17359949945, 53614456414, 102966237229, -254542795389, 46712416102, 100110908066, -32849910421, -10083499345, 3823159598]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 4241 T_ofList CD4241
    exact satisfiesDedekindCriterion_of_certificate_lists T l 400481 T_ofList CD400481

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

end VoightMaximalOrderD10R446

namespace VoightMaximalOrderD10R448

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5312565052173, [3, -12, 0, 41, -19, -45, 24, 17, -9, -2, 1], 1⟩
local notation "l" => [3, -12, 0, 41, -19, -45, 24, 17, -9, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 12, 0, -41, 19, 45, -24, -17, 9, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 12, 0, -41, 19, 45, -24, -17, 9, 2], ![-6, 21, 12, -82, -3, 109, -3, -58, 1, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 12, 0, -41, 19, 45, -24, -17, 9, 2], ![-6, 21, 12, -82, -3, 109, -3, -58, 1, 13], ![-39, 150, 21, -521, 165, 582, -203, -224, 59, 27]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 12, 0, -41, 19, 45, -24, -17, 9, 2], ![-6, 21, 12, -82, -3, 109, -3, -58, 1, 13], ![-39, 150, 21, -521, 165, 582, -203, -224, 59, 27], ![-81, 285, 150, -1086, -8, 1380, -66, -662, 19, 113]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 12, 0, -41, 19, 45, -24, -17, 9, 2], ![-6, 21, 12, -82, -3, 109, -3, -58, 1, 13], ![-39, 150, 21, -521, 165, 582, -203, -224, 59, 27], ![-81, 285, 150, -1086, -8, 1380, -66, -662, 19, 113], ![-339, 1275, 285, -4483, 1061, 5077, -1332, -1987, 355, 245]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 12, 0, -41, 19, 45, -24, -17, 9, 2], ![-6, 21, 12, -82, -3, 109, -3, -58, 1, 13], ![-39, 150, 21, -521, 165, 582, -203, -224, 59, 27], ![-81, 285, 150, -1086, -8, 1380, -66, -662, 19, 113], ![-339, 1275, 285, -4483, 1061, 5077, -1332, -1987, 355, 245], ![-735, 2601, 1275, -9760, 172, 12086, -803, -5497, 218, 845]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 12, 0, -41, 19, 45, -24, -17, 9, 2], ![-6, 21, 12, -82, -3, 109, -3, -58, 1, 13], ![-39, 150, 21, -521, 165, 582, -203, -224, 59, 27], ![-81, 285, 150, -1086, -8, 1380, -66, -662, 19, 113], ![-339, 1275, 285, -4483, 1061, 5077, -1332, -1987, 355, 245], ![-735, 2601, 1275, -9760, 172, 12086, -803, -5497, 218, 845], ![-2535, 9405, 2601, -33370, 6295, 38197, -8194, -15168, 2108, 1908]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 12, 0, -41, 19, 45, -24, -17, 9, 2], ![-6, 21, 12, -82, -3, 109, -3, -58, 1, 13], ![-39, 150, 21, -521, 165, 582, -203, -224, 59, 27], ![-81, 285, 150, -1086, -8, 1380, -66, -662, 19, 113], ![-339, 1275, 285, -4483, 1061, 5077, -1332, -1987, 355, 245], ![-735, 2601, 1275, -9760, 172, 12086, -803, -5497, 218, 845], ![-2535, 9405, 2601, -33370, 6295, 38197, -8194, -15168, 2108, 1908], ![-5724, 20361, 9405, -75627, 2882, 92155, -7595, -40630, 2004, 5924]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-3, 12, 0, -41, 19, 45, -24, -17, 9, 2], ![-6, 21, 12, -82, -3, 109, -3, -58, 1, 13], ![-39, 150, 21, -521, 165, 582, -203, -224, 59, 27], ![-81, 285, 150, -1086, -8, 1380, -66, -662, 19, 113], ![-339, 1275, 285, -4483, 1061, 5077, -1332, -1987, 355, 245], ![-735, 2601, 1275, -9760, 172, 12086, -803, -5497, 218, 845], ![-2535, 9405, 2601, -33370, 6295, 38197, -8194, -15168, 2108, 1908], ![-5724, 20361, 9405, -75627, 2882, 92155, -7595, -40630, 2004, 5924], ![-17772, 65364, 20361, -233479, 36929, 269462, -50021, -108303, 12686, 13852]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-27, -13, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-27, -13, -2, -1], [-113, -27, -13, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-27, -13, -2, -1], [-113, -27, -13, -2, -1], [-245, -113, -27, -13, -2, -1]], ![[], [], [], [-1], [-2, -1], [-13, -2, -1], [-27, -13, -2, -1], [-113, -27, -13, -2, -1], [-245, -113, -27, -13, -2, -1], [-845, -245, -113, -27, -13, -2, -1]], ![[], [], [-1], [-2, -1], [-13, -2, -1], [-27, -13, -2, -1], [-113, -27, -13, -2, -1], [-245, -113, -27, -13, -2, -1], [-845, -245, -113, -27, -13, -2, -1], [-1908, -845, -245, -113, -27, -13, -2, -1]], ![[], [-1], [-2, -1], [-13, -2, -1], [-27, -13, -2, -1], [-113, -27, -13, -2, -1], [-245, -113, -27, -13, -2, -1], [-845, -245, -113, -27, -13, -2, -1], [-1908, -845, -245, -113, -27, -13, -2, -1], [-5924, -1908, -845, -245, -113, -27, -13, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 12, 0, -41, 19, 45, -24, -17, 9, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 12, 0, -41, 19, 45, -24, -17, 9, 2], [-6, 21, 12, -82, -3, 109, -3, -58, 1, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 12, 0, -41, 19, 45, -24, -17, 9, 2], [-6, 21, 12, -82, -3, 109, -3, -58, 1, 13], [-39, 150, 21, -521, 165, 582, -203, -224, 59, 27]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 12, 0, -41, 19, 45, -24, -17, 9, 2], [-6, 21, 12, -82, -3, 109, -3, -58, 1, 13], [-39, 150, 21, -521, 165, 582, -203, -224, 59, 27], [-81, 285, 150, -1086, -8, 1380, -66, -662, 19, 113]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 12, 0, -41, 19, 45, -24, -17, 9, 2], [-6, 21, 12, -82, -3, 109, -3, -58, 1, 13], [-39, 150, 21, -521, 165, 582, -203, -224, 59, 27], [-81, 285, 150, -1086, -8, 1380, -66, -662, 19, 113], [-339, 1275, 285, -4483, 1061, 5077, -1332, -1987, 355, 245]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 12, 0, -41, 19, 45, -24, -17, 9, 2], [-6, 21, 12, -82, -3, 109, -3, -58, 1, 13], [-39, 150, 21, -521, 165, 582, -203, -224, 59, 27], [-81, 285, 150, -1086, -8, 1380, -66, -662, 19, 113], [-339, 1275, 285, -4483, 1061, 5077, -1332, -1987, 355, 245], [-735, 2601, 1275, -9760, 172, 12086, -803, -5497, 218, 845]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 12, 0, -41, 19, 45, -24, -17, 9, 2], [-6, 21, 12, -82, -3, 109, -3, -58, 1, 13], [-39, 150, 21, -521, 165, 582, -203, -224, 59, 27], [-81, 285, 150, -1086, -8, 1380, -66, -662, 19, 113], [-339, 1275, 285, -4483, 1061, 5077, -1332, -1987, 355, 245], [-735, 2601, 1275, -9760, 172, 12086, -803, -5497, 218, 845], [-2535, 9405, 2601, -33370, 6295, 38197, -8194, -15168, 2108, 1908]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 12, 0, -41, 19, 45, -24, -17, 9, 2], [-6, 21, 12, -82, -3, 109, -3, -58, 1, 13], [-39, 150, 21, -521, 165, 582, -203, -224, 59, 27], [-81, 285, 150, -1086, -8, 1380, -66, -662, 19, 113], [-339, 1275, 285, -4483, 1061, 5077, -1332, -1987, 355, 245], [-735, 2601, 1275, -9760, 172, 12086, -803, -5497, 218, 845], [-2535, 9405, 2601, -33370, 6295, 38197, -8194, -15168, 2108, 1908], [-5724, 20361, 9405, -75627, 2882, 92155, -7595, -40630, 2004, 5924]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-3, 12, 0, -41, 19, 45, -24, -17, 9, 2], [-6, 21, 12, -82, -3, 109, -3, -58, 1, 13], [-39, 150, 21, -521, 165, 582, -203, -224, 59, 27], [-81, 285, 150, -1086, -8, 1380, -66, -662, 19, 113], [-339, 1275, 285, -4483, 1061, 5077, -1332, -1987, 355, 245], [-735, 2601, 1275, -9760, 172, 12086, -803, -5497, 218, 845], [-2535, 9405, 2601, -33370, 6295, 38197, -8194, -15168, 2108, 1908], [-5724, 20361, 9405, -75627, 2882, 92155, -7595, -40630, 2004, 5924], [-17772, 65364, 20361, -233479, 36929, 269462, -50021, -108303, 12686, 13852]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp9552001 : Fact (Nat.Prime 9552001) := fact_iff.2 (by norm_num)
instance hp20599 : Fact (Nat.Prime 20599) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 3
  a' := [1, 1, 2, 1, 0, 1, 2]
  b' := [2, 1, 2, 2, 1, 0, 2, 2]
  k := [1, 2, 1, 0, 2, 2, 1, 2, 2, 0, 1, 1, 1, 2, 1]
  f := [-1, 4, 0, -13, 7, 15, -8, -5, 3, 1]
  g := [0, 2, 2, 0, 0, 2, 0, 1, 1]
  h := [0, 0, 1]
  a := [2, 2, 0, 2, 0, 0, 2, 2]
  b := [0, 2, 0, 2, 0, 2, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD9552001 : CertificateDedekindCriterionLists l 9552001 where
  n := 2
  a' := [4795929, 9390670, 4071441, 88354, 7182538, 6946284, 7589212, 4977429]
  b' := [1038048, 5230180, 7929540, 1353150, 5032376, 3018081, 7512770, 8213185, 5814953]
  k := [7297852, 9005392, 827067, 1084798, 9129151, 8759520, 7114240, 5903878, 1]
  f := [4984898, 1418121, 373815, 1930678, 1436592, 2785529, 6105676, 4678808, 2039675, 1]
  g := [7214441, 2052388, 541007, 2794192, 2079121, 4031383, 8836497, 6771448, 2951938, 1]
  h := [6600061, 1]
  a := [574596, 712030, 3177071, 6482750, 5880727, 3676936, 3715787, 7308820, 6331490]
  b := [1879120, 8527455, 1960222, 8647174, 8175612, 6434281, 6911263, 5924363, 3220511]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD20599 : CertificateDedekindCriterionLists l 20599 where
  n := 2
  a' := [7539, 19184, 9954, 1688, 18858, 16096, 11555, 13643]
  b' := [757, 5459, 19351, 7499, 5683, 8504, 17464, 1796, 9928]
  k := [2864, 17140, 13304, 7246, 2319, 5588, 14265, 8170, 1]
  f := [14852, 4349, 14235, 5541, 5894, 11257, 11198, 1624, 3274, 1]
  g := [18527, 5424, 17757, 6911, 7352, 14042, 13968, 2025, 4084, 1]
  h := [16513, 1]
  a := [9113, 9133, 11917, 4642, 811, 10849, 19906, 8345, 10529]
  b := [1407, 17581, 4446, 16451, 1852, 10844, 4569, 12758, 10070]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![3, 9552001, 20599]
  exp := ![1, 1, 1]
  pdgood := [3, 9552001, 20599]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp9552001.out
    exact hp20599.out
  a := [-29625308256169, -66006387660288, 161063353536104, 167745056187914, -214773104828997, -100167898131724, 93718788138142, 16276897251738, -12094849382660]
  b := [-7455517481192, 13123711341097, 29853171862096, -38610574070576, -37384292963660, 35271671197293, 15131212816386, -11658828335434, -1869586712827, 1209484938266]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 9552001 T_ofList CD9552001
    exact satisfiesDedekindCriterion_of_certificate_lists T l 20599 T_ofList CD20599

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

end VoightMaximalOrderD10R448

end TraceEuclidean
