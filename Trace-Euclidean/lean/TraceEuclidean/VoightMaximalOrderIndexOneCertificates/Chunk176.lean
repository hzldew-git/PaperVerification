import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk172
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

namespace VoightMaximalOrderD10R93

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2012919003125, [-1, -2, 10, 16, -28, -25, 26, 13, -9, -2, 1], 1⟩
local notation "l" => [-1, -2, 10, 16, -28, -25, 26, 13, -9, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -16, 28, 25, -26, -13, 9, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -16, 28, 25, -26, -13, 9, 2], ![2, 5, -18, -42, 40, 78, -27, -52, 5, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -16, 28, 25, -26, -13, 9, 2], ![2, 5, -18, -42, 40, 78, -27, -52, 5, 13], ![13, 28, -125, -226, 322, 365, -260, -196, 65, 31]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -16, 28, 25, -26, -13, 9, 2], ![2, 5, -18, -42, 40, 78, -27, -52, 5, 13], ![13, 28, -125, -226, 322, 365, -260, -196, 65, 31], ![31, 75, -282, -621, 642, 1097, -441, -663, 83, 127]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -16, 28, 25, -26, -13, 9, 2], ![2, 5, -18, -42, 40, 78, -27, -52, 5, 13], ![13, 28, -125, -226, 322, 365, -260, -196, 65, 31], ![31, 75, -282, -621, 642, 1097, -441, -663, 83, 127], ![127, 285, -1195, -2314, 2935, 3817, -2205, -2092, 480, 337]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -16, 28, 25, -26, -13, 9, 2], ![2, 5, -18, -42, 40, 78, -27, -52, 5, 13], ![13, 28, -125, -226, 322, 365, -260, -196, 65, 31], ![31, 75, -282, -621, 642, 1097, -441, -663, 83, 127], ![127, 285, -1195, -2314, 2935, 3817, -2205, -2092, 480, 337], ![337, 801, -3085, -6587, 7122, 11360, -4945, -6586, 941, 1154]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -16, 28, 25, -26, -13, 9, 2], ![2, 5, -18, -42, 40, 78, -27, -52, 5, 13], ![13, 28, -125, -226, 322, 365, -260, -196, 65, 31], ![31, 75, -282, -621, 642, 1097, -441, -663, 83, 127], ![127, 285, -1195, -2314, 2935, 3817, -2205, -2092, 480, 337], ![337, 801, -3085, -6587, 7122, 11360, -4945, -6586, 941, 1154], ![1154, 2645, -10739, -21549, 25725, 35972, -18644, -19947, 3800, 3249]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -16, 28, 25, -26, -13, 9, 2], ![2, 5, -18, -42, 40, 78, -27, -52, 5, 13], ![13, 28, -125, -226, 322, 365, -260, -196, 65, 31], ![31, 75, -282, -621, 642, 1097, -441, -663, 83, 127], ![127, 285, -1195, -2314, 2935, 3817, -2205, -2092, 480, 337], ![337, 801, -3085, -6587, 7122, 11360, -4945, -6586, 941, 1154], ![1154, 2645, -10739, -21549, 25725, 35972, -18644, -19947, 3800, 3249], ![3249, 7652, -29845, -62723, 69423, 106950, -48502, -60881, 9294, 10298]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -16, 28, 25, -26, -13, 9, 2], ![2, 5, -18, -42, 40, 78, -27, -52, 5, 13], ![13, 28, -125, -226, 322, 365, -260, -196, 65, 31], ![31, 75, -282, -621, 642, 1097, -441, -663, 83, 127], ![127, 285, -1195, -2314, 2935, 3817, -2205, -2092, 480, 337], ![337, 801, -3085, -6587, 7122, 11360, -4945, -6586, 941, 1154], ![1154, 2645, -10739, -21549, 25725, 35972, -18644, -19947, 3800, 3249], ![3249, 7652, -29845, -62723, 69423, 106950, -48502, -60881, 9294, 10298], ![10298, 23845, -95328, -194613, 225621, 326873, -160798, -182376, 31801, 29890]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-31, -13, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-31, -13, -2, -1], [-127, -31, -13, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-31, -13, -2, -1], [-127, -31, -13, -2, -1], [-337, -127, -31, -13, -2, -1]], ![[], [], [], [-1], [-2, -1], [-13, -2, -1], [-31, -13, -2, -1], [-127, -31, -13, -2, -1], [-337, -127, -31, -13, -2, -1], [-1154, -337, -127, -31, -13, -2, -1]], ![[], [], [-1], [-2, -1], [-13, -2, -1], [-31, -13, -2, -1], [-127, -31, -13, -2, -1], [-337, -127, -31, -13, -2, -1], [-1154, -337, -127, -31, -13, -2, -1], [-3249, -1154, -337, -127, -31, -13, -2, -1]], ![[], [-1], [-2, -1], [-13, -2, -1], [-31, -13, -2, -1], [-127, -31, -13, -2, -1], [-337, -127, -31, -13, -2, -1], [-1154, -337, -127, -31, -13, -2, -1], [-3249, -1154, -337, -127, -31, -13, -2, -1], [-10298, -3249, -1154, -337, -127, -31, -13, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -16, 28, 25, -26, -13, 9, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -16, 28, 25, -26, -13, 9, 2], [2, 5, -18, -42, 40, 78, -27, -52, 5, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -16, 28, 25, -26, -13, 9, 2], [2, 5, -18, -42, 40, 78, -27, -52, 5, 13], [13, 28, -125, -226, 322, 365, -260, -196, 65, 31]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -16, 28, 25, -26, -13, 9, 2], [2, 5, -18, -42, 40, 78, -27, -52, 5, 13], [13, 28, -125, -226, 322, 365, -260, -196, 65, 31], [31, 75, -282, -621, 642, 1097, -441, -663, 83, 127]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -16, 28, 25, -26, -13, 9, 2], [2, 5, -18, -42, 40, 78, -27, -52, 5, 13], [13, 28, -125, -226, 322, 365, -260, -196, 65, 31], [31, 75, -282, -621, 642, 1097, -441, -663, 83, 127], [127, 285, -1195, -2314, 2935, 3817, -2205, -2092, 480, 337]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -16, 28, 25, -26, -13, 9, 2], [2, 5, -18, -42, 40, 78, -27, -52, 5, 13], [13, 28, -125, -226, 322, 365, -260, -196, 65, 31], [31, 75, -282, -621, 642, 1097, -441, -663, 83, 127], [127, 285, -1195, -2314, 2935, 3817, -2205, -2092, 480, 337], [337, 801, -3085, -6587, 7122, 11360, -4945, -6586, 941, 1154]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -16, 28, 25, -26, -13, 9, 2], [2, 5, -18, -42, 40, 78, -27, -52, 5, 13], [13, 28, -125, -226, 322, 365, -260, -196, 65, 31], [31, 75, -282, -621, 642, 1097, -441, -663, 83, 127], [127, 285, -1195, -2314, 2935, 3817, -2205, -2092, 480, 337], [337, 801, -3085, -6587, 7122, 11360, -4945, -6586, 941, 1154], [1154, 2645, -10739, -21549, 25725, 35972, -18644, -19947, 3800, 3249]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -16, 28, 25, -26, -13, 9, 2], [2, 5, -18, -42, 40, 78, -27, -52, 5, 13], [13, 28, -125, -226, 322, 365, -260, -196, 65, 31], [31, 75, -282, -621, 642, 1097, -441, -663, 83, 127], [127, 285, -1195, -2314, 2935, 3817, -2205, -2092, 480, 337], [337, 801, -3085, -6587, 7122, 11360, -4945, -6586, 941, 1154], [1154, 2645, -10739, -21549, 25725, 35972, -18644, -19947, 3800, 3249], [3249, 7652, -29845, -62723, 69423, 106950, -48502, -60881, 9294, 10298]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -16, 28, 25, -26, -13, 9, 2], [2, 5, -18, -42, 40, 78, -27, -52, 5, 13], [13, 28, -125, -226, 322, 365, -260, -196, 65, 31], [31, 75, -282, -621, 642, 1097, -441, -663, 83, 127], [127, 285, -1195, -2314, 2935, 3817, -2205, -2092, 480, 337], [337, 801, -3085, -6587, 7122, 11360, -4945, -6586, 941, 1154], [1154, 2645, -10739, -21549, 25725, 35972, -18644, -19947, 3800, 3249], [3249, 7652, -29845, -62723, 69423, 106950, -48502, -60881, 9294, 10298], [10298, 23845, -95328, -194613, 225621, 326873, -160798, -182376, 31801, 29890]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp71 : Fact (Nat.Prime 71) := fact_iff.2 (by norm_num)
instance hp9072311 : Fact (Nat.Prime 9072311) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 4, 1]
  b' := [4, 1, 3, 2, 4]
  k := [1]
  f := [1, 2, 2, 0, 12, 9, 2, -1, 5, 2]
  g := [2, 2, 4, 0, 4, 1]
  h := [2, 2, 4, 0, 4, 1]
  a := [2, 3, 4, 0, 3]
  b := [2, 2, 2, 2, 0, 1, 4, 4, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD71 : CertificateDedekindCriterionLists l 71 where
  n := 2
  a' := [46, 3, 31, 61, 1, 31, 45, 1]
  b' := [51, 16, 43, 60, 40, 64, 18, 63, 63]
  k := [26, 27, 5, 60, 63, 44, 24, 62, 1]
  f := [11, 8, 5, 1, 18, 3, 31, 16, 17, 1]
  g := [20, 14, 9, 2, 32, 4, 57, 28, 30, 1]
  h := [39, 1]
  a := [39, 58, 8, 27, 15, 14, 42, 22, 46]
  b := [7, 47, 26, 0, 66, 30, 38, 8, 25]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD9072311 : CertificateDedekindCriterionLists l 9072311 where
  n := 2
  a' := [4698321, 1351076, 6717351, 1069154, 5752145, 8397397, 2584972, 5222105]
  b' := [8049103, 195154, 3192149, 7517583, 6766166, 2159842, 5069447, 6361244, 6476008]
  k := [8422442, 5055390, 5505546, 8029405, 955117, 3245085, 8180858, 4975384, 1]
  f := [4998273, 3883599, 1331302, 6198352, 6100452, 2848083, 1244910, 5165244, 1805549, 1]
  g := [6886639, 5350836, 1834272, 8540112, 8405224, 3924098, 1715241, 7116692, 2487691, 1]
  h := [6584618, 1]
  a := [557879, 1632337, 8547562, 8088340, 7544024, 2163211, 8825206, 1394593, 8626711]
  b := [1104922, 6058136, 2067633, 952271, 5312368, 3391145, 1519904, 3910262, 445600]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 71, 9072311]
  exp := ![1, 1, 1]
  pdgood := [5, 71, 9072311]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp71.out
    exact hp9072311.out
  a := [3216802388291, -40657961118400, 29548632370862, 102793167248780, -68769867017362, -70657679729996, 39063955169800, 13370477482580, -6132232464600]
  b := [-1610011529348, 1012062877429, 13448008944362, -9570358335520, -19965163511349, 12191462718420, 9859387416688, -4963548179682, -1459692397550, 613223246460]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 71 T_ofList CD71
    exact satisfiesDedekindCriterion_of_certificate_lists T l 9072311 T_ofList CD9072311

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

end VoightMaximalOrderD10R93

namespace VoightMaximalOrderD10R98

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2061312753125, [-1, -2, 22, -2, -46, 4, 34, -1, -10, 0, 1], 1⟩
local notation "l" => [-1, -2, 22, -2, -46, 4, 34, -1, -10, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -22, 2, 46, -4, -34, 1, 10, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -22, 2, 46, -4, -34, 1, 10, 0], ![0, 1, 2, -22, 2, 46, -4, -34, 1, 10]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -22, 2, 46, -4, -34, 1, 10, 0], ![0, 1, 2, -22, 2, 46, -4, -34, 1, 10], ![10, 20, -219, 22, 438, -38, -294, 6, 66, 1]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -22, 2, 46, -4, -34, 1, 10, 0], ![0, 1, 2, -22, 2, 46, -4, -34, 1, 10], ![10, 20, -219, 22, 438, -38, -294, 6, 66, 1], ![1, 12, -2, -217, 68, 434, -72, -293, 16, 66]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -22, 2, 46, -4, -34, 1, 10, 0], ![0, 1, 2, -22, 2, 46, -4, -34, 1, 10], ![10, 20, -219, 22, 438, -38, -294, 6, 66, 1], ![1, 12, -2, -217, 68, 434, -72, -293, 16, 66], ![66, 133, -1440, 130, 2819, -196, -1810, -6, 367, 16]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -22, 2, 46, -4, -34, 1, 10, 0], ![0, 1, 2, -22, 2, 46, -4, -34, 1, 10], ![10, 20, -219, 22, 438, -38, -294, 6, 66, 1], ![1, 12, -2, -217, 68, 434, -72, -293, 16, 66], ![66, 133, -1440, 130, 2819, -196, -1810, -6, 367, 16], ![16, 98, -219, -1408, 866, 2755, -740, -1794, 154, 367]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -22, 2, 46, -4, -34, 1, 10, 0], ![0, 1, 2, -22, 2, 46, -4, -34, 1, 10], ![10, 20, -219, 22, 438, -38, -294, 6, 66, 1], ![1, 12, -2, -217, 68, 434, -72, -293, 16, 66], ![66, 133, -1440, 130, 2819, -196, -1810, -6, 367, 16], ![16, 98, -219, -1408, 866, 2755, -740, -1794, 154, 367], ![367, 750, -7976, 515, 15474, -602, -9723, -373, 1876, 154]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -22, 2, 46, -4, -34, 1, 10, 0], ![0, 1, 2, -22, 2, 46, -4, -34, 1, 10], ![10, 20, -219, 22, 438, -38, -294, 6, 66, 1], ![1, 12, -2, -217, 68, 434, -72, -293, 16, 66], ![66, 133, -1440, 130, 2819, -196, -1810, -6, 367, 16], ![16, 98, -219, -1408, 866, 2755, -740, -1794, 154, 367], ![367, 750, -7976, 515, 15474, -602, -9723, -373, 1876, 154], ![154, 675, -2638, -7668, 7599, 14858, -5838, -9569, 1167, 1876]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -22, 2, 46, -4, -34, 1, 10, 0], ![0, 1, 2, -22, 2, 46, -4, -34, 1, 10], ![10, 20, -219, 22, 438, -38, -294, 6, 66, 1], ![1, 12, -2, -217, 68, 434, -72, -293, 16, 66], ![66, 133, -1440, 130, 2819, -196, -1810, -6, 367, 16], ![16, 98, -219, -1408, 866, 2755, -740, -1794, 154, 367], ![367, 750, -7976, 515, 15474, -602, -9723, -373, 1876, 154], ![154, 675, -2638, -7668, 7599, 14858, -5838, -9569, 1167, 1876], ![1876, 3906, -40597, 1114, 78628, 95, -48926, -3962, 9191, 1167]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-10, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-66, -1, -10, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-66, -1, -10, 0, -1], [-16, -66, -1, -10, 0, -1]], ![[], [], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-66, -1, -10, 0, -1], [-16, -66, -1, -10, 0, -1], [-367, -16, -66, -1, -10, 0, -1]], ![[], [], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-66, -1, -10, 0, -1], [-16, -66, -1, -10, 0, -1], [-367, -16, -66, -1, -10, 0, -1], [-154, -367, -16, -66, -1, -10, 0, -1]], ![[], [-1], [0, -1], [-10, 0, -1], [-1, -10, 0, -1], [-66, -1, -10, 0, -1], [-16, -66, -1, -10, 0, -1], [-367, -16, -66, -1, -10, 0, -1], [-154, -367, -16, -66, -1, -10, 0, -1], [-1876, -154, -367, -16, -66, -1, -10, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -22, 2, 46, -4, -34, 1, 10, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -22, 2, 46, -4, -34, 1, 10, 0], [0, 1, 2, -22, 2, 46, -4, -34, 1, 10]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -22, 2, 46, -4, -34, 1, 10, 0], [0, 1, 2, -22, 2, 46, -4, -34, 1, 10], [10, 20, -219, 22, 438, -38, -294, 6, 66, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -22, 2, 46, -4, -34, 1, 10, 0], [0, 1, 2, -22, 2, 46, -4, -34, 1, 10], [10, 20, -219, 22, 438, -38, -294, 6, 66, 1], [1, 12, -2, -217, 68, 434, -72, -293, 16, 66]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -22, 2, 46, -4, -34, 1, 10, 0], [0, 1, 2, -22, 2, 46, -4, -34, 1, 10], [10, 20, -219, 22, 438, -38, -294, 6, 66, 1], [1, 12, -2, -217, 68, 434, -72, -293, 16, 66], [66, 133, -1440, 130, 2819, -196, -1810, -6, 367, 16]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -22, 2, 46, -4, -34, 1, 10, 0], [0, 1, 2, -22, 2, 46, -4, -34, 1, 10], [10, 20, -219, 22, 438, -38, -294, 6, 66, 1], [1, 12, -2, -217, 68, 434, -72, -293, 16, 66], [66, 133, -1440, 130, 2819, -196, -1810, -6, 367, 16], [16, 98, -219, -1408, 866, 2755, -740, -1794, 154, 367]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -22, 2, 46, -4, -34, 1, 10, 0], [0, 1, 2, -22, 2, 46, -4, -34, 1, 10], [10, 20, -219, 22, 438, -38, -294, 6, 66, 1], [1, 12, -2, -217, 68, 434, -72, -293, 16, 66], [66, 133, -1440, 130, 2819, -196, -1810, -6, 367, 16], [16, 98, -219, -1408, 866, 2755, -740, -1794, 154, 367], [367, 750, -7976, 515, 15474, -602, -9723, -373, 1876, 154]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -22, 2, 46, -4, -34, 1, 10, 0], [0, 1, 2, -22, 2, 46, -4, -34, 1, 10], [10, 20, -219, 22, 438, -38, -294, 6, 66, 1], [1, 12, -2, -217, 68, 434, -72, -293, 16, 66], [66, 133, -1440, 130, 2819, -196, -1810, -6, 367, 16], [16, 98, -219, -1408, 866, 2755, -740, -1794, 154, 367], [367, 750, -7976, 515, 15474, -602, -9723, -373, 1876, 154], [154, 675, -2638, -7668, 7599, 14858, -5838, -9569, 1167, 1876]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -22, 2, 46, -4, -34, 1, 10, 0], [0, 1, 2, -22, 2, 46, -4, -34, 1, 10], [10, 20, -219, 22, 438, -38, -294, 6, 66, 1], [1, 12, -2, -217, 68, 434, -72, -293, 16, 66], [66, 133, -1440, 130, 2819, -196, -1810, -6, 367, 16], [16, 98, -219, -1408, 866, 2755, -740, -1794, 154, 367], [367, 750, -7976, 515, 15474, -602, -9723, -373, 1876, 154], [154, 675, -2638, -7668, 7599, 14858, -5838, -9569, 1167, 1876], [1876, 3906, -40597, 1114, 78628, 95, -48926, -3962, 9191, 1167]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp659620081 : Fact (Nat.Prime 659620081) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1]
  b' := [2, 0, 4, 2, 1]
  k := [1]
  f := [1, 2, -2, 2, 10, 0, -6, 1, 2]
  g := [2, 2, 2, 0, 0, 1]
  h := [2, 2, 2, 0, 0, 1]
  a := [0, 2, 2, 3]
  b := [3, 1, 3, 2, 2, 3, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD659620081 : CertificateDedekindCriterionLists l 659620081 where
  n := 2
  a' := [569376257, 179068828, 112410172, 310205254, 284151617, 293649847, 414159042, 445523906]
  b' := [71716862, 476755361, 265292395, 486653372, 588346497, 380003599, 479649714, 45183125, 97079584]
  k := [429547597, 232205200, 619204835, 324037565, 77877006, 391020735, 416897872, 409089515, 1]
  f := [6664888, 57021737, 281221, 41082342, 105612202, 95391954, 12241578, 68145451, 101476755, 1]
  g := [35095869, 300264222, 1480847, 216330791, 556131175, 502313541, 64461517, 358839311, 534354798, 1]
  h := [125265283, 1]
  a := [134063732, 89004212, 176270636, 304814494, 317685600, 145538424, 583079930, 161199484, 238166898]
  b := [578449904, 364406317, 305378745, 124113363, 492578177, 183005505, 71614607, 286692850, 421453183]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 659620081]
  exp := ![1, 1]
  pdgood := [5, 659620081]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp659620081.out
  a := [-3284711613, 1396165340, 31280775370, 3794483672, -54458394080, -6563112044, 27125849060, 1887183440, -4004787680]
  b := [-6694396, 2439352231, 517451502, -9853726070, -1146233061, 9966475680, 913604262, -3513542442, -188718344, 400478768]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 659620081 T_ofList CD659620081

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

end VoightMaximalOrderD10R98

namespace VoightMaximalOrderD10R99

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2062590684013, [-1, -14, 10, 54, -16, -58, 16, 23, -7, -3, 1], 1⟩
local notation "l" => [-1, -14, 10, 54, -16, -58, 16, 23, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -10, -54, 16, 58, -16, -23, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -10, -54, 16, 58, -16, -23, 7, 3], ![3, 43, -16, -172, -6, 190, 10, -85, -2, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -10, -54, 16, 58, -16, -23, 7, 3], ![3, 43, -16, -172, -6, 190, 10, -85, -2, 16], ![16, 227, -117, -880, 84, 922, -66, -358, 27, 46]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -10, -54, 16, 58, -16, -23, 7, 3], ![3, 43, -16, -172, -6, 190, 10, -85, -2, 16], ![16, 227, -117, -880, 84, 922, -66, -358, 27, 46], ![46, 660, -233, -2601, -144, 2752, 186, -1124, -36, 165]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -10, -54, 16, 58, -16, -23, 7, 3], ![3, 43, -16, -172, -6, 190, 10, -85, -2, 16], ![16, 227, -117, -880, 84, 922, -66, -358, 27, 46], ![46, 660, -233, -2601, -144, 2752, 186, -1124, -36, 165], ![165, 2356, -990, -9143, 39, 9426, 112, -3609, 31, 459]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -10, -54, 16, 58, -16, -23, 7, 3], ![3, 43, -16, -172, -6, 190, 10, -85, -2, 16], ![16, 227, -117, -880, 84, 922, -66, -358, 27, 46], ![46, 660, -233, -2601, -144, 2752, 186, -1124, -36, 165], ![165, 2356, -990, -9143, 39, 9426, 112, -3609, 31, 459], ![459, 6591, -2234, -25776, -1799, 26661, 2082, -10445, -396, 1408]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -10, -54, 16, 58, -16, -23, 7, 3], ![3, 43, -16, -172, -6, 190, 10, -85, -2, 16], ![16, 227, -117, -880, 84, 922, -66, -358, 27, 46], ![46, 660, -233, -2601, -144, 2752, 186, -1124, -36, 165], ![165, 2356, -990, -9143, 39, 9426, 112, -3609, 31, 459], ![459, 6591, -2234, -25776, -1799, 26661, 2082, -10445, -396, 1408], ![1408, 20171, -7489, -78266, -3248, 79865, 4133, -30302, -589, 3828]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -10, -54, 16, 58, -16, -23, 7, 3], ![3, 43, -16, -172, -6, 190, 10, -85, -2, 16], ![16, 227, -117, -880, 84, 922, -66, -358, 27, 46], ![46, 660, -233, -2601, -144, 2752, 186, -1124, -36, 165], ![165, 2356, -990, -9143, 39, 9426, 112, -3609, 31, 459], ![459, 6591, -2234, -25776, -1799, 26661, 2082, -10445, -396, 1408], ![1408, 20171, -7489, -78266, -3248, 79865, 4133, -30302, -589, 3828], ![3828, 55000, -18109, -214201, -17018, 218776, 18617, -83911, -3506, 10895]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 14, -10, -54, 16, 58, -16, -23, 7, 3], ![3, 43, -16, -172, -6, 190, 10, -85, -2, 16], ![16, 227, -117, -880, 84, 922, -66, -358, 27, 46], ![46, 660, -233, -2601, -144, 2752, 186, -1124, -36, 165], ![165, 2356, -990, -9143, 39, 9426, 112, -3609, 31, 459], ![459, 6591, -2234, -25776, -1799, 26661, 2082, -10445, -396, 1408], ![1408, 20171, -7489, -78266, -3248, 79865, 4133, -30302, -589, 3828], ![3828, 55000, -18109, -214201, -17018, 218776, 18617, -83911, -3506, 10895], ![10895, 156358, -53950, -606439, -39881, 614892, 44456, -231968, -7646, 29179]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-165, -46, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-165, -46, -16, -3, -1], [-459, -165, -46, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-165, -46, -16, -3, -1], [-459, -165, -46, -16, -3, -1], [-1408, -459, -165, -46, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-165, -46, -16, -3, -1], [-459, -165, -46, -16, -3, -1], [-1408, -459, -165, -46, -16, -3, -1], [-3828, -1408, -459, -165, -46, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-165, -46, -16, -3, -1], [-459, -165, -46, -16, -3, -1], [-1408, -459, -165, -46, -16, -3, -1], [-3828, -1408, -459, -165, -46, -16, -3, -1], [-10895, -3828, -1408, -459, -165, -46, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -10, -54, 16, 58, -16, -23, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -10, -54, 16, 58, -16, -23, 7, 3], [3, 43, -16, -172, -6, 190, 10, -85, -2, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -10, -54, 16, 58, -16, -23, 7, 3], [3, 43, -16, -172, -6, 190, 10, -85, -2, 16], [16, 227, -117, -880, 84, 922, -66, -358, 27, 46]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -10, -54, 16, 58, -16, -23, 7, 3], [3, 43, -16, -172, -6, 190, 10, -85, -2, 16], [16, 227, -117, -880, 84, 922, -66, -358, 27, 46], [46, 660, -233, -2601, -144, 2752, 186, -1124, -36, 165]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -10, -54, 16, 58, -16, -23, 7, 3], [3, 43, -16, -172, -6, 190, 10, -85, -2, 16], [16, 227, -117, -880, 84, 922, -66, -358, 27, 46], [46, 660, -233, -2601, -144, 2752, 186, -1124, -36, 165], [165, 2356, -990, -9143, 39, 9426, 112, -3609, 31, 459]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -10, -54, 16, 58, -16, -23, 7, 3], [3, 43, -16, -172, -6, 190, 10, -85, -2, 16], [16, 227, -117, -880, 84, 922, -66, -358, 27, 46], [46, 660, -233, -2601, -144, 2752, 186, -1124, -36, 165], [165, 2356, -990, -9143, 39, 9426, 112, -3609, 31, 459], [459, 6591, -2234, -25776, -1799, 26661, 2082, -10445, -396, 1408]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -10, -54, 16, 58, -16, -23, 7, 3], [3, 43, -16, -172, -6, 190, 10, -85, -2, 16], [16, 227, -117, -880, 84, 922, -66, -358, 27, 46], [46, 660, -233, -2601, -144, 2752, 186, -1124, -36, 165], [165, 2356, -990, -9143, 39, 9426, 112, -3609, 31, 459], [459, 6591, -2234, -25776, -1799, 26661, 2082, -10445, -396, 1408], [1408, 20171, -7489, -78266, -3248, 79865, 4133, -30302, -589, 3828]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -10, -54, 16, 58, -16, -23, 7, 3], [3, 43, -16, -172, -6, 190, 10, -85, -2, 16], [16, 227, -117, -880, 84, 922, -66, -358, 27, 46], [46, 660, -233, -2601, -144, 2752, 186, -1124, -36, 165], [165, 2356, -990, -9143, 39, 9426, 112, -3609, 31, 459], [459, 6591, -2234, -25776, -1799, 26661, 2082, -10445, -396, 1408], [1408, 20171, -7489, -78266, -3248, 79865, 4133, -30302, -589, 3828], [3828, 55000, -18109, -214201, -17018, 218776, 18617, -83911, -3506, 10895]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 14, -10, -54, 16, 58, -16, -23, 7, 3], [3, 43, -16, -172, -6, 190, 10, -85, -2, 16], [16, 227, -117, -880, 84, 922, -66, -358, 27, 46], [46, 660, -233, -2601, -144, 2752, 186, -1124, -36, 165], [165, 2356, -990, -9143, 39, 9426, 112, -3609, 31, 459], [459, 6591, -2234, -25776, -1799, 26661, 2082, -10445, -396, 1408], [1408, 20171, -7489, -78266, -3248, 79865, 4133, -30302, -589, 3828], [3828, 55000, -18109, -214201, -17018, 218776, 18617, -83911, -3506, 10895], [10895, 156358, -53950, -606439, -39881, 614892, 44456, -231968, -7646, 29179]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp61 : Fact (Nat.Prime 61) := fact_iff.2 (by norm_num)
instance hp397 : Fact (Nat.Prime 397) := fact_iff.2 (by norm_num)
instance hp3517 : Fact (Nat.Prime 3517) := fact_iff.2 (by norm_num)

def CD61 : CertificateDedekindCriterionLists l 61 where
  n := 2
  a' := [2, 39, 59, 5, 0, 36, 44]
  b' := [5, 31, 19, 51, 8, 52, 2, 25]
  k := [19, 30, 29, 42, 1, 34, 1]
  f := [1, 6, 9, 5, 15, 12, 5, 12, 10, 1]
  g := [15, 43, 7, 58, 49, 7, 47, 46, 1]
  h := [4, 12, 1]
  a := [24, 45, 26, 26, 39, 9, 55, 48]
  b := [31, 49, 59, 7, 17, 10, 47, 26, 13]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD397 : CertificateDedekindCriterionLists l 397 where
  n := 2
  a' := [120, 273, 346, 240, 171, 63, 54]
  b' := [215, 25, 30, 49, 127, 175, 305, 291]
  k := [169, 3, 25, 239, 322, 173, 1]
  f := [253, 446, 386, 239, 25, 263, 312, 103, 67, 1]
  g := [372, 230, 303, 4, 31, 351, 57, 85, 1]
  h := [270, 309, 1]
  a := [32, 40, 41, 93, 225, 312, 261, 125]
  b := [165, 334, 105, 173, 7, 215, 328, 4, 272]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3517 : CertificateDedekindCriterionLists l 3517 where
  n := 2
  a' := [255, 2606, 2007, 2066, 3492, 948, 351, 2141]
  b' := [1192, 1586, 2939, 1917, 2904, 972, 3282, 1939, 1716]
  k := [2601, 2055, 416, 716, 1029, 3361, 2300, 2434, 1]
  f := [193, 143, 247, 29, 106, 184, 53, 200, 457, 1]
  g := [1257, 929, 1607, 186, 690, 1197, 343, 1302, 2974, 1]
  h := [540, 1]
  a := [985, 879, 1352, 972, 633, 2990, 231, 2339, 1268]
  b := [1964, 2448, 839, 1944, 1629, 406, 3268, 2815, 2249]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![61, 397, 3517]
  exp := ![1, 1, 1]
  pdgood := [61, 397, 3517]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp61.out
    exact hp397.out
    exact hp3517.out
  a := [1466762383, -4067913956, -12244773460, 22961353968, 4150201770, -17752178744, 3156177348, 3474101736, -1048611680]
  b := [-110852398, -1334557669, 2800996487, 2421974602, -5102331036, -322220334, 2559348386, -443137864, -378868524, 104861168]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 61 T_ofList CD61
    exact satisfiesDedekindCriterion_of_certificate_lists T l 397 T_ofList CD397
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3517 T_ofList CD3517

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

end VoightMaximalOrderD10R99

namespace VoightMaximalOrderD10R100

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2077116340625, [5, -15, -11, 53, 0, -58, 13, 23, -7, -3, 1], 1⟩
local notation "l" => [5, -15, -11, 53, 0, -58, 13, 23, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 15, 11, -53, 0, 58, -13, -23, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 15, 11, -53, 0, 58, -13, -23, 7, 3], ![-15, 40, 48, -148, -53, 174, 19, -82, -2, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 15, 11, -53, 0, 58, -13, -23, 7, 3], ![-15, 40, 48, -148, -53, 174, 19, -82, -2, 16], ![-80, 225, 216, -800, -148, 875, -34, -349, 30, 46]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 15, 11, -53, 0, 58, -13, -23, 7, 3], ![-15, 40, 48, -148, -53, 174, 19, -82, -2, 16], ![-80, 225, 216, -800, -148, 875, -34, -349, 30, 46], ![-230, 610, 731, -2222, -800, 2520, 277, -1092, -27, 168]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 15, 11, -53, 0, 58, -13, -23, 7, 3], ![-15, 40, 48, -148, -53, 174, 19, -82, -2, 16], ![-80, 225, 216, -800, -148, 875, -34, -349, 30, 46], ![-230, 610, 731, -2222, -800, 2520, 277, -1092, -27, 168], ![-840, 2290, 2458, -8173, -2222, 8944, 336, -3587, 84, 477]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 15, 11, -53, 0, 58, -13, -23, 7, 3], ![-15, 40, 48, -148, -53, 174, 19, -82, -2, 16], ![-80, 225, 216, -800, -148, 875, -34, -349, 30, 46], ![-230, 610, 731, -2222, -800, 2520, 277, -1092, -27, 168], ![-840, 2290, 2458, -8173, -2222, 8944, 336, -3587, 84, 477], ![-2385, 6315, 7537, -22823, -8173, 25444, 2743, -10635, -248, 1515]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 15, 11, -53, 0, 58, -13, -23, 7, 3], ![-15, 40, 48, -148, -53, 174, 19, -82, -2, 16], ![-80, 225, 216, -800, -148, 875, -34, -349, 30, 46], ![-230, 610, 731, -2222, -800, 2520, 277, -1092, -27, 168], ![-840, 2290, 2458, -8173, -2222, 8944, 336, -3587, 84, 477], ![-2385, 6315, 7537, -22823, -8173, 25444, 2743, -10635, -248, 1515], ![-7575, 20340, 22980, -72758, -22823, 79697, 5749, -32102, -30, 4297]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 15, 11, -53, 0, 58, -13, -23, 7, 3], ![-15, 40, 48, -148, -53, 174, 19, -82, -2, 16], ![-80, 225, 216, -800, -148, 875, -34, -349, 30, 46], ![-230, 610, 731, -2222, -800, 2520, 277, -1092, -27, 168], ![-840, 2290, 2458, -8173, -2222, 8944, 336, -3587, 84, 477], ![-2385, 6315, 7537, -22823, -8173, 25444, 2743, -10635, -248, 1515], ![-7575, 20340, 22980, -72758, -22823, 79697, 5749, -32102, -30, 4297], ![-21485, 56880, 67607, -204761, -72758, 226403, 23836, -93082, -2023, 12861]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 15, 11, -53, 0, 58, -13, -23, 7, 3], ![-15, 40, 48, -148, -53, 174, 19, -82, -2, 16], ![-80, 225, 216, -800, -148, 875, -34, -349, 30, 46], ![-230, 610, 731, -2222, -800, 2520, 277, -1092, -27, 168], ![-840, 2290, 2458, -8173, -2222, 8944, 336, -3587, 84, 477], ![-2385, 6315, 7537, -22823, -8173, 25444, 2743, -10635, -248, 1515], ![-7575, 20340, 22980, -72758, -22823, 79697, 5749, -32102, -30, 4297], ![-21485, 56880, 67607, -204761, -72758, 226403, 23836, -93082, -2023, 12861], ![-64305, 171430, 198351, -614026, -204761, 673180, 59210, -271967, -3055, 36560]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-168, -46, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-168, -46, -16, -3, -1], [-477, -168, -46, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-168, -46, -16, -3, -1], [-477, -168, -46, -16, -3, -1], [-1515, -477, -168, -46, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-168, -46, -16, -3, -1], [-477, -168, -46, -16, -3, -1], [-1515, -477, -168, -46, -16, -3, -1], [-4297, -1515, -477, -168, -46, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-168, -46, -16, -3, -1], [-477, -168, -46, -16, -3, -1], [-1515, -477, -168, -46, -16, -3, -1], [-4297, -1515, -477, -168, -46, -16, -3, -1], [-12861, -4297, -1515, -477, -168, -46, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 15, 11, -53, 0, 58, -13, -23, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 15, 11, -53, 0, 58, -13, -23, 7, 3], [-15, 40, 48, -148, -53, 174, 19, -82, -2, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 15, 11, -53, 0, 58, -13, -23, 7, 3], [-15, 40, 48, -148, -53, 174, 19, -82, -2, 16], [-80, 225, 216, -800, -148, 875, -34, -349, 30, 46]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 15, 11, -53, 0, 58, -13, -23, 7, 3], [-15, 40, 48, -148, -53, 174, 19, -82, -2, 16], [-80, 225, 216, -800, -148, 875, -34, -349, 30, 46], [-230, 610, 731, -2222, -800, 2520, 277, -1092, -27, 168]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 15, 11, -53, 0, 58, -13, -23, 7, 3], [-15, 40, 48, -148, -53, 174, 19, -82, -2, 16], [-80, 225, 216, -800, -148, 875, -34, -349, 30, 46], [-230, 610, 731, -2222, -800, 2520, 277, -1092, -27, 168], [-840, 2290, 2458, -8173, -2222, 8944, 336, -3587, 84, 477]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 15, 11, -53, 0, 58, -13, -23, 7, 3], [-15, 40, 48, -148, -53, 174, 19, -82, -2, 16], [-80, 225, 216, -800, -148, 875, -34, -349, 30, 46], [-230, 610, 731, -2222, -800, 2520, 277, -1092, -27, 168], [-840, 2290, 2458, -8173, -2222, 8944, 336, -3587, 84, 477], [-2385, 6315, 7537, -22823, -8173, 25444, 2743, -10635, -248, 1515]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 15, 11, -53, 0, 58, -13, -23, 7, 3], [-15, 40, 48, -148, -53, 174, 19, -82, -2, 16], [-80, 225, 216, -800, -148, 875, -34, -349, 30, 46], [-230, 610, 731, -2222, -800, 2520, 277, -1092, -27, 168], [-840, 2290, 2458, -8173, -2222, 8944, 336, -3587, 84, 477], [-2385, 6315, 7537, -22823, -8173, 25444, 2743, -10635, -248, 1515], [-7575, 20340, 22980, -72758, -22823, 79697, 5749, -32102, -30, 4297]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 15, 11, -53, 0, 58, -13, -23, 7, 3], [-15, 40, 48, -148, -53, 174, 19, -82, -2, 16], [-80, 225, 216, -800, -148, 875, -34, -349, 30, 46], [-230, 610, 731, -2222, -800, 2520, 277, -1092, -27, 168], [-840, 2290, 2458, -8173, -2222, 8944, 336, -3587, 84, 477], [-2385, 6315, 7537, -22823, -8173, 25444, 2743, -10635, -248, 1515], [-7575, 20340, 22980, -72758, -22823, 79697, 5749, -32102, -30, 4297], [-21485, 56880, 67607, -204761, -72758, 226403, 23836, -93082, -2023, 12861]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 15, 11, -53, 0, 58, -13, -23, 7, 3], [-15, 40, 48, -148, -53, 174, 19, -82, -2, 16], [-80, 225, 216, -800, -148, 875, -34, -349, 30, 46], [-230, 610, 731, -2222, -800, 2520, 277, -1092, -27, 168], [-840, 2290, 2458, -8173, -2222, 8944, 336, -3587, 84, 477], [-2385, 6315, 7537, -22823, -8173, 25444, 2743, -10635, -248, 1515], [-7575, 20340, 22980, -72758, -22823, 79697, 5749, -32102, -30, 4297], [-21485, 56880, 67607, -204761, -72758, 226403, 23836, -93082, -2023, 12861], [-64305, 171430, 198351, -614026, -204761, 673180, 59210, -271967, -3055, 36560]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp149 : Fact (Nat.Prime 149) := fact_iff.2 (by norm_num)
instance hp4460921 : Fact (Nat.Prime 4460921) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 2, 4]
  b' := [2, 4, 1, 3, 4]
  k := [1]
  f := [-1, 3, 4, -7, 3, 14, 0, -3, 2, 1]
  g := [0, 3, 3, 1, 1, 1]
  h := [0, 3, 3, 1, 1, 1]
  a := [4, 4, 0, 1, 1]
  b := [4, 0, 3, 2, 4, 0, 4, 3, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD149 : CertificateDedekindCriterionLists l 149 where
  n := 2
  a' := [120, 129, 147, 0, 115, 44, 73, 104]
  b' := [137, 20, 118, 19, 49, 88, 67, 27, 5]
  k := [142, 55, 62, 55, 24, 114, 96, 40, 1]
  f := [27, 28, 23, 52, 49, 39, 49, 47, 34, 1]
  g := [76, 77, 63, 146, 135, 106, 136, 130, 93, 1]
  h := [53, 1]
  a := [86, 113, 116, 16, 65, 40, 89, 77, 2]
  b := [42, 115, 28, 109, 68, 67, 53, 41, 147]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD4460921 : CertificateDedekindCriterionLists l 4460921 where
  n := 2
  a' := [3768443, 1307041, 810397, 1824895, 2932026, 4399396, 2534455, 4147434]
  b' := [21926, 3259181, 723617, 3849477, 3775628, 3499146, 484991, 2939580, 4000095]
  k := [3752457, 767476, 4275789, 1851807, 3687593, 744914, 1077889, 2996386, 1]
  f := [520227, 20147, 375505, 360745, 450606, 315788, 38151, 667358, 612064, 1]
  g := [3169192, 122730, 2287554, 2197634, 2745062, 1923758, 232411, 4065505, 3728652, 1]
  h := [732266, 1]
  a := [894029, 124894, 638155, 3541602, 4039767, 1442514, 2941435, 911624, 2217081]
  b := [4186308, 3390488, 4121143, 495136, 805357, 1295605, 4107414, 1388738, 2243840]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 149, 4460921]
  exp := ![1, 1, 1]
  pdgood := [5, 149, 4460921]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp149.out
    exact hp4460921.out
  a := [-39385806836, -127346234646, 196530463337, 301884962292, -290697740646, -194635532478, 139367533212, 36676400548, -20096852440]
  b := [-13350161355, 16517298608, 56002232450, -48731330335, -69663843379, 48002604300, 30248828888, -17277865694, -4270545628, 2009685244]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 149 T_ofList CD149
    exact satisfiesDedekindCriterion_of_certificate_lists T l 4460921 T_ofList CD4460921

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

end VoightMaximalOrderD10R100

end TraceEuclidean
