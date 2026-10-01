import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk224
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

namespace VoightMaximalOrderD10R682

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6903865824256, [1, 12, 30, -22, -61, 12, 41, -2, -11, 0, 1], 1⟩
local notation "l" => [1, 12, 30, -22, -61, 12, 41, -2, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -30, 22, 61, -12, -41, 2, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -30, 22, 61, -12, -41, 2, 11, 0], ![0, -1, -12, -30, 22, 61, -12, -41, 2, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -30, 22, 61, -12, -41, 2, 11, 0], ![0, -1, -12, -30, 22, 61, -12, -41, 2, 11], ![-11, -132, -331, 230, 641, -110, -390, 10, 80, 2]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -30, 22, 61, -12, -41, 2, 11, 0], ![0, -1, -12, -30, 22, 61, -12, -41, 2, 11], ![-11, -132, -331, 230, 641, -110, -390, 10, 80, 2], ![-2, -35, -192, -287, 352, 617, -192, -386, 32, 80]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -30, 22, 61, -12, -41, 2, 11, 0], ![0, -1, -12, -30, 22, 61, -12, -41, 2, 11], ![-11, -132, -331, 230, 641, -110, -390, 10, 80, 2], ![-2, -35, -192, -287, 352, 617, -192, -386, 32, 80], ![-80, -962, -2435, 1568, 4593, -608, -2663, -32, 494, 32]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -30, 22, 61, -12, -41, 2, 11, 0], ![0, -1, -12, -30, 22, 61, -12, -41, 2, 11], ![-11, -132, -331, 230, 641, -110, -390, 10, 80, 2], ![-2, -35, -192, -287, 352, 617, -192, -386, 32, 80], ![-80, -962, -2435, 1568, 4593, -608, -2663, -32, 494, 32], ![-32, -464, -1922, -1731, 3520, 4209, -1920, -2599, 320, 494]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -30, 22, 61, -12, -41, 2, 11, 0], ![0, -1, -12, -30, 22, 61, -12, -41, 2, 11], ![-11, -132, -331, 230, 641, -110, -390, 10, 80, 2], ![-2, -35, -192, -287, 352, 617, -192, -386, 32, 80], ![-80, -962, -2435, 1568, 4593, -608, -2663, -32, 494, 32], ![-32, -464, -1922, -1731, 3520, 4209, -1920, -2599, 320, 494], ![-494, -5960, -15284, 8946, 28403, -2408, -16045, -932, 2835, 320]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -30, 22, 61, -12, -41, 2, 11, 0], ![0, -1, -12, -30, 22, 61, -12, -41, 2, 11], ![-11, -132, -331, 230, 641, -110, -390, 10, 80, 2], ![-2, -35, -192, -287, 352, 617, -192, -386, 32, 80], ![-80, -962, -2435, 1568, 4593, -608, -2663, -32, 494, 32], ![-32, -464, -1922, -1731, 3520, 4209, -1920, -2599, 320, 494], ![-494, -5960, -15284, 8946, 28403, -2408, -16045, -932, 2835, 320], ![-320, -4334, -15560, -8244, 28466, 24563, -15528, -15405, 2588, 2835]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -30, 22, 61, -12, -41, 2, 11, 0], ![0, -1, -12, -30, 22, 61, -12, -41, 2, 11], ![-11, -132, -331, 230, 641, -110, -390, 10, 80, 2], ![-2, -35, -192, -287, 352, 617, -192, -386, 32, 80], ![-80, -962, -2435, 1568, 4593, -608, -2663, -32, 494, 32], ![-32, -464, -1922, -1731, 3520, 4209, -1920, -2599, 320, 494], ![-494, -5960, -15284, 8946, 28403, -2408, -16045, -932, 2835, 320], ![-320, -4334, -15560, -8244, 28466, 24563, -15528, -15405, 2588, 2835], ![-2835, -34340, -89384, 46810, 164691, -5554, -91672, -9858, 15780, 2588]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-80, -2, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-80, -2, -11, 0, -1], [-32, -80, -2, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-80, -2, -11, 0, -1], [-32, -80, -2, -11, 0, -1], [-494, -32, -80, -2, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-80, -2, -11, 0, -1], [-32, -80, -2, -11, 0, -1], [-494, -32, -80, -2, -11, 0, -1], [-320, -494, -32, -80, -2, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-80, -2, -11, 0, -1], [-32, -80, -2, -11, 0, -1], [-494, -32, -80, -2, -11, 0, -1], [-320, -494, -32, -80, -2, -11, 0, -1], [-2835, -320, -494, -32, -80, -2, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -30, 22, 61, -12, -41, 2, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -30, 22, 61, -12, -41, 2, 11, 0], [0, -1, -12, -30, 22, 61, -12, -41, 2, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -30, 22, 61, -12, -41, 2, 11, 0], [0, -1, -12, -30, 22, 61, -12, -41, 2, 11], [-11, -132, -331, 230, 641, -110, -390, 10, 80, 2]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -30, 22, 61, -12, -41, 2, 11, 0], [0, -1, -12, -30, 22, 61, -12, -41, 2, 11], [-11, -132, -331, 230, 641, -110, -390, 10, 80, 2], [-2, -35, -192, -287, 352, 617, -192, -386, 32, 80]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -30, 22, 61, -12, -41, 2, 11, 0], [0, -1, -12, -30, 22, 61, -12, -41, 2, 11], [-11, -132, -331, 230, 641, -110, -390, 10, 80, 2], [-2, -35, -192, -287, 352, 617, -192, -386, 32, 80], [-80, -962, -2435, 1568, 4593, -608, -2663, -32, 494, 32]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -30, 22, 61, -12, -41, 2, 11, 0], [0, -1, -12, -30, 22, 61, -12, -41, 2, 11], [-11, -132, -331, 230, 641, -110, -390, 10, 80, 2], [-2, -35, -192, -287, 352, 617, -192, -386, 32, 80], [-80, -962, -2435, 1568, 4593, -608, -2663, -32, 494, 32], [-32, -464, -1922, -1731, 3520, 4209, -1920, -2599, 320, 494]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -30, 22, 61, -12, -41, 2, 11, 0], [0, -1, -12, -30, 22, 61, -12, -41, 2, 11], [-11, -132, -331, 230, 641, -110, -390, 10, 80, 2], [-2, -35, -192, -287, 352, 617, -192, -386, 32, 80], [-80, -962, -2435, 1568, 4593, -608, -2663, -32, 494, 32], [-32, -464, -1922, -1731, 3520, 4209, -1920, -2599, 320, 494], [-494, -5960, -15284, 8946, 28403, -2408, -16045, -932, 2835, 320]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -30, 22, 61, -12, -41, 2, 11, 0], [0, -1, -12, -30, 22, 61, -12, -41, 2, 11], [-11, -132, -331, 230, 641, -110, -390, 10, 80, 2], [-2, -35, -192, -287, 352, 617, -192, -386, 32, 80], [-80, -962, -2435, 1568, 4593, -608, -2663, -32, 494, 32], [-32, -464, -1922, -1731, 3520, 4209, -1920, -2599, 320, 494], [-494, -5960, -15284, 8946, 28403, -2408, -16045, -932, 2835, 320], [-320, -4334, -15560, -8244, 28466, 24563, -15528, -15405, 2588, 2835]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -30, 22, 61, -12, -41, 2, 11, 0], [0, -1, -12, -30, 22, 61, -12, -41, 2, 11], [-11, -132, -331, 230, 641, -110, -390, 10, 80, 2], [-2, -35, -192, -287, 352, 617, -192, -386, 32, 80], [-80, -962, -2435, 1568, 4593, -608, -2663, -32, 494, 32], [-32, -464, -1922, -1731, 3520, 4209, -1920, -2599, 320, 494], [-494, -5960, -15284, 8946, 28403, -2408, -16045, -932, 2835, 320], [-320, -4334, -15560, -8244, 28466, 24563, -15528, -15405, 2588, 2835], [-2835, -34340, -89384, 46810, 164691, -5554, -91672, -9858, 15780, 2588]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp17 : Fact (Nat.Prime 17) := fact_iff.2 (by norm_num)
instance hp396591557 : Fact (Nat.Prime 396591557) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1]
  b' := [1, 1]
  k := [1]
  f := [0, -6, -14, 12, 32, -4, -19, 3, 7, 1]
  g := [1, 0, 1, 1, 1, 1]
  h := [1, 0, 1, 1, 1, 1]
  a := [0, 1, 0, 0, 1]
  b := [1, 0, 1, 1, 0, 1, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD17 : CertificateDedekindCriterionLists l 17 where
  n := 2
  a' := [15, 9, 14, 4, 7, 14, 16, 2]
  b' := [16, 14, 14, 11, 8, 3, 12, 12, 13]
  k := [2, 14, 3, 15, 1, 6, 16, 6, 1]
  f := [9, 9, 3, 9, 14, 0, 5, 13, 4, 1]
  g := [11, 11, 5, 9, 12, 0, 9, 15, 3, 1]
  h := [14, 1]
  a := [13, 11, 13, 11, 4, 6, 3]
  b := [8, 11, 7, 10, 5, 8, 14]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD396591557 : CertificateDedekindCriterionLists l 396591557 where
  n := 2
  a' := [247925655, 194971480, 306073405, 328823891, 143805216, 357945959, 341499478, 234695209]
  b' := [330118331, 371647898, 169393979, 317161440, 91462246, 346836152, 258150183, 141028180, 326448583]
  k := [311549850, 76081306, 74931214, 90944136, 67372918, 28599683, 320078198, 355850032, 1]
  f := [29479102, 181971669, 51400002, 86679122, 109692848, 141092466, 65716657, 131715438, 98101554, 1]
  g := [53465715, 330038730, 93223254, 157208358, 198947937, 255896857, 119189113, 238889911, 177925016, 1]
  h := [218666541, 1]
  a := [129498745, 72447374, 126559638, 136214235, 390712760, 163850853, 372196031, 359920083, 111246669]
  b := [214832571, 58052097, 387893624, 284092503, 150431491, 117051919, 236737876, 48502728, 285344888]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 17, 396591557]
  exp := ![1, 1, 1]
  pdgood := [2, 17, 396591557]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp17.out
    exact hp396591557.out
  a := [-159792117346, -148153003812, 856537461750, 537345926324, -1159223219514, -334856227124, 495945844018, 57373446260, -64100261010]
  b := [14439685857, 99939771712, 55974589018, -260483249463, -95791333464, 209499137152, 42261765229, -63696641824, -5737344626, 6410026101]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 17 T_ofList CD17
    exact satisfiesDedekindCriterion_of_certificate_lists T l 396591557 T_ofList CD396591557

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

end VoightMaximalOrderD10R682

namespace VoightMaximalOrderD10R694

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6979543778125, [1, -1, -14, 11, 44, -47, -14, 27, -3, -4, 1], 1⟩
local notation "l" => [1, -1, -14, 11, 44, -47, -14, 27, -3, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 14, -11, -44, 47, 14, -27, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 14, -11, -44, 47, 14, -27, 3, 4], ![-4, 3, 57, -30, -187, 144, 103, -94, -15, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 14, -11, -44, 47, 14, -27, 3, 4], ![-4, 3, 57, -30, -187, 144, 103, -94, -15, 19], ![-19, 15, 269, -152, -866, 706, 410, -410, -37, 61]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 14, -11, -44, 47, 14, -27, 3, 4], ![-4, 3, 57, -30, -187, 144, 103, -94, -15, 19], ![-19, 15, 269, -152, -866, 706, 410, -410, -37, 61], ![-61, 42, 869, -402, -2836, 2001, 1560, -1237, -227, 207]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 14, -11, -44, 47, 14, -27, 3, 4], ![-4, 3, 57, -30, -187, 144, 103, -94, -15, 19], ![-19, 15, 269, -152, -866, 706, 410, -410, -37, 61], ![-61, 42, 869, -402, -2836, 2001, 1560, -1237, -227, 207], ![-207, 146, 2940, -1408, -9510, 6893, 4899, -4029, -616, 601]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 14, -11, -44, 47, 14, -27, 3, 4], ![-4, 3, 57, -30, -187, 144, 103, -94, -15, 19], ![-19, 15, 269, -152, -866, 706, 410, -410, -37, 61], ![-61, 42, 869, -402, -2836, 2001, 1560, -1237, -227, 207], ![-207, 146, 2940, -1408, -9510, 6893, 4899, -4029, -616, 601], ![-601, 394, 8560, -3671, -27852, 18737, 15307, -11328, -2226, 1788]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 14, -11, -44, 47, 14, -27, 3, 4], ![-4, 3, 57, -30, -187, 144, 103, -94, -15, 19], ![-19, 15, 269, -152, -866, 706, 410, -410, -37, 61], ![-61, 42, 869, -402, -2836, 2001, 1560, -1237, -227, 207], ![-207, 146, 2940, -1408, -9510, 6893, 4899, -4029, -616, 601], ![-601, 394, 8560, -3671, -27852, 18737, 15307, -11328, -2226, 1788], ![-1788, 1187, 25426, -11108, -82343, 56184, 43769, -32969, -5964, 4926]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 14, -11, -44, 47, 14, -27, 3, 4], ![-4, 3, 57, -30, -187, 144, 103, -94, -15, 19], ![-19, 15, 269, -152, -866, 706, 410, -410, -37, 61], ![-61, 42, 869, -402, -2836, 2001, 1560, -1237, -227, 207], ![-207, 146, 2940, -1408, -9510, 6893, 4899, -4029, -616, 601], ![-601, 394, 8560, -3671, -27852, 18737, 15307, -11328, -2226, 1788], ![-1788, 1187, 25426, -11108, -82343, 56184, 43769, -32969, -5964, 4926], ![-4926, 3138, 70151, -28760, -227852, 149179, 125148, -89233, -18191, 13740]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 14, -11, -44, 47, 14, -27, 3, 4], ![-4, 3, 57, -30, -187, 144, 103, -94, -15, 19], ![-19, 15, 269, -152, -866, 706, 410, -410, -37, 61], ![-61, 42, 869, -402, -2836, 2001, 1560, -1237, -227, 207], ![-207, 146, 2940, -1408, -9510, 6893, 4899, -4029, -616, 601], ![-601, 394, 8560, -3671, -27852, 18737, 15307, -11328, -2226, 1788], ![-1788, 1187, 25426, -11108, -82343, 56184, 43769, -32969, -5964, 4926], ![-4926, 3138, 70151, -28760, -227852, 149179, 125148, -89233, -18191, 13740], ![-13740, 8814, 195498, -80989, -633320, 417928, 341539, -245832, -48013, 36769]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1], [-207, -61, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1], [-207, -61, -19, -4, -1], [-601, -207, -61, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1], [-207, -61, -19, -4, -1], [-601, -207, -61, -19, -4, -1], [-1788, -601, -207, -61, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1], [-207, -61, -19, -4, -1], [-601, -207, -61, -19, -4, -1], [-1788, -601, -207, -61, -19, -4, -1], [-4926, -1788, -601, -207, -61, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1], [-207, -61, -19, -4, -1], [-601, -207, -61, -19, -4, -1], [-1788, -601, -207, -61, -19, -4, -1], [-4926, -1788, -601, -207, -61, -19, -4, -1], [-13740, -4926, -1788, -601, -207, -61, -19, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 14, -11, -44, 47, 14, -27, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 14, -11, -44, 47, 14, -27, 3, 4], [-4, 3, 57, -30, -187, 144, 103, -94, -15, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 14, -11, -44, 47, 14, -27, 3, 4], [-4, 3, 57, -30, -187, 144, 103, -94, -15, 19], [-19, 15, 269, -152, -866, 706, 410, -410, -37, 61]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 14, -11, -44, 47, 14, -27, 3, 4], [-4, 3, 57, -30, -187, 144, 103, -94, -15, 19], [-19, 15, 269, -152, -866, 706, 410, -410, -37, 61], [-61, 42, 869, -402, -2836, 2001, 1560, -1237, -227, 207]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 14, -11, -44, 47, 14, -27, 3, 4], [-4, 3, 57, -30, -187, 144, 103, -94, -15, 19], [-19, 15, 269, -152, -866, 706, 410, -410, -37, 61], [-61, 42, 869, -402, -2836, 2001, 1560, -1237, -227, 207], [-207, 146, 2940, -1408, -9510, 6893, 4899, -4029, -616, 601]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 14, -11, -44, 47, 14, -27, 3, 4], [-4, 3, 57, -30, -187, 144, 103, -94, -15, 19], [-19, 15, 269, -152, -866, 706, 410, -410, -37, 61], [-61, 42, 869, -402, -2836, 2001, 1560, -1237, -227, 207], [-207, 146, 2940, -1408, -9510, 6893, 4899, -4029, -616, 601], [-601, 394, 8560, -3671, -27852, 18737, 15307, -11328, -2226, 1788]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 14, -11, -44, 47, 14, -27, 3, 4], [-4, 3, 57, -30, -187, 144, 103, -94, -15, 19], [-19, 15, 269, -152, -866, 706, 410, -410, -37, 61], [-61, 42, 869, -402, -2836, 2001, 1560, -1237, -227, 207], [-207, 146, 2940, -1408, -9510, 6893, 4899, -4029, -616, 601], [-601, 394, 8560, -3671, -27852, 18737, 15307, -11328, -2226, 1788], [-1788, 1187, 25426, -11108, -82343, 56184, 43769, -32969, -5964, 4926]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 14, -11, -44, 47, 14, -27, 3, 4], [-4, 3, 57, -30, -187, 144, 103, -94, -15, 19], [-19, 15, 269, -152, -866, 706, 410, -410, -37, 61], [-61, 42, 869, -402, -2836, 2001, 1560, -1237, -227, 207], [-207, 146, 2940, -1408, -9510, 6893, 4899, -4029, -616, 601], [-601, 394, 8560, -3671, -27852, 18737, 15307, -11328, -2226, 1788], [-1788, 1187, 25426, -11108, -82343, 56184, 43769, -32969, -5964, 4926], [-4926, 3138, 70151, -28760, -227852, 149179, 125148, -89233, -18191, 13740]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 14, -11, -44, 47, 14, -27, 3, 4], [-4, 3, 57, -30, -187, 144, 103, -94, -15, 19], [-19, 15, 269, -152, -866, 706, 410, -410, -37, 61], [-61, 42, 869, -402, -2836, 2001, 1560, -1237, -227, 207], [-207, 146, 2940, -1408, -9510, 6893, 4899, -4029, -616, 601], [-601, 394, 8560, -3671, -27852, 18737, 15307, -11328, -2226, 1788], [-1788, 1187, 25426, -11108, -82343, 56184, 43769, -32969, -5964, 4926], [-4926, 3138, 70151, -28760, -227852, 149179, 125148, -89233, -18191, 13740], [-13740, 8814, 195498, -80989, -633320, 417928, 341539, -245832, -48013, 36769]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp3559 : Fact (Nat.Prime 3559) := fact_iff.2 (by norm_num)
instance hp33029 : Fact (Nat.Prime 33029) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 1, 3]
  b' := [2, 0, 2, 4, 1]
  k := [1]
  f := [3, 5, 11, 9, 4, 21, 12, 1, 4, 2]
  g := [4, 3, 4, 4, 3, 1]
  h := [4, 3, 4, 4, 3, 1]
  a := [3, 1, 4, 0, 1]
  b := [3, 2, 3, 2, 3, 1, 3, 2, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD19 : CertificateDedekindCriterionLists l 19 where
  n := 2
  a' := [6, 15, 14, 17, 11, 14, 5, 5]
  b' := [16, 0, 16, 18, 7, 15, 14, 6, 10]
  k := [11, 6, 2, 8, 8, 5, 11, 12, 1]
  f := [4, 1, 6, 8, -1, 6, 8, 5, 3, 1]
  g := [7, 1, 9, 14, 1, 6, 12, 10, 4, 1]
  h := [11, 1]
  a := [4, 3, 11, 6, 15, 8, 12, 3, 12]
  b := [6, 5, 14, 0, 1, 1, 3, 9, 7]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3559 : CertificateDedekindCriterionLists l 3559 where
  n := 2
  a' := [27, 15, 1227, 671, 2936, 2607, 3046, 1158]
  b' := [2939, 2539, 1097, 1382, 1984, 1945, 819, 3508, 2244]
  k := [2752, 712, 572, 8, 2254, 1100, 1300, 517, 1]
  f := [863, 1001, 506, 874, 33, 181, 237, 36, 869, 1]
  g := [2022, 2344, 1184, 2047, 76, 424, 555, 84, 2036, 1]
  h := [1519, 1]
  a := [2490, 3228, 1041, 3144, 2941, 2920, 2958, 2852, 193]
  b := [1280, 3154, 45, 1208, 320, 2065, 3082, 1721, 3366]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD33029 : CertificateDedekindCriterionLists l 33029 where
  n := 2
  a' := [369, 7356, 4538, 22989, 10591, 30998, 11173, 2254]
  b' := [5242, 8862, 12329, 26954, 19725, 9963, 20613, 23896, 18099]
  k := [6905, 13642, 3375, 32955, 7054, 19239, 32036, 31578, 1]
  f := [12997, 638, 14521, 8296, 8888, 2478, 5703, 11822, 8240, 1]
  g := [24903, 1221, 27823, 15894, 17029, 4747, 10927, 22651, 15787, 1]
  h := [17238, 1]
  a := [15452, 9190, 3693, 2807, 2029, 20453, 18752, 30432, 4247]
  b := [21792, 1985, 30853, 17265, 20069, 17715, 28615, 16576, 28782]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 19, 3559, 33029]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 19, 3559, 33029]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp19.out
    exact hp3559.out
    exact hp33029.out
  a := [17755837119, 153480191964, -1186423549489, 1347780797400, 613826020673, -1302603912980, 181230422932, 261984412986, -75862950560]
  b := [6588567074, -48755523227, -5908097321, 296878131223, -291326375220, -99016007657, 189406824273, -23119707688, -29232959321, 7586295056]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19 T_ofList CD19
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3559 T_ofList CD3559
    exact satisfiesDedekindCriterion_of_certificate_lists T l 33029 T_ofList CD33029

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

end VoightMaximalOrderD10R694

namespace VoightMaximalOrderD10R696

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6997289737216, [1, 14, 29, -30, -62, 20, 44, -4, -12, 0, 1], 1⟩
local notation "l" => [1, 14, 29, -30, -62, 20, 44, -4, -12, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -14, -29, 30, 62, -20, -44, 4, 12, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -14, -29, 30, 62, -20, -44, 4, 12, 0], ![0, -1, -14, -29, 30, 62, -20, -44, 4, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -14, -29, 30, 62, -20, -44, 4, 12, 0], ![0, -1, -14, -29, 30, 62, -20, -44, 4, 12], ![-12, -168, -349, 346, 715, -210, -466, 28, 100, 4]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -14, -29, 30, 62, -20, -44, 4, 12, 0], ![0, -1, -14, -29, 30, 62, -20, -44, 4, 12], ![-12, -168, -349, 346, 715, -210, -466, 28, 100, 4], ![-4, -68, -284, -229, 594, 635, -386, -450, 76, 100]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -14, -29, 30, 62, -20, -44, 4, 12, 0], ![0, -1, -14, -29, 30, 62, -20, -44, 4, 12], ![-12, -168, -349, 346, 715, -210, -466, 28, 100, 4], ![-4, -68, -284, -229, 594, 635, -386, -450, 76, 100], ![-100, -1404, -2968, 2716, 5971, -1406, -3765, 14, 750, 76]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -14, -29, 30, 62, -20, -44, 4, 12, 0], ![0, -1, -14, -29, 30, 62, -20, -44, 4, 12], ![-12, -168, -349, 346, 715, -210, -466, 28, 100, 4], ![-4, -68, -284, -229, 594, 635, -386, -450, 76, 100], ![-100, -1404, -2968, 2716, 5971, -1406, -3765, 14, 750, 76], ![-76, -1164, -3608, -688, 7428, 4451, -4750, -3461, 926, 750]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -14, -29, 30, 62, -20, -44, 4, 12, 0], ![0, -1, -14, -29, 30, 62, -20, -44, 4, 12], ![-12, -168, -349, 346, 715, -210, -466, 28, 100, 4], ![-4, -68, -284, -229, 594, 635, -386, -450, 76, 100], ![-100, -1404, -2968, 2716, 5971, -1406, -3765, 14, 750, 76], ![-76, -1164, -3608, -688, 7428, 4451, -4750, -3461, 926, 750], ![-750, -10576, -22914, 18892, 45812, -7572, -28549, -1750, 5539, 926]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -14, -29, 30, 62, -20, -44, 4, 12, 0], ![0, -1, -14, -29, 30, 62, -20, -44, 4, 12], ![-12, -168, -349, 346, 715, -210, -466, 28, 100, 4], ![-4, -68, -284, -229, 594, 635, -386, -450, 76, 100], ![-100, -1404, -2968, 2716, 5971, -1406, -3765, 14, 750, 76], ![-76, -1164, -3608, -688, 7428, 4451, -4750, -3461, 926, 750], ![-750, -10576, -22914, 18892, 45812, -7572, -28549, -1750, 5539, 926], ![-926, -13714, -37430, 4866, 76304, 27292, -48316, -24845, 9362, 5539]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -14, -29, 30, 62, -20, -44, 4, 12, 0], ![0, -1, -14, -29, 30, 62, -20, -44, 4, 12], ![-12, -168, -349, 346, 715, -210, -466, 28, 100, 4], ![-4, -68, -284, -229, 594, 635, -386, -450, 76, 100], ![-100, -1404, -2968, 2716, 5971, -1406, -3765, 14, 750, 76], ![-76, -1164, -3608, -688, 7428, 4451, -4750, -3461, 926, 750], ![-750, -10576, -22914, 18892, 45812, -7572, -28549, -1750, 5539, 926], ![-926, -13714, -37430, 4866, 76304, 27292, -48316, -24845, 9362, 5539], ![-5539, -78472, -174345, 128740, 348284, -34476, -216424, -26160, 41623, 9362]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1], [-100, -4, -12, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1], [-100, -4, -12, 0, -1], [-76, -100, -4, -12, 0, -1]], ![[], [], [], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1], [-100, -4, -12, 0, -1], [-76, -100, -4, -12, 0, -1], [-750, -76, -100, -4, -12, 0, -1]], ![[], [], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1], [-100, -4, -12, 0, -1], [-76, -100, -4, -12, 0, -1], [-750, -76, -100, -4, -12, 0, -1], [-926, -750, -76, -100, -4, -12, 0, -1]], ![[], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1], [-100, -4, -12, 0, -1], [-76, -100, -4, -12, 0, -1], [-750, -76, -100, -4, -12, 0, -1], [-926, -750, -76, -100, -4, -12, 0, -1], [-5539, -926, -750, -76, -100, -4, -12, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -14, -29, 30, 62, -20, -44, 4, 12, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -14, -29, 30, 62, -20, -44, 4, 12, 0], [0, -1, -14, -29, 30, 62, -20, -44, 4, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -14, -29, 30, 62, -20, -44, 4, 12, 0], [0, -1, -14, -29, 30, 62, -20, -44, 4, 12], [-12, -168, -349, 346, 715, -210, -466, 28, 100, 4]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -14, -29, 30, 62, -20, -44, 4, 12, 0], [0, -1, -14, -29, 30, 62, -20, -44, 4, 12], [-12, -168, -349, 346, 715, -210, -466, 28, 100, 4], [-4, -68, -284, -229, 594, 635, -386, -450, 76, 100]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -14, -29, 30, 62, -20, -44, 4, 12, 0], [0, -1, -14, -29, 30, 62, -20, -44, 4, 12], [-12, -168, -349, 346, 715, -210, -466, 28, 100, 4], [-4, -68, -284, -229, 594, 635, -386, -450, 76, 100], [-100, -1404, -2968, 2716, 5971, -1406, -3765, 14, 750, 76]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -14, -29, 30, 62, -20, -44, 4, 12, 0], [0, -1, -14, -29, 30, 62, -20, -44, 4, 12], [-12, -168, -349, 346, 715, -210, -466, 28, 100, 4], [-4, -68, -284, -229, 594, 635, -386, -450, 76, 100], [-100, -1404, -2968, 2716, 5971, -1406, -3765, 14, 750, 76], [-76, -1164, -3608, -688, 7428, 4451, -4750, -3461, 926, 750]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -14, -29, 30, 62, -20, -44, 4, 12, 0], [0, -1, -14, -29, 30, 62, -20, -44, 4, 12], [-12, -168, -349, 346, 715, -210, -466, 28, 100, 4], [-4, -68, -284, -229, 594, 635, -386, -450, 76, 100], [-100, -1404, -2968, 2716, 5971, -1406, -3765, 14, 750, 76], [-76, -1164, -3608, -688, 7428, 4451, -4750, -3461, 926, 750], [-750, -10576, -22914, 18892, 45812, -7572, -28549, -1750, 5539, 926]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -14, -29, 30, 62, -20, -44, 4, 12, 0], [0, -1, -14, -29, 30, 62, -20, -44, 4, 12], [-12, -168, -349, 346, 715, -210, -466, 28, 100, 4], [-4, -68, -284, -229, 594, 635, -386, -450, 76, 100], [-100, -1404, -2968, 2716, 5971, -1406, -3765, 14, 750, 76], [-76, -1164, -3608, -688, 7428, 4451, -4750, -3461, 926, 750], [-750, -10576, -22914, 18892, 45812, -7572, -28549, -1750, 5539, 926], [-926, -13714, -37430, 4866, 76304, 27292, -48316, -24845, 9362, 5539]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -14, -29, 30, 62, -20, -44, 4, 12, 0], [0, -1, -14, -29, 30, 62, -20, -44, 4, 12], [-12, -168, -349, 346, 715, -210, -466, 28, 100, 4], [-4, -68, -284, -229, 594, 635, -386, -450, 76, 100], [-100, -1404, -2968, 2716, 5971, -1406, -3765, 14, 750, 76], [-76, -1164, -3608, -688, 7428, 4451, -4750, -3461, 926, 750], [-750, -10576, -22914, 18892, 45812, -7572, -28549, -1750, 5539, 926], [-926, -13714, -37430, 4866, 76304, 27292, -48316, -24845, 9362, 5539], [-5539, -78472, -174345, 128740, 348284, -34476, -216424, -26160, 41623, 9362]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp2371 : Fact (Nat.Prime 2371) := fact_iff.2 (by norm_num)
instance hp2882029 : Fact (Nat.Prime 2882029) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1]
  b' := [0, 1]
  k := [1]
  f := [0, -6, -14, 15, 31, -9, -21, 2, 6]
  g := [1, 1, 0, 0, 0, 1]
  h := [1, 1, 0, 0, 0, 1]
  a := [0, 0, 0, 1]
  b := [1, 1, 1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2371 : CertificateDedekindCriterionLists l 2371 where
  n := 2
  a' := [1806, 621, 772, 1333, 1701, 417, 1948, 267]
  b' := [2343, 560, 1244, 1860, 357, 2300, 1846, 1275, 1551]
  k := [769, 2014, 2301, 1057, 1744, 1008, 99, 1546, 1]
  f := [461, 1142, 1073, 583, 1378, 168, 238, 17, 521, 1]
  g := [684, 1694, 1591, 864, 2044, 248, 353, 25, 773, 1]
  h := [1598, 1]
  a := [1769, 1145, 1652, 586, 862, 1873, 2304, 1558, 444]
  b := [430, 1328, 140, 2355, 1708, 884, 192, 1264, 1927]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2882029 : CertificateDedekindCriterionLists l 2882029 where
  n := 2
  a' := [32381, 1072810, 1547475, 1191109, 564009, 413847, 2668590, 10680]
  b' := [885730, 2113455, 2724016, 2212692, 469161, 2513781, 2734437, 60215, 1920166]
  k := [412612, 2780007, 288523, 482787, 112629, 74351, 2366431, 1249405, 1]
  f := [79235, 176109, 677868, 581911, 362524, 305174, 780314, 767631, 585099, 1]
  g := [279743, 621761, 2393245, 2054462, 1279906, 1077430, 2754935, 2710155, 2065717, 1]
  h := [816312, 1]
  a := [2776116, 93313, 935043, 2133379, 1291267, 2305538, 2225869, 2679276, 2367398]
  b := [439551, 1508057, 657963, 1709841, 1590909, 1925680, 2463680, 2164047, 514631]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 2371, 2882029]
  exp := ![1, 1, 1]
  pdgood := [2, 2371, 2882029]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp2371.out
    exact hp2882029.out
  a := [364254229222, 2025319740844, -513618633696, -7814342817246, -4578189736140, 3859925804048, 2894139281918, -344945420690, -346622121830]
  b := [-25041974836, -405174600676, -1225562948685, -313936765376, 1581846251283, 922456516516, -510374135990, -372603237431, 34494542069, 34662212183]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2371 T_ofList CD2371
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2882029 T_ofList CD2882029

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

end VoightMaximalOrderD10R696

namespace VoightMaximalOrderD10R697

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7014791637833, [-1, -6, 1, 35, -5, -46, 10, 21, -6, -3, 1], 1⟩
local notation "l" => [-1, -6, 1, 35, -5, -46, 10, 21, -6, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -1, -35, 5, 46, -10, -21, 6, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -1, -35, 5, 46, -10, -21, 6, 3], ![3, 19, 3, -106, -20, 143, 16, -73, -3, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -1, -35, 5, 46, -10, -21, 6, 3], ![3, 19, 3, -106, -20, 143, 16, -73, -3, 15], ![15, 93, 4, -522, -31, 670, -7, -299, 17, 42]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -1, -35, 5, 46, -10, -21, 6, 3], ![3, 19, 3, -106, -20, 143, 16, -73, -3, 15], ![15, 93, 4, -522, -31, 670, -7, -299, 17, 42], ![42, 267, 51, -1466, -312, 1901, 250, -889, -47, 143]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -1, -35, 5, 46, -10, -21, 6, 3], ![3, 19, 3, -106, -20, 143, 16, -73, -3, 15], ![15, 93, 4, -522, -31, 670, -7, -299, 17, 42], ![42, 267, 51, -1466, -312, 1901, 250, -889, -47, 143], ![143, 900, 124, -4954, -751, 6266, 471, -2753, -31, 382]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -1, -35, 5, 46, -10, -21, 6, 3], ![3, 19, 3, -106, -20, 143, 16, -73, -3, 15], ![15, 93, 4, -522, -31, 670, -7, -299, 17, 42], ![42, 267, 51, -1466, -312, 1901, 250, -889, -47, 143], ![143, 900, 124, -4954, -751, 6266, 471, -2753, -31, 382], ![382, 2435, 518, -13246, -3044, 16821, 2446, -7551, -461, 1115]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -1, -35, 5, 46, -10, -21, 6, 3], ![3, 19, 3, -106, -20, 143, 16, -73, -3, 15], ![15, 93, 4, -522, -31, 670, -7, -299, 17, 42], ![42, 267, 51, -1466, -312, 1901, 250, -889, -47, 143], ![143, 900, 124, -4954, -751, 6266, 471, -2753, -31, 382], ![382, 2435, 518, -13246, -3044, 16821, 2446, -7551, -461, 1115], ![1115, 7072, 1320, -38507, -7671, 48246, 5671, -20969, -861, 2884]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -1, -35, 5, 46, -10, -21, 6, 3], ![3, 19, 3, -106, -20, 143, 16, -73, -3, 15], ![15, 93, 4, -522, -31, 670, -7, -299, 17, 42], ![42, 267, 51, -1466, -312, 1901, 250, -889, -47, 143], ![143, 900, 124, -4954, -751, 6266, 471, -2753, -31, 382], ![382, 2435, 518, -13246, -3044, 16821, 2446, -7551, -461, 1115], ![1115, 7072, 1320, -38507, -7671, 48246, 5671, -20969, -861, 2884], ![2884, 18419, 4188, -99620, -24087, 124993, 19406, -54893, -3665, 7791]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -1, -35, 5, 46, -10, -21, 6, 3], ![3, 19, 3, -106, -20, 143, 16, -73, -3, 15], ![15, 93, 4, -522, -31, 670, -7, -299, 17, 42], ![42, 267, 51, -1466, -312, 1901, 250, -889, -47, 143], ![143, 900, 124, -4954, -751, 6266, 471, -2753, -31, 382], ![382, 2435, 518, -13246, -3044, 16821, 2446, -7551, -461, 1115], ![1115, 7072, 1320, -38507, -7671, 48246, 5671, -20969, -861, 2884], ![2884, 18419, 4188, -99620, -24087, 124993, 19406, -54893, -3665, 7791], ![7791, 49630, 10628, -268497, -60665, 334299, 47083, -144205, -8147, 19708]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1], [-143, -42, -15, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1], [-143, -42, -15, -3, -1], [-382, -143, -42, -15, -3, -1]], ![[], [], [], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1], [-143, -42, -15, -3, -1], [-382, -143, -42, -15, -3, -1], [-1115, -382, -143, -42, -15, -3, -1]], ![[], [], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1], [-143, -42, -15, -3, -1], [-382, -143, -42, -15, -3, -1], [-1115, -382, -143, -42, -15, -3, -1], [-2884, -1115, -382, -143, -42, -15, -3, -1]], ![[], [-1], [-3, -1], [-15, -3, -1], [-42, -15, -3, -1], [-143, -42, -15, -3, -1], [-382, -143, -42, -15, -3, -1], [-1115, -382, -143, -42, -15, -3, -1], [-2884, -1115, -382, -143, -42, -15, -3, -1], [-7791, -2884, -1115, -382, -143, -42, -15, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -1, -35, 5, 46, -10, -21, 6, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -1, -35, 5, 46, -10, -21, 6, 3], [3, 19, 3, -106, -20, 143, 16, -73, -3, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -1, -35, 5, 46, -10, -21, 6, 3], [3, 19, 3, -106, -20, 143, 16, -73, -3, 15], [15, 93, 4, -522, -31, 670, -7, -299, 17, 42]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -1, -35, 5, 46, -10, -21, 6, 3], [3, 19, 3, -106, -20, 143, 16, -73, -3, 15], [15, 93, 4, -522, -31, 670, -7, -299, 17, 42], [42, 267, 51, -1466, -312, 1901, 250, -889, -47, 143]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -1, -35, 5, 46, -10, -21, 6, 3], [3, 19, 3, -106, -20, 143, 16, -73, -3, 15], [15, 93, 4, -522, -31, 670, -7, -299, 17, 42], [42, 267, 51, -1466, -312, 1901, 250, -889, -47, 143], [143, 900, 124, -4954, -751, 6266, 471, -2753, -31, 382]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -1, -35, 5, 46, -10, -21, 6, 3], [3, 19, 3, -106, -20, 143, 16, -73, -3, 15], [15, 93, 4, -522, -31, 670, -7, -299, 17, 42], [42, 267, 51, -1466, -312, 1901, 250, -889, -47, 143], [143, 900, 124, -4954, -751, 6266, 471, -2753, -31, 382], [382, 2435, 518, -13246, -3044, 16821, 2446, -7551, -461, 1115]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -1, -35, 5, 46, -10, -21, 6, 3], [3, 19, 3, -106, -20, 143, 16, -73, -3, 15], [15, 93, 4, -522, -31, 670, -7, -299, 17, 42], [42, 267, 51, -1466, -312, 1901, 250, -889, -47, 143], [143, 900, 124, -4954, -751, 6266, 471, -2753, -31, 382], [382, 2435, 518, -13246, -3044, 16821, 2446, -7551, -461, 1115], [1115, 7072, 1320, -38507, -7671, 48246, 5671, -20969, -861, 2884]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -1, -35, 5, 46, -10, -21, 6, 3], [3, 19, 3, -106, -20, 143, 16, -73, -3, 15], [15, 93, 4, -522, -31, 670, -7, -299, 17, 42], [42, 267, 51, -1466, -312, 1901, 250, -889, -47, 143], [143, 900, 124, -4954, -751, 6266, 471, -2753, -31, 382], [382, 2435, 518, -13246, -3044, 16821, 2446, -7551, -461, 1115], [1115, 7072, 1320, -38507, -7671, 48246, 5671, -20969, -861, 2884], [2884, 18419, 4188, -99620, -24087, 124993, 19406, -54893, -3665, 7791]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -1, -35, 5, 46, -10, -21, 6, 3], [3, 19, 3, -106, -20, 143, 16, -73, -3, 15], [15, 93, 4, -522, -31, 670, -7, -299, 17, 42], [42, 267, 51, -1466, -312, 1901, 250, -889, -47, 143], [143, 900, 124, -4954, -751, 6266, 471, -2753, -31, 382], [382, 2435, 518, -13246, -3044, 16821, 2446, -7551, -461, 1115], [1115, 7072, 1320, -38507, -7671, 48246, 5671, -20969, -861, 2884], [2884, 18419, 4188, -99620, -24087, 124993, 19406, -54893, -3665, 7791], [7791, 49630, 10628, -268497, -60665, 334299, 47083, -144205, -8147, 19708]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp71 : Fact (Nat.Prime 71) := fact_iff.2 (by norm_num)
instance hp2016324127 : Fact (Nat.Prime 2016324127) := fact_iff.2 (by norm_num)

def CD7 : CertificateDedekindCriterionLists l 7 where
  n := 2
  a' := [0, 0, 5, 4, 0, 4, 5]
  b' := [2, 1, 5, 0, 4, 1, 4, 2]
  k := [5, 2, 4, 5, 4, 4, 1]
  f := [1, 2, 2, -3, 3, 9, 1, -1, 2, 1]
  g := [3, 4, 6, 5, 5, 6, 6, 4, 1]
  h := [2, 0, 1]
  a := [2, 4, 3, 4, 0, 4, 2, 6]
  b := [2, 4, 2, 3, 5, 2, 1, 3, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD71 : CertificateDedekindCriterionLists l 71 where
  n := 2
  a' := [64, 70, 58, 9, 20, 42, 59, 20]
  b' := [54, 67, 7, 49, 25, 51, 11, 56, 53]
  k := [51, 11, 32, 29, 25, 58, 23, 43, 1]
  f := [23, 8, 38, 3, 15, 28, 18, 19, 14, 1]
  g := [34, 11, 56, 4, 22, 40, 26, 28, 20, 1]
  h := [48, 1]
  a := [58, 7, 16, 19, 58, 50, 69, 7, 37]
  b := [13, 15, 28, 50, 59, 50, 55, 2, 34]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2016324127 : CertificateDedekindCriterionLists l 2016324127 where
  n := 2
  a' := [635192579, 171954909, 823819832, 36923602, 1458731020, 464359415, 6956414, 1035906359]
  b' := [867712733, 1744391227, 1902406374, 545140998, 835798503, 1949797331, 461715459, 468077043, 1005079364]
  k := [639292897, 1897992106, 1306276984, 466599385, 1303561733, 51055225, 380014530, 265622356, 1]
  f := [333186631, 846231380, 172912989, 263484539, 54504433, 50140769, 799026528, 435010014, 495333028, 1]
  g := [767477654, 1949248900, 398295856, 606922598, 125548057, 115496590, 1840515039, 1002022390, 1140973240, 1]
  h := [875350884, 1]
  a := [205487005, 117955191, 602441859, 960685884, 1958223807, 16618782, 1182552858, 7682568, 780435532]
  b := [1915288972, 488665971, 1887483052, 1196634090, 192082107, 1701473938, 751947217, 1585133064, 1235888595]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![7, 71, 2016324127]
  exp := ![1, 1, 1]
  pdgood := [7, 71, 2016324127]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp7.out
    exact hp71.out
    exact hp2016324127.out
  a := [11922540387421, -52165690070372, -20382435527223, 132688636288090, -13709486983272, -89899015364252, 24123155966760, 16998347651814, -5865036564420]
  b := [-2154108913090, -3946295013389, 18537515072608, 3420905394297, -26760796163617, 2862568924254, 12797716520240, -3081237516570, -1875785862114, 586503656442]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T l 71 T_ofList CD71
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2016324127 T_ofList CD2016324127

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

end VoightMaximalOrderD10R697

end TraceEuclidean
