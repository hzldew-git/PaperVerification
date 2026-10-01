import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk173
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

namespace VoightMaximalOrderD10R104

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2109137628125, [1, 11, 26, -25, -57, 16, 40, -3, -11, 0, 1], 1⟩
local notation "l" => [1, 11, 26, -25, -57, 16, 40, -3, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -26, 25, 57, -16, -40, 3, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -26, 25, 57, -16, -40, 3, 11, 0], ![0, -1, -11, -26, 25, 57, -16, -40, 3, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -26, 25, 57, -16, -40, 3, 11, 0], ![0, -1, -11, -26, 25, 57, -16, -40, 3, 11], ![-11, -121, -287, 264, 601, -151, -383, 17, 81, 3]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -26, 25, 57, -16, -40, 3, 11, 0], ![0, -1, -11, -26, 25, 57, -16, -40, 3, 11], ![-11, -121, -287, 264, 601, -151, -383, 17, 81, 3], ![-3, -44, -199, -212, 435, 553, -271, -374, 50, 81]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -26, 25, 57, -16, -40, 3, 11, 0], ![0, -1, -11, -26, 25, 57, -16, -40, 3, 11], ![-11, -121, -287, 264, 601, -151, -383, 17, 81, 3], ![-3, -44, -199, -212, 435, 553, -271, -374, 50, 81], ![-81, -894, -2150, 1826, 4405, -861, -2687, -28, 517, 50]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -26, 25, 57, -16, -40, 3, 11, 0], ![0, -1, -11, -26, 25, 57, -16, -40, 3, 11], ![-11, -121, -287, 264, 601, -151, -383, 17, 81, 3], ![-3, -44, -199, -212, 435, 553, -271, -374, 50, 81], ![-81, -894, -2150, 1826, 4405, -861, -2687, -28, 517, 50], ![-50, -631, -2194, -900, 4676, 3605, -2861, -2537, 522, 517]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -26, 25, 57, -16, -40, 3, 11, 0], ![0, -1, -11, -26, 25, 57, -16, -40, 3, 11], ![-11, -121, -287, 264, 601, -151, -383, 17, 81, 3], ![-3, -44, -199, -212, 435, 553, -271, -374, 50, 81], ![-81, -894, -2150, 1826, 4405, -861, -2687, -28, 517, 50], ![-50, -631, -2194, -900, 4676, 3605, -2861, -2537, 522, 517], ![-517, -5737, -14073, 10731, 28569, -3596, -17075, -1310, 3150, 522]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -26, 25, 57, -16, -40, 3, 11, 0], ![0, -1, -11, -26, 25, 57, -16, -40, 3, 11], ![-11, -121, -287, 264, 601, -151, -383, 17, 81, 3], ![-3, -44, -199, -212, 435, 553, -271, -374, 50, 81], ![-81, -894, -2150, 1826, 4405, -861, -2687, -28, 517, 50], ![-50, -631, -2194, -900, 4676, 3605, -2861, -2537, 522, 517], ![-517, -5737, -14073, 10731, 28569, -3596, -17075, -1310, 3150, 522], ![-522, -6259, -19309, -1023, 40485, 20217, -24476, -15509, 4432, 3150]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -11, -26, 25, 57, -16, -40, 3, 11, 0], ![0, -1, -11, -26, 25, 57, -16, -40, 3, 11], ![-11, -121, -287, 264, 601, -151, -383, 17, 81, 3], ![-3, -44, -199, -212, 435, 553, -271, -374, 50, 81], ![-81, -894, -2150, 1826, 4405, -861, -2687, -28, 517, 50], ![-50, -631, -2194, -900, 4676, 3605, -2861, -2537, 522, 517], ![-517, -5737, -14073, 10731, 28569, -3596, -17075, -1310, 3150, 522], ![-522, -6259, -19309, -1023, 40485, 20217, -24476, -15509, 4432, 3150], ![-3150, -35172, -88159, 59441, 178527, -9915, -105783, -15026, 19141, 4432]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-81, -3, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-81, -3, -11, 0, -1], [-50, -81, -3, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-81, -3, -11, 0, -1], [-50, -81, -3, -11, 0, -1], [-517, -50, -81, -3, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-81, -3, -11, 0, -1], [-50, -81, -3, -11, 0, -1], [-517, -50, -81, -3, -11, 0, -1], [-522, -517, -50, -81, -3, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-81, -3, -11, 0, -1], [-50, -81, -3, -11, 0, -1], [-517, -50, -81, -3, -11, 0, -1], [-522, -517, -50, -81, -3, -11, 0, -1], [-3150, -522, -517, -50, -81, -3, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -26, 25, 57, -16, -40, 3, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -26, 25, 57, -16, -40, 3, 11, 0], [0, -1, -11, -26, 25, 57, -16, -40, 3, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -26, 25, 57, -16, -40, 3, 11, 0], [0, -1, -11, -26, 25, 57, -16, -40, 3, 11], [-11, -121, -287, 264, 601, -151, -383, 17, 81, 3]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -26, 25, 57, -16, -40, 3, 11, 0], [0, -1, -11, -26, 25, 57, -16, -40, 3, 11], [-11, -121, -287, 264, 601, -151, -383, 17, 81, 3], [-3, -44, -199, -212, 435, 553, -271, -374, 50, 81]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -26, 25, 57, -16, -40, 3, 11, 0], [0, -1, -11, -26, 25, 57, -16, -40, 3, 11], [-11, -121, -287, 264, 601, -151, -383, 17, 81, 3], [-3, -44, -199, -212, 435, 553, -271, -374, 50, 81], [-81, -894, -2150, 1826, 4405, -861, -2687, -28, 517, 50]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -26, 25, 57, -16, -40, 3, 11, 0], [0, -1, -11, -26, 25, 57, -16, -40, 3, 11], [-11, -121, -287, 264, 601, -151, -383, 17, 81, 3], [-3, -44, -199, -212, 435, 553, -271, -374, 50, 81], [-81, -894, -2150, 1826, 4405, -861, -2687, -28, 517, 50], [-50, -631, -2194, -900, 4676, 3605, -2861, -2537, 522, 517]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -26, 25, 57, -16, -40, 3, 11, 0], [0, -1, -11, -26, 25, 57, -16, -40, 3, 11], [-11, -121, -287, 264, 601, -151, -383, 17, 81, 3], [-3, -44, -199, -212, 435, 553, -271, -374, 50, 81], [-81, -894, -2150, 1826, 4405, -861, -2687, -28, 517, 50], [-50, -631, -2194, -900, 4676, 3605, -2861, -2537, 522, 517], [-517, -5737, -14073, 10731, 28569, -3596, -17075, -1310, 3150, 522]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -26, 25, 57, -16, -40, 3, 11, 0], [0, -1, -11, -26, 25, 57, -16, -40, 3, 11], [-11, -121, -287, 264, 601, -151, -383, 17, 81, 3], [-3, -44, -199, -212, 435, 553, -271, -374, 50, 81], [-81, -894, -2150, 1826, 4405, -861, -2687, -28, 517, 50], [-50, -631, -2194, -900, 4676, 3605, -2861, -2537, 522, 517], [-517, -5737, -14073, 10731, 28569, -3596, -17075, -1310, 3150, 522], [-522, -6259, -19309, -1023, 40485, 20217, -24476, -15509, 4432, 3150]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -11, -26, 25, 57, -16, -40, 3, 11, 0], [0, -1, -11, -26, 25, 57, -16, -40, 3, 11], [-11, -121, -287, 264, 601, -151, -383, 17, 81, 3], [-3, -44, -199, -212, 435, 553, -271, -374, 50, 81], [-81, -894, -2150, 1826, 4405, -861, -2687, -28, 517, 50], [-50, -631, -2194, -900, 4676, 3605, -2861, -2537, 522, 517], [-517, -5737, -14073, 10731, 28569, -3596, -17075, -1310, 3150, 522], [-522, -6259, -19309, -1023, 40485, 20217, -24476, -15509, 4432, 3150], [-3150, -35172, -88159, 59441, 178527, -9915, -105783, -15026, 19141, 4432]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp61356731 : Fact (Nat.Prime 61356731) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 2]
  b' := [0, 0, 1, 3, 3]
  k := [1]
  f := [0, -1, -3, 7, 14, -2, -6, 1, 3]
  g := [1, 3, 1, 2, 0, 1]
  h := [1, 3, 1, 2, 0, 1]
  a := [2, 4, 2, 4, 3]
  b := [1, 4, 2, 3, 0, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [10, 1, 1, 8, 6, 2, 7]
  b' := [10, 5, 2, 5, 7, 9, 9, 9]
  k := [5, 4, 7, 8, 1, 10, 5, 5, 1]
  f := [1, 1, -1, 5, 6, 1, -2, 3, 4, 1]
  g := [4, 6, 3, 9, 0, 9, 3, 9, 8, 1]
  h := [3, 1]
  a := [2, 0, 4, 3, 5, 3, 6, 5, 7]
  b := [8, 4, 4, 10, 2, 8, 8, 1, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD61356731 : CertificateDedekindCriterionLists l 61356731 where
  n := 2
  a' := [34604491, 39430850, 50488579, 7294518, 55354703, 26926979, 20504322, 17095180]
  b' := [30087854, 9360715, 45558055, 9000509, 31654936, 54968387, 24307816, 44219417, 52639852]
  k := [10802164, 8647135, 16506521, 55759436, 21431646, 26018212, 4484330, 58498091, 1]
  f := [60949, 418800, 814601, 1312197, 464229, 1340604, 1406646, 511262, 1396024, 1]
  g := [2616371, 17977917, 34968542, 56328942, 19928020, 57548386, 60383359, 21947013, 59927411, 1]
  h := [1429320, 1]
  a := [21698895, 40586570, 40999932, 1021431, 20423935, 131578, 1014856, 12833071, 12019862]
  b := [14214599, 20119925, 23734291, 29378552, 40992245, 53386292, 58427718, 17868860, 49336869]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 11, 61356731]
  exp := ![1, 1, 1]
  pdgood := [5, 11, 61356731]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp11.out
    exact hp61356731.out
  a := [-67075135457, 16455526020, 298406059425, 20045973340, -336907939685, -38418002980, 134488878944, 10855053410, -16916700780]
  b := [6404523242, 35303250493, -8263009659, -79053009231, -2385443093, 58571290681, 4707408978, -17170562066, -1085505341, 1691670078]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 61356731 T_ofList CD61356731

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

end VoightMaximalOrderD10R104

namespace VoightMaximalOrderD10R107

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2112566804973, [-1, 1, 13, -1, -34, -1, 31, 0, -10, 0, 1], 1⟩
local notation "l" => [-1, 1, 13, -1, -34, -1, 31, 0, -10, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -13, 1, 34, 1, -31, 0, 10, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -13, 1, 34, 1, -31, 0, 10, 0], ![0, 1, -1, -13, 1, 34, 1, -31, 0, 10]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -13, 1, 34, 1, -31, 0, 10, 0], ![0, 1, -1, -13, 1, 34, 1, -31, 0, 10], ![10, -10, -129, 9, 327, 11, -276, 1, 69, 0]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -13, 1, 34, 1, -31, 0, 10, 0], ![0, 1, -1, -13, 1, 34, 1, -31, 0, 10], ![10, -10, -129, 9, 327, 11, -276, 1, 69, 0], ![0, 10, -10, -129, 9, 327, 11, -276, 1, 69]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -13, 1, 34, 1, -31, 0, 10, 0], ![0, 1, -1, -13, 1, 34, 1, -31, 0, 10], ![10, -10, -129, 9, 327, 11, -276, 1, 69, 0], ![0, 10, -10, -129, 9, 327, 11, -276, 1, 69], ![69, -69, -887, 59, 2217, 78, -1812, 11, 414, 1]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -13, 1, 34, 1, -31, 0, 10, 0], ![0, 1, -1, -13, 1, 34, 1, -31, 0, 10], ![10, -10, -129, 9, 327, 11, -276, 1, 69, 0], ![0, 10, -10, -129, 9, 327, 11, -276, 1, 69], ![69, -69, -887, 59, 2217, 78, -1812, 11, 414, 1], ![1, 68, -82, -886, 93, 2218, 47, -1812, 21, 414]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -13, 1, 34, 1, -31, 0, 10, 0], ![0, 1, -1, -13, 1, 34, 1, -31, 0, 10], ![10, -10, -129, 9, 327, 11, -276, 1, 69, 0], ![0, 10, -10, -129, 9, 327, 11, -276, 1, 69], ![69, -69, -887, 59, 2217, 78, -1812, 11, 414, 1], ![1, 68, -82, -886, 93, 2218, 47, -1812, 21, 414], ![414, -413, -5314, 332, 13190, 507, -10616, 47, 2328, 21]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -13, 1, 34, 1, -31, 0, 10, 0], ![0, 1, -1, -13, 1, 34, 1, -31, 0, 10], ![10, -10, -129, 9, 327, 11, -276, 1, 69, 0], ![0, 10, -10, -129, 9, 327, 11, -276, 1, 69], ![69, -69, -887, 59, 2217, 78, -1812, 11, 414, 1], ![1, 68, -82, -886, 93, 2218, 47, -1812, 21, 414], ![414, -413, -5314, 332, 13190, 507, -10616, 47, 2328, 21], ![21, 393, -686, -5293, 1046, 13211, -144, -10616, 257, 2328]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -13, 1, 34, 1, -31, 0, 10, 0], ![0, 1, -1, -13, 1, 34, 1, -31, 0, 10], ![10, -10, -129, 9, 327, 11, -276, 1, 69, 0], ![0, 10, -10, -129, 9, 327, 11, -276, 1, 69], ![69, -69, -887, 59, 2217, 78, -1812, 11, 414, 1], ![1, 68, -82, -886, 93, 2218, 47, -1812, 21, 414], ![414, -413, -5314, 332, 13190, 507, -10616, 47, 2328, 21], ![21, 393, -686, -5293, 1046, 13211, -144, -10616, 257, 2328], ![2328, -2307, -29871, 1642, 73859, 3374, -58957, -144, 12664, 257]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-10, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-10, 0, -1], [0, -10, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-10, 0, -1], [0, -10, 0, -1], [-69, 0, -10, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-10, 0, -1], [0, -10, 0, -1], [-69, 0, -10, 0, -1], [-1, -69, 0, -10, 0, -1]], ![[], [], [], [-1], [0, -1], [-10, 0, -1], [0, -10, 0, -1], [-69, 0, -10, 0, -1], [-1, -69, 0, -10, 0, -1], [-414, -1, -69, 0, -10, 0, -1]], ![[], [], [-1], [0, -1], [-10, 0, -1], [0, -10, 0, -1], [-69, 0, -10, 0, -1], [-1, -69, 0, -10, 0, -1], [-414, -1, -69, 0, -10, 0, -1], [-21, -414, -1, -69, 0, -10, 0, -1]], ![[], [-1], [0, -1], [-10, 0, -1], [0, -10, 0, -1], [-69, 0, -10, 0, -1], [-1, -69, 0, -10, 0, -1], [-414, -1, -69, 0, -10, 0, -1], [-21, -414, -1, -69, 0, -10, 0, -1], [-2328, -21, -414, -1, -69, 0, -10, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -13, 1, 34, 1, -31, 0, 10, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -13, 1, 34, 1, -31, 0, 10, 0], [0, 1, -1, -13, 1, 34, 1, -31, 0, 10]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -13, 1, 34, 1, -31, 0, 10, 0], [0, 1, -1, -13, 1, 34, 1, -31, 0, 10], [10, -10, -129, 9, 327, 11, -276, 1, 69, 0]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -13, 1, 34, 1, -31, 0, 10, 0], [0, 1, -1, -13, 1, 34, 1, -31, 0, 10], [10, -10, -129, 9, 327, 11, -276, 1, 69, 0], [0, 10, -10, -129, 9, 327, 11, -276, 1, 69]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -13, 1, 34, 1, -31, 0, 10, 0], [0, 1, -1, -13, 1, 34, 1, -31, 0, 10], [10, -10, -129, 9, 327, 11, -276, 1, 69, 0], [0, 10, -10, -129, 9, 327, 11, -276, 1, 69], [69, -69, -887, 59, 2217, 78, -1812, 11, 414, 1]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -13, 1, 34, 1, -31, 0, 10, 0], [0, 1, -1, -13, 1, 34, 1, -31, 0, 10], [10, -10, -129, 9, 327, 11, -276, 1, 69, 0], [0, 10, -10, -129, 9, 327, 11, -276, 1, 69], [69, -69, -887, 59, 2217, 78, -1812, 11, 414, 1], [1, 68, -82, -886, 93, 2218, 47, -1812, 21, 414]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -13, 1, 34, 1, -31, 0, 10, 0], [0, 1, -1, -13, 1, 34, 1, -31, 0, 10], [10, -10, -129, 9, 327, 11, -276, 1, 69, 0], [0, 10, -10, -129, 9, 327, 11, -276, 1, 69], [69, -69, -887, 59, 2217, 78, -1812, 11, 414, 1], [1, 68, -82, -886, 93, 2218, 47, -1812, 21, 414], [414, -413, -5314, 332, 13190, 507, -10616, 47, 2328, 21]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -13, 1, 34, 1, -31, 0, 10, 0], [0, 1, -1, -13, 1, 34, 1, -31, 0, 10], [10, -10, -129, 9, 327, 11, -276, 1, 69, 0], [0, 10, -10, -129, 9, 327, 11, -276, 1, 69], [69, -69, -887, 59, 2217, 78, -1812, 11, 414, 1], [1, 68, -82, -886, 93, 2218, 47, -1812, 21, 414], [414, -413, -5314, 332, 13190, 507, -10616, 47, 2328, 21], [21, 393, -686, -5293, 1046, 13211, -144, -10616, 257, 2328]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -13, 1, 34, 1, -31, 0, 10, 0], [0, 1, -1, -13, 1, 34, 1, -31, 0, 10], [10, -10, -129, 9, 327, 11, -276, 1, 69, 0], [0, 10, -10, -129, 9, 327, 11, -276, 1, 69], [69, -69, -887, 59, 2217, 78, -1812, 11, 414, 1], [1, 68, -82, -886, 93, 2218, 47, -1812, 21, 414], [414, -413, -5314, 332, 13190, 507, -10616, 47, 2328, 21], [21, 393, -686, -5293, 1046, 13211, -144, -10616, 257, 2328], [2328, -2307, -29871, 1642, 73859, 3374, -58957, -144, 12664, 257]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp23 : Fact (Nat.Prime 23) := fact_iff.2 (by norm_num)
instance hp73 : Fact (Nat.Prime 73) := fact_iff.2 (by norm_num)
instance hp983 : Fact (Nat.Prime 983) := fact_iff.2 (by norm_num)
instance hp47407 : Fact (Nat.Prime 47407) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 2
  a' := [1, 0, 1, 0, 0, 2]
  b' := [1, 1, 2, 1, 1, 1, 1]
  k := [2, 0, 0, 2, 1]
  f := [1, 1, -2, 3, 13, 2, -9, 2, 5, 1]
  g := [2, 2, 1, 1, 0, 2, 1, 1]
  h := [1, 1, 2, 1]
  a := [2, 1, 0, 1, 1, 1, 2]
  b := [1, 2, 2, 0, 2, 1, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD23 : CertificateDedekindCriterionLists l 23 where
  n := 2
  a' := [13, 13, 7, 1, 15, 6, 2, 11]
  b' := [15, 21, 3, 2, 16, 7, 8, 13, 9]
  k := [5, 6, 10, 11, 5, 2, 17, 6, 1]
  f := [7, 9, 19, 1, 18, 20, 17, 20, 4, 1]
  g := [8, 10, 22, 0, 19, 22, 20, 22, 3, 1]
  h := [20, 1]
  a := [10, 11, 5, 5, 20, 8, 15, 7, 6]
  b := [0, 5, 5, 3, 7, 3, 8, 10, 17]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD73 : CertificateDedekindCriterionLists l 73 where
  n := 2
  a' := [60, 1, 54, 9, 15, 35, 39, 65]
  b' := [23, 63, 29, 43, 46, 47, 3, 38, 9]
  k := [57, 71, 42, 45, 30, 46, 13, 36, 1]
  f := [52, 16, 34, 27, 13, 4, 23, 17, 14, 1]
  g := [69, 20, 45, 35, 16, 5, 31, 22, 18, 1]
  h := [55, 1]
  a := [34, 21, 67, 4, 34, 48, 68, 14, 3]
  b := [22, 8, 35, 54, 21, 36, 6, 71, 70]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD983 : CertificateDedekindCriterionLists l 983 where
  n := 2
  a' := [9, 466, 345, 190, 922, 777, 479, 191]
  b' := [345, 670, 807, 169, 686, 617, 359, 59, 88]
  k := [611, 350, 600, 583, 450, 307, 537, 157, 1]
  f := [292, 278, 183, 229, 272, 183, 384, 211, 240, 1]
  g := [695, 660, 434, 544, 646, 434, 913, 500, 570, 1]
  h := [413, 1]
  a := [48, 741, 693, 573, 79, 601, 671, 201, 687]
  b := [291, 973, 881, 261, 165, 138, 255, 419, 296]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD47407 : CertificateDedekindCriterionLists l 47407 where
  n := 2
  a' := [19339, 42625, 29469, 30821, 31523, 25244, 2886, 28433]
  b' := [18961, 11086, 31929, 13969, 15259, 23867, 43416, 43031, 23178]
  k := [23895, 3762, 37613, 26091, 6657, 42069, 6674, 12453, 1]
  f := [1715, 6953, 7632, 8143, 12425, 4206, 5508, 818, 11034, 1]
  g := [4652, 18860, 20701, 22087, 33702, 11407, 14940, 2218, 29930, 1]
  h := [17477, 1]
  a := [31223, 2466, 14143, 38543, 45186, 40048, 17861, 18503, 19456]
  b := [33899, 21730, 29703, 16714, 32701, 8467, 44425, 28195, 27951]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 5
  p := ![3, 23, 73, 983, 47407]
  exp := ![1, 1, 1, 1, 1]
  pdgood := [3, 23, 73, 983, 47407]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp23.out
    exact hp73.out
    exact hp983.out
    exact hp47407.out
  a := [-985624574973, -18566829067662, 28870077731848, 68771235196072, -87940161445980, -34739731508110, 46284275915980, 4718090564320, -6275199027500]
  b := [-750894929976, 1942063686687, 7503685630369, -11107035037412, -12440317169449, 15791799677894, 4417591263675, -5883467397098, -471809056432, 627519902750]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 23 T_ofList CD23
    exact satisfiesDedekindCriterion_of_certificate_lists T l 73 T_ofList CD73
    exact satisfiesDedekindCriterion_of_certificate_lists T l 983 T_ofList CD983
    exact satisfiesDedekindCriterion_of_certificate_lists T l 47407 T_ofList CD47407

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

end VoightMaximalOrderD10R107

namespace VoightMaximalOrderD10R108

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2123384396013, [-1, -5, 9, 27, -17, -39, 14, 19, -6, -3, 1], 1⟩
local notation "l" => [-1, -5, 9, 27, -17, -39, 14, 19, -6, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -9, -27, 17, 39, -14, -19, 6, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -9, -27, 17, 39, -14, -19, 6, 3], ![3, 16, -22, -90, 24, 134, -3, -71, -1, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -9, -27, 17, 39, -14, -19, 6, 3], ![3, 16, -22, -90, 24, 134, -3, -71, -1, 15], ![15, 78, -119, -427, 165, 609, -76, -288, 19, 44]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -9, -27, 17, 39, -14, -19, 6, 3], ![3, 16, -22, -90, 24, 134, -3, -71, -1, 15], ![15, 78, -119, -427, 165, 609, -76, -288, 19, 44], ![44, 235, -318, -1307, 321, 1881, -7, -912, -24, 151]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -9, -27, 17, 39, -14, -19, 6, 3], ![3, 16, -22, -90, 24, 134, -3, -71, -1, 15], ![15, 78, -119, -427, 165, 609, -76, -288, 19, 44], ![44, 235, -318, -1307, 321, 1881, -7, -912, -24, 151], ![151, 799, -1124, -4395, 1260, 6210, -233, -2876, -6, 429]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -9, -27, 17, 39, -14, -19, 6, 3], ![3, 16, -22, -90, 24, 134, -3, -71, -1, 15], ![15, 78, -119, -427, 165, 609, -76, -288, 19, 44], ![44, 235, -318, -1307, 321, 1881, -7, -912, -24, 151], ![151, 799, -1124, -4395, 1260, 6210, -233, -2876, -6, 429], ![429, 2296, -3062, -12707, 2898, 17991, 204, -8384, -302, 1281]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -9, -27, 17, 39, -14, -19, 6, 3], ![3, 16, -22, -90, 24, 134, -3, -71, -1, 15], ![15, 78, -119, -427, 165, 609, -76, -288, 19, 44], ![44, 235, -318, -1307, 321, 1881, -7, -912, -24, 151], ![151, 799, -1124, -4395, 1260, 6210, -233, -2876, -6, 429], ![429, 2296, -3062, -12707, 2898, 17991, 204, -8384, -302, 1281], ![1281, 6834, -9233, -37649, 9070, 52857, 57, -24135, -698, 3541]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -9, -27, 17, 39, -14, -19, 6, 3], ![3, 16, -22, -90, 24, 134, -3, -71, -1, 15], ![15, 78, -119, -427, 165, 609, -76, -288, 19, 44], ![44, 235, -318, -1307, 321, 1881, -7, -912, -24, 151], ![151, 799, -1124, -4395, 1260, 6210, -233, -2876, -6, 429], ![429, 2296, -3062, -12707, 2898, 17991, 204, -8384, -302, 1281], ![1281, 6834, -9233, -37649, 9070, 52857, 57, -24135, -698, 3541], ![3541, 18986, -25035, -104840, 22548, 147169, 3283, -67222, -2889, 9925]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -9, -27, 17, 39, -14, -19, 6, 3], ![3, 16, -22, -90, 24, 134, -3, -71, -1, 15], ![15, 78, -119, -427, 165, 609, -76, -288, 19, 44], ![44, 235, -318, -1307, 321, 1881, -7, -912, -24, 151], ![151, 799, -1124, -4395, 1260, 6210, -233, -2876, -6, 429], ![429, 2296, -3062, -12707, 2898, 17991, 204, -8384, -302, 1281], ![1281, 6834, -9233, -37649, 9070, 52857, 57, -24135, -698, 3541], ![3541, 18986, -25035, -104840, 22548, 147169, 3283, -67222, -2889, 9925], ![9925, 53166, -70339, -293010, 63885, 409623, 8219, -185292, -7672, 26886]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1], [-151, -44, -15, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1], [-151, -44, -15, -3, -1], [-429, -151, -44, -15, -3, -1]], ![[], [], [], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1], [-151, -44, -15, -3, -1], [-429, -151, -44, -15, -3, -1], [-1281, -429, -151, -44, -15, -3, -1]], ![[], [], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1], [-151, -44, -15, -3, -1], [-429, -151, -44, -15, -3, -1], [-1281, -429, -151, -44, -15, -3, -1], [-3541, -1281, -429, -151, -44, -15, -3, -1]], ![[], [-1], [-3, -1], [-15, -3, -1], [-44, -15, -3, -1], [-151, -44, -15, -3, -1], [-429, -151, -44, -15, -3, -1], [-1281, -429, -151, -44, -15, -3, -1], [-3541, -1281, -429, -151, -44, -15, -3, -1], [-9925, -3541, -1281, -429, -151, -44, -15, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -9, -27, 17, 39, -14, -19, 6, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -9, -27, 17, 39, -14, -19, 6, 3], [3, 16, -22, -90, 24, 134, -3, -71, -1, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -9, -27, 17, 39, -14, -19, 6, 3], [3, 16, -22, -90, 24, 134, -3, -71, -1, 15], [15, 78, -119, -427, 165, 609, -76, -288, 19, 44]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -9, -27, 17, 39, -14, -19, 6, 3], [3, 16, -22, -90, 24, 134, -3, -71, -1, 15], [15, 78, -119, -427, 165, 609, -76, -288, 19, 44], [44, 235, -318, -1307, 321, 1881, -7, -912, -24, 151]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -9, -27, 17, 39, -14, -19, 6, 3], [3, 16, -22, -90, 24, 134, -3, -71, -1, 15], [15, 78, -119, -427, 165, 609, -76, -288, 19, 44], [44, 235, -318, -1307, 321, 1881, -7, -912, -24, 151], [151, 799, -1124, -4395, 1260, 6210, -233, -2876, -6, 429]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -9, -27, 17, 39, -14, -19, 6, 3], [3, 16, -22, -90, 24, 134, -3, -71, -1, 15], [15, 78, -119, -427, 165, 609, -76, -288, 19, 44], [44, 235, -318, -1307, 321, 1881, -7, -912, -24, 151], [151, 799, -1124, -4395, 1260, 6210, -233, -2876, -6, 429], [429, 2296, -3062, -12707, 2898, 17991, 204, -8384, -302, 1281]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -9, -27, 17, 39, -14, -19, 6, 3], [3, 16, -22, -90, 24, 134, -3, -71, -1, 15], [15, 78, -119, -427, 165, 609, -76, -288, 19, 44], [44, 235, -318, -1307, 321, 1881, -7, -912, -24, 151], [151, 799, -1124, -4395, 1260, 6210, -233, -2876, -6, 429], [429, 2296, -3062, -12707, 2898, 17991, 204, -8384, -302, 1281], [1281, 6834, -9233, -37649, 9070, 52857, 57, -24135, -698, 3541]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -9, -27, 17, 39, -14, -19, 6, 3], [3, 16, -22, -90, 24, 134, -3, -71, -1, 15], [15, 78, -119, -427, 165, 609, -76, -288, 19, 44], [44, 235, -318, -1307, 321, 1881, -7, -912, -24, 151], [151, 799, -1124, -4395, 1260, 6210, -233, -2876, -6, 429], [429, 2296, -3062, -12707, 2898, 17991, 204, -8384, -302, 1281], [1281, 6834, -9233, -37649, 9070, 52857, 57, -24135, -698, 3541], [3541, 18986, -25035, -104840, 22548, 147169, 3283, -67222, -2889, 9925]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -9, -27, 17, 39, -14, -19, 6, 3], [3, 16, -22, -90, 24, 134, -3, -71, -1, 15], [15, 78, -119, -427, 165, 609, -76, -288, 19, 44], [44, 235, -318, -1307, 321, 1881, -7, -912, -24, 151], [151, 799, -1124, -4395, 1260, 6210, -233, -2876, -6, 429], [429, 2296, -3062, -12707, 2898, 17991, 204, -8384, -302, 1281], [1281, 6834, -9233, -37649, 9070, 52857, 57, -24135, -698, 3541], [3541, 18986, -25035, -104840, 22548, 147169, 3283, -67222, -2889, 9925], [9925, 53166, -70339, -293010, 63885, 409623, 8219, -185292, -7672, 26886]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp317 : Fact (Nat.Prime 317) := fact_iff.2 (by norm_num)
instance hp9188441 : Fact (Nat.Prime 9188441) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 3
  a' := [0, 0, 2]
  b' := [1, 2, 0, 0, 0, 1]
  k := [1, 1, 1, 0, 1, 2, 0, 0, 1]
  f := [1, 2, -1, -8, 8, 14, -3, -6, 3, 1]
  g := [2, 1, 2, 1, 1, 0, 1]
  h := [1, 0, 2, 0, 1]
  a := [1, 1, 2]
  b := [0, 0, 0, 1, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD317 : CertificateDedekindCriterionLists l 317 where
  n := 2
  a' := [189, 16, 139, 304, 240, 162, 211, 89]
  b' := [99, 203, 269, 192, 159, 280, 276, 35, 131]
  k := [121, 70, 180, 163, 253, 240, 9, 178, 1]
  f := [65, 28, 57, 37, 54, 20, 47, 15, 53, 1]
  g := [303, 126, 264, 169, 249, 89, 218, 67, 246, 1]
  h := [68, 1]
  a := [61, 2, 233, 124, 82, 92, 0, 276, 99]
  b := [102, 53, 157, 213, 47, 64, 242, 128, 218]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD9188441 : CertificateDedekindCriterionLists l 9188441 where
  n := 2
  a' := [6402175, 537015, 8104974, 3023529, 6916327, 7510115, 2052486, 7595435]
  b' := [8931094, 5625168, 1576374, 2424208, 1011684, 8450512, 8318968, 4435470, 6302628]
  k := [2152294, 8599809, 1720160, 696329, 8487454, 5661732, 1669364, 6558300, 1]
  f := [1109575, 1294628, 1121468, 339458, 449895, 1202839, 661054, 1144569, 1126854, 1]
  g := [7752646, 9045613, 7835736, 2371801, 3143433, 8404283, 4618805, 7997147, 7873369, 1]
  h := [1315069, 1]
  a := [264181, 7088807, 2461590, 7493686, 1971227, 2973769, 5885536, 6205462, 1987157]
  b := [2052066, 7513023, 6789305, 1184457, 2779826, 4253070, 5639812, 1838225, 7201284]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![3, 317, 9188441]
  exp := ![1, 1, 1]
  pdgood := [3, 317, 9188441]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp317.out
    exact hp9188441.out
  a := [21510679609, -147398388590, -187615403052, 696272821702, 61136654309, -594176226376, 101352417378, 137011920520, -40859993800]
  b := [-6049777400, -13810200531, 75917576705, 31056409314, -149867625141, -689388615, 85229229907, -14237742876, -14926991866, 4085999380]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 317 T_ofList CD317
    exact satisfiesDedekindCriterion_of_certificate_lists T l 9188441 T_ofList CD9188441

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

end VoightMaximalOrderD10R108

namespace VoightMaximalOrderD10R110

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2170033278125, [1, -6, 2, 28, -18, -41, 18, 20, -7, -3, 1], 1⟩
local notation "l" => [1, -6, 2, 28, -18, -41, 18, 20, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -2, -28, 18, 41, -18, -20, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -2, -28, 18, 41, -18, -20, 7, 3], ![-3, 17, 0, -86, 26, 141, -13, -78, 1, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -2, -28, 18, 41, -18, -20, 7, 3], ![-3, 17, 0, -86, 26, 141, -13, -78, 1, 16], ![-16, 93, -15, -448, 202, 682, -147, -333, 34, 49]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -2, -28, 18, 41, -18, -20, 7, 3], ![-3, 17, 0, -86, 26, 141, -13, -78, 1, 16], ![-16, 93, -15, -448, 202, 682, -147, -333, 34, 49], ![-49, 278, -5, -1387, 434, 2211, -200, -1127, 10, 181]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -2, -28, 18, 41, -18, -20, 7, 3], ![-3, 17, 0, -86, 26, 141, -13, -78, 1, 16], ![-16, 93, -15, -448, 202, 682, -147, -333, 34, 49], ![-49, 278, -5, -1387, 434, 2211, -200, -1127, 10, 181], ![-181, 1037, -84, -5073, 1871, 7855, -1047, -3820, 140, 553]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -2, -28, 18, 41, -18, -20, 7, 3], ![-3, 17, 0, -86, 26, 141, -13, -78, 1, 16], ![-16, 93, -15, -448, 202, 682, -147, -333, 34, 49], ![-49, 278, -5, -1387, 434, 2211, -200, -1127, 10, 181], ![-181, 1037, -84, -5073, 1871, 7855, -1047, -3820, 140, 553], ![-553, 3137, -69, -15568, 4881, 24544, -2099, -12107, 51, 1799]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -2, -28, 18, 41, -18, -20, 7, 3], ![-3, 17, 0, -86, 26, 141, -13, -78, 1, 16], ![-16, 93, -15, -448, 202, 682, -147, -333, 34, 49], ![-49, 278, -5, -1387, 434, 2211, -200, -1127, 10, 181], ![-181, 1037, -84, -5073, 1871, 7855, -1047, -3820, 140, 553], ![-553, 3137, -69, -15568, 4881, 24544, -2099, -12107, 51, 1799], ![-1799, 10241, -461, -50441, 16814, 78640, -7838, -38079, 486, 5448]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -2, -28, 18, 41, -18, -20, 7, 3], ![-3, 17, 0, -86, 26, 141, -13, -78, 1, 16], ![-16, 93, -15, -448, 202, 682, -147, -333, 34, 49], ![-49, 278, -5, -1387, 434, 2211, -200, -1127, 10, 181], ![-181, 1037, -84, -5073, 1871, 7855, -1047, -3820, 140, 553], ![-553, 3137, -69, -15568, 4881, 24544, -2099, -12107, 51, 1799], ![-1799, 10241, -461, -50441, 16814, 78640, -7838, -38079, 486, 5448], ![-5448, 30889, -655, -153005, 47623, 240182, -19424, -116798, 57, 16830]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -2, -28, 18, 41, -18, -20, 7, 3], ![-3, 17, 0, -86, 26, 141, -13, -78, 1, 16], ![-16, 93, -15, -448, 202, 682, -147, -333, 34, 49], ![-49, 278, -5, -1387, 434, 2211, -200, -1127, 10, 181], ![-181, 1037, -84, -5073, 1871, 7855, -1047, -3820, 140, 553], ![-553, 3137, -69, -15568, 4881, 24544, -2099, -12107, 51, 1799], ![-1799, 10241, -461, -50441, 16814, 78640, -7838, -38079, 486, 5448], ![-5448, 30889, -655, -153005, 47623, 240182, -19424, -116798, 57, 16830], ![-16830, 95532, -2771, -471895, 149935, 737653, -62758, -356024, 1012, 50547]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-49, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-49, -16, -3, -1], [-181, -49, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-49, -16, -3, -1], [-181, -49, -16, -3, -1], [-553, -181, -49, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-49, -16, -3, -1], [-181, -49, -16, -3, -1], [-553, -181, -49, -16, -3, -1], [-1799, -553, -181, -49, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-49, -16, -3, -1], [-181, -49, -16, -3, -1], [-553, -181, -49, -16, -3, -1], [-1799, -553, -181, -49, -16, -3, -1], [-5448, -1799, -553, -181, -49, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-49, -16, -3, -1], [-181, -49, -16, -3, -1], [-553, -181, -49, -16, -3, -1], [-1799, -553, -181, -49, -16, -3, -1], [-5448, -1799, -553, -181, -49, -16, -3, -1], [-16830, -5448, -1799, -553, -181, -49, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -2, -28, 18, 41, -18, -20, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -2, -28, 18, 41, -18, -20, 7, 3], [-3, 17, 0, -86, 26, 141, -13, -78, 1, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -2, -28, 18, 41, -18, -20, 7, 3], [-3, 17, 0, -86, 26, 141, -13, -78, 1, 16], [-16, 93, -15, -448, 202, 682, -147, -333, 34, 49]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -2, -28, 18, 41, -18, -20, 7, 3], [-3, 17, 0, -86, 26, 141, -13, -78, 1, 16], [-16, 93, -15, -448, 202, 682, -147, -333, 34, 49], [-49, 278, -5, -1387, 434, 2211, -200, -1127, 10, 181]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -2, -28, 18, 41, -18, -20, 7, 3], [-3, 17, 0, -86, 26, 141, -13, -78, 1, 16], [-16, 93, -15, -448, 202, 682, -147, -333, 34, 49], [-49, 278, -5, -1387, 434, 2211, -200, -1127, 10, 181], [-181, 1037, -84, -5073, 1871, 7855, -1047, -3820, 140, 553]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -2, -28, 18, 41, -18, -20, 7, 3], [-3, 17, 0, -86, 26, 141, -13, -78, 1, 16], [-16, 93, -15, -448, 202, 682, -147, -333, 34, 49], [-49, 278, -5, -1387, 434, 2211, -200, -1127, 10, 181], [-181, 1037, -84, -5073, 1871, 7855, -1047, -3820, 140, 553], [-553, 3137, -69, -15568, 4881, 24544, -2099, -12107, 51, 1799]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -2, -28, 18, 41, -18, -20, 7, 3], [-3, 17, 0, -86, 26, 141, -13, -78, 1, 16], [-16, 93, -15, -448, 202, 682, -147, -333, 34, 49], [-49, 278, -5, -1387, 434, 2211, -200, -1127, 10, 181], [-181, 1037, -84, -5073, 1871, 7855, -1047, -3820, 140, 553], [-553, 3137, -69, -15568, 4881, 24544, -2099, -12107, 51, 1799], [-1799, 10241, -461, -50441, 16814, 78640, -7838, -38079, 486, 5448]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -2, -28, 18, 41, -18, -20, 7, 3], [-3, 17, 0, -86, 26, 141, -13, -78, 1, 16], [-16, 93, -15, -448, 202, 682, -147, -333, 34, 49], [-49, 278, -5, -1387, 434, 2211, -200, -1127, 10, 181], [-181, 1037, -84, -5073, 1871, 7855, -1047, -3820, 140, 553], [-553, 3137, -69, -15568, 4881, 24544, -2099, -12107, 51, 1799], [-1799, 10241, -461, -50441, 16814, 78640, -7838, -38079, 486, 5448], [-5448, 30889, -655, -153005, 47623, 240182, -19424, -116798, 57, 16830]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -2, -28, 18, 41, -18, -20, 7, 3], [-3, 17, 0, -86, 26, 141, -13, -78, 1, 16], [-16, 93, -15, -448, 202, 682, -147, -333, 34, 49], [-49, 278, -5, -1387, 434, 2211, -200, -1127, 10, 181], [-181, 1037, -84, -5073, 1871, 7855, -1047, -3820, 140, 553], [-553, 3137, -69, -15568, 4881, 24544, -2099, -12107, 51, 1799], [-1799, 10241, -461, -50441, 16814, 78640, -7838, -38079, 486, 5448], [-5448, 30889, -655, -153005, 47623, 240182, -19424, -116798, 57, 16830], [-16830, 95532, -2771, -471895, 149935, 737653, -62758, -356024, 1012, 50547]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp694410649 : Fact (Nat.Prime 694410649) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 4, 1]
  b' := [2, 3, 4, 3, 1]
  k := [1]
  f := [0, 2, 2, -2, 8, 11, -1, -2, 2, 1]
  g := [1, 2, 4, 1, 1, 1]
  h := [1, 2, 4, 1, 1, 1]
  a := [2, 3, 3, 4, 4]
  b := [1, 4, 3, 4, 1, 3, 4, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD694410649 : CertificateDedekindCriterionLists l 694410649 where
  n := 2
  a' := [396520046, 36614725, 676138132, 497814450, 60808660, 384816115, 379558647, 593064547]
  b' := [371249915, 122582502, 634139560, 571254518, 58865524, 583423983, 344204968, 487452303, 11260678]
  k := [343643, 482263329, 688892766, 255062674, 419993861, 628187208, 556828009, 302422529, 1]
  f := [43635695, 281116400, 171053439, 153209177, 375357346, 49478996, 508932454, 207974183, 118284282, 1]
  g := [55782632, 359371214, 218669853, 195858256, 479846160, 63252541, 650604781, 265868282, 151211263, 1]
  h := [543199383, 1]
  a := [196465465, 278044536, 339912248, 143055616, 364040213, 410405705, 232862528, 385665757, 567695556]
  b := [540981307, 511809618, 58396250, 691612338, 611380961, 649970830, 227604288, 401317689, 126715093]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 694410649]
  exp := ![1, 1]
  pdgood := [5, 694410649]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp694410649.out
  a := [-4037246397781, -5227946189408, 46244872206196, 42006724382676, -55746720558809, -36346078660938, 23121679382555, 7531403395240, -3441359796700]
  b := [-673453075171, 2716953316099, 3972635249519, -11059676568080, -9518247374606, 8968387974641, 5425906439402, -2846766351469, -856381133425, 344135979670]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 694410649 T_ofList CD694410649

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

end VoightMaximalOrderD10R110

end TraceEuclidean
