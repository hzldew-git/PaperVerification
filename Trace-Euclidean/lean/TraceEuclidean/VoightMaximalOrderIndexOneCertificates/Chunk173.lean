import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk169
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

namespace VoightMaximalOrderD10R60

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1569279344237, [1, -1, -16, 26, 27, -54, 2, 24, -6, -3, 1], 1⟩
local notation "l" => [1, -1, -16, 26, 27, -54, 2, 24, -6, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 16, -26, -27, 54, -2, -24, 6, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 16, -26, -27, 54, -2, -24, 6, 3], ![-3, 2, 49, -62, -107, 135, 48, -74, -6, 15]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 16, -26, -27, 54, -2, -24, 6, 3], ![-3, 2, 49, -62, -107, 135, 48, -74, -6, 15], ![-15, 12, 242, -341, -467, 703, 105, -312, 16, 39]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 16, -26, -27, 54, -2, -24, 6, 3], ![-3, 2, 49, -62, -107, 135, 48, -74, -6, 15], ![-15, 12, 242, -341, -467, 703, 105, -312, 16, 39], ![-39, 24, 636, -772, -1394, 1639, 625, -831, -78, 133]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 16, -26, -27, 54, -2, -24, 6, 3], ![-3, 2, 49, -62, -107, 135, 48, -74, -6, 15], ![-15, 12, 242, -341, -467, 703, 105, -312, 16, 39], ![-39, 24, 636, -772, -1394, 1639, 625, -831, -78, 133], ![-133, 94, 2152, -2822, -4363, 5788, 1373, -2567, -33, 321]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 16, -26, -27, 54, -2, -24, 6, 3], ![-3, 2, 49, -62, -107, 135, 48, -74, -6, 15], ![-15, 12, 242, -341, -467, 703, 105, -312, 16, 39], ![-39, 24, 636, -772, -1394, 1639, 625, -831, -78, 133], ![-133, 94, 2152, -2822, -4363, 5788, 1373, -2567, -33, 321], ![-321, 188, 5230, -6194, -11489, 12971, 5146, -6331, -641, 930]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 16, -26, -27, 54, -2, -24, 6, 3], ![-3, 2, 49, -62, -107, 135, 48, -74, -6, 15], ![-15, 12, 242, -341, -467, 703, 105, -312, 16, 39], ![-39, 24, 636, -772, -1394, 1639, 625, -831, -78, 133], ![-133, 94, 2152, -2822, -4363, 5788, 1373, -2567, -33, 321], ![-321, 188, 5230, -6194, -11489, 12971, 5146, -6331, -641, 930], ![-930, 609, 15068, -18950, -31304, 38731, 11111, -17174, -751, 2149]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 16, -26, -27, 54, -2, -24, 6, 3], ![-3, 2, 49, -62, -107, 135, 48, -74, -6, 15], ![-15, 12, 242, -341, -467, 703, 105, -312, 16, 39], ![-39, 24, 636, -772, -1394, 1639, 625, -831, -78, 133], ![-133, 94, 2152, -2822, -4363, 5788, 1373, -2567, -33, 321], ![-321, 188, 5230, -6194, -11489, 12971, 5146, -6331, -641, 930], ![-930, 609, 15068, -18950, -31304, 38731, 11111, -17174, -751, 2149], ![-2149, 1219, 34993, -40806, -76973, 84742, 34433, -40465, -4280, 5696]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 16, -26, -27, 54, -2, -24, 6, 3], ![-3, 2, 49, -62, -107, 135, 48, -74, -6, 15], ![-15, 12, 242, -341, -467, 703, 105, -312, 16, 39], ![-39, 24, 636, -772, -1394, 1639, 625, -831, -78, 133], ![-133, 94, 2152, -2822, -4363, 5788, 1373, -2567, -33, 321], ![-321, 188, 5230, -6194, -11489, 12971, 5146, -6331, -641, 930], ![-930, 609, 15068, -18950, -31304, 38731, 11111, -17174, -751, 2149], ![-2149, 1219, 34993, -40806, -76973, 84742, 34433, -40465, -4280, 5696], ![-5696, 3547, 92355, -113103, -194598, 230611, 73350, -102271, -6289, 12808]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-39, -15, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-39, -15, -3, -1], [-133, -39, -15, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-15, -3, -1], [-39, -15, -3, -1], [-133, -39, -15, -3, -1], [-321, -133, -39, -15, -3, -1]], ![[], [], [], [-1], [-3, -1], [-15, -3, -1], [-39, -15, -3, -1], [-133, -39, -15, -3, -1], [-321, -133, -39, -15, -3, -1], [-930, -321, -133, -39, -15, -3, -1]], ![[], [], [-1], [-3, -1], [-15, -3, -1], [-39, -15, -3, -1], [-133, -39, -15, -3, -1], [-321, -133, -39, -15, -3, -1], [-930, -321, -133, -39, -15, -3, -1], [-2149, -930, -321, -133, -39, -15, -3, -1]], ![[], [-1], [-3, -1], [-15, -3, -1], [-39, -15, -3, -1], [-133, -39, -15, -3, -1], [-321, -133, -39, -15, -3, -1], [-930, -321, -133, -39, -15, -3, -1], [-2149, -930, -321, -133, -39, -15, -3, -1], [-5696, -2149, -930, -321, -133, -39, -15, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 16, -26, -27, 54, -2, -24, 6, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 16, -26, -27, 54, -2, -24, 6, 3], [-3, 2, 49, -62, -107, 135, 48, -74, -6, 15]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 16, -26, -27, 54, -2, -24, 6, 3], [-3, 2, 49, -62, -107, 135, 48, -74, -6, 15], [-15, 12, 242, -341, -467, 703, 105, -312, 16, 39]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 16, -26, -27, 54, -2, -24, 6, 3], [-3, 2, 49, -62, -107, 135, 48, -74, -6, 15], [-15, 12, 242, -341, -467, 703, 105, -312, 16, 39], [-39, 24, 636, -772, -1394, 1639, 625, -831, -78, 133]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 16, -26, -27, 54, -2, -24, 6, 3], [-3, 2, 49, -62, -107, 135, 48, -74, -6, 15], [-15, 12, 242, -341, -467, 703, 105, -312, 16, 39], [-39, 24, 636, -772, -1394, 1639, 625, -831, -78, 133], [-133, 94, 2152, -2822, -4363, 5788, 1373, -2567, -33, 321]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 16, -26, -27, 54, -2, -24, 6, 3], [-3, 2, 49, -62, -107, 135, 48, -74, -6, 15], [-15, 12, 242, -341, -467, 703, 105, -312, 16, 39], [-39, 24, 636, -772, -1394, 1639, 625, -831, -78, 133], [-133, 94, 2152, -2822, -4363, 5788, 1373, -2567, -33, 321], [-321, 188, 5230, -6194, -11489, 12971, 5146, -6331, -641, 930]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 16, -26, -27, 54, -2, -24, 6, 3], [-3, 2, 49, -62, -107, 135, 48, -74, -6, 15], [-15, 12, 242, -341, -467, 703, 105, -312, 16, 39], [-39, 24, 636, -772, -1394, 1639, 625, -831, -78, 133], [-133, 94, 2152, -2822, -4363, 5788, 1373, -2567, -33, 321], [-321, 188, 5230, -6194, -11489, 12971, 5146, -6331, -641, 930], [-930, 609, 15068, -18950, -31304, 38731, 11111, -17174, -751, 2149]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 16, -26, -27, 54, -2, -24, 6, 3], [-3, 2, 49, -62, -107, 135, 48, -74, -6, 15], [-15, 12, 242, -341, -467, 703, 105, -312, 16, 39], [-39, 24, 636, -772, -1394, 1639, 625, -831, -78, 133], [-133, 94, 2152, -2822, -4363, 5788, 1373, -2567, -33, 321], [-321, 188, 5230, -6194, -11489, 12971, 5146, -6331, -641, 930], [-930, 609, 15068, -18950, -31304, 38731, 11111, -17174, -751, 2149], [-2149, 1219, 34993, -40806, -76973, 84742, 34433, -40465, -4280, 5696]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 16, -26, -27, 54, -2, -24, 6, 3], [-3, 2, 49, -62, -107, 135, 48, -74, -6, 15], [-15, 12, 242, -341, -467, 703, 105, -312, 16, 39], [-39, 24, 636, -772, -1394, 1639, 625, -831, -78, 133], [-133, 94, 2152, -2822, -4363, 5788, 1373, -2567, -33, 321], [-321, 188, 5230, -6194, -11489, 12971, 5146, -6331, -641, 930], [-930, 609, 15068, -18950, -31304, 38731, 11111, -17174, -751, 2149], [-2149, 1219, 34993, -40806, -76973, 84742, 34433, -40465, -4280, 5696], [-5696, 3547, 92355, -113103, -194598, 230611, 73350, -102271, -6289, 12808]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp17 : Fact (Nat.Prime 17) := fact_iff.2 (by norm_num)
instance hp41 : Fact (Nat.Prime 41) := fact_iff.2 (by norm_num)
instance hp523 : Fact (Nat.Prime 523) := fact_iff.2 (by norm_num)
instance hp23021 : Fact (Nat.Prime 23021) := fact_iff.2 (by norm_num)

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [2, 8, 7, 7, 8, 6, 5, 6]
  b' := [5, 1, 3, 3, 6, 1, 1, 2, 3]
  k := [9, 3, 10, 4, 8, 2, 0, 0, 1]
  f := [1, 4, 6, 0, -1, 7, 1, -2, 2, 1]
  g := [3, 10, 10, 4, 3, 5, 2, 0, 4, 1]
  h := [4, 1]
  a := [0, 5, 7, 7, 5, 4, 2, 4, 8]
  b := [4, 7, 2, 9, 2, 0, 2, 1, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD17 : CertificateDedekindCriterionLists l 17 where
  n := 3
  a' := [7, 14, 5, 4, 2, 16]
  b' := [2, 0, 13, 2, 10, 1, 15]
  k := [1, 9, 2, 2, 4, 12, 7, 1, 7, 1, 12, 5, 3, 5, 1]
  f := [0, 1, 3, 0, -1, 4, 1, 0, 2, 1]
  g := [1, 14, 6, 0, 4, 6, 3, 12, 1]
  h := [1, 2, 1]
  a := [13, 8, 5, 1, 12, 0, 12]
  b := [1, 7, 2, 3, 7, 12, 1, 5]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD41 : CertificateDedekindCriterionLists l 41 where
  n := 2
  a' := [40, 7, 30, 10, 34, 11, 15, 22]
  b' := [17, 5, 31, 22, 17, 4, 33, 33, 34]
  k := [21, 8, 15, 18, 25, 20, 21, 31, 1]
  f := [7, 5, 24, 22, 2, 9, 19, 16, 9, 1]
  g := [12, 8, 40, 37, 3, 13, 32, 27, 14, 1]
  h := [24, 1]
  a := [38, 1, 31, 2, 37, 22, 35, 22]
  b := [36, 4, 22, 11, 7, 3, 34, 19]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD523 : CertificateDedekindCriterionLists l 523 where
  n := 2
  a' := [168, 405, 218, 191, 482, 336, 363, 51]
  b' := [376, 329, 485, 46, 268, 102, 305, 425, 343]
  k := [201, 457, 177, 462, 104, 103, 253, 340, 1]
  f := [53, 3, 30, 76, 71, 84, 67, 90, 75, 1]
  g := [308, 14, 174, 440, 408, 483, 384, 519, 430, 1]
  h := [90, 1]
  a := [209, 103, 422, 425, 115, 115, 131, 88, 86]
  b := [521, 269, 440, 339, 311, 221, 459, 108, 437]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD23021 : CertificateDedekindCriterionLists l 23021 where
  n := 2
  a' := [14046, 16886, 8357, 20844, 13707, 8382, 2694, 20571]
  b' := [17753, 2651, 13761, 9469, 10959, 6950, 21524, 4737, 5388]
  k := [2530, 1458, 4760, 11670, 6090, 17035, 2331, 9582, 1]
  f := [2055, 3925, 867, 5053, 4662, 2869, 6541, 2187, 4757, 1]
  g := [7042, 13449, 2969, 17315, 15973, 9829, 22413, 7491, 16300, 1]
  h := [6718, 1]
  a := [1595, 7865, 16319, 6817, 11765, 6264, 4756, 23009, 19999]
  b := [20836, 18011, 6770, 1616, 15514, 2331, 12942, 16902, 3022]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 5
  p := ![11, 17, 41, 523, 23021]
  exp := ![1, 1, 1, 1, 1]
  pdgood := [11, 17, 41, 523, 23021]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp11.out
    exact hp17.out
    exact hp41.out
    exact hp523.out
    exact hp23021.out
  a := [-314736507, -3127496666394, 32244677234, 10030507612450, -4091348058567, -6172434417856, 3011500694675, 992344776820, -508798050100]
  b := [-92625286168, -163172772511, 1161533526988, 129946422720, -2133684306498, 648224067089, 923992737835, -373648134233, -114498419185, 50879805010]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 17 T_ofList CD17
    exact satisfiesDedekindCriterion_of_certificate_lists T l 41 T_ofList CD41
    exact satisfiesDedekindCriterion_of_certificate_lists T l 523 T_ofList CD523
    exact satisfiesDedekindCriterion_of_certificate_lists T l 23021 T_ofList CD23021

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

end VoightMaximalOrderD10R60

namespace VoightMaximalOrderD10R66

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1646448878125, [-1, -5, 3, 30, -5, -51, 21, 19, -9, -2, 1], 1⟩
local notation "l" => [-1, -5, 3, 30, -5, -51, 21, 19, -9, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -30, 5, 51, -21, -19, 9, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -30, 5, 51, -21, -19, 9, 2], ![2, 11, -1, -63, -20, 107, 9, -59, -1, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -30, 5, 51, -21, -19, 9, 2], ![2, 11, -1, -63, -20, 107, 9, -59, -1, 13], ![13, 67, -28, -391, 2, 643, -166, -238, 58, 25]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -30, 5, 51, -21, -19, 9, 2], ![2, 11, -1, -63, -20, 107, 9, -59, -1, 13], ![13, 67, -28, -391, 2, 643, -166, -238, 58, 25], ![25, 138, -8, -778, -266, 1277, 118, -641, -13, 108]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -30, 5, 51, -21, -19, 9, 2], ![2, 11, -1, -63, -20, 107, 9, -59, -1, 13], ![13, 67, -28, -391, 2, 643, -166, -238, 58, 25], ![25, 138, -8, -778, -266, 1277, 118, -641, -13, 108], ![108, 565, -186, -3248, -238, 5242, -991, -1934, 331, 203]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -30, 5, 51, -21, -19, 9, 2], ![2, 11, -1, -63, -20, 107, 9, -59, -1, 13], ![13, 67, -28, -391, 2, 643, -166, -238, 58, 25], ![25, 138, -8, -778, -266, 1277, 118, -641, -13, 108], ![108, 565, -186, -3248, -238, 5242, -991, -1934, 331, 203], ![203, 1123, -44, -6276, -2233, 10115, 979, -4848, -107, 737]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -30, 5, 51, -21, -19, 9, 2], ![2, 11, -1, -63, -20, 107, 9, -59, -1, 13], ![13, 67, -28, -391, 2, 643, -166, -238, 58, 25], ![25, 138, -8, -778, -266, 1277, 118, -641, -13, 108], ![108, 565, -186, -3248, -238, 5242, -991, -1934, 331, 203], ![203, 1123, -44, -6276, -2233, 10115, 979, -4848, -107, 737], ![737, 3888, -1088, -22154, -2591, 35354, -5362, -13024, 1785, 1367]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -30, 5, 51, -21, -19, 9, 2], ![2, 11, -1, -63, -20, 107, 9, -59, -1, 13], ![13, 67, -28, -391, 2, 643, -166, -238, 58, 25], ![25, 138, -8, -778, -266, 1277, 118, -641, -13, 108], ![108, 565, -186, -3248, -238, 5242, -991, -1934, 331, 203], ![203, 1123, -44, -6276, -2233, 10115, 979, -4848, -107, 737], ![737, 3888, -1088, -22154, -2591, 35354, -5362, -13024, 1785, 1367], ![1367, 7572, -213, -42098, -15319, 67126, 6647, -31335, -721, 4519]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -3, -30, 5, 51, -21, -19, 9, 2], ![2, 11, -1, -63, -20, 107, 9, -59, -1, 13], ![13, 67, -28, -391, 2, 643, -166, -238, 58, 25], ![25, 138, -8, -778, -266, 1277, 118, -641, -13, 108], ![108, 565, -186, -3248, -238, 5242, -991, -1934, 331, 203], ![203, 1123, -44, -6276, -2233, 10115, 979, -4848, -107, 737], ![737, 3888, -1088, -22154, -2591, 35354, -5362, -13024, 1785, 1367], ![1367, 7572, -213, -42098, -15319, 67126, 6647, -31335, -721, 4519], ![4519, 23962, -5985, -135783, -19503, 215150, -27773, -79214, 9336, 8317]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-25, -13, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-25, -13, -2, -1], [-108, -25, -13, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-25, -13, -2, -1], [-108, -25, -13, -2, -1], [-203, -108, -25, -13, -2, -1]], ![[], [], [], [-1], [-2, -1], [-13, -2, -1], [-25, -13, -2, -1], [-108, -25, -13, -2, -1], [-203, -108, -25, -13, -2, -1], [-737, -203, -108, -25, -13, -2, -1]], ![[], [], [-1], [-2, -1], [-13, -2, -1], [-25, -13, -2, -1], [-108, -25, -13, -2, -1], [-203, -108, -25, -13, -2, -1], [-737, -203, -108, -25, -13, -2, -1], [-1367, -737, -203, -108, -25, -13, -2, -1]], ![[], [-1], [-2, -1], [-13, -2, -1], [-25, -13, -2, -1], [-108, -25, -13, -2, -1], [-203, -108, -25, -13, -2, -1], [-737, -203, -108, -25, -13, -2, -1], [-1367, -737, -203, -108, -25, -13, -2, -1], [-4519, -1367, -737, -203, -108, -25, -13, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -30, 5, 51, -21, -19, 9, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -30, 5, 51, -21, -19, 9, 2], [2, 11, -1, -63, -20, 107, 9, -59, -1, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -30, 5, 51, -21, -19, 9, 2], [2, 11, -1, -63, -20, 107, 9, -59, -1, 13], [13, 67, -28, -391, 2, 643, -166, -238, 58, 25]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -30, 5, 51, -21, -19, 9, 2], [2, 11, -1, -63, -20, 107, 9, -59, -1, 13], [13, 67, -28, -391, 2, 643, -166, -238, 58, 25], [25, 138, -8, -778, -266, 1277, 118, -641, -13, 108]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -30, 5, 51, -21, -19, 9, 2], [2, 11, -1, -63, -20, 107, 9, -59, -1, 13], [13, 67, -28, -391, 2, 643, -166, -238, 58, 25], [25, 138, -8, -778, -266, 1277, 118, -641, -13, 108], [108, 565, -186, -3248, -238, 5242, -991, -1934, 331, 203]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -30, 5, 51, -21, -19, 9, 2], [2, 11, -1, -63, -20, 107, 9, -59, -1, 13], [13, 67, -28, -391, 2, 643, -166, -238, 58, 25], [25, 138, -8, -778, -266, 1277, 118, -641, -13, 108], [108, 565, -186, -3248, -238, 5242, -991, -1934, 331, 203], [203, 1123, -44, -6276, -2233, 10115, 979, -4848, -107, 737]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -30, 5, 51, -21, -19, 9, 2], [2, 11, -1, -63, -20, 107, 9, -59, -1, 13], [13, 67, -28, -391, 2, 643, -166, -238, 58, 25], [25, 138, -8, -778, -266, 1277, 118, -641, -13, 108], [108, 565, -186, -3248, -238, 5242, -991, -1934, 331, 203], [203, 1123, -44, -6276, -2233, 10115, 979, -4848, -107, 737], [737, 3888, -1088, -22154, -2591, 35354, -5362, -13024, 1785, 1367]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -30, 5, 51, -21, -19, 9, 2], [2, 11, -1, -63, -20, 107, 9, -59, -1, 13], [13, 67, -28, -391, 2, 643, -166, -238, 58, 25], [25, 138, -8, -778, -266, 1277, 118, -641, -13, 108], [108, 565, -186, -3248, -238, 5242, -991, -1934, 331, 203], [203, 1123, -44, -6276, -2233, 10115, 979, -4848, -107, 737], [737, 3888, -1088, -22154, -2591, 35354, -5362, -13024, 1785, 1367], [1367, 7572, -213, -42098, -15319, 67126, 6647, -31335, -721, 4519]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -3, -30, 5, 51, -21, -19, 9, 2], [2, 11, -1, -63, -20, 107, 9, -59, -1, 13], [13, 67, -28, -391, 2, 643, -166, -238, 58, 25], [25, 138, -8, -778, -266, 1277, 118, -641, -13, 108], [108, 565, -186, -3248, -238, 5242, -991, -1934, 331, 203], [203, 1123, -44, -6276, -2233, 10115, 979, -4848, -107, 737], [737, 3888, -1088, -22154, -2591, 35354, -5362, -13024, 1785, 1367], [1367, 7572, -213, -42098, -15319, 67126, 6647, -31335, -721, 4519], [4519, 23962, -5985, -135783, -19503, 215150, -27773, -79214, 9336, 8317]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp526863641 : Fact (Nat.Prime 526863641) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 3, 3]
  b' := [1, 2, 2, 0, 2]
  k := [1]
  f := [1, 1, 1, -6, 5, 11, -1, -3, 5, 2]
  g := [2, 0, 2, 0, 4, 1]
  h := [2, 0, 2, 0, 4, 1]
  a := [3, 0, 1, 4, 2]
  b := [4, 1, 4, 3, 2, 4, 2, 3, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD526863641 : CertificateDedekindCriterionLists l 526863641 where
  n := 2
  a' := [247070745, 496727272, 313201863, 257264179, 518453813, 48535327, 523815813, 174996761]
  b' := [58625107, 262186311, 404503877, 525043795, 315691013, 92728993, 266400852, 356717476, 39096320]
  k := [134980495, 395240632, 55411443, 376010596, 491067306, 20498747, 133348206, 22419556, 1]
  f := [273829099, 205729180, 459614081, 423879231, 20529493, 367810319, 442232768, 36189489, 10971273, 1]
  g := [279781859, 210201518, 469605613, 433093924, 20975782, 375806133, 451846448, 36976210, 11209777, 1]
  h := [515653862, 1]
  a := [254166807, 78075373, 755230, 242201336, 351518062, 74213537, 430932509, 352441369, 294616364]
  b := [424461527, 194667038, 42992541, 414867914, 506586560, 77819293, 152201881, 78765199, 232247277]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 526863641]
  exp := ![1, 1]
  pdgood := [5, 526863641]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp526863641.out
  a := [44099513900, -189004317726, -269721695385, 949936179740, -255136595718, -535656901488, 228723144808, 74444365164, -35455743780]
  b := [-9346766421, -17514770060, 80148845493, 49228771397, -190369385822, 47882786934, 75539089589, -29041867834, -8153551392, 3545574378]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 526863641 T_ofList CD526863641

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

end VoightMaximalOrderD10R66

namespace VoightMaximalOrderD10R67

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1659927378125, [1, -10, 3, 45, -30, -48, 36, 13, -11, -1, 1], 1⟩
local notation "l" => [1, -10, 3, 45, -30, -48, 36, 13, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -3, -45, 30, 48, -36, -13, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -3, -45, 30, 48, -36, -13, 11, 1], ![-1, 9, 7, -48, -15, 78, 12, -49, -2, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -3, -45, 30, 48, -36, -13, 11, 1], ![-1, 9, 7, -48, -15, 78, 12, -49, -2, 12], ![-12, 119, -27, -533, 312, 561, -354, -144, 83, 10]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -3, -45, 30, 48, -36, -13, 11, 1], ![-1, 9, 7, -48, -15, 78, 12, -49, -2, 12], ![-12, 119, -27, -533, 312, 561, -354, -144, 83, 10], ![-10, 88, 89, -477, -233, 792, 201, -484, -34, 93]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -3, -45, 30, 48, -36, -13, 11, 1], ![-1, 9, 7, -48, -15, 78, 12, -49, -2, 12], ![-12, 119, -27, -533, 312, 561, -354, -144, 83, 10], ![-10, 88, 89, -477, -233, 792, 201, -484, -34, 93], ![-93, 920, -191, -4096, 2313, 4231, -2556, -1008, 539, 59]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -3, -45, 30, 48, -36, -13, 11, 1], ![-1, 9, 7, -48, -15, 78, 12, -49, -2, 12], ![-12, 119, -27, -533, 312, 561, -354, -144, 83, 10], ![-10, 88, 89, -477, -233, 792, 201, -484, -34, 93], ![-93, 920, -191, -4096, 2313, 4231, -2556, -1008, 539, 59], ![-59, 497, 743, -2846, -2326, 5145, 2107, -3323, -359, 598]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -3, -45, 30, 48, -36, -13, 11, 1], ![-1, 9, 7, -48, -15, 78, 12, -49, -2, 12], ![-12, 119, -27, -533, 312, 561, -354, -144, 83, 10], ![-10, 88, 89, -477, -233, 792, 201, -484, -34, 93], ![-93, 920, -191, -4096, 2313, 4231, -2556, -1008, 539, 59], ![-59, 497, 743, -2846, -2326, 5145, 2107, -3323, -359, 598], ![-598, 5921, -1297, -26167, 15094, 26378, -16383, -5667, 3255, 239]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -3, -45, 30, 48, -36, -13, 11, 1], ![-1, 9, 7, -48, -15, 78, 12, -49, -2, 12], ![-12, 119, -27, -533, 312, 561, -354, -144, 83, 10], ![-10, 88, 89, -477, -233, 792, 201, -484, -34, 93], ![-93, 920, -191, -4096, 2313, 4231, -2556, -1008, 539, 59], ![-59, 497, 743, -2846, -2326, 5145, 2107, -3323, -359, 598], ![-598, 5921, -1297, -26167, 15094, 26378, -16383, -5667, 3255, 239], ![-239, 1792, 5204, -12052, -18997, 26566, 17774, -19490, -3038, 3494]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -3, -45, 30, 48, -36, -13, 11, 1], ![-1, 9, 7, -48, -15, 78, 12, -49, -2, 12], ![-12, 119, -27, -533, 312, 561, -354, -144, 83, 10], ![-10, 88, 89, -477, -233, 792, 201, -484, -34, 93], ![-93, 920, -191, -4096, 2313, 4231, -2556, -1008, 539, 59], ![-59, 497, 743, -2846, -2326, 5145, 2107, -3323, -359, 598], ![-598, 5921, -1297, -26167, 15094, 26378, -16383, -5667, 3255, 239], ![-239, 1792, 5204, -12052, -18997, 26566, 17774, -19490, -3038, 3494], ![-3494, 34701, -8690, -152026, 92768, 148715, -99218, -27648, 18944, 456]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-10, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-10, -12, -1, -1], [-93, -10, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-10, -12, -1, -1], [-93, -10, -12, -1, -1], [-59, -93, -10, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-10, -12, -1, -1], [-93, -10, -12, -1, -1], [-59, -93, -10, -12, -1, -1], [-598, -59, -93, -10, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-10, -12, -1, -1], [-93, -10, -12, -1, -1], [-59, -93, -10, -12, -1, -1], [-598, -59, -93, -10, -12, -1, -1], [-239, -598, -59, -93, -10, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-10, -12, -1, -1], [-93, -10, -12, -1, -1], [-59, -93, -10, -12, -1, -1], [-598, -59, -93, -10, -12, -1, -1], [-239, -598, -59, -93, -10, -12, -1, -1], [-3494, -239, -598, -59, -93, -10, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -3, -45, 30, 48, -36, -13, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -3, -45, 30, 48, -36, -13, 11, 1], [-1, 9, 7, -48, -15, 78, 12, -49, -2, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -3, -45, 30, 48, -36, -13, 11, 1], [-1, 9, 7, -48, -15, 78, 12, -49, -2, 12], [-12, 119, -27, -533, 312, 561, -354, -144, 83, 10]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -3, -45, 30, 48, -36, -13, 11, 1], [-1, 9, 7, -48, -15, 78, 12, -49, -2, 12], [-12, 119, -27, -533, 312, 561, -354, -144, 83, 10], [-10, 88, 89, -477, -233, 792, 201, -484, -34, 93]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -3, -45, 30, 48, -36, -13, 11, 1], [-1, 9, 7, -48, -15, 78, 12, -49, -2, 12], [-12, 119, -27, -533, 312, 561, -354, -144, 83, 10], [-10, 88, 89, -477, -233, 792, 201, -484, -34, 93], [-93, 920, -191, -4096, 2313, 4231, -2556, -1008, 539, 59]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -3, -45, 30, 48, -36, -13, 11, 1], [-1, 9, 7, -48, -15, 78, 12, -49, -2, 12], [-12, 119, -27, -533, 312, 561, -354, -144, 83, 10], [-10, 88, 89, -477, -233, 792, 201, -484, -34, 93], [-93, 920, -191, -4096, 2313, 4231, -2556, -1008, 539, 59], [-59, 497, 743, -2846, -2326, 5145, 2107, -3323, -359, 598]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -3, -45, 30, 48, -36, -13, 11, 1], [-1, 9, 7, -48, -15, 78, 12, -49, -2, 12], [-12, 119, -27, -533, 312, 561, -354, -144, 83, 10], [-10, 88, 89, -477, -233, 792, 201, -484, -34, 93], [-93, 920, -191, -4096, 2313, 4231, -2556, -1008, 539, 59], [-59, 497, 743, -2846, -2326, 5145, 2107, -3323, -359, 598], [-598, 5921, -1297, -26167, 15094, 26378, -16383, -5667, 3255, 239]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -3, -45, 30, 48, -36, -13, 11, 1], [-1, 9, 7, -48, -15, 78, 12, -49, -2, 12], [-12, 119, -27, -533, 312, 561, -354, -144, 83, 10], [-10, 88, 89, -477, -233, 792, 201, -484, -34, 93], [-93, 920, -191, -4096, 2313, 4231, -2556, -1008, 539, 59], [-59, 497, 743, -2846, -2326, 5145, 2107, -3323, -359, 598], [-598, 5921, -1297, -26167, 15094, 26378, -16383, -5667, 3255, 239], [-239, 1792, 5204, -12052, -18997, 26566, 17774, -19490, -3038, 3494]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -3, -45, 30, 48, -36, -13, 11, 1], [-1, 9, 7, -48, -15, 78, 12, -49, -2, 12], [-12, 119, -27, -533, 312, 561, -354, -144, 83, 10], [-10, 88, 89, -477, -233, 792, 201, -484, -34, 93], [-93, 920, -191, -4096, 2313, 4231, -2556, -1008, 539, 59], [-59, 497, 743, -2846, -2326, 5145, 2107, -3323, -359, 598], [-598, 5921, -1297, -26167, 15094, 26378, -16383, -5667, 3255, 239], [-239, 1792, 5204, -12052, -18997, 26566, 17774, -19490, -3038, 3494], [-3494, 34701, -8690, -152026, 92768, 148715, -99218, -27648, 18944, 456]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp4001 : Fact (Nat.Prime 4001) := fact_iff.2 (by norm_num)
instance hp132761 : Fact (Nat.Prime 132761) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 2, 4]
  b' := [1, 4, 3, 0, 2]
  k := [1]
  f := [0, 2, 1, -9, 10, 10, -4, -1, 3, 1]
  g := [1, 0, 4, 0, 2, 1]
  h := [1, 0, 4, 0, 2, 1]
  a := [0, 2, 3, 2]
  b := [1, 0, 2, 2, 1, 1, 0, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD4001 : CertificateDedekindCriterionLists l 4001 where
  n := 2
  a' := [1286, 1417, 3479, 1729, 1317, 2811, 941, 1672]
  b' := [455, 354, 644, 2479, 1174, 1348, 431, 1203, 2037]
  k := [3115, 2625, 2077, 3105, 1567, 1352, 2109, 3167, 1]
  f := [1857, 1302, 894, 596, 965, 323, 925, 1713, 957, 1]
  g := [3074, 2154, 1479, 986, 1597, 534, 1531, 2835, 1583, 1]
  h := [2417, 1]
  a := [1440, 2253, 360, 1274, 3277, 3877, 816, 3906, 1003]
  b := [2466, 2982, 2581, 3103, 629, 2749, 2361, 3817, 2998]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD132761 : CertificateDedekindCriterionLists l 132761 where
  n := 2
  a' := [30976, 39270, 26036, 104550, 105159, 33196, 43668, 1341]
  b' := [49802, 1753, 68996, 88304, 55228, 22883, 106543, 297, 132612]
  k := [93321, 36655, 131755, 67452, 103454, 43651, 82183, 1161, 1]
  f := [79399, 38358, 89703, 106172, 100968, 99139, 88898, 71135, 578, 1]
  g := [79748, 38526, 90097, 106638, 101411, 99574, 89288, 71447, 580, 1]
  h := [132180, 1]
  a := [23486, 109200, 130226, 15701, 102854, 57835, 123617, 97654, 8248]
  b := [13030, 87155, 9215, 15075, 82800, 100255, 113720, 51603, 124513]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 4001, 132761]
  exp := ![1, 1, 1]
  pdgood := [5, 4001, 132761]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp4001.out
    exact hp132761.out
  a := [-10956201665, -10797266998, 129919586388, 8645676154, -226150418561, 26306480378, 102481271266, -8339212324, -13559975040]
  b := [-1361208547, 9059749837, 7561899655, -38418841208, -5017590888, 41750669773, -2215113341, -13436753534, 698321482, 1355997504]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 4001 T_ofList CD4001
    exact satisfiesDedekindCriterion_of_certificate_lists T l 132761 T_ofList CD132761

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

end VoightMaximalOrderD10R67

namespace VoightMaximalOrderD10R68

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1687684377149, [1, -7, -1, 40, -7, -54, 12, 24, -7, -3, 1], 1⟩
local notation "l" => [1, -7, -1, 40, -7, -54, 12, 24, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 1, -40, 7, 54, -12, -24, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 1, -40, 7, 54, -12, -24, 7, 3], ![-3, 20, 10, -119, -19, 169, 18, -84, -3, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 1, -40, 7, 54, -12, -24, 7, 3], ![-3, 20, 10, -119, -19, 169, 18, -84, -3, 16], ![-16, 109, 36, -630, -7, 845, -23, -366, 28, 45]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 1, -40, 7, 54, -12, -24, 7, 3], ![-3, 20, 10, -119, -19, 169, 18, -84, -3, 16], ![-16, 109, 36, -630, -7, 845, -23, -366, 28, 45], ![-45, 299, 154, -1764, -315, 2423, 305, -1103, -51, 163]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 1, -40, 7, 54, -12, -24, 7, 3], ![-3, 20, 10, -119, -19, 169, 18, -84, -3, 16], ![-16, 109, 36, -630, -7, 845, -23, -366, 28, 45], ![-45, 299, 154, -1764, -315, 2423, 305, -1103, -51, 163], ![-163, 1096, 462, -6366, -623, 8487, 467, -3607, 38, 438]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 1, -40, 7, 54, -12, -24, 7, 3], ![-3, 20, 10, -119, -19, 169, 18, -84, -3, 16], ![-16, 109, 36, -630, -7, 845, -23, -366, 28, 45], ![-45, 299, 154, -1764, -315, 2423, 305, -1103, -51, 163], ![-163, 1096, 462, -6366, -623, 8487, 467, -3607, 38, 438], ![-438, 2903, 1534, -17058, -3300, 23029, 3231, -10045, -541, 1352]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 1, -40, 7, 54, -12, -24, 7, 3], ![-3, 20, 10, -119, -19, 169, 18, -84, -3, 16], ![-16, 109, 36, -630, -7, 845, -23, -366, 28, 45], ![-45, 299, 154, -1764, -315, 2423, 305, -1103, -51, 163], ![-163, 1096, 462, -6366, -623, 8487, 467, -3607, 38, 438], ![-438, 2903, 1534, -17058, -3300, 23029, 3231, -10045, -541, 1352], ![-1352, 9026, 4255, -52546, -7594, 69708, 6805, -29217, -581, 3515]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 1, -40, 7, 54, -12, -24, 7, 3], ![-3, 20, 10, -119, -19, 169, 18, -84, -3, 16], ![-16, 109, 36, -630, -7, 845, -23, -366, 28, 45], ![-45, 299, 154, -1764, -315, 2423, 305, -1103, -51, 163], ![-163, 1096, 462, -6366, -623, 8487, 467, -3607, 38, 438], ![-438, 2903, 1534, -17058, -3300, 23029, 3231, -10045, -541, 1352], ![-1352, 9026, 4255, -52546, -7594, 69708, 6805, -29217, -581, 3515], ![-3515, 23253, 12541, -136345, -27941, 182216, 27528, -77555, -4612, 9964]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 7, 1, -40, 7, 54, -12, -24, 7, 3], ![-3, 20, 10, -119, -19, 169, 18, -84, -3, 16], ![-16, 109, 36, -630, -7, 845, -23, -366, 28, 45], ![-45, 299, 154, -1764, -315, 2423, 305, -1103, -51, 163], ![-163, 1096, 462, -6366, -623, 8487, 467, -3607, 38, 438], ![-438, 2903, 1534, -17058, -3300, 23029, 3231, -10045, -541, 1352], ![-1352, 9026, 4255, -52546, -7594, 69708, 6805, -29217, -581, 3515], ![-3515, 23253, 12541, -136345, -27941, 182216, 27528, -77555, -4612, 9964], ![-9964, 66233, 33217, -386019, -66597, 510115, 62648, -211608, -7807, 25280]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-163, -45, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-163, -45, -16, -3, -1], [-438, -163, -45, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-163, -45, -16, -3, -1], [-438, -163, -45, -16, -3, -1], [-1352, -438, -163, -45, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-163, -45, -16, -3, -1], [-438, -163, -45, -16, -3, -1], [-1352, -438, -163, -45, -16, -3, -1], [-3515, -1352, -438, -163, -45, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-163, -45, -16, -3, -1], [-438, -163, -45, -16, -3, -1], [-1352, -438, -163, -45, -16, -3, -1], [-3515, -1352, -438, -163, -45, -16, -3, -1], [-9964, -3515, -1352, -438, -163, -45, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 1, -40, 7, 54, -12, -24, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 1, -40, 7, 54, -12, -24, 7, 3], [-3, 20, 10, -119, -19, 169, 18, -84, -3, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 1, -40, 7, 54, -12, -24, 7, 3], [-3, 20, 10, -119, -19, 169, 18, -84, -3, 16], [-16, 109, 36, -630, -7, 845, -23, -366, 28, 45]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 1, -40, 7, 54, -12, -24, 7, 3], [-3, 20, 10, -119, -19, 169, 18, -84, -3, 16], [-16, 109, 36, -630, -7, 845, -23, -366, 28, 45], [-45, 299, 154, -1764, -315, 2423, 305, -1103, -51, 163]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 1, -40, 7, 54, -12, -24, 7, 3], [-3, 20, 10, -119, -19, 169, 18, -84, -3, 16], [-16, 109, 36, -630, -7, 845, -23, -366, 28, 45], [-45, 299, 154, -1764, -315, 2423, 305, -1103, -51, 163], [-163, 1096, 462, -6366, -623, 8487, 467, -3607, 38, 438]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 1, -40, 7, 54, -12, -24, 7, 3], [-3, 20, 10, -119, -19, 169, 18, -84, -3, 16], [-16, 109, 36, -630, -7, 845, -23, -366, 28, 45], [-45, 299, 154, -1764, -315, 2423, 305, -1103, -51, 163], [-163, 1096, 462, -6366, -623, 8487, 467, -3607, 38, 438], [-438, 2903, 1534, -17058, -3300, 23029, 3231, -10045, -541, 1352]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 1, -40, 7, 54, -12, -24, 7, 3], [-3, 20, 10, -119, -19, 169, 18, -84, -3, 16], [-16, 109, 36, -630, -7, 845, -23, -366, 28, 45], [-45, 299, 154, -1764, -315, 2423, 305, -1103, -51, 163], [-163, 1096, 462, -6366, -623, 8487, 467, -3607, 38, 438], [-438, 2903, 1534, -17058, -3300, 23029, 3231, -10045, -541, 1352], [-1352, 9026, 4255, -52546, -7594, 69708, 6805, -29217, -581, 3515]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 1, -40, 7, 54, -12, -24, 7, 3], [-3, 20, 10, -119, -19, 169, 18, -84, -3, 16], [-16, 109, 36, -630, -7, 845, -23, -366, 28, 45], [-45, 299, 154, -1764, -315, 2423, 305, -1103, -51, 163], [-163, 1096, 462, -6366, -623, 8487, 467, -3607, 38, 438], [-438, 2903, 1534, -17058, -3300, 23029, 3231, -10045, -541, 1352], [-1352, 9026, 4255, -52546, -7594, 69708, 6805, -29217, -581, 3515], [-3515, 23253, 12541, -136345, -27941, 182216, 27528, -77555, -4612, 9964]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 7, 1, -40, 7, 54, -12, -24, 7, 3], [-3, 20, 10, -119, -19, 169, 18, -84, -3, 16], [-16, 109, 36, -630, -7, 845, -23, -366, 28, 45], [-45, 299, 154, -1764, -315, 2423, 305, -1103, -51, 163], [-163, 1096, 462, -6366, -623, 8487, 467, -3607, 38, 438], [-438, 2903, 1534, -17058, -3300, 23029, 3231, -10045, -541, 1352], [-1352, 9026, 4255, -52546, -7594, 69708, 6805, -29217, -581, 3515], [-3515, 23253, 12541, -136345, -27941, 182216, 27528, -77555, -4612, 9964], [-9964, 66233, 33217, -386019, -66597, 510115, 62648, -211608, -7807, 25280]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp17 : Fact (Nat.Prime 17) := fact_iff.2 (by norm_num)
instance hp41 : Fact (Nat.Prime 41) := fact_iff.2 (by norm_num)
instance hp2179 : Fact (Nat.Prime 2179) := fact_iff.2 (by norm_num)
instance hp27103 : Fact (Nat.Prime 27103) := fact_iff.2 (by norm_num)

def CD17 : CertificateDedekindCriterionLists l 17 where
  n := 2
  a' := [11, 6, 9, 0, 8, 11, 9, 8]
  b' := [15, 3, 5, 3, 5, 3, 16, 0, 1]
  k := [15, 8, 5, 2, 13, 15, 13, 4, 1]
  f := [2, 2, 5, 3, 6, 5, 3, 4, 4, 1]
  g := [7, 4, 16, 15, 16, 3, 12, 16, 9, 1]
  h := [5, 1]
  a := [3, 13, 16, 5, 7, 15, 14, 12, 9]
  b := [9, 0, 3, 11, 4, 10, 4, 16, 8]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD41 : CertificateDedekindCriterionLists l 41 where
  n := 2
  a' := [17, 16, 36, 18, 3, 37, 12]
  b' := [30, 6, 27, 1, 24, 30, 1, 19]
  k := [36, 14, 32, 33, 19, 25, 1]
  f := [29, 34, 31, 43, 31, 11, 27, 29, 9, 1]
  g := [35, 13, 26, 32, 11, 2, 31, 11, 1]
  h := [34, 27, 1]
  a := [3, 16, 8, 37, 22, 5, 3, 30]
  b := [28, 32, 28, 21, 29, 23, 16, 16, 11]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2179 : CertificateDedekindCriterionLists l 2179 where
  n := 2
  a' := [949, 705, 192, 750, 1195, 1711, 129, 1269]
  b' := [1805, 1941, 564, 1606, 225, 285, 2038, 638, 2038]
  k := [1080, 2156, 362, 1149, 1543, 792, 388, 2006, 1]
  f := [11, 51, 10, 84, 62, 52, 43, 37, 82, 1]
  g := [282, 1304, 241, 2151, 1564, 1314, 1087, 936, 2091, 1]
  h := [85, 1]
  a := [584, 655, 1214, 143, 910, 1386, 2132, 464, 1255]
  b := [974, 627, 1452, 584, 622, 1670, 777, 1907, 924]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD27103 : CertificateDedekindCriterionLists l 27103 where
  n := 2
  a' := [8973, 16602, 2692, 26004, 24114, 3214, 9787, 24607]
  b' := [4694, 25725, 17891, 20640, 26774, 26267, 3090, 4887, 18346]
  k := [839, 19850, 6550, 11849, 19829, 15791, 24760, 6515, 1]
  f := [2729, 4003, 3045, 10939, 2367, 22484, 7551, 12338, 2865, 1]
  g := [3102, 4550, 3461, 12434, 2690, 25557, 8582, 14024, 3256, 1]
  h := [23844, 1]
  a := [25721, 20701, 11643, 23517, 26137, 1731, 1048, 23504, 982]
  b := [14645, 23592, 9906, 2981, 526, 3975, 3277, 8119, 26121]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![17, 41, 2179, 27103]
  exp := ![1, 1, 1, 1]
  pdgood := [17, 41, 2179, 27103]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp17.out
    exact hp41.out
    exact hp2179.out
    exact hp27103.out
  a := [-84776749170, -402445535816, 428014804482, 1189857052512, -653648460451, -866498791860, 430236340634, 150112521560, -72733567400]
  b := [-17991397537, 32424929064, 158013248828, -102306698398, -257009177659, 113938696341, 129480646207, -54594376812, -17193259178, 7273356740]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 17 T_ofList CD17
    exact satisfiesDedekindCriterion_of_certificate_lists T l 41 T_ofList CD41
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2179 T_ofList CD2179
    exact satisfiesDedekindCriterion_of_certificate_lists T l 27103 T_ofList CD27103

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

end VoightMaximalOrderD10R68

end TraceEuclidean
