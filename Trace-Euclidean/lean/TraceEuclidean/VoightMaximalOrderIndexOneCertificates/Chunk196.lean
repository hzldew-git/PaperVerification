import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk192
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

namespace VoightMaximalOrderD10R304

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4191810278125, [5, 40, 59, -46, -95, 17, 52, -2, -12, 0, 1], 1⟩
local notation "l" => [5, 40, 59, -46, -95, 17, 52, -2, -12, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, -40, -59, 46, 95, -17, -52, 2, 12, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, -40, -59, 46, 95, -17, -52, 2, 12, 0], ![0, -5, -40, -59, 46, 95, -17, -52, 2, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, -40, -59, 46, 95, -17, -52, 2, 12, 0], ![0, -5, -40, -59, 46, 95, -17, -52, 2, 12], ![-60, -480, -713, 512, 1081, -158, -529, 7, 92, 2]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, -40, -59, 46, 95, -17, -52, 2, 12, 0], ![0, -5, -40, -59, 46, 95, -17, -52, 2, 12], ![-60, -480, -713, 512, 1081, -158, -529, 7, 92, 2], ![-10, -140, -598, -621, 702, 1047, -262, -525, 31, 92]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, -40, -59, 46, 95, -17, -52, 2, 12, 0], ![0, -5, -40, -59, 46, 95, -17, -52, 2, 12], ![-60, -480, -713, 512, 1081, -158, -529, 7, 92, 2], ![-10, -140, -598, -621, 702, 1047, -262, -525, 31, 92], ![-460, -3690, -5568, 3634, 8119, -862, -3737, -78, 579, 31]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, -40, -59, 46, 95, -17, -52, 2, 12, 0], ![0, -5, -40, -59, 46, 95, -17, -52, 2, 12], ![-60, -480, -713, 512, 1081, -158, -529, 7, 92, 2], ![-10, -140, -598, -621, 702, 1047, -262, -525, 31, 92], ![-460, -3690, -5568, 3634, 8119, -862, -3737, -78, 579, 31], ![-155, -1700, -5519, -4142, 6579, 7592, -2474, -3675, 294, 579]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, -40, -59, 46, 95, -17, -52, 2, 12, 0], ![0, -5, -40, -59, 46, 95, -17, -52, 2, 12], ![-60, -480, -713, 512, 1081, -158, -529, 7, 92, 2], ![-10, -140, -598, -621, 702, 1047, -262, -525, 31, 92], ![-460, -3690, -5568, 3634, 8119, -862, -3737, -78, 579, 31], ![-155, -1700, -5519, -4142, 6579, 7592, -2474, -3675, 294, 579], ![-2895, -23315, -35861, 21115, 50863, -3264, -22516, -1316, 3273, 294]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, -40, -59, 46, 95, -17, -52, 2, 12, 0], ![0, -5, -40, -59, 46, 95, -17, -52, 2, 12], ![-60, -480, -713, 512, 1081, -158, -529, 7, 92, 2], ![-10, -140, -598, -621, 702, 1047, -262, -525, 31, 92], ![-460, -3690, -5568, 3634, 8119, -862, -3737, -78, 579, 31], ![-155, -1700, -5519, -4142, 6579, 7592, -2474, -3675, 294, 579], ![-2895, -23315, -35861, 21115, 50863, -3264, -22516, -1316, 3273, 294], ![-1470, -14655, -40661, -22337, 49045, 45865, -18552, -21928, 2212, 3273]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, -40, -59, 46, 95, -17, -52, 2, 12, 0], ![0, -5, -40, -59, 46, 95, -17, -52, 2, 12], ![-60, -480, -713, 512, 1081, -158, -529, 7, 92, 2], ![-10, -140, -598, -621, 702, 1047, -262, -525, 31, 92], ![-460, -3690, -5568, 3634, 8119, -862, -3737, -78, 579, 31], ![-155, -1700, -5519, -4142, 6579, 7592, -2474, -3675, 294, 579], ![-2895, -23315, -35861, 21115, 50863, -3264, -22516, -1316, 3273, 294], ![-1470, -14655, -40661, -22337, 49045, 45865, -18552, -21928, 2212, 3273], ![-16365, -132390, -207762, 109897, 288598, -6596, -124331, -12006, 17348, 2212]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-2, -12, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-2, -12, 0, -1], [-92, -2, -12, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-12, 0, -1], [-2, -12, 0, -1], [-92, -2, -12, 0, -1], [-31, -92, -2, -12, 0, -1]], ![[], [], [], [-1], [0, -1], [-12, 0, -1], [-2, -12, 0, -1], [-92, -2, -12, 0, -1], [-31, -92, -2, -12, 0, -1], [-579, -31, -92, -2, -12, 0, -1]], ![[], [], [-1], [0, -1], [-12, 0, -1], [-2, -12, 0, -1], [-92, -2, -12, 0, -1], [-31, -92, -2, -12, 0, -1], [-579, -31, -92, -2, -12, 0, -1], [-294, -579, -31, -92, -2, -12, 0, -1]], ![[], [-1], [0, -1], [-12, 0, -1], [-2, -12, 0, -1], [-92, -2, -12, 0, -1], [-31, -92, -2, -12, 0, -1], [-579, -31, -92, -2, -12, 0, -1], [-294, -579, -31, -92, -2, -12, 0, -1], [-3273, -294, -579, -31, -92, -2, -12, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, -40, -59, 46, 95, -17, -52, 2, 12, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, -40, -59, 46, 95, -17, -52, 2, 12, 0], [0, -5, -40, -59, 46, 95, -17, -52, 2, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, -40, -59, 46, 95, -17, -52, 2, 12, 0], [0, -5, -40, -59, 46, 95, -17, -52, 2, 12], [-60, -480, -713, 512, 1081, -158, -529, 7, 92, 2]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, -40, -59, 46, 95, -17, -52, 2, 12, 0], [0, -5, -40, -59, 46, 95, -17, -52, 2, 12], [-60, -480, -713, 512, 1081, -158, -529, 7, 92, 2], [-10, -140, -598, -621, 702, 1047, -262, -525, 31, 92]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, -40, -59, 46, 95, -17, -52, 2, 12, 0], [0, -5, -40, -59, 46, 95, -17, -52, 2, 12], [-60, -480, -713, 512, 1081, -158, -529, 7, 92, 2], [-10, -140, -598, -621, 702, 1047, -262, -525, 31, 92], [-460, -3690, -5568, 3634, 8119, -862, -3737, -78, 579, 31]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, -40, -59, 46, 95, -17, -52, 2, 12, 0], [0, -5, -40, -59, 46, 95, -17, -52, 2, 12], [-60, -480, -713, 512, 1081, -158, -529, 7, 92, 2], [-10, -140, -598, -621, 702, 1047, -262, -525, 31, 92], [-460, -3690, -5568, 3634, 8119, -862, -3737, -78, 579, 31], [-155, -1700, -5519, -4142, 6579, 7592, -2474, -3675, 294, 579]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, -40, -59, 46, 95, -17, -52, 2, 12, 0], [0, -5, -40, -59, 46, 95, -17, -52, 2, 12], [-60, -480, -713, 512, 1081, -158, -529, 7, 92, 2], [-10, -140, -598, -621, 702, 1047, -262, -525, 31, 92], [-460, -3690, -5568, 3634, 8119, -862, -3737, -78, 579, 31], [-155, -1700, -5519, -4142, 6579, 7592, -2474, -3675, 294, 579], [-2895, -23315, -35861, 21115, 50863, -3264, -22516, -1316, 3273, 294]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, -40, -59, 46, 95, -17, -52, 2, 12, 0], [0, -5, -40, -59, 46, 95, -17, -52, 2, 12], [-60, -480, -713, 512, 1081, -158, -529, 7, 92, 2], [-10, -140, -598, -621, 702, 1047, -262, -525, 31, 92], [-460, -3690, -5568, 3634, 8119, -862, -3737, -78, 579, 31], [-155, -1700, -5519, -4142, 6579, 7592, -2474, -3675, 294, 579], [-2895, -23315, -35861, 21115, 50863, -3264, -22516, -1316, 3273, 294], [-1470, -14655, -40661, -22337, 49045, 45865, -18552, -21928, 2212, 3273]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, -40, -59, 46, 95, -17, -52, 2, 12, 0], [0, -5, -40, -59, 46, 95, -17, -52, 2, 12], [-60, -480, -713, 512, 1081, -158, -529, 7, 92, 2], [-10, -140, -598, -621, 702, 1047, -262, -525, 31, 92], [-460, -3690, -5568, 3634, 8119, -862, -3737, -78, 579, 31], [-155, -1700, -5519, -4142, 6579, 7592, -2474, -3675, 294, 579], [-2895, -23315, -35861, 21115, 50863, -3264, -22516, -1316, 3273, 294], [-1470, -14655, -40661, -22337, 49045, 45865, -18552, -21928, 2212, 3273], [-16365, -132390, -207762, 109897, 288598, -6596, -124331, -12006, 17348, 2212]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp4519 : Fact (Nat.Prime 4519) := fact_iff.2 (by norm_num)
instance hp296831 : Fact (Nat.Prime 296831) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1]
  b' := [2, 2, 2, 2]
  k := [1]
  f := [-1, -8, -10, 14, 27, 3, -6, 2, 4]
  g := [0, 3, 4, 4, 0, 1]
  h := [0, 3, 4, 4, 0, 1]
  a := [4]
  b := [4, 3, 2, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD4519 : CertificateDedekindCriterionLists l 4519 where
  n := 2
  a' := [864, 3547, 3532, 2594, 3801, 2086, 701, 1643]
  b' := [1848, 396, 961, 3410, 1639, 1697, 1265, 3981, 2328]
  k := [932, 4016, 3043, 3480, 2976, 3973, 2873, 2353, 1]
  f := [388, 715, 172, 728, 1065, 875, 442, 589, 824, 1]
  g := [1619, 2982, 715, 3037, 4441, 3647, 1841, 2456, 3436, 1]
  h := [1083, 1]
  a := [2313, 3090, 757, 182, 2602, 2504, 769, 1207, 4140]
  b := [4054, 638, 2793, 597, 4202, 1243, 533, 3025, 379]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD296831 : CertificateDedekindCriterionLists l 296831 where
  n := 2
  a' := [49834, 83298, 133547, 81639, 223613, 83136, 140652, 272416]
  b' := [82015, 104089, 233596, 158820, 264052, 114991, 95326, 207558, 35694]
  k := [282031, 54614, 246846, 178041, 106908, 128933, 129651, 5651, 1]
  f := [128045, 12490, 70674, 84427, 139025, 81798, 116687, 21194, 74181, 1]
  g := [261060, 25463, 144091, 172130, 283445, 166769, 237902, 43209, 151241, 1]
  h := [145590, 1]
  a := [137631, 181576, 75757, 144707, 67718, 156158, 83692, 45769, 61343]
  b := [104451, 34241, 102176, 148335, 70513, 131044, 203151, 12136, 235488]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 4519, 296831]
  exp := ![1, 1, 1]
  pdgood := [5, 4519, 296831]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp4519.out
    exact hp296831.out
  a := [-15868293991, -16176342672, 70565024199, 41672375594, -79402980970, -25425950374, 31972742680, 4231910090, -4166620900]
  b := [2151209160, 11544269803, 4127523967, -22074481659, -7661483724, 14934347864, 3308256205, -4197263284, -423191009, 416662090]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 4519 T_ofList CD4519
    exact satisfiesDedekindCriterion_of_certificate_lists T l 296831 T_ofList CD296831

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

end VoightMaximalOrderD10R304

namespace VoightMaximalOrderD10R305

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4192566003125, [-1, 11, 30, -20, -60, 12, 41, -2, -11, 0, 1], 1⟩
local notation "l" => [-1, 11, 30, -20, -60, 12, 41, -2, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -11, -30, 20, 60, -12, -41, 2, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -11, -30, 20, 60, -12, -41, 2, 11, 0], ![0, 1, -11, -30, 20, 60, -12, -41, 2, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -11, -30, 20, 60, -12, -41, 2, 11, 0], ![0, 1, -11, -30, 20, 60, -12, -41, 2, 11], ![11, -121, -329, 209, 630, -112, -391, 10, 80, 2]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -11, -30, 20, 60, -12, -41, 2, 11, 0], ![0, 1, -11, -30, 20, 60, -12, -41, 2, 11], ![11, -121, -329, 209, 630, -112, -391, 10, 80, 2], ![2, -11, -181, -289, 329, 606, -194, -387, 32, 80]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -11, -30, 20, 60, -12, -41, 2, 11, 0], ![0, 1, -11, -30, 20, 60, -12, -41, 2, 11], ![11, -121, -329, 209, 630, -112, -391, 10, 80, 2], ![2, -11, -181, -289, 329, 606, -194, -387, 32, 80], ![80, -878, -2411, 1419, 4511, -631, -2674, -34, 493, 32]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -11, -30, 20, 60, -12, -41, 2, 11, 0], ![0, 1, -11, -30, 20, 60, -12, -41, 2, 11], ![11, -121, -329, 209, 630, -112, -391, 10, 80, 2], ![2, -11, -181, -289, 329, 606, -194, -387, 32, 80], ![80, -878, -2411, 1419, 4511, -631, -2674, -34, 493, 32], ![32, -272, -1838, -1771, 3339, 4127, -1943, -2610, 318, 493]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -11, -30, 20, 60, -12, -41, 2, 11, 0], ![0, 1, -11, -30, 20, 60, -12, -41, 2, 11], ![11, -121, -329, 209, 630, -112, -391, 10, 80, 2], ![2, -11, -181, -289, 329, 606, -194, -387, 32, 80], ![80, -878, -2411, 1419, 4511, -631, -2674, -34, 493, 32], ![32, -272, -1838, -1771, 3339, 4127, -1943, -2610, 318, 493], ![493, -5391, -15062, 8022, 27809, -2577, -16086, -957, 2813, 318]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -11, -30, 20, 60, -12, -41, 2, 11, 0], ![0, 1, -11, -30, 20, 60, -12, -41, 2, 11], ![11, -121, -329, 209, 630, -112, -391, 10, 80, 2], ![2, -11, -181, -289, 329, 606, -194, -387, 32, 80], ![80, -878, -2411, 1419, 4511, -631, -2674, -34, 493, 32], ![32, -272, -1838, -1771, 3339, 4127, -1943, -2610, 318, 493], ![493, -5391, -15062, 8022, 27809, -2577, -16086, -957, 2813, 318], ![318, -3005, -14931, -8702, 27102, 23993, -15615, -15450, 2541, 2813]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -11, -30, 20, 60, -12, -41, 2, 11, 0], ![0, 1, -11, -30, 20, 60, -12, -41, 2, 11], ![11, -121, -329, 209, 630, -112, -391, 10, 80, 2], ![2, -11, -181, -289, 329, 606, -194, -387, 32, 80], ![80, -878, -2411, 1419, 4511, -631, -2674, -34, 493, 32], ![32, -272, -1838, -1771, 3339, 4127, -1943, -2610, 318, 493], ![493, -5391, -15062, 8022, 27809, -2577, -16086, -957, 2813, 318], ![318, -3005, -14931, -8702, 27102, 23993, -15615, -15450, 2541, 2813], ![2813, -30625, -87395, 41329, 160078, -6654, -91340, -9989, 15493, 2541]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-80, -2, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-80, -2, -11, 0, -1], [-32, -80, -2, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-80, -2, -11, 0, -1], [-32, -80, -2, -11, 0, -1], [-493, -32, -80, -2, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-80, -2, -11, 0, -1], [-32, -80, -2, -11, 0, -1], [-493, -32, -80, -2, -11, 0, -1], [-318, -493, -32, -80, -2, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-80, -2, -11, 0, -1], [-32, -80, -2, -11, 0, -1], [-493, -32, -80, -2, -11, 0, -1], [-318, -493, -32, -80, -2, -11, 0, -1], [-2813, -318, -493, -32, -80, -2, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -11, -30, 20, 60, -12, -41, 2, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -11, -30, 20, 60, -12, -41, 2, 11, 0], [0, 1, -11, -30, 20, 60, -12, -41, 2, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -11, -30, 20, 60, -12, -41, 2, 11, 0], [0, 1, -11, -30, 20, 60, -12, -41, 2, 11], [11, -121, -329, 209, 630, -112, -391, 10, 80, 2]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -11, -30, 20, 60, -12, -41, 2, 11, 0], [0, 1, -11, -30, 20, 60, -12, -41, 2, 11], [11, -121, -329, 209, 630, -112, -391, 10, 80, 2], [2, -11, -181, -289, 329, 606, -194, -387, 32, 80]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -11, -30, 20, 60, -12, -41, 2, 11, 0], [0, 1, -11, -30, 20, 60, -12, -41, 2, 11], [11, -121, -329, 209, 630, -112, -391, 10, 80, 2], [2, -11, -181, -289, 329, 606, -194, -387, 32, 80], [80, -878, -2411, 1419, 4511, -631, -2674, -34, 493, 32]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -11, -30, 20, 60, -12, -41, 2, 11, 0], [0, 1, -11, -30, 20, 60, -12, -41, 2, 11], [11, -121, -329, 209, 630, -112, -391, 10, 80, 2], [2, -11, -181, -289, 329, 606, -194, -387, 32, 80], [80, -878, -2411, 1419, 4511, -631, -2674, -34, 493, 32], [32, -272, -1838, -1771, 3339, 4127, -1943, -2610, 318, 493]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -11, -30, 20, 60, -12, -41, 2, 11, 0], [0, 1, -11, -30, 20, 60, -12, -41, 2, 11], [11, -121, -329, 209, 630, -112, -391, 10, 80, 2], [2, -11, -181, -289, 329, 606, -194, -387, 32, 80], [80, -878, -2411, 1419, 4511, -631, -2674, -34, 493, 32], [32, -272, -1838, -1771, 3339, 4127, -1943, -2610, 318, 493], [493, -5391, -15062, 8022, 27809, -2577, -16086, -957, 2813, 318]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -11, -30, 20, 60, -12, -41, 2, 11, 0], [0, 1, -11, -30, 20, 60, -12, -41, 2, 11], [11, -121, -329, 209, 630, -112, -391, 10, 80, 2], [2, -11, -181, -289, 329, 606, -194, -387, 32, 80], [80, -878, -2411, 1419, 4511, -631, -2674, -34, 493, 32], [32, -272, -1838, -1771, 3339, 4127, -1943, -2610, 318, 493], [493, -5391, -15062, 8022, 27809, -2577, -16086, -957, 2813, 318], [318, -3005, -14931, -8702, 27102, 23993, -15615, -15450, 2541, 2813]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -11, -30, 20, 60, -12, -41, 2, 11, 0], [0, 1, -11, -30, 20, 60, -12, -41, 2, 11], [11, -121, -329, 209, 630, -112, -391, 10, 80, 2], [2, -11, -181, -289, 329, 606, -194, -387, 32, 80], [80, -878, -2411, 1419, 4511, -631, -2674, -34, 493, 32], [32, -272, -1838, -1771, 3339, 4127, -1943, -2610, 318, 493], [493, -5391, -15062, 8022, 27809, -2577, -16086, -957, 2813, 318], [318, -3005, -14931, -8702, 27102, 23993, -15615, -15450, 2541, 2813], [2813, -30625, -87395, 41329, 160078, -6654, -91340, -9989, 15493, 2541]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp5171 : Fact (Nat.Prime 5171) := fact_iff.2 (by norm_num)
instance hp259451 : Fact (Nat.Prime 259451) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1]
  b' := [3, 0, 3, 4]
  k := [1]
  f := [2, -1, -1, 8, 16, 2, -7, 2, 3]
  g := [3, 1, 4, 2, 0, 1]
  h := [3, 1, 4, 2, 0, 1]
  a := [0, 1, 3, 2, 4]
  b := [2, 2, 0, 1, 3, 4, 1, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD5171 : CertificateDedekindCriterionLists l 5171 where
  n := 2
  a' := [2915, 3498, 3012, 252, 3017, 2034, 1238, 3840]
  b' := [2131, 2849, 3736, 3805, 4254, 1263, 2297, 1771, 1297]
  k := [4321, 3289, 3413, 480, 3527, 4790, 2465, 4129, 1]
  f := [187, 113, 266, 12, 236, 154, 149, 256, 469, 1]
  g := [1856, 1118, 2638, 114, 2342, 1524, 1476, 2538, 4650, 1]
  h := [521, 1]
  a := [3789, 1694, 4771, 2707, 3665, 4892, 1321, 3439, 1537]
  b := [3034, 4193, 1466, 560, 1361, 1538, 34, 376, 3634]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD259451 : CertificateDedekindCriterionLists l 259451 where
  n := 2
  a' := [2235, 130144, 81492, 246063, 185710, 5739, 243784, 34188]
  b' := [22888, 84212, 83277, 146008, 200088, 31077, 82016, 44314, 82685]
  k := [109782, 179730, 176795, 200, 187992, 28209, 174821, 225782, 1]
  f := [31411, 32145, 80785, 96501, 128612, 83235, 129566, 81768, 63771, 1]
  g := [55606, 56905, 143011, 170832, 227677, 147347, 229366, 144750, 112891, 1]
  h := [146560, 1]
  a := [110059, 89165, 78614, 192145, 125781, 26732, 18192, 118165, 80806]
  b := [48616, 223525, 128267, 186300, 146653, 116244, 96229, 250608, 178645]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 5171, 259451]
  exp := ![1, 1, 1]
  pdgood := [5, 5171, 259451]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp5171.out
    exact hp259451.out
  a := [2309191508, 50357219112, 75661583880, -187984778984, -266948860856, 71735126296, 139951187644, -4854440880, -19071629380]
  b := [819754283, -2202649496, -33290849532, -38432901344, 37039457908, 51547678618, -9385787386, -18190877228, 485444088, 1907162938]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5171 T_ofList CD5171
    exact satisfiesDedekindCriterion_of_certificate_lists T l 259451 T_ofList CD259451

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

end VoightMaximalOrderD10R305

namespace VoightMaximalOrderD10R306

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4196688143624, [-1, -13, -23, 51, 42, -60, -19, 29, 0, -5, 1], 1⟩
local notation "l" => [-1, -13, -23, 51, 42, -60, -19, 29, 0, -5, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 13, 23, -51, -42, 60, 19, -29, 0, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 13, 23, -51, -42, 60, 19, -29, 0, 5], ![5, 66, 128, -232, -261, 258, 155, -126, -29, 25]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 13, 23, -51, -42, 60, 19, -29, 0, 5], ![5, 66, 128, -232, -261, 258, 155, -126, -29, 25], ![25, 330, 641, -1147, -1282, 1239, 733, -570, -126, 96]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 13, 23, -51, -42, 60, 19, -29, 0, 5], ![5, 66, 128, -232, -261, 258, 155, -126, -29, 25], ![25, 330, 641, -1147, -1282, 1239, 733, -570, -126, 96], ![96, 1273, 2538, -4255, -5179, 4478, 3063, -2051, -570, 354]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 13, 23, -51, -42, 60, 19, -29, 0, 5], ![5, 66, 128, -232, -261, 258, 155, -126, -29, 25], ![25, 330, 641, -1147, -1282, 1239, 733, -570, -126, 96], ![96, 1273, 2538, -4255, -5179, 4478, 3063, -2051, -570, 354], ![354, 4698, 9415, -15516, -19123, 16061, 11204, -7203, -2051, 1200]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 13, 23, -51, -42, 60, 19, -29, 0, 5], ![5, 66, 128, -232, -261, 258, 155, -126, -29, 25], ![25, 330, 641, -1147, -1282, 1239, 733, -570, -126, 96], ![96, 1273, 2538, -4255, -5179, 4478, 3063, -2051, -570, 354], ![354, 4698, 9415, -15516, -19123, 16061, 11204, -7203, -2051, 1200], ![1200, 15954, 32298, -51785, -65916, 52877, 38861, -23596, -7203, 3949]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 13, 23, -51, -42, 60, 19, -29, 0, 5], ![5, 66, 128, -232, -261, 258, 155, -126, -29, 25], ![25, 330, 641, -1147, -1282, 1239, 733, -570, -126, 96], ![96, 1273, 2538, -4255, -5179, 4478, 3063, -2051, -570, 354], ![354, 4698, 9415, -15516, -19123, 16061, 11204, -7203, -2051, 1200], ![1200, 15954, 32298, -51785, -65916, 52877, 38861, -23596, -7203, 3949], ![3949, 52537, 106781, -169101, -217643, 171024, 127908, -75660, -23596, 12542]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 13, 23, -51, -42, 60, 19, -29, 0, 5], ![5, 66, 128, -232, -261, 258, 155, -126, -29, 25], ![25, 330, 641, -1147, -1282, 1239, 733, -570, -126, 96], ![96, 1273, 2538, -4255, -5179, 4478, 3063, -2051, -570, 354], ![354, 4698, 9415, -15516, -19123, 16061, 11204, -7203, -2051, 1200], ![1200, 15954, 32298, -51785, -65916, 52877, 38861, -23596, -7203, 3949], ![3949, 52537, 106781, -169101, -217643, 171024, 127908, -75660, -23596, 12542], ![12542, 166995, 341003, -532861, -695865, 534877, 409322, -235810, -75660, 39114]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 13, 23, -51, -42, 60, 19, -29, 0, 5], ![5, 66, 128, -232, -261, 258, 155, -126, -29, 25], ![25, 330, 641, -1147, -1282, 1239, 733, -570, -126, 96], ![96, 1273, 2538, -4255, -5179, 4478, 3063, -2051, -570, 354], ![354, 4698, 9415, -15516, -19123, 16061, 11204, -7203, -2051, 1200], ![1200, 15954, 32298, -51785, -65916, 52877, 38861, -23596, -7203, 3949], ![3949, 52537, 106781, -169101, -217643, 171024, 127908, -75660, -23596, 12542], ![12542, 166995, 341003, -532861, -695865, 534877, 409322, -235810, -75660, 39114], ![39114, 521024, 1066617, -1653811, -2175649, 1650975, 1278043, -724984, -235810, 119910]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-5, -1]], ![[], [], [], [], [], [], [], [-1], [-5, -1], [-25, -5, -1]], ![[], [], [], [], [], [], [-1], [-5, -1], [-25, -5, -1], [-96, -25, -5, -1]], ![[], [], [], [], [], [-1], [-5, -1], [-25, -5, -1], [-96, -25, -5, -1], [-354, -96, -25, -5, -1]], ![[], [], [], [], [-1], [-5, -1], [-25, -5, -1], [-96, -25, -5, -1], [-354, -96, -25, -5, -1], [-1200, -354, -96, -25, -5, -1]], ![[], [], [], [-1], [-5, -1], [-25, -5, -1], [-96, -25, -5, -1], [-354, -96, -25, -5, -1], [-1200, -354, -96, -25, -5, -1], [-3949, -1200, -354, -96, -25, -5, -1]], ![[], [], [-1], [-5, -1], [-25, -5, -1], [-96, -25, -5, -1], [-354, -96, -25, -5, -1], [-1200, -354, -96, -25, -5, -1], [-3949, -1200, -354, -96, -25, -5, -1], [-12542, -3949, -1200, -354, -96, -25, -5, -1]], ![[], [-1], [-5, -1], [-25, -5, -1], [-96, -25, -5, -1], [-354, -96, -25, -5, -1], [-1200, -354, -96, -25, -5, -1], [-3949, -1200, -354, -96, -25, -5, -1], [-12542, -3949, -1200, -354, -96, -25, -5, -1], [-39114, -12542, -3949, -1200, -354, -96, -25, -5, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 13, 23, -51, -42, 60, 19, -29, 0, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 13, 23, -51, -42, 60, 19, -29, 0, 5], [5, 66, 128, -232, -261, 258, 155, -126, -29, 25]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 13, 23, -51, -42, 60, 19, -29, 0, 5], [5, 66, 128, -232, -261, 258, 155, -126, -29, 25], [25, 330, 641, -1147, -1282, 1239, 733, -570, -126, 96]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 13, 23, -51, -42, 60, 19, -29, 0, 5], [5, 66, 128, -232, -261, 258, 155, -126, -29, 25], [25, 330, 641, -1147, -1282, 1239, 733, -570, -126, 96], [96, 1273, 2538, -4255, -5179, 4478, 3063, -2051, -570, 354]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 13, 23, -51, -42, 60, 19, -29, 0, 5], [5, 66, 128, -232, -261, 258, 155, -126, -29, 25], [25, 330, 641, -1147, -1282, 1239, 733, -570, -126, 96], [96, 1273, 2538, -4255, -5179, 4478, 3063, -2051, -570, 354], [354, 4698, 9415, -15516, -19123, 16061, 11204, -7203, -2051, 1200]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 13, 23, -51, -42, 60, 19, -29, 0, 5], [5, 66, 128, -232, -261, 258, 155, -126, -29, 25], [25, 330, 641, -1147, -1282, 1239, 733, -570, -126, 96], [96, 1273, 2538, -4255, -5179, 4478, 3063, -2051, -570, 354], [354, 4698, 9415, -15516, -19123, 16061, 11204, -7203, -2051, 1200], [1200, 15954, 32298, -51785, -65916, 52877, 38861, -23596, -7203, 3949]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 13, 23, -51, -42, 60, 19, -29, 0, 5], [5, 66, 128, -232, -261, 258, 155, -126, -29, 25], [25, 330, 641, -1147, -1282, 1239, 733, -570, -126, 96], [96, 1273, 2538, -4255, -5179, 4478, 3063, -2051, -570, 354], [354, 4698, 9415, -15516, -19123, 16061, 11204, -7203, -2051, 1200], [1200, 15954, 32298, -51785, -65916, 52877, 38861, -23596, -7203, 3949], [3949, 52537, 106781, -169101, -217643, 171024, 127908, -75660, -23596, 12542]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 13, 23, -51, -42, 60, 19, -29, 0, 5], [5, 66, 128, -232, -261, 258, 155, -126, -29, 25], [25, 330, 641, -1147, -1282, 1239, 733, -570, -126, 96], [96, 1273, 2538, -4255, -5179, 4478, 3063, -2051, -570, 354], [354, 4698, 9415, -15516, -19123, 16061, 11204, -7203, -2051, 1200], [1200, 15954, 32298, -51785, -65916, 52877, 38861, -23596, -7203, 3949], [3949, 52537, 106781, -169101, -217643, 171024, 127908, -75660, -23596, 12542], [12542, 166995, 341003, -532861, -695865, 534877, 409322, -235810, -75660, 39114]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 13, 23, -51, -42, 60, 19, -29, 0, 5], [5, 66, 128, -232, -261, 258, 155, -126, -29, 25], [25, 330, 641, -1147, -1282, 1239, 733, -570, -126, 96], [96, 1273, 2538, -4255, -5179, 4478, 3063, -2051, -570, 354], [354, 4698, 9415, -15516, -19123, 16061, 11204, -7203, -2051, 1200], [1200, 15954, 32298, -51785, -65916, 52877, 38861, -23596, -7203, 3949], [3949, 52537, 106781, -169101, -217643, 171024, 127908, -75660, -23596, 12542], [12542, 166995, 341003, -532861, -695865, 534877, 409322, -235810, -75660, 39114], [39114, 521024, 1066617, -1653811, -2175649, 1650975, 1278043, -724984, -235810, 119910]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp67 : Fact (Nat.Prime 67) := fact_iff.2 (by norm_num)
instance hp7829642059 : Fact (Nat.Prime 7829642059) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 1, 0, 1]
  b' := [1, 1, 1, 1, 0, 1]
  k := [1, 1, 0, 0, 0, 0, 1, 1, 1]
  f := [1, 7, 12, -25, -21, 30, 10, -14, 0, 3]
  g := [1, 0, 1, 0, 0, 0, 1, 0, 0, 1]
  h := [1, 1]
  a := [0, 0, 0, 0, 0, 0, 0, 1]
  b := [1, 0, 1, 0, 1, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD67 : CertificateDedekindCriterionLists l 67 where
  n := 2
  a' := [16, 45, 49, 19, 32, 32, 44, 23]
  b' := [51, 38, 31, 30, 13, 20, 9, 14, 57]
  k := [20, 11, 43, 8, 41, 2, 16, 38, 1]
  f := [7, 4, 11, 1, 5, 13, 12, 1, 9, 1]
  g := [39, 18, 58, 5, 31, 65, 60, 3, 50, 1]
  h := [12, 1]
  a := [4, 18, 56, 32, 48, 42, 4, 36, 65]
  b := [56, 65, 18, 55, 45, 62, 7, 16, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD7829642059 : CertificateDedekindCriterionLists l 7829642059 where
  n := 2
  a' := [4483385104, 5901338919, 5083556613, 1256423928, 1126424211, 2861862829, 4394668995, 4576010077]
  b' := [5510057828, 915164108, 5370837130, 1809089769, 6250711469, 6490453412, 4230184990, 3918300596, 2971395351]
  k := [1315881806, 3173986774, 1328021394, 6955370466, 6544813765, 2199576010, 7077380151, 1984282522, 1]
  f := [2542701687, 414446939, 2088719658, 2491519677, 2460520168, 1572270421, 2676049280, 1724713345, 1831690298, 1]
  g := [6811709002, 1110272571, 5595524858, 6674596196, 6591550813, 4211995701, 7168937300, 4620378974, 4906962288, 1]
  h := [2922679766, 1]
  a := [4018378583, 7364291880, 6267698723, 6199600202, 1973261023, 1166256422, 3847288641, 5234786533, 4152089241]
  b := [6006585520, 6062846444, 7152193064, 7092060954, 3485669627, 6656662132, 4236376705, 1961667138, 3677552818]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 67, 7829642059]
  exp := ![2, 1, 1]
  pdgood := [2, 67, 7829642059]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp67.out
    exact hp7829642059.out
  a := [3137039945233, -16531200027393, -1580886919572, 59007055977492, -6881281790868, -51385908220990, 10245621907255, 12742153532815, -3754279144450]
  b := [-402721847465, -440393405942, 7921247888193, 179711344134, -14205454104540, 789764256052, 7982871684261, -1232167321586, -1461929310504, 375427914445]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 67 T_ofList CD67
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7829642059 T_ofList CD7829642059

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

end VoightMaximalOrderD10R306

namespace VoightMaximalOrderD10R308

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4223036003125, [-1, -5, 5, 32, -23, -49, 39, 13, -12, -1, 1], 1⟩
local notation "l" => [-1, -5, 5, 32, -23, -49, 39, 13, -12, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -5, -32, 23, 49, -39, -13, 12, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -5, -32, 23, 49, -39, -13, 12, 1], ![1, 6, 0, -37, -9, 72, 10, -52, -1, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -5, -32, 23, 49, -39, -13, 12, 1], ![1, 6, 0, -37, -9, 72, 10, -52, -1, 13], ![13, 66, -59, -416, 262, 628, -435, -159, 104, 12]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -5, -32, 23, 49, -39, -13, 12, 1], ![1, 6, 0, -37, -9, 72, 10, -52, -1, 13], ![13, 66, -59, -416, 262, 628, -435, -159, 104, 12], ![12, 73, 6, -443, -140, 850, 160, -591, -15, 116]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -5, -32, 23, 49, -39, -13, 12, 1], ![1, 6, 0, -37, -9, 72, 10, -52, -1, 13], ![13, 66, -59, -416, 262, 628, -435, -159, 104, 12], ![12, 73, 6, -443, -140, 850, 160, -591, -15, 116], ![116, 592, -507, -3706, 2225, 5544, -3674, -1348, 801, 101]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -5, -32, 23, 49, -39, -13, 12, 1], ![1, 6, 0, -37, -9, 72, 10, -52, -1, 13], ![13, 66, -59, -416, 262, 628, -435, -159, 104, 12], ![12, 73, 6, -443, -140, 850, 160, -591, -15, 116], ![116, 592, -507, -3706, 2225, 5544, -3674, -1348, 801, 101], ![101, 621, 87, -3739, -1383, 7174, 1605, -4987, -136, 902]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -5, -32, 23, 49, -39, -13, 12, 1], ![1, 6, 0, -37, -9, 72, 10, -52, -1, 13], ![13, 66, -59, -416, 262, 628, -435, -159, 104, 12], ![12, 73, 6, -443, -140, 850, 160, -591, -15, 116], ![116, 592, -507, -3706, 2225, 5544, -3674, -1348, 801, 101], ![101, 621, 87, -3739, -1383, 7174, 1605, -4987, -136, 902], ![902, 4611, -3889, -28777, 17007, 42815, -28004, -10121, 5837, 766]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -5, -32, 23, 49, -39, -13, 12, 1], ![1, 6, 0, -37, -9, 72, 10, -52, -1, 13], ![13, 66, -59, -416, 262, 628, -435, -159, 104, 12], ![12, 73, 6, -443, -140, 850, 160, -591, -15, 116], ![116, 592, -507, -3706, 2225, 5544, -3674, -1348, 801, 101], ![101, 621, 87, -3739, -1383, 7174, 1605, -4987, -136, 902], ![902, 4611, -3889, -28777, 17007, 42815, -28004, -10121, 5837, 766], ![766, 4732, 781, -28401, -11159, 54541, 12941, -37962, -929, 6603]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -5, -32, 23, 49, -39, -13, 12, 1], ![1, 6, 0, -37, -9, 72, 10, -52, -1, 13], ![13, 66, -59, -416, 262, 628, -435, -159, 104, 12], ![12, 73, 6, -443, -140, 850, 160, -591, -15, 116], ![116, 592, -507, -3706, 2225, 5544, -3674, -1348, 801, 101], ![101, 621, 87, -3739, -1383, 7174, 1605, -4987, -136, 902], ![902, 4611, -3889, -28777, 17007, 42815, -28004, -10121, 5837, 766], ![766, 4732, 781, -28401, -11159, 54541, 12941, -37962, -929, 6603], ![6603, 33781, -28283, -210515, 123468, 312388, -202976, -72898, 41274, 5674]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-13, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-12, -13, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-12, -13, -1, -1], [-116, -12, -13, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-12, -13, -1, -1], [-116, -12, -13, -1, -1], [-101, -116, -12, -13, -1, -1]], ![[], [], [], [-1], [-1, -1], [-13, -1, -1], [-12, -13, -1, -1], [-116, -12, -13, -1, -1], [-101, -116, -12, -13, -1, -1], [-902, -101, -116, -12, -13, -1, -1]], ![[], [], [-1], [-1, -1], [-13, -1, -1], [-12, -13, -1, -1], [-116, -12, -13, -1, -1], [-101, -116, -12, -13, -1, -1], [-902, -101, -116, -12, -13, -1, -1], [-766, -902, -101, -116, -12, -13, -1, -1]], ![[], [-1], [-1, -1], [-13, -1, -1], [-12, -13, -1, -1], [-116, -12, -13, -1, -1], [-101, -116, -12, -13, -1, -1], [-902, -101, -116, -12, -13, -1, -1], [-766, -902, -101, -116, -12, -13, -1, -1], [-6603, -766, -902, -101, -116, -12, -13, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -5, -32, 23, 49, -39, -13, 12, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -5, -32, 23, 49, -39, -13, 12, 1], [1, 6, 0, -37, -9, 72, 10, -52, -1, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -5, -32, 23, 49, -39, -13, 12, 1], [1, 6, 0, -37, -9, 72, 10, -52, -1, 13], [13, 66, -59, -416, 262, 628, -435, -159, 104, 12]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -5, -32, 23, 49, -39, -13, 12, 1], [1, 6, 0, -37, -9, 72, 10, -52, -1, 13], [13, 66, -59, -416, 262, 628, -435, -159, 104, 12], [12, 73, 6, -443, -140, 850, 160, -591, -15, 116]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -5, -32, 23, 49, -39, -13, 12, 1], [1, 6, 0, -37, -9, 72, 10, -52, -1, 13], [13, 66, -59, -416, 262, 628, -435, -159, 104, 12], [12, 73, 6, -443, -140, 850, 160, -591, -15, 116], [116, 592, -507, -3706, 2225, 5544, -3674, -1348, 801, 101]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -5, -32, 23, 49, -39, -13, 12, 1], [1, 6, 0, -37, -9, 72, 10, -52, -1, 13], [13, 66, -59, -416, 262, 628, -435, -159, 104, 12], [12, 73, 6, -443, -140, 850, 160, -591, -15, 116], [116, 592, -507, -3706, 2225, 5544, -3674, -1348, 801, 101], [101, 621, 87, -3739, -1383, 7174, 1605, -4987, -136, 902]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -5, -32, 23, 49, -39, -13, 12, 1], [1, 6, 0, -37, -9, 72, 10, -52, -1, 13], [13, 66, -59, -416, 262, 628, -435, -159, 104, 12], [12, 73, 6, -443, -140, 850, 160, -591, -15, 116], [116, 592, -507, -3706, 2225, 5544, -3674, -1348, 801, 101], [101, 621, 87, -3739, -1383, 7174, 1605, -4987, -136, 902], [902, 4611, -3889, -28777, 17007, 42815, -28004, -10121, 5837, 766]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -5, -32, 23, 49, -39, -13, 12, 1], [1, 6, 0, -37, -9, 72, 10, -52, -1, 13], [13, 66, -59, -416, 262, 628, -435, -159, 104, 12], [12, 73, 6, -443, -140, 850, 160, -591, -15, 116], [116, 592, -507, -3706, 2225, 5544, -3674, -1348, 801, 101], [101, 621, 87, -3739, -1383, 7174, 1605, -4987, -136, 902], [902, 4611, -3889, -28777, 17007, 42815, -28004, -10121, 5837, 766], [766, 4732, 781, -28401, -11159, 54541, 12941, -37962, -929, 6603]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -5, -32, 23, 49, -39, -13, 12, 1], [1, 6, 0, -37, -9, 72, 10, -52, -1, 13], [13, 66, -59, -416, 262, 628, -435, -159, 104, 12], [12, 73, 6, -443, -140, 850, 160, -591, -15, 116], [116, 592, -507, -3706, 2225, 5544, -3674, -1348, 801, 101], [101, 621, 87, -3739, -1383, 7174, 1605, -4987, -136, 902], [902, 4611, -3889, -28777, 17007, 42815, -28004, -10121, 5837, 766], [766, 4732, 781, -28401, -11159, 54541, 12941, -37962, -929, 6603], [6603, 33781, -28283, -210515, 123468, 312388, -202976, -72898, 41274, 5674]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp41 : Fact (Nat.Prime 41) := fact_iff.2 (by norm_num)
instance hp181 : Fact (Nat.Prime 181) := fact_iff.2 (by norm_num)
instance hp182101 : Fact (Nat.Prime 182101) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 0, 4]
  b' := [3, 2, 0, 0, 2]
  k := [1]
  f := [2, 1, -1, -4, 7, 11, -7, -1, 4, 1]
  g := [3, 0, 0, 2, 2, 1]
  h := [3, 0, 0, 2, 2, 1]
  a := [1, 2, 2, 0, 4]
  b := [3, 0, 0, 1, 3, 2, 1, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD41 : CertificateDedekindCriterionLists l 41 where
  n := 2
  a' := [40, 36, 15, 25, 40, 5, 29, 1]
  b' := [20, 18, 4, 8, 6, 8, 29, 2, 9]
  k := [39, 4, 27, 31, 11, 9, 34, 16, 1]
  f := [5, 2, 0, 8, 13, 13, 2, 6, 9, 1]
  g := [17, 5, 0, 30, 40, 37, 7, 21, 28, 1]
  h := [12, 1]
  a := [23, 17, 31, 32, 34, 37, 0, 17, 22]
  b := [15, 12, 36, 9, 39, 38, 19, 32, 19]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD181 : CertificateDedekindCriterionLists l 181 where
  n := 2
  a' := [91, 154, 68, 92, 73, 93, 128, 50]
  b' := [120, 125, 93, 34, 148, 59, 11, 20, 95]
  k := [178, 2, 73, 159, 78, 20, 11, 158, 1]
  f := [9, 2, 5, 1, 7, 8, 9, 8, 11, 1]
  g := [148, 19, 81, 12, 112, 117, 141, 120, 169, 1]
  h := [11, 1]
  a := [21, 31, 105, 9, 95, 172, 80, 11, 57]
  b := [77, 76, 69, 60, 47, 163, 93, 126, 124]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD182101 : CertificateDedekindCriterionLists l 182101 where
  n := 2
  a' := [172933, 131498, 88657, 54026, 52588, 137342, 53524, 143148]
  b' := [134210, 131354, 148414, 34265, 2835, 130170, 88581, 125439, 44795]
  k := [72208, 138778, 110364, 132714, 137220, 50549, 49295, 82171, 1]
  f := [39961, 2874, 29716, 56687, 122936, 110668, 33687, 96123, 31816, 1]
  g := [51604, 3711, 38374, 73203, 158754, 142911, 43501, 124129, 41085, 1]
  h := [141015, 1]
  a := [105386, 101003, 135825, 50494, 2029, 118054, 171151, 166833, 21177]
  b := [4004, 58203, 35079, 70813, 118070, 113290, 153222, 3, 160924]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 41, 181, 182101]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 41, 181, 182101]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp41.out
    exact hp181.out
    exact hp182101.out
  a := [49937300475, -357166841120, 258247351374, 1234403196834, -1183347784167, -466581482476, 519400615933, 46245380312, -55391332180]
  b := [-11338831616, -1181595483, 135385913327, -85976413706, -250264839442, 202295482569, 67239108224, -65270049503, -5178451353, 5539133218]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 41 T_ofList CD41
    exact satisfiesDedekindCriterion_of_certificate_lists T l 181 T_ofList CD181
    exact satisfiesDedekindCriterion_of_certificate_lists T l 182101 T_ofList CD182101

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

end VoightMaximalOrderD10R308

end TraceEuclidean
