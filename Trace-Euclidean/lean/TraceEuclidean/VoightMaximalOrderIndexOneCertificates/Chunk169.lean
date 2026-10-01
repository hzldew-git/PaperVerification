import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk165
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

namespace VoightMaximalOrderD10R17

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨968074628125, [1, -13, 20, 28, -46, -23, 34, 8, -10, -1, 1], 1⟩
local notation "l" => [1, -13, 20, 28, -46, -23, 34, 8, -10, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 13, -20, -28, 46, 23, -34, -8, 10, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 13, -20, -28, 46, 23, -34, -8, 10, 1], ![-1, 12, -7, -48, 18, 69, -11, -42, 2, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 13, -20, -28, 46, 23, -34, -8, 10, 1], ![-1, 12, -7, -48, 18, 69, -11, -42, 2, 11], ![-11, 142, -208, -315, 458, 271, -305, -99, 68, 13]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 13, -20, -28, 46, 23, -34, -8, 10, 1], ![-1, 12, -7, -48, 18, 69, -11, -42, 2, 11], ![-11, 142, -208, -315, 458, 271, -305, -99, 68, 13], ![-13, 158, -118, -572, 283, 757, -171, -409, 31, 81]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 13, -20, -28, 46, 23, -34, -8, 10, 1], ![-1, 12, -7, -48, 18, 69, -11, -42, 2, 11], ![-11, 142, -208, -315, 458, 271, -305, -99, 68, 13], ![-13, 158, -118, -572, 283, 757, -171, -409, 31, 81], ![-81, 1040, -1462, -2386, 3154, 2146, -1997, -819, 401, 112]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 13, -20, -28, 46, 23, -34, -8, 10, 1], ![-1, 12, -7, -48, 18, 69, -11, -42, 2, 11], ![-11, 142, -208, -315, 458, 271, -305, -99, 68, 13], ![-13, 158, -118, -572, 283, 757, -171, -409, 31, 81], ![-81, 1040, -1462, -2386, 3154, 2146, -1997, -819, 401, 112], ![-112, 1375, -1200, -4598, 2766, 5730, -1662, -2893, 301, 513]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 13, -20, -28, 46, 23, -34, -8, 10, 1], ![-1, 12, -7, -48, 18, 69, -11, -42, 2, 11], ![-11, 142, -208, -315, 458, 271, -305, -99, 68, 13], ![-13, 158, -118, -572, 283, 757, -171, -409, 31, 81], ![-81, 1040, -1462, -2386, 3154, 2146, -1997, -819, 401, 112], ![-112, 1375, -1200, -4598, 2766, 5730, -1662, -2893, 301, 513], ![-513, 6557, -8885, -15564, 19000, 14565, -11712, -5766, 2237, 814]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 13, -20, -28, 46, 23, -34, -8, 10, 1], ![-1, 12, -7, -48, 18, 69, -11, -42, 2, 11], ![-11, 142, -208, -315, 458, 271, -305, -99, 68, 13], ![-13, 158, -118, -572, 283, 757, -171, -409, 31, 81], ![-81, 1040, -1462, -2386, 3154, 2146, -1997, -819, 401, 112], ![-112, 1375, -1200, -4598, 2766, 5730, -1662, -2893, 301, 513], ![-513, 6557, -8885, -15564, 19000, 14565, -11712, -5766, 2237, 814], ![-814, 10069, -9723, -31677, 21880, 37722, -13111, -18224, 2374, 3051]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 13, -20, -28, 46, 23, -34, -8, 10, 1], ![-1, 12, -7, -48, 18, 69, -11, -42, 2, 11], ![-11, 142, -208, -315, 458, 271, -305, -99, 68, 13], ![-13, 158, -118, -572, 283, 757, -171, -409, 31, 81], ![-81, 1040, -1462, -2386, 3154, 2146, -1997, -819, 401, 112], ![-112, 1375, -1200, -4598, 2766, 5730, -1662, -2893, 301, 513], ![-513, 6557, -8885, -15564, 19000, 14565, -11712, -5766, 2237, 814], ![-814, 10069, -9723, -31677, 21880, 37722, -13111, -18224, 2374, 3051], ![-3051, 38849, -50951, -95151, 108669, 92053, -66012, -37519, 12286, 5425]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-81, -13, -11, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-81, -13, -11, -1, -1], [-112, -81, -13, -11, -1, -1]], ![[], [], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-81, -13, -11, -1, -1], [-112, -81, -13, -11, -1, -1], [-513, -112, -81, -13, -11, -1, -1]], ![[], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-81, -13, -11, -1, -1], [-112, -81, -13, -11, -1, -1], [-513, -112, -81, -13, -11, -1, -1], [-814, -513, -112, -81, -13, -11, -1, -1]], ![[], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-81, -13, -11, -1, -1], [-112, -81, -13, -11, -1, -1], [-513, -112, -81, -13, -11, -1, -1], [-814, -513, -112, -81, -13, -11, -1, -1], [-3051, -814, -513, -112, -81, -13, -11, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 13, -20, -28, 46, 23, -34, -8, 10, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 13, -20, -28, 46, 23, -34, -8, 10, 1], [-1, 12, -7, -48, 18, 69, -11, -42, 2, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 13, -20, -28, 46, 23, -34, -8, 10, 1], [-1, 12, -7, -48, 18, 69, -11, -42, 2, 11], [-11, 142, -208, -315, 458, 271, -305, -99, 68, 13]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 13, -20, -28, 46, 23, -34, -8, 10, 1], [-1, 12, -7, -48, 18, 69, -11, -42, 2, 11], [-11, 142, -208, -315, 458, 271, -305, -99, 68, 13], [-13, 158, -118, -572, 283, 757, -171, -409, 31, 81]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 13, -20, -28, 46, 23, -34, -8, 10, 1], [-1, 12, -7, -48, 18, 69, -11, -42, 2, 11], [-11, 142, -208, -315, 458, 271, -305, -99, 68, 13], [-13, 158, -118, -572, 283, 757, -171, -409, 31, 81], [-81, 1040, -1462, -2386, 3154, 2146, -1997, -819, 401, 112]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 13, -20, -28, 46, 23, -34, -8, 10, 1], [-1, 12, -7, -48, 18, 69, -11, -42, 2, 11], [-11, 142, -208, -315, 458, 271, -305, -99, 68, 13], [-13, 158, -118, -572, 283, 757, -171, -409, 31, 81], [-81, 1040, -1462, -2386, 3154, 2146, -1997, -819, 401, 112], [-112, 1375, -1200, -4598, 2766, 5730, -1662, -2893, 301, 513]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 13, -20, -28, 46, 23, -34, -8, 10, 1], [-1, 12, -7, -48, 18, 69, -11, -42, 2, 11], [-11, 142, -208, -315, 458, 271, -305, -99, 68, 13], [-13, 158, -118, -572, 283, 757, -171, -409, 31, 81], [-81, 1040, -1462, -2386, 3154, 2146, -1997, -819, 401, 112], [-112, 1375, -1200, -4598, 2766, 5730, -1662, -2893, 301, 513], [-513, 6557, -8885, -15564, 19000, 14565, -11712, -5766, 2237, 814]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 13, -20, -28, 46, 23, -34, -8, 10, 1], [-1, 12, -7, -48, 18, 69, -11, -42, 2, 11], [-11, 142, -208, -315, 458, 271, -305, -99, 68, 13], [-13, 158, -118, -572, 283, 757, -171, -409, 31, 81], [-81, 1040, -1462, -2386, 3154, 2146, -1997, -819, 401, 112], [-112, 1375, -1200, -4598, 2766, 5730, -1662, -2893, 301, 513], [-513, 6557, -8885, -15564, 19000, 14565, -11712, -5766, 2237, 814], [-814, 10069, -9723, -31677, 21880, 37722, -13111, -18224, 2374, 3051]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 13, -20, -28, 46, 23, -34, -8, 10, 1], [-1, 12, -7, -48, 18, 69, -11, -42, 2, 11], [-11, 142, -208, -315, 458, 271, -305, -99, 68, 13], [-13, 158, -118, -572, 283, 757, -171, -409, 31, 81], [-81, 1040, -1462, -2386, 3154, 2146, -1997, -819, 401, 112], [-112, 1375, -1200, -4598, 2766, 5730, -1662, -2893, 301, 513], [-513, 6557, -8885, -15564, 19000, 14565, -11712, -5766, 2237, 814], [-814, 10069, -9723, -31677, 21880, 37722, -13111, -18224, 2374, 3051], [-3051, 38849, -50951, -95151, 108669, 92053, -66012, -37519, 12286, 5425]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp28162171 : Fact (Nat.Prime 28162171) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 0, 3]
  b' := [3, 2, 4, 1, 4]
  k := [1]
  f := [3, 9, 4, 4, 19, 13, -1, 2, 4, 1]
  g := [4, 4, 3, 3, 2, 1]
  h := [4, 4, 3, 3, 2, 1]
  a := [2, 1, 0, 4, 3]
  b := [0, 1, 1, 1, 2, 4, 2, 0, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [10, 6, 2, 4, 1, 2, 8, 7]
  b' := [1, 5, 8, 5, 9, 8, 2, 1, 9]
  k := [3, 2, 5, 7, 5, 4, 6, 6, 1]
  f := [1, 3, -1, -1, 6, 3, -2, 1, 3, 1]
  g := [6, 7, 1, 8, 6, 2, 5, 7, 8, 1]
  h := [2, 1]
  a := [6, 5, 10, 3, 0, 3, 5, 2, 10]
  b := [1, 6, 8, 3, 5, 7, 6, 4, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD28162171 : CertificateDedekindCriterionLists l 28162171 where
  n := 2
  a' := [14058158, 4799897, 9056270, 10740958, 23570092, 8720792, 27169916, 13405966]
  b' := [5356203, 12904834, 11839085, 15608873, 15170428, 21348384, 2679567, 20434539, 20414359]
  k := [9009682, 23122677, 19385801, 23829649, 371079, 14989138, 15777642, 15455894, 1]
  f := [6288565, 5160083, 6135118, 5360403, 23604, 4243329, 4777108, 1664169, 4919926, 1]
  g := [27875932, 22873596, 27195729, 23761574, 104628, 18809816, 21175947, 7376920, 21809032, 1]
  h := [6353138, 1]
  a := [8542846, 21505823, 8030904, 5841224, 20751662, 8939112, 2847064, 2550317, 20086742]
  b := [3055112, 18713403, 798929, 22128908, 10624675, 3230729, 22076777, 24306477, 8075429]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 11, 28162171]
  exp := ![1, 1, 1]
  pdgood := [5, 11, 28162171]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp11.out
    exact hp28162171.out
  a := [186420891, -16076273234, 14222241274, 74516295364, -60172874783, -49073332228, 36680076433, 8647764786, -5780468840]
  b := [-104807578, -1745542149, 11408976048, -7512340398, -16312146275, 11809704241, 6919085653, -4789647983, -922581167, 578046884]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 28162171 T_ofList CD28162171

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

end VoightMaximalOrderD10R17

namespace VoightMaximalOrderD10R19

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨993530403125, [1, -10, 20, 21, -46, -18, 34, 7, -10, -1, 1], 1⟩
local notation "l" => [1, -10, 20, 21, -46, -18, 34, 7, -10, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -20, -21, 46, 18, -34, -7, 10, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -20, -21, 46, 18, -34, -7, 10, 1], ![-1, 9, -10, -41, 25, 64, -16, -41, 3, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -20, -21, 46, 18, -34, -7, 10, 1], ![-1, 9, -10, -41, 25, 64, -16, -41, 3, 11], ![-11, 109, -211, -241, 465, 223, -310, -93, 69, 14]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -20, -21, 46, 18, -34, -7, 10, 1], ![-1, 9, -10, -41, 25, 64, -16, -41, 3, 11], ![-11, 109, -211, -241, 465, 223, -310, -93, 69, 14], ![-14, 129, -171, -505, 403, 717, -253, -408, 47, 83]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -20, -21, 46, 18, -34, -7, 10, 1], ![-1, 9, -10, -41, 25, 64, -16, -41, 3, 11], ![-11, 109, -211, -241, 465, 223, -310, -93, 69, 14], ![-14, 129, -171, -505, 403, 717, -253, -408, 47, 83], ![-83, 816, -1531, -1914, 3313, 1897, -2105, -834, 422, 130]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -20, -21, 46, 18, -34, -7, 10, 1], ![-1, 9, -10, -41, 25, 64, -16, -41, 3, 11], ![-11, 109, -211, -241, 465, 223, -310, -93, 69, 14], ![-14, 129, -171, -505, 403, 717, -253, -408, 47, 83], ![-83, 816, -1531, -1914, 3313, 1897, -2105, -834, 422, 130], ![-130, 1217, -1784, -4261, 4066, 5653, -2523, -3015, 466, 552]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -20, -21, 46, 18, -34, -7, 10, 1], ![-1, 9, -10, -41, 25, 64, -16, -41, 3, 11], ![-11, 109, -211, -241, 465, 223, -310, -93, 69, 14], ![-14, 129, -171, -505, 403, 717, -253, -408, 47, 83], ![-83, 816, -1531, -1914, 3313, 1897, -2105, -834, 422, 130], ![-130, 1217, -1784, -4261, 4066, 5653, -2523, -3015, 466, 552], ![-552, 5390, -9823, -13376, 21131, 14002, -13115, -6387, 2505, 1018]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -20, -21, 46, 18, -34, -7, 10, 1], ![-1, 9, -10, -41, 25, 64, -16, -41, 3, 11], ![-11, 109, -211, -241, 465, 223, -310, -93, 69, 14], ![-14, 129, -171, -505, 403, 717, -253, -408, 47, 83], ![-83, 816, -1531, -1914, 3313, 1897, -2105, -834, 422, 130], ![-130, 1217, -1784, -4261, 4066, 5653, -2523, -3015, 466, 552], ![-552, 5390, -9823, -13376, 21131, 14002, -13115, -6387, 2505, 1018], ![-1018, 9628, -14970, -31201, 33452, 39455, -20610, -20241, 3793, 3523]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -20, -21, 46, 18, -34, -7, 10, 1], ![-1, 9, -10, -41, 25, 64, -16, -41, 3, 11], ![-11, 109, -211, -241, 465, 223, -310, -93, 69, 14], ![-14, 129, -171, -505, 403, 717, -253, -408, 47, 83], ![-83, 816, -1531, -1914, 3313, 1897, -2105, -834, 422, 130], ![-130, 1217, -1784, -4261, 4066, 5653, -2523, -3015, 466, 552], ![-552, 5390, -9823, -13376, 21131, 14002, -13115, -6387, 2505, 1018], ![-1018, 9628, -14970, -31201, 33452, 39455, -20610, -20241, 3793, 3523], ![-3523, 34212, -60832, -88953, 130857, 96866, -80327, -45271, 14989, 7316]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-14, -11, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-14, -11, -1, -1], [-83, -14, -11, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-14, -11, -1, -1], [-83, -14, -11, -1, -1], [-130, -83, -14, -11, -1, -1]], ![[], [], [], [-1], [-1, -1], [-11, -1, -1], [-14, -11, -1, -1], [-83, -14, -11, -1, -1], [-130, -83, -14, -11, -1, -1], [-552, -130, -83, -14, -11, -1, -1]], ![[], [], [-1], [-1, -1], [-11, -1, -1], [-14, -11, -1, -1], [-83, -14, -11, -1, -1], [-130, -83, -14, -11, -1, -1], [-552, -130, -83, -14, -11, -1, -1], [-1018, -552, -130, -83, -14, -11, -1, -1]], ![[], [-1], [-1, -1], [-11, -1, -1], [-14, -11, -1, -1], [-83, -14, -11, -1, -1], [-130, -83, -14, -11, -1, -1], [-552, -130, -83, -14, -11, -1, -1], [-1018, -552, -130, -83, -14, -11, -1, -1], [-3523, -1018, -552, -130, -83, -14, -11, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -20, -21, 46, 18, -34, -7, 10, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -20, -21, 46, 18, -34, -7, 10, 1], [-1, 9, -10, -41, 25, 64, -16, -41, 3, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -20, -21, 46, 18, -34, -7, 10, 1], [-1, 9, -10, -41, 25, 64, -16, -41, 3, 11], [-11, 109, -211, -241, 465, 223, -310, -93, 69, 14]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -20, -21, 46, 18, -34, -7, 10, 1], [-1, 9, -10, -41, 25, 64, -16, -41, 3, 11], [-11, 109, -211, -241, 465, 223, -310, -93, 69, 14], [-14, 129, -171, -505, 403, 717, -253, -408, 47, 83]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -20, -21, 46, 18, -34, -7, 10, 1], [-1, 9, -10, -41, 25, 64, -16, -41, 3, 11], [-11, 109, -211, -241, 465, 223, -310, -93, 69, 14], [-14, 129, -171, -505, 403, 717, -253, -408, 47, 83], [-83, 816, -1531, -1914, 3313, 1897, -2105, -834, 422, 130]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -20, -21, 46, 18, -34, -7, 10, 1], [-1, 9, -10, -41, 25, 64, -16, -41, 3, 11], [-11, 109, -211, -241, 465, 223, -310, -93, 69, 14], [-14, 129, -171, -505, 403, 717, -253, -408, 47, 83], [-83, 816, -1531, -1914, 3313, 1897, -2105, -834, 422, 130], [-130, 1217, -1784, -4261, 4066, 5653, -2523, -3015, 466, 552]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -20, -21, 46, 18, -34, -7, 10, 1], [-1, 9, -10, -41, 25, 64, -16, -41, 3, 11], [-11, 109, -211, -241, 465, 223, -310, -93, 69, 14], [-14, 129, -171, -505, 403, 717, -253, -408, 47, 83], [-83, 816, -1531, -1914, 3313, 1897, -2105, -834, 422, 130], [-130, 1217, -1784, -4261, 4066, 5653, -2523, -3015, 466, 552], [-552, 5390, -9823, -13376, 21131, 14002, -13115, -6387, 2505, 1018]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -20, -21, 46, 18, -34, -7, 10, 1], [-1, 9, -10, -41, 25, 64, -16, -41, 3, 11], [-11, 109, -211, -241, 465, 223, -310, -93, 69, 14], [-14, 129, -171, -505, 403, 717, -253, -408, 47, 83], [-83, 816, -1531, -1914, 3313, 1897, -2105, -834, 422, 130], [-130, 1217, -1784, -4261, 4066, 5653, -2523, -3015, 466, 552], [-552, 5390, -9823, -13376, 21131, 14002, -13115, -6387, 2505, 1018], [-1018, 9628, -14970, -31201, 33452, 39455, -20610, -20241, 3793, 3523]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -20, -21, 46, 18, -34, -7, 10, 1], [-1, 9, -10, -41, 25, 64, -16, -41, 3, 11], [-11, 109, -211, -241, 465, 223, -310, -93, 69, 14], [-14, 129, -171, -505, 403, 717, -253, -408, 47, 83], [-83, 816, -1531, -1914, 3313, 1897, -2105, -834, 422, 130], [-130, 1217, -1784, -4261, 4066, 5653, -2523, -3015, 466, 552], [-552, 5390, -9823, -13376, 21131, 14002, -13115, -6387, 2505, 1018], [-1018, 9628, -14970, -31201, 33452, 39455, -20610, -20241, 3793, 3523], [-3523, 34212, -60832, -88953, 130857, 96866, -80327, -45271, 14989, 7316]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp13 : Fact (Nat.Prime 13) := fact_iff.2 (by norm_num)
instance hp1881241 : Fact (Nat.Prime 1881241) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 0, 2]
  b' := [2, 4, 4, 4, 1]
  k := [1]
  f := [0, 2, -4, -3, 10, 4, -5, 1, 4, 1]
  g := [1, 0, 0, 3, 2, 1]
  h := [1, 0, 0, 3, 2, 1]
  a := [4, 3, 3, 0, 2]
  b := [1, 2, 0, 0, 3, 4, 4, 1, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD13 : CertificateDedekindCriterionLists l 13 where
  n := 2
  a' := [6, 6, 12, 8, 8, 5, 7]
  b' := [12, 6, 5, 11, 8, 12, 11, 4]
  k := [3, 6, 0, 8, 3, 2, 1]
  f := [3, 10, 8, 8, 11, 7, 7, 9, 5, 1]
  g := [4, 10, 7, 8, 5, 4, 10, 7, 1]
  h := [10, 5, 1]
  a := [1, 11, 12, 4, 6, 5, 12, 10]
  b := [6, 10, 4, 1, 7, 8, 6, 8, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1881241 : CertificateDedekindCriterionLists l 1881241 where
  n := 2
  a' := [1604557, 1427301, 1310567, 319507, 601996, 854992, 479008, 7205]
  b' := [1429671, 143216, 343990, 1427189, 50869, 1663898, 1587759, 655101, 417253]
  k := [1603818, 1793335, 709142, 1428121, 886242, 937073, 1020724, 485652, 1]
  f := [459113, 396331, 310524, 85021, 396168, 435902, 462229, 445075, 438967, 1]
  g := [1237761, 1068500, 837166, 229214, 1068062, 1175183, 1246160, 1199913, 1183446, 1]
  h := [697794, 1]
  a := [563174, 1430082, 1319929, 288478, 1409194, 330994, 641457, 206450, 1196629]
  b := [1844815, 250683, 835728, 1654454, 685623, 757183, 667069, 1398050, 684612]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 13, 1881241]
  exp := ![1, 1, 1]
  pdgood := [5, 13, 1881241]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp13.out
    exact hp1881241.out
  a := [-1143246045, -639836560, 5506616773, 2063224146, -6777434540, -1581328254, 2872123953, 344048492, -380963180]
  b := [-126552671, 573051705, 398931140, -1446264725, -489429074, 1162079414, 236626239, -363393215, -38214481, 38096318]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 13 T_ofList CD13
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1881241 T_ofList CD1881241

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

end VoightMaximalOrderD10R19

namespace VoightMaximalOrderD10R21

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1056719528125, [-1, -7, 10, 41, -36, -43, 35, 13, -11, -1, 1], 1⟩
local notation "l" => [-1, -7, 10, 41, -36, -43, 35, 13, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -10, -41, 36, 43, -35, -13, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -10, -41, 36, 43, -35, -13, 11, 1], ![1, 8, -3, -51, -5, 79, 8, -48, -2, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -10, -41, 36, 43, -35, -13, 11, 1], ![1, 8, -3, -51, -5, 79, 8, -48, -2, 12], ![12, 85, -112, -495, 381, 511, -341, -148, 84, 10]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -10, -41, 36, 43, -35, -13, 11, 1], ![1, 8, -3, -51, -5, 79, 8, -48, -2, 12], ![12, 85, -112, -495, 381, 511, -341, -148, 84, 10], ![10, 82, -15, -522, -135, 811, 161, -471, -38, 94]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -10, -41, 36, 43, -35, -13, 11, 1], ![1, 8, -3, -51, -5, 79, 8, -48, -2, 12], ![12, 85, -112, -495, 381, 511, -341, -148, 84, 10], ![10, 82, -15, -522, -135, 811, 161, -471, -38, 94], ![94, 668, -858, -3869, 2862, 3907, -2479, -1061, 563, 56]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -10, -41, 36, 43, -35, -13, 11, 1], ![1, 8, -3, -51, -5, 79, 8, -48, -2, 12], ![12, 85, -112, -495, 381, 511, -341, -148, 84, 10], ![10, 82, -15, -522, -135, 811, 161, -471, -38, 94], ![94, 668, -858, -3869, 2862, 3907, -2479, -1061, 563, 56], ![56, 486, 108, -3154, -1853, 5270, 1947, -3207, -445, 619]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -10, -41, 36, 43, -35, -13, 11, 1], ![1, 8, -3, -51, -5, 79, 8, -48, -2, 12], ![12, 85, -112, -495, 381, 511, -341, -148, 84, 10], ![10, 82, -15, -522, -135, 811, 161, -471, -38, 94], ![94, 668, -858, -3869, 2862, 3907, -2479, -1061, 563, 56], ![56, 486, 108, -3154, -1853, 5270, 1947, -3207, -445, 619], ![619, 4389, -5704, -25271, 19130, 24764, -16395, -6100, 3602, 174]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -10, -41, 36, 43, -35, -13, 11, 1], ![1, 8, -3, -51, -5, 79, 8, -48, -2, 12], ![12, 85, -112, -495, 381, 511, -341, -148, 84, 10], ![10, 82, -15, -522, -135, 811, 161, -471, -38, 94], ![94, 668, -858, -3869, 2862, 3907, -2479, -1061, 563, 56], ![56, 486, 108, -3154, -1853, 5270, 1947, -3207, -445, 619], ![619, 4389, -5704, -25271, 19130, 24764, -16395, -6100, 3602, 174], ![174, 1837, 2649, -12838, -19007, 26612, 18674, -18657, -4186, 3776]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 7, -10, -41, 36, 43, -35, -13, 11, 1], ![1, 8, -3, -51, -5, 79, 8, -48, -2, 12], ![12, 85, -112, -495, 381, 511, -341, -148, 84, 10], ![10, 82, -15, -522, -135, 811, 161, -471, -38, 94], ![94, 668, -858, -3869, 2862, 3907, -2479, -1061, 563, 56], ![56, 486, 108, -3154, -1853, 5270, 1947, -3207, -445, 619], ![619, 4389, -5704, -25271, 19130, 24764, -16395, -6100, 3602, 174], ![174, 1837, 2649, -12838, -19007, 26612, 18674, -18657, -4186, 3776], ![3776, 26606, -35923, -152167, 123098, 143361, -105548, -30414, 22879, -410]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-10, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-10, -12, -1, -1], [-94, -10, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-10, -12, -1, -1], [-94, -10, -12, -1, -1], [-56, -94, -10, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-10, -12, -1, -1], [-94, -10, -12, -1, -1], [-56, -94, -10, -12, -1, -1], [-619, -56, -94, -10, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-10, -12, -1, -1], [-94, -10, -12, -1, -1], [-56, -94, -10, -12, -1, -1], [-619, -56, -94, -10, -12, -1, -1], [-174, -619, -56, -94, -10, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-10, -12, -1, -1], [-94, -10, -12, -1, -1], [-56, -94, -10, -12, -1, -1], [-619, -56, -94, -10, -12, -1, -1], [-174, -619, -56, -94, -10, -12, -1, -1], [-3776, -174, -619, -56, -94, -10, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -10, -41, 36, 43, -35, -13, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -10, -41, 36, 43, -35, -13, 11, 1], [1, 8, -3, -51, -5, 79, 8, -48, -2, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -10, -41, 36, 43, -35, -13, 11, 1], [1, 8, -3, -51, -5, 79, 8, -48, -2, 12], [12, 85, -112, -495, 381, 511, -341, -148, 84, 10]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -10, -41, 36, 43, -35, -13, 11, 1], [1, 8, -3, -51, -5, 79, 8, -48, -2, 12], [12, 85, -112, -495, 381, 511, -341, -148, 84, 10], [10, 82, -15, -522, -135, 811, 161, -471, -38, 94]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -10, -41, 36, 43, -35, -13, 11, 1], [1, 8, -3, -51, -5, 79, 8, -48, -2, 12], [12, 85, -112, -495, 381, 511, -341, -148, 84, 10], [10, 82, -15, -522, -135, 811, 161, -471, -38, 94], [94, 668, -858, -3869, 2862, 3907, -2479, -1061, 563, 56]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -10, -41, 36, 43, -35, -13, 11, 1], [1, 8, -3, -51, -5, 79, 8, -48, -2, 12], [12, 85, -112, -495, 381, 511, -341, -148, 84, 10], [10, 82, -15, -522, -135, 811, 161, -471, -38, 94], [94, 668, -858, -3869, 2862, 3907, -2479, -1061, 563, 56], [56, 486, 108, -3154, -1853, 5270, 1947, -3207, -445, 619]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -10, -41, 36, 43, -35, -13, 11, 1], [1, 8, -3, -51, -5, 79, 8, -48, -2, 12], [12, 85, -112, -495, 381, 511, -341, -148, 84, 10], [10, 82, -15, -522, -135, 811, 161, -471, -38, 94], [94, 668, -858, -3869, 2862, 3907, -2479, -1061, 563, 56], [56, 486, 108, -3154, -1853, 5270, 1947, -3207, -445, 619], [619, 4389, -5704, -25271, 19130, 24764, -16395, -6100, 3602, 174]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -10, -41, 36, 43, -35, -13, 11, 1], [1, 8, -3, -51, -5, 79, 8, -48, -2, 12], [12, 85, -112, -495, 381, 511, -341, -148, 84, 10], [10, 82, -15, -522, -135, 811, 161, -471, -38, 94], [94, 668, -858, -3869, 2862, 3907, -2479, -1061, 563, 56], [56, 486, 108, -3154, -1853, 5270, 1947, -3207, -445, 619], [619, 4389, -5704, -25271, 19130, 24764, -16395, -6100, 3602, 174], [174, 1837, 2649, -12838, -19007, 26612, 18674, -18657, -4186, 3776]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 7, -10, -41, 36, 43, -35, -13, 11, 1], [1, 8, -3, -51, -5, 79, 8, -48, -2, 12], [12, 85, -112, -495, 381, 511, -341, -148, 84, 10], [10, 82, -15, -522, -135, 811, 161, -471, -38, 94], [94, 668, -858, -3869, 2862, 3907, -2479, -1061, 563, 56], [56, 486, 108, -3154, -1853, 5270, 1947, -3207, -445, 619], [619, 4389, -5704, -25271, 19130, 24764, -16395, -6100, 3602, 174], [174, 1837, 2649, -12838, -19007, 26612, 18674, -18657, -4186, 3776], [3776, 26606, -35923, -152167, 123098, 143361, -105548, -30414, 22879, -410]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp89 : Fact (Nat.Prime 89) := fact_iff.2 (by norm_num)
instance hp1061 : Fact (Nat.Prime 1061) := fact_iff.2 (by norm_num)
instance hp3581 : Fact (Nat.Prime 3581) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 4, 1]
  b' := [4, 1, 3, 3, 3]
  k := [1]
  f := [1, 3, 2, -5, 12, 11, -3, -1, 3, 1]
  g := [2, 2, 4, 0, 2, 1]
  h := [2, 2, 4, 0, 2, 1]
  a := [0, 4, 2, 0, 3]
  b := [3, 0, 2, 1, 1, 2, 2, 2, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD89 : CertificateDedekindCriterionLists l 89 where
  n := 2
  a' := [43, 67, 11, 28, 0, 38, 40, 71]
  b' := [59, 54, 48, 41, 75, 7, 10, 56, 2]
  k := [42, 41, 82, 57, 80, 14, 85, 11, 1]
  f := [14, 59, 78, 7, 21, 80, 36, 18, 5, 1]
  g := [15, 63, 83, 7, 22, 85, 38, 19, 5, 1]
  h := [83, 1]
  a := [53, 26, 23, 64, 80, 39, 32, 75, 7]
  b := [4, 59, 19, 59, 1, 15, 64, 14, 82]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1061 : CertificateDedekindCriterionLists l 1061 where
  n := 2
  a' := [458, 367, 267, 575, 536, 201, 411, 1043]
  b' := [413, 54, 530, 1037, 65, 845, 899, 108, 2]
  k := [219, 514, 639, 560, 497, 879, 944, 323, 1]
  f := [505, 653, 826, 89, 578, 232, 623, 515, 137, 1]
  g := [596, 770, 974, 104, 682, 273, 735, 607, 161, 1]
  h := [899, 1]
  a := [19, 29, 1043, 669, 1026, 733, 750, 104, 265]
  b := [137, 714, 340, 678, 169, 904, 567, 951, 796]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3581 : CertificateDedekindCriterionLists l 3581 where
  n := 2
  a' := [2862, 1324, 335, 3093, 1136, 473, 3241, 736]
  b' := [1577, 313, 3554, 2867, 3315, 1826, 3514, 2095, 714]
  k := [498, 3493, 3067, 3459, 702, 3381, 367, 3353, 1]
  f := [1493, 667, 1303, 1885, 412, 1632, 146, 1668, 892, 1]
  g := [2808, 1253, 2450, 3544, 773, 3069, 273, 3137, 1676, 1]
  h := [1904, 1]
  a := [1913, 2073, 766, 1338, 2603, 2944, 3466, 2419, 1320]
  b := [1814, 3059, 579, 776, 2970, 1838, 2491, 1133, 2261]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 89, 1061, 3581]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 89, 1061, 3581]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp89.out
    exact hp1061.out
    exact hp3581.out
  a := [-77611835771, 174101163500, 1466213453242, -817841271746, -2832777351028, 844819111534, 1460392404391, -213127834180, -212372896900]
  b := [10845869218, 83728438751, -64632752374, -491798397294, 139631575290, 553598778298, -98317700324, -196803912171, 19189054449, 21237289690]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 89 T_ofList CD89
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1061 T_ofList CD1061
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3581 T_ofList CD3581

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

end VoightMaximalOrderD10R21

namespace VoightMaximalOrderD10R23

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨1086015136753, [-1, -3, 8, 22, -18, -32, 19, 15, -8, -2, 1], 1⟩
local notation "l" => [-1, -3, 8, 22, -18, -32, 19, 15, -8, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -8, -22, 18, 32, -19, -15, 8, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -8, -22, 18, 32, -19, -15, 8, 2], ![2, 7, -13, -52, 14, 82, -6, -49, 1, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -8, -22, 18, 32, -19, -15, 8, 2], ![2, 7, -13, -52, 14, 82, -6, -49, 1, 12], ![12, 38, -89, -277, 164, 398, -146, -186, 47, 25]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -8, -22, 18, 32, -19, -15, 8, 2], ![2, 7, -13, -52, 14, 82, -6, -49, 1, 12], ![12, 38, -89, -277, 164, 398, -146, -186, 47, 25], ![25, 87, -162, -639, 173, 964, -77, -521, 14, 97]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -8, -22, 18, 32, -19, -15, 8, 2], ![2, 7, -13, -52, 14, 82, -6, -49, 1, 12], ![12, 38, -89, -277, 164, 398, -146, -186, 47, 25], ![25, 87, -162, -639, 173, 964, -77, -521, 14, 97], ![97, 316, -689, -2296, 1107, 3277, -879, -1532, 255, 208]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -8, -22, 18, 32, -19, -15, 8, 2], ![2, 7, -13, -52, 14, 82, -6, -49, 1, 12], ![12, 38, -89, -277, 164, 398, -146, -186, 47, 25], ![25, 87, -162, -639, 173, 964, -77, -521, 14, 97], ![97, 316, -689, -2296, 1107, 3277, -879, -1532, 255, 208], ![208, 721, -1348, -5265, 1448, 7763, -675, -3999, 132, 671]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -8, -22, 18, 32, -19, -15, 8, 2], ![2, 7, -13, -52, 14, 82, -6, -49, 1, 12], ![12, 38, -89, -277, 164, 398, -146, -186, 47, 25], ![25, 87, -162, -639, 173, 964, -77, -521, 14, 97], ![97, 316, -689, -2296, 1107, 3277, -879, -1532, 255, 208], ![208, 721, -1348, -5265, 1448, 7763, -675, -3999, 132, 671], ![671, 2221, -4647, -16110, 6813, 22920, -4986, -10740, 1369, 1474]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -8, -22, 18, 32, -19, -15, 8, 2], ![2, 7, -13, -52, 14, 82, -6, -49, 1, 12], ![12, 38, -89, -277, 164, 398, -146, -186, 47, 25], ![25, 87, -162, -639, 173, 964, -77, -521, 14, 97], ![97, 316, -689, -2296, 1107, 3277, -879, -1532, 255, 208], ![208, 721, -1348, -5265, 1448, 7763, -675, -3999, 132, 671], ![671, 2221, -4647, -16110, 6813, 22920, -4986, -10740, 1369, 1474], ![1474, 5093, -9571, -37075, 10422, 53981, -5086, -27096, 1052, 4317]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -8, -22, 18, 32, -19, -15, 8, 2], ![2, 7, -13, -52, 14, 82, -6, -49, 1, 12], ![12, 38, -89, -277, 164, 398, -146, -186, 47, 25], ![25, 87, -162, -639, 173, 964, -77, -521, 14, 97], ![97, 316, -689, -2296, 1107, 3277, -879, -1532, 255, 208], ![208, 721, -1348, -5265, 1448, 7763, -675, -3999, 132, 671], ![671, 2221, -4647, -16110, 6813, 22920, -4986, -10740, 1369, 1474], ![1474, 5093, -9571, -37075, 10422, 53981, -5086, -27096, 1052, 4317], ![4317, 14425, -29443, -104545, 40631, 148566, -28042, -69841, 7440, 9686]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-12, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-12, -2, -1], [-25, -12, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-12, -2, -1], [-25, -12, -2, -1], [-97, -25, -12, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-12, -2, -1], [-25, -12, -2, -1], [-97, -25, -12, -2, -1], [-208, -97, -25, -12, -2, -1]], ![[], [], [], [-1], [-2, -1], [-12, -2, -1], [-25, -12, -2, -1], [-97, -25, -12, -2, -1], [-208, -97, -25, -12, -2, -1], [-671, -208, -97, -25, -12, -2, -1]], ![[], [], [-1], [-2, -1], [-12, -2, -1], [-25, -12, -2, -1], [-97, -25, -12, -2, -1], [-208, -97, -25, -12, -2, -1], [-671, -208, -97, -25, -12, -2, -1], [-1474, -671, -208, -97, -25, -12, -2, -1]], ![[], [-1], [-2, -1], [-12, -2, -1], [-25, -12, -2, -1], [-97, -25, -12, -2, -1], [-208, -97, -25, -12, -2, -1], [-671, -208, -97, -25, -12, -2, -1], [-1474, -671, -208, -97, -25, -12, -2, -1], [-4317, -1474, -671, -208, -97, -25, -12, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -8, -22, 18, 32, -19, -15, 8, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -8, -22, 18, 32, -19, -15, 8, 2], [2, 7, -13, -52, 14, 82, -6, -49, 1, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -8, -22, 18, 32, -19, -15, 8, 2], [2, 7, -13, -52, 14, 82, -6, -49, 1, 12], [12, 38, -89, -277, 164, 398, -146, -186, 47, 25]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -8, -22, 18, 32, -19, -15, 8, 2], [2, 7, -13, -52, 14, 82, -6, -49, 1, 12], [12, 38, -89, -277, 164, 398, -146, -186, 47, 25], [25, 87, -162, -639, 173, 964, -77, -521, 14, 97]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -8, -22, 18, 32, -19, -15, 8, 2], [2, 7, -13, -52, 14, 82, -6, -49, 1, 12], [12, 38, -89, -277, 164, 398, -146, -186, 47, 25], [25, 87, -162, -639, 173, 964, -77, -521, 14, 97], [97, 316, -689, -2296, 1107, 3277, -879, -1532, 255, 208]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -8, -22, 18, 32, -19, -15, 8, 2], [2, 7, -13, -52, 14, 82, -6, -49, 1, 12], [12, 38, -89, -277, 164, 398, -146, -186, 47, 25], [25, 87, -162, -639, 173, 964, -77, -521, 14, 97], [97, 316, -689, -2296, 1107, 3277, -879, -1532, 255, 208], [208, 721, -1348, -5265, 1448, 7763, -675, -3999, 132, 671]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -8, -22, 18, 32, -19, -15, 8, 2], [2, 7, -13, -52, 14, 82, -6, -49, 1, 12], [12, 38, -89, -277, 164, 398, -146, -186, 47, 25], [25, 87, -162, -639, 173, 964, -77, -521, 14, 97], [97, 316, -689, -2296, 1107, 3277, -879, -1532, 255, 208], [208, 721, -1348, -5265, 1448, 7763, -675, -3999, 132, 671], [671, 2221, -4647, -16110, 6813, 22920, -4986, -10740, 1369, 1474]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -8, -22, 18, 32, -19, -15, 8, 2], [2, 7, -13, -52, 14, 82, -6, -49, 1, 12], [12, 38, -89, -277, 164, 398, -146, -186, 47, 25], [25, 87, -162, -639, 173, 964, -77, -521, 14, 97], [97, 316, -689, -2296, 1107, 3277, -879, -1532, 255, 208], [208, 721, -1348, -5265, 1448, 7763, -675, -3999, 132, 671], [671, 2221, -4647, -16110, 6813, 22920, -4986, -10740, 1369, 1474], [1474, 5093, -9571, -37075, 10422, 53981, -5086, -27096, 1052, 4317]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -8, -22, 18, 32, -19, -15, 8, 2], [2, 7, -13, -52, 14, 82, -6, -49, 1, 12], [12, 38, -89, -277, 164, 398, -146, -186, 47, 25], [25, 87, -162, -639, 173, 964, -77, -521, 14, 97], [97, 316, -689, -2296, 1107, 3277, -879, -1532, 255, 208], [208, 721, -1348, -5265, 1448, 7763, -675, -3999, 132, 671], [671, 2221, -4647, -16110, 6813, 22920, -4986, -10740, 1369, 1474], [1474, 5093, -9571, -37075, 10422, 53981, -5086, -27096, 1052, 4317], [4317, 14425, -29443, -104545, 40631, 148566, -28042, -69841, 7440, 9686]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp43 : Fact (Nat.Prime 43) := fact_iff.2 (by norm_num)
instance hp4583 : Fact (Nat.Prime 4583) := fact_iff.2 (by norm_num)
instance hp128159 : Fact (Nat.Prime 128159) := fact_iff.2 (by norm_num)

def CD43 : CertificateDedekindCriterionLists l 43 where
  n := 3
  a' := [37, 1, 16, 20, 12, 1, 39]
  b' := [6, 39, 33, 20, 11, 17, 34, 22]
  k := [16, 16, 14, 30, 18, 13, 23, 35, 9, 28, 23, 38, 35, 6, 1]
  f := [21, 20, 28, 11, 8, 31, 15, 31, 9, 1]
  g := [22, 15, 25, 5, 6, 30, 8, 30, 1]
  h := [41, 11, 1]
  a := [20, 31, 17, 28, 37, 4, 10, 13]
  b := [22, 33, 39, 23, 7, 23, 16, 5, 30]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD4583 : CertificateDedekindCriterionLists l 4583 where
  n := 2
  a' := [2964, 3516, 2569, 716, 2103, 3888, 502, 182]
  b' := [3820, 3209, 3343, 1356, 4109, 1177, 1024, 569, 489]
  k := [2160, 591, 1399, 3468, 1202, 3697, 598, 2518, 1]
  f := [509, 3284, 1673, 2829, 971, 2823, 1327, 2855, 913, 1]
  g := [702, 4529, 2306, 3901, 1338, 3893, 1829, 3937, 1258, 1]
  h := [3323, 1]
  a := [3764, 2206, 2091, 216, 716, 4490, 2464, 287, 3717]
  b := [1090, 1245, 1725, 3728, 3703, 1338, 3641, 3421, 866]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD128159 : CertificateDedekindCriterionLists l 128159 where
  n := 2
  a' := [29058, 103981, 48704, 117140, 80830, 77124, 59694, 19693]
  b' := [63243, 108332, 74491, 112684, 22566, 9404, 29127, 19780, 111731]
  k := [63010, 9851, 44497, 33108, 54914, 27481, 56231, 59325, 1]
  f := [27359, 30741, 12545, 7454, 32418, 7410, 19517, 22666, 25174, 1]
  g := [101880, 114471, 46712, 27756, 120718, 27590, 72677, 84402, 93741, 1]
  h := [34416, 1]
  a := [89509, 18655, 63012, 90734, 51408, 102329, 80586, 60152, 44013]
  b := [54597, 27122, 56045, 74451, 101091, 55926, 22276, 19246, 84146]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![43, 4583, 128159]
  exp := ![1, 1, 1]
  pdgood := [43, 4583, 128159]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp43.out
    exact hp4583.out
    exact hp128159.out
  a := [910402874624, -7606603891622, 925620920931, 20807051734278, -8323388445718, -14191809932242, 6622293299452, 2458352125528, -1167278641160]
  b := [-311886346865, -38262094030, 2660240451119, -637838800705, -4132733839150, 1525501404674, 1997511693669, -841848901102, -269180785376, 116727864116]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 43 T_ofList CD43
    exact satisfiesDedekindCriterion_of_certificate_lists T l 4583 T_ofList CD4583
    exact satisfiesDedekindCriterion_of_certificate_lists T l 128159 T_ofList CD128159

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

end VoightMaximalOrderD10R23

end TraceEuclidean
