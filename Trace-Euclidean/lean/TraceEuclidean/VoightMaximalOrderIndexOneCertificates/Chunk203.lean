import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk199
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

namespace VoightMaximalOrderD10R375

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4729783590625, [1, -4, -10, 36, 19, -51, -5, 25, -3, -4, 1], 1⟩
local notation "l" => [1, -4, -10, 36, 19, -51, -5, 25, -3, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 10, -36, -19, 51, 5, -25, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 10, -36, -19, 51, 5, -25, 3, 4], ![-4, 15, 44, -134, -112, 185, 71, -95, -13, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 10, -36, -19, 51, 5, -25, 3, 4], ![-4, 15, 44, -134, -112, 185, 71, -95, -13, 19], ![-19, 72, 205, -640, -495, 857, 280, -404, -38, 63]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 10, -36, -19, 51, 5, -25, 3, 4], ![-4, 15, 44, -134, -112, 185, 71, -95, -13, 19], ![-19, 72, 205, -640, -495, 857, 280, -404, -38, 63], ![-63, 233, 702, -2063, -1837, 2718, 1172, -1295, -215, 214]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 10, -36, -19, 51, 5, -25, 3, 4], ![-4, 15, 44, -134, -112, 185, 71, -95, -13, 19], ![-19, 72, 205, -640, -495, 857, 280, -404, -38, 63], ![-63, 233, 702, -2063, -1837, 2718, 1172, -1295, -215, 214], ![-214, 793, 2373, -7002, -6129, 9077, 3788, -4178, -653, 641]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 10, -36, -19, 51, 5, -25, 3, 4], ![-4, 15, 44, -134, -112, 185, 71, -95, -13, 19], ![-19, 72, 205, -640, -495, 857, 280, -404, -38, 63], ![-63, 233, 702, -2063, -1837, 2718, 1172, -1295, -215, 214], ![-214, 793, 2373, -7002, -6129, 9077, 3788, -4178, -653, 641], ![-641, 2350, 7203, -20703, -19181, 26562, 12282, -12237, -2255, 1911]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 10, -36, -19, 51, 5, -25, 3, 4], ![-4, 15, 44, -134, -112, 185, 71, -95, -13, 19], ![-19, 72, 205, -640, -495, 857, 280, -404, -38, 63], ![-63, 233, 702, -2063, -1837, 2718, 1172, -1295, -215, 214], ![-214, 793, 2373, -7002, -6129, 9077, 3788, -4178, -653, 641], ![-641, 2350, 7203, -20703, -19181, 26562, 12282, -12237, -2255, 1911], ![-1911, 7003, 21460, -61593, -57012, 78280, 36117, -35493, -6504, 5389]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 10, -36, -19, 51, 5, -25, 3, 4], ![-4, 15, 44, -134, -112, 185, 71, -95, -13, 19], ![-19, 72, 205, -640, -495, 857, 280, -404, -38, 63], ![-63, 233, 702, -2063, -1837, 2718, 1172, -1295, -215, 214], ![-214, 793, 2373, -7002, -6129, 9077, 3788, -4178, -653, 641], ![-641, 2350, 7203, -20703, -19181, 26562, 12282, -12237, -2255, 1911], ![-1911, 7003, 21460, -61593, -57012, 78280, 36117, -35493, -6504, 5389], ![-5389, 19645, 60893, -172544, -163984, 217827, 105225, -98608, -19326, 15052]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 10, -36, -19, 51, 5, -25, 3, 4], ![-4, 15, 44, -134, -112, 185, 71, -95, -13, 19], ![-19, 72, 205, -640, -495, 857, 280, -404, -38, 63], ![-63, 233, 702, -2063, -1837, 2718, 1172, -1295, -215, 214], ![-214, 793, 2373, -7002, -6129, 9077, 3788, -4178, -653, 641], ![-641, 2350, 7203, -20703, -19181, 26562, 12282, -12237, -2255, 1911], ![-1911, 7003, 21460, -61593, -57012, 78280, 36117, -35493, -6504, 5389], ![-5389, 19645, 60893, -172544, -163984, 217827, 105225, -98608, -19326, 15052], ![-15052, 54819, 170165, -480979, -458532, 603668, 293087, -271075, -53452, 40882]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-63, -19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-63, -19, -4, -1], [-214, -63, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-63, -19, -4, -1], [-214, -63, -19, -4, -1], [-641, -214, -63, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-63, -19, -4, -1], [-214, -63, -19, -4, -1], [-641, -214, -63, -19, -4, -1], [-1911, -641, -214, -63, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-63, -19, -4, -1], [-214, -63, -19, -4, -1], [-641, -214, -63, -19, -4, -1], [-1911, -641, -214, -63, -19, -4, -1], [-5389, -1911, -641, -214, -63, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-63, -19, -4, -1], [-214, -63, -19, -4, -1], [-641, -214, -63, -19, -4, -1], [-1911, -641, -214, -63, -19, -4, -1], [-5389, -1911, -641, -214, -63, -19, -4, -1], [-15052, -5389, -1911, -641, -214, -63, -19, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 10, -36, -19, 51, 5, -25, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 10, -36, -19, 51, 5, -25, 3, 4], [-4, 15, 44, -134, -112, 185, 71, -95, -13, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 10, -36, -19, 51, 5, -25, 3, 4], [-4, 15, 44, -134, -112, 185, 71, -95, -13, 19], [-19, 72, 205, -640, -495, 857, 280, -404, -38, 63]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 10, -36, -19, 51, 5, -25, 3, 4], [-4, 15, 44, -134, -112, 185, 71, -95, -13, 19], [-19, 72, 205, -640, -495, 857, 280, -404, -38, 63], [-63, 233, 702, -2063, -1837, 2718, 1172, -1295, -215, 214]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 10, -36, -19, 51, 5, -25, 3, 4], [-4, 15, 44, -134, -112, 185, 71, -95, -13, 19], [-19, 72, 205, -640, -495, 857, 280, -404, -38, 63], [-63, 233, 702, -2063, -1837, 2718, 1172, -1295, -215, 214], [-214, 793, 2373, -7002, -6129, 9077, 3788, -4178, -653, 641]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 10, -36, -19, 51, 5, -25, 3, 4], [-4, 15, 44, -134, -112, 185, 71, -95, -13, 19], [-19, 72, 205, -640, -495, 857, 280, -404, -38, 63], [-63, 233, 702, -2063, -1837, 2718, 1172, -1295, -215, 214], [-214, 793, 2373, -7002, -6129, 9077, 3788, -4178, -653, 641], [-641, 2350, 7203, -20703, -19181, 26562, 12282, -12237, -2255, 1911]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 10, -36, -19, 51, 5, -25, 3, 4], [-4, 15, 44, -134, -112, 185, 71, -95, -13, 19], [-19, 72, 205, -640, -495, 857, 280, -404, -38, 63], [-63, 233, 702, -2063, -1837, 2718, 1172, -1295, -215, 214], [-214, 793, 2373, -7002, -6129, 9077, 3788, -4178, -653, 641], [-641, 2350, 7203, -20703, -19181, 26562, 12282, -12237, -2255, 1911], [-1911, 7003, 21460, -61593, -57012, 78280, 36117, -35493, -6504, 5389]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 10, -36, -19, 51, 5, -25, 3, 4], [-4, 15, 44, -134, -112, 185, 71, -95, -13, 19], [-19, 72, 205, -640, -495, 857, 280, -404, -38, 63], [-63, 233, 702, -2063, -1837, 2718, 1172, -1295, -215, 214], [-214, 793, 2373, -7002, -6129, 9077, 3788, -4178, -653, 641], [-641, 2350, 7203, -20703, -19181, 26562, 12282, -12237, -2255, 1911], [-1911, 7003, 21460, -61593, -57012, 78280, 36117, -35493, -6504, 5389], [-5389, 19645, 60893, -172544, -163984, 217827, 105225, -98608, -19326, 15052]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 10, -36, -19, 51, 5, -25, 3, 4], [-4, 15, 44, -134, -112, 185, 71, -95, -13, 19], [-19, 72, 205, -640, -495, 857, 280, -404, -38, 63], [-63, 233, 702, -2063, -1837, 2718, 1172, -1295, -215, 214], [-214, 793, 2373, -7002, -6129, 9077, 3788, -4178, -653, 641], [-641, 2350, 7203, -20703, -19181, 26562, 12282, -12237, -2255, 1911], [-1911, 7003, 21460, -61593, -57012, 78280, 36117, -35493, -6504, 5389], [-5389, 19645, 60893, -172544, -163984, 217827, 105225, -98608, -19326, 15052], [-15052, 54819, 170165, -480979, -458532, 603668, 293087, -271075, -53452, 40882]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1513530749 : Fact (Nat.Prime 1513530749) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 4]
  b' := [0, 1, 3, 3]
  k := [1]
  f := [0, 2, 5, -2, 4, 19, 9, 1, 4, 2]
  g := [1, 3, 3, 4, 3, 1]
  h := [1, 3, 3, 4, 3, 1]
  a := [0, 0, 4]
  b := [1, 2, 1, 4, 4, 3, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1513530749 : CertificateDedekindCriterionLists l 1513530749 where
  n := 2
  a' := [961309657, 326859330, 281063427, 94518706, 1306922033, 1059709990, 271036963, 1479495737]
  b' := [1337127236, 1290409102, 1353411269, 241749878, 820955886, 1046491866, 683353289, 369648498, 3781668]
  k := [300265990, 481987239, 1491123147, 630194312, 387219180, 108321350, 1075470594, 1011234068, 1]
  f := [800503552, 629682891, 801660365, 665944435, 49006929, 390304909, 140200259, 797700646, 336708284, 1]
  g := [1202073873, 945561514, 1203810997, 1000013558, 73591114, 586100252, 210531318, 1197864897, 505617032, 1]
  h := [1007913713, 1]
  a := [1107500025, 197206786, 454002307, 277892789, 492458427, 765447059, 634015842, 1009059773, 1329134612]
  b := [727991016, 1116148222, 901964042, 593908627, 1146111797, 332198537, 1273482663, 1250115797, 184396137]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 1513530749]
  exp := ![1, 1]
  pdgood := [5, 1513530749]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1513530749.out
  a := [-21825837211, -229958321660, -1128021398, 558060159396, -61763013800, -383318713614, 87873912784, 78374408872, -24801042620]
  b := [-7348372739, 1078120491, 80444242930, 6375287064, -114917305813, 8150650584, 55841203456, -10711827618, -8829482592, 2480104262]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1513530749 T_ofList CD1513530749

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

end VoightMaximalOrderD10R375

namespace VoightMaximalOrderD10R376

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4740603689984, [-1, 0, 19, -10, -45, 12, 38, -2, -11, 0, 1], 1⟩
local notation "l" => [-1, 0, 19, -10, -45, 12, 38, -2, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -19, 10, 45, -12, -38, 2, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -19, 10, 45, -12, -38, 2, 11, 0], ![0, 1, 0, -19, 10, 45, -12, -38, 2, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -19, 10, 45, -12, -38, 2, 11, 0], ![0, 1, 0, -19, 10, 45, -12, -38, 2, 11], ![11, 0, -208, 110, 476, -122, -373, 10, 83, 2]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -19, 10, 45, -12, -38, 2, 11, 0], ![0, 1, 0, -19, 10, 45, -12, -38, 2, 11], ![11, 0, -208, 110, 476, -122, -373, 10, 83, 2], ![2, 11, -38, -188, 200, 452, -198, -369, 32, 83]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -19, 10, 45, -12, -38, 2, 11, 0], ![0, 1, 0, -19, 10, 45, -12, -38, 2, 11], ![11, 0, -208, 110, 476, -122, -373, 10, 83, 2], ![2, 11, -38, -188, 200, 452, -198, -369, 32, 83], ![83, 2, -1566, 792, 3547, -796, -2702, -32, 544, 32]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -19, 10, 45, -12, -38, 2, 11, 0], ![0, 1, 0, -19, 10, 45, -12, -38, 2, 11], ![11, 0, -208, 110, 476, -122, -373, 10, 83, 2], ![2, 11, -38, -188, 200, 452, -198, -369, 32, 83], ![83, 2, -1566, 792, 3547, -796, -2702, -32, 544, 32], ![32, 83, -606, -1246, 2232, 3163, -2012, -2638, 320, 544]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -19, 10, 45, -12, -38, 2, 11, 0], ![0, 1, 0, -19, 10, 45, -12, -38, 2, 11], ![11, 0, -208, 110, 476, -122, -373, 10, 83, 2], ![2, 11, -38, -188, 200, 452, -198, -369, 32, 83], ![83, 2, -1566, 792, 3547, -796, -2702, -32, 544, 32], ![32, 83, -606, -1246, 2232, 3163, -2012, -2638, 320, 544], ![544, 32, -10253, 4834, 23234, -4296, -17509, -924, 3346, 320]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -19, 10, 45, -12, -38, 2, 11, 0], ![0, 1, 0, -19, 10, 45, -12, -38, 2, 11], ![11, 0, -208, 110, 476, -122, -373, 10, 83, 2], ![2, 11, -38, -188, 200, 452, -198, -369, 32, 83], ![83, 2, -1566, 792, 3547, -796, -2702, -32, 544, 32], ![32, 83, -606, -1246, 2232, 3163, -2012, -2638, 320, 544], ![544, 32, -10253, 4834, 23234, -4296, -17509, -924, 3346, 320], ![320, 544, -6048, -7053, 19234, 19394, -16456, -16869, 2596, 3346]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, -19, 10, 45, -12, -38, 2, 11, 0], ![0, 1, 0, -19, 10, 45, -12, -38, 2, 11], ![11, 0, -208, 110, 476, -122, -373, 10, 83, 2], ![2, 11, -38, -188, 200, 452, -198, -369, 32, 83], ![83, 2, -1566, 792, 3547, -796, -2702, -32, 544, 32], ![32, 83, -606, -1246, 2232, 3163, -2012, -2638, 320, 544], ![544, 32, -10253, 4834, 23234, -4296, -17509, -924, 3346, 320], ![320, 544, -6048, -7053, 19234, 19394, -16456, -16869, 2596, 3346], ![3346, 320, -63030, 27412, 143517, -20918, -107754, -9764, 19937, 2596]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-83, -2, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-83, -2, -11, 0, -1], [-32, -83, -2, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-83, -2, -11, 0, -1], [-32, -83, -2, -11, 0, -1], [-544, -32, -83, -2, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-83, -2, -11, 0, -1], [-32, -83, -2, -11, 0, -1], [-544, -32, -83, -2, -11, 0, -1], [-320, -544, -32, -83, -2, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [-2, -11, 0, -1], [-83, -2, -11, 0, -1], [-32, -83, -2, -11, 0, -1], [-544, -32, -83, -2, -11, 0, -1], [-320, -544, -32, -83, -2, -11, 0, -1], [-3346, -320, -544, -32, -83, -2, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -19, 10, 45, -12, -38, 2, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -19, 10, 45, -12, -38, 2, 11, 0], [0, 1, 0, -19, 10, 45, -12, -38, 2, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -19, 10, 45, -12, -38, 2, 11, 0], [0, 1, 0, -19, 10, 45, -12, -38, 2, 11], [11, 0, -208, 110, 476, -122, -373, 10, 83, 2]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -19, 10, 45, -12, -38, 2, 11, 0], [0, 1, 0, -19, 10, 45, -12, -38, 2, 11], [11, 0, -208, 110, 476, -122, -373, 10, 83, 2], [2, 11, -38, -188, 200, 452, -198, -369, 32, 83]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -19, 10, 45, -12, -38, 2, 11, 0], [0, 1, 0, -19, 10, 45, -12, -38, 2, 11], [11, 0, -208, 110, 476, -122, -373, 10, 83, 2], [2, 11, -38, -188, 200, 452, -198, -369, 32, 83], [83, 2, -1566, 792, 3547, -796, -2702, -32, 544, 32]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -19, 10, 45, -12, -38, 2, 11, 0], [0, 1, 0, -19, 10, 45, -12, -38, 2, 11], [11, 0, -208, 110, 476, -122, -373, 10, 83, 2], [2, 11, -38, -188, 200, 452, -198, -369, 32, 83], [83, 2, -1566, 792, 3547, -796, -2702, -32, 544, 32], [32, 83, -606, -1246, 2232, 3163, -2012, -2638, 320, 544]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -19, 10, 45, -12, -38, 2, 11, 0], [0, 1, 0, -19, 10, 45, -12, -38, 2, 11], [11, 0, -208, 110, 476, -122, -373, 10, 83, 2], [2, 11, -38, -188, 200, 452, -198, -369, 32, 83], [83, 2, -1566, 792, 3547, -796, -2702, -32, 544, 32], [32, 83, -606, -1246, 2232, 3163, -2012, -2638, 320, 544], [544, 32, -10253, 4834, 23234, -4296, -17509, -924, 3346, 320]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -19, 10, 45, -12, -38, 2, 11, 0], [0, 1, 0, -19, 10, 45, -12, -38, 2, 11], [11, 0, -208, 110, 476, -122, -373, 10, 83, 2], [2, 11, -38, -188, 200, 452, -198, -369, 32, 83], [83, 2, -1566, 792, 3547, -796, -2702, -32, 544, 32], [32, 83, -606, -1246, 2232, 3163, -2012, -2638, 320, 544], [544, 32, -10253, 4834, 23234, -4296, -17509, -924, 3346, 320], [320, 544, -6048, -7053, 19234, 19394, -16456, -16869, 2596, 3346]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 0, -19, 10, 45, -12, -38, 2, 11, 0], [0, 1, 0, -19, 10, 45, -12, -38, 2, 11], [11, 0, -208, 110, 476, -122, -373, 10, 83, 2], [2, 11, -38, -188, 200, 452, -198, -369, 32, 83], [83, 2, -1566, 792, 3547, -796, -2702, -32, 544, 32], [32, 83, -606, -1246, 2232, 3163, -2012, -2638, 320, 544], [544, 32, -10253, 4834, 23234, -4296, -17509, -924, 3346, 320], [320, 544, -6048, -7053, 19234, 19394, -16456, -16869, 2596, 3346], [3346, 320, -63030, 27412, 143517, -20918, -107754, -9764, 19937, 2596]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp4629495791 : Fact (Nat.Prime 4629495791) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [0, 0, 1]
  b' := [1, 0, 1, 1]
  k := [1]
  f := [1, 1, -8, 6, 24, -4, -17, 2, 6, 1]
  g := [1, 1, 1, 0, 1, 1]
  h := [1, 1, 1, 0, 1, 1]
  a := [1, 0, 1]
  b := [0, 1, 0, 0, 0, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD4629495791 : CertificateDedekindCriterionLists l 4629495791 where
  n := 2
  a' := [1476387639, 4222099127, 2663039209, 2021789146, 2491228303, 4317944698, 1863022810, 3566932367]
  b' := [4448526500, 2293336788, 4011067972, 1355903014, 295255409, 468988175, 2735621191, 1390979005, 3204393130]
  k := [2998325694, 1029688971, 113845628, 4148394742, 4614473967, 4507404141, 159896464, 569377794, 1]
  f := [957919231, 1530861978, 867981294, 3187079694, 2808470826, 2932314005, 674256126, 50021226, 267182073, 1]
  g := [1020685880, 1631170097, 924854854, 3395909735, 2992492919, 3124450792, 718436048, 53298814, 284688897, 1]
  h := [4344806894, 1]
  a := [2323499500, 1409082168, 1881971081, 2920992006, 4433511077, 3540695394, 2908326583, 1801058400, 906970095]
  b := [3547334487, 2726552065, 1652395022, 308909841, 463596843, 660722948, 655169521, 2692322318, 3722525696]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![2, 4629495791]
  exp := ![1, 1]
  pdgood := [2, 4629495791]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp4629495791.out
  a := [-9258991582, -382605133130, 774239846726, 1374640774924, -2026088674268, -1043720047154, 1090120188642, 174236769600, -149484704440]
  b := [-10068556135, 17055368493, 190812351028, -304760565444, -264471170642, 390703878057, 133735011761, -141898653841, -17423676960, 14948470444]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 4629495791 T_ofList CD4629495791

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

end VoightMaximalOrderD10R376

namespace VoightMaximalOrderD10R378

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4748740254477, [1, -1, -16, 16, 38, -41, -18, 28, -3, -4, 1], 1⟩
local notation "l" => [1, -1, -16, 16, 38, -41, -18, 28, -3, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 16, -16, -38, 41, 18, -28, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 16, -16, -38, 41, 18, -28, 3, 4], ![-4, 3, 65, -48, -168, 126, 113, -94, -16, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 16, -16, -38, 41, 18, -28, 3, 4], ![-4, 3, 65, -48, -168, 126, 113, -94, -16, 19], ![-19, 15, 307, -239, -770, 611, 468, -419, -37, 60]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 16, -16, -38, 41, 18, -28, 3, 4], ![-4, 3, 65, -48, -168, 126, 113, -94, -16, 19], ![-19, 15, 307, -239, -770, 611, 468, -419, -37, 60], ![-60, 41, 975, -653, -2519, 1690, 1691, -1212, -239, 203]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 16, -16, -38, 41, 18, -28, 3, 4], ![-4, 3, 65, -48, -168, 126, 113, -94, -16, 19], ![-19, 15, 307, -239, -770, 611, 468, -419, -37, 60], ![-60, 41, 975, -653, -2519, 1690, 1691, -1212, -239, 203], ![-203, 143, 3289, -2273, -8367, 5804, 5344, -3993, -603, 573]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 16, -16, -38, 41, 18, -28, 3, 4], ![-4, 3, 65, -48, -168, 126, 113, -94, -16, 19], ![-19, 15, 307, -239, -770, 611, 468, -419, -37, 60], ![-60, 41, 975, -653, -2519, 1690, 1691, -1212, -239, 203], ![-203, 143, 3289, -2273, -8367, 5804, 5344, -3993, -603, 573], ![-573, 370, 9311, -5879, -24047, 15126, 16118, -10700, -2274, 1689]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 16, -16, -38, 41, 18, -28, 3, 4], ![-4, 3, 65, -48, -168, 126, 113, -94, -16, 19], ![-19, 15, 307, -239, -770, 611, 468, -419, -37, 60], ![-60, 41, 975, -653, -2519, 1690, 1691, -1212, -239, 203], ![-203, 143, 3289, -2273, -8367, 5804, 5344, -3993, -603, 573], ![-573, 370, 9311, -5879, -24047, 15126, 16118, -10700, -2274, 1689], ![-1689, 1116, 27394, -17713, -70061, 45202, 45528, -31174, -5633, 4482]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 16, -16, -38, 41, 18, -28, 3, 4], ![-4, 3, 65, -48, -168, 126, 113, -94, -16, 19], ![-19, 15, 307, -239, -770, 611, 468, -419, -37, 60], ![-60, 41, 975, -653, -2519, 1690, 1691, -1212, -239, 203], ![-203, 143, 3289, -2273, -8367, 5804, 5344, -3993, -603, 573], ![-573, 370, 9311, -5879, -24047, 15126, 16118, -10700, -2274, 1689], ![-1689, 1116, 27394, -17713, -70061, 45202, 45528, -31174, -5633, 4482], ![-4482, 2793, 72828, -44318, -188029, 113701, 125878, -79968, -17728, 12295]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 16, -16, -38, 41, 18, -28, 3, 4], ![-4, 3, 65, -48, -168, 126, 113, -94, -16, 19], ![-19, 15, 307, -239, -770, 611, 468, -419, -37, 60], ![-60, 41, 975, -653, -2519, 1690, 1691, -1212, -239, 203], ![-203, 143, 3289, -2273, -8367, 5804, 5344, -3993, -603, 573], ![-573, 370, 9311, -5879, -24047, 15126, 16118, -10700, -2274, 1689], ![-1689, 1116, 27394, -17713, -70061, 45202, 45528, -31174, -5633, 4482], ![-4482, 2793, 72828, -44318, -188029, 113701, 125878, -79968, -17728, 12295], ![-12295, 7813, 199513, -123892, -511528, 316066, 335011, -218382, -43083, 31452]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-60, -19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-60, -19, -4, -1], [-203, -60, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-60, -19, -4, -1], [-203, -60, -19, -4, -1], [-573, -203, -60, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-60, -19, -4, -1], [-203, -60, -19, -4, -1], [-573, -203, -60, -19, -4, -1], [-1689, -573, -203, -60, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-60, -19, -4, -1], [-203, -60, -19, -4, -1], [-573, -203, -60, -19, -4, -1], [-1689, -573, -203, -60, -19, -4, -1], [-4482, -1689, -573, -203, -60, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-60, -19, -4, -1], [-203, -60, -19, -4, -1], [-573, -203, -60, -19, -4, -1], [-1689, -573, -203, -60, -19, -4, -1], [-4482, -1689, -573, -203, -60, -19, -4, -1], [-12295, -4482, -1689, -573, -203, -60, -19, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 16, -16, -38, 41, 18, -28, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 16, -16, -38, 41, 18, -28, 3, 4], [-4, 3, 65, -48, -168, 126, 113, -94, -16, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 16, -16, -38, 41, 18, -28, 3, 4], [-4, 3, 65, -48, -168, 126, 113, -94, -16, 19], [-19, 15, 307, -239, -770, 611, 468, -419, -37, 60]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 16, -16, -38, 41, 18, -28, 3, 4], [-4, 3, 65, -48, -168, 126, 113, -94, -16, 19], [-19, 15, 307, -239, -770, 611, 468, -419, -37, 60], [-60, 41, 975, -653, -2519, 1690, 1691, -1212, -239, 203]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 16, -16, -38, 41, 18, -28, 3, 4], [-4, 3, 65, -48, -168, 126, 113, -94, -16, 19], [-19, 15, 307, -239, -770, 611, 468, -419, -37, 60], [-60, 41, 975, -653, -2519, 1690, 1691, -1212, -239, 203], [-203, 143, 3289, -2273, -8367, 5804, 5344, -3993, -603, 573]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 16, -16, -38, 41, 18, -28, 3, 4], [-4, 3, 65, -48, -168, 126, 113, -94, -16, 19], [-19, 15, 307, -239, -770, 611, 468, -419, -37, 60], [-60, 41, 975, -653, -2519, 1690, 1691, -1212, -239, 203], [-203, 143, 3289, -2273, -8367, 5804, 5344, -3993, -603, 573], [-573, 370, 9311, -5879, -24047, 15126, 16118, -10700, -2274, 1689]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 16, -16, -38, 41, 18, -28, 3, 4], [-4, 3, 65, -48, -168, 126, 113, -94, -16, 19], [-19, 15, 307, -239, -770, 611, 468, -419, -37, 60], [-60, 41, 975, -653, -2519, 1690, 1691, -1212, -239, 203], [-203, 143, 3289, -2273, -8367, 5804, 5344, -3993, -603, 573], [-573, 370, 9311, -5879, -24047, 15126, 16118, -10700, -2274, 1689], [-1689, 1116, 27394, -17713, -70061, 45202, 45528, -31174, -5633, 4482]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 16, -16, -38, 41, 18, -28, 3, 4], [-4, 3, 65, -48, -168, 126, 113, -94, -16, 19], [-19, 15, 307, -239, -770, 611, 468, -419, -37, 60], [-60, 41, 975, -653, -2519, 1690, 1691, -1212, -239, 203], [-203, 143, 3289, -2273, -8367, 5804, 5344, -3993, -603, 573], [-573, 370, 9311, -5879, -24047, 15126, 16118, -10700, -2274, 1689], [-1689, 1116, 27394, -17713, -70061, 45202, 45528, -31174, -5633, 4482], [-4482, 2793, 72828, -44318, -188029, 113701, 125878, -79968, -17728, 12295]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 16, -16, -38, 41, 18, -28, 3, 4], [-4, 3, 65, -48, -168, 126, 113, -94, -16, 19], [-19, 15, 307, -239, -770, 611, 468, -419, -37, 60], [-60, 41, 975, -653, -2519, 1690, 1691, -1212, -239, 203], [-203, 143, 3289, -2273, -8367, 5804, 5344, -3993, -603, 573], [-573, 370, 9311, -5879, -24047, 15126, 16118, -10700, -2274, 1689], [-1689, 1116, 27394, -17713, -70061, 45202, 45528, -31174, -5633, 4482], [-4482, 2793, 72828, -44318, -188029, 113701, 125878, -79968, -17728, 12295], [-12295, 7813, 199513, -123892, -511528, 316066, 335011, -218382, -43083, 31452]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp47 : Fact (Nat.Prime 47) := fact_iff.2 (by norm_num)
instance hp109 : Fact (Nat.Prime 109) := fact_iff.2 (by norm_num)
instance hp102993911 : Fact (Nat.Prime 102993911) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 2
  a' := [0, 0, 0, 2]
  b' := [2, 1, 2, 2, 2]
  k := [1, 2, 0, 0, 1, 2, 1]
  f := [0, 1, 6, -4, -12, 15, 7, -8, 2, 2]
  g := [1, 2, 1, 2, 1, 2, 2, 2, 1]
  h := [1, 0, 1]
  a := [1, 2, 0, 1, 0, 0, 0, 1]
  b := [1, 0, 0, 2, 2, 1, 2, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD47 : CertificateDedekindCriterionLists l 47 where
  n := 2
  a' := [31, 22, 20, 14, 18, 21, 11, 35]
  b' := [6, 24, 29, 38, 24, 40, 32, 34, 17]
  k := [32, 21, 16, 31, 43, 10, 18, 33, 1]
  f := [2, 5, 2, 3, 1, 6, 2, 4, 5, 1]
  g := [19, 43, 7, 30, 11, 46, 6, 42, 38, 1]
  h := [5, 1]
  a := [44, 0, 0, 0, 17, 36, 34, 2, 39]
  b := [35, 23, 17, 17, 43, 19, 31, 16, 8]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD109 : CertificateDedekindCriterionLists l 109 where
  n := 2
  a' := [86, 50, 108, 94, 88, 48, 26, 40]
  b' := [37, 86, 11, 94, 21, 40, 33, 52, 44]
  k := [28, 17, 6, 5, 106, 58, 8, 76, 1]
  f := [50, 2, 66, 16, 10, 48, 42, 13, 23, 1]
  g := [79, 2, 104, 24, 16, 75, 65, 20, 36, 1]
  h := [69, 1]
  a := [63, 69, 30, 62, 101, 102, 53, 23, 91]
  b := [65, 0, 77, 79, 0, 68, 42, 70, 18]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD102993911 : CertificateDedekindCriterionLists l 102993911 where
  n := 2
  a' := [76549561, 6467044, 90075599, 35414652, 98368626, 51639857, 97380970, 23613521]
  b' := [45501897, 57222824, 63696678, 80800068, 90448201, 67765633, 88074853, 27001427, 43151347]
  k := [9585206, 76271752, 98105294, 99546657, 25203732, 69519869, 36514683, 81798689, 1]
  f := [5020769, 4590566, 1017696, 646675, 3553772, 2873353, 9495120, 6238864, 9507163, 1]
  g := [48794840, 44613865, 9890575, 6284774, 34537684, 27924962, 92279260, 60633008, 92396298, 1]
  h := [10597609, 1]
  a := [22445198, 74501596, 76323787, 75649540, 50852376, 57688806, 42476751, 38210325, 38865765]
  b := [28242920, 28591555, 77669406, 39824645, 75540426, 94380678, 102721578, 74760531, 64128146]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![3, 47, 109, 102993911]
  exp := ![1, 1, 1, 1]
  pdgood := [3, 47, 109, 102993911]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp47.out
    exact hp109.out
    exact hp102993911.out
  a := [676651232776, -29476203949116, 1293154153525, 138936372581452, -53528263059308, -135341865549912, 66238913730412, 25411182225830, -12627027947500]
  b := [-906262185383, -1152465249636, 13321241468193, 738990195279, -32680684154349, 8270269726980, 21488843746573, -8183357785298, -3046199340483, 1262702794750]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 47 T_ofList CD47
    exact satisfiesDedekindCriterion_of_certificate_lists T l 109 T_ofList CD109
    exact satisfiesDedekindCriterion_of_certificate_lists T l 102993911 T_ofList CD102993911

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

end VoightMaximalOrderD10R378

namespace VoightMaximalOrderD10R379

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4755599565625, [-1, -5, 13, 18, -34, -21, 31, 8, -10, -1, 1], 1⟩
local notation "l" => [-1, -5, 13, 18, -34, -21, 31, 8, -10, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -13, -18, 34, 21, -31, -8, 10, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -13, -18, 34, 21, -31, -8, 10, 1], ![1, 6, -8, -31, 16, 55, -10, -39, 2, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -13, -18, 34, 21, -31, -8, 10, 1], ![1, 6, -8, -31, 16, 55, -10, -39, 2, 11], ![11, 56, -137, -206, 343, 247, -286, -98, 71, 13]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -13, -18, 34, 21, -31, -8, 10, 1], ![1, 6, -8, -31, 16, 55, -10, -39, 2, 11], ![11, 56, -137, -206, 343, 247, -286, -98, 71, 13], ![13, 76, -113, -371, 236, 616, -156, -390, 32, 84]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -13, -18, 34, 21, -31, -8, 10, 1], ![1, 6, -8, -31, 16, 55, -10, -39, 2, 11], ![11, 56, -137, -206, 343, 247, -286, -98, 71, 13], ![13, 76, -113, -371, 236, 616, -156, -390, 32, 84], ![84, 433, -1016, -1625, 2485, 2000, -1988, -828, 450, 116]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -13, -18, 34, 21, -31, -8, 10, 1], ![1, 6, -8, -31, 16, 55, -10, -39, 2, 11], ![11, 56, -137, -206, 343, 247, -286, -98, 71, 13], ![13, 76, -113, -371, 236, 616, -156, -390, 32, 84], ![84, 433, -1016, -1625, 2485, 2000, -1988, -828, 450, 116], ![116, 664, -1075, -3104, 2319, 4921, -1596, -2916, 332, 566]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -13, -18, 34, 21, -31, -8, 10, 1], ![1, 6, -8, -31, 16, 55, -10, -39, 2, 11], ![11, 56, -137, -206, 343, 247, -286, -98, 71, 13], ![13, 76, -113, -371, 236, 616, -156, -390, 32, 84], ![84, 433, -1016, -1625, 2485, 2000, -1988, -828, 450, 116], ![116, 664, -1075, -3104, 2319, 4921, -1596, -2916, 332, 566], ![566, 2946, -6694, -11263, 16140, 14205, -12625, -6124, 2744, 898]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -13, -18, 34, 21, -31, -8, 10, 1], ![1, 6, -8, -31, 16, 55, -10, -39, 2, 11], ![11, 56, -137, -206, 343, 247, -286, -98, 71, 13], ![13, 76, -113, -371, 236, 616, -156, -390, 32, 84], ![84, 433, -1016, -1625, 2485, 2000, -1988, -828, 450, 116], ![116, 664, -1075, -3104, 2319, 4921, -1596, -2916, 332, 566], ![566, 2946, -6694, -11263, 16140, 14205, -12625, -6124, 2744, 898], ![898, 5056, -8728, -22858, 19269, 34998, -13633, -19809, 2856, 3642]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 5, -13, -18, 34, 21, -31, -8, 10, 1], ![1, 6, -8, -31, 16, 55, -10, -39, 2, 11], ![11, 56, -137, -206, 343, 247, -286, -98, 71, 13], ![13, 76, -113, -371, 236, 616, -156, -390, 32, 84], ![84, 433, -1016, -1625, 2485, 2000, -1988, -828, 450, 116], ![116, 664, -1075, -3104, 2319, 4921, -1596, -2916, 332, 566], ![566, 2946, -6694, -11263, 16140, 14205, -12625, -6124, 2744, 898], ![898, 5056, -8728, -22858, 19269, 34998, -13633, -19809, 2856, 3642], ![3642, 19108, -42290, -74284, 100970, 95751, -77904, -42769, 16611, 6498]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-84, -13, -11, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-84, -13, -11, -1, -1], [-116, -84, -13, -11, -1, -1]], ![[], [], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-84, -13, -11, -1, -1], [-116, -84, -13, -11, -1, -1], [-566, -116, -84, -13, -11, -1, -1]], ![[], [], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-84, -13, -11, -1, -1], [-116, -84, -13, -11, -1, -1], [-566, -116, -84, -13, -11, -1, -1], [-898, -566, -116, -84, -13, -11, -1, -1]], ![[], [-1], [-1, -1], [-11, -1, -1], [-13, -11, -1, -1], [-84, -13, -11, -1, -1], [-116, -84, -13, -11, -1, -1], [-566, -116, -84, -13, -11, -1, -1], [-898, -566, -116, -84, -13, -11, -1, -1], [-3642, -898, -566, -116, -84, -13, -11, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -13, -18, 34, 21, -31, -8, 10, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -13, -18, 34, 21, -31, -8, 10, 1], [1, 6, -8, -31, 16, 55, -10, -39, 2, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -13, -18, 34, 21, -31, -8, 10, 1], [1, 6, -8, -31, 16, 55, -10, -39, 2, 11], [11, 56, -137, -206, 343, 247, -286, -98, 71, 13]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -13, -18, 34, 21, -31, -8, 10, 1], [1, 6, -8, -31, 16, 55, -10, -39, 2, 11], [11, 56, -137, -206, 343, 247, -286, -98, 71, 13], [13, 76, -113, -371, 236, 616, -156, -390, 32, 84]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -13, -18, 34, 21, -31, -8, 10, 1], [1, 6, -8, -31, 16, 55, -10, -39, 2, 11], [11, 56, -137, -206, 343, 247, -286, -98, 71, 13], [13, 76, -113, -371, 236, 616, -156, -390, 32, 84], [84, 433, -1016, -1625, 2485, 2000, -1988, -828, 450, 116]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -13, -18, 34, 21, -31, -8, 10, 1], [1, 6, -8, -31, 16, 55, -10, -39, 2, 11], [11, 56, -137, -206, 343, 247, -286, -98, 71, 13], [13, 76, -113, -371, 236, 616, -156, -390, 32, 84], [84, 433, -1016, -1625, 2485, 2000, -1988, -828, 450, 116], [116, 664, -1075, -3104, 2319, 4921, -1596, -2916, 332, 566]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -13, -18, 34, 21, -31, -8, 10, 1], [1, 6, -8, -31, 16, 55, -10, -39, 2, 11], [11, 56, -137, -206, 343, 247, -286, -98, 71, 13], [13, 76, -113, -371, 236, 616, -156, -390, 32, 84], [84, 433, -1016, -1625, 2485, 2000, -1988, -828, 450, 116], [116, 664, -1075, -3104, 2319, 4921, -1596, -2916, 332, 566], [566, 2946, -6694, -11263, 16140, 14205, -12625, -6124, 2744, 898]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -13, -18, 34, 21, -31, -8, 10, 1], [1, 6, -8, -31, 16, 55, -10, -39, 2, 11], [11, 56, -137, -206, 343, 247, -286, -98, 71, 13], [13, 76, -113, -371, 236, 616, -156, -390, 32, 84], [84, 433, -1016, -1625, 2485, 2000, -1988, -828, 450, 116], [116, 664, -1075, -3104, 2319, 4921, -1596, -2916, 332, 566], [566, 2946, -6694, -11263, 16140, 14205, -12625, -6124, 2744, 898], [898, 5056, -8728, -22858, 19269, 34998, -13633, -19809, 2856, 3642]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 5, -13, -18, 34, 21, -31, -8, 10, 1], [1, 6, -8, -31, 16, 55, -10, -39, 2, 11], [11, 56, -137, -206, 343, 247, -286, -98, 71, 13], [13, 76, -113, -371, 236, 616, -156, -390, 32, 84], [84, 433, -1016, -1625, 2485, 2000, -1988, -828, 450, 116], [116, 664, -1075, -3104, 2319, 4921, -1596, -2916, 332, 566], [566, 2946, -6694, -11263, 16140, 14205, -12625, -6124, 2744, 898], [898, 5056, -8728, -22858, 19269, 34998, -13633, -19809, 2856, 3642], [3642, 19108, -42290, -74284, 100970, 95751, -77904, -42769, 16611, 6498]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1521791861 : Fact (Nat.Prime 1521791861) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 3]
  b' := [1, 0, 2, 4]
  k := [1]
  f := [2, 1, 1, 0, 11, 9, -2, 2, 4, 1]
  g := [3, 0, 3, 3, 2, 1]
  h := [3, 0, 3, 3, 2, 1]
  a := [0, 2, 1, 2, 4]
  b := [2, 2, 0, 2, 3, 0, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1521791861 : CertificateDedekindCriterionLists l 1521791861 where
  n := 2
  a' := [880404030, 928415527, 659089922, 1015677588, 589657202, 979750521, 416705667, 961352955]
  b' := [720630933, 649609545, 1347027995, 443185613, 979290068, 335748866, 101674996, 662939554, 1414974866]
  k := [1323013213, 980629196, 1510477586, 28282255, 1404814957, 8431741, 1257258674, 1290571830, 1]
  f := [9071146, 60456877, 113798965, 43566170, 3507516, 51598177, 105017934, 111838801, 106827162, 1]
  g := [119404847, 795802883, 1497952733, 573467977, 46169951, 679194495, 1382366714, 1472150797, 1406181845, 1]
  h := [115610015, 1]
  a := [587168339, 385238888, 194754753, 1489104771, 1330353753, 610943857, 275885283, 1057916992, 592520671]
  b := [290980563, 77678618, 591318176, 486398822, 514949522, 1258345319, 1209979664, 1146322456, 929271190]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 1521791861]
  exp := ![1, 1]
  pdgood := [5, 1521791861]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1521791861.out
  a := [27862245665, -278171028344, 224170155204, 1661281093076, -1469373483126, -1052611698888, 878046975586, 171980851040, -126583204200]
  b := [-7094240994, -9118093165, 181746948839, -139794880302, -342518100628, 273959137122, 146428649474, -112540778726, -18463917146, 12658320420]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1521791861 T_ofList CD1521791861

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

end VoightMaximalOrderD10R379

end TraceEuclidean
