import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk164
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

namespace VoightMaximalOrderD10R11

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨838055754181, [1, -3, -9, 31, -3, -43, 17, 17, -8, -2, 1], 1⟩
local notation "l" => [1, -3, -9, 31, -3, -43, 17, 17, -8, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 9, -31, 3, 43, -17, -17, 8, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 9, -31, 3, 43, -17, -17, 8, 2], ![-2, 5, 21, -53, -25, 89, 9, -51, -1, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 9, -31, 3, 43, -17, -17, 8, 2], ![-2, 5, 21, -53, -25, 89, 9, -51, -1, 12], ![-12, 34, 113, -351, -17, 491, -115, -195, 45, 23]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 9, -31, 3, 43, -17, -17, 8, 2], ![-2, 5, 21, -53, -25, 89, 9, -51, -1, 12], ![-12, 34, 113, -351, -17, 491, -115, -195, 45, 23], ![-23, 57, 241, -600, -282, 972, 100, -506, -11, 91]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 9, -31, 3, 43, -17, -17, 8, 2], ![-2, 5, 21, -53, -25, 89, 9, -51, -1, 12], ![-12, 34, 113, -351, -17, 491, -115, -195, 45, 23], ![-23, 57, 241, -600, -282, 972, 100, -506, -11, 91], ![-91, 250, 876, -2580, -327, 3631, -575, -1447, 222, 171]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 9, -31, 3, 43, -17, -17, 8, 2], ![-2, 5, 21, -53, -25, 89, 9, -51, -1, 12], ![-12, 34, 113, -351, -17, 491, -115, -195, 45, 23], ![-23, 57, 241, -600, -282, 972, 100, -506, -11, 91], ![-91, 250, 876, -2580, -327, 3631, -575, -1447, 222, 171], ![-171, 422, 1789, -4425, -2067, 7026, 724, -3482, -79, 564]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 9, -31, 3, 43, -17, -17, 8, 2], ![-2, 5, 21, -53, -25, 89, 9, -51, -1, 12], ![-12, 34, 113, -351, -17, 491, -115, -195, 45, 23], ![-23, 57, 241, -600, -282, 972, 100, -506, -11, 91], ![-91, 250, 876, -2580, -327, 3631, -575, -1447, 222, 171], ![-171, 422, 1789, -4425, -2067, 7026, 724, -3482, -79, 564], ![-564, 1521, 5498, -15695, -2733, 22185, -2562, -8864, 1030, 1049]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 9, -31, 3, 43, -17, -17, 8, 2], ![-2, 5, 21, -53, -25, 89, 9, -51, -1, 12], ![-12, 34, 113, -351, -17, 491, -115, -195, 45, 23], ![-23, 57, 241, -600, -282, 972, 100, -506, -11, 91], ![-91, 250, 876, -2580, -327, 3631, -575, -1447, 222, 171], ![-171, 422, 1789, -4425, -2067, 7026, 724, -3482, -79, 564], ![-564, 1521, 5498, -15695, -2733, 22185, -2562, -8864, 1030, 1049], ![-1049, 2583, 10962, -27021, -12548, 42374, 4352, -20395, -472, 3128]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 9, -31, 3, 43, -17, -17, 8, 2], ![-2, 5, 21, -53, -25, 89, 9, -51, -1, 12], ![-12, 34, 113, -351, -17, 491, -115, -195, 45, 23], ![-23, 57, 241, -600, -282, 972, 100, -506, -11, 91], ![-91, 250, 876, -2580, -327, 3631, -575, -1447, 222, 171], ![-171, 422, 1789, -4425, -2067, 7026, 724, -3482, -79, 564], ![-564, 1521, 5498, -15695, -2733, 22185, -2562, -8864, 1030, 1049], ![-1049, 2583, 10962, -27021, -12548, 42374, 4352, -20395, -472, 3128], ![-3128, 8335, 30735, -86006, -17637, 121956, -10802, -48824, 4629, 5784]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-12, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-12, -2, -1], [-23, -12, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-12, -2, -1], [-23, -12, -2, -1], [-91, -23, -12, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-12, -2, -1], [-23, -12, -2, -1], [-91, -23, -12, -2, -1], [-171, -91, -23, -12, -2, -1]], ![[], [], [], [-1], [-2, -1], [-12, -2, -1], [-23, -12, -2, -1], [-91, -23, -12, -2, -1], [-171, -91, -23, -12, -2, -1], [-564, -171, -91, -23, -12, -2, -1]], ![[], [], [-1], [-2, -1], [-12, -2, -1], [-23, -12, -2, -1], [-91, -23, -12, -2, -1], [-171, -91, -23, -12, -2, -1], [-564, -171, -91, -23, -12, -2, -1], [-1049, -564, -171, -91, -23, -12, -2, -1]], ![[], [-1], [-2, -1], [-12, -2, -1], [-23, -12, -2, -1], [-91, -23, -12, -2, -1], [-171, -91, -23, -12, -2, -1], [-564, -171, -91, -23, -12, -2, -1], [-1049, -564, -171, -91, -23, -12, -2, -1], [-3128, -1049, -564, -171, -91, -23, -12, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 9, -31, 3, 43, -17, -17, 8, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 9, -31, 3, 43, -17, -17, 8, 2], [-2, 5, 21, -53, -25, 89, 9, -51, -1, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 9, -31, 3, 43, -17, -17, 8, 2], [-2, 5, 21, -53, -25, 89, 9, -51, -1, 12], [-12, 34, 113, -351, -17, 491, -115, -195, 45, 23]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 9, -31, 3, 43, -17, -17, 8, 2], [-2, 5, 21, -53, -25, 89, 9, -51, -1, 12], [-12, 34, 113, -351, -17, 491, -115, -195, 45, 23], [-23, 57, 241, -600, -282, 972, 100, -506, -11, 91]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 9, -31, 3, 43, -17, -17, 8, 2], [-2, 5, 21, -53, -25, 89, 9, -51, -1, 12], [-12, 34, 113, -351, -17, 491, -115, -195, 45, 23], [-23, 57, 241, -600, -282, 972, 100, -506, -11, 91], [-91, 250, 876, -2580, -327, 3631, -575, -1447, 222, 171]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 9, -31, 3, 43, -17, -17, 8, 2], [-2, 5, 21, -53, -25, 89, 9, -51, -1, 12], [-12, 34, 113, -351, -17, 491, -115, -195, 45, 23], [-23, 57, 241, -600, -282, 972, 100, -506, -11, 91], [-91, 250, 876, -2580, -327, 3631, -575, -1447, 222, 171], [-171, 422, 1789, -4425, -2067, 7026, 724, -3482, -79, 564]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 9, -31, 3, 43, -17, -17, 8, 2], [-2, 5, 21, -53, -25, 89, 9, -51, -1, 12], [-12, 34, 113, -351, -17, 491, -115, -195, 45, 23], [-23, 57, 241, -600, -282, 972, 100, -506, -11, 91], [-91, 250, 876, -2580, -327, 3631, -575, -1447, 222, 171], [-171, 422, 1789, -4425, -2067, 7026, 724, -3482, -79, 564], [-564, 1521, 5498, -15695, -2733, 22185, -2562, -8864, 1030, 1049]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 9, -31, 3, 43, -17, -17, 8, 2], [-2, 5, 21, -53, -25, 89, 9, -51, -1, 12], [-12, 34, 113, -351, -17, 491, -115, -195, 45, 23], [-23, 57, 241, -600, -282, 972, 100, -506, -11, 91], [-91, 250, 876, -2580, -327, 3631, -575, -1447, 222, 171], [-171, 422, 1789, -4425, -2067, 7026, 724, -3482, -79, 564], [-564, 1521, 5498, -15695, -2733, 22185, -2562, -8864, 1030, 1049], [-1049, 2583, 10962, -27021, -12548, 42374, 4352, -20395, -472, 3128]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 9, -31, 3, 43, -17, -17, 8, 2], [-2, 5, 21, -53, -25, 89, 9, -51, -1, 12], [-12, 34, 113, -351, -17, 491, -115, -195, 45, 23], [-23, 57, 241, -600, -282, 972, 100, -506, -11, 91], [-91, 250, 876, -2580, -327, 3631, -575, -1447, 222, 171], [-171, 422, 1789, -4425, -2067, 7026, 724, -3482, -79, 564], [-564, 1521, 5498, -15695, -2733, 22185, -2562, -8864, 1030, 1049], [-1049, 2583, 10962, -27021, -12548, 42374, 4352, -20395, -472, 3128], [-3128, 8335, 30735, -86006, -17637, 121956, -10802, -48824, 4629, 5784]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp61 : Fact (Nat.Prime 61) := fact_iff.2 (by norm_num)
instance hp397 : Fact (Nat.Prime 397) := fact_iff.2 (by norm_num)
instance hp1429 : Fact (Nat.Prime 1429) := fact_iff.2 (by norm_num)

def CD61 : CertificateDedekindCriterionLists l 61 where
  n := 2
  a' := [5, 58, 59, 39, 19, 60, 5]
  b' := [1, 17, 59, 50, 25, 53, 9, 7]
  k := [27, 7, 1, 21, 21, 31, 1]
  f := [20, 41, 34, 32, 17, 35, 13, 25, 11, 1]
  g := [37, 60, 36, 43, 12, 57, 0, 45, 1]
  h := [33, 14, 1]
  a := [55, 55, 6, 8, 38, 54, 18, 8]
  b := [28, 9, 5, 41, 47, 27, 13, 10, 53]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD397 : CertificateDedekindCriterionLists l 397 where
  n := 2
  a' := [204, 312, 194, 101, 90, 201, 135]
  b' := [58, 79, 101, 307, 138, 156, 5, 132]
  k := [25, 310, 137, 123, 283, 144, 1]
  f := [2, 93, 329, 437, 288, 174, 407, 235, 59, 1]
  g := [5, 222, 369, 338, 28, 375, 252, 71, 1]
  h := [159, 324, 1]
  a := [26, 149, 304, 56, 168, 392, 309, 245]
  b := [228, 132, 102, 124, 367, 12, 20, 249, 152]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1429 : CertificateDedekindCriterionLists l 1429 where
  n := 2
  a' := [263, 1003, 950, 293, 1036, 100, 476, 99]
  b' := [1141, 75, 352, 1300, 1407, 1337, 750, 736, 1418]
  k := [1182, 212, 1067, 865, 337, 1420, 634, 270, 1]
  f := [656, 842, 777, 548, 689, 120, 847, 967, 122, 1]
  g := [725, 930, 858, 605, 761, 132, 936, 1068, 134, 1]
  h := [1293, 1]
  a := [1266, 1052, 442, 1035, 1020, 837, 157, 4, 27]
  b := [589, 175, 180, 1408, 419, 757, 643, 320, 1402]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![61, 397, 1429]
  exp := ![1, 1, 1]
  pdgood := [61, 397, 1429]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp61.out
    exact hp397.out
    exact hp1429.out
  a := [-366945629, -3202809738, 5542794549, 9215768390, -9757744785, -5457235166, 4793224346, 851704926, -679847020]
  b := [-133850574, 102445827, 1387202052, -1266203417, -2042163353, 1588264185, 828373702, -595538352, -98767433, 67984702]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 61 T_ofList CD61
    exact satisfiesDedekindCriterion_of_certificate_lists T l 397 T_ofList CD397
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1429 T_ofList CD1429

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

end VoightMaximalOrderD10R11

namespace VoightMaximalOrderD10R12

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨911025153125, [-1, -4, 5, 27, -3, -41, 2, 22, -3, -4, 1], 1⟩
local notation "l" => [-1, -4, 5, 27, -3, -41, 2, 22, -3, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -5, -27, 3, 41, -2, -22, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -5, -27, 3, 41, -2, -22, 3, 4], ![4, 17, -16, -113, -15, 167, 33, -90, -10, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -5, -27, 3, 41, -2, -22, 3, 4], ![4, 17, -16, -113, -15, 167, 33, -90, -10, 19], ![19, 80, -78, -529, -56, 764, 129, -385, -33, 66]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -5, -27, 3, 41, -2, -22, 3, 4], ![4, 17, -16, -113, -15, 167, 33, -90, -10, 19], ![19, 80, -78, -529, -56, 764, 129, -385, -33, 66], ![66, 283, -250, -1860, -331, 2650, 632, -1323, -187, 231]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -5, -27, 3, 41, -2, -22, 3, 4], ![4, 17, -16, -113, -15, 167, 33, -90, -10, 19], ![19, 80, -78, -529, -56, 764, 129, -385, -33, 66], ![66, 283, -250, -1860, -331, 2650, 632, -1323, -187, 231], ![231, 990, -872, -6487, -1167, 9140, 2188, -4450, -630, 737]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -5, -27, 3, 41, -2, -22, 3, 4], ![4, 17, -16, -113, -15, 167, 33, -90, -10, 19], ![19, 80, -78, -529, -56, 764, 129, -385, -33, 66], ![66, 283, -250, -1860, -331, 2650, 632, -1323, -187, 231], ![231, 990, -872, -6487, -1167, 9140, 2188, -4450, -630, 737], ![737, 3179, -2695, -20771, -4276, 29050, 7666, -14026, -2239, 2318]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -5, -27, 3, 41, -2, -22, 3, 4], ![4, 17, -16, -113, -15, 167, 33, -90, -10, 19], ![19, 80, -78, -529, -56, 764, 129, -385, -33, 66], ![66, 283, -250, -1860, -331, 2650, 632, -1323, -187, 231], ![231, 990, -872, -6487, -1167, 9140, 2188, -4450, -630, 737], ![737, 3179, -2695, -20771, -4276, 29050, 7666, -14026, -2239, 2318], ![2318, 10009, -8411, -65281, -13817, 90762, 24414, -43330, -7072, 7033]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -5, -27, 3, 41, -2, -22, 3, 4], ![4, 17, -16, -113, -15, 167, 33, -90, -10, 19], ![19, 80, -78, -529, -56, 764, 129, -385, -33, 66], ![66, 283, -250, -1860, -331, 2650, 632, -1323, -187, 231], ![231, 990, -872, -6487, -1167, 9140, 2188, -4450, -630, 737], ![737, 3179, -2695, -20771, -4276, 29050, 7666, -14026, -2239, 2318], ![2318, 10009, -8411, -65281, -13817, 90762, 24414, -43330, -7072, 7033], ![7033, 30450, -25156, -198302, -44182, 274536, 76696, -130312, -22231, 21060]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 4, -5, -27, 3, 41, -2, -22, 3, 4], ![4, 17, -16, -113, -15, 167, 33, -90, -10, 19], ![19, 80, -78, -529, -56, 764, 129, -385, -33, 66], ![66, 283, -250, -1860, -331, 2650, 632, -1323, -187, 231], ![231, 990, -872, -6487, -1167, 9140, 2188, -4450, -630, 737], ![737, 3179, -2695, -20771, -4276, 29050, 7666, -14026, -2239, 2318], ![2318, 10009, -8411, -65281, -13817, 90762, 24414, -43330, -7072, 7033], ![7033, 30450, -25156, -198302, -44182, 274536, 76696, -130312, -22231, 21060], ![21060, 91273, -74850, -593776, -135122, 819278, 232416, -386624, -67132, 62009]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-66, -19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-66, -19, -4, -1], [-231, -66, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-66, -19, -4, -1], [-231, -66, -19, -4, -1], [-737, -231, -66, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-66, -19, -4, -1], [-231, -66, -19, -4, -1], [-737, -231, -66, -19, -4, -1], [-2318, -737, -231, -66, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-66, -19, -4, -1], [-231, -66, -19, -4, -1], [-737, -231, -66, -19, -4, -1], [-2318, -737, -231, -66, -19, -4, -1], [-7033, -2318, -737, -231, -66, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-66, -19, -4, -1], [-231, -66, -19, -4, -1], [-737, -231, -66, -19, -4, -1], [-2318, -737, -231, -66, -19, -4, -1], [-7033, -2318, -737, -231, -66, -19, -4, -1], [-21060, -7033, -2318, -737, -231, -66, -19, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -5, -27, 3, 41, -2, -22, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -5, -27, 3, 41, -2, -22, 3, 4], [4, 17, -16, -113, -15, 167, 33, -90, -10, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -5, -27, 3, 41, -2, -22, 3, 4], [4, 17, -16, -113, -15, 167, 33, -90, -10, 19], [19, 80, -78, -529, -56, 764, 129, -385, -33, 66]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -5, -27, 3, 41, -2, -22, 3, 4], [4, 17, -16, -113, -15, 167, 33, -90, -10, 19], [19, 80, -78, -529, -56, 764, 129, -385, -33, 66], [66, 283, -250, -1860, -331, 2650, 632, -1323, -187, 231]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -5, -27, 3, 41, -2, -22, 3, 4], [4, 17, -16, -113, -15, 167, 33, -90, -10, 19], [19, 80, -78, -529, -56, 764, 129, -385, -33, 66], [66, 283, -250, -1860, -331, 2650, 632, -1323, -187, 231], [231, 990, -872, -6487, -1167, 9140, 2188, -4450, -630, 737]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -5, -27, 3, 41, -2, -22, 3, 4], [4, 17, -16, -113, -15, 167, 33, -90, -10, 19], [19, 80, -78, -529, -56, 764, 129, -385, -33, 66], [66, 283, -250, -1860, -331, 2650, 632, -1323, -187, 231], [231, 990, -872, -6487, -1167, 9140, 2188, -4450, -630, 737], [737, 3179, -2695, -20771, -4276, 29050, 7666, -14026, -2239, 2318]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -5, -27, 3, 41, -2, -22, 3, 4], [4, 17, -16, -113, -15, 167, 33, -90, -10, 19], [19, 80, -78, -529, -56, 764, 129, -385, -33, 66], [66, 283, -250, -1860, -331, 2650, 632, -1323, -187, 231], [231, 990, -872, -6487, -1167, 9140, 2188, -4450, -630, 737], [737, 3179, -2695, -20771, -4276, 29050, 7666, -14026, -2239, 2318], [2318, 10009, -8411, -65281, -13817, 90762, 24414, -43330, -7072, 7033]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -5, -27, 3, 41, -2, -22, 3, 4], [4, 17, -16, -113, -15, 167, 33, -90, -10, 19], [19, 80, -78, -529, -56, 764, 129, -385, -33, 66], [66, 283, -250, -1860, -331, 2650, 632, -1323, -187, 231], [231, 990, -872, -6487, -1167, 9140, 2188, -4450, -630, 737], [737, 3179, -2695, -20771, -4276, 29050, 7666, -14026, -2239, 2318], [2318, 10009, -8411, -65281, -13817, 90762, 24414, -43330, -7072, 7033], [7033, 30450, -25156, -198302, -44182, 274536, 76696, -130312, -22231, 21060]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 4, -5, -27, 3, 41, -2, -22, 3, 4], [4, 17, -16, -113, -15, 167, 33, -90, -10, 19], [19, 80, -78, -529, -56, 764, 129, -385, -33, 66], [66, 283, -250, -1860, -331, 2650, 632, -1323, -187, 231], [231, 990, -872, -6487, -1167, 9140, 2188, -4450, -630, 737], [737, 3179, -2695, -20771, -4276, 29050, 7666, -14026, -2239, 2318], [2318, 10009, -8411, -65281, -13817, 90762, 24414, -43330, -7072, 7033], [7033, 30450, -25156, -198302, -44182, 274536, 76696, -130312, -22231, 21060], [21060, 91273, -74850, -593776, -135122, 819278, 232416, -386624, -67132, 62009]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp419 : Fact (Nat.Prime 419) := fact_iff.2 (by norm_num)
instance hp695771 : Fact (Nat.Prime 695771) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 3, 1]
  b' := [1, 3, 3, 0, 2]
  k := [1]
  f := [2, 2, 4, 1, 9, 17, 8, 2, 4, 2]
  g := [3, 1, 4, 4, 3, 1]
  h := [3, 1, 4, 4, 3, 1]
  a := [1, 4, 4, 2, 2]
  b := [3, 4, 3, 0, 2, 4, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD419 : CertificateDedekindCriterionLists l 419 where
  n := 2
  a' := [108, 125, 213, 350, 73, 413, 364, 410]
  b' := [361, 35, 240, 119, 229, 291, 310, 224, 1]
  k := [416, 233, 130, 218, 94, 66, 200, 155, 1]
  f := [9, 37, 116, 124, 90, 92, 28, 74, 89, 1]
  g := [29, 119, 373, 397, 287, 294, 88, 238, 285, 1]
  h := [130, 1]
  a := [386, 117, 178, 345, 409, 295, 401, 241, 227]
  b := [227, 418, 335, 201, 348, 169, 240, 256, 192]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD695771 : CertificateDedekindCriterionLists l 695771 where
  n := 2
  a' := [239967, 133220, 576705, 227268, 312345, 577455, 476293, 352640]
  b' := [100635, 324916, 18188, 639459, 527824, 299550, 368511, 29849, 501973]
  k := [3349, 3776, 390151, 75696, 251476, 500365, 336499, 416300, 1]
  f := [43097, 170041, 266117, 382953, 335530, 227280, 92031, 46642, 145877, 1]
  g := [61494, 242627, 379715, 546425, 478758, 324299, 131316, 66552, 208148, 1]
  h := [487619, 1]
  a := [333194, 335521, 403633, 70851, 343265, 651814, 119878, 649076, 84492]
  b := [220615, 158484, 249386, 43395, 288144, 315800, 387134, 27725, 611279]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 419, 695771]
  exp := ![1, 1, 1]
  pdgood := [5, 419, 695771]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp419.out
    exact hp695771.out
  a := [57382369991, -314376187886, -277155429494, 970312789286, 224062657608, -809443768034, 50736737312, 204029704664, -51591108840]
  b := [-14710002559, -15563329417, 118607132386, 54428412702, -199405704308, -30666705338, 115804781101, -7437071748, -22466614820, 5159110884]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 419 T_ofList CD419
    exact satisfiesDedekindCriterion_of_certificate_lists T l 695771 T_ofList CD695771

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

end VoightMaximalOrderD10R12

namespace VoightMaximalOrderD10R13

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨913378895261, [1, -3, -13, 20, 30, -40, -15, 27, -3, -4, 1], 1⟩
local notation "l" => [1, -3, -13, 20, 30, -40, -15, 27, -3, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 13, -20, -30, 40, 15, -27, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 13, -20, -30, 40, 15, -27, 3, 4], ![-4, 11, 55, -67, -140, 130, 100, -93, -15, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 13, -20, -30, 40, 15, -27, 3, 4], ![-4, 11, 55, -67, -140, 130, 100, -93, -15, 19], ![-19, 53, 258, -325, -637, 620, 415, -413, -36, 61]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 13, -20, -30, 40, 15, -27, 3, 4], ![-4, 11, 55, -67, -140, 130, 100, -93, -15, 19], ![-19, 53, 258, -325, -637, 620, 415, -413, -36, 61], ![-61, 164, 846, -962, -2155, 1803, 1535, -1232, -230, 208]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 13, -20, -30, 40, 15, -27, 3, 4], ![-4, 11, 55, -67, -140, 130, 100, -93, -15, 19], ![-19, 53, 258, -325, -637, 620, 415, -413, -36, 61], ![-61, 164, 846, -962, -2155, 1803, 1535, -1232, -230, 208], ![-208, 563, 2868, -3314, -7202, 6165, 4923, -4081, -608, 602]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 13, -20, -30, 40, 15, -27, 3, 4], ![-4, 11, 55, -67, -140, 130, 100, -93, -15, 19], ![-19, 53, 258, -325, -637, 620, 415, -413, -36, 61], ![-61, 164, 846, -962, -2155, 1803, 1535, -1232, -230, 208], ![-208, 563, 2868, -3314, -7202, 6165, 4923, -4081, -608, 602], ![-602, 1598, 8389, -9172, -21374, 16878, 15195, -11331, -2275, 1800]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 13, -20, -30, 40, 15, -27, 3, 4], ![-4, 11, 55, -67, -140, 130, 100, -93, -15, 19], ![-19, 53, 258, -325, -637, 620, 415, -413, -36, 61], ![-61, 164, 846, -962, -2155, 1803, 1535, -1232, -230, 208], ![-208, 563, 2868, -3314, -7202, 6165, 4923, -4081, -608, 602], ![-602, 1598, 8389, -9172, -21374, 16878, 15195, -11331, -2275, 1800], ![-1800, 4798, 24998, -27611, -63172, 50626, 43878, -33405, -5931, 4925]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 13, -20, -30, 40, 15, -27, 3, 4], ![-4, 11, 55, -67, -140, 130, 100, -93, -15, 19], ![-19, 53, 258, -325, -637, 620, 415, -413, -36, 61], ![-61, 164, 846, -962, -2155, 1803, 1535, -1232, -230, 208], ![-208, 563, 2868, -3314, -7202, 6165, 4923, -4081, -608, 602], ![-602, 1598, 8389, -9172, -21374, 16878, 15195, -11331, -2275, 1800], ![-1800, 4798, 24998, -27611, -63172, 50626, 43878, -33405, -5931, 4925], ![-4925, 12975, 68823, -73502, -175361, 133828, 124501, -89097, -18630, 13769]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 13, -20, -30, 40, 15, -27, 3, 4], ![-4, 11, 55, -67, -140, 130, 100, -93, -15, 19], ![-19, 53, 258, -325, -637, 620, 415, -413, -36, 61], ![-61, 164, 846, -962, -2155, 1803, 1535, -1232, -230, 208], ![-208, 563, 2868, -3314, -7202, 6165, 4923, -4081, -608, 602], ![-602, 1598, 8389, -9172, -21374, 16878, 15195, -11331, -2275, 1800], ![-1800, 4798, 24998, -27611, -63172, 50626, 43878, -33405, -5931, 4925], ![-4925, 12975, 68823, -73502, -175361, 133828, 124501, -89097, -18630, 13769], ![-13769, 36382, 191972, -206557, -486572, 375399, 340363, -247262, -47790, 36446]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1], [-208, -61, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1], [-208, -61, -19, -4, -1], [-602, -208, -61, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1], [-208, -61, -19, -4, -1], [-602, -208, -61, -19, -4, -1], [-1800, -602, -208, -61, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1], [-208, -61, -19, -4, -1], [-602, -208, -61, -19, -4, -1], [-1800, -602, -208, -61, -19, -4, -1], [-4925, -1800, -602, -208, -61, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-61, -19, -4, -1], [-208, -61, -19, -4, -1], [-602, -208, -61, -19, -4, -1], [-1800, -602, -208, -61, -19, -4, -1], [-4925, -1800, -602, -208, -61, -19, -4, -1], [-13769, -4925, -1800, -602, -208, -61, -19, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 13, -20, -30, 40, 15, -27, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 13, -20, -30, 40, 15, -27, 3, 4], [-4, 11, 55, -67, -140, 130, 100, -93, -15, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 13, -20, -30, 40, 15, -27, 3, 4], [-4, 11, 55, -67, -140, 130, 100, -93, -15, 19], [-19, 53, 258, -325, -637, 620, 415, -413, -36, 61]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 13, -20, -30, 40, 15, -27, 3, 4], [-4, 11, 55, -67, -140, 130, 100, -93, -15, 19], [-19, 53, 258, -325, -637, 620, 415, -413, -36, 61], [-61, 164, 846, -962, -2155, 1803, 1535, -1232, -230, 208]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 13, -20, -30, 40, 15, -27, 3, 4], [-4, 11, 55, -67, -140, 130, 100, -93, -15, 19], [-19, 53, 258, -325, -637, 620, 415, -413, -36, 61], [-61, 164, 846, -962, -2155, 1803, 1535, -1232, -230, 208], [-208, 563, 2868, -3314, -7202, 6165, 4923, -4081, -608, 602]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 13, -20, -30, 40, 15, -27, 3, 4], [-4, 11, 55, -67, -140, 130, 100, -93, -15, 19], [-19, 53, 258, -325, -637, 620, 415, -413, -36, 61], [-61, 164, 846, -962, -2155, 1803, 1535, -1232, -230, 208], [-208, 563, 2868, -3314, -7202, 6165, 4923, -4081, -608, 602], [-602, 1598, 8389, -9172, -21374, 16878, 15195, -11331, -2275, 1800]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 13, -20, -30, 40, 15, -27, 3, 4], [-4, 11, 55, -67, -140, 130, 100, -93, -15, 19], [-19, 53, 258, -325, -637, 620, 415, -413, -36, 61], [-61, 164, 846, -962, -2155, 1803, 1535, -1232, -230, 208], [-208, 563, 2868, -3314, -7202, 6165, 4923, -4081, -608, 602], [-602, 1598, 8389, -9172, -21374, 16878, 15195, -11331, -2275, 1800], [-1800, 4798, 24998, -27611, -63172, 50626, 43878, -33405, -5931, 4925]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 13, -20, -30, 40, 15, -27, 3, 4], [-4, 11, 55, -67, -140, 130, 100, -93, -15, 19], [-19, 53, 258, -325, -637, 620, 415, -413, -36, 61], [-61, 164, 846, -962, -2155, 1803, 1535, -1232, -230, 208], [-208, 563, 2868, -3314, -7202, 6165, 4923, -4081, -608, 602], [-602, 1598, 8389, -9172, -21374, 16878, 15195, -11331, -2275, 1800], [-1800, 4798, 24998, -27611, -63172, 50626, 43878, -33405, -5931, 4925], [-4925, 12975, 68823, -73502, -175361, 133828, 124501, -89097, -18630, 13769]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 13, -20, -30, 40, 15, -27, 3, 4], [-4, 11, 55, -67, -140, 130, 100, -93, -15, 19], [-19, 53, 258, -325, -637, 620, 415, -413, -36, 61], [-61, 164, 846, -962, -2155, 1803, 1535, -1232, -230, 208], [-208, 563, 2868, -3314, -7202, 6165, 4923, -4081, -608, 602], [-602, 1598, 8389, -9172, -21374, 16878, 15195, -11331, -2275, 1800], [-1800, 4798, 24998, -27611, -63172, 50626, 43878, -33405, -5931, 4925], [-4925, 12975, 68823, -73502, -175361, 133828, 124501, -89097, -18630, 13769], [-13769, 36382, 191972, -206557, -486572, 375399, 340363, -247262, -47790, 36446]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp31 : Fact (Nat.Prime 31) := fact_iff.2 (by norm_num)
instance hp135778043 : Fact (Nat.Prime 135778043) := fact_iff.2 (by norm_num)

def CD7 : CertificateDedekindCriterionLists l 7 where
  n := 2
  a' := [6, 0, 4, 1, 5, 4, 2, 1]
  b' := [6, 4, 4, 2, 0, 0, 3, 3, 3]
  k := [2, 3, 1, 0, 2, 6, 0, 0, 1]
  f := [2, 3, 3, -2, -2, 9, 7, -3, 4, 2]
  g := [3, 3, 1, 1, 3, 4, 6, 0, 5, 1]
  h := [5, 1]
  a := [1, 4, 0, 5, 5, 4, 5, 5]
  b := [2, 6, 0, 0, 5, 6, 6, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD31 : CertificateDedekindCriterionLists l 31 where
  n := 2
  a' := [3, 28, 1, 17, 4, 15, 20]
  b' := [12, 27, 1, 22, 4, 21, 4, 13]
  k := [14, 7, 28, 12, 24, 16, 1]
  f := [11, 27, 24, 18, 25, 26, 15, 8, 5, 1]
  g := [18, 24, 11, 17, 23, 14, 7, 6, 1]
  h := [19, 21, 1]
  a := [2, 13, 17, 29, 15, 15, 3, 2]
  b := [4, 13, 20, 11, 11, 16, 5, 30, 29]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD135778043 : CertificateDedekindCriterionLists l 135778043 where
  n := 2
  a' := [97898109, 40235714, 76194029, 41395764, 110167180, 45598672, 127708691, 43489756]
  b' := [37372387, 38764594, 132317665, 75682118, 135745269, 19818682, 21081732, 24390424, 70600051]
  k := [82262601, 71650894, 1794377, 36576136, 29449459, 13971286, 30236515, 47633469, 1]
  f := [8804648, 35028954, 24144192, 10926190, 30479107, 8937008, 24414084, 22345433, 29766832, 1]
  g := [27125389, 107917318, 74383505, 33661441, 93900134, 27533162, 75214991, 68841883, 91705754, 1]
  h := [44072285, 1]
  a := [7084216, 128416504, 66073688, 37774537, 60780928, 69435826, 95742196, 34610650, 64739228]
  b := [82731750, 2638614, 40784916, 128933228, 64036348, 94454574, 20710350, 5009981, 71038815]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![7, 31, 135778043]
  exp := ![1, 1, 1]
  pdgood := [7, 31, 135778043]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp7.out
    exact hp31.out
    exact hp135778043.out
  a := [-372864155800, -3779557125340, 4876888948147, 19862616934080, -11785073182486, -20978093167850, 9936442005280, 4104385525300, -1835281946000]
  b := [-134109330377, 275292643954, 1952875261381, -1147136066949, -4898170239341, 1703114062028, 3295121892459, -1203866296500, -483849830370, 183528194600]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T l 31 T_ofList CD31
    exact satisfiesDedekindCriterion_of_certificate_lists T l 135778043 T_ofList CD135778043

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

end VoightMaximalOrderD10R13

namespace VoightMaximalOrderD10R14

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨925108450304, [-1, -2, 12, 14, -29, -22, 24, 12, -8, -2, 1], 1⟩
local notation "l" => [-1, -2, 12, 14, -29, -22, 24, 12, -8, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -14, 29, 22, -24, -12, 8, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -14, 29, 22, -24, -12, 8, 2], ![2, 5, -22, -40, 44, 73, -26, -48, 4, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -14, 29, 22, -24, -12, 8, 2], ![2, 5, -22, -40, 44, 73, -26, -48, 4, 12], ![12, 26, -139, -190, 308, 308, -215, -170, 48, 28]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -14, 29, 22, -24, -12, 8, 2], ![2, 5, -22, -40, 44, 73, -26, -48, 4, 12], ![12, 26, -139, -190, 308, 308, -215, -170, 48, 28], ![28, 68, -310, -531, 622, 924, -364, -551, 54, 104]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -14, 29, 22, -24, -12, 8, 2], ![2, 5, -22, -40, 44, 73, -26, -48, 4, 12], ![12, 26, -139, -190, 308, 308, -215, -170, 48, 28], ![28, 68, -310, -531, 622, 924, -364, -551, 54, 104], ![104, 236, -1180, -1766, 2485, 2910, -1572, -1612, 281, 262]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -14, 29, 22, -24, -12, 8, 2], ![2, 5, -22, -40, 44, 73, -26, -48, 4, 12], ![12, 26, -139, -190, 308, 308, -215, -170, 48, 28], ![28, 68, -310, -531, 622, 924, -364, -551, 54, 104], ![104, 236, -1180, -1766, 2485, 2910, -1572, -1612, 281, 262], ![262, 628, -2908, -4848, 5832, 8249, -3378, -4716, 484, 805]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -14, 29, 22, -24, -12, 8, 2], ![2, 5, -22, -40, 44, 73, -26, -48, 4, 12], ![12, 26, -139, -190, 308, 308, -215, -170, 48, 28], ![28, 68, -310, -531, 622, 924, -364, -551, 54, 104], ![104, 236, -1180, -1766, 2485, 2910, -1572, -1612, 281, 262], ![262, 628, -2908, -4848, 5832, 8249, -3378, -4716, 484, 805], ![805, 1872, -9032, -14178, 18497, 23542, -11071, -13038, 1724, 2094]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -14, 29, 22, -24, -12, 8, 2], ![2, 5, -22, -40, 44, 73, -26, -48, 4, 12], ![12, 26, -139, -190, 308, 308, -215, -170, 48, 28], ![28, 68, -310, -531, 622, 924, -364, -551, 54, 104], ![104, 236, -1180, -1766, 2485, 2910, -1572, -1612, 281, 262], ![262, 628, -2908, -4848, 5832, 8249, -3378, -4716, 484, 805], ![805, 1872, -9032, -14178, 18497, 23542, -11071, -13038, 1724, 2094], ![2094, 4993, -23256, -38348, 46548, 64565, -26714, -36199, 3714, 5912]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -12, -14, 29, 22, -24, -12, 8, 2], ![2, 5, -22, -40, 44, 73, -26, -48, 4, 12], ![12, 26, -139, -190, 308, 308, -215, -170, 48, 28], ![28, 68, -310, -531, 622, 924, -364, -551, 54, 104], ![104, 236, -1180, -1766, 2485, 2910, -1572, -1612, 281, 262], ![262, 628, -2908, -4848, 5832, 8249, -3378, -4716, 484, 805], ![805, 1872, -9032, -14178, 18497, 23542, -11071, -13038, 1724, 2094], ![2094, 4993, -23256, -38348, 46548, 64565, -26714, -36199, 3714, 5912], ![5912, 13918, -65951, -106024, 133100, 176612, -77323, -97658, 11097, 15538]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-12, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-12, -2, -1], [-28, -12, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-12, -2, -1], [-28, -12, -2, -1], [-104, -28, -12, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-12, -2, -1], [-28, -12, -2, -1], [-104, -28, -12, -2, -1], [-262, -104, -28, -12, -2, -1]], ![[], [], [], [-1], [-2, -1], [-12, -2, -1], [-28, -12, -2, -1], [-104, -28, -12, -2, -1], [-262, -104, -28, -12, -2, -1], [-805, -262, -104, -28, -12, -2, -1]], ![[], [], [-1], [-2, -1], [-12, -2, -1], [-28, -12, -2, -1], [-104, -28, -12, -2, -1], [-262, -104, -28, -12, -2, -1], [-805, -262, -104, -28, -12, -2, -1], [-2094, -805, -262, -104, -28, -12, -2, -1]], ![[], [-1], [-2, -1], [-12, -2, -1], [-28, -12, -2, -1], [-104, -28, -12, -2, -1], [-262, -104, -28, -12, -2, -1], [-805, -262, -104, -28, -12, -2, -1], [-2094, -805, -262, -104, -28, -12, -2, -1], [-5912, -2094, -805, -262, -104, -28, -12, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -14, 29, 22, -24, -12, 8, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -14, 29, 22, -24, -12, 8, 2], [2, 5, -22, -40, 44, 73, -26, -48, 4, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -14, 29, 22, -24, -12, 8, 2], [2, 5, -22, -40, 44, 73, -26, -48, 4, 12], [12, 26, -139, -190, 308, 308, -215, -170, 48, 28]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -14, 29, 22, -24, -12, 8, 2], [2, 5, -22, -40, 44, 73, -26, -48, 4, 12], [12, 26, -139, -190, 308, 308, -215, -170, 48, 28], [28, 68, -310, -531, 622, 924, -364, -551, 54, 104]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -14, 29, 22, -24, -12, 8, 2], [2, 5, -22, -40, 44, 73, -26, -48, 4, 12], [12, 26, -139, -190, 308, 308, -215, -170, 48, 28], [28, 68, -310, -531, 622, 924, -364, -551, 54, 104], [104, 236, -1180, -1766, 2485, 2910, -1572, -1612, 281, 262]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -14, 29, 22, -24, -12, 8, 2], [2, 5, -22, -40, 44, 73, -26, -48, 4, 12], [12, 26, -139, -190, 308, 308, -215, -170, 48, 28], [28, 68, -310, -531, 622, 924, -364, -551, 54, 104], [104, 236, -1180, -1766, 2485, 2910, -1572, -1612, 281, 262], [262, 628, -2908, -4848, 5832, 8249, -3378, -4716, 484, 805]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -14, 29, 22, -24, -12, 8, 2], [2, 5, -22, -40, 44, 73, -26, -48, 4, 12], [12, 26, -139, -190, 308, 308, -215, -170, 48, 28], [28, 68, -310, -531, 622, 924, -364, -551, 54, 104], [104, 236, -1180, -1766, 2485, 2910, -1572, -1612, 281, 262], [262, 628, -2908, -4848, 5832, 8249, -3378, -4716, 484, 805], [805, 1872, -9032, -14178, 18497, 23542, -11071, -13038, 1724, 2094]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -14, 29, 22, -24, -12, 8, 2], [2, 5, -22, -40, 44, 73, -26, -48, 4, 12], [12, 26, -139, -190, 308, 308, -215, -170, 48, 28], [28, 68, -310, -531, 622, 924, -364, -551, 54, 104], [104, 236, -1180, -1766, 2485, 2910, -1572, -1612, 281, 262], [262, 628, -2908, -4848, 5832, 8249, -3378, -4716, 484, 805], [805, 1872, -9032, -14178, 18497, 23542, -11071, -13038, 1724, 2094], [2094, 4993, -23256, -38348, 46548, 64565, -26714, -36199, 3714, 5912]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -12, -14, 29, 22, -24, -12, 8, 2], [2, 5, -22, -40, 44, 73, -26, -48, 4, 12], [12, 26, -139, -190, 308, 308, -215, -170, 48, 28], [28, 68, -310, -531, 622, 924, -364, -551, 54, 104], [104, 236, -1180, -1766, 2485, 2910, -1572, -1612, 281, 262], [262, 628, -2908, -4848, 5832, 8249, -3378, -4716, 484, 805], [805, 1872, -9032, -14178, 18497, 23542, -11071, -13038, 1724, 2094], [2094, 4993, -23256, -38348, 46548, 64565, -26714, -36199, 3714, 5912], [5912, 13918, -65951, -106024, 133100, 176612, -77323, -97658, 11097, 15538]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp93629 : Fact (Nat.Prime 93629) := fact_iff.2 (by norm_num)
instance hp9649 : Fact (Nat.Prime 9649) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 1]
  b' := [1, 1, 0, 1]
  k := [1]
  f := [1, 1, -5, -7, 15, 12, -12, -5, 4, 1]
  g := [1, 0, 1, 0, 0, 1]
  h := [1, 0, 1, 0, 0, 1]
  a := [0, 0, 0, 1, 1]
  b := [1, 0, 1, 1, 1, 0, 1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD93629 : CertificateDedekindCriterionLists l 93629 where
  n := 2
  a' := [27987, 76191, 46374, 87069, 62772, 52338, 16520, 92696]
  b' := [6721, 55317, 11237, 74585, 6667, 30021, 46537, 17408, 62523]
  k := [56309, 29330, 34560, 67002, 52868, 32130, 75874, 69275, 1]
  f := [8693, 10064, 8215, 7990, 11496, 11157, 4762, 8403, 10593, 1]
  g := [66846, 77383, 63164, 61435, 88395, 85786, 36611, 64613, 81451, 1]
  h := [12176, 1]
  a := [22802, 83784, 34706, 55812, 85922, 3847, 37035, 64535, 42127]
  b := [18217, 25093, 41493, 70148, 78999, 41973, 67800, 77911, 51502]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD9649 : CertificateDedekindCriterionLists l 9649 where
  n := 2
  a' := [3734, 9489, 471, 5798, 7009, 2941, 9040, 5479]
  b' := [5368, 1580, 6299, 2129, 5596, 6820, 3829, 4854, 6896]
  k := [3670, 4885, 2607, 9019, 9451, 5316, 4761, 896, 1]
  f := [2049, 599, 1784, 5393, 1365, 5597, 54, 7356, 427, 1]
  g := [2149, 628, 1871, 5656, 1431, 5870, 56, 7715, 447, 1]
  h := [9200, 1]
  a := [5289, 2411, 3403, 1214, 6883, 6687, 2645, 3299, 7489]
  b := [9370, 3937, 4942, 3352, 230, 3014, 4672, 1746, 2160]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 93629, 9649]
  exp := ![1, 1, 1]
  pdgood := [2, 93629, 9649]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp93629.out
    exact hp9649.out
  a := [-637232040, -15350511144, 17084326746, 55667840548, -33664507606, -51966601780, 22519710304, 13113570814, -5322683780]
  b := [-584810201, 1294765200, 6241123710, -5479392786, -12164275764, 6494949708, 7574334063, -3032945635, -1417810757, 532268378]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 93629 T_ofList CD93629
    exact satisfiesDedekindCriterion_of_certificate_lists T l 9649 T_ofList CD9649

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

end VoightMaximalOrderD10R14

end TraceEuclidean
