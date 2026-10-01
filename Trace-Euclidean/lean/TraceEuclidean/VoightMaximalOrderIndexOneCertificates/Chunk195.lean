import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk191
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

namespace VoightMaximalOrderD10R286

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4010648855552, [1, 6, 5, -22, -28, 22, 31, -6, -11, 0, 1], 1⟩
local notation "l" => [1, 6, 5, -22, -28, 22, 31, -6, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -5, 22, 28, -22, -31, 6, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -5, 22, 28, -22, -31, 6, 11, 0], ![0, -1, -6, -5, 22, 28, -22, -31, 6, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -5, 22, 28, -22, -31, 6, 11, 0], ![0, -1, -6, -5, 22, 28, -22, -31, 6, 11], ![-11, -66, -56, 236, 303, -220, -313, 44, 90, 6]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -5, 22, 28, -22, -31, 6, 11, 0], ![0, -1, -6, -5, 22, 28, -22, -31, 6, 11], ![-11, -66, -56, 236, 303, -220, -313, 44, 90, 6], ![-6, -47, -96, 76, 404, 171, -406, -277, 110, 90]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -5, 22, 28, -22, -31, 6, 11, 0], ![0, -1, -6, -5, 22, 28, -22, -31, 6, 11], ![-11, -66, -56, 236, 303, -220, -313, 44, 90, 6], ![-6, -47, -96, 76, 404, 171, -406, -277, 110, 90], ![-90, -546, -497, 1884, 2596, -1576, -2619, 134, 713, 110]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -5, 22, 28, -22, -31, 6, 11, 0], ![0, -1, -6, -5, 22, 28, -22, -31, 6, 11], ![-11, -66, -56, 236, 303, -220, -313, 44, 90, 6], ![-6, -47, -96, 76, 404, 171, -406, -277, 110, 90], ![-90, -546, -497, 1884, 2596, -1576, -2619, 134, 713, 110], ![-110, -750, -1096, 1923, 4964, 176, -4986, -1959, 1344, 713]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -5, 22, 28, -22, -31, 6, 11, 0], ![0, -1, -6, -5, 22, 28, -22, -31, 6, 11], ![-11, -66, -56, 236, 303, -220, -313, 44, 90, 6], ![-6, -47, -96, 76, 404, 171, -406, -277, 110, 90], ![-90, -546, -497, 1884, 2596, -1576, -2619, 134, 713, 110], ![-110, -750, -1096, 1923, 4964, 176, -4986, -1959, 1344, 713], ![-713, -4388, -4315, 14590, 21887, -10722, -21927, -708, 5884, 1344]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -5, 22, 28, -22, -31, 6, 11, 0], ![0, -1, -6, -5, 22, 28, -22, -31, 6, 11], ![-11, -66, -56, 236, 303, -220, -313, 44, 90, 6], ![-6, -47, -96, 76, 404, 171, -406, -277, 110, 90], ![-90, -546, -497, 1884, 2596, -1576, -2619, 134, 713, 110], ![-110, -750, -1096, 1923, 4964, 176, -4986, -1959, 1344, 713], ![-713, -4388, -4315, 14590, 21887, -10722, -21927, -708, 5884, 1344], ![-1344, -8777, -11108, 25253, 52222, -7681, -52386, -13863, 14076, 5884]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -6, -5, 22, 28, -22, -31, 6, 11, 0], ![0, -1, -6, -5, 22, 28, -22, -31, 6, 11], ![-11, -66, -56, 236, 303, -220, -313, 44, 90, 6], ![-6, -47, -96, 76, 404, 171, -406, -277, 110, 90], ![-90, -546, -497, 1884, 2596, -1576, -2619, 134, 713, 110], ![-110, -750, -1096, 1923, 4964, 176, -4986, -1959, 1344, 713], ![-713, -4388, -4315, 14590, 21887, -10722, -21927, -708, 5884, 1344], ![-1344, -8777, -11108, 25253, 52222, -7681, -52386, -13863, 14076, 5884], ![-5884, -36648, -38197, 118340, 190005, -77226, -190085, -17082, 50861, 14076]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-6, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-6, -11, 0, -1], [-90, -6, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [-6, -11, 0, -1], [-90, -6, -11, 0, -1], [-110, -90, -6, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [-6, -11, 0, -1], [-90, -6, -11, 0, -1], [-110, -90, -6, -11, 0, -1], [-713, -110, -90, -6, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [-6, -11, 0, -1], [-90, -6, -11, 0, -1], [-110, -90, -6, -11, 0, -1], [-713, -110, -90, -6, -11, 0, -1], [-1344, -713, -110, -90, -6, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [-6, -11, 0, -1], [-90, -6, -11, 0, -1], [-110, -90, -6, -11, 0, -1], [-713, -110, -90, -6, -11, 0, -1], [-1344, -713, -110, -90, -6, -11, 0, -1], [-5884, -1344, -713, -110, -90, -6, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -5, 22, 28, -22, -31, 6, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -5, 22, 28, -22, -31, 6, 11, 0], [0, -1, -6, -5, 22, 28, -22, -31, 6, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -5, 22, 28, -22, -31, 6, 11, 0], [0, -1, -6, -5, 22, 28, -22, -31, 6, 11], [-11, -66, -56, 236, 303, -220, -313, 44, 90, 6]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -5, 22, 28, -22, -31, 6, 11, 0], [0, -1, -6, -5, 22, 28, -22, -31, 6, 11], [-11, -66, -56, 236, 303, -220, -313, 44, 90, 6], [-6, -47, -96, 76, 404, 171, -406, -277, 110, 90]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -5, 22, 28, -22, -31, 6, 11, 0], [0, -1, -6, -5, 22, 28, -22, -31, 6, 11], [-11, -66, -56, 236, 303, -220, -313, 44, 90, 6], [-6, -47, -96, 76, 404, 171, -406, -277, 110, 90], [-90, -546, -497, 1884, 2596, -1576, -2619, 134, 713, 110]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -5, 22, 28, -22, -31, 6, 11, 0], [0, -1, -6, -5, 22, 28, -22, -31, 6, 11], [-11, -66, -56, 236, 303, -220, -313, 44, 90, 6], [-6, -47, -96, 76, 404, 171, -406, -277, 110, 90], [-90, -546, -497, 1884, 2596, -1576, -2619, 134, 713, 110], [-110, -750, -1096, 1923, 4964, 176, -4986, -1959, 1344, 713]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -5, 22, 28, -22, -31, 6, 11, 0], [0, -1, -6, -5, 22, 28, -22, -31, 6, 11], [-11, -66, -56, 236, 303, -220, -313, 44, 90, 6], [-6, -47, -96, 76, 404, 171, -406, -277, 110, 90], [-90, -546, -497, 1884, 2596, -1576, -2619, 134, 713, 110], [-110, -750, -1096, 1923, 4964, 176, -4986, -1959, 1344, 713], [-713, -4388, -4315, 14590, 21887, -10722, -21927, -708, 5884, 1344]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -5, 22, 28, -22, -31, 6, 11, 0], [0, -1, -6, -5, 22, 28, -22, -31, 6, 11], [-11, -66, -56, 236, 303, -220, -313, 44, 90, 6], [-6, -47, -96, 76, 404, 171, -406, -277, 110, 90], [-90, -546, -497, 1884, 2596, -1576, -2619, 134, 713, 110], [-110, -750, -1096, 1923, 4964, 176, -4986, -1959, 1344, 713], [-713, -4388, -4315, 14590, 21887, -10722, -21927, -708, 5884, 1344], [-1344, -8777, -11108, 25253, 52222, -7681, -52386, -13863, 14076, 5884]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -6, -5, 22, 28, -22, -31, 6, 11, 0], [0, -1, -6, -5, 22, 28, -22, -31, 6, 11], [-11, -66, -56, 236, 303, -220, -313, 44, 90, 6], [-6, -47, -96, 76, 404, 171, -406, -277, 110, 90], [-90, -546, -497, 1884, 2596, -1576, -2619, 134, 713, 110], [-110, -750, -1096, 1923, 4964, 176, -4986, -1959, 1344, 713], [-713, -4388, -4315, 14590, 21887, -10722, -21927, -708, 5884, 1344], [-1344, -8777, -11108, 25253, 52222, -7681, -52386, -13863, 14076, 5884], [-5884, -36648, -38197, 118340, 190005, -77226, -190085, -17082, 50861, 14076]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp1151 : Fact (Nat.Prime 1151) := fact_iff.2 (by norm_num)
instance hp3402823 : Fact (Nat.Prime 3402823) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 1]
  b' := [0, 1, 1, 1]
  k := [1]
  f := [0, -2, -2, 12, 16, -9, -14, 4, 7, 1]
  g := [1, 1, 0, 1, 1, 1]
  h := [1, 1, 0, 1, 1, 1]
  a := [0, 0, 0, 0, 1]
  b := [1, 1, 1, 0, 0, 1, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1151 : CertificateDedekindCriterionLists l 1151 where
  n := 2
  a' := [499, 418, 188, 368, 423, 778, 483, 799]
  b' := [425, 104, 381, 84, 628, 664, 85, 973, 167]
  k := [442, 791, 485, 440, 565, 913, 752, 1048, 1]
  f := [487, 174, 557, 69, 102, 528, 277, 342, 286, 1]
  g := [894, 318, 1022, 125, 187, 969, 507, 627, 524, 1]
  h := [627, 1]
  a := [650, 194, 565, 931, 474, 109, 405, 989, 20]
  b := [1066, 707, 644, 491, 163, 1065, 95, 318, 1131]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3402823 : CertificateDedekindCriterionLists l 3402823 where
  n := 2
  a' := [1110014, 1172844, 1105583, 2316150, 2601336, 3039713, 2630810, 2577968]
  b' := [2868584, 1801324, 1568831, 2273325, 940444, 141863, 1189030, 140924, 469742]
  k := [349794, 1069363, 582862, 64017, 619156, 1609304, 1442478, 2101972, 1]
  f := [1514686, 1790848, 599024, 157896, 705874, 555297, 2162556, 1116261, 726382, 1]
  g := [2191567, 2591139, 866714, 228456, 1021314, 803447, 3128956, 1615093, 1050986, 1]
  h := [2351837, 1]
  a := [634564, 1372328, 2917704, 1609594, 474759, 3124368, 536331, 1398597, 2131155]
  b := [1865005, 1828245, 472726, 841618, 2807059, 988564, 1507915, 3137238, 1271668]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 1151, 3402823]
  exp := ![1, 1, 1]
  pdgood := [2, 1151, 3402823]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp1151.out
    exact hp3402823.out
  a := [-664632785738, 716224752538, 5246576847126, -1476527094766, -7971808650338, 302984959412, 3667387971472, 174307344420, -426093548940]
  b := [112077680714, 358465859125, -401382182965, -1330118377508, 395817430221, 1338820430691, -68647718978, -460479377914, -17430734442, 42609354894]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1151 T_ofList CD1151
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3402823 T_ofList CD3402823

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

end VoightMaximalOrderD10R286

namespace VoightMaximalOrderD10R293

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4101511878125, [1, -9, 13, 38, -31, -45, 24, 20, -8, -3, 1], 1⟩
local notation "l" => [1, -9, 13, 38, -31, -45, 24, 20, -8, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, -13, -38, 31, 45, -24, -20, 8, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, -13, -38, 31, 45, -24, -20, 8, 3], ![-3, 26, -30, -127, 55, 166, -27, -84, 4, 17]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, -13, -38, 31, 45, -24, -20, 8, 3], ![-3, 26, -30, -127, 55, 166, -27, -84, 4, 17], ![-17, 150, -195, -676, 400, 820, -242, -367, 52, 55]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, -13, -38, 31, 45, -24, -20, 8, 3], ![-3, 26, -30, -127, 55, 166, -27, -84, 4, 17], ![-17, 150, -195, -676, 400, 820, -242, -367, 52, 55], ![-55, 478, -565, -2285, 1029, 2875, -500, -1342, 73, 217]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, -13, -38, 31, 45, -24, -20, 8, 3], ![-3, 26, -30, -127, 55, 166, -27, -84, 4, 17], ![-17, 150, -195, -676, 400, 820, -242, -367, 52, 55], ![-55, 478, -565, -2285, 1029, 2875, -500, -1342, 73, 217], ![-217, 1898, -2343, -8811, 4442, 10794, -2333, -4840, 394, 724]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, -13, -38, 31, 45, -24, -20, 8, 3], ![-3, 26, -30, -127, 55, 166, -27, -84, 4, 17], ![-17, 150, -195, -676, 400, 820, -242, -367, 52, 55], ![-55, 478, -565, -2285, 1029, 2875, -500, -1342, 73, 217], ![-217, 1898, -2343, -8811, 4442, 10794, -2333, -4840, 394, 724], ![-724, 6299, -7514, -29855, 13633, 37022, -6582, -16813, 952, 2566]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, -13, -38, 31, 45, -24, -20, 8, 3], ![-3, 26, -30, -127, 55, 166, -27, -84, 4, 17], ![-17, 150, -195, -676, 400, 820, -242, -367, 52, 55], ![-55, 478, -565, -2285, 1029, 2875, -500, -1342, 73, 217], ![-217, 1898, -2343, -8811, 4442, 10794, -2333, -4840, 394, 724], ![-724, 6299, -7514, -29855, 13633, 37022, -6582, -16813, 952, 2566], ![-2566, 22370, -27059, -105022, 49691, 129103, -24562, -57902, 3715, 8650]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, -13, -38, 31, 45, -24, -20, 8, 3], ![-3, 26, -30, -127, 55, 166, -27, -84, 4, 17], ![-17, 150, -195, -676, 400, 820, -242, -367, 52, 55], ![-55, 478, -565, -2285, 1029, 2875, -500, -1342, 73, 217], ![-217, 1898, -2343, -8811, 4442, 10794, -2333, -4840, 394, 724], ![-724, 6299, -7514, -29855, 13633, 37022, -6582, -16813, 952, 2566], ![-2566, 22370, -27059, -105022, 49691, 129103, -24562, -57902, 3715, 8650], ![-8650, 75284, -90080, -355759, 163128, 438941, -78497, -197562, 11298, 29665]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, -13, -38, 31, 45, -24, -20, 8, 3], ![-3, 26, -30, -127, 55, 166, -27, -84, 4, 17], ![-17, 150, -195, -676, 400, 820, -242, -367, 52, 55], ![-55, 478, -565, -2285, 1029, 2875, -500, -1342, 73, 217], ![-217, 1898, -2343, -8811, 4442, 10794, -2333, -4840, 394, 724], ![-724, 6299, -7514, -29855, 13633, 37022, -6582, -16813, 952, 2566], ![-2566, 22370, -27059, -105022, 49691, 129103, -24562, -57902, 3715, 8650], ![-8650, 75284, -90080, -355759, 163128, 438941, -78497, -197562, 11298, 29665], ![-29665, 258335, -310361, -1217350, 563856, 1498053, -273019, -671797, 39758, 100293]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-55, -17, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-55, -17, -3, -1], [-217, -55, -17, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-55, -17, -3, -1], [-217, -55, -17, -3, -1], [-724, -217, -55, -17, -3, -1]], ![[], [], [], [-1], [-3, -1], [-17, -3, -1], [-55, -17, -3, -1], [-217, -55, -17, -3, -1], [-724, -217, -55, -17, -3, -1], [-2566, -724, -217, -55, -17, -3, -1]], ![[], [], [-1], [-3, -1], [-17, -3, -1], [-55, -17, -3, -1], [-217, -55, -17, -3, -1], [-724, -217, -55, -17, -3, -1], [-2566, -724, -217, -55, -17, -3, -1], [-8650, -2566, -724, -217, -55, -17, -3, -1]], ![[], [-1], [-3, -1], [-17, -3, -1], [-55, -17, -3, -1], [-217, -55, -17, -3, -1], [-724, -217, -55, -17, -3, -1], [-2566, -724, -217, -55, -17, -3, -1], [-8650, -2566, -724, -217, -55, -17, -3, -1], [-29665, -8650, -2566, -724, -217, -55, -17, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, -13, -38, 31, 45, -24, -20, 8, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, -13, -38, 31, 45, -24, -20, 8, 3], [-3, 26, -30, -127, 55, 166, -27, -84, 4, 17]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, -13, -38, 31, 45, -24, -20, 8, 3], [-3, 26, -30, -127, 55, 166, -27, -84, 4, 17], [-17, 150, -195, -676, 400, 820, -242, -367, 52, 55]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, -13, -38, 31, 45, -24, -20, 8, 3], [-3, 26, -30, -127, 55, 166, -27, -84, 4, 17], [-17, 150, -195, -676, 400, 820, -242, -367, 52, 55], [-55, 478, -565, -2285, 1029, 2875, -500, -1342, 73, 217]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, -13, -38, 31, 45, -24, -20, 8, 3], [-3, 26, -30, -127, 55, 166, -27, -84, 4, 17], [-17, 150, -195, -676, 400, 820, -242, -367, 52, 55], [-55, 478, -565, -2285, 1029, 2875, -500, -1342, 73, 217], [-217, 1898, -2343, -8811, 4442, 10794, -2333, -4840, 394, 724]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, -13, -38, 31, 45, -24, -20, 8, 3], [-3, 26, -30, -127, 55, 166, -27, -84, 4, 17], [-17, 150, -195, -676, 400, 820, -242, -367, 52, 55], [-55, 478, -565, -2285, 1029, 2875, -500, -1342, 73, 217], [-217, 1898, -2343, -8811, 4442, 10794, -2333, -4840, 394, 724], [-724, 6299, -7514, -29855, 13633, 37022, -6582, -16813, 952, 2566]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, -13, -38, 31, 45, -24, -20, 8, 3], [-3, 26, -30, -127, 55, 166, -27, -84, 4, 17], [-17, 150, -195, -676, 400, 820, -242, -367, 52, 55], [-55, 478, -565, -2285, 1029, 2875, -500, -1342, 73, 217], [-217, 1898, -2343, -8811, 4442, 10794, -2333, -4840, 394, 724], [-724, 6299, -7514, -29855, 13633, 37022, -6582, -16813, 952, 2566], [-2566, 22370, -27059, -105022, 49691, 129103, -24562, -57902, 3715, 8650]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, -13, -38, 31, 45, -24, -20, 8, 3], [-3, 26, -30, -127, 55, 166, -27, -84, 4, 17], [-17, 150, -195, -676, 400, 820, -242, -367, 52, 55], [-55, 478, -565, -2285, 1029, 2875, -500, -1342, 73, 217], [-217, 1898, -2343, -8811, 4442, 10794, -2333, -4840, 394, 724], [-724, 6299, -7514, -29855, 13633, 37022, -6582, -16813, 952, 2566], [-2566, 22370, -27059, -105022, 49691, 129103, -24562, -57902, 3715, 8650], [-8650, 75284, -90080, -355759, 163128, 438941, -78497, -197562, 11298, 29665]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, -13, -38, 31, 45, -24, -20, 8, 3], [-3, 26, -30, -127, 55, 166, -27, -84, 4, 17], [-17, 150, -195, -676, 400, 820, -242, -367, 52, 55], [-55, 478, -565, -2285, 1029, 2875, -500, -1342, 73, 217], [-217, 1898, -2343, -8811, 4442, 10794, -2333, -4840, 394, 724], [-724, 6299, -7514, -29855, 13633, 37022, -6582, -16813, 952, 2566], [-2566, 22370, -27059, -105022, 49691, 129103, -24562, -57902, 3715, 8650], [-8650, 75284, -90080, -355759, 163128, 438941, -78497, -197562, 11298, 29665], [-29665, 258335, -310361, -1217350, 563856, 1498053, -273019, -671797, 39758, 100293]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp79 : Fact (Nat.Prime 79) := fact_iff.2 (by norm_num)
instance hp89 : Fact (Nat.Prime 89) := fact_iff.2 (by norm_num)
instance hp186671 : Fact (Nat.Prime 186671) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 3, 4]
  b' := [4, 3, 2, 3, 4]
  k := [1]
  f := [0, 3, 0, -4, 11, 13, -1, -2, 3, 1]
  g := [1, 3, 2, 3, 1, 1]
  h := [1, 3, 2, 3, 1, 1]
  a := [1, 4, 2, 0, 4]
  b := [1, 4, 4, 0, 4, 0, 1, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD79 : CertificateDedekindCriterionLists l 79 where
  n := 2
  a' := [50, 38, 3, 49, 21, 46, 52, 51]
  b' := [25, 46, 71, 67, 36, 35, 36, 53, 47]
  k := [25, 78, 26, 4, 36, 74, 66, 44, 1]
  f := [1, 2, 4, 2, 6, 8, 5, 12, 13, 1]
  g := [5, 9, 20, 11, 27, 35, 24, 59, 60, 1]
  h := [16, 1]
  a := [75, 21, 21, 25, 16, 11, 11, 38, 7]
  b := [1, 43, 4, 27, 23, 5, 60, 54, 72]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD89 : CertificateDedekindCriterionLists l 89 where
  n := 2
  a' := [5, 31, 72, 62, 17, 27, 64, 58]
  b' := [58, 21, 41, 40, 44, 47, 56, 65, 43]
  k := [4, 69, 45, 56, 9, 77, 12, 87, 1]
  f := [43, 8, 1, 8, 4, 8, 35, 7, 21, 1]
  g := [87, 14, 2, 17, 7, 15, 71, 13, 42, 1]
  h := [44, 1]
  a := [3, 26, 83, 86, 21, 45, 5, 55, 20]
  b := [64, 40, 9, 5, 42, 83, 6, 9, 69]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD186671 : CertificateDedekindCriterionLists l 186671 where
  n := 2
  a' := [168381, 79496, 11983, 16882, 57792, 82025, 120015, 120941]
  b' := [43387, 2638, 144658, 167322, 140960, 73312, 139608, 82046, 69527]
  k := [5775, 56276, 30390, 144066, 183761, 38416, 59629, 84977, 1]
  f := [71534, 72639, 135286, 129879, 20927, 107473, 67730, 126711, 32817, 1]
  g := [92615, 94045, 175154, 168153, 27093, 139145, 87689, 164052, 42487, 1]
  h := [144181, 1]
  a := [80285, 34232, 178612, 31768, 49754, 122031, 144895, 145410, 42409]
  b := [28093, 11520, 173022, 74146, 78954, 32050, 104803, 20104, 144262]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 79, 89, 186671]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 79, 89, 186671]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp79.out
    exact hp89.out
    exact hp186671.out
  a := [-131885115361, -261500157066, 501666901005, 658337062350, -535414650694, -458814774628, 231005936901, 95464703438, -36418528440]
  b := [-15383059374, 58389593051, 100569162844, -121010029793, -138649253408, 88839669628, 66979872246, -29013517941, -10639026197, 3641852844]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 79 T_ofList CD79
    exact satisfiesDedekindCriterion_of_certificate_lists T l 89 T_ofList CD89
    exact satisfiesDedekindCriterion_of_certificate_lists T l 186671 T_ofList CD186671

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

end VoightMaximalOrderD10R293

namespace VoightMaximalOrderD10R297

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4117404111872, [5, -14, -22, 48, 27, -56, -7, 26, -3, -4, 1], 1⟩
local notation "l" => [5, -14, -22, 48, 27, -56, -7, 26, -3, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 14, 22, -48, -27, 56, 7, -26, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 14, 22, -48, -27, 56, 7, -26, 3, 4], ![-20, 51, 102, -170, -156, 197, 84, -97, -14, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 14, 22, -48, -27, 56, 7, -26, 3, 4], ![-20, 51, 102, -170, -156, 197, 84, -97, -14, 19], ![-95, 246, 469, -810, -683, 908, 330, -410, -40, 62]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 14, 22, -48, -27, 56, 7, -26, 3, 4], ![-20, 51, 102, -170, -156, 197, 84, -97, -14, 19], ![-95, 246, 469, -810, -683, 908, 330, -410, -40, 62], ![-310, 773, 1610, -2507, -2484, 2789, 1342, -1282, -224, 208]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 14, 22, -48, -27, 56, 7, -26, 3, 4], ![-20, 51, 102, -170, -156, 197, 84, -97, -14, 19], ![-95, 246, 469, -810, -683, 908, 330, -410, -40, 62], ![-310, 773, 1610, -2507, -2484, 2789, 1342, -1282, -224, 208], ![-1040, 2602, 5349, -8374, -8123, 9164, 4245, -4066, -658, 608]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 14, 22, -48, -27, 56, 7, -26, 3, 4], ![-20, 51, 102, -170, -156, 197, 84, -97, -14, 19], ![-95, 246, 469, -810, -683, 908, 330, -410, -40, 62], ![-310, 773, 1610, -2507, -2484, 2789, 1342, -1282, -224, 208], ![-1040, 2602, 5349, -8374, -8123, 9164, 4245, -4066, -658, 608], ![-3040, 7472, 15978, -23835, -24790, 25925, 13420, -11563, -2242, 1774]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 14, 22, -48, -27, 56, 7, -26, 3, 4], ![-20, 51, 102, -170, -156, 197, 84, -97, -14, 19], ![-95, 246, 469, -810, -683, 908, 330, -410, -40, 62], ![-310, 773, 1610, -2507, -2484, 2789, 1342, -1282, -224, 208], ![-1040, 2602, 5349, -8374, -8123, 9164, 4245, -4066, -658, 608], ![-3040, 7472, 15978, -23835, -24790, 25925, 13420, -11563, -2242, 1774], ![-8870, 21796, 46500, -69174, -71733, 74554, 38343, -32704, -6241, 4854]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 14, 22, -48, -27, 56, 7, -26, 3, 4], ![-20, 51, 102, -170, -156, 197, 84, -97, -14, 19], ![-95, 246, 469, -810, -683, 908, 330, -410, -40, 62], ![-310, 773, 1610, -2507, -2484, 2789, 1342, -1282, -224, 208], ![-1040, 2602, 5349, -8374, -8123, 9164, 4245, -4066, -658, 608], ![-3040, 7472, 15978, -23835, -24790, 25925, 13420, -11563, -2242, 1774], ![-8870, 21796, 46500, -69174, -71733, 74554, 38343, -32704, -6241, 4854], ![-24270, 59086, 128584, -186492, -200232, 200091, 108532, -87861, -18142, 13175]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 14, 22, -48, -27, 56, 7, -26, 3, 4], ![-20, 51, 102, -170, -156, 197, 84, -97, -14, 19], ![-95, 246, 469, -810, -683, 908, 330, -410, -40, 62], ![-310, 773, 1610, -2507, -2484, 2789, 1342, -1282, -224, 208], ![-1040, 2602, 5349, -8374, -8123, 9164, 4245, -4066, -658, 608], ![-3040, 7472, 15978, -23835, -24790, 25925, 13420, -11563, -2242, 1774], ![-8870, 21796, 46500, -69174, -71733, 74554, 38343, -32704, -6241, 4854], ![-24270, 59086, 128584, -186492, -200232, 200091, 108532, -87861, -18142, 13175], ![-65875, 160180, 348936, -503816, -542217, 537568, 292316, -234018, -48336, 34558]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-208, -62, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-208, -62, -19, -4, -1], [-608, -208, -62, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-208, -62, -19, -4, -1], [-608, -208, -62, -19, -4, -1], [-1774, -608, -208, -62, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-208, -62, -19, -4, -1], [-608, -208, -62, -19, -4, -1], [-1774, -608, -208, -62, -19, -4, -1], [-4854, -1774, -608, -208, -62, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-208, -62, -19, -4, -1], [-608, -208, -62, -19, -4, -1], [-1774, -608, -208, -62, -19, -4, -1], [-4854, -1774, -608, -208, -62, -19, -4, -1], [-13175, -4854, -1774, -608, -208, -62, -19, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 14, 22, -48, -27, 56, 7, -26, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 14, 22, -48, -27, 56, 7, -26, 3, 4], [-20, 51, 102, -170, -156, 197, 84, -97, -14, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 14, 22, -48, -27, 56, 7, -26, 3, 4], [-20, 51, 102, -170, -156, 197, 84, -97, -14, 19], [-95, 246, 469, -810, -683, 908, 330, -410, -40, 62]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 14, 22, -48, -27, 56, 7, -26, 3, 4], [-20, 51, 102, -170, -156, 197, 84, -97, -14, 19], [-95, 246, 469, -810, -683, 908, 330, -410, -40, 62], [-310, 773, 1610, -2507, -2484, 2789, 1342, -1282, -224, 208]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 14, 22, -48, -27, 56, 7, -26, 3, 4], [-20, 51, 102, -170, -156, 197, 84, -97, -14, 19], [-95, 246, 469, -810, -683, 908, 330, -410, -40, 62], [-310, 773, 1610, -2507, -2484, 2789, 1342, -1282, -224, 208], [-1040, 2602, 5349, -8374, -8123, 9164, 4245, -4066, -658, 608]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 14, 22, -48, -27, 56, 7, -26, 3, 4], [-20, 51, 102, -170, -156, 197, 84, -97, -14, 19], [-95, 246, 469, -810, -683, 908, 330, -410, -40, 62], [-310, 773, 1610, -2507, -2484, 2789, 1342, -1282, -224, 208], [-1040, 2602, 5349, -8374, -8123, 9164, 4245, -4066, -658, 608], [-3040, 7472, 15978, -23835, -24790, 25925, 13420, -11563, -2242, 1774]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 14, 22, -48, -27, 56, 7, -26, 3, 4], [-20, 51, 102, -170, -156, 197, 84, -97, -14, 19], [-95, 246, 469, -810, -683, 908, 330, -410, -40, 62], [-310, 773, 1610, -2507, -2484, 2789, 1342, -1282, -224, 208], [-1040, 2602, 5349, -8374, -8123, 9164, 4245, -4066, -658, 608], [-3040, 7472, 15978, -23835, -24790, 25925, 13420, -11563, -2242, 1774], [-8870, 21796, 46500, -69174, -71733, 74554, 38343, -32704, -6241, 4854]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 14, 22, -48, -27, 56, 7, -26, 3, 4], [-20, 51, 102, -170, -156, 197, 84, -97, -14, 19], [-95, 246, 469, -810, -683, 908, 330, -410, -40, 62], [-310, 773, 1610, -2507, -2484, 2789, 1342, -1282, -224, 208], [-1040, 2602, 5349, -8374, -8123, 9164, 4245, -4066, -658, 608], [-3040, 7472, 15978, -23835, -24790, 25925, 13420, -11563, -2242, 1774], [-8870, 21796, 46500, -69174, -71733, 74554, 38343, -32704, -6241, 4854], [-24270, 59086, 128584, -186492, -200232, 200091, 108532, -87861, -18142, 13175]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 14, 22, -48, -27, 56, 7, -26, 3, 4], [-20, 51, 102, -170, -156, 197, 84, -97, -14, 19], [-95, 246, 469, -810, -683, 908, 330, -410, -40, 62], [-310, 773, 1610, -2507, -2484, 2789, 1342, -1282, -224, 208], [-1040, 2602, 5349, -8374, -8123, 9164, 4245, -4066, -658, 608], [-3040, 7472, 15978, -23835, -24790, 25925, 13420, -11563, -2242, 1774], [-8870, 21796, 46500, -69174, -71733, 74554, 38343, -32704, -6241, 4854], [-24270, 59086, 128584, -186492, -200232, 200091, 108532, -87861, -18142, 13175], [-65875, 160180, 348936, -503816, -542217, 537568, 292316, -234018, -48336, 34558]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp587 : Fact (Nat.Prime 587) := fact_iff.2 (by norm_num)
instance hp6849919 : Fact (Nat.Prime 6849919) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1]
  b' := [1, 1]
  k := [1]
  f := [-2, 7, 12, -23, -12, 30, 5, -11, 3, 3]
  g := [1, 0, 1, 1, 1, 1]
  h := [1, 0, 1, 1, 1, 1]
  a := [1, 1, 1]
  b := [1, 1, 0, 0, 1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD587 : CertificateDedekindCriterionLists l 587 where
  n := 2
  a' := [136, 94, 4, 402, 306, 73, 6, 293]
  b' := [291, 352, 175, 571, 462, 534, 491, 563, 424]
  k := [76, 63, 551, 216, 172, 123, 106, 75, 1]
  f := [225, 100, 135, 103, 202, 132, 20, 161, 143, 1]
  g := [520, 229, 311, 237, 466, 303, 45, 372, 329, 1]
  h := [254, 1]
  a := [447, 174, 187, 392, 398, 255, 296, 569, 563]
  b := [441, 183, 457, 393, 553, 388, 79, 250, 24]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD6849919 : CertificateDedekindCriterionLists l 6849919 where
  n := 2
  a' := [1925951, 432221, 3284837, 3991559, 5701093, 1303349, 3322608, 5993446]
  b' := [5644346, 231650, 3225454, 684476, 2591255, 2211804, 5052694, 5751010, 2378470]
  k := [3542376, 2097735, 4969018, 3630525, 669326, 6753327, 6838605, 4884696, 1]
  f := [4195334, 2722492, 3009256, 21414, 1025564, 598514, 50229, 2309773, 1571524, 1]
  g := [6520079, 4231095, 4676763, 33279, 1593856, 930166, 78062, 3589679, 2442346, 1]
  h := [4407569, 1]
  a := [6014982, 3856595, 4867941, 5547953, 555257, 3184589, 1791050, 4921733, 6521581]
  b := [4619324, 4972107, 693847, 860084, 81117, 5790533, 1607221, 443329, 328338]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 587, 6849919]
  exp := ![1, 1, 1]
  pdgood := [2, 587, 6849919]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp587.out
    exact hp6849919.out
  a := [291952618, -19876269966, -46603243374, 140777014108, 20099414798, -134924115748, 25508514182, 31451235226, -9956836710]
  b := [-470145844, -5913019239, 16521460717, 12744810684, -34281041094, -2838799821, 20426979558, -3323996698, -3543396991, 995683671]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 587 T_ofList CD587
    exact satisfiesDedekindCriterion_of_certificate_lists T l 6849919 T_ofList CD6849919

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

end VoightMaximalOrderD10R297

namespace VoightMaximalOrderD10R302

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4176724171033, [-1, -3, 8, 20, -22, -31, 21, 17, -8, -3, 1], 1⟩
local notation "l" => [-1, -3, 8, 20, -22, -31, 21, 17, -8, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -8, -20, 22, 31, -21, -17, 8, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -8, -20, 22, 31, -21, -17, 8, 3], ![3, 10, -21, -68, 46, 115, -32, -72, 7, 17]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -8, -20, 22, 31, -21, -17, 8, 3], ![3, 10, -21, -68, 46, 115, -32, -72, 7, 17], ![17, 54, -126, -361, 306, 573, -242, -321, 64, 58]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -8, -20, 22, 31, -21, -17, 8, 3], ![3, 10, -21, -68, 46, 115, -32, -72, 7, 17], ![17, 54, -126, -361, 306, 573, -242, -321, 64, 58], ![58, 191, -410, -1286, 915, 2104, -645, -1228, 143, 238]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -8, -20, 22, 31, -21, -17, 8, 3], ![3, 10, -21, -68, 46, 115, -32, -72, 7, 17], ![17, 54, -126, -361, 306, 573, -242, -321, 64, 58], ![58, 191, -410, -1286, 915, 2104, -645, -1228, 143, 238], ![238, 772, -1713, -5170, 3950, 8293, -2894, -4691, 676, 857]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -8, -20, 22, 31, -21, -17, 8, 3], ![3, 10, -21, -68, 46, 115, -32, -72, 7, 17], ![17, 54, -126, -361, 306, 573, -242, -321, 64, 58], ![58, 191, -410, -1286, 915, 2104, -645, -1228, 143, 238], ![238, 772, -1713, -5170, 3950, 8293, -2894, -4691, 676, 857], ![857, 2809, -6084, -18853, 13684, 30517, -9704, -17463, 2165, 3247]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -8, -20, 22, 31, -21, -17, 8, 3], ![3, 10, -21, -68, 46, 115, -32, -72, 7, 17], ![17, 54, -126, -361, 306, 573, -242, -321, 64, 58], ![58, 191, -410, -1286, 915, 2104, -645, -1228, 143, 238], ![238, 772, -1713, -5170, 3950, 8293, -2894, -4691, 676, 857], ![857, 2809, -6084, -18853, 13684, 30517, -9704, -17463, 2165, 3247], ![3247, 10598, -23167, -71024, 52581, 114341, -37670, -64903, 8513, 11906]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -8, -20, 22, 31, -21, -17, 8, 3], ![3, 10, -21, -68, 46, 115, -32, -72, 7, 17], ![17, 54, -126, -361, 306, 573, -242, -321, 64, 58], ![58, 191, -410, -1286, 915, 2104, -645, -1228, 143, 238], ![238, 772, -1713, -5170, 3950, 8293, -2894, -4691, 676, 857], ![857, 2809, -6084, -18853, 13684, 30517, -9704, -17463, 2165, 3247], ![3247, 10598, -23167, -71024, 52581, 114341, -37670, -64903, 8513, 11906], ![11906, 38965, -84650, -261287, 190908, 421667, -135685, -240072, 30345, 44231]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 3, -8, -20, 22, 31, -21, -17, 8, 3], ![3, 10, -21, -68, 46, 115, -32, -72, 7, 17], ![17, 54, -126, -361, 306, 573, -242, -321, 64, 58], ![58, 191, -410, -1286, 915, 2104, -645, -1228, 143, 238], ![238, 772, -1713, -5170, 3950, 8293, -2894, -4691, 676, 857], ![857, 2809, -6084, -18853, 13684, 30517, -9704, -17463, 2165, 3247], ![3247, 10598, -23167, -71024, 52581, 114341, -37670, -64903, 8513, 11906], ![11906, 38965, -84650, -261287, 190908, 421667, -135685, -240072, 30345, 44231], ![44231, 144599, -314883, -969270, 711795, 1562069, -507184, -887612, 113776, 163038]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-58, -17, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-58, -17, -3, -1], [-238, -58, -17, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-17, -3, -1], [-58, -17, -3, -1], [-238, -58, -17, -3, -1], [-857, -238, -58, -17, -3, -1]], ![[], [], [], [-1], [-3, -1], [-17, -3, -1], [-58, -17, -3, -1], [-238, -58, -17, -3, -1], [-857, -238, -58, -17, -3, -1], [-3247, -857, -238, -58, -17, -3, -1]], ![[], [], [-1], [-3, -1], [-17, -3, -1], [-58, -17, -3, -1], [-238, -58, -17, -3, -1], [-857, -238, -58, -17, -3, -1], [-3247, -857, -238, -58, -17, -3, -1], [-11906, -3247, -857, -238, -58, -17, -3, -1]], ![[], [-1], [-3, -1], [-17, -3, -1], [-58, -17, -3, -1], [-238, -58, -17, -3, -1], [-857, -238, -58, -17, -3, -1], [-3247, -857, -238, -58, -17, -3, -1], [-11906, -3247, -857, -238, -58, -17, -3, -1], [-44231, -11906, -3247, -857, -238, -58, -17, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -8, -20, 22, 31, -21, -17, 8, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -8, -20, 22, 31, -21, -17, 8, 3], [3, 10, -21, -68, 46, 115, -32, -72, 7, 17]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -8, -20, 22, 31, -21, -17, 8, 3], [3, 10, -21, -68, 46, 115, -32, -72, 7, 17], [17, 54, -126, -361, 306, 573, -242, -321, 64, 58]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -8, -20, 22, 31, -21, -17, 8, 3], [3, 10, -21, -68, 46, 115, -32, -72, 7, 17], [17, 54, -126, -361, 306, 573, -242, -321, 64, 58], [58, 191, -410, -1286, 915, 2104, -645, -1228, 143, 238]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -8, -20, 22, 31, -21, -17, 8, 3], [3, 10, -21, -68, 46, 115, -32, -72, 7, 17], [17, 54, -126, -361, 306, 573, -242, -321, 64, 58], [58, 191, -410, -1286, 915, 2104, -645, -1228, 143, 238], [238, 772, -1713, -5170, 3950, 8293, -2894, -4691, 676, 857]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -8, -20, 22, 31, -21, -17, 8, 3], [3, 10, -21, -68, 46, 115, -32, -72, 7, 17], [17, 54, -126, -361, 306, 573, -242, -321, 64, 58], [58, 191, -410, -1286, 915, 2104, -645, -1228, 143, 238], [238, 772, -1713, -5170, 3950, 8293, -2894, -4691, 676, 857], [857, 2809, -6084, -18853, 13684, 30517, -9704, -17463, 2165, 3247]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -8, -20, 22, 31, -21, -17, 8, 3], [3, 10, -21, -68, 46, 115, -32, -72, 7, 17], [17, 54, -126, -361, 306, 573, -242, -321, 64, 58], [58, 191, -410, -1286, 915, 2104, -645, -1228, 143, 238], [238, 772, -1713, -5170, 3950, 8293, -2894, -4691, 676, 857], [857, 2809, -6084, -18853, 13684, 30517, -9704, -17463, 2165, 3247], [3247, 10598, -23167, -71024, 52581, 114341, -37670, -64903, 8513, 11906]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -8, -20, 22, 31, -21, -17, 8, 3], [3, 10, -21, -68, 46, 115, -32, -72, 7, 17], [17, 54, -126, -361, 306, 573, -242, -321, 64, 58], [58, 191, -410, -1286, 915, 2104, -645, -1228, 143, 238], [238, 772, -1713, -5170, 3950, 8293, -2894, -4691, 676, 857], [857, 2809, -6084, -18853, 13684, 30517, -9704, -17463, 2165, 3247], [3247, 10598, -23167, -71024, 52581, 114341, -37670, -64903, 8513, 11906], [11906, 38965, -84650, -261287, 190908, 421667, -135685, -240072, 30345, 44231]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 3, -8, -20, 22, 31, -21, -17, 8, 3], [3, 10, -21, -68, 46, 115, -32, -72, 7, 17], [17, 54, -126, -361, 306, 573, -242, -321, 64, 58], [58, 191, -410, -1286, 915, 2104, -645, -1228, 143, 238], [238, 772, -1713, -5170, 3950, 8293, -2894, -4691, 676, 857], [857, 2809, -6084, -18853, 13684, 30517, -9704, -17463, 2165, 3247], [3247, 10598, -23167, -71024, 52581, 114341, -37670, -64903, 8513, 11906], [11906, 38965, -84650, -261287, 190908, 421667, -135685, -240072, 30345, 44231], [44231, 144599, -314883, -969270, 711795, 1562069, -507184, -887612, 113776, 163038]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp157 : Fact (Nat.Prime 157) := fact_iff.2 (by norm_num)
instance hp193 : Fact (Nat.Prime 193) := fact_iff.2 (by norm_num)
instance hp937 : Fact (Nat.Prime 937) := fact_iff.2 (by norm_num)

def CD157 : CertificateDedekindCriterionLists l 157 where
  n := 2
  a' := [87, 56, 107, 15, 112, 16, 18]
  b' := [23, 148, 58, 130, 31, 23, 116, 37]
  k := [11, 46, 2, 25, 20, 71, 1]
  f := [76, 129, 152, 146, 147, 104, 31, 48, 27, 1]
  g := [97, 70, 125, 64, 124, 11, 28, 34, 1]
  h := [123, 120, 1]
  a := [34, 50, 92, 148, 114, 56, 20, 32]
  b := [98, 99, 28, 72, 48, 126, 149, 47, 125]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD193 : CertificateDedekindCriterionLists l 193 where
  n := 2
  a' := [8, 93, 42, 67, 168, 61, 175, 134]
  b' := [3, 73, 89, 118, 186, 79, 97, 60, 28]
  k := [108, 162, 135, 176, 94, 20, 134, 123, 1]
  f := [97, 89, 101, 33, 30, 125, 48, 71, 41, 1]
  g := [144, 131, 149, 48, 44, 185, 70, 105, 60, 1]
  h := [130, 1]
  a := [60, 103, 187, 62, 145, 122, 9, 183, 79]
  b := [103, 25, 159, 37, 149, 166, 49, 160, 114]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD937 : CertificateDedekindCriterionLists l 937 where
  n := 2
  a' := [908, 698, 862, 65, 35, 757, 408]
  b' := [693, 99, 452, 525, 4, 552, 446, 886]
  k := [243, 671, 630, 78, 569, 899, 1]
  f := [651, 695, 369, 781, 726, 520, 811, 757, 234, 1]
  g := [754, 352, 215, 775, 375, 376, 713, 448, 1]
  h := [809, 486, 1]
  a := [165, 845, 861, 498, 80, 756, 576, 609]
  b := [546, 643, 900, 902, 404, 636, 434, 444, 328]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![157, 193, 937]
  exp := ![1, 1, 1]
  pdgood := [157, 193, 937]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp157.out
    exact hp193.out
    exact hp937.out
  a := [252808478, -2279254562, 962122873, 6409154084, -2904563090, -5055886226, 2012022320, 1153161002, -380923660]
  b := [-93733505, 7031016, 795531531, -358158581, -1287158501, 533582820, 717127792, -258410004, -126743810, 38092366]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 157 T_ofList CD157
    exact satisfiesDedekindCriterion_of_certificate_lists T l 193 T_ofList CD193
    exact satisfiesDedekindCriterion_of_certificate_lists T l 937 T_ofList CD937

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

end VoightMaximalOrderD10R302

end TraceEuclidean
