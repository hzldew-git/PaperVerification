import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk178
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

namespace VoightMaximalOrderD10R141

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2571640645265, [1, 8, 12, -26, -49, 25, 45, -4, -12, 0, 1], 1⟩
local notation "l" => [1, 8, 12, -26, -49, 25, 45, -4, -12, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -12, 26, 49, -25, -45, 4, 12, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -12, 26, 49, -25, -45, 4, 12, 0], ![0, -1, -8, -12, 26, 49, -25, -45, 4, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -12, 26, 49, -25, -45, 4, 12, 0], ![0, -1, -8, -12, 26, 49, -25, -45, 4, 12], ![-12, -96, -145, 304, 576, -274, -491, 23, 99, 4]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -12, 26, 49, -25, -45, 4, 12, 0], ![0, -1, -8, -12, 26, 49, -25, -45, 4, 12], ![-12, -96, -145, 304, 576, -274, -491, 23, 99, 4], ![-4, -44, -144, -41, 500, 476, -454, -475, 71, 99]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -12, 26, 49, -25, -45, 4, 12, 0], ![0, -1, -8, -12, 26, 49, -25, -45, 4, 12], ![-12, -96, -145, 304, 576, -274, -491, 23, 99, 4], ![-4, -44, -144, -41, 500, 476, -454, -475, 71, 99], ![-99, -796, -1232, 2430, 4810, -1975, -3979, -58, 713, 71]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -12, 26, 49, -25, -45, 4, 12, 0], ![0, -1, -8, -12, 26, 49, -25, -45, 4, 12], ![-12, -96, -145, 304, 576, -274, -491, 23, 99, 4], ![-4, -44, -144, -41, 500, 476, -454, -475, 71, 99], ![-99, -796, -1232, 2430, 4810, -1975, -3979, -58, 713, 71], ![-71, -667, -1648, 614, 5909, 3035, -5170, -3695, 794, 713]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -12, 26, 49, -25, -45, 4, 12, 0], ![0, -1, -8, -12, 26, 49, -25, -45, 4, 12], ![-12, -96, -145, 304, 576, -274, -491, 23, 99, 4], ![-4, -44, -144, -41, 500, 476, -454, -475, 71, 99], ![-99, -796, -1232, 2430, 4810, -1975, -3979, -58, 713, 71], ![-71, -667, -1648, 614, 5909, 3035, -5170, -3695, 794, 713], ![-713, -5775, -9223, 16890, 35551, -11916, -29050, -2318, 4861, 794]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -12, 26, 49, -25, -45, 4, 12, 0], ![0, -1, -8, -12, 26, 49, -25, -45, 4, 12], ![-12, -96, -145, 304, 576, -274, -491, 23, 99, 4], ![-4, -44, -144, -41, 500, 476, -454, -475, 71, 99], ![-99, -796, -1232, 2430, 4810, -1975, -3979, -58, 713, 71], ![-71, -667, -1648, 614, 5909, 3035, -5170, -3695, 794, 713], ![-713, -5775, -9223, 16890, 35551, -11916, -29050, -2318, 4861, 794], ![-794, -7065, -15303, 11421, 55796, 15701, -47646, -25874, 7210, 4861]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -12, 26, 49, -25, -45, 4, 12, 0], ![0, -1, -8, -12, 26, 49, -25, -45, 4, 12], ![-12, -96, -145, 304, 576, -274, -491, 23, 99, 4], ![-4, -44, -144, -41, 500, 476, -454, -475, 71, 99], ![-99, -796, -1232, 2430, 4810, -1975, -3979, -58, 713, 71], ![-71, -667, -1648, 614, 5909, 3035, -5170, -3695, 794, 713], ![-713, -5775, -9223, 16890, 35551, -11916, -29050, -2318, 4861, 794], ![-794, -7065, -15303, 11421, 55796, 15701, -47646, -25874, 7210, 4861], ![-4861, -39682, -65397, 111083, 249610, -65729, -203044, -28202, 32458, 7210]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1], [-99, -4, -12, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1], [-99, -4, -12, 0, -1], [-71, -99, -4, -12, 0, -1]], ![[], [], [], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1], [-99, -4, -12, 0, -1], [-71, -99, -4, -12, 0, -1], [-713, -71, -99, -4, -12, 0, -1]], ![[], [], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1], [-99, -4, -12, 0, -1], [-71, -99, -4, -12, 0, -1], [-713, -71, -99, -4, -12, 0, -1], [-794, -713, -71, -99, -4, -12, 0, -1]], ![[], [-1], [0, -1], [-12, 0, -1], [-4, -12, 0, -1], [-99, -4, -12, 0, -1], [-71, -99, -4, -12, 0, -1], [-713, -71, -99, -4, -12, 0, -1], [-794, -713, -71, -99, -4, -12, 0, -1], [-4861, -794, -713, -71, -99, -4, -12, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -12, 26, 49, -25, -45, 4, 12, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -12, 26, 49, -25, -45, 4, 12, 0], [0, -1, -8, -12, 26, 49, -25, -45, 4, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -12, 26, 49, -25, -45, 4, 12, 0], [0, -1, -8, -12, 26, 49, -25, -45, 4, 12], [-12, -96, -145, 304, 576, -274, -491, 23, 99, 4]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -12, 26, 49, -25, -45, 4, 12, 0], [0, -1, -8, -12, 26, 49, -25, -45, 4, 12], [-12, -96, -145, 304, 576, -274, -491, 23, 99, 4], [-4, -44, -144, -41, 500, 476, -454, -475, 71, 99]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -12, 26, 49, -25, -45, 4, 12, 0], [0, -1, -8, -12, 26, 49, -25, -45, 4, 12], [-12, -96, -145, 304, 576, -274, -491, 23, 99, 4], [-4, -44, -144, -41, 500, 476, -454, -475, 71, 99], [-99, -796, -1232, 2430, 4810, -1975, -3979, -58, 713, 71]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -12, 26, 49, -25, -45, 4, 12, 0], [0, -1, -8, -12, 26, 49, -25, -45, 4, 12], [-12, -96, -145, 304, 576, -274, -491, 23, 99, 4], [-4, -44, -144, -41, 500, 476, -454, -475, 71, 99], [-99, -796, -1232, 2430, 4810, -1975, -3979, -58, 713, 71], [-71, -667, -1648, 614, 5909, 3035, -5170, -3695, 794, 713]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -12, 26, 49, -25, -45, 4, 12, 0], [0, -1, -8, -12, 26, 49, -25, -45, 4, 12], [-12, -96, -145, 304, 576, -274, -491, 23, 99, 4], [-4, -44, -144, -41, 500, 476, -454, -475, 71, 99], [-99, -796, -1232, 2430, 4810, -1975, -3979, -58, 713, 71], [-71, -667, -1648, 614, 5909, 3035, -5170, -3695, 794, 713], [-713, -5775, -9223, 16890, 35551, -11916, -29050, -2318, 4861, 794]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -12, 26, 49, -25, -45, 4, 12, 0], [0, -1, -8, -12, 26, 49, -25, -45, 4, 12], [-12, -96, -145, 304, 576, -274, -491, 23, 99, 4], [-4, -44, -144, -41, 500, 476, -454, -475, 71, 99], [-99, -796, -1232, 2430, 4810, -1975, -3979, -58, 713, 71], [-71, -667, -1648, 614, 5909, 3035, -5170, -3695, 794, 713], [-713, -5775, -9223, 16890, 35551, -11916, -29050, -2318, 4861, 794], [-794, -7065, -15303, 11421, 55796, 15701, -47646, -25874, 7210, 4861]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -12, 26, 49, -25, -45, 4, 12, 0], [0, -1, -8, -12, 26, 49, -25, -45, 4, 12], [-12, -96, -145, 304, 576, -274, -491, 23, 99, 4], [-4, -44, -144, -41, 500, 476, -454, -475, 71, 99], [-99, -796, -1232, 2430, 4810, -1975, -3979, -58, 713, 71], [-71, -667, -1648, 614, 5909, 3035, -5170, -3695, 794, 713], [-713, -5775, -9223, 16890, 35551, -11916, -29050, -2318, 4861, 794], [-794, -7065, -15303, 11421, 55796, 15701, -47646, -25874, 7210, 4861], [-4861, -39682, -65397, 111083, 249610, -65729, -203044, -28202, 32458, 7210]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp61 : Fact (Nat.Prime 61) := fact_iff.2 (by norm_num)
instance hp397 : Fact (Nat.Prime 397) := fact_iff.2 (by norm_num)
instance hp877 : Fact (Nat.Prime 877) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 3, 2, 4, 3, 3, 1]
  b' := [2, 4, 4, 0, 4, 0, 4, 1]
  k := [1, 1, 4, 0, 2, 1, 1, 3, 1]
  f := [0, -1, -2, 6, 11, -4, -8, 2, 4, 1]
  g := [1, 2, 0, 4, 2, 3, 2, 4, 4, 1]
  h := [1, 1]
  a := [2, 1, 3, 0, 3, 3, 4, 0, 3]
  b := [1, 0, 0, 4, 3, 3, 2, 0, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD61 : CertificateDedekindCriterionLists l 61 where
  n := 2
  a' := [20, 52, 36, 16, 28, 7, 19]
  b' := [15, 25, 10, 17, 7, 25, 5, 51]
  k := [47, 25, 24, 29, 17, 15, 1]
  f := [10, 51, 55, 55, 40, 31, 43, 46, 16, 1]
  g := [13, 60, 42, 49, 26, 27, 43, 38, 1]
  h := [47, 23, 1]
  a := [30, 27, 43, 58, 19, 13, 25, 17]
  b := [38, 24, 12, 53, 41, 35, 60, 44, 44]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD397 : CertificateDedekindCriterionLists l 397 where
  n := 2
  a' := [116, 68, 281, 369, 21, 79, 46]
  b' := [264, 31, 159, 189, 137, 232, 358, 292]
  k := [27, 229, 221, 2, 321, 12, 1]
  f := [73, 349, 120, 246, 268, 90, 367, 332, 7, 1]
  g := [337, 79, 191, 266, 25, 299, 335, 6, 1]
  h := [86, 391, 1]
  a := [251, 78, 319, 41, 361, 379, 45, 85]
  b := [1, 127, 396, 44, 265, 302, 341, 267, 312]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD877 : CertificateDedekindCriterionLists l 877 where
  n := 2
  a' := [584, 676, 167, 244, 853, 441, 614, 238]
  b' := [805, 685, 24, 657, 517, 808, 407, 383, 71]
  k := [343, 412, 762, 341, 504, 334, 190, 732, 1]
  f := [437, 231, 237, 286, 28, 95, 45, 373, 214, 1]
  g := [750, 395, 406, 490, 47, 163, 77, 640, 366, 1]
  h := [511, 1]
  a := [600, 343, 389, 538, 413, 197, 855, 437, 357]
  b := [863, 550, 653, 413, 183, 24, 315, 330, 520]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 61, 397, 877]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 61, 397, 877]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp61.out
    exact hp397.out
    exact hp877.out
  a := [-3675306399, 1471624952, 29590396622, -5193057024, -38789519376, -606866734, 13778391988, 507182780, -1459976080]
  b := [472687243, 2073291551, -1268638965, -7492100748, 1444658576, 6510800004, 7213411, -1728233458, -50718278, 145997608]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 61 T_ofList CD61
    exact satisfiesDedekindCriterion_of_certificate_lists T l 397 T_ofList CD397
    exact satisfiesDedekindCriterion_of_certificate_lists T l 877 T_ofList CD877

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

end VoightMaximalOrderD10R141

namespace VoightMaximalOrderD10R142

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2573858170877, [1, -10, 14, 33, -35, -34, 28, 14, -9, -2, 1], 1⟩
local notation "l" => [1, -10, 14, 33, -35, -34, 28, 14, -9, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -14, -33, 35, 34, -28, -14, 9, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -14, -33, 35, 34, -28, -14, 9, 2], ![-2, 19, -18, -80, 37, 103, -22, -56, 4, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -14, -33, 35, 34, -28, -14, 9, 2], ![-2, 19, -18, -80, 37, 103, -22, -56, 4, 13], ![-13, 128, -163, -447, 375, 479, -261, -204, 61, 30]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -14, -33, 35, 34, -28, -14, 9, 2], ![-2, 19, -18, -80, 37, 103, -22, -56, 4, 13], ![-13, 128, -163, -447, 375, 479, -261, -204, 61, 30], ![-30, 287, -292, -1153, 603, 1395, -361, -681, 66, 121]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -14, -33, 35, 34, -28, -14, 9, 2], ![-2, 19, -18, -80, 37, 103, -22, -56, 4, 13], ![-13, 128, -163, -447, 375, 479, -261, -204, 61, 30], ![-30, 287, -292, -1153, 603, 1395, -361, -681, 66, 121], ![-121, 1180, -1407, -4285, 3082, 4717, -1993, -2055, 408, 308]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -14, -33, 35, 34, -28, -14, 9, 2], ![-2, 19, -18, -80, 37, 103, -22, -56, 4, 13], ![-13, 128, -163, -447, 375, 479, -261, -204, 61, 30], ![-30, 287, -292, -1153, 603, 1395, -361, -681, 66, 121], ![-121, 1180, -1407, -4285, 3082, 4717, -1993, -2055, 408, 308], ![-308, 2959, -3132, -11571, 6495, 13554, -3907, -6305, 717, 1024]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -14, -33, 35, 34, -28, -14, 9, 2], ![-2, 19, -18, -80, 37, 103, -22, -56, 4, 13], ![-13, 128, -163, -447, 375, 479, -261, -204, 61, 30], ![-30, 287, -292, -1153, 603, 1395, -361, -681, 66, 121], ![-121, 1180, -1407, -4285, 3082, 4717, -1993, -2055, 408, 308], ![-308, 2959, -3132, -11571, 6495, 13554, -3907, -6305, 717, 1024], ![-1024, 9932, -11377, -36924, 24269, 41311, -15118, -18243, 2911, 2765]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -14, -33, 35, 34, -28, -14, 9, 2], ![-2, 19, -18, -80, 37, 103, -22, -56, 4, 13], ![-13, 128, -163, -447, 375, 479, -261, -204, 61, 30], ![-30, 287, -292, -1153, 603, 1395, -361, -681, 66, 121], ![-121, 1180, -1407, -4285, 3082, 4717, -1993, -2055, 408, 308], ![-308, 2959, -3132, -11571, 6495, 13554, -3907, -6305, 717, 1024], ![-1024, 9932, -11377, -36924, 24269, 41311, -15118, -18243, 2911, 2765], ![-2765, 26626, -28778, -102622, 59851, 118279, -36109, -53828, 6642, 8441]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 10, -14, -33, 35, 34, -28, -14, 9, 2], ![-2, 19, -18, -80, 37, 103, -22, -56, 4, 13], ![-13, 128, -163, -447, 375, 479, -261, -204, 61, 30], ![-30, 287, -292, -1153, 603, 1395, -361, -681, 66, 121], ![-121, 1180, -1407, -4285, 3082, 4717, -1993, -2055, 408, 308], ![-308, 2959, -3132, -11571, 6495, 13554, -3907, -6305, 717, 1024], ![-1024, 9932, -11377, -36924, 24269, 41311, -15118, -18243, 2911, 2765], ![-2765, 26626, -28778, -102622, 59851, 118279, -36109, -53828, 6642, 8441], ![-8441, 81645, -91548, -307331, 192813, 346845, -118069, -154283, 22141, 23524]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-121, -30, -13, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-121, -30, -13, -2, -1], [-308, -121, -30, -13, -2, -1]], ![[], [], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-121, -30, -13, -2, -1], [-308, -121, -30, -13, -2, -1], [-1024, -308, -121, -30, -13, -2, -1]], ![[], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-121, -30, -13, -2, -1], [-308, -121, -30, -13, -2, -1], [-1024, -308, -121, -30, -13, -2, -1], [-2765, -1024, -308, -121, -30, -13, -2, -1]], ![[], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-121, -30, -13, -2, -1], [-308, -121, -30, -13, -2, -1], [-1024, -308, -121, -30, -13, -2, -1], [-2765, -1024, -308, -121, -30, -13, -2, -1], [-8441, -2765, -1024, -308, -121, -30, -13, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -14, -33, 35, 34, -28, -14, 9, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -14, -33, 35, 34, -28, -14, 9, 2], [-2, 19, -18, -80, 37, 103, -22, -56, 4, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -14, -33, 35, 34, -28, -14, 9, 2], [-2, 19, -18, -80, 37, 103, -22, -56, 4, 13], [-13, 128, -163, -447, 375, 479, -261, -204, 61, 30]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -14, -33, 35, 34, -28, -14, 9, 2], [-2, 19, -18, -80, 37, 103, -22, -56, 4, 13], [-13, 128, -163, -447, 375, 479, -261, -204, 61, 30], [-30, 287, -292, -1153, 603, 1395, -361, -681, 66, 121]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -14, -33, 35, 34, -28, -14, 9, 2], [-2, 19, -18, -80, 37, 103, -22, -56, 4, 13], [-13, 128, -163, -447, 375, 479, -261, -204, 61, 30], [-30, 287, -292, -1153, 603, 1395, -361, -681, 66, 121], [-121, 1180, -1407, -4285, 3082, 4717, -1993, -2055, 408, 308]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -14, -33, 35, 34, -28, -14, 9, 2], [-2, 19, -18, -80, 37, 103, -22, -56, 4, 13], [-13, 128, -163, -447, 375, 479, -261, -204, 61, 30], [-30, 287, -292, -1153, 603, 1395, -361, -681, 66, 121], [-121, 1180, -1407, -4285, 3082, 4717, -1993, -2055, 408, 308], [-308, 2959, -3132, -11571, 6495, 13554, -3907, -6305, 717, 1024]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -14, -33, 35, 34, -28, -14, 9, 2], [-2, 19, -18, -80, 37, 103, -22, -56, 4, 13], [-13, 128, -163, -447, 375, 479, -261, -204, 61, 30], [-30, 287, -292, -1153, 603, 1395, -361, -681, 66, 121], [-121, 1180, -1407, -4285, 3082, 4717, -1993, -2055, 408, 308], [-308, 2959, -3132, -11571, 6495, 13554, -3907, -6305, 717, 1024], [-1024, 9932, -11377, -36924, 24269, 41311, -15118, -18243, 2911, 2765]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -14, -33, 35, 34, -28, -14, 9, 2], [-2, 19, -18, -80, 37, 103, -22, -56, 4, 13], [-13, 128, -163, -447, 375, 479, -261, -204, 61, 30], [-30, 287, -292, -1153, 603, 1395, -361, -681, 66, 121], [-121, 1180, -1407, -4285, 3082, 4717, -1993, -2055, 408, 308], [-308, 2959, -3132, -11571, 6495, 13554, -3907, -6305, 717, 1024], [-1024, 9932, -11377, -36924, 24269, 41311, -15118, -18243, 2911, 2765], [-2765, 26626, -28778, -102622, 59851, 118279, -36109, -53828, 6642, 8441]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 10, -14, -33, 35, 34, -28, -14, 9, 2], [-2, 19, -18, -80, 37, 103, -22, -56, 4, 13], [-13, 128, -163, -447, 375, 479, -261, -204, 61, 30], [-30, 287, -292, -1153, 603, 1395, -361, -681, 66, 121], [-121, 1180, -1407, -4285, 3082, 4717, -1993, -2055, 408, 308], [-308, 2959, -3132, -11571, 6495, 13554, -3907, -6305, 717, 1024], [-1024, 9932, -11377, -36924, 24269, 41311, -15118, -18243, 2911, 2765], [-2765, 26626, -28778, -102622, 59851, 118279, -36109, -53828, 6642, 8441], [-8441, 81645, -91548, -307331, 192813, 346845, -118069, -154283, 22141, 23524]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp52527717773 : Fact (Nat.Prime 52527717773) := fact_iff.2 (by norm_num)

def CD7 : CertificateDedekindCriterionLists l 7 where
  n := 2
  a' := [3, 1, 4, 6, 5, 4, 3]
  b' := [0, 5, 3, 0, 6, 5, 5, 4]
  k := [4, 4, 2, 3, 6, 3, 1]
  f := [2, 3, -1, -4, 6, 7, -1, 1, 3, 1]
  g := [5, 2, 0, 1, 2, 4, 5, 4, 1]
  h := [3, 1, 1]
  a := [1, 4, 2, 5, 5, 6, 1, 1]
  b := [4, 6, 3, 2, 5, 1, 2, 0, 6]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD52527717773 : CertificateDedekindCriterionLists l 52527717773 where
  n := 2
  a' := [24154642112, 32089087585, 44889399134, 1395785041, 32388877659, 35250280624, 3271376229, 15973837349]
  b' := [26854057575, 4093341672, 47395308314, 12809711407, 26842510956, 22866284216, 6037491914, 44490332929, 21570781527]
  k := [14711513252, 31862198152, 6350125779, 43878953347, 46534637323, 51699739457, 17912581810, 21216721508, 1]
  f := [34517226619, 20361532532, 26197264759, 22247022127, 10823406251, 4330191242, 16590737577, 41040408923, 8465923910, 1]
  g := [43252360416, 25514342545, 32826899732, 27876985304, 13562441538, 5426015083, 20789287887, 51426337867, 10608360753, 1]
  h := [41919357018, 1]
  a := [15038176931, 24189408742, 21269139057, 36572823311, 41713579026, 18141034268, 52231982471, 20953784458, 3785690786]
  b := [9649138374, 24047892939, 13687464797, 35049548205, 34054352660, 3188495278, 5575580599, 42702409141, 48742026987]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![7, 52527717773]
  exp := ![1, 1]
  pdgood := [7, 52527717773]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp7.out
    exact hp52527717773.out
  a := [-1959779991049, -541596920812, 14025434039258, 1955635138080, -22230550805238, -3975518899748, 10301153747942, 1337717441274, -1370159536080]
  b := [-232747401546, 1253927574639, 407246270953, -4242744015810, -917347814148, 3913549086224, 737967936579, -1299315485762, -161174934849, 137015953608]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T l 52527717773 T_ofList CD52527717773

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

end VoightMaximalOrderD10R142

namespace VoightMaximalOrderD10R143

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2585491128125, [-1, 1, 19, 16, -40, -29, 29, 14, -9, -2, 1], 1⟩
local notation "l" => [-1, 1, 19, 16, -40, -29, 29, 14, -9, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -19, -16, 40, 29, -29, -14, 9, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -19, -16, 40, 29, -29, -14, 9, 2], ![2, -1, -39, -51, 64, 98, -29, -57, 4, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -19, -16, 40, 29, -29, -14, 9, 2], ![2, -1, -39, -51, 64, 98, -29, -57, 4, 13], ![13, -11, -248, -247, 469, 441, -279, -211, 60, 30]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -19, -16, 40, 29, -29, -14, 9, 2], ![2, -1, -39, -51, 64, 98, -29, -57, 4, 13], ![13, -11, -248, -247, 469, 441, -279, -211, 60, 30], ![30, -17, -581, -728, 953, 1339, -429, -699, 59, 120]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -19, -16, 40, 29, -29, -14, 9, 2], ![2, -1, -39, -51, 64, 98, -29, -57, 4, 13], ![13, -11, -248, -247, 469, 441, -279, -211, 60, 30], ![30, -17, -581, -728, 953, 1339, -429, -699, 59, 120], ![120, -90, -2297, -2501, 4072, 4433, -2141, -2109, 381, 299]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -19, -16, 40, 29, -29, -14, 9, 2], ![2, -1, -39, -51, 64, 98, -29, -57, 4, 13], ![13, -11, -248, -247, 469, 441, -279, -211, 60, 30], ![30, -17, -581, -728, 953, 1339, -429, -699, 59, 120], ![120, -90, -2297, -2501, 4072, 4433, -2141, -2109, 381, 299], ![299, -179, -5771, -7081, 9459, 12743, -4238, -6327, 582, 979]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -19, -16, 40, 29, -29, -14, 9, 2], ![2, -1, -39, -51, 64, 98, -29, -57, 4, 13], ![13, -11, -248, -247, 469, 441, -279, -211, 60, 30], ![30, -17, -581, -728, 953, 1339, -429, -699, 59, 120], ![120, -90, -2297, -2501, 4072, 4433, -2141, -2109, 381, 299], ![299, -179, -5771, -7081, 9459, 12743, -4238, -6327, 582, 979], ![979, -680, -18780, -21435, 32079, 37850, -15648, -17944, 2484, 2540]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -19, -16, 40, 29, -29, -14, 9, 2], ![2, -1, -39, -51, 64, 98, -29, -57, 4, 13], ![13, -11, -248, -247, 469, 441, -279, -211, 60, 30], ![30, -17, -581, -728, 953, 1339, -429, -699, 59, 120], ![120, -90, -2297, -2501, 4072, 4433, -2141, -2109, 381, 299], ![299, -179, -5771, -7081, 9459, 12743, -4238, -6327, 582, 979], ![979, -680, -18780, -21435, 32079, 37850, -15648, -17944, 2484, 2540], ![2540, -1561, -48940, -59420, 80165, 105739, -35810, -51208, 4916, 7564]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -1, -19, -16, 40, 29, -29, -14, 9, 2], ![2, -1, -39, -51, 64, 98, -29, -57, 4, 13], ![13, -11, -248, -247, 469, 441, -279, -211, 60, 30], ![30, -17, -581, -728, 953, 1339, -429, -699, 59, 120], ![120, -90, -2297, -2501, 4072, 4433, -2141, -2109, 381, 299], ![299, -179, -5771, -7081, 9459, 12743, -4238, -6327, 582, 979], ![979, -680, -18780, -21435, 32079, 37850, -15648, -17944, 2484, 2540], ![2540, -1561, -48940, -59420, 80165, 105739, -35810, -51208, 4916, 7564], ![7564, -5024, -145277, -169964, 243140, 299521, -113617, -141706, 16868, 20044]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-120, -30, -13, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-120, -30, -13, -2, -1], [-299, -120, -30, -13, -2, -1]], ![[], [], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-120, -30, -13, -2, -1], [-299, -120, -30, -13, -2, -1], [-979, -299, -120, -30, -13, -2, -1]], ![[], [], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-120, -30, -13, -2, -1], [-299, -120, -30, -13, -2, -1], [-979, -299, -120, -30, -13, -2, -1], [-2540, -979, -299, -120, -30, -13, -2, -1]], ![[], [-1], [-2, -1], [-13, -2, -1], [-30, -13, -2, -1], [-120, -30, -13, -2, -1], [-299, -120, -30, -13, -2, -1], [-979, -299, -120, -30, -13, -2, -1], [-2540, -979, -299, -120, -30, -13, -2, -1], [-7564, -2540, -979, -299, -120, -30, -13, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -19, -16, 40, 29, -29, -14, 9, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -19, -16, 40, 29, -29, -14, 9, 2], [2, -1, -39, -51, 64, 98, -29, -57, 4, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -19, -16, 40, 29, -29, -14, 9, 2], [2, -1, -39, -51, 64, 98, -29, -57, 4, 13], [13, -11, -248, -247, 469, 441, -279, -211, 60, 30]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -19, -16, 40, 29, -29, -14, 9, 2], [2, -1, -39, -51, 64, 98, -29, -57, 4, 13], [13, -11, -248, -247, 469, 441, -279, -211, 60, 30], [30, -17, -581, -728, 953, 1339, -429, -699, 59, 120]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -19, -16, 40, 29, -29, -14, 9, 2], [2, -1, -39, -51, 64, 98, -29, -57, 4, 13], [13, -11, -248, -247, 469, 441, -279, -211, 60, 30], [30, -17, -581, -728, 953, 1339, -429, -699, 59, 120], [120, -90, -2297, -2501, 4072, 4433, -2141, -2109, 381, 299]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -19, -16, 40, 29, -29, -14, 9, 2], [2, -1, -39, -51, 64, 98, -29, -57, 4, 13], [13, -11, -248, -247, 469, 441, -279, -211, 60, 30], [30, -17, -581, -728, 953, 1339, -429, -699, 59, 120], [120, -90, -2297, -2501, 4072, 4433, -2141, -2109, 381, 299], [299, -179, -5771, -7081, 9459, 12743, -4238, -6327, 582, 979]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -19, -16, 40, 29, -29, -14, 9, 2], [2, -1, -39, -51, 64, 98, -29, -57, 4, 13], [13, -11, -248, -247, 469, 441, -279, -211, 60, 30], [30, -17, -581, -728, 953, 1339, -429, -699, 59, 120], [120, -90, -2297, -2501, 4072, 4433, -2141, -2109, 381, 299], [299, -179, -5771, -7081, 9459, 12743, -4238, -6327, 582, 979], [979, -680, -18780, -21435, 32079, 37850, -15648, -17944, 2484, 2540]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -19, -16, 40, 29, -29, -14, 9, 2], [2, -1, -39, -51, 64, 98, -29, -57, 4, 13], [13, -11, -248, -247, 469, 441, -279, -211, 60, 30], [30, -17, -581, -728, 953, 1339, -429, -699, 59, 120], [120, -90, -2297, -2501, 4072, 4433, -2141, -2109, 381, 299], [299, -179, -5771, -7081, 9459, 12743, -4238, -6327, 582, 979], [979, -680, -18780, -21435, 32079, 37850, -15648, -17944, 2484, 2540], [2540, -1561, -48940, -59420, 80165, 105739, -35810, -51208, 4916, 7564]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -1, -19, -16, 40, 29, -29, -14, 9, 2], [2, -1, -39, -51, 64, 98, -29, -57, 4, 13], [13, -11, -248, -247, 469, 441, -279, -211, 60, 30], [30, -17, -581, -728, 953, 1339, -429, -699, 59, 120], [120, -90, -2297, -2501, 4072, 4433, -2141, -2109, 381, 299], [299, -179, -5771, -7081, 9459, 12743, -4238, -6327, 582, 979], [979, -680, -18780, -21435, 32079, 37850, -15648, -17944, 2484, 2540], [2540, -1561, -48940, -59420, 80165, 105739, -35810, -51208, 4916, 7564], [7564, -5024, -145277, -169964, 243140, 299521, -113617, -141706, 16868, 20044]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp461 : Fact (Nat.Prime 461) := fact_iff.2 (by norm_num)
instance hp991 : Fact (Nat.Prime 991) := fact_iff.2 (by norm_num)
instance hp1811 : Fact (Nat.Prime 1811) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 2, 1]
  b' := [1, 2, 0, 4, 4]
  k := [1]
  f := [1, 3, 1, 0, 12, 13, -1, -2, 5, 2]
  g := [2, 4, 2, 0, 4, 1]
  h := [2, 4, 2, 0, 4, 1]
  a := [0, 1, 3]
  b := [3, 1, 2, 0, 3, 2, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD461 : CertificateDedekindCriterionLists l 461 where
  n := 2
  a' := [366, 6, 102, 412, 87, 234, 458, 394]
  b' := [95, 369, 349, 184, 137, 275, 122, 209, 366]
  k := [17, 116, 60, 0, 317, 424, 105, 307, 1]
  f := [61, 13, 11, 10, 20, 45, 18, 64, 64, 1]
  g := [370, 74, 66, 60, 120, 271, 106, 387, 383, 1]
  h := [76, 1]
  a := [327, 217, 255, 446, 230, 65, 259, 382, 34]
  b := [128, 276, 118, 3, 459, 173, 327, 322, 427]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD991 : CertificateDedekindCriterionLists l 991 where
  n := 2
  a' := [844, 827, 38, 97, 104, 474, 432, 375]
  b' := [350, 427, 665, 148, 548, 818, 526, 805, 619]
  k := [270, 400, 457, 392, 974, 507, 620, 680, 1]
  f := [61, 412, 99, 374, 160, 342, 112, 416, 223, 1]
  g := [93, 628, 150, 570, 243, 521, 170, 634, 339, 1]
  h := [650, 1]
  a := [683, 729, 316, 637, 973, 598, 410, 927, 924]
  b := [234, 148, 43, 571, 900, 70, 983, 220, 67]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1811 : CertificateDedekindCriterionLists l 1811 where
  n := 2
  a' := [1042, 1704, 1277, 180, 1458, 112, 837, 659]
  b' := [1375, 683, 1102, 767, 745, 1446, 1373, 1483, 128]
  k := [999, 917, 415, 837, 953, 430, 191, 450, 1]
  f := [526, 185, 1137, 1233, 848, 1372, 638, 1504, 197, 1]
  g := [601, 211, 1299, 1408, 968, 1567, 728, 1718, 224, 1]
  h := [1585, 1]
  a := [1451, 508, 250, 1664, 237, 449, 97, 205, 1659]
  b := [1656, 1616, 1758, 1443, 40, 787, 1194, 1124, 152]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 461, 991, 1811]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 461, 991, 1811]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp461.out
    exact hp991.out
    exact hp1811.out
  a := [-38059580576, -1214634529156, 1106359267881, 3009495838934, -1818536258926, -1918521021464, 956661245078, 343901192598, -154219836260]
  b := [-33922794771, 112491252718, 397752373705, -351671580381, -585887634420, 326880701988, 267871987119, -122099585288, -37474515985, 15421983626]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 461 T_ofList CD461
    exact satisfiesDedekindCriterion_of_certificate_lists T l 991 T_ofList CD991
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1811 T_ofList CD1811

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

end VoightMaximalOrderD10R143

namespace VoightMaximalOrderD10R145

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2601619878125, [1, -4, -4, 27, -8, -38, 18, 16, -8, -2, 1], 1⟩
local notation "l" => [1, -4, -4, 27, -8, -38, 18, 16, -8, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 4, -27, 8, 38, -18, -16, 8, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 4, -27, 8, 38, -18, -16, 8, 2], ![-2, 7, 12, -50, -11, 84, 2, -50, 0, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 4, -27, 8, 38, -18, -16, 8, 2], ![-2, 7, 12, -50, -11, 84, 2, -50, 0, 12], ![-12, 46, 55, -312, 46, 445, -132, -190, 46, 24]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 4, -27, 8, 38, -18, -16, 8, 2], ![-2, 7, 12, -50, -11, 84, 2, -50, 0, 12], ![-12, 46, 55, -312, 46, 445, -132, -190, 46, 24], ![-24, 84, 142, -593, -120, 958, 13, -516, 2, 94]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 4, -27, 8, 38, -18, -16, 8, 2], ![-2, 7, 12, -50, -11, 84, 2, -50, 0, 12], ![-12, 46, 55, -312, 46, 445, -132, -190, 46, 24], ![-24, 84, 142, -593, -120, 958, 13, -516, 2, 94], ![-94, 352, 460, -2396, 159, 3452, -734, -1491, 236, 190]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 4, -27, 8, 38, -18, -16, 8, 2], ![-2, 7, 12, -50, -11, 84, 2, -50, 0, 12], ![-12, 46, 55, -312, 46, 445, -132, -190, 46, 24], ![-24, 84, 142, -593, -120, 958, 13, -516, 2, 94], ![-94, 352, 460, -2396, 159, 3452, -734, -1491, 236, 190], ![-190, 666, 1112, -4670, -876, 7379, 32, -3774, 29, 616]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 4, -27, 8, 38, -18, -16, 8, 2], ![-2, 7, 12, -50, -11, 84, 2, -50, 0, 12], ![-12, 46, 55, -312, 46, 445, -132, -190, 46, 24], ![-24, 84, 142, -593, -120, 958, 13, -516, 2, 94], ![-94, 352, 460, -2396, 159, 3452, -734, -1491, 236, 190], ![-190, 666, 1112, -4670, -876, 7379, 32, -3774, 29, 616], ![-616, 2274, 3130, -15520, 258, 22532, -3709, -9824, 1154, 1261]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 4, -27, 8, 38, -18, -16, 8, 2], ![-2, 7, 12, -50, -11, 84, 2, -50, 0, 12], ![-12, 46, 55, -312, 46, 445, -132, -190, 46, 24], ![-24, 84, 142, -593, -120, 958, 13, -516, 2, 94], ![-94, 352, 460, -2396, 159, 3452, -734, -1491, 236, 190], ![-190, 666, 1112, -4670, -876, 7379, 32, -3774, 29, 616], ![-616, 2274, 3130, -15520, 258, 22532, -3709, -9824, 1154, 1261], ![-1261, 4428, 7318, -30917, -5432, 48176, -166, -23885, 264, 3676]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 4, 4, -27, 8, 38, -18, -16, 8, 2], ![-2, 7, 12, -50, -11, 84, 2, -50, 0, 12], ![-12, 46, 55, -312, 46, 445, -132, -190, 46, 24], ![-24, 84, 142, -593, -120, 958, 13, -516, 2, 94], ![-94, 352, 460, -2396, 159, 3452, -734, -1491, 236, 190], ![-190, 666, 1112, -4670, -876, 7379, 32, -3774, 29, 616], ![-616, 2274, 3130, -15520, 258, 22532, -3709, -9824, 1154, 1261], ![-1261, 4428, 7318, -30917, -5432, 48176, -166, -23885, 264, 3676], ![-3676, 13443, 19132, -91934, -1509, 134256, -17992, -58982, 5523, 7616]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-12, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-12, -2, -1], [-24, -12, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-12, -2, -1], [-24, -12, -2, -1], [-94, -24, -12, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-12, -2, -1], [-24, -12, -2, -1], [-94, -24, -12, -2, -1], [-190, -94, -24, -12, -2, -1]], ![[], [], [], [-1], [-2, -1], [-12, -2, -1], [-24, -12, -2, -1], [-94, -24, -12, -2, -1], [-190, -94, -24, -12, -2, -1], [-616, -190, -94, -24, -12, -2, -1]], ![[], [], [-1], [-2, -1], [-12, -2, -1], [-24, -12, -2, -1], [-94, -24, -12, -2, -1], [-190, -94, -24, -12, -2, -1], [-616, -190, -94, -24, -12, -2, -1], [-1261, -616, -190, -94, -24, -12, -2, -1]], ![[], [-1], [-2, -1], [-12, -2, -1], [-24, -12, -2, -1], [-94, -24, -12, -2, -1], [-190, -94, -24, -12, -2, -1], [-616, -190, -94, -24, -12, -2, -1], [-1261, -616, -190, -94, -24, -12, -2, -1], [-3676, -1261, -616, -190, -94, -24, -12, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 4, -27, 8, 38, -18, -16, 8, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 4, -27, 8, 38, -18, -16, 8, 2], [-2, 7, 12, -50, -11, 84, 2, -50, 0, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 4, -27, 8, 38, -18, -16, 8, 2], [-2, 7, 12, -50, -11, 84, 2, -50, 0, 12], [-12, 46, 55, -312, 46, 445, -132, -190, 46, 24]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 4, -27, 8, 38, -18, -16, 8, 2], [-2, 7, 12, -50, -11, 84, 2, -50, 0, 12], [-12, 46, 55, -312, 46, 445, -132, -190, 46, 24], [-24, 84, 142, -593, -120, 958, 13, -516, 2, 94]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 4, -27, 8, 38, -18, -16, 8, 2], [-2, 7, 12, -50, -11, 84, 2, -50, 0, 12], [-12, 46, 55, -312, 46, 445, -132, -190, 46, 24], [-24, 84, 142, -593, -120, 958, 13, -516, 2, 94], [-94, 352, 460, -2396, 159, 3452, -734, -1491, 236, 190]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 4, -27, 8, 38, -18, -16, 8, 2], [-2, 7, 12, -50, -11, 84, 2, -50, 0, 12], [-12, 46, 55, -312, 46, 445, -132, -190, 46, 24], [-24, 84, 142, -593, -120, 958, 13, -516, 2, 94], [-94, 352, 460, -2396, 159, 3452, -734, -1491, 236, 190], [-190, 666, 1112, -4670, -876, 7379, 32, -3774, 29, 616]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 4, -27, 8, 38, -18, -16, 8, 2], [-2, 7, 12, -50, -11, 84, 2, -50, 0, 12], [-12, 46, 55, -312, 46, 445, -132, -190, 46, 24], [-24, 84, 142, -593, -120, 958, 13, -516, 2, 94], [-94, 352, 460, -2396, 159, 3452, -734, -1491, 236, 190], [-190, 666, 1112, -4670, -876, 7379, 32, -3774, 29, 616], [-616, 2274, 3130, -15520, 258, 22532, -3709, -9824, 1154, 1261]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 4, -27, 8, 38, -18, -16, 8, 2], [-2, 7, 12, -50, -11, 84, 2, -50, 0, 12], [-12, 46, 55, -312, 46, 445, -132, -190, 46, 24], [-24, 84, 142, -593, -120, 958, 13, -516, 2, 94], [-94, 352, 460, -2396, 159, 3452, -734, -1491, 236, 190], [-190, 666, 1112, -4670, -876, 7379, 32, -3774, 29, 616], [-616, 2274, 3130, -15520, 258, 22532, -3709, -9824, 1154, 1261], [-1261, 4428, 7318, -30917, -5432, 48176, -166, -23885, 264, 3676]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 4, 4, -27, 8, 38, -18, -16, 8, 2], [-2, 7, 12, -50, -11, 84, 2, -50, 0, 12], [-12, 46, 55, -312, 46, 445, -132, -190, 46, 24], [-24, 84, 142, -593, -120, 958, 13, -516, 2, 94], [-94, 352, 460, -2396, 159, 3452, -734, -1491, 236, 190], [-190, 666, 1112, -4670, -876, 7379, 32, -3774, 29, 616], [-616, 2274, 3130, -15520, 258, 22532, -3709, -9824, 1154, 1261], [-1261, 4428, 7318, -30917, -5432, 48176, -166, -23885, 264, 3676], [-3676, 13443, 19132, -91934, -1509, 134256, -17992, -58982, 5523, 7616]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp31 : Fact (Nat.Prime 31) := fact_iff.2 (by norm_num)
instance hp26855431 : Fact (Nat.Prime 26855431) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 2]
  b' := [2, 3, 0, 3]
  k := [1]
  f := [0, 2, 3, -3, 7, 14, 1, 2, 6, 2]
  g := [1, 3, 1, 3, 4, 1]
  h := [1, 3, 1, 3, 4, 1]
  a := [0, 1, 2, 0, 4]
  b := [1, 2, 1, 0, 1, 1, 0, 3, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD31 : CertificateDedekindCriterionLists l 31 where
  n := 2
  a' := [30, 14, 6, 16, 3, 30, 11, 28]
  b' := [28, 13, 15, 3, 10, 2, 17, 2, 21]
  k := [2, 22, 8, 6, 27, 7, 25, 21, 1]
  f := [1, 4, 4, 0, 3, 5, 2, 2, 4, 1]
  g := [8, 28, 23, 1, 21, 24, 14, 16, 25, 1]
  h := [4, 1]
  a := [9, 25, 25, 6, 22, 12, 8, 4, 24]
  b := [30, 23, 3, 14, 29, 18, 26, 4, 7]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD26855431 : CertificateDedekindCriterionLists l 26855431 where
  n := 2
  a' := [4926121, 20247683, 13431140, 22824429, 5437951, 26149507, 5421876, 18834741]
  b' := [6765181, 22106601, 16060031, 155020, 15768814, 15480450, 7897415, 21436596, 24762682]
  k := [1490100, 24389103, 6698934, 1416953, 19735011, 16729303, 11570358, 5318403, 1]
  f := [5751416, 8702374, 220841, 2571539, 1448345, 5700913, 4004157, 835636, 6450545, 1]
  g := [14343369, 21702717, 550750, 6413122, 3612005, 14217420, 9985905, 2083979, 16086916, 1]
  h := [10768513, 1]
  a := [4584221, 8031829, 6813230, 19721081, 18550031, 6304606, 8573944, 2478132, 19622991]
  b := [16006967, 10046118, 418025, 4261654, 9279458, 22039711, 16138568, 11881191, 7232440]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 31, 26855431]
  exp := ![1, 1, 1]
  pdgood := [5, 31, 26855431]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp31.out
    exact hp26855431.out
  a := [-226498759403, -1057068417576, 1878612935590, 2991634522084, -3157354844716, -1888320267288, 1557296295606, 314201008418, -224114808560]
  b := [-57665337802, 77562330613, 430372659160, -431287934454, -645573351096, 513562551970, 281382058444, -193372111870, -35902397013, 22411480856]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 31 T_ofList CD31
    exact satisfiesDedekindCriterion_of_certificate_lists T l 26855431 T_ofList CD26855431

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

end VoightMaximalOrderD10R145

end TraceEuclidean
