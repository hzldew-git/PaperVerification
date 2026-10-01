import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk208
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

namespace VoightMaximalOrderD10R487

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5592831903125, [1, -6, -3, 28, 1, -43, 4, 24, -4, -4, 1], 1⟩
local notation "l" => [1, -6, -3, 28, 1, -43, 4, 24, -4, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 3, -28, -1, 43, -4, -24, 4, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 3, -28, -1, 43, -4, -24, 4, 4], ![-4, 23, 18, -109, -32, 171, 27, -100, -8, 20]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 3, -28, -1, 43, -4, -24, 4, 4], ![-4, 23, 18, -109, -32, 171, 27, -100, -8, 20], ![-20, 116, 83, -542, -129, 828, 91, -453, -20, 72]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 3, -28, -1, 43, -4, -24, 4, 4], ![-4, 23, 18, -109, -32, 171, 27, -100, -8, 20], ![-20, 116, 83, -542, -129, 828, 91, -453, -20, 72], ![-72, 412, 332, -1933, -614, 2967, 540, -1637, -165, 268]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 3, -28, -1, 43, -4, -24, 4, 4], ![-4, 23, 18, -109, -32, 171, 27, -100, -8, 20], ![-20, 116, 83, -542, -129, 828, 91, -453, -20, 72], ![-72, 412, 332, -1933, -614, 2967, 540, -1637, -165, 268], ![-268, 1536, 1216, -7172, -2201, 10910, 1895, -5892, -565, 907]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 3, -28, -1, 43, -4, -24, 4, 4], ![-4, 23, 18, -109, -32, 171, 27, -100, -8, 20], ![-20, 116, 83, -542, -129, 828, 91, -453, -20, 72], ![-72, 412, 332, -1933, -614, 2967, 540, -1637, -165, 268], ![-268, 1536, 1216, -7172, -2201, 10910, 1895, -5892, -565, 907], ![-907, 5174, 4257, -24180, -8079, 36800, 7282, -19873, -2264, 3063]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 3, -28, -1, 43, -4, -24, 4, 4], ![-4, 23, 18, -109, -32, 171, 27, -100, -8, 20], ![-20, 116, 83, -542, -129, 828, 91, -453, -20, 72], ![-72, 412, 332, -1933, -614, 2967, 540, -1637, -165, 268], ![-268, 1536, 1216, -7172, -2201, 10910, 1895, -5892, -565, 907], ![-907, 5174, 4257, -24180, -8079, 36800, 7282, -19873, -2264, 3063], ![-3063, 17471, 14363, -81507, -27243, 123630, 24548, -66230, -7621, 9988]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 3, -28, -1, 43, -4, -24, 4, 4], ![-4, 23, 18, -109, -32, 171, 27, -100, -8, 20], ![-20, 116, 83, -542, -129, 828, 91, -453, -20, 72], ![-72, 412, 332, -1933, -614, 2967, 540, -1637, -165, 268], ![-268, 1536, 1216, -7172, -2201, 10910, 1895, -5892, -565, 907], ![-907, 5174, 4257, -24180, -8079, 36800, 7282, -19873, -2264, 3063], ![-3063, 17471, 14363, -81507, -27243, 123630, 24548, -66230, -7621, 9988], ![-9988, 56865, 47435, -265301, -91495, 402241, 83678, -215164, -26278, 32331]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, 3, -28, -1, 43, -4, -24, 4, 4], ![-4, 23, 18, -109, -32, 171, 27, -100, -8, 20], ![-20, 116, 83, -542, -129, 828, 91, -453, -20, 72], ![-72, 412, 332, -1933, -614, 2967, 540, -1637, -165, 268], ![-268, 1536, 1216, -7172, -2201, 10910, 1895, -5892, -565, 907], ![-907, 5174, 4257, -24180, -8079, 36800, 7282, -19873, -2264, 3063], ![-3063, 17471, 14363, -81507, -27243, 123630, 24548, -66230, -7621, 9988], ![-9988, 56865, 47435, -265301, -91495, 402241, 83678, -215164, -26278, 32331], ![-32331, 183998, 153858, -857833, -297632, 1298738, 272917, -692266, -85840, 103046]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-72, -20, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-72, -20, -4, -1], [-268, -72, -20, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-72, -20, -4, -1], [-268, -72, -20, -4, -1], [-907, -268, -72, -20, -4, -1]], ![[], [], [], [-1], [-4, -1], [-20, -4, -1], [-72, -20, -4, -1], [-268, -72, -20, -4, -1], [-907, -268, -72, -20, -4, -1], [-3063, -907, -268, -72, -20, -4, -1]], ![[], [], [-1], [-4, -1], [-20, -4, -1], [-72, -20, -4, -1], [-268, -72, -20, -4, -1], [-907, -268, -72, -20, -4, -1], [-3063, -907, -268, -72, -20, -4, -1], [-9988, -3063, -907, -268, -72, -20, -4, -1]], ![[], [-1], [-4, -1], [-20, -4, -1], [-72, -20, -4, -1], [-268, -72, -20, -4, -1], [-907, -268, -72, -20, -4, -1], [-3063, -907, -268, -72, -20, -4, -1], [-9988, -3063, -907, -268, -72, -20, -4, -1], [-32331, -9988, -3063, -907, -268, -72, -20, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 3, -28, -1, 43, -4, -24, 4, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 3, -28, -1, 43, -4, -24, 4, 4], [-4, 23, 18, -109, -32, 171, 27, -100, -8, 20]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 3, -28, -1, 43, -4, -24, 4, 4], [-4, 23, 18, -109, -32, 171, 27, -100, -8, 20], [-20, 116, 83, -542, -129, 828, 91, -453, -20, 72]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 3, -28, -1, 43, -4, -24, 4, 4], [-4, 23, 18, -109, -32, 171, 27, -100, -8, 20], [-20, 116, 83, -542, -129, 828, 91, -453, -20, 72], [-72, 412, 332, -1933, -614, 2967, 540, -1637, -165, 268]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 3, -28, -1, 43, -4, -24, 4, 4], [-4, 23, 18, -109, -32, 171, 27, -100, -8, 20], [-20, 116, 83, -542, -129, 828, 91, -453, -20, 72], [-72, 412, 332, -1933, -614, 2967, 540, -1637, -165, 268], [-268, 1536, 1216, -7172, -2201, 10910, 1895, -5892, -565, 907]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 3, -28, -1, 43, -4, -24, 4, 4], [-4, 23, 18, -109, -32, 171, 27, -100, -8, 20], [-20, 116, 83, -542, -129, 828, 91, -453, -20, 72], [-72, 412, 332, -1933, -614, 2967, 540, -1637, -165, 268], [-268, 1536, 1216, -7172, -2201, 10910, 1895, -5892, -565, 907], [-907, 5174, 4257, -24180, -8079, 36800, 7282, -19873, -2264, 3063]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 3, -28, -1, 43, -4, -24, 4, 4], [-4, 23, 18, -109, -32, 171, 27, -100, -8, 20], [-20, 116, 83, -542, -129, 828, 91, -453, -20, 72], [-72, 412, 332, -1933, -614, 2967, 540, -1637, -165, 268], [-268, 1536, 1216, -7172, -2201, 10910, 1895, -5892, -565, 907], [-907, 5174, 4257, -24180, -8079, 36800, 7282, -19873, -2264, 3063], [-3063, 17471, 14363, -81507, -27243, 123630, 24548, -66230, -7621, 9988]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 3, -28, -1, 43, -4, -24, 4, 4], [-4, 23, 18, -109, -32, 171, 27, -100, -8, 20], [-20, 116, 83, -542, -129, 828, 91, -453, -20, 72], [-72, 412, 332, -1933, -614, 2967, 540, -1637, -165, 268], [-268, 1536, 1216, -7172, -2201, 10910, 1895, -5892, -565, 907], [-907, 5174, 4257, -24180, -8079, 36800, 7282, -19873, -2264, 3063], [-3063, 17471, 14363, -81507, -27243, 123630, 24548, -66230, -7621, 9988], [-9988, 56865, 47435, -265301, -91495, 402241, 83678, -215164, -26278, 32331]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, 3, -28, -1, 43, -4, -24, 4, 4], [-4, 23, 18, -109, -32, 171, 27, -100, -8, 20], [-20, 116, 83, -542, -129, 828, 91, -453, -20, 72], [-72, 412, 332, -1933, -614, 2967, 540, -1637, -165, 268], [-268, 1536, 1216, -7172, -2201, 10910, 1895, -5892, -565, 907], [-907, 5174, 4257, -24180, -8079, 36800, 7282, -19873, -2264, 3063], [-3063, 17471, 14363, -81507, -27243, 123630, 24548, -66230, -7621, 9988], [-9988, 56865, 47435, -265301, -91495, 402241, 83678, -215164, -26278, 32331], [-32331, 183998, 153858, -857833, -297632, 1298738, 272917, -692266, -85840, 103046]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp151 : Fact (Nat.Prime 151) := fact_iff.2 (by norm_num)
instance hp11852359 : Fact (Nat.Prime 11852359) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 2, 4]
  b' := [2, 4, 3, 1, 3]
  k := [1]
  f := [0, 2, 3, -2, 5, 13, 5, -2, 3, 2]
  g := [1, 2, 4, 1, 3, 1]
  h := [1, 2, 4, 1, 3, 1]
  a := [1, 2, 4, 4]
  b := [1, 1, 2, 4, 4, 3, 4, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD151 : CertificateDedekindCriterionLists l 151 where
  n := 2
  a' := [28, 86, 6, 141, 112, 43, 47, 88]
  b' := [91, 2, 36, 72, 96, 62, 148, 45, 7]
  k := [62, 74, 63, 100, 22, 60, 56, 90, 1]
  f := [73, 40, 92, 31, 85, 50, 101, 38, 30, 1]
  g := [106, 57, 133, 44, 123, 71, 146, 54, 43, 1]
  h := [104, 1]
  a := [65, 97, 55, 68, 48, 99, 57, 81, 149]
  b := [92, 80, 91, 146, 26, 63, 119, 44, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11852359 : CertificateDedekindCriterionLists l 11852359 where
  n := 2
  a' := [1765645, 8355438, 870957, 5950074, 8622719, 1383699, 9106108, 10176491]
  b' := [1286264, 9056026, 5905155, 7384935, 6398151, 7545868, 10952901, 3880067, 9404709]
  k := [7679416, 11197833, 9725485, 2720390, 9918549, 3363258, 2367221, 825384, 1]
  f := [748731, 10974922, 8866077, 235527, 7493298, 7457863, 7724164, 7856941, 398321, 1]
  g := [775742, 11370850, 9185926, 244023, 7763624, 7726910, 8002818, 8140385, 412690, 1]
  h := [11439665, 1]
  a := [1527727, 7762905, 2375892, 7077309, 7162450, 7573167, 11191915, 1138457, 4131201]
  b := [10914905, 8513309, 5021776, 246256, 2201147, 5892572, 7962095, 3474840, 7721158]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 151, 11852359]
  exp := ![1, 1, 1]
  pdgood := [5, 151, 11852359]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp151.out
    exact hp11852359.out
  a := [-1770699031, -330163823868, -362464633641, 3548058540478, -43346517272, -3896161909630, 633886847884, 948310440230, -258901062700]
  b := [-1786538346, -51470066601, 297096930867, 91757484665, -817806477288, 23791793842, 571884815647, -83450105224, -105187086531, 25890106270]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 151 T_ofList CD151
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11852359 T_ofList CD11852359

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

end VoightMaximalOrderD10R487

namespace VoightMaximalOrderD10R491

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5599012878125, [-1, 14, 30, -30, -60, 18, 41, -3, -11, 0, 1], 1⟩
local notation "l" => [-1, 14, 30, -30, -60, 18, 41, -3, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -14, -30, 30, 60, -18, -41, 3, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -14, -30, 30, 60, -18, -41, 3, 11, 0], ![0, 1, -14, -30, 30, 60, -18, -41, 3, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -14, -30, 30, 60, -18, -41, 3, 11, 0], ![0, 1, -14, -30, 30, 60, -18, -41, 3, 11], ![11, -154, -329, 316, 630, -168, -391, 15, 80, 3]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -14, -30, 30, 60, -18, -41, 3, 11, 0], ![0, 1, -14, -30, 30, 60, -18, -41, 3, 11], ![11, -154, -329, 316, 630, -168, -391, 15, 80, 3], ![3, -31, -244, -239, 496, 576, -291, -382, 48, 80]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -14, -30, 30, 60, -18, -41, 3, 11, 0], ![0, 1, -14, -30, 30, 60, -18, -41, 3, 11], ![11, -154, -329, 316, 630, -168, -391, 15, 80, 3], ![3, -31, -244, -239, 496, 576, -291, -382, 48, 80], ![80, -1117, -2431, 2156, 4561, -944, -2704, -51, 498, 48]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -14, -30, 30, 60, -18, -41, 3, 11, 0], ![0, 1, -14, -30, 30, 60, -18, -41, 3, 11], ![11, -154, -329, 316, 630, -168, -391, 15, 80, 3], ![3, -31, -244, -239, 496, 576, -291, -382, 48, 80], ![80, -1117, -2431, 2156, 4561, -944, -2704, -51, 498, 48], ![48, -592, -2557, -991, 5036, 3697, -2912, -2560, 477, 498]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -14, -30, 30, 60, -18, -41, 3, 11, 0], ![0, 1, -14, -30, 30, 60, -18, -41, 3, 11], ![11, -154, -329, 316, 630, -168, -391, 15, 80, 3], ![3, -31, -244, -239, 496, 576, -291, -382, 48, 80], ![80, -1117, -2431, 2156, 4561, -944, -2704, -51, 498, 48], ![48, -592, -2557, -991, 5036, 3697, -2912, -2560, 477, 498], ![498, -6924, -15532, 12383, 28889, -3928, -16721, -1418, 2918, 477]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -14, -30, 30, 60, -18, -41, 3, 11, 0], ![0, 1, -14, -30, 30, 60, -18, -41, 3, 11], ![11, -154, -329, 316, 630, -168, -391, 15, 80, 3], ![3, -31, -244, -239, 496, 576, -291, -382, 48, 80], ![80, -1117, -2431, 2156, 4561, -944, -2704, -51, 498, 48], ![48, -592, -2557, -991, 5036, 3697, -2912, -2560, 477, 498], ![498, -6924, -15532, 12383, 28889, -3928, -16721, -1418, 2918, 477], ![477, -6180, -21234, -1222, 41003, 20303, -23485, -15290, 3829, 2918]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -14, -30, 30, 60, -18, -41, 3, 11, 0], ![0, 1, -14, -30, 30, 60, -18, -41, 3, 11], ![11, -154, -329, 316, 630, -168, -391, 15, 80, 3], ![3, -31, -244, -239, 496, 576, -291, -382, 48, 80], ![80, -1117, -2431, 2156, 4561, -944, -2704, -51, 498, 48], ![48, -592, -2557, -991, 5036, 3697, -2912, -2560, 477, 498], ![498, -6924, -15532, 12383, 28889, -3928, -16721, -1418, 2918, 477], ![477, -6180, -21234, -1222, 41003, 20303, -23485, -15290, 3829, 2918], ![2918, -40375, -93720, 66306, 173858, -11521, -99335, -14731, 16808, 3829]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-80, -3, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-80, -3, -11, 0, -1], [-48, -80, -3, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-80, -3, -11, 0, -1], [-48, -80, -3, -11, 0, -1], [-498, -48, -80, -3, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-80, -3, -11, 0, -1], [-48, -80, -3, -11, 0, -1], [-498, -48, -80, -3, -11, 0, -1], [-477, -498, -48, -80, -3, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-80, -3, -11, 0, -1], [-48, -80, -3, -11, 0, -1], [-498, -48, -80, -3, -11, 0, -1], [-477, -498, -48, -80, -3, -11, 0, -1], [-2918, -477, -498, -48, -80, -3, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -14, -30, 30, 60, -18, -41, 3, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -14, -30, 30, 60, -18, -41, 3, 11, 0], [0, 1, -14, -30, 30, 60, -18, -41, 3, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -14, -30, 30, 60, -18, -41, 3, 11, 0], [0, 1, -14, -30, 30, 60, -18, -41, 3, 11], [11, -154, -329, 316, 630, -168, -391, 15, 80, 3]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -14, -30, 30, 60, -18, -41, 3, 11, 0], [0, 1, -14, -30, 30, 60, -18, -41, 3, 11], [11, -154, -329, 316, 630, -168, -391, 15, 80, 3], [3, -31, -244, -239, 496, 576, -291, -382, 48, 80]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -14, -30, 30, 60, -18, -41, 3, 11, 0], [0, 1, -14, -30, 30, 60, -18, -41, 3, 11], [11, -154, -329, 316, 630, -168, -391, 15, 80, 3], [3, -31, -244, -239, 496, 576, -291, -382, 48, 80], [80, -1117, -2431, 2156, 4561, -944, -2704, -51, 498, 48]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -14, -30, 30, 60, -18, -41, 3, 11, 0], [0, 1, -14, -30, 30, 60, -18, -41, 3, 11], [11, -154, -329, 316, 630, -168, -391, 15, 80, 3], [3, -31, -244, -239, 496, 576, -291, -382, 48, 80], [80, -1117, -2431, 2156, 4561, -944, -2704, -51, 498, 48], [48, -592, -2557, -991, 5036, 3697, -2912, -2560, 477, 498]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -14, -30, 30, 60, -18, -41, 3, 11, 0], [0, 1, -14, -30, 30, 60, -18, -41, 3, 11], [11, -154, -329, 316, 630, -168, -391, 15, 80, 3], [3, -31, -244, -239, 496, 576, -291, -382, 48, 80], [80, -1117, -2431, 2156, 4561, -944, -2704, -51, 498, 48], [48, -592, -2557, -991, 5036, 3697, -2912, -2560, 477, 498], [498, -6924, -15532, 12383, 28889, -3928, -16721, -1418, 2918, 477]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -14, -30, 30, 60, -18, -41, 3, 11, 0], [0, 1, -14, -30, 30, 60, -18, -41, 3, 11], [11, -154, -329, 316, 630, -168, -391, 15, 80, 3], [3, -31, -244, -239, 496, 576, -291, -382, 48, 80], [80, -1117, -2431, 2156, 4561, -944, -2704, -51, 498, 48], [48, -592, -2557, -991, 5036, 3697, -2912, -2560, 477, 498], [498, -6924, -15532, 12383, 28889, -3928, -16721, -1418, 2918, 477], [477, -6180, -21234, -1222, 41003, 20303, -23485, -15290, 3829, 2918]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -14, -30, 30, 60, -18, -41, 3, 11, 0], [0, 1, -14, -30, 30, 60, -18, -41, 3, 11], [11, -154, -329, 316, 630, -168, -391, 15, 80, 3], [3, -31, -244, -239, 496, 576, -291, -382, 48, 80], [80, -1117, -2431, 2156, 4561, -944, -2704, -51, 498, 48], [48, -592, -2557, -991, 5036, 3697, -2912, -2560, 477, 498], [498, -6924, -15532, 12383, 28889, -3928, -16721, -1418, 2918, 477], [477, -6180, -21234, -1222, 41003, 20303, -23485, -15290, 3829, 2918], [2918, -40375, -93720, 66306, 173858, -11521, -99335, -14731, 16808, 3829]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp109 : Fact (Nat.Prime 109) := fact_iff.2 (by norm_num)
instance hp16437469 : Fact (Nat.Prime 16437469) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4]
  b' := [3, 0, 3, 1]
  k := [1]
  f := [1, -2, -5, 8, 13, -2, -7, 1, 3]
  g := [2, 1, 1, 2, 0, 1]
  h := [2, 1, 1, 2, 0, 1]
  a := [4, 4, 0, 4, 3]
  b := [1, 4, 4, 2, 1, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD109 : CertificateDedekindCriterionLists l 109 where
  n := 2
  a' := [106, 31, 47, 73, 89, 40, 83, 5]
  b' := [73, 55, 35, 14, 92, 87, 61, 13, 60]
  k := [1, 52, 24, 31, 59, 92, 95, 43, 1]
  f := [10, 25, 25, 21, 6, 13, 20, 30, 24, 1]
  g := [33, 82, 81, 66, 16, 43, 66, 97, 76, 1]
  h := [33, 1]
  a := [69, 62, 100, 89, 20, 56, 55, 7, 75]
  b := [65, 68, 44, 107, 60, 86, 73, 78, 34]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD16437469 : CertificateDedekindCriterionLists l 16437469 where
  n := 2
  a' := [10780953, 10089125, 3725881, 10498358, 13223359, 16435298, 5675408, 2465814]
  b' := [9582958, 14743135, 4086355, 870752, 1921488, 9496858, 10274897, 8640832, 5205177]
  k := [15313381, 4686773, 13035110, 8495910, 12077575, 15529904, 9506668, 15276711, 1]
  f := [214507, 518866, 458960, 514946, 54868, 94170, 104696, 111888, 559887, 1]
  g := [6075258, 14695290, 12998620, 14584256, 1553944, 2667076, 2965191, 3168882, 15857090, 1]
  h := [580379, 1]
  a := [16120994, 3571048, 8659282, 6436026, 12746039, 11059611, 6171083, 10660453, 14685694]
  b := [10293109, 8868616, 1638754, 11410450, 12864973, 14815032, 3403778, 14016286, 1751775]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 109, 16437469]
  exp := ![1, 1, 1]
  pdgood := [5, 109, 16437469]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp109.out
    exact hp16437469.out
  a := [-289523804795, -998912864980, 2636219874178, 2857806100976, -4083415491226, -1866943694338, 1886228851516, 339962209900, -264371663220]
  b := [-20040384585, 304060248375, 375676043757, -910888064574, -519706380865, 775654483034, 237692605922, -246784651060, -33996220990, 26437166322]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 109 T_ofList CD109
    exact satisfiesDedekindCriterion_of_certificate_lists T l 16437469 T_ofList CD16437469

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

end VoightMaximalOrderD10R491

namespace VoightMaximalOrderD10R492

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5619032377856, [-1, -2, 23, 24, -56, -23, 40, 8, -11, -1, 1], 1⟩
local notation "l" => [-1, -2, 23, 24, -56, -23, 40, 8, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -23, -24, 56, 23, -40, -8, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -23, -24, 56, 23, -40, -8, 11, 1], ![1, 3, -21, -47, 32, 79, -17, -48, 3, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -23, -24, 56, 23, -40, -8, 11, 1], ![1, 3, -21, -47, 32, 79, -17, -48, 3, 12], ![12, 25, -273, -309, 625, 308, -401, -113, 84, 15]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -23, -24, 56, 23, -40, -8, 11, 1], ![1, 3, -21, -47, 32, 79, -17, -48, 3, 12], ![12, 25, -273, -309, 625, 308, -401, -113, 84, 15], ![15, 42, -320, -633, 531, 970, -292, -521, 52, 99]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -23, -24, 56, 23, -40, -8, 11, 1], ![1, 3, -21, -47, 32, 79, -17, -48, 3, 12], ![12, 25, -273, -309, 625, 308, -401, -113, 84, 15], ![15, 42, -320, -633, 531, 970, -292, -521, 52, 99], ![99, 213, -2235, -2696, 4911, 2808, -2990, -1084, 568, 151]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -23, -24, 56, 23, -40, -8, 11, 1], ![1, 3, -21, -47, 32, 79, -17, -48, 3, 12], ![12, 25, -273, -309, 625, 308, -401, -113, 84, 15], ![15, 42, -320, -633, 531, 970, -292, -521, 52, 99], ![99, 213, -2235, -2696, 4911, 2808, -2990, -1084, 568, 151], ![151, 401, -3260, -5859, 5760, 8384, -3232, -4198, 577, 719]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -23, -24, 56, 23, -40, -8, 11, 1], ![1, 3, -21, -47, 32, 79, -17, -48, 3, 12], ![12, 25, -273, -309, 625, 308, -401, -113, 84, 15], ![15, 42, -320, -633, 531, 970, -292, -521, 52, 99], ![99, 213, -2235, -2696, 4911, 2808, -2990, -1084, 568, 151], ![151, 401, -3260, -5859, 5760, 8384, -3232, -4198, 577, 719], ![719, 1589, -16136, -20516, 34405, 22297, -20376, -8984, 3711, 1296]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -23, -24, 56, 23, -40, -8, 11, 1], ![1, 3, -21, -47, 32, 79, -17, -48, 3, 12], ![12, 25, -273, -309, 625, 308, -401, -113, 84, 15], ![15, 42, -320, -633, 531, 970, -292, -521, 52, 99], ![99, 213, -2235, -2696, 4911, 2808, -2990, -1084, 568, 151], ![151, 401, -3260, -5859, 5760, 8384, -3232, -4198, 577, 719], ![719, 1589, -16136, -20516, 34405, 22297, -20376, -8984, 3711, 1296], ![1296, 3311, -28219, -47240, 52060, 64213, -29543, -30744, 5272, 5007]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -23, -24, 56, 23, -40, -8, 11, 1], ![1, 3, -21, -47, 32, 79, -17, -48, 3, 12], ![12, 25, -273, -309, 625, 308, -401, -113, 84, 15], ![15, 42, -320, -633, 531, 970, -292, -521, 52, 99], ![99, 213, -2235, -2696, 4911, 2808, -2990, -1084, 568, 151], ![151, 401, -3260, -5859, 5760, 8384, -3232, -4198, 577, 719], ![719, 1589, -16136, -20516, 34405, 22297, -20376, -8984, 3711, 1296], ![1296, 3311, -28219, -47240, 52060, 64213, -29543, -30744, 5272, 5007], ![5007, 11310, -111850, -148387, 233152, 167221, -136067, -69599, 24333, 10279]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-15, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-15, -12, -1, -1], [-99, -15, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-15, -12, -1, -1], [-99, -15, -12, -1, -1], [-151, -99, -15, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-15, -12, -1, -1], [-99, -15, -12, -1, -1], [-151, -99, -15, -12, -1, -1], [-719, -151, -99, -15, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-15, -12, -1, -1], [-99, -15, -12, -1, -1], [-151, -99, -15, -12, -1, -1], [-719, -151, -99, -15, -12, -1, -1], [-1296, -719, -151, -99, -15, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-15, -12, -1, -1], [-99, -15, -12, -1, -1], [-151, -99, -15, -12, -1, -1], [-719, -151, -99, -15, -12, -1, -1], [-1296, -719, -151, -99, -15, -12, -1, -1], [-5007, -1296, -719, -151, -99, -15, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -23, -24, 56, 23, -40, -8, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -23, -24, 56, 23, -40, -8, 11, 1], [1, 3, -21, -47, 32, 79, -17, -48, 3, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -23, -24, 56, 23, -40, -8, 11, 1], [1, 3, -21, -47, 32, 79, -17, -48, 3, 12], [12, 25, -273, -309, 625, 308, -401, -113, 84, 15]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -23, -24, 56, 23, -40, -8, 11, 1], [1, 3, -21, -47, 32, 79, -17, -48, 3, 12], [12, 25, -273, -309, 625, 308, -401, -113, 84, 15], [15, 42, -320, -633, 531, 970, -292, -521, 52, 99]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -23, -24, 56, 23, -40, -8, 11, 1], [1, 3, -21, -47, 32, 79, -17, -48, 3, 12], [12, 25, -273, -309, 625, 308, -401, -113, 84, 15], [15, 42, -320, -633, 531, 970, -292, -521, 52, 99], [99, 213, -2235, -2696, 4911, 2808, -2990, -1084, 568, 151]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -23, -24, 56, 23, -40, -8, 11, 1], [1, 3, -21, -47, 32, 79, -17, -48, 3, 12], [12, 25, -273, -309, 625, 308, -401, -113, 84, 15], [15, 42, -320, -633, 531, 970, -292, -521, 52, 99], [99, 213, -2235, -2696, 4911, 2808, -2990, -1084, 568, 151], [151, 401, -3260, -5859, 5760, 8384, -3232, -4198, 577, 719]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -23, -24, 56, 23, -40, -8, 11, 1], [1, 3, -21, -47, 32, 79, -17, -48, 3, 12], [12, 25, -273, -309, 625, 308, -401, -113, 84, 15], [15, 42, -320, -633, 531, 970, -292, -521, 52, 99], [99, 213, -2235, -2696, 4911, 2808, -2990, -1084, 568, 151], [151, 401, -3260, -5859, 5760, 8384, -3232, -4198, 577, 719], [719, 1589, -16136, -20516, 34405, 22297, -20376, -8984, 3711, 1296]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -23, -24, 56, 23, -40, -8, 11, 1], [1, 3, -21, -47, 32, 79, -17, -48, 3, 12], [12, 25, -273, -309, 625, 308, -401, -113, 84, 15], [15, 42, -320, -633, 531, 970, -292, -521, 52, 99], [99, 213, -2235, -2696, 4911, 2808, -2990, -1084, 568, 151], [151, 401, -3260, -5859, 5760, 8384, -3232, -4198, 577, 719], [719, 1589, -16136, -20516, 34405, 22297, -20376, -8984, 3711, 1296], [1296, 3311, -28219, -47240, 52060, 64213, -29543, -30744, 5272, 5007]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -23, -24, 56, 23, -40, -8, 11, 1], [1, 3, -21, -47, 32, 79, -17, -48, 3, 12], [12, 25, -273, -309, 625, 308, -401, -113, 84, 15], [15, 42, -320, -633, 531, 970, -292, -521, 52, 99], [99, 213, -2235, -2696, 4911, 2808, -2990, -1084, 568, 151], [151, 401, -3260, -5859, 5760, 8384, -3232, -4198, 577, 719], [719, 1589, -16136, -20516, 34405, 22297, -20376, -8984, 3711, 1296], [1296, 3311, -28219, -47240, 52060, 64213, -29543, -30744, 5272, 5007], [5007, 11310, -111850, -148387, 233152, 167221, -136067, -69599, 24333, 10279]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp73 : Fact (Nat.Prime 73) := fact_iff.2 (by norm_num)
instance hp150337981 : Fact (Nat.Prime 150337981) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 4
  a' := [0, 0, 0, 0, 1]
  b' := [1, 0, 1, 0, 0, 1]
  k := [1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1]
  f := [1, 2, -10, -10, 30, 13, -19, -3, 6, 1]
  g := [1, 1, 1, 1, 1, 0, 0, 1]
  h := [1, 1, 1, 1]
  a := [1, 1, 1, 1, 0, 0, 1]
  b := [0, 1, 0, 0, 1, 1, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD73 : CertificateDedekindCriterionLists l 73 where
  n := 2
  a' := [1, 12, 25, 47, 13, 37, 16, 6]
  b' := [15, 7, 61, 7, 15, 34, 4, 36, 48]
  k := [18, 54, 37, 66, 61, 57, 70, 3, 1]
  f := [36, 55, 52, 50, 18, 20, 61, 63, 2, 1]
  g := [37, 56, 53, 51, 17, 20, 63, 64, 1, 1]
  h := [71, 1]
  a := [12, 54, 36, 37, 17, 37, 11, 15, 66]
  b := [14, 13, 55, 5, 6, 45, 33, 65, 7]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD150337981 : CertificateDedekindCriterionLists l 150337981 where
  n := 2
  a' := [38150809, 90984862, 82285000, 144914250, 149841218, 18156432, 50533261, 93513122]
  b' := [138674450, 58174137, 42036751, 128823036, 112501816, 33813295, 70559230, 63713336, 123243414]
  k := [116146286, 148874344, 114140886, 50172326, 129858276, 123492441, 91526342, 144495596, 1]
  f := [2718149, 258288, 966794, 2276835, 1850732, 2031331, 2233931, 611732, 2864431, 1]
  g := [139888454, 13292641, 49755663, 117176388, 95247144, 104541607, 114968332, 31482504, 147416788, 1]
  h := [2921192, 1]
  a := [9510901, 45914816, 13133096, 50896718, 43009582, 112226232, 143256222, 133909666, 108894502]
  b := [14928180, 62911341, 9692511, 14416301, 9745459, 44026332, 43252598, 102207596, 41443479]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 73, 150337981]
  exp := ![3, 1, 1]
  pdgood := [2, 73, 150337981]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp73.out
    exact hp150337981.out
  a := [-72773518250, -315774281704, 852574394896, 903472521816, -1689631728695, -772265249473, 982160658441, 172058697871, -147347283090]
  b := [-7511931327, 57886238581, 113545583972, -272207785504, -230144698982, 335362203413, 118478085329, -130238006693, -18679342618, 14734728309]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 73 T_ofList CD73
    exact satisfiesDedekindCriterion_of_certificate_lists T l 150337981 T_ofList CD150337981

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

end VoightMaximalOrderD10R492

namespace VoightMaximalOrderD10R500

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5681435815625, [1, -3, -13, 43, -2, -55, 14, 23, -7, -3, 1], 1⟩
local notation "l" => [1, -3, -13, 43, -2, -55, 14, 23, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 13, -43, 2, 55, -14, -23, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 13, -43, 2, 55, -14, -23, 7, 3], ![-3, 8, 42, -116, -37, 167, 13, -83, -2, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 13, -43, 2, 55, -14, -23, 7, 3], ![-3, 8, 42, -116, -37, 167, 13, -83, -2, 16], ![-16, 45, 216, -646, -84, 843, -57, -355, 29, 46]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 13, -43, 2, 55, -14, -23, 7, 3], ![-3, 8, 42, -116, -37, 167, 13, -83, -2, 16], ![-16, 45, 216, -646, -84, 843, -57, -355, 29, 46], ![-46, 122, 643, -1762, -554, 2446, 199, -1115, -33, 167]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 13, -43, 2, 55, -14, -23, 7, 3], ![-3, 8, 42, -116, -37, 167, 13, -83, -2, 16], ![-16, 45, 216, -646, -84, 843, -57, -355, 29, 46], ![-46, 122, 643, -1762, -554, 2446, 199, -1115, -33, 167], ![-167, 455, 2293, -6538, -1428, 8631, 108, -3642, 54, 468]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 13, -43, 2, 55, -14, -23, 7, 3], ![-3, 8, 42, -116, -37, 167, 13, -83, -2, 16], ![-16, 45, 216, -646, -84, 843, -57, -355, 29, 46], ![-46, 122, 643, -1762, -554, 2446, 199, -1115, -33, 167], ![-167, 455, 2293, -6538, -1428, 8631, 108, -3642, 54, 468], ![-468, 1237, 6539, -17831, -5602, 24312, 2079, -10656, -366, 1458]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 13, -43, 2, 55, -14, -23, 7, 3], ![-3, 8, 42, -116, -37, 167, 13, -83, -2, 16], ![-16, 45, 216, -646, -84, 843, -57, -355, 29, 46], ![-46, 122, 643, -1762, -554, 2446, 199, -1115, -33, 167], ![-167, 455, 2293, -6538, -1428, 8631, 108, -3642, 54, 468], ![-468, 1237, 6539, -17831, -5602, 24312, 2079, -10656, -366, 1458], ![-1458, 3906, 20191, -56155, -14915, 74588, 3900, -31455, -450, 4008]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 13, -43, 2, 55, -14, -23, 7, 3], ![-3, 8, 42, -116, -37, 167, 13, -83, -2, 16], ![-16, 45, 216, -646, -84, 843, -57, -355, 29, 46], ![-46, 122, 643, -1762, -554, 2446, 199, -1115, -33, 167], ![-167, 455, 2293, -6538, -1428, 8631, 108, -3642, 54, 468], ![-468, 1237, 6539, -17831, -5602, 24312, 2079, -10656, -366, 1458], ![-1458, 3906, 20191, -56155, -14915, 74588, 3900, -31455, -450, 4008], ![-4008, 10566, 56010, -152153, -48139, 205525, 18476, -88284, -3399, 11574]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 13, -43, 2, 55, -14, -23, 7, 3], ![-3, 8, 42, -116, -37, 167, 13, -83, -2, 16], ![-16, 45, 216, -646, -84, 843, -57, -355, 29, 46], ![-46, 122, 643, -1762, -554, 2446, 199, -1115, -33, 167], ![-167, 455, 2293, -6538, -1428, 8631, 108, -3642, 54, 468], ![-468, 1237, 6539, -17831, -5602, 24312, 2079, -10656, -366, 1458], ![-1458, 3906, 20191, -56155, -14915, 74588, 3900, -31455, -450, 4008], ![-4008, 10566, 56010, -152153, -48139, 205525, 18476, -88284, -3399, 11574], ![-11574, 30714, 161028, -441672, -129005, 588431, 43489, -247726, -7266, 31323]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-167, -46, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-167, -46, -16, -3, -1], [-468, -167, -46, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-167, -46, -16, -3, -1], [-468, -167, -46, -16, -3, -1], [-1458, -468, -167, -46, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-167, -46, -16, -3, -1], [-468, -167, -46, -16, -3, -1], [-1458, -468, -167, -46, -16, -3, -1], [-4008, -1458, -468, -167, -46, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-46, -16, -3, -1], [-167, -46, -16, -3, -1], [-468, -167, -46, -16, -3, -1], [-1458, -468, -167, -46, -16, -3, -1], [-4008, -1458, -468, -167, -46, -16, -3, -1], [-11574, -4008, -1458, -468, -167, -46, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 13, -43, 2, 55, -14, -23, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 13, -43, 2, 55, -14, -23, 7, 3], [-3, 8, 42, -116, -37, 167, 13, -83, -2, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 13, -43, 2, 55, -14, -23, 7, 3], [-3, 8, 42, -116, -37, 167, 13, -83, -2, 16], [-16, 45, 216, -646, -84, 843, -57, -355, 29, 46]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 13, -43, 2, 55, -14, -23, 7, 3], [-3, 8, 42, -116, -37, 167, 13, -83, -2, 16], [-16, 45, 216, -646, -84, 843, -57, -355, 29, 46], [-46, 122, 643, -1762, -554, 2446, 199, -1115, -33, 167]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 13, -43, 2, 55, -14, -23, 7, 3], [-3, 8, 42, -116, -37, 167, 13, -83, -2, 16], [-16, 45, 216, -646, -84, 843, -57, -355, 29, 46], [-46, 122, 643, -1762, -554, 2446, 199, -1115, -33, 167], [-167, 455, 2293, -6538, -1428, 8631, 108, -3642, 54, 468]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 13, -43, 2, 55, -14, -23, 7, 3], [-3, 8, 42, -116, -37, 167, 13, -83, -2, 16], [-16, 45, 216, -646, -84, 843, -57, -355, 29, 46], [-46, 122, 643, -1762, -554, 2446, 199, -1115, -33, 167], [-167, 455, 2293, -6538, -1428, 8631, 108, -3642, 54, 468], [-468, 1237, 6539, -17831, -5602, 24312, 2079, -10656, -366, 1458]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 13, -43, 2, 55, -14, -23, 7, 3], [-3, 8, 42, -116, -37, 167, 13, -83, -2, 16], [-16, 45, 216, -646, -84, 843, -57, -355, 29, 46], [-46, 122, 643, -1762, -554, 2446, 199, -1115, -33, 167], [-167, 455, 2293, -6538, -1428, 8631, 108, -3642, 54, 468], [-468, 1237, 6539, -17831, -5602, 24312, 2079, -10656, -366, 1458], [-1458, 3906, 20191, -56155, -14915, 74588, 3900, -31455, -450, 4008]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 13, -43, 2, 55, -14, -23, 7, 3], [-3, 8, 42, -116, -37, 167, 13, -83, -2, 16], [-16, 45, 216, -646, -84, 843, -57, -355, 29, 46], [-46, 122, 643, -1762, -554, 2446, 199, -1115, -33, 167], [-167, 455, 2293, -6538, -1428, 8631, 108, -3642, 54, 468], [-468, 1237, 6539, -17831, -5602, 24312, 2079, -10656, -366, 1458], [-1458, 3906, 20191, -56155, -14915, 74588, 3900, -31455, -450, 4008], [-4008, 10566, 56010, -152153, -48139, 205525, 18476, -88284, -3399, 11574]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 13, -43, 2, 55, -14, -23, 7, 3], [-3, 8, 42, -116, -37, 167, 13, -83, -2, 16], [-16, 45, 216, -646, -84, 843, -57, -355, 29, 46], [-46, 122, 643, -1762, -554, 2446, 199, -1115, -33, 167], [-167, 455, 2293, -6538, -1428, 8631, 108, -3642, 54, 468], [-468, 1237, 6539, -17831, -5602, 24312, 2079, -10656, -366, 1458], [-1458, 3906, 20191, -56155, -14915, 74588, 3900, -31455, -450, 4008], [-4008, 10566, 56010, -152153, -48139, 205525, 18476, -88284, -3399, 11574], [-11574, 30714, 161028, -441672, -129005, 588431, 43489, -247726, -7266, 31323]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1818059461 : Fact (Nat.Prime 1818059461) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 3, 4]
  b' := [0, 1, 4, 4, 4]
  k := [1]
  f := [0, 1, 4, -7, 3, 13, -1, -3, 2, 1]
  g := [1, 1, 3, 1, 1, 1]
  h := [1, 1, 3, 1, 1, 1]
  a := [0, 1, 3, 4, 3]
  b := [1, 4, 2, 3, 2, 1, 3, 3, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1818059461 : CertificateDedekindCriterionLists l 1818059461 where
  n := 2
  a' := [442815146, 1225326148, 753741735, 915721552, 1812010372, 362842386, 1720021562, 199637375]
  b' := [478374531, 1597619954, 990899494, 281413388, 339013796, 658310527, 1309412083, 1370170232, 381831283]
  k := [1576605481, 1625225247, 1119609065, 1268665722, 866689917, 1756898975, 1245035867, 184852845, 1]
  f := [739061737, 1463259817, 493742670, 818583457, 356200561, 821244110, 545638524, 306185939, 87727651, 1]
  g := [778646534, 1541633300, 520187961, 862427507, 375278976, 865230667, 574863403, 322585527, 92426421, 1]
  h := [1725633037, 1]
  a := [510408987, 1418900286, 1524434432, 658968371, 1022919979, 1214652372, 1110100243, 1330144860, 955171109]
  b := [1386524854, 334890503, 686523467, 255650725, 48871956, 236081605, 1787544196, 986125874, 862888352]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 1818059461]
  exp := ![1, 1]
  pdgood := [5, 1818059461]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1818059461.out
  a := [-35230377334, -496624232456, 460782610456, 1191835447046, -701858035097, -736260479158, 343183417571, 126339839002, -53868398760]
  b := [-14773558213, -2273528972, 187324318987, -98277551034, -250316445515, 112031602647, 107818685475, -42433062713, -14250035863, 5386839876]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1818059461 T_ofList CD1818059461

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

end VoightMaximalOrderD10R500

end TraceEuclidean
