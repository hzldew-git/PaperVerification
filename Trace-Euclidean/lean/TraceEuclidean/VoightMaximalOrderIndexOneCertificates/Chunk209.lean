import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk205
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

namespace VoightMaximalOrderD10R449

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5320307480336, [1, -1, -12, 15, 28, -32, -18, 23, 1, -5, 1], 1⟩
local notation "l" => [1, -1, -12, 15, 28, -32, -18, 23, 1, -5, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 12, -15, -28, 32, 18, -23, -1, 5]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 12, -15, -28, 32, 18, -23, -1, 5], ![-5, 4, 61, -63, -155, 132, 122, -97, -28, 24]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 12, -15, -28, 32, 18, -23, -1, 5], ![-5, 4, 61, -63, -155, 132, 122, -97, -28, 24], ![-24, 19, 292, -299, -735, 613, 564, -430, -121, 92]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 12, -15, -28, 32, 18, -23, -1, 5], ![-5, 4, 61, -63, -155, 132, 122, -97, -28, 24], ![-24, 19, 292, -299, -735, 613, 564, -430, -121, 92], ![-92, 68, 1123, -1088, -2875, 2209, 2269, -1552, -522, 339]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 12, -15, -28, 32, 18, -23, -1, 5], ![-5, 4, 61, -63, -155, 132, 122, -97, -28, 24], ![-24, 19, 292, -299, -735, 613, 564, -430, -121, 92], ![-92, 68, 1123, -1088, -2875, 2209, 2269, -1552, -522, 339], ![-339, 247, 4136, -3962, -10580, 7973, 8311, -5528, -1891, 1173]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 12, -15, -28, 32, 18, -23, -1, 5], ![-5, 4, 61, -63, -155, 132, 122, -97, -28, 24], ![-24, 19, 292, -299, -735, 613, 564, -430, -121, 92], ![-92, 68, 1123, -1088, -2875, 2209, 2269, -1552, -522, 339], ![-339, 247, 4136, -3962, -10580, 7973, 8311, -5528, -1891, 1173], ![-1173, 834, 14323, -13459, -36806, 26956, 29087, -18668, -6701, 3974]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 12, -15, -28, 32, 18, -23, -1, 5], ![-5, 4, 61, -63, -155, 132, 122, -97, -28, 24], ![-24, 19, 292, -299, -735, 613, 564, -430, -121, 92], ![-92, 68, 1123, -1088, -2875, 2209, 2269, -1552, -522, 339], ![-339, 247, 4136, -3962, -10580, 7973, 8311, -5528, -1891, 1173], ![-1173, 834, 14323, -13459, -36806, 26956, 29087, -18668, -6701, 3974], ![-3974, 2801, 48522, -45287, -124731, 90362, 98488, -62315, -22642, 13169]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 12, -15, -28, 32, 18, -23, -1, 5], ![-5, 4, 61, -63, -155, 132, 122, -97, -28, 24], ![-24, 19, 292, -299, -735, 613, 564, -430, -121, 92], ![-92, 68, 1123, -1088, -2875, 2209, 2269, -1552, -522, 339], ![-339, 247, 4136, -3962, -10580, 7973, 8311, -5528, -1891, 1173], ![-1173, 834, 14323, -13459, -36806, 26956, 29087, -18668, -6701, 3974], ![-3974, 2801, 48522, -45287, -124731, 90362, 98488, -62315, -22642, 13169], ![-13169, 9195, 160829, -149013, -414019, 296677, 327404, -204399, -75484, 43203]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 1, 12, -15, -28, 32, 18, -23, -1, 5], ![-5, 4, 61, -63, -155, 132, 122, -97, -28, 24], ![-24, 19, 292, -299, -735, 613, 564, -430, -121, 92], ![-92, 68, 1123, -1088, -2875, 2209, 2269, -1552, -522, 339], ![-339, 247, 4136, -3962, -10580, 7973, 8311, -5528, -1891, 1173], ![-1173, 834, 14323, -13459, -36806, 26956, 29087, -18668, -6701, 3974], ![-3974, 2801, 48522, -45287, -124731, 90362, 98488, -62315, -22642, 13169], ![-13169, 9195, 160829, -149013, -414019, 296677, 327404, -204399, -75484, 43203], ![-43203, 30034, 527631, -487216, -1358697, 968477, 1074331, -666265, -247602, 140531]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-5, -1]], ![[], [], [], [], [], [], [], [-1], [-5, -1], [-24, -5, -1]], ![[], [], [], [], [], [], [-1], [-5, -1], [-24, -5, -1], [-92, -24, -5, -1]], ![[], [], [], [], [], [-1], [-5, -1], [-24, -5, -1], [-92, -24, -5, -1], [-339, -92, -24, -5, -1]], ![[], [], [], [], [-1], [-5, -1], [-24, -5, -1], [-92, -24, -5, -1], [-339, -92, -24, -5, -1], [-1173, -339, -92, -24, -5, -1]], ![[], [], [], [-1], [-5, -1], [-24, -5, -1], [-92, -24, -5, -1], [-339, -92, -24, -5, -1], [-1173, -339, -92, -24, -5, -1], [-3974, -1173, -339, -92, -24, -5, -1]], ![[], [], [-1], [-5, -1], [-24, -5, -1], [-92, -24, -5, -1], [-339, -92, -24, -5, -1], [-1173, -339, -92, -24, -5, -1], [-3974, -1173, -339, -92, -24, -5, -1], [-13169, -3974, -1173, -339, -92, -24, -5, -1]], ![[], [-1], [-5, -1], [-24, -5, -1], [-92, -24, -5, -1], [-339, -92, -24, -5, -1], [-1173, -339, -92, -24, -5, -1], [-3974, -1173, -339, -92, -24, -5, -1], [-13169, -3974, -1173, -339, -92, -24, -5, -1], [-43203, -13169, -3974, -1173, -339, -92, -24, -5, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 12, -15, -28, 32, 18, -23, -1, 5]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 12, -15, -28, 32, 18, -23, -1, 5], [-5, 4, 61, -63, -155, 132, 122, -97, -28, 24]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 12, -15, -28, 32, 18, -23, -1, 5], [-5, 4, 61, -63, -155, 132, 122, -97, -28, 24], [-24, 19, 292, -299, -735, 613, 564, -430, -121, 92]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 12, -15, -28, 32, 18, -23, -1, 5], [-5, 4, 61, -63, -155, 132, 122, -97, -28, 24], [-24, 19, 292, -299, -735, 613, 564, -430, -121, 92], [-92, 68, 1123, -1088, -2875, 2209, 2269, -1552, -522, 339]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 12, -15, -28, 32, 18, -23, -1, 5], [-5, 4, 61, -63, -155, 132, 122, -97, -28, 24], [-24, 19, 292, -299, -735, 613, 564, -430, -121, 92], [-92, 68, 1123, -1088, -2875, 2209, 2269, -1552, -522, 339], [-339, 247, 4136, -3962, -10580, 7973, 8311, -5528, -1891, 1173]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 12, -15, -28, 32, 18, -23, -1, 5], [-5, 4, 61, -63, -155, 132, 122, -97, -28, 24], [-24, 19, 292, -299, -735, 613, 564, -430, -121, 92], [-92, 68, 1123, -1088, -2875, 2209, 2269, -1552, -522, 339], [-339, 247, 4136, -3962, -10580, 7973, 8311, -5528, -1891, 1173], [-1173, 834, 14323, -13459, -36806, 26956, 29087, -18668, -6701, 3974]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 12, -15, -28, 32, 18, -23, -1, 5], [-5, 4, 61, -63, -155, 132, 122, -97, -28, 24], [-24, 19, 292, -299, -735, 613, 564, -430, -121, 92], [-92, 68, 1123, -1088, -2875, 2209, 2269, -1552, -522, 339], [-339, 247, 4136, -3962, -10580, 7973, 8311, -5528, -1891, 1173], [-1173, 834, 14323, -13459, -36806, 26956, 29087, -18668, -6701, 3974], [-3974, 2801, 48522, -45287, -124731, 90362, 98488, -62315, -22642, 13169]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 12, -15, -28, 32, 18, -23, -1, 5], [-5, 4, 61, -63, -155, 132, 122, -97, -28, 24], [-24, 19, 292, -299, -735, 613, 564, -430, -121, 92], [-92, 68, 1123, -1088, -2875, 2209, 2269, -1552, -522, 339], [-339, 247, 4136, -3962, -10580, 7973, 8311, -5528, -1891, 1173], [-1173, 834, 14323, -13459, -36806, 26956, 29087, -18668, -6701, 3974], [-3974, 2801, 48522, -45287, -124731, 90362, 98488, -62315, -22642, 13169], [-13169, 9195, 160829, -149013, -414019, 296677, 327404, -204399, -75484, 43203]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 1, 12, -15, -28, 32, 18, -23, -1, 5], [-5, 4, 61, -63, -155, 132, 122, -97, -28, 24], [-24, 19, 292, -299, -735, 613, 564, -430, -121, 92], [-92, 68, 1123, -1088, -2875, 2209, 2269, -1552, -522, 339], [-339, 247, 4136, -3962, -10580, 7973, 8311, -5528, -1891, 1173], [-1173, 834, 14323, -13459, -36806, 26956, 29087, -18668, -6701, 3974], [-3974, 2801, 48522, -45287, -124731, 90362, 98488, -62315, -22642, 13169], [-13169, 9195, 160829, -149013, -414019, 296677, 327404, -204399, -75484, 43203], [-43203, 30034, 527631, -487216, -1358697, 968477, 1074331, -666265, -247602, 140531]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp397 : Fact (Nat.Prime 397) := fact_iff.2 (by norm_num)
instance hp837579893 : Fact (Nat.Prime 837579893) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 1]
  b' := [0, 1, 1, 1, 1, 0, 1]
  k := [1, 1, 1, 0, 0, 1, 1]
  f := [0, 1, 7, -7, -13, 17, 10, -11, 0, 3]
  g := [1, 0, 1, 0, 1, 1, 0, 0, 1]
  h := [1, 1, 1]
  a := [1, 0, 0, 0, 0, 0, 0, 1]
  b := [1, 1, 0, 0, 0, 1, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD397 : CertificateDedekindCriterionLists l 397 where
  n := 2
  a' := [351, 162, 22, 89, 299, 122, 146, 80]
  b' := [60, 282, 316, 291, 325, 272, 186, 241, 344]
  k := [257, 124, 152, 146, 283, 327, 50, 30, 1]
  f := [31, 33, 111, 172, 72, 145, 113, 146, 97, 1]
  g := [68, 72, 243, 376, 156, 317, 246, 319, 211, 1]
  h := [181, 1]
  a := [8, 111, 259, 154, 305, 360, 324, 116, 188]
  b := [154, 232, 175, 364, 228, 77, 241, 275, 209]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD837579893 : CertificateDedekindCriterionLists l 837579893 where
  n := 2
  a' := [532863334, 472914302, 67403349, 113454043, 412770919, 428207135, 282260193, 210060631]
  b' := [43397566, 710403117, 590859813, 46698775, 731041461, 711371303, 85194263, 117821113, 162788795]
  k := [701938098, 293785482, 826329679, 663159444, 119410083, 676750677, 63185076, 261654194, 1]
  f := [147505160, 187091803, 27877299, 266059829, 255040482, 205901427, 52171993, 172245444, 188960229, 1]
  g := [429039223, 544182465, 81084990, 773871926, 741820624, 598892865, 151749478, 500999771, 549617041, 1]
  h := [287962847, 1]
  a := [219248065, 342128046, 532267845, 85617096, 777382240, 94021774, 38557320, 456035424, 618257594]
  b := [336009060, 632431267, 451371204, 406804383, 537563691, 437392706, 227218804, 264156838, 219322299]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 397, 837579893]
  exp := ![1, 1, 1]
  pdgood := [2, 397, 837579893]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp397.out
    exact hp837579893.out
  a := [-2650828930213, -86875018890961, -50944838985722, 264159226158019, 56946988971611, -238479900964387, 16153732785236, 62370279499255, -15489421084030]
  b := [-3315867365255, -4643373194628, 29967052302392, 18303663957850, -53512263506419, -11861745084918, 34459870474372, -1672190625787, -7011499004127, 1548942108403]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 397 T_ofList CD397
    exact satisfiesDedekindCriterion_of_certificate_lists T l 837579893 T_ofList CD837579893

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

end VoightMaximalOrderD10R449

namespace VoightMaximalOrderD10R459

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5382271169981, [1, -6, 3, 28, -18, -44, 17, 21, -7, -3, 1], 1⟩
local notation "l" => [1, -6, 3, 28, -18, -44, 17, 21, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -28, 18, 44, -17, -21, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -28, 18, 44, -17, -21, 7, 3], ![-3, 17, -3, -87, 26, 150, -7, -80, 0, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -28, 18, 44, -17, -21, 7, 3], ![-3, 17, -3, -87, 26, 150, -7, -80, 0, 16], ![-16, 93, -31, -451, 201, 730, -122, -343, 32, 48]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -28, 18, 44, -17, -21, 7, 3], ![-3, 17, -3, -87, 26, 150, -7, -80, 0, 16], ![-16, 93, -31, -451, 201, 730, -122, -343, 32, 48], ![-48, 272, -51, -1375, 413, 2313, -86, -1130, -7, 176]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -28, 18, 44, -17, -21, 7, 3], ![-3, 17, -3, -87, 26, 150, -7, -80, 0, 16], ![-16, 93, -31, -451, 201, 730, -122, -343, 32, 48], ![-48, 272, -51, -1375, 413, 2313, -86, -1130, -7, 176], ![-176, 1008, -256, -4979, 1793, 8157, -679, -3782, 102, 521]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -28, 18, 44, -17, -21, 7, 3], ![-3, 17, -3, -87, 26, 150, -7, -80, 0, 16], ![-16, 93, -31, -451, 201, 730, -122, -343, 32, 48], ![-48, 272, -51, -1375, 413, 2313, -86, -1130, -7, 176], ![-176, 1008, -256, -4979, 1793, 8157, -679, -3782, 102, 521], ![-521, 2950, -555, -14844, 4399, 24717, -700, -11620, -135, 1665]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -28, 18, 44, -17, -21, 7, 3], ![-3, 17, -3, -87, 26, 150, -7, -80, 0, 16], ![-16, 93, -31, -451, 201, 730, -122, -343, 32, 48], ![-48, 272, -51, -1375, 413, 2313, -86, -1130, -7, 176], ![-176, 1008, -256, -4979, 1793, 8157, -679, -3782, 102, 521], ![-521, 2950, -555, -14844, 4399, 24717, -700, -11620, -135, 1665], ![-1665, 9469, -2045, -47175, 15126, 77659, -3588, -35665, 35, 4860]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -28, 18, 44, -17, -21, 7, 3], ![-3, 17, -3, -87, 26, 150, -7, -80, 0, 16], ![-16, 93, -31, -451, 201, 730, -122, -343, 32, 48], ![-48, 272, -51, -1375, 413, 2313, -86, -1130, -7, 176], ![-176, 1008, -256, -4979, 1793, 8157, -679, -3782, 102, 521], ![-521, 2950, -555, -14844, 4399, 24717, -700, -11620, -135, 1665], ![-1665, 9469, -2045, -47175, 15126, 77659, -3588, -35665, 35, 4860], ![-4860, 27495, -5111, -138125, 40305, 228966, -4961, -105648, -1645, 14615]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -28, 18, 44, -17, -21, 7, 3], ![-3, 17, -3, -87, 26, 150, -7, -80, 0, 16], ![-16, 93, -31, -451, 201, 730, -122, -343, 32, 48], ![-48, 272, -51, -1375, 413, 2313, -86, -1130, -7, 176], ![-176, 1008, -256, -4979, 1793, 8157, -679, -3782, 102, 521], ![-521, 2950, -555, -14844, 4399, 24717, -700, -11620, -135, 1665], ![-1665, 9469, -2045, -47175, 15126, 77659, -3588, -35665, 35, 4860], ![-4860, 27495, -5111, -138125, 40305, 228966, -4961, -105648, -1645, 14615], ![-14615, 82830, -16350, -414331, 124945, 683365, -19489, -311876, -3343, 42200]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-48, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-48, -16, -3, -1], [-176, -48, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-48, -16, -3, -1], [-176, -48, -16, -3, -1], [-521, -176, -48, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-48, -16, -3, -1], [-176, -48, -16, -3, -1], [-521, -176, -48, -16, -3, -1], [-1665, -521, -176, -48, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-48, -16, -3, -1], [-176, -48, -16, -3, -1], [-521, -176, -48, -16, -3, -1], [-1665, -521, -176, -48, -16, -3, -1], [-4860, -1665, -521, -176, -48, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-48, -16, -3, -1], [-176, -48, -16, -3, -1], [-521, -176, -48, -16, -3, -1], [-1665, -521, -176, -48, -16, -3, -1], [-4860, -1665, -521, -176, -48, -16, -3, -1], [-14615, -4860, -1665, -521, -176, -48, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -28, 18, 44, -17, -21, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -28, 18, 44, -17, -21, 7, 3], [-3, 17, -3, -87, 26, 150, -7, -80, 0, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -28, 18, 44, -17, -21, 7, 3], [-3, 17, -3, -87, 26, 150, -7, -80, 0, 16], [-16, 93, -31, -451, 201, 730, -122, -343, 32, 48]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -28, 18, 44, -17, -21, 7, 3], [-3, 17, -3, -87, 26, 150, -7, -80, 0, 16], [-16, 93, -31, -451, 201, 730, -122, -343, 32, 48], [-48, 272, -51, -1375, 413, 2313, -86, -1130, -7, 176]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -28, 18, 44, -17, -21, 7, 3], [-3, 17, -3, -87, 26, 150, -7, -80, 0, 16], [-16, 93, -31, -451, 201, 730, -122, -343, 32, 48], [-48, 272, -51, -1375, 413, 2313, -86, -1130, -7, 176], [-176, 1008, -256, -4979, 1793, 8157, -679, -3782, 102, 521]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -28, 18, 44, -17, -21, 7, 3], [-3, 17, -3, -87, 26, 150, -7, -80, 0, 16], [-16, 93, -31, -451, 201, 730, -122, -343, 32, 48], [-48, 272, -51, -1375, 413, 2313, -86, -1130, -7, 176], [-176, 1008, -256, -4979, 1793, 8157, -679, -3782, 102, 521], [-521, 2950, -555, -14844, 4399, 24717, -700, -11620, -135, 1665]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -28, 18, 44, -17, -21, 7, 3], [-3, 17, -3, -87, 26, 150, -7, -80, 0, 16], [-16, 93, -31, -451, 201, 730, -122, -343, 32, 48], [-48, 272, -51, -1375, 413, 2313, -86, -1130, -7, 176], [-176, 1008, -256, -4979, 1793, 8157, -679, -3782, 102, 521], [-521, 2950, -555, -14844, 4399, 24717, -700, -11620, -135, 1665], [-1665, 9469, -2045, -47175, 15126, 77659, -3588, -35665, 35, 4860]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -28, 18, 44, -17, -21, 7, 3], [-3, 17, -3, -87, 26, 150, -7, -80, 0, 16], [-16, 93, -31, -451, 201, 730, -122, -343, 32, 48], [-48, 272, -51, -1375, 413, 2313, -86, -1130, -7, 176], [-176, 1008, -256, -4979, 1793, 8157, -679, -3782, 102, 521], [-521, 2950, -555, -14844, 4399, 24717, -700, -11620, -135, 1665], [-1665, 9469, -2045, -47175, 15126, 77659, -3588, -35665, 35, 4860], [-4860, 27495, -5111, -138125, 40305, 228966, -4961, -105648, -1645, 14615]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -28, 18, 44, -17, -21, 7, 3], [-3, 17, -3, -87, 26, 150, -7, -80, 0, 16], [-16, 93, -31, -451, 201, 730, -122, -343, 32, 48], [-48, 272, -51, -1375, 413, 2313, -86, -1130, -7, 176], [-176, 1008, -256, -4979, 1793, 8157, -679, -3782, 102, 521], [-521, 2950, -555, -14844, 4399, 24717, -700, -11620, -135, 1665], [-1665, 9469, -2045, -47175, 15126, 77659, -3588, -35665, 35, 4860], [-4860, 27495, -5111, -138125, 40305, 228966, -4961, -105648, -1645, 14615], [-14615, 82830, -16350, -414331, 124945, 683365, -19489, -311876, -3343, 42200]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp58661 : Fact (Nat.Prime 58661) := fact_iff.2 (by norm_num)
instance hp254161 : Fact (Nat.Prime 254161) := fact_iff.2 (by norm_num)

def CD19 : CertificateDedekindCriterionLists l 19 where
  n := 3
  a' := [8, 0, 2, 6, 9, 7, 15]
  b' := [6, 10, 6, 3, 15, 1, 4, 10]
  k := [1, 17, 12, 7, 13, 5, 14, 7, 15, 3, 7, 11, 3, 9, 1]
  f := [4, 13, 15, 7, 11, 22, 18, 9, 3, 1]
  g := [7, 13, 9, 2, 14, 16, 11, 2, 1]
  h := [11, 14, 1]
  a := [9, 2, 14, 14, 12, 10, 11, 2]
  b := [14, 5, 15, 4, 6, 5, 6, 6, 17]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD58661 : CertificateDedekindCriterionLists l 58661 where
  n := 2
  a' := [4904, 41969, 33812, 46396, 16607, 42166, 45538, 25582]
  b' := [13158, 16508, 16415, 64, 21544, 44618, 56660, 41402, 29747]
  k := [28465, 7296, 46934, 16500, 16262, 4769, 20195, 12715, 1]
  f := [16861, 30361, 18865, 8294, 22990, 15985, 46679, 329, 5667, 1]
  g := [18911, 34052, 21158, 9302, 25785, 17928, 52354, 368, 6356, 1]
  h := [52302, 1]
  a := [2717, 41933, 3565, 2431, 43273, 50087, 42271, 36506, 31247]
  b := [5320, 36019, 28420, 23206, 29894, 6937, 14996, 22751, 27414]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD254161 : CertificateDedekindCriterionLists l 254161 where
  n := 2
  a' := [126192, 168087, 47495, 183006, 216335, 40722, 70724, 237812]
  b' := [128576, 168714, 147546, 246421, 140898, 90161, 137666, 10814, 114777]
  k := [86969, 228644, 168182, 224794, 42616, 113339, 151345, 234388, 1]
  f := [4514, 9074, 9359, 4950, 3307, 2215, 6496, 5642, 9501, 1]
  g := [116063, 233297, 240613, 127249, 85016, 56943, 167018, 145049, 244273, 1]
  h := [9885, 1]
  a := [200724, 53821, 102024, 179453, 8089, 106675, 14056, 157676, 52937]
  b := [170535, 63449, 231056, 144084, 176914, 22011, 153125, 3110, 201224]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![19, 58661, 254161]
  exp := ![1, 1, 1]
  pdgood := [19, 58661, 254161]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp19.out
    exact hp58661.out
    exact hp254161.out
  a := [-29612593350421, -68653341913248, 191514355687749, 274335928771828, -215976049245949, -199352425831538, 97938842146886, 37518471628876, -15588568706080]
  b := [-4982645130070, 13187724568143, 29196797266492, -44693791369699, -57613577700133, 34828220728677, 29065209872833, -12113403749866, -4219504224070, 1558856870608]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19 T_ofList CD19
    exact satisfiesDedekindCriterion_of_certificate_lists T l 58661 T_ofList CD58661
    exact satisfiesDedekindCriterion_of_certificate_lists T l 254161 T_ofList CD254161

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

end VoightMaximalOrderD10R459

namespace VoightMaximalOrderD10R462

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5389875278125, [-1, -6, 14, 26, -32, -30, 29, 11, -10, -1, 1], 1⟩
local notation "l" => [-1, -6, 14, 26, -32, -30, 29, 11, -10, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -14, -26, 32, 30, -29, -11, 10, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -14, -26, 32, 30, -29, -11, 10, 1], ![1, 7, -8, -40, 6, 62, 1, -40, -1, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -14, -26, 32, 30, -29, -11, 10, 1], ![1, 7, -8, -40, 6, 62, 1, -40, -1, 11], ![11, 67, -147, -294, 312, 336, -257, -120, 70, 10]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -14, -26, 32, 30, -29, -11, 10, 1], ![1, 7, -8, -40, 6, 62, 1, -40, -1, 11], ![11, 67, -147, -294, 312, 336, -257, -120, 70, 10], ![10, 71, -73, -407, 26, 612, 46, -367, -20, 80]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -14, -26, 32, 30, -29, -11, 10, 1], ![1, 7, -8, -40, 6, 62, 1, -40, -1, 11], ![11, 67, -147, -294, 312, 336, -257, -120, 70, 10], ![10, 71, -73, -407, 26, 612, 46, -367, -20, 80], ![80, 490, -1049, -2153, 2153, 2426, -1708, -834, 433, 60]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -14, -26, 32, 30, -29, -11, 10, 1], ![1, 7, -8, -40, 6, 62, 1, -40, -1, 11], ![11, 67, -147, -294, 312, 336, -257, -120, 70, 10], ![10, 71, -73, -407, 26, 612, 46, -367, -20, 80], ![80, 490, -1049, -2153, 2153, 2426, -1708, -834, 433, 60], ![60, 440, -350, -2609, -233, 3953, 686, -2368, -234, 493]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -14, -26, 32, 30, -29, -11, 10, 1], ![1, 7, -8, -40, 6, 62, 1, -40, -1, 11], ![11, 67, -147, -294, 312, 336, -257, -120, 70, 10], ![10, 71, -73, -407, 26, 612, 46, -367, -20, 80], ![80, 490, -1049, -2153, 2153, 2426, -1708, -834, 433, 60], ![60, 440, -350, -2609, -233, 3953, 686, -2368, -234, 493], ![493, 3018, -6462, -13168, 13167, 14557, -10344, -4737, 2562, 259]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -14, -26, 32, 30, -29, -11, 10, 1], ![1, 7, -8, -40, 6, 62, 1, -40, -1, 11], ![11, 67, -147, -294, 312, 336, -257, -120, 70, 10], ![10, 71, -73, -407, 26, 612, 46, -367, -20, 80], ![80, 490, -1049, -2153, 2153, 2426, -1708, -834, 433, 60], ![60, 440, -350, -2609, -233, 3953, 686, -2368, -234, 493], ![493, 3018, -6462, -13168, 13167, 14557, -10344, -4737, 2562, 259], ![259, 2047, -608, -13196, -4880, 20937, 7046, -13193, -2147, 2821]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 6, -14, -26, 32, 30, -29, -11, 10, 1], ![1, 7, -8, -40, 6, 62, 1, -40, -1, 11], ![11, 67, -147, -294, 312, 336, -257, -120, 70, 10], ![10, 71, -73, -407, 26, 612, 46, -367, -20, 80], ![80, 490, -1049, -2153, 2153, 2426, -1708, -834, 433, 60], ![60, 440, -350, -2609, -233, 3953, 686, -2368, -234, 493], ![493, 3018, -6462, -13168, 13167, 14557, -10344, -4737, 2562, 259], ![259, 2047, -608, -13196, -4880, 20937, 7046, -13193, -2147, 2821], ![2821, 17185, -37447, -73954, 77076, 79750, -60872, -23985, 15017, 674]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-10, -11, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-10, -11, -1, -1], [-80, -10, -11, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-10, -11, -1, -1], [-80, -10, -11, -1, -1], [-60, -80, -10, -11, -1, -1]], ![[], [], [], [-1], [-1, -1], [-11, -1, -1], [-10, -11, -1, -1], [-80, -10, -11, -1, -1], [-60, -80, -10, -11, -1, -1], [-493, -60, -80, -10, -11, -1, -1]], ![[], [], [-1], [-1, -1], [-11, -1, -1], [-10, -11, -1, -1], [-80, -10, -11, -1, -1], [-60, -80, -10, -11, -1, -1], [-493, -60, -80, -10, -11, -1, -1], [-259, -493, -60, -80, -10, -11, -1, -1]], ![[], [-1], [-1, -1], [-11, -1, -1], [-10, -11, -1, -1], [-80, -10, -11, -1, -1], [-60, -80, -10, -11, -1, -1], [-493, -60, -80, -10, -11, -1, -1], [-259, -493, -60, -80, -10, -11, -1, -1], [-2821, -259, -493, -60, -80, -10, -11, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -14, -26, 32, 30, -29, -11, 10, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -14, -26, 32, 30, -29, -11, 10, 1], [1, 7, -8, -40, 6, 62, 1, -40, -1, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -14, -26, 32, 30, -29, -11, 10, 1], [1, 7, -8, -40, 6, 62, 1, -40, -1, 11], [11, 67, -147, -294, 312, 336, -257, -120, 70, 10]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -14, -26, 32, 30, -29, -11, 10, 1], [1, 7, -8, -40, 6, 62, 1, -40, -1, 11], [11, 67, -147, -294, 312, 336, -257, -120, 70, 10], [10, 71, -73, -407, 26, 612, 46, -367, -20, 80]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -14, -26, 32, 30, -29, -11, 10, 1], [1, 7, -8, -40, 6, 62, 1, -40, -1, 11], [11, 67, -147, -294, 312, 336, -257, -120, 70, 10], [10, 71, -73, -407, 26, 612, 46, -367, -20, 80], [80, 490, -1049, -2153, 2153, 2426, -1708, -834, 433, 60]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -14, -26, 32, 30, -29, -11, 10, 1], [1, 7, -8, -40, 6, 62, 1, -40, -1, 11], [11, 67, -147, -294, 312, 336, -257, -120, 70, 10], [10, 71, -73, -407, 26, 612, 46, -367, -20, 80], [80, 490, -1049, -2153, 2153, 2426, -1708, -834, 433, 60], [60, 440, -350, -2609, -233, 3953, 686, -2368, -234, 493]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -14, -26, 32, 30, -29, -11, 10, 1], [1, 7, -8, -40, 6, 62, 1, -40, -1, 11], [11, 67, -147, -294, 312, 336, -257, -120, 70, 10], [10, 71, -73, -407, 26, 612, 46, -367, -20, 80], [80, 490, -1049, -2153, 2153, 2426, -1708, -834, 433, 60], [60, 440, -350, -2609, -233, 3953, 686, -2368, -234, 493], [493, 3018, -6462, -13168, 13167, 14557, -10344, -4737, 2562, 259]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -14, -26, 32, 30, -29, -11, 10, 1], [1, 7, -8, -40, 6, 62, 1, -40, -1, 11], [11, 67, -147, -294, 312, 336, -257, -120, 70, 10], [10, 71, -73, -407, 26, 612, 46, -367, -20, 80], [80, 490, -1049, -2153, 2153, 2426, -1708, -834, 433, 60], [60, 440, -350, -2609, -233, 3953, 686, -2368, -234, 493], [493, 3018, -6462, -13168, 13167, 14557, -10344, -4737, 2562, 259], [259, 2047, -608, -13196, -4880, 20937, 7046, -13193, -2147, 2821]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 6, -14, -26, 32, 30, -29, -11, 10, 1], [1, 7, -8, -40, 6, 62, 1, -40, -1, 11], [11, 67, -147, -294, 312, 336, -257, -120, 70, 10], [10, 71, -73, -407, 26, 612, 46, -367, -20, 80], [80, 490, -1049, -2153, 2153, 2426, -1708, -834, 433, 60], [60, 440, -350, -2609, -233, 3953, 686, -2368, -234, 493], [493, 3018, -6462, -13168, 13167, 14557, -10344, -4737, 2562, 259], [259, 2047, -608, -13196, -4880, 20937, 7046, -13193, -2147, 2821], [2821, 17185, -37447, -73954, 77076, 79750, -60872, -23985, 15017, 674]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp13 : Fact (Nat.Prime 13) := fact_iff.2 (by norm_num)
instance hp1951 : Fact (Nat.Prime 1951) := fact_iff.2 (by norm_num)
instance hp5231 : Fact (Nat.Prime 5231) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [0, 2, 2]
  b' := [1, 2, 2, 0, 1]
  k := [1]
  f := [1, 2, -1, -2, 10, 10, -2, 1, 4, 1]
  g := [2, 1, 2, 3, 2, 1]
  h := [2, 1, 2, 3, 2, 1]
  a := [2, 4, 3, 2, 3]
  b := [2, 0, 1, 4, 2, 1, 1, 2, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD13 : CertificateDedekindCriterionLists l 13 where
  n := 2
  a' := [5, 7, 11, 8, 2, 11, 3]
  b' := [7, 4, 1, 5, 0, 5, 7, 11]
  k := [1, 6, 9, 8, 6, 12, 1]
  f := [2, 2, 2, 1, 3, 4, 2, 4, 2, 1]
  g := [5, 4, 7, 7, 0, 3, 11, 12, 1]
  h := [5, 0, 1]
  a := [6, 12, 0, 0, 7, 9, 5, 5]
  b := [3, 6, 2, 11, 5, 7, 9, 6, 8]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1951 : CertificateDedekindCriterionLists l 1951 where
  n := 2
  a' := [1397, 1258, 1465, 918, 928, 718, 1742, 514]
  b' := [814, 1146, 1379, 1516, 319, 1834, 1863, 50, 810]
  k := [604, 976, 1082, 1380, 1179, 1223, 574, 1731, 1]
  f := [976, 96, 247, 8, 411, 809, 915, 1028, 482, 1]
  g := [1755, 171, 444, 14, 739, 1454, 1644, 1847, 865, 1]
  h := [1085, 1]
  a := [1599, 552, 1848, 1753, 1663, 1817, 237, 240, 1481]
  b := [1104, 832, 948, 166, 843, 667, 694, 1193, 470]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD5231 : CertificateDedekindCriterionLists l 5231 where
  n := 2
  a' := [153, 3521, 3421, 4531, 4607, 1554, 1723, 2234]
  b' := [3256, 359, 4971, 2427, 1435, 4198, 944, 1903, 333]
  k := [2633, 2514, 4136, 4151, 1988, 2107, 4712, 5141, 1]
  f := [2391, 2368, 1771, 1605, 1877, 2140, 1298, 360, 1307, 1]
  g := [4702, 4655, 3481, 3155, 3690, 4207, 2551, 707, 2570, 1]
  h := [2660, 1]
  a := [2220, 3039, 3400, 1113, 1858, 685, 4975, 849, 4414]
  b := [3656, 3604, 3772, 1255, 453, 1046, 5104, 3018, 817]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 13, 1951, 5231]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 13, 1951, 5231]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp13.out
    exact hp1951.out
    exact hp5231.out
  a := [1397722313, -12103734572, -3460103870, 60089020996, -35802835912, -39423952346, 28000629670, 5060324028, -4109481920]
  b := [-343515263, -983504445, 6886384785, -2060753452, -12624030358, 7166256214, 5534386184, -3608341448, -547127222, 410948192]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 13 T_ofList CD13
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1951 T_ofList CD1951
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5231 T_ofList CD5231

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

end VoightMaximalOrderD10R462

namespace VoightMaximalOrderD10R464

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5393446214656, [5, -12, -23, 46, 28, -56, -7, 26, -3, -4, 1], 1⟩
local notation "l" => [5, -12, -23, 46, 28, -56, -7, 26, -3, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 12, 23, -46, -28, 56, 7, -26, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 12, 23, -46, -28, 56, 7, -26, 3, 4], ![-20, 43, 104, -161, -158, 196, 84, -97, -14, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 12, 23, -46, -28, 56, 7, -26, 3, 4], ![-20, 43, 104, -161, -158, 196, 84, -97, -14, 19], ![-95, 208, 480, -770, -693, 906, 329, -410, -40, 62]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 12, 23, -46, -28, 56, 7, -26, 3, 4], ![-20, 43, 104, -161, -158, 196, 84, -97, -14, 19], ![-95, 208, 480, -770, -693, 906, 329, -410, -40, 62], ![-310, 649, 1634, -2372, -2506, 2779, 1340, -1283, -224, 208]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 12, 23, -46, -28, 56, 7, -26, 3, 4], ![-20, 43, 104, -161, -158, 196, 84, -97, -14, 19], ![-95, 208, 480, -770, -693, 906, 329, -410, -40, 62], ![-310, 649, 1634, -2372, -2506, 2779, 1340, -1283, -224, 208], ![-1040, 2186, 5433, -7934, -8196, 9142, 4235, -4068, -659, 608]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 12, 23, -46, -28, 56, 7, -26, 3, 4], ![-20, 43, 104, -161, -158, 196, 84, -97, -14, 19], ![-95, 208, 480, -770, -693, 906, 329, -410, -40, 62], ![-310, 649, 1634, -2372, -2506, 2779, 1340, -1283, -224, 208], ![-1040, 2186, 5433, -7934, -8196, 9142, 4235, -4068, -659, 608], ![-3040, 6256, 16170, -22535, -24958, 25852, 13398, -11573, -2244, 1773]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 12, 23, -46, -28, 56, 7, -26, 3, 4], ![-20, 43, 104, -161, -158, 196, 84, -97, -14, 19], ![-95, 208, 480, -770, -693, 906, 329, -410, -40, 62], ![-310, 649, 1634, -2372, -2506, 2779, 1340, -1283, -224, 208], ![-1040, 2186, 5433, -7934, -8196, 9142, 4235, -4068, -659, 608], ![-3040, 6256, 16170, -22535, -24958, 25852, 13398, -11573, -2244, 1773], ![-8865, 18236, 47035, -65388, -72179, 74330, 38263, -32700, -6254, 4848]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 12, 23, -46, -28, 56, 7, -26, 3, 4], ![-20, 43, 104, -161, -158, 196, 84, -97, -14, 19], ![-95, 208, 480, -770, -693, 906, 329, -410, -40, 62], ![-310, 649, 1634, -2372, -2506, 2779, 1340, -1283, -224, 208], ![-1040, 2186, 5433, -7934, -8196, 9142, 4235, -4068, -659, 608], ![-3040, 6256, 16170, -22535, -24958, 25852, 13398, -11573, -2244, 1773], ![-8865, 18236, 47035, -65388, -72179, 74330, 38263, -32700, -6254, 4848], ![-24240, 49311, 129740, -175973, -201132, 199309, 108266, -87785, -18156, 13138]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-5, 12, 23, -46, -28, 56, 7, -26, 3, 4], ![-20, 43, 104, -161, -158, 196, 84, -97, -14, 19], ![-95, 208, 480, -770, -693, 906, 329, -410, -40, 62], ![-310, 649, 1634, -2372, -2506, 2779, 1340, -1283, -224, 208], ![-1040, 2186, 5433, -7934, -8196, 9142, 4235, -4068, -659, 608], ![-3040, 6256, 16170, -22535, -24958, 25852, 13398, -11573, -2244, 1773], ![-8865, 18236, 47035, -65388, -72179, 74330, 38263, -32700, -6254, 4848], ![-24240, 49311, 129740, -175973, -201132, 199309, 108266, -87785, -18156, 13138], ![-65690, 133416, 351485, -474608, -543837, 534596, 291275, -233322, -48371, 34396]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-208, -62, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-208, -62, -19, -4, -1], [-608, -208, -62, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-208, -62, -19, -4, -1], [-608, -208, -62, -19, -4, -1], [-1773, -608, -208, -62, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-208, -62, -19, -4, -1], [-608, -208, -62, -19, -4, -1], [-1773, -608, -208, -62, -19, -4, -1], [-4848, -1773, -608, -208, -62, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-208, -62, -19, -4, -1], [-608, -208, -62, -19, -4, -1], [-1773, -608, -208, -62, -19, -4, -1], [-4848, -1773, -608, -208, -62, -19, -4, -1], [-13138, -4848, -1773, -608, -208, -62, -19, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 12, 23, -46, -28, 56, 7, -26, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 12, 23, -46, -28, 56, 7, -26, 3, 4], [-20, 43, 104, -161, -158, 196, 84, -97, -14, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 12, 23, -46, -28, 56, 7, -26, 3, 4], [-20, 43, 104, -161, -158, 196, 84, -97, -14, 19], [-95, 208, 480, -770, -693, 906, 329, -410, -40, 62]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 12, 23, -46, -28, 56, 7, -26, 3, 4], [-20, 43, 104, -161, -158, 196, 84, -97, -14, 19], [-95, 208, 480, -770, -693, 906, 329, -410, -40, 62], [-310, 649, 1634, -2372, -2506, 2779, 1340, -1283, -224, 208]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 12, 23, -46, -28, 56, 7, -26, 3, 4], [-20, 43, 104, -161, -158, 196, 84, -97, -14, 19], [-95, 208, 480, -770, -693, 906, 329, -410, -40, 62], [-310, 649, 1634, -2372, -2506, 2779, 1340, -1283, -224, 208], [-1040, 2186, 5433, -7934, -8196, 9142, 4235, -4068, -659, 608]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 12, 23, -46, -28, 56, 7, -26, 3, 4], [-20, 43, 104, -161, -158, 196, 84, -97, -14, 19], [-95, 208, 480, -770, -693, 906, 329, -410, -40, 62], [-310, 649, 1634, -2372, -2506, 2779, 1340, -1283, -224, 208], [-1040, 2186, 5433, -7934, -8196, 9142, 4235, -4068, -659, 608], [-3040, 6256, 16170, -22535, -24958, 25852, 13398, -11573, -2244, 1773]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 12, 23, -46, -28, 56, 7, -26, 3, 4], [-20, 43, 104, -161, -158, 196, 84, -97, -14, 19], [-95, 208, 480, -770, -693, 906, 329, -410, -40, 62], [-310, 649, 1634, -2372, -2506, 2779, 1340, -1283, -224, 208], [-1040, 2186, 5433, -7934, -8196, 9142, 4235, -4068, -659, 608], [-3040, 6256, 16170, -22535, -24958, 25852, 13398, -11573, -2244, 1773], [-8865, 18236, 47035, -65388, -72179, 74330, 38263, -32700, -6254, 4848]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 12, 23, -46, -28, 56, 7, -26, 3, 4], [-20, 43, 104, -161, -158, 196, 84, -97, -14, 19], [-95, 208, 480, -770, -693, 906, 329, -410, -40, 62], [-310, 649, 1634, -2372, -2506, 2779, 1340, -1283, -224, 208], [-1040, 2186, 5433, -7934, -8196, 9142, 4235, -4068, -659, 608], [-3040, 6256, 16170, -22535, -24958, 25852, 13398, -11573, -2244, 1773], [-8865, 18236, 47035, -65388, -72179, 74330, 38263, -32700, -6254, 4848], [-24240, 49311, 129740, -175973, -201132, 199309, 108266, -87785, -18156, 13138]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-5, 12, 23, -46, -28, 56, 7, -26, 3, 4], [-20, 43, 104, -161, -158, 196, 84, -97, -14, 19], [-95, 208, 480, -770, -693, 906, 329, -410, -40, 62], [-310, 649, 1634, -2372, -2506, 2779, 1340, -1283, -224, 208], [-1040, 2186, 5433, -7934, -8196, 9142, 4235, -4068, -659, 608], [-3040, 6256, 16170, -22535, -24958, 25852, 13398, -11573, -2244, 1773], [-8865, 18236, 47035, -65388, -72179, 74330, 38263, -32700, -6254, 4848], [-24240, 49311, 129740, -175973, -201132, 199309, 108266, -87785, -18156, 13138], [-65690, 133416, 351485, -474608, -543837, 534596, 291275, -233322, -48371, 34396]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp12781 : Fact (Nat.Prime 12781) := fact_iff.2 (by norm_num)
instance hp412099 : Fact (Nat.Prime 412099) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 1]
  b' := [0, 1, 1, 1]
  k := [1]
  f := [-2, 7, 12, -22, -12, 30, 5, -12, 3, 3]
  g := [1, 1, 0, 1, 1, 1]
  h := [1, 1, 0, 1, 1, 1]
  a := [1, 0, 0, 1, 1]
  b := [1, 0, 0, 1, 1, 1, 1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD12781 : CertificateDedekindCriterionLists l 12781 where
  n := 2
  a' := [10451, 1851, 1899, 6447, 9357, 772, 3511, 8263]
  b' := [7395, 467, 938, 4277, 2925, 8270, 6814, 6418, 502]
  k := [5547, 5438, 682, 11864, 5641, 8893, 7577, 961, 1]
  f := [551, 840, 4012, 1013, 2794, 1292, 909, 4808, 3176, 1]
  g := [1192, 1817, 8679, 2190, 6044, 2794, 1966, 10401, 6869, 1]
  h := [5908, 1]
  a := [5671, 11452, 2181, 10364, 2548, 12141, 10744, 6824, 8249]
  b := [6128, 5344, 1707, 2895, 7535, 6304, 10517, 12391, 4532]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD412099 : CertificateDedekindCriterionLists l 412099 where
  n := 2
  a' := [160886, 351338, 375423, 179116, 280986, 174021, 71266, 262815]
  b' := [303685, 145047, 324357, 229732, 95997, 407853, 324908, 254135, 245531]
  k := [161729, 311998, 239349, 175036, 387289, 381244, 182207, 369318, 1]
  f := [103625, 116918, 181166, 42729, 171014, 5283, 49324, 125071, 101913, 1]
  g := [187760, 211845, 328257, 77420, 309863, 9571, 89371, 226618, 184657, 1]
  h := [227438, 1]
  a := [324044, 280974, 290647, 352803, 368159, 31246, 119979, 66561, 71973]
  b := [17203, 282761, 26154, 8005, 57504, 222070, 203550, 24702, 340126]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 12781, 412099]
  exp := ![1, 1, 1]
  pdgood := [2, 12781, 412099]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp12781.out
    exact hp412099.out
  a := [-6168218114, -45444269572, 14028191814, 142448550272, -35971362420, -107988755910, 33830707092, 22833663862, -8378135070]
  b := [-3447930434, 450172456, 21734906474, -1538790915, -32416085208, 5461207665, 16387913295, -4178863709, -2618491789, 837813507]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 12781 T_ofList CD12781
    exact satisfiesDedekindCriterion_of_certificate_lists T l 412099 T_ofList CD412099

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

end VoightMaximalOrderD10R464

end TraceEuclidean
