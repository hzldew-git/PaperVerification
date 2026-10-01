import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk176
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

namespace VoightMaximalOrderD10R132

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2467196253125, [-1, -2, 10, 10, -27, -15, 26, 7, -9, -1, 1], 1⟩
local notation "l" => [-1, -2, 10, 10, -27, -15, 26, 7, -9, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -10, 27, 15, -26, -7, 9, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -10, 27, 15, -26, -7, 9, 1], ![1, 3, -8, -20, 17, 42, -11, -33, 2, 10]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -10, 27, 15, -26, -7, 9, 1], ![1, 3, -8, -20, 17, 42, -11, -33, 2, 10], ![10, 21, -97, -108, 250, 167, -218, -81, 57, 12]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -10, 27, 15, -26, -7, 9, 1], ![1, 3, -8, -20, 17, 42, -11, -33, 2, 10], ![10, 21, -97, -108, 250, 167, -218, -81, 57, 12], ![12, 34, -99, -217, 216, 430, -145, -302, 27, 69]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -10, 27, 15, -26, -7, 9, 1], ![1, 3, -8, -20, 17, 42, -11, -33, 2, 10], ![10, 21, -97, -108, 250, 167, -218, -81, 57, 12], ![12, 34, -99, -217, 216, 430, -145, -302, 27, 69], ![69, 150, -656, -789, 1646, 1251, -1364, -628, 319, 96]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -10, 27, 15, -26, -7, 9, 1], ![1, 3, -8, -20, 17, 42, -11, -33, 2, 10], ![10, 21, -97, -108, 250, 167, -218, -81, 57, 12], ![12, 34, -99, -217, 216, 430, -145, -302, 27, 69], ![69, 150, -656, -789, 1646, 1251, -1364, -628, 319, 96], ![96, 261, -810, -1616, 1803, 3086, -1245, -2036, 236, 415]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -10, 27, 15, -26, -7, 9, 1], ![1, 3, -8, -20, 17, 42, -11, -33, 2, 10], ![10, 21, -97, -108, 250, 167, -218, -81, 57, 12], ![12, 34, -99, -217, 216, 430, -145, -302, 27, 69], ![69, 150, -656, -789, 1646, 1251, -1364, -628, 319, 96], ![96, 261, -810, -1616, 1803, 3086, -1245, -2036, 236, 415], ![415, 926, -3889, -4960, 9589, 8028, -7704, -4150, 1699, 651]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -10, 27, 15, -26, -7, 9, 1], ![1, 3, -8, -20, 17, 42, -11, -33, 2, 10], ![10, 21, -97, -108, 250, 167, -218, -81, 57, 12], ![12, 34, -99, -217, 216, 430, -145, -302, 27, 69], ![69, 150, -656, -789, 1646, 1251, -1364, -628, 319, 96], ![96, 261, -810, -1616, 1803, 3086, -1245, -2036, 236, 415], ![415, 926, -3889, -4960, 9589, 8028, -7704, -4150, 1699, 651], ![651, 1717, -5584, -10399, 12617, 19354, -8898, -12261, 1709, 2350]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -10, -10, 27, 15, -26, -7, 9, 1], ![1, 3, -8, -20, 17, 42, -11, -33, 2, 10], ![10, 21, -97, -108, 250, 167, -218, -81, 57, 12], ![12, 34, -99, -217, 216, 430, -145, -302, 27, 69], ![69, 150, -656, -789, 1646, 1251, -1364, -628, 319, 96], ![96, 261, -810, -1616, 1803, 3086, -1245, -2036, 236, 415], ![415, 926, -3889, -4960, 9589, 8028, -7704, -4150, 1699, 651], ![651, 1717, -5584, -10399, 12617, 19354, -8898, -12261, 1709, 2350], ![2350, 5351, -21783, -29084, 53051, 47867, -41746, -25348, 8889, 4059]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-10, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-10, -1, -1], [-12, -10, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-10, -1, -1], [-12, -10, -1, -1], [-69, -12, -10, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-10, -1, -1], [-12, -10, -1, -1], [-69, -12, -10, -1, -1], [-96, -69, -12, -10, -1, -1]], ![[], [], [], [-1], [-1, -1], [-10, -1, -1], [-12, -10, -1, -1], [-69, -12, -10, -1, -1], [-96, -69, -12, -10, -1, -1], [-415, -96, -69, -12, -10, -1, -1]], ![[], [], [-1], [-1, -1], [-10, -1, -1], [-12, -10, -1, -1], [-69, -12, -10, -1, -1], [-96, -69, -12, -10, -1, -1], [-415, -96, -69, -12, -10, -1, -1], [-651, -415, -96, -69, -12, -10, -1, -1]], ![[], [-1], [-1, -1], [-10, -1, -1], [-12, -10, -1, -1], [-69, -12, -10, -1, -1], [-96, -69, -12, -10, -1, -1], [-415, -96, -69, -12, -10, -1, -1], [-651, -415, -96, -69, -12, -10, -1, -1], [-2350, -651, -415, -96, -69, -12, -10, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -10, 27, 15, -26, -7, 9, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -10, 27, 15, -26, -7, 9, 1], [1, 3, -8, -20, 17, 42, -11, -33, 2, 10]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -10, 27, 15, -26, -7, 9, 1], [1, 3, -8, -20, 17, 42, -11, -33, 2, 10], [10, 21, -97, -108, 250, 167, -218, -81, 57, 12]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -10, 27, 15, -26, -7, 9, 1], [1, 3, -8, -20, 17, 42, -11, -33, 2, 10], [10, 21, -97, -108, 250, 167, -218, -81, 57, 12], [12, 34, -99, -217, 216, 430, -145, -302, 27, 69]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -10, 27, 15, -26, -7, 9, 1], [1, 3, -8, -20, 17, 42, -11, -33, 2, 10], [10, 21, -97, -108, 250, 167, -218, -81, 57, 12], [12, 34, -99, -217, 216, 430, -145, -302, 27, 69], [69, 150, -656, -789, 1646, 1251, -1364, -628, 319, 96]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -10, 27, 15, -26, -7, 9, 1], [1, 3, -8, -20, 17, 42, -11, -33, 2, 10], [10, 21, -97, -108, 250, 167, -218, -81, 57, 12], [12, 34, -99, -217, 216, 430, -145, -302, 27, 69], [69, 150, -656, -789, 1646, 1251, -1364, -628, 319, 96], [96, 261, -810, -1616, 1803, 3086, -1245, -2036, 236, 415]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -10, 27, 15, -26, -7, 9, 1], [1, 3, -8, -20, 17, 42, -11, -33, 2, 10], [10, 21, -97, -108, 250, 167, -218, -81, 57, 12], [12, 34, -99, -217, 216, 430, -145, -302, 27, 69], [69, 150, -656, -789, 1646, 1251, -1364, -628, 319, 96], [96, 261, -810, -1616, 1803, 3086, -1245, -2036, 236, 415], [415, 926, -3889, -4960, 9589, 8028, -7704, -4150, 1699, 651]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -10, 27, 15, -26, -7, 9, 1], [1, 3, -8, -20, 17, 42, -11, -33, 2, 10], [10, 21, -97, -108, 250, 167, -218, -81, 57, 12], [12, 34, -99, -217, 216, 430, -145, -302, 27, 69], [69, 150, -656, -789, 1646, 1251, -1364, -628, 319, 96], [96, 261, -810, -1616, 1803, 3086, -1245, -2036, 236, 415], [415, 926, -3889, -4960, 9589, 8028, -7704, -4150, 1699, 651], [651, 1717, -5584, -10399, 12617, 19354, -8898, -12261, 1709, 2350]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -10, -10, 27, 15, -26, -7, 9, 1], [1, 3, -8, -20, 17, 42, -11, -33, 2, 10], [10, 21, -97, -108, 250, 167, -218, -81, 57, 12], [12, 34, -99, -217, 216, 430, -145, -302, 27, 69], [69, 150, -656, -789, 1646, 1251, -1364, -628, 319, 96], [96, 261, -810, -1616, 1803, 3086, -1245, -2036, 236, 415], [415, 926, -3889, -4960, 9589, 8028, -7704, -4150, 1699, 651], [651, 1717, -5584, -10399, 12617, 19354, -8898, -12261, 1709, 2350], [2350, 5351, -21783, -29084, 53051, 47867, -41746, -25348, 8889, 4059]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp19 : Fact (Nat.Prime 19) := fact_iff.2 (by norm_num)
instance hp239 : Fact (Nat.Prime 239) := fact_iff.2 (by norm_num)
instance hp173861 : Fact (Nat.Prime 173861) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [4, 1, 3]
  b' := [4, 4, 1, 2, 4]
  k := [1]
  f := [1, 2, 2, 2, 11, 7, -1, 1, 3, 1]
  g := [2, 2, 4, 1, 2, 1]
  h := [2, 2, 4, 1, 2, 1]
  a := [2, 4, 2, 2, 3]
  b := [2, 4, 0, 2, 1, 4, 2, 0, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD19 : CertificateDedekindCriterionLists l 19 where
  n := 2
  a' := [9, 17, 16, 1, 1, 0, 11, 6]
  b' := [5, 6, 4, 15, 17, 7, 9, 15, 12]
  k := [15, 14, 17, 14, 13, 12, 5, 0, 1]
  f := [1, 4, 7, 5, 10, 5, -1, 2, 5, 1]
  g := [2, 8, 15, 10, 17, 7, 0, 5, 9, 1]
  h := [9, 1]
  a := [10, 5, 3, 0, 1, 0, 3, 9]
  b := [5, 5, 10, 1, 8, 0, 14, 10]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD239 : CertificateDedekindCriterionLists l 239 where
  n := 2
  a' := [138, 16, 25, 75, 58, 148, 133, 12]
  b' := [65, 147, 155, 117, 9, 49, 203, 191, 158]
  k := [41, 63, 6, 95, 79, 14, 33, 91, 1]
  f := [21, 9, 21, 143, 38, 123, 137, 121, 37, 1]
  g := [26, 11, 26, 177, 46, 152, 169, 149, 45, 1]
  h := [193, 1]
  a := [192, 222, 42, 5, 150, 41, 150, 83, 114]
  b := [38, 161, 152, 73, 130, 105, 189, 112, 125]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD173861 : CertificateDedekindCriterionLists l 173861 where
  n := 2
  a' := [142467, 23888, 78101, 147155, 81228, 6534, 125413, 83538]
  b' := [125008, 164868, 125187, 143667, 14934, 36100, 129749, 21494, 164579]
  k := [170510, 108755, 131994, 116332, 111264, 53250, 55580, 121384, 1]
  f := [7565, 15636, 8483, 22229, 24315, 20792, 2298, 21607, 22279, 1]
  g := [50128, 103607, 56207, 147294, 161113, 137768, 15222, 143174, 147622, 1]
  h := [26238, 1]
  a := [34540, 106237, 45241, 107871, 29782, 135208, 22136, 109938, 139490]
  b := [168423, 152339, 61793, 20804, 45391, 143881, 154008, 1389, 34371]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 19, 239, 173861]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 19, 239, 173861]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp19.out
    exact hp239.out
    exact hp173861.out
  a := [-3547975801, -14591496960, 142783857182, 125790315856, -304422198215, -102719368192, 159257977338, 20591732552, -23364345480]
  b := [-199769102, 8846033261, 10923485444, -43663494052, -27696855954, 53150353429, 15006358555, -20135741704, -2292816710, 2336434548]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 19 T_ofList CD19
    exact satisfiesDedekindCriterion_of_certificate_lists T l 239 T_ofList CD239
    exact satisfiesDedekindCriterion_of_certificate_lists T l 173861 T_ofList CD173861

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

end VoightMaximalOrderD10R132

namespace VoightMaximalOrderD10R133

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2470850051021, [-1, 10, -32, 25, 43, -60, -8, 29, -4, -4, 1], 1⟩
local notation "l" => [-1, 10, -32, 25, 43, -60, -8, 29, -4, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, 32, -25, -43, 60, 8, -29, 4, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, 32, -25, -43, 60, 8, -29, 4, 4], ![4, -39, 118, -68, -197, 197, 92, -108, -13, 20]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, 32, -25, -43, 60, 8, -29, 4, 4], ![4, -39, 118, -68, -197, 197, 92, -108, -13, 20], ![20, -196, 601, -382, -928, 1003, 357, -488, -28, 67]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, 32, -25, -43, 60, 8, -29, 4, 4], ![4, -39, 118, -68, -197, 197, 92, -108, -13, 20], ![20, -196, 601, -382, -928, 1003, 357, -488, -28, 67], ![67, -650, 1948, -1074, -3263, 3092, 1539, -1586, -220, 240]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, 32, -25, -43, 60, 8, -29, 4, 4], ![4, -39, 118, -68, -197, 197, 92, -108, -13, 20], ![20, -196, 601, -382, -928, 1003, 357, -488, -28, 67], ![67, -650, 1948, -1074, -3263, 3092, 1539, -1586, -220, 240], ![240, -2333, 7030, -4052, -11394, 11137, 5012, -5421, -626, 740]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, 32, -25, -43, 60, 8, -29, 4, 4], ![4, -39, 118, -68, -197, 197, 92, -108, -13, 20], ![20, -196, 601, -382, -928, 1003, 357, -488, -28, 67], ![67, -650, 1948, -1074, -3263, 3092, 1539, -1586, -220, 240], ![240, -2333, 7030, -4052, -11394, 11137, 5012, -5421, -626, 740], ![740, -7160, 21347, -11470, -35872, 33006, 17057, -16448, -2461, 2334]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, 32, -25, -43, 60, 8, -29, 4, 4], ![4, -39, 118, -68, -197, 197, 92, -108, -13, 20], ![20, -196, 601, -382, -928, 1003, 357, -488, -28, 67], ![67, -650, 1948, -1074, -3263, 3092, 1539, -1586, -220, 240], ![240, -2333, 7030, -4052, -11394, 11137, 5012, -5421, -626, 740], ![740, -7160, 21347, -11470, -35872, 33006, 17057, -16448, -2461, 2334], ![2334, -22600, 67528, -37003, -111832, 104168, 51678, -50629, -7112, 6875]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, 32, -25, -43, 60, 8, -29, 4, 4], ![4, -39, 118, -68, -197, 197, 92, -108, -13, 20], ![20, -196, 601, -382, -928, 1003, 357, -488, -28, 67], ![67, -650, 1948, -1074, -3263, 3092, 1539, -1586, -220, 240], ![240, -2333, 7030, -4052, -11394, 11137, 5012, -5421, -626, 740], ![740, -7160, 21347, -11470, -35872, 33006, 17057, -16448, -2461, 2334], ![2334, -22600, 67528, -37003, -111832, 104168, 51678, -50629, -7112, 6875], ![6875, -66416, 197400, -104347, -332628, 300668, 159168, -147697, -23129, 20388]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -10, 32, -25, -43, 60, 8, -29, 4, 4], ![4, -39, 118, -68, -197, 197, 92, -108, -13, 20], ![20, -196, 601, -382, -928, 1003, 357, -488, -28, 67], ![67, -650, 1948, -1074, -3263, 3092, 1539, -1586, -220, 240], ![240, -2333, 7030, -4052, -11394, 11137, 5012, -5421, -626, 740], ![740, -7160, 21347, -11470, -35872, 33006, 17057, -16448, -2461, 2334], ![2334, -22600, 67528, -37003, -111832, 104168, 51678, -50629, -7112, 6875], ![6875, -66416, 197400, -104347, -332628, 300668, 159168, -147697, -23129, 20388], ![20388, -197005, 586000, -312300, -981031, 890652, 463772, -432084, -66145, 58423]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1], [-240, -67, -20, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1], [-240, -67, -20, -4, -1], [-740, -240, -67, -20, -4, -1]], ![[], [], [], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1], [-240, -67, -20, -4, -1], [-740, -240, -67, -20, -4, -1], [-2334, -740, -240, -67, -20, -4, -1]], ![[], [], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1], [-240, -67, -20, -4, -1], [-740, -240, -67, -20, -4, -1], [-2334, -740, -240, -67, -20, -4, -1], [-6875, -2334, -740, -240, -67, -20, -4, -1]], ![[], [-1], [-4, -1], [-20, -4, -1], [-67, -20, -4, -1], [-240, -67, -20, -4, -1], [-740, -240, -67, -20, -4, -1], [-2334, -740, -240, -67, -20, -4, -1], [-6875, -2334, -740, -240, -67, -20, -4, -1], [-20388, -6875, -2334, -740, -240, -67, -20, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, 32, -25, -43, 60, 8, -29, 4, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, 32, -25, -43, 60, 8, -29, 4, 4], [4, -39, 118, -68, -197, 197, 92, -108, -13, 20]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, 32, -25, -43, 60, 8, -29, 4, 4], [4, -39, 118, -68, -197, 197, 92, -108, -13, 20], [20, -196, 601, -382, -928, 1003, 357, -488, -28, 67]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, 32, -25, -43, 60, 8, -29, 4, 4], [4, -39, 118, -68, -197, 197, 92, -108, -13, 20], [20, -196, 601, -382, -928, 1003, 357, -488, -28, 67], [67, -650, 1948, -1074, -3263, 3092, 1539, -1586, -220, 240]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, 32, -25, -43, 60, 8, -29, 4, 4], [4, -39, 118, -68, -197, 197, 92, -108, -13, 20], [20, -196, 601, -382, -928, 1003, 357, -488, -28, 67], [67, -650, 1948, -1074, -3263, 3092, 1539, -1586, -220, 240], [240, -2333, 7030, -4052, -11394, 11137, 5012, -5421, -626, 740]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, 32, -25, -43, 60, 8, -29, 4, 4], [4, -39, 118, -68, -197, 197, 92, -108, -13, 20], [20, -196, 601, -382, -928, 1003, 357, -488, -28, 67], [67, -650, 1948, -1074, -3263, 3092, 1539, -1586, -220, 240], [240, -2333, 7030, -4052, -11394, 11137, 5012, -5421, -626, 740], [740, -7160, 21347, -11470, -35872, 33006, 17057, -16448, -2461, 2334]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, 32, -25, -43, 60, 8, -29, 4, 4], [4, -39, 118, -68, -197, 197, 92, -108, -13, 20], [20, -196, 601, -382, -928, 1003, 357, -488, -28, 67], [67, -650, 1948, -1074, -3263, 3092, 1539, -1586, -220, 240], [240, -2333, 7030, -4052, -11394, 11137, 5012, -5421, -626, 740], [740, -7160, 21347, -11470, -35872, 33006, 17057, -16448, -2461, 2334], [2334, -22600, 67528, -37003, -111832, 104168, 51678, -50629, -7112, 6875]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, 32, -25, -43, 60, 8, -29, 4, 4], [4, -39, 118, -68, -197, 197, 92, -108, -13, 20], [20, -196, 601, -382, -928, 1003, 357, -488, -28, 67], [67, -650, 1948, -1074, -3263, 3092, 1539, -1586, -220, 240], [240, -2333, 7030, -4052, -11394, 11137, 5012, -5421, -626, 740], [740, -7160, 21347, -11470, -35872, 33006, 17057, -16448, -2461, 2334], [2334, -22600, 67528, -37003, -111832, 104168, 51678, -50629, -7112, 6875], [6875, -66416, 197400, -104347, -332628, 300668, 159168, -147697, -23129, 20388]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -10, 32, -25, -43, 60, 8, -29, 4, 4], [4, -39, 118, -68, -197, 197, 92, -108, -13, 20], [20, -196, 601, -382, -928, 1003, 357, -488, -28, 67], [67, -650, 1948, -1074, -3263, 3092, 1539, -1586, -220, 240], [240, -2333, 7030, -4052, -11394, 11137, 5012, -5421, -626, 740], [740, -7160, 21347, -11470, -35872, 33006, 17057, -16448, -2461, 2334], [2334, -22600, 67528, -37003, -111832, 104168, 51678, -50629, -7112, 6875], [6875, -66416, 197400, -104347, -332628, 300668, 159168, -147697, -23129, 20388], [20388, -197005, 586000, -312300, -981031, 890652, 463772, -432084, -66145, 58423]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp151 : Fact (Nat.Prime 151) := fact_iff.2 (by norm_num)
instance hp38569 : Fact (Nat.Prime 38569) := fact_iff.2 (by norm_num)

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [6, 10, 7, 7, 3, 9, 4, 10]
  b' := [1, 6, 1, 7, 10, 5, 1, 7, 5]
  k := [8, 5, 6, 0, 1, 8, 3, 0, 1]
  f := [5, 7, 7, 3, 4, 12, 3, 0, 8, 2]
  g := [6, 9, 4, 6, 9, 7, 2, 3, 9, 1]
  h := [9, 1]
  a := [4, 8, 9, 0, 4, 5, 7, 3, 3]
  b := [6, 9, 5, 10, 0, 9, 6, 2, 5]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD151 : CertificateDedekindCriterionLists l 151 where
  n := 2
  a' := [91, 131, 109, 17, 146, 43, 110, 28]
  b' := [130, 55, 13, 1, 85, 0, 34, 104, 64]
  k := [83, 83, 39, 109, 112, 8, 82, 65, 1]
  f := [22, 4, 6, 35, 6, 38, 14, 8, 29, 1]
  g := [81, 13, 21, 129, 20, 138, 48, 29, 106, 1]
  h := [41, 1]
  a := [92, 111, 11, 112, 134, 72, 33, 4, 42]
  b := [44, 44, 52, 109, 18, 116, 66, 59, 109]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD38569 : CertificateDedekindCriterionLists l 38569 where
  n := 2
  a' := [24614, 36734, 11116, 27067, 7000, 8107, 37344]
  b' := [17322, 7443, 5305, 29735, 15875, 1390, 4984, 33901]
  k := [23282, 37601, 24658, 9386, 2207, 2016, 1]
  f := [1489, 38019, 36164, 18395, 13721, 13423, 14354, 11466, 980, 1]
  g := [37560, 36389, 18337, 13552, 13203, 14262, 11733, 1006, 1]
  h := [1529, 37559, 1]
  a := [6220, 32927, 27048, 23874, 15898, 35340, 35772, 30736]
  b := [37389, 14456, 7711, 3507, 28513, 17168, 380, 30553, 7833]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![11, 151, 38569]
  exp := ![1, 1, 1]
  pdgood := [11, 151, 38569]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp11.out
    exact hp151.out
    exact hp38569.out
  a := [178316499121, -489976544632, -436109169059, 1470254373446, -27853597573, -943735736622, 203726767208, 163704327162, -49322633320]
  b := [17838056223, -113150593757, 159029203196, 129020202375, -296066488292, -1309402463, 136016036049, -24872773498, -18343338049, 4932263332]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 151 T_ofList CD151
    exact satisfiesDedekindCriterion_of_certificate_lists T l 38569 T_ofList CD38569

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

end VoightMaximalOrderD10R133

namespace VoightMaximalOrderD10R134

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2490005403125, [-5, -10, 26, 32, -45, -30, 33, 10, -10, -1, 1], 1⟩
local notation "l" => [-5, -10, 26, 32, -45, -30, 33, 10, -10, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 10, -26, -32, 45, 30, -33, -10, 10, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 10, -26, -32, 45, 30, -33, -10, 10, 1], ![5, 15, -16, -58, 13, 75, -3, -43, 0, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 10, -26, -32, 45, 30, -33, -10, 10, 1], ![5, 15, -16, -58, 13, 75, -3, -43, 0, 11], ![55, 115, -271, -368, 437, 343, -288, -113, 67, 11]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 10, -26, -32, 45, 30, -33, -10, 10, 1], ![5, 15, -16, -58, 13, 75, -3, -43, 0, 11], ![55, 115, -271, -368, 437, 343, -288, -113, 67, 11], ![55, 165, -171, -623, 127, 767, -20, -398, -3, 78]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 10, -26, -32, 45, 30, -33, -10, 10, 1], ![5, 15, -16, -58, 13, 75, -3, -43, 0, 11], ![55, 115, -271, -368, 437, 343, -288, -113, 67, 11], ![55, 165, -171, -623, 127, 767, -20, -398, -3, 78], ![390, 835, -1863, -2667, 2887, 2467, -1807, -800, 382, 75]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 10, -26, -32, 45, 30, -33, -10, 10, 1], ![5, 15, -16, -58, 13, 75, -3, -43, 0, 11], ![55, 115, -271, -368, 437, 343, -288, -113, 67, 11], ![55, 165, -171, -623, 127, 767, -20, -398, -3, 78], ![390, 835, -1863, -2667, 2887, 2467, -1807, -800, 382, 75], ![375, 1140, -1115, -4263, 708, 5137, -8, -2557, -50, 457]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 10, -26, -32, 45, 30, -33, -10, 10, 1], ![5, 15, -16, -58, 13, 75, -3, -43, 0, 11], ![55, 115, -271, -368, 437, 343, -288, -113, 67, 11], ![55, 165, -171, -623, 127, 767, -20, -398, -3, 78], ![390, 835, -1863, -2667, 2887, 2467, -1807, -800, 382, 75], ![375, 1140, -1115, -4263, 708, 5137, -8, -2557, -50, 457], ![2285, 4945, -10742, -15739, 16302, 14418, -9944, -4578, 2013, 407]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 10, -26, -32, 45, 30, -33, -10, 10, 1], ![5, 15, -16, -58, 13, 75, -3, -43, 0, 11], ![55, 115, -271, -368, 437, 343, -288, -113, 67, 11], ![55, 165, -171, -623, 127, 767, -20, -398, -3, 78], ![390, 835, -1863, -2667, 2887, 2467, -1807, -800, 382, 75], ![375, 1140, -1115, -4263, 708, 5137, -8, -2557, -50, 457], ![2285, 4945, -10742, -15739, 16302, 14418, -9944, -4578, 2013, 407], ![2035, 6355, -5637, -23766, 2576, 28512, 987, -14014, -508, 2420]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![5, 10, -26, -32, 45, 30, -33, -10, 10, 1], ![5, 15, -16, -58, 13, 75, -3, -43, 0, 11], ![55, 115, -271, -368, 437, 343, -288, -113, 67, 11], ![55, 165, -171, -623, 127, 767, -20, -398, -3, 78], ![390, 835, -1863, -2667, 2887, 2467, -1807, -800, 382, 75], ![375, 1140, -1115, -4263, 708, 5137, -8, -2557, -50, 457], ![2285, 4945, -10742, -15739, 16302, 14418, -9944, -4578, 2013, 407], ![2035, 6355, -5637, -23766, 2576, 28512, 987, -14014, -508, 2420], ![12100, 26235, -56565, -83077, 85134, 75176, -51348, -23213, 10186, 1912]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-11, -11, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-11, -11, -1, -1], [-78, -11, -11, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-11, -1, -1], [-11, -11, -1, -1], [-78, -11, -11, -1, -1], [-75, -78, -11, -11, -1, -1]], ![[], [], [], [-1], [-1, -1], [-11, -1, -1], [-11, -11, -1, -1], [-78, -11, -11, -1, -1], [-75, -78, -11, -11, -1, -1], [-457, -75, -78, -11, -11, -1, -1]], ![[], [], [-1], [-1, -1], [-11, -1, -1], [-11, -11, -1, -1], [-78, -11, -11, -1, -1], [-75, -78, -11, -11, -1, -1], [-457, -75, -78, -11, -11, -1, -1], [-407, -457, -75, -78, -11, -11, -1, -1]], ![[], [-1], [-1, -1], [-11, -1, -1], [-11, -11, -1, -1], [-78, -11, -11, -1, -1], [-75, -78, -11, -11, -1, -1], [-457, -75, -78, -11, -11, -1, -1], [-407, -457, -75, -78, -11, -11, -1, -1], [-2420, -407, -457, -75, -78, -11, -11, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 10, -26, -32, 45, 30, -33, -10, 10, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 10, -26, -32, 45, 30, -33, -10, 10, 1], [5, 15, -16, -58, 13, 75, -3, -43, 0, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 10, -26, -32, 45, 30, -33, -10, 10, 1], [5, 15, -16, -58, 13, 75, -3, -43, 0, 11], [55, 115, -271, -368, 437, 343, -288, -113, 67, 11]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 10, -26, -32, 45, 30, -33, -10, 10, 1], [5, 15, -16, -58, 13, 75, -3, -43, 0, 11], [55, 115, -271, -368, 437, 343, -288, -113, 67, 11], [55, 165, -171, -623, 127, 767, -20, -398, -3, 78]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 10, -26, -32, 45, 30, -33, -10, 10, 1], [5, 15, -16, -58, 13, 75, -3, -43, 0, 11], [55, 115, -271, -368, 437, 343, -288, -113, 67, 11], [55, 165, -171, -623, 127, 767, -20, -398, -3, 78], [390, 835, -1863, -2667, 2887, 2467, -1807, -800, 382, 75]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 10, -26, -32, 45, 30, -33, -10, 10, 1], [5, 15, -16, -58, 13, 75, -3, -43, 0, 11], [55, 115, -271, -368, 437, 343, -288, -113, 67, 11], [55, 165, -171, -623, 127, 767, -20, -398, -3, 78], [390, 835, -1863, -2667, 2887, 2467, -1807, -800, 382, 75], [375, 1140, -1115, -4263, 708, 5137, -8, -2557, -50, 457]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 10, -26, -32, 45, 30, -33, -10, 10, 1], [5, 15, -16, -58, 13, 75, -3, -43, 0, 11], [55, 115, -271, -368, 437, 343, -288, -113, 67, 11], [55, 165, -171, -623, 127, 767, -20, -398, -3, 78], [390, 835, -1863, -2667, 2887, 2467, -1807, -800, 382, 75], [375, 1140, -1115, -4263, 708, 5137, -8, -2557, -50, 457], [2285, 4945, -10742, -15739, 16302, 14418, -9944, -4578, 2013, 407]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 10, -26, -32, 45, 30, -33, -10, 10, 1], [5, 15, -16, -58, 13, 75, -3, -43, 0, 11], [55, 115, -271, -368, 437, 343, -288, -113, 67, 11], [55, 165, -171, -623, 127, 767, -20, -398, -3, 78], [390, 835, -1863, -2667, 2887, 2467, -1807, -800, 382, 75], [375, 1140, -1115, -4263, 708, 5137, -8, -2557, -50, 457], [2285, 4945, -10742, -15739, 16302, 14418, -9944, -4578, 2013, 407], [2035, 6355, -5637, -23766, 2576, 28512, 987, -14014, -508, 2420]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [5, 10, -26, -32, 45, 30, -33, -10, 10, 1], [5, 15, -16, -58, 13, 75, -3, -43, 0, 11], [55, 115, -271, -368, 437, 343, -288, -113, 67, 11], [55, 165, -171, -623, 127, 767, -20, -398, -3, 78], [390, 835, -1863, -2667, 2887, 2467, -1807, -800, 382, 75], [375, 1140, -1115, -4263, 708, 5137, -8, -2557, -50, 457], [2285, 4945, -10742, -15739, 16302, 14418, -9944, -4578, 2013, 407], [2035, 6355, -5637, -23766, 2576, 28512, 987, -14014, -508, 2420], [12100, 26235, -56565, -83077, 85134, 75176, -51348, -23213, 10186, 1912]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp1741 : Fact (Nat.Prime 1741) := fact_iff.2 (by norm_num)
instance hp457669 : Fact (Nat.Prime 457669) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2, 1, 1]
  b' := [4, 0, 3, 0, 3]
  k := [1]
  f := [1, 2, -2, 0, 17, 14, 0, 2, 4, 1]
  g := [0, 4, 4, 3, 2, 1]
  h := [0, 4, 4, 3, 2, 1]
  a := [1, 1, 0, 1, 1]
  b := [3, 2, 1, 1, 0, 4, 3, 2, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1741 : CertificateDedekindCriterionLists l 1741 where
  n := 2
  a' := [1435, 276, 1205, 269, 1417, 1247, 368, 873]
  b' := [1648, 821, 181, 789, 5, 215, 696, 443, 1644]
  k := [680, 1190, 726, 1487, 1330, 1412, 198, 1724, 1]
  f := [1, 7, 1, 2, 8, 3, 6, 1, 8, 1]
  g := [217, 1495, 34, 435, 1681, 439, 1255, 62, 1732, 1]
  h := [8, 1]
  a := [1677, 48, 1702, 1635, 654, 847, 1279, 1389, 1578]
  b := [1637, 1296, 642, 968, 619, 922, 550, 1382, 163]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD457669 : CertificateDedekindCriterionLists l 457669 where
  n := 2
  a' := [373285, 7737, 337269, 4979, 182512, 277777, 280225, 164048]
  b' := [189526, 81292, 159745, 447223, 358581, 378312, 169248, 194279, 236033]
  k := [139503, 253743, 454057, 44599, 182552, 284668, 30724, 217208, 1]
  f := [65635, 94623, 81665, 22108, 78021, 108505, 101059, 93371, 88646, 1]
  g := [249847, 360191, 310864, 84154, 296995, 413034, 384689, 355424, 337438, 1]
  h := [120230, 1]
  a := [423183, 227207, 265677, 304015, 6393, 289779, 195100, 411366, 251229]
  b := [237992, 352834, 220427, 396263, 300914, 180803, 388403, 414010, 206440]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 1741, 457669]
  exp := ![1, 1, 1]
  pdgood := [5, 1741, 457669]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp1741.out
    exact hp457669.out
  a := [-28655083959, 119842136560, 388416261796, -210210347432, -636728511541, 92407125826, 295394648979, -13838826262, -39683784720]
  b := [13929141115, 41165549477, -40772873767, -130972010372, 28508549271, 116724356775, -7913168049, -37971764167, 987044779, 3968378472]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1741 T_ofList CD1741
    exact satisfiesDedekindCriterion_of_certificate_lists T l 457669 T_ofList CD457669

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

end VoightMaximalOrderD10R134

namespace VoightMaximalOrderD10R135

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨2505570811904, [1, -2, -11, 20, 21, -36, -9, 22, -2, -4, 1], 1⟩
local notation "l" => [1, -2, -11, 20, 21, -36, -9, 22, -2, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 11, -20, -21, 36, 9, -22, 2, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 11, -20, -21, 36, 9, -22, 2, 4], ![-4, 7, 46, -69, -104, 123, 72, -79, -14, 18]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 11, -20, -21, 36, 9, -22, 2, 4], ![-4, 7, 46, -69, -104, 123, 72, -79, -14, 18], ![-18, 32, 205, -314, -447, 544, 285, -324, -43, 58]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 11, -20, -21, 36, 9, -22, 2, 4], ![-4, 7, 46, -69, -104, 123, 72, -79, -14, 18], ![-18, 32, 205, -314, -447, 544, 285, -324, -43, 58], ![-58, 98, 670, -955, -1532, 1641, 1066, -991, -208, 189]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 11, -20, -21, 36, 9, -22, 2, 4], ![-4, 7, 46, -69, -104, 123, 72, -79, -14, 18], ![-18, 32, 205, -314, -447, 544, 285, -324, -43, 58], ![-58, 98, 670, -955, -1532, 1641, 1066, -991, -208, 189], ![-189, 320, 2177, -3110, -4924, 5272, 3342, -3092, -613, 548]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 11, -20, -21, 36, 9, -22, 2, 4], ![-4, 7, 46, -69, -104, 123, 72, -79, -14, 18], ![-18, 32, 205, -314, -447, 544, 285, -324, -43, 58], ![-58, 98, 670, -955, -1532, 1641, 1066, -991, -208, 189], ![-189, 320, 2177, -3110, -4924, 5272, 3342, -3092, -613, 548], ![-548, 907, 6348, -8783, -14618, 14804, 10204, -8714, -1996, 1579]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 11, -20, -21, 36, 9, -22, 2, 4], ![-4, 7, 46, -69, -104, 123, 72, -79, -14, 18], ![-18, 32, 205, -314, -447, 544, 285, -324, -43, 58], ![-58, 98, 670, -955, -1532, 1641, 1066, -991, -208, 189], ![-189, 320, 2177, -3110, -4924, 5272, 3342, -3092, -613, 548], ![-548, 907, 6348, -8783, -14618, 14804, 10204, -8714, -1996, 1579], ![-1579, 2610, 18276, -25232, -41942, 42226, 29015, -24534, -5556, 4320]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 11, -20, -21, 36, 9, -22, 2, 4], ![-4, 7, 46, -69, -104, 123, 72, -79, -14, 18], ![-18, 32, 205, -314, -447, 544, 285, -324, -43, 58], ![-58, 98, 670, -955, -1532, 1641, 1066, -991, -208, 189], ![-189, 320, 2177, -3110, -4924, 5272, 3342, -3092, -613, 548], ![-548, 907, 6348, -8783, -14618, 14804, 10204, -8714, -1996, 1579], ![-1579, 2610, 18276, -25232, -41942, 42226, 29015, -24534, -5556, 4320], ![-4320, 7061, 50130, -68124, -115952, 113578, 81106, -66025, -15894, 11724]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 2, 11, -20, -21, 36, 9, -22, 2, 4], ![-4, 7, 46, -69, -104, 123, 72, -79, -14, 18], ![-18, 32, 205, -314, -447, 544, 285, -324, -43, 58], ![-58, 98, 670, -955, -1532, 1641, 1066, -991, -208, 189], ![-189, 320, 2177, -3110, -4924, 5272, 3342, -3092, -613, 548], ![-548, 907, 6348, -8783, -14618, 14804, 10204, -8714, -1996, 1579], ![-1579, 2610, 18276, -25232, -41942, 42226, 29015, -24534, -5556, 4320], ![-4320, 7061, 50130, -68124, -115952, 113578, 81106, -66025, -15894, 11724], ![-11724, 19128, 136025, -184350, -314328, 306112, 219094, -176822, -42577, 31002]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-18, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-18, -4, -1], [-58, -18, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-18, -4, -1], [-58, -18, -4, -1], [-189, -58, -18, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-18, -4, -1], [-58, -18, -4, -1], [-189, -58, -18, -4, -1], [-548, -189, -58, -18, -4, -1]], ![[], [], [], [-1], [-4, -1], [-18, -4, -1], [-58, -18, -4, -1], [-189, -58, -18, -4, -1], [-548, -189, -58, -18, -4, -1], [-1579, -548, -189, -58, -18, -4, -1]], ![[], [], [-1], [-4, -1], [-18, -4, -1], [-58, -18, -4, -1], [-189, -58, -18, -4, -1], [-548, -189, -58, -18, -4, -1], [-1579, -548, -189, -58, -18, -4, -1], [-4320, -1579, -548, -189, -58, -18, -4, -1]], ![[], [-1], [-4, -1], [-18, -4, -1], [-58, -18, -4, -1], [-189, -58, -18, -4, -1], [-548, -189, -58, -18, -4, -1], [-1579, -548, -189, -58, -18, -4, -1], [-4320, -1579, -548, -189, -58, -18, -4, -1], [-11724, -4320, -1579, -548, -189, -58, -18, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 11, -20, -21, 36, 9, -22, 2, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 11, -20, -21, 36, 9, -22, 2, 4], [-4, 7, 46, -69, -104, 123, 72, -79, -14, 18]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 11, -20, -21, 36, 9, -22, 2, 4], [-4, 7, 46, -69, -104, 123, 72, -79, -14, 18], [-18, 32, 205, -314, -447, 544, 285, -324, -43, 58]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 11, -20, -21, 36, 9, -22, 2, 4], [-4, 7, 46, -69, -104, 123, 72, -79, -14, 18], [-18, 32, 205, -314, -447, 544, 285, -324, -43, 58], [-58, 98, 670, -955, -1532, 1641, 1066, -991, -208, 189]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 11, -20, -21, 36, 9, -22, 2, 4], [-4, 7, 46, -69, -104, 123, 72, -79, -14, 18], [-18, 32, 205, -314, -447, 544, 285, -324, -43, 58], [-58, 98, 670, -955, -1532, 1641, 1066, -991, -208, 189], [-189, 320, 2177, -3110, -4924, 5272, 3342, -3092, -613, 548]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 11, -20, -21, 36, 9, -22, 2, 4], [-4, 7, 46, -69, -104, 123, 72, -79, -14, 18], [-18, 32, 205, -314, -447, 544, 285, -324, -43, 58], [-58, 98, 670, -955, -1532, 1641, 1066, -991, -208, 189], [-189, 320, 2177, -3110, -4924, 5272, 3342, -3092, -613, 548], [-548, 907, 6348, -8783, -14618, 14804, 10204, -8714, -1996, 1579]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 11, -20, -21, 36, 9, -22, 2, 4], [-4, 7, 46, -69, -104, 123, 72, -79, -14, 18], [-18, 32, 205, -314, -447, 544, 285, -324, -43, 58], [-58, 98, 670, -955, -1532, 1641, 1066, -991, -208, 189], [-189, 320, 2177, -3110, -4924, 5272, 3342, -3092, -613, 548], [-548, 907, 6348, -8783, -14618, 14804, 10204, -8714, -1996, 1579], [-1579, 2610, 18276, -25232, -41942, 42226, 29015, -24534, -5556, 4320]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 11, -20, -21, 36, 9, -22, 2, 4], [-4, 7, 46, -69, -104, 123, 72, -79, -14, 18], [-18, 32, 205, -314, -447, 544, 285, -324, -43, 58], [-58, 98, 670, -955, -1532, 1641, 1066, -991, -208, 189], [-189, 320, 2177, -3110, -4924, 5272, 3342, -3092, -613, 548], [-548, 907, 6348, -8783, -14618, 14804, 10204, -8714, -1996, 1579], [-1579, 2610, 18276, -25232, -41942, 42226, 29015, -24534, -5556, 4320], [-4320, 7061, 50130, -68124, -115952, 113578, 81106, -66025, -15894, 11724]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 2, 11, -20, -21, 36, 9, -22, 2, 4], [-4, 7, 46, -69, -104, 123, 72, -79, -14, 18], [-18, 32, 205, -314, -447, 544, 285, -324, -43, 58], [-58, 98, 670, -955, -1532, 1641, 1066, -991, -208, 189], [-189, 320, 2177, -3110, -4924, 5272, 3342, -3092, -613, 548], [-548, 907, 6348, -8783, -14618, 14804, 10204, -8714, -1996, 1579], [-1579, 2610, 18276, -25232, -41942, 42226, 29015, -24534, -5556, 4320], [-4320, 7061, 50130, -68124, -115952, 113578, 81106, -66025, -15894, 11724], [-11724, 19128, 136025, -184350, -314328, 306112, 219094, -176822, -42577, 31002]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp1847 : Fact (Nat.Prime 1847) := fact_iff.2 (by norm_num)
instance hp41399 : Fact (Nat.Prime 41399) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [0, 0, 1]
  b' := [1, 0, 0, 1]
  k := [1]
  f := [0, 2, 7, -8, -9, 20, 6, -10, 2, 2]
  g := [1, 1, 1, 1, 0, 1]
  h := [1, 1, 1, 1, 0, 1]
  a := [1, 1, 1, 1]
  b := [1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1847 : CertificateDedekindCriterionLists l 1847 where
  n := 2
  a' := [1458, 1054, 113, 293, 1060, 816, 180, 55]
  b' := [1288, 931, 423, 769, 1097, 556, 402, 1031, 1020]
  k := [1001, 1497, 1395, 1154, 776, 1509, 815, 468, 1]
  f := [157, 424, 910, 489, 760, 980, 1097, 1036, 203, 1]
  g := [180, 486, 1043, 560, 871, 1123, 1257, 1187, 232, 1]
  h := [1611, 1]
  a := [932, 844, 1058, 122, 701, 148, 1382, 1552, 734]
  b := [716, 430, 920, 556, 1122, 187, 1685, 1264, 1113]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD41399 : CertificateDedekindCriterionLists l 41399 where
  n := 2
  a' := [18071, 27988, 5038, 1767, 37558, 17740, 1516, 17752]
  b' := [19483, 31643, 20704, 20971, 38709, 4571, 37913, 12332, 21027]
  k := [40052, 12109, 15945, 8752, 25526, 17725, 4047, 38677, 1]
  f := [1063, 637, 975, 933, 205, 643, 379, 1010, 1315, 1]
  g := [32382, 19381, 29687, 28400, 6224, 19583, 11531, 30759, 40036, 1]
  h := [1359, 1]
  a := [41360, 37904, 18775, 22916, 12910, 21716, 18671, 21816, 15830]
  b := [38782, 13450, 16094, 15386, 18799, 33387, 9977, 19419, 25569]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 1847, 41399]
  exp := ![2, 1, 1]
  pdgood := [2, 1847, 41399]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp1847.out
    exact hp41399.out
  a := [-342929056, -8440587218, -1850509234, 25435579058, -708939758, -21345397830, 4566008946, 4912385900, -1570072100]
  b := [-324392434, -309047779, 3069194958, 905177766, -5284669762, -52194671, 3116806359, -548998725, -554041474, 157007210]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1847 T_ofList CD1847
    exact satisfiesDedekindCriterion_of_certificate_lists T l 41399 T_ofList CD41399

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

end VoightMaximalOrderD10R135

end TraceEuclidean
