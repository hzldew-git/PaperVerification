import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk218
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

namespace VoightMaximalOrderD10R592

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6351881378125, [1, -3, -23, 60, -4, -68, 25, 22, -10, -2, 1], 1⟩
local notation "l" => [1, -3, -23, 60, -4, -68, 25, 22, -10, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 23, -60, 4, 68, -25, -22, 10, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 23, -60, 4, 68, -25, -22, 10, 2], ![-2, 5, 49, -97, -52, 140, 18, -69, -2, 14]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 23, -60, 4, 68, -25, -22, 10, 2], ![-2, 5, 49, -97, -52, 140, 18, -69, -2, 14], ![-14, 40, 327, -791, -41, 900, -210, -290, 71, 26]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 23, -60, 4, 68, -25, -22, 10, 2], ![-2, 5, 49, -97, -52, 140, 18, -69, -2, 14], ![-14, 40, 327, -791, -41, 900, -210, -290, 71, 26], ![-26, 64, 638, -1233, -687, 1727, 250, -782, -30, 123]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 23, -60, 4, 68, -25, -22, 10, 2], ![-2, 5, 49, -97, -52, 140, 18, -69, -2, 14], ![-14, 40, 327, -791, -41, 900, -210, -290, 71, 26], ![-26, 64, 638, -1233, -687, 1727, 250, -782, -30, 123], ![-123, 343, 2893, -6742, -741, 7677, -1348, -2456, 448, 216]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 23, -60, 4, 68, -25, -22, 10, 2], ![-2, 5, 49, -97, -52, 140, 18, -69, -2, 14], ![-14, 40, 327, -791, -41, 900, -210, -290, 71, 26], ![-26, 64, 638, -1233, -687, 1727, 250, -782, -30, 123], ![-123, 343, 2893, -6742, -741, 7677, -1348, -2456, 448, 216], ![-216, 525, 5311, -10067, -5878, 13947, 2277, -6100, -296, 880]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 23, -60, 4, 68, -25, -22, 10, 2], ![-2, 5, 49, -97, -52, 140, 18, -69, -2, 14], ![-14, 40, 327, -791, -41, 900, -210, -290, 71, 26], ![-26, 64, 638, -1233, -687, 1727, 250, -782, -30, 123], ![-123, 343, 2893, -6742, -741, 7677, -1348, -2456, 448, 216], ![-216, 525, 5311, -10067, -5878, 13947, 2277, -6100, -296, 880], ![-880, 2424, 20765, -47489, -6547, 53962, -8053, -17083, 2700, 1464]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 23, -60, 4, 68, -25, -22, 10, 2], ![-2, 5, 49, -97, -52, 140, 18, -69, -2, 14], ![-14, 40, 327, -791, -41, 900, -210, -290, 71, 26], ![-26, 64, 638, -1233, -687, 1727, 250, -782, -30, 123], ![-123, 343, 2893, -6742, -741, 7677, -1348, -2456, 448, 216], ![-216, 525, 5311, -10067, -5878, 13947, 2277, -6100, -296, 880], ![-880, 2424, 20765, -47489, -6547, 53962, -8053, -17083, 2700, 1464], ![-1464, 3512, 36096, -67075, -41633, 93005, 17362, -40261, -2443, 5628]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 3, 23, -60, 4, 68, -25, -22, 10, 2], ![-2, 5, 49, -97, -52, 140, 18, -69, -2, 14], ![-14, 40, 327, -791, -41, 900, -210, -290, 71, 26], ![-26, 64, 638, -1233, -687, 1727, 250, -782, -30, 123], ![-123, 343, 2893, -6742, -741, 7677, -1348, -2456, 448, 216], ![-216, 525, 5311, -10067, -5878, 13947, 2277, -6100, -296, 880], ![-880, 2424, 20765, -47489, -6547, 53962, -8053, -17083, 2700, 1464], ![-1464, 3512, 36096, -67075, -41633, 93005, 17362, -40261, -2443, 5628], ![-5628, 15420, 132956, -301584, -44563, 341071, -47695, -106454, 16019, 8813]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-26, -14, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-26, -14, -2, -1], [-123, -26, -14, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-26, -14, -2, -1], [-123, -26, -14, -2, -1], [-216, -123, -26, -14, -2, -1]], ![[], [], [], [-1], [-2, -1], [-14, -2, -1], [-26, -14, -2, -1], [-123, -26, -14, -2, -1], [-216, -123, -26, -14, -2, -1], [-880, -216, -123, -26, -14, -2, -1]], ![[], [], [-1], [-2, -1], [-14, -2, -1], [-26, -14, -2, -1], [-123, -26, -14, -2, -1], [-216, -123, -26, -14, -2, -1], [-880, -216, -123, -26, -14, -2, -1], [-1464, -880, -216, -123, -26, -14, -2, -1]], ![[], [-1], [-2, -1], [-14, -2, -1], [-26, -14, -2, -1], [-123, -26, -14, -2, -1], [-216, -123, -26, -14, -2, -1], [-880, -216, -123, -26, -14, -2, -1], [-1464, -880, -216, -123, -26, -14, -2, -1], [-5628, -1464, -880, -216, -123, -26, -14, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 23, -60, 4, 68, -25, -22, 10, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 23, -60, 4, 68, -25, -22, 10, 2], [-2, 5, 49, -97, -52, 140, 18, -69, -2, 14]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 23, -60, 4, 68, -25, -22, 10, 2], [-2, 5, 49, -97, -52, 140, 18, -69, -2, 14], [-14, 40, 327, -791, -41, 900, -210, -290, 71, 26]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 23, -60, 4, 68, -25, -22, 10, 2], [-2, 5, 49, -97, -52, 140, 18, -69, -2, 14], [-14, 40, 327, -791, -41, 900, -210, -290, 71, 26], [-26, 64, 638, -1233, -687, 1727, 250, -782, -30, 123]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 23, -60, 4, 68, -25, -22, 10, 2], [-2, 5, 49, -97, -52, 140, 18, -69, -2, 14], [-14, 40, 327, -791, -41, 900, -210, -290, 71, 26], [-26, 64, 638, -1233, -687, 1727, 250, -782, -30, 123], [-123, 343, 2893, -6742, -741, 7677, -1348, -2456, 448, 216]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 23, -60, 4, 68, -25, -22, 10, 2], [-2, 5, 49, -97, -52, 140, 18, -69, -2, 14], [-14, 40, 327, -791, -41, 900, -210, -290, 71, 26], [-26, 64, 638, -1233, -687, 1727, 250, -782, -30, 123], [-123, 343, 2893, -6742, -741, 7677, -1348, -2456, 448, 216], [-216, 525, 5311, -10067, -5878, 13947, 2277, -6100, -296, 880]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 23, -60, 4, 68, -25, -22, 10, 2], [-2, 5, 49, -97, -52, 140, 18, -69, -2, 14], [-14, 40, 327, -791, -41, 900, -210, -290, 71, 26], [-26, 64, 638, -1233, -687, 1727, 250, -782, -30, 123], [-123, 343, 2893, -6742, -741, 7677, -1348, -2456, 448, 216], [-216, 525, 5311, -10067, -5878, 13947, 2277, -6100, -296, 880], [-880, 2424, 20765, -47489, -6547, 53962, -8053, -17083, 2700, 1464]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 23, -60, 4, 68, -25, -22, 10, 2], [-2, 5, 49, -97, -52, 140, 18, -69, -2, 14], [-14, 40, 327, -791, -41, 900, -210, -290, 71, 26], [-26, 64, 638, -1233, -687, 1727, 250, -782, -30, 123], [-123, 343, 2893, -6742, -741, 7677, -1348, -2456, 448, 216], [-216, 525, 5311, -10067, -5878, 13947, 2277, -6100, -296, 880], [-880, 2424, 20765, -47489, -6547, 53962, -8053, -17083, 2700, 1464], [-1464, 3512, 36096, -67075, -41633, 93005, 17362, -40261, -2443, 5628]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 3, 23, -60, 4, 68, -25, -22, 10, 2], [-2, 5, 49, -97, -52, 140, 18, -69, -2, 14], [-14, 40, 327, -791, -41, 900, -210, -290, 71, 26], [-26, 64, 638, -1233, -687, 1727, 250, -782, -30, 123], [-123, 343, 2893, -6742, -741, 7677, -1348, -2456, 448, 216], [-216, 525, 5311, -10067, -5878, 13947, 2277, -6100, -296, 880], [-880, 2424, 20765, -47489, -6547, 53962, -8053, -17083, 2700, 1464], [-1464, 3512, 36096, -67075, -41633, 93005, 17362, -40261, -2443, 5628], [-5628, 15420, 132956, -301584, -44563, 341071, -47695, -106454, 16019, 8813]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp2032602041 : Fact (Nat.Prime 2032602041) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 0, 3]
  b' := [0, 4, 0, 1, 2]
  k := [1]
  f := [0, 1, 6, -10, 5, 18, 1, 0, 6, 2]
  g := [1, 1, 3, 2, 4, 1]
  h := [1, 1, 3, 2, 4, 1]
  a := [1, 2, 3, 3, 4]
  b := [1, 3, 1, 3, 3, 3, 4, 2, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2032602041 : CertificateDedekindCriterionLists l 2032602041 where
  n := 2
  a' := [1523597260, 1617540708, 1820759384, 817645097, 692924703, 485105913, 1446935346, 223865031]
  b' := [1475868789, 1560749045, 1933589851, 1745478301, 310729227, 1043907215, 1290235526, 1341265432, 1330194135]
  k := [254698734, 626763117, 1279761111, 392109398, 819209211, 1776094726, 1626275023, 1278924018, 1]
  f := [887582399, 1342103062, 1226339170, 1086914199, 1170571341, 223460861, 1117790467, 79357814, 438285559, 1]
  g := [1294989560, 1958138709, 1789238298, 1585816191, 1707872606, 326031117, 1630864905, 115783661, 639462008, 1]
  h := [1393140031, 1]
  a := [105320864, 121587053, 1674231904, 1178674934, 946630266, 1139563160, 1048224608, 1991629054, 2003985726]
  b := [1428077273, 141644994, 321521048, 1168804781, 872281942, 295161607, 1888072256, 3521647, 28616315]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![5, 2032602041]
  exp := ![1, 1]
  pdgood := [5, 2032602041]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp2032602041.out
  a := [-62624564276, -1194882554960, 2793225450688, 2889345763832, -4401695867628, -1349165544144, 1888646987988, 149186694024, -223081693380]
  b := [-24262524827, 36355759970, 592872888812, -701807124744, -696186519800, 748497081510, 224673297306, -238528244556, -19380303270, 22308169338]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2032602041 T_ofList CD2032602041

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

end VoightMaximalOrderD10R592

namespace VoightMaximalOrderD10R593

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6354199778125, [1, -5, -3, 34, -10, -59, 38, 15, -12, -1, 1], 1⟩
local notation "l" => [1, -5, -3, 34, -10, -59, 38, 15, -12, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -34, 10, 59, -38, -15, 12, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -34, 10, 59, -38, -15, 12, 1], ![-1, 4, 8, -31, -24, 69, 21, -53, -3, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -34, 10, 59, -38, -15, 12, 1], ![-1, 4, 8, -31, -24, 69, 21, -53, -3, 13], ![-13, 64, 43, -434, 99, 743, -425, -174, 103, 10]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -34, 10, 59, -38, -15, 12, 1], ![-1, 4, 8, -31, -24, 69, 21, -53, -3, 13], ![-13, 64, 43, -434, 99, 743, -425, -174, 103, 10], ![-10, 37, 94, -297, -334, 689, 363, -575, -54, 113]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -34, 10, 59, -38, -15, 12, 1], ![-1, 4, 8, -31, -24, 69, 21, -53, -3, 13], ![-13, 64, 43, -434, 99, 743, -425, -174, 103, 10], ![-10, 37, 94, -297, -334, 689, 363, -575, -54, 113], ![-113, 555, 376, -3748, 833, 6333, -3605, -1332, 781, 59]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -34, 10, 59, -38, -15, 12, 1], ![-1, 4, 8, -31, -24, 69, 21, -53, -3, 13], ![-13, 64, 43, -434, 99, 743, -425, -174, 103, 10], ![-10, 37, 94, -297, -334, 689, 363, -575, -54, 113], ![-113, 555, 376, -3748, 833, 6333, -3605, -1332, 781, 59], ![-59, 182, 732, -1630, -3158, 4314, 4091, -4490, -624, 840]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -34, 10, 59, -38, -15, 12, 1], ![-1, 4, 8, -31, -24, 69, 21, -53, -3, 13], ![-13, 64, 43, -434, 99, 743, -425, -174, 103, 10], ![-10, 37, 94, -297, -334, 689, 363, -575, -54, 113], ![-113, 555, 376, -3748, 833, 6333, -3605, -1332, 781, 59], ![-59, 182, 732, -1630, -3158, 4314, 4091, -4490, -624, 840], ![-840, 4141, 2702, -27828, 6770, 46402, -27606, -8509, 5590, 216]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -34, 10, 59, -38, -15, 12, 1], ![-1, 4, 8, -31, -24, 69, 21, -53, -3, 13], ![-13, 64, 43, -434, 99, 743, -425, -174, 103, 10], ![-10, 37, 94, -297, -334, 689, 363, -575, -54, 113], ![-113, 555, 376, -3748, 833, 6333, -3605, -1332, 781, 59], ![-59, 182, 732, -1630, -3158, 4314, 4091, -4490, -624, 840], ![-840, 4141, 2702, -27828, 6770, 46402, -27606, -8509, 5590, 216], ![-216, 240, 4789, -4642, -25668, 19514, 38194, -30846, -5917, 5806]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 3, -34, 10, 59, -38, -15, 12, 1], ![-1, 4, 8, -31, -24, 69, 21, -53, -3, 13], ![-13, 64, 43, -434, 99, 743, -425, -174, 103, 10], ![-10, 37, 94, -297, -334, 689, 363, -575, -54, 113], ![-113, 555, 376, -3748, 833, 6333, -3605, -1332, 781, 59], ![-59, 182, 732, -1630, -3158, 4314, 4091, -4490, -624, 840], ![-840, 4141, 2702, -27828, 6770, 46402, -27606, -8509, 5590, 216], ![-216, 240, 4789, -4642, -25668, 19514, 38194, -30846, -5917, 5806], ![-5806, 28814, 17658, -192615, 53418, 316886, -201114, -48896, 38826, -111]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-13, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-10, -13, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-10, -13, -1, -1], [-113, -10, -13, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-10, -13, -1, -1], [-113, -10, -13, -1, -1], [-59, -113, -10, -13, -1, -1]], ![[], [], [], [-1], [-1, -1], [-13, -1, -1], [-10, -13, -1, -1], [-113, -10, -13, -1, -1], [-59, -113, -10, -13, -1, -1], [-840, -59, -113, -10, -13, -1, -1]], ![[], [], [-1], [-1, -1], [-13, -1, -1], [-10, -13, -1, -1], [-113, -10, -13, -1, -1], [-59, -113, -10, -13, -1, -1], [-840, -59, -113, -10, -13, -1, -1], [-216, -840, -59, -113, -10, -13, -1, -1]], ![[], [-1], [-1, -1], [-13, -1, -1], [-10, -13, -1, -1], [-113, -10, -13, -1, -1], [-59, -113, -10, -13, -1, -1], [-840, -59, -113, -10, -13, -1, -1], [-216, -840, -59, -113, -10, -13, -1, -1], [-5806, -216, -840, -59, -113, -10, -13, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -34, 10, 59, -38, -15, 12, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -34, 10, 59, -38, -15, 12, 1], [-1, 4, 8, -31, -24, 69, 21, -53, -3, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -34, 10, 59, -38, -15, 12, 1], [-1, 4, 8, -31, -24, 69, 21, -53, -3, 13], [-13, 64, 43, -434, 99, 743, -425, -174, 103, 10]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -34, 10, 59, -38, -15, 12, 1], [-1, 4, 8, -31, -24, 69, 21, -53, -3, 13], [-13, 64, 43, -434, 99, 743, -425, -174, 103, 10], [-10, 37, 94, -297, -334, 689, 363, -575, -54, 113]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -34, 10, 59, -38, -15, 12, 1], [-1, 4, 8, -31, -24, 69, 21, -53, -3, 13], [-13, 64, 43, -434, 99, 743, -425, -174, 103, 10], [-10, 37, 94, -297, -334, 689, 363, -575, -54, 113], [-113, 555, 376, -3748, 833, 6333, -3605, -1332, 781, 59]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -34, 10, 59, -38, -15, 12, 1], [-1, 4, 8, -31, -24, 69, 21, -53, -3, 13], [-13, 64, 43, -434, 99, 743, -425, -174, 103, 10], [-10, 37, 94, -297, -334, 689, 363, -575, -54, 113], [-113, 555, 376, -3748, 833, 6333, -3605, -1332, 781, 59], [-59, 182, 732, -1630, -3158, 4314, 4091, -4490, -624, 840]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -34, 10, 59, -38, -15, 12, 1], [-1, 4, 8, -31, -24, 69, 21, -53, -3, 13], [-13, 64, 43, -434, 99, 743, -425, -174, 103, 10], [-10, 37, 94, -297, -334, 689, 363, -575, -54, 113], [-113, 555, 376, -3748, 833, 6333, -3605, -1332, 781, 59], [-59, 182, 732, -1630, -3158, 4314, 4091, -4490, -624, 840], [-840, 4141, 2702, -27828, 6770, 46402, -27606, -8509, 5590, 216]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -34, 10, 59, -38, -15, 12, 1], [-1, 4, 8, -31, -24, 69, 21, -53, -3, 13], [-13, 64, 43, -434, 99, 743, -425, -174, 103, 10], [-10, 37, 94, -297, -334, 689, 363, -575, -54, 113], [-113, 555, 376, -3748, 833, 6333, -3605, -1332, 781, 59], [-59, 182, 732, -1630, -3158, 4314, 4091, -4490, -624, 840], [-840, 4141, 2702, -27828, 6770, 46402, -27606, -8509, 5590, 216], [-216, 240, 4789, -4642, -25668, 19514, 38194, -30846, -5917, 5806]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 3, -34, 10, 59, -38, -15, 12, 1], [-1, 4, 8, -31, -24, 69, 21, -53, -3, 13], [-13, 64, 43, -434, 99, 743, -425, -174, 103, 10], [-10, 37, 94, -297, -334, 689, 363, -575, -54, 113], [-113, 555, 376, -3748, 833, 6333, -3605, -1332, 781, 59], [-59, 182, 732, -1630, -3158, 4314, 4091, -4490, -624, 840], [-840, 4141, 2702, -27828, 6770, 46402, -27606, -8509, 5590, 216], [-216, 240, 4789, -4642, -25668, 19514, 38194, -30846, -5917, 5806], [-5806, 28814, 17658, -192615, 53418, 316886, -201114, -48896, 38826, -111]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp89 : Fact (Nat.Prime 89) := fact_iff.2 (by norm_num)
instance hp2269 : Fact (Nat.Prime 2269) := fact_iff.2 (by norm_num)
instance hp10069 : Fact (Nat.Prime 10069) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 0, 4]
  b' := [0, 0, 4, 0, 2]
  k := [1]
  f := [0, 1, 1, -6, 3, 13, -6, -1, 4, 1]
  g := [1, 0, 1, 2, 2, 1]
  h := [1, 0, 1, 2, 2, 1]
  a := [1, 1, 4, 2, 1]
  b := [1, 4, 2, 0, 0, 2, 4, 1, 4]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD89 : CertificateDedekindCriterionLists l 89 where
  n := 2
  a' := [68, 32, 36, 21, 40, 6, 12, 26]
  b' := [30, 16, 79, 38, 48, 14, 22, 55, 7]
  k := [80, 78, 16, 11, 75, 88, 40, 6, 1]
  f := [35, 35, 11, 10, 28, 17, 17, 9, 22, 1]
  g := [76, 74, 22, 22, 60, 34, 37, 19, 47, 1]
  h := [41, 1]
  a := [66, 56, 49, 7, 87, 48, 55, 86, 3]
  b := [27, 44, 87, 77, 80, 46, 24, 78, 86]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2269 : CertificateDedekindCriterionLists l 2269 where
  n := 2
  a' := [1403, 743, 602, 1345, 733, 1767, 1013, 273]
  b' := [1070, 1725, 330, 49, 746, 1370, 543, 1450, 726]
  k := [561, 1677, 1125, 495, 1205, 1326, 1953, 121, 1]
  f := [2027, 360, 1092, 416, 1817, 1950, 177, 1342, 59, 1]
  g := [2083, 369, 1122, 427, 1867, 2003, 181, 1379, 60, 1]
  h := [2208, 1]
  a := [2141, 1619, 1392, 68, 644, 441, 1512, 1005, 2241]
  b := [1667, 160, 1429, 1080, 1554, 506, 137, 1236, 28]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD10069 : CertificateDedekindCriterionLists l 10069 where
  n := 2
  a' := [1804, 4408, 9792, 1187, 3377, 8483, 8970, 6143]
  b' := [2721, 8114, 3072, 4707, 2349, 120, 7780, 8161, 1555]
  k := [7342, 9809, 3856, 9864, 188, 5395, 4861, 5339, 1]
  f := [884, 4983, 3533, 5497, 945, 3143, 4017, 5464, 1962, 1]
  g := [1203, 6781, 4807, 7480, 1285, 4277, 5466, 7435, 2669, 1]
  h := [7399, 1]
  a := [7141, 9807, 2624, 984, 4499, 4816, 8654, 4256, 9778]
  b := [5985, 288, 9244, 5687, 5728, 9724, 9355, 1456, 291]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 89, 2269, 10069]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 89, 2269, 10069]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp89.out
    exact hp2269.out
    exact hp10069.out
  a := [-128781080175, -664882247614, 772611635937, 2958976692930, -2942339801747, -1068188266628, 1215831496518, 88434449894, -126599003860]
  b := [-27789559964, 29152102609, 294783676510, -194319332849, -621511341040, 492708317087, 157442530253, -152221957114, -10109435028, 12659900386]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 89 T_ofList CD89
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2269 T_ofList CD2269
    exact satisfiesDedekindCriterion_of_certificate_lists T l 10069 T_ofList CD10069

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

end VoightMaximalOrderD10R593

namespace VoightMaximalOrderD10R594

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6362893642157, [1, 8, 4, -36, -33, 43, 48, -6, -13, 0, 1], 1⟩
local notation "l" => [1, 8, 4, -36, -33, 43, 48, -6, -13, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -4, 36, 33, -43, -48, 6, 13, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -4, 36, 33, -43, -48, 6, 13, 0], ![0, -1, -8, -4, 36, 33, -43, -48, 6, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -4, 36, 33, -43, -48, 6, 13, 0], ![0, -1, -8, -4, 36, 33, -43, -48, 6, 13], ![-13, -104, -53, 460, 425, -523, -591, 35, 121, 6]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -4, 36, 33, -43, -48, 6, 13, 0], ![0, -1, -8, -4, 36, 33, -43, -48, 6, 13], ![-13, -104, -53, 460, 425, -523, -591, 35, 121, 6], ![-6, -61, -128, 163, 658, 167, -811, -555, 113, 121]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -4, 36, 33, -43, -48, 6, 13, 0], ![0, -1, -8, -4, 36, 33, -43, -48, 6, 13], ![-13, -104, -53, 460, 425, -523, -591, 35, 121, 6], ![-6, -61, -128, 163, 658, 167, -811, -555, 113, 121], ![-121, -974, -545, 4228, 4156, -4545, -5641, -85, 1018, 113]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -4, 36, 33, -43, -48, 6, 13, 0], ![0, -1, -8, -4, 36, 33, -43, -48, 6, 13], ![-13, -104, -53, 460, 425, -523, -591, 35, 121, 6], ![-6, -61, -128, 163, 658, 167, -811, -555, 113, 121], ![-121, -974, -545, 4228, 4156, -4545, -5641, -85, 1018, 113], ![-113, -1025, -1426, 3523, 7957, -703, -9969, -4963, 1384, 1018]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -4, 36, 33, -43, -48, 6, 13, 0], ![0, -1, -8, -4, 36, 33, -43, -48, 6, 13], ![-13, -104, -53, 460, 425, -523, -591, 35, 121, 6], ![-6, -61, -128, 163, 658, 167, -811, -555, 113, 121], ![-121, -974, -545, 4228, 4156, -4545, -5641, -85, 1018, 113], ![-113, -1025, -1426, 3523, 7957, -703, -9969, -4963, 1384, 1018], ![-1018, -8257, -5097, 35222, 37117, -35817, -49567, -3861, 8271, 1384]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -4, 36, 33, -43, -48, 6, 13, 0], ![0, -1, -8, -4, 36, 33, -43, -48, 6, 13], ![-13, -104, -53, 460, 425, -523, -591, 35, 121, 6], ![-6, -61, -128, 163, 658, 167, -811, -555, 113, 121], ![-121, -974, -545, 4228, 4156, -4545, -5641, -85, 1018, 113], ![-113, -1025, -1426, 3523, 7957, -703, -9969, -4963, 1384, 1018], ![-1018, -8257, -5097, 35222, 37117, -35817, -49567, -3861, 8271, 1384], ![-1384, -12090, -13793, 44727, 80894, -22395, -102249, -41263, 14131, 8271]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -8, -4, 36, 33, -43, -48, 6, 13, 0], ![0, -1, -8, -4, 36, 33, -43, -48, 6, 13], ![-13, -104, -53, 460, 425, -523, -591, 35, 121, 6], ![-6, -61, -128, 163, 658, 167, -811, -555, 113, 121], ![-121, -974, -545, 4228, 4156, -4545, -5641, -85, 1018, 113], ![-113, -1025, -1426, 3523, 7957, -703, -9969, -4963, 1384, 1018], ![-1018, -8257, -5097, 35222, 37117, -35817, -49567, -3861, 8271, 1384], ![-1384, -12090, -13793, 44727, 80894, -22395, -102249, -41263, 14131, 8271], ![-8271, -67552, -45174, 283963, 317670, -274759, -419403, -52623, 66260, 14131]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-13, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-13, 0, -1], [-6, -13, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-13, 0, -1], [-6, -13, 0, -1], [-121, -6, -13, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-13, 0, -1], [-6, -13, 0, -1], [-121, -6, -13, 0, -1], [-113, -121, -6, -13, 0, -1]], ![[], [], [], [-1], [0, -1], [-13, 0, -1], [-6, -13, 0, -1], [-121, -6, -13, 0, -1], [-113, -121, -6, -13, 0, -1], [-1018, -113, -121, -6, -13, 0, -1]], ![[], [], [-1], [0, -1], [-13, 0, -1], [-6, -13, 0, -1], [-121, -6, -13, 0, -1], [-113, -121, -6, -13, 0, -1], [-1018, -113, -121, -6, -13, 0, -1], [-1384, -1018, -113, -121, -6, -13, 0, -1]], ![[], [-1], [0, -1], [-13, 0, -1], [-6, -13, 0, -1], [-121, -6, -13, 0, -1], [-113, -121, -6, -13, 0, -1], [-1018, -113, -121, -6, -13, 0, -1], [-1384, -1018, -113, -121, -6, -13, 0, -1], [-8271, -1384, -1018, -113, -121, -6, -13, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -4, 36, 33, -43, -48, 6, 13, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -4, 36, 33, -43, -48, 6, 13, 0], [0, -1, -8, -4, 36, 33, -43, -48, 6, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -4, 36, 33, -43, -48, 6, 13, 0], [0, -1, -8, -4, 36, 33, -43, -48, 6, 13], [-13, -104, -53, 460, 425, -523, -591, 35, 121, 6]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -4, 36, 33, -43, -48, 6, 13, 0], [0, -1, -8, -4, 36, 33, -43, -48, 6, 13], [-13, -104, -53, 460, 425, -523, -591, 35, 121, 6], [-6, -61, -128, 163, 658, 167, -811, -555, 113, 121]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -4, 36, 33, -43, -48, 6, 13, 0], [0, -1, -8, -4, 36, 33, -43, -48, 6, 13], [-13, -104, -53, 460, 425, -523, -591, 35, 121, 6], [-6, -61, -128, 163, 658, 167, -811, -555, 113, 121], [-121, -974, -545, 4228, 4156, -4545, -5641, -85, 1018, 113]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -4, 36, 33, -43, -48, 6, 13, 0], [0, -1, -8, -4, 36, 33, -43, -48, 6, 13], [-13, -104, -53, 460, 425, -523, -591, 35, 121, 6], [-6, -61, -128, 163, 658, 167, -811, -555, 113, 121], [-121, -974, -545, 4228, 4156, -4545, -5641, -85, 1018, 113], [-113, -1025, -1426, 3523, 7957, -703, -9969, -4963, 1384, 1018]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -4, 36, 33, -43, -48, 6, 13, 0], [0, -1, -8, -4, 36, 33, -43, -48, 6, 13], [-13, -104, -53, 460, 425, -523, -591, 35, 121, 6], [-6, -61, -128, 163, 658, 167, -811, -555, 113, 121], [-121, -974, -545, 4228, 4156, -4545, -5641, -85, 1018, 113], [-113, -1025, -1426, 3523, 7957, -703, -9969, -4963, 1384, 1018], [-1018, -8257, -5097, 35222, 37117, -35817, -49567, -3861, 8271, 1384]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -4, 36, 33, -43, -48, 6, 13, 0], [0, -1, -8, -4, 36, 33, -43, -48, 6, 13], [-13, -104, -53, 460, 425, -523, -591, 35, 121, 6], [-6, -61, -128, 163, 658, 167, -811, -555, 113, 121], [-121, -974, -545, 4228, 4156, -4545, -5641, -85, 1018, 113], [-113, -1025, -1426, 3523, 7957, -703, -9969, -4963, 1384, 1018], [-1018, -8257, -5097, 35222, 37117, -35817, -49567, -3861, 8271, 1384], [-1384, -12090, -13793, 44727, 80894, -22395, -102249, -41263, 14131, 8271]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -8, -4, 36, 33, -43, -48, 6, 13, 0], [0, -1, -8, -4, 36, 33, -43, -48, 6, 13], [-13, -104, -53, 460, 425, -523, -591, 35, 121, 6], [-6, -61, -128, 163, 658, 167, -811, -555, 113, 121], [-121, -974, -545, 4228, 4156, -4545, -5641, -85, 1018, 113], [-113, -1025, -1426, 3523, 7957, -703, -9969, -4963, 1384, 1018], [-1018, -8257, -5097, 35222, 37117, -35817, -49567, -3861, 8271, 1384], [-1384, -12090, -13793, 44727, 80894, -22395, -102249, -41263, 14131, 8271], [-8271, -67552, -45174, 283963, 317670, -274759, -419403, -52623, 66260, 14131]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp13 : Fact (Nat.Prime 13) := fact_iff.2 (by norm_num)
instance hp23 : Fact (Nat.Prime 23) := fact_iff.2 (by norm_num)
instance hp1063 : Fact (Nat.Prime 1063) := fact_iff.2 (by norm_num)
instance hp870407 : Fact (Nat.Prime 870407) := fact_iff.2 (by norm_num)

def CD13 : CertificateDedekindCriterionLists l 13 where
  n := 2
  a' := [4, 2, 3, 7, 9, 1, 5, 11]
  b' := [8, 12, 7, 5, 1, 6, 12, 7, 6]
  k := [4, 9, 10, 3, 9, 1, 4, 1, 1]
  f := [5, 3, 2, 4, 5, -2, 2, 6, 5, 1]
  g := [11, 6, 4, 2, 5, 2, 12, 10, 7, 1]
  h := [6, 1]
  a := [12, 7, 6, 12, 9, 6, 6, 6, 5]
  b := [10, 7, 7, 11, 7, 12, 8, 4, 8]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD23 : CertificateDedekindCriterionLists l 23 where
  n := 2
  a' := [14, 5, 12, 14, 6, 10, 16]
  b' := [14, 13, 8, 9, 16, 7, 5, 21]
  k := [8, 20, 12, 6, 8, 19, 1]
  f := [3, 6, 7, 9, 7, 5, 2, 8, 3, 1]
  g := [10, 18, 17, 17, 11, 17, 7, 21, 1]
  h := [7, 2, 1]
  a := [16, 17, 7, 3, 1, 15, 12, 17]
  b := [16, 14, 0, 5, 15, 15, 14, 18, 6]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1063 : CertificateDedekindCriterionLists l 1063 where
  n := 2
  a' := [256, 978, 127, 400, 26, 966, 959, 1038]
  b' := [392, 936, 994, 106, 90, 463, 565, 218, 239]
  k := [955, 820, 197, 163, 251, 621, 548, 785, 1]
  f := [122, 18, 74, 70, 136, 62, 34, 23, 121, 1]
  g := [933, 131, 565, 531, 1036, 467, 257, 174, 924, 1]
  h := [139, 1]
  a := [753, 7, 628, 918, 622, 944, 412, 943, 395]
  b := [584, 176, 709, 14, 933, 275, 868, 531, 668]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD870407 : CertificateDedekindCriterionLists l 870407 where
  n := 2
  a' := [576752, 339249, 688829, 267178, 209086, 115866, 522434, 578089]
  b' := [606651, 568827, 112392, 737350, 176297, 766764, 225253, 828926, 709463]
  k := [330971, 316729, 718164, 24935, 862418, 775036, 137263, 658655, 1]
  f := [20701, 19473, 61318, 96314, 26418, 10172, 54342, 76149, 92998, 1]
  g := [170183, 160086, 504094, 791793, 217175, 83622, 446745, 626017, 764531, 1]
  h := [105876, 1]
  a := [483413, 728170, 475850, 374170, 689068, 618072, 59223, 27873, 113322]
  b := [313536, 518624, 21483, 585267, 639786, 29626, 860450, 621150, 757085]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![13, 23, 1063, 870407]
  exp := ![1, 1, 1, 1]
  pdgood := [13, 23, 1063, 870407]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp13.out
    exact hp23.out
    exact hp1063.out
    exact hp870407.out
  a := [-16749938681677, 11388146387496, 209291390657576, -62895294668108, -376547210852580, -27694017289806, 138250834345408, 8645076839500, -13868681512120]
  b := [2128323278917, 13198097104323, -13640333717798, -55566297357068, 19462868644937, 64283005540672, 2520759035069, -17430940627692, -864507683950, 1386868151212]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 13 T_ofList CD13
    exact satisfiesDedekindCriterion_of_certificate_lists T l 23 T_ofList CD23
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1063 T_ofList CD1063
    exact satisfiesDedekindCriterion_of_certificate_lists T l 870407 T_ofList CD870407

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

end VoightMaximalOrderD10R594

namespace VoightMaximalOrderD10R601

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨6376506153125, [-1, -8, 3, 35, -4, -48, 9, 24, -7, -3, 1], 1⟩
local notation "l" => [-1, -8, 3, 35, -4, -48, 9, 24, -7, -3, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, -3, -35, 4, 48, -9, -24, 7, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, -3, -35, 4, 48, -9, -24, 7, 3], ![3, 25, -1, -108, -23, 148, 21, -81, -3, 16]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, -3, -35, 4, 48, -9, -24, 7, 3], ![3, 25, -1, -108, -23, 148, 21, -81, -3, 16], ![16, 131, -23, -561, -44, 745, 4, -363, 31, 45]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, -3, -35, 4, 48, -9, -24, 7, 3], ![3, 25, -1, -108, -23, 148, 21, -81, -3, 16], ![16, 131, -23, -561, -44, 745, 4, -363, 31, 45], ![45, 376, -4, -1598, -381, 2116, 340, -1076, -48, 166]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, -3, -35, 4, 48, -9, -24, 7, 3], ![3, 25, -1, -108, -23, 148, 21, -81, -3, 16], ![16, 131, -23, -561, -44, 745, 4, -363, 31, 45], ![45, 376, -4, -1598, -381, 2116, 340, -1076, -48, 166], ![166, 1373, -122, -5814, -934, 7587, 622, -3644, 86, 450]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, -3, -35, 4, 48, -9, -24, 7, 3], ![3, 25, -1, -108, -23, 148, 21, -81, -3, 16], ![16, 131, -23, -561, -44, 745, 4, -363, 31, 45], ![45, 376, -4, -1598, -381, 2116, 340, -1076, -48, 166], ![166, 1373, -122, -5814, -934, 7587, 622, -3644, 86, 450], ![450, 3766, 23, -15872, -4014, 20666, 3537, -10178, -494, 1436]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, -3, -35, 4, 48, -9, -24, 7, 3], ![3, 25, -1, -108, -23, 148, 21, -81, -3, 16], ![16, 131, -23, -561, -44, 745, 4, -363, 31, 45], ![45, 376, -4, -1598, -381, 2116, 340, -1076, -48, 166], ![166, 1373, -122, -5814, -934, 7587, 622, -3644, 86, 450], ![450, 3766, 23, -15872, -4014, 20666, 3537, -10178, -494, 1436], ![1436, 11938, -542, -50237, -10128, 64914, 7742, -30927, -126, 3814]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, -3, -35, 4, 48, -9, -24, 7, 3], ![3, 25, -1, -108, -23, 148, 21, -81, -3, 16], ![16, 131, -23, -561, -44, 745, 4, -363, 31, 45], ![45, 376, -4, -1598, -381, 2116, 340, -1076, -48, 166], ![166, 1373, -122, -5814, -934, 7587, 622, -3644, 86, 450], ![450, 3766, 23, -15872, -4014, 20666, 3537, -10178, -494, 1436], ![1436, 11938, -542, -50237, -10128, 64914, 7742, -30927, -126, 3814], ![3814, 31948, 496, -134032, -34981, 172944, 30588, -83794, -4229, 11316]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 8, -3, -35, 4, 48, -9, -24, 7, 3], ![3, 25, -1, -108, -23, 148, 21, -81, -3, 16], ![16, 131, -23, -561, -44, 745, 4, -363, 31, 45], ![45, 376, -4, -1598, -381, 2116, 340, -1076, -48, 166], ![166, 1373, -122, -5814, -934, 7587, 622, -3644, 86, 450], ![450, 3766, 23, -15872, -4014, 20666, 3537, -10178, -494, 1436], ![1436, 11938, -542, -50237, -10128, 64914, 7742, -30927, -126, 3814], ![3814, 31948, 496, -134032, -34981, 172944, 30588, -83794, -4229, 11316], ![11316, 94342, -2000, -395564, -88768, 508187, 71100, -240996, -4582, 29719]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-166, -45, -16, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-166, -45, -16, -3, -1], [-450, -166, -45, -16, -3, -1]], ![[], [], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-166, -45, -16, -3, -1], [-450, -166, -45, -16, -3, -1], [-1436, -450, -166, -45, -16, -3, -1]], ![[], [], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-166, -45, -16, -3, -1], [-450, -166, -45, -16, -3, -1], [-1436, -450, -166, -45, -16, -3, -1], [-3814, -1436, -450, -166, -45, -16, -3, -1]], ![[], [-1], [-3, -1], [-16, -3, -1], [-45, -16, -3, -1], [-166, -45, -16, -3, -1], [-450, -166, -45, -16, -3, -1], [-1436, -450, -166, -45, -16, -3, -1], [-3814, -1436, -450, -166, -45, -16, -3, -1], [-11316, -3814, -1436, -450, -166, -45, -16, -3, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, -3, -35, 4, 48, -9, -24, 7, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, -3, -35, 4, 48, -9, -24, 7, 3], [3, 25, -1, -108, -23, 148, 21, -81, -3, 16]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, -3, -35, 4, 48, -9, -24, 7, 3], [3, 25, -1, -108, -23, 148, 21, -81, -3, 16], [16, 131, -23, -561, -44, 745, 4, -363, 31, 45]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, -3, -35, 4, 48, -9, -24, 7, 3], [3, 25, -1, -108, -23, 148, 21, -81, -3, 16], [16, 131, -23, -561, -44, 745, 4, -363, 31, 45], [45, 376, -4, -1598, -381, 2116, 340, -1076, -48, 166]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, -3, -35, 4, 48, -9, -24, 7, 3], [3, 25, -1, -108, -23, 148, 21, -81, -3, 16], [16, 131, -23, -561, -44, 745, 4, -363, 31, 45], [45, 376, -4, -1598, -381, 2116, 340, -1076, -48, 166], [166, 1373, -122, -5814, -934, 7587, 622, -3644, 86, 450]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, -3, -35, 4, 48, -9, -24, 7, 3], [3, 25, -1, -108, -23, 148, 21, -81, -3, 16], [16, 131, -23, -561, -44, 745, 4, -363, 31, 45], [45, 376, -4, -1598, -381, 2116, 340, -1076, -48, 166], [166, 1373, -122, -5814, -934, 7587, 622, -3644, 86, 450], [450, 3766, 23, -15872, -4014, 20666, 3537, -10178, -494, 1436]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, -3, -35, 4, 48, -9, -24, 7, 3], [3, 25, -1, -108, -23, 148, 21, -81, -3, 16], [16, 131, -23, -561, -44, 745, 4, -363, 31, 45], [45, 376, -4, -1598, -381, 2116, 340, -1076, -48, 166], [166, 1373, -122, -5814, -934, 7587, 622, -3644, 86, 450], [450, 3766, 23, -15872, -4014, 20666, 3537, -10178, -494, 1436], [1436, 11938, -542, -50237, -10128, 64914, 7742, -30927, -126, 3814]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, -3, -35, 4, 48, -9, -24, 7, 3], [3, 25, -1, -108, -23, 148, 21, -81, -3, 16], [16, 131, -23, -561, -44, 745, 4, -363, 31, 45], [45, 376, -4, -1598, -381, 2116, 340, -1076, -48, 166], [166, 1373, -122, -5814, -934, 7587, 622, -3644, 86, 450], [450, 3766, 23, -15872, -4014, 20666, 3537, -10178, -494, 1436], [1436, 11938, -542, -50237, -10128, 64914, 7742, -30927, -126, 3814], [3814, 31948, 496, -134032, -34981, 172944, 30588, -83794, -4229, 11316]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 8, -3, -35, 4, 48, -9, -24, 7, 3], [3, 25, -1, -108, -23, 148, 21, -81, -3, 16], [16, 131, -23, -561, -44, 745, 4, -363, 31, 45], [45, 376, -4, -1598, -381, 2116, 340, -1076, -48, 166], [166, 1373, -122, -5814, -934, 7587, 622, -3644, 86, 450], [450, 3766, 23, -15872, -4014, 20666, 3537, -10178, -494, 1436], [1436, 11938, -542, -50237, -10128, 64914, 7742, -30927, -126, 3814], [3814, 31948, 496, -134032, -34981, 172944, 30588, -83794, -4229, 11316], [11316, 94342, -2000, -395564, -88768, 508187, 71100, -240996, -4582, 29719]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp31 : Fact (Nat.Prime 31) := fact_iff.2 (by norm_num)
instance hp9811 : Fact (Nat.Prime 9811) := fact_iff.2 (by norm_num)
instance hp6709 : Fact (Nat.Prime 6709) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [3, 3, 4]
  b' := [0, 0, 0, 4, 4]
  k := [1]
  f := [1, 4, 2, -5, 3, 12, 0, -4, 2, 1]
  g := [2, 3, 1, 1, 1, 1]
  h := [2, 3, 1, 1, 1, 1]
  a := [1, 3, 2, 1, 4]
  b := [0, 4, 1, 4, 4, 0, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD31 : CertificateDedekindCriterionLists l 31 where
  n := 2
  a' := [6, 29, 30, 30, 10, 7, 17, 28]
  b' := [0, 5, 26, 30, 5, 29, 6, 12, 21]
  k := [6, 19, 14, 12, 19, 15, 3, 9, 1]
  f := [21, 14, 23, 3, 18, 20, 23, 9, 3, 1]
  g := [26, 16, 28, 4, 22, 22, 28, 11, 3, 1]
  h := [25, 1]
  a := [19, 22, 7, 7, 0, 4, 8, 11, 11]
  b := [30, 6, 6, 9, 4, 7, 14, 20, 20]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD9811 : CertificateDedekindCriterionLists l 9811 where
  n := 2
  a' := [8801, 4575, 2288, 4031, 1106, 7449, 1839, 3179]
  b' := [5137, 8686, 6270, 4472, 5258, 9464, 7862, 6305, 1827]
  k := [7384, 5758, 1266, 6817, 1587, 8706, 8366, 8541, 1]
  f := [4363, 3041, 1845, 4461, 3701, 1726, 461, 4699, 2411, 1]
  g := [7728, 5385, 3267, 7901, 6554, 3056, 816, 8323, 4269, 1]
  h := [5539, 1]
  a := [8409, 876, 7545, 3672, 313, 508, 2583, 7160, 6158]
  b := [1943, 4943, 2620, 9569, 8459, 7576, 710, 4589, 3653]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD6709 : CertificateDedekindCriterionLists l 6709 where
  n := 2
  a' := [2974, 1617, 339, 242, 392, 3880, 4848, 2019]
  b' := [922, 5855, 322, 3532, 2250, 6201, 3773, 378, 2012]
  k := [1240, 3209, 5965, 5629, 2184, 6237, 4441, 4226, 1]
  f := [229, 363, 1200, 344, 620, 109, 922, 916, 1011, 1]
  g := [1239, 1963, 6491, 1856, 3353, 587, 4988, 4952, 5466, 1]
  h := [1240, 1]
  a := [3121, 2136, 1641, 2833, 1499, 2496, 4363, 5286, 4864]
  b := [5856, 1840, 33, 2510, 6406, 1510, 3390, 473, 1845]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 4
  p := ![5, 31, 9811, 6709]
  exp := ![1, 1, 1, 1]
  pdgood := [5, 31, 9811, 6709]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp31.out
    exact hp9811.out
    exact hp6709.out
  a := [1107502539627, -2425430360856, -11134516301905, 18094853637018, 7934508791244, -18952681725990, 3212313211447, 3393088617216, -999775663180]
  b := [-139713118684, -909108583533, 1716992230577, 2443567074255, -4049310888096, -994618162538, 2696820181203, -440389084191, -369302131617, 99977566318]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 31 T_ofList CD31
    exact satisfiesDedekindCriterion_of_certificate_lists T l 9811 T_ofList CD9811
    exact satisfiesDedekindCriterion_of_certificate_lists T l 6709 T_ofList CD6709

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

end VoightMaximalOrderD10R601

end TraceEuclidean
