import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk202
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

namespace VoightMaximalOrderD10R403

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨4974535312384, [1, 0, -17, 22, 30, -44, -11, 26, -3, -4, 1], 1⟩
local notation "l" => [1, 0, -17, 22, 30, -44, -11, 26, -3, -4, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 17, -22, -30, 44, 11, -26, 3, 4]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 17, -22, -30, 44, 11, -26, 3, 4], ![-4, -1, 68, -71, -142, 146, 88, -93, -14, 19]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 17, -22, -30, 44, 11, -26, 3, 4], ![-4, -1, 68, -71, -142, 146, 88, -93, -14, 19], ![-19, -4, 322, -350, -641, 694, 355, -406, -36, 62]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 17, -22, -30, 44, 11, -26, 3, 4], ![-4, -1, 68, -71, -142, 146, 88, -93, -14, 19], ![-19, -4, 322, -350, -641, 694, 355, -406, -36, 62], ![-62, -19, 1050, -1042, -2210, 2087, 1376, -1257, -220, 212]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 17, -22, -30, 44, 11, -26, 3, 4], ![-4, -1, 68, -71, -142, 146, 88, -93, -14, 19], ![-19, -4, 322, -350, -641, 694, 355, -406, -36, 62], ![-62, -19, 1050, -1042, -2210, 2087, 1376, -1257, -220, 212], ![-212, -62, 3585, -3614, -7402, 7118, 4419, -4136, -621, 628]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 17, -22, -30, 44, 11, -26, 3, 4], ![-4, -1, 68, -71, -142, 146, 88, -93, -14, 19], ![-19, -4, 322, -350, -641, 694, 355, -406, -36, 62], ![-62, -19, 1050, -1042, -2210, 2087, 1376, -1257, -220, 212], ![-212, -62, 3585, -3614, -7402, 7118, 4419, -4136, -621, 628], ![-628, -212, 10614, -10231, -22454, 20230, 14026, -11909, -2252, 1891]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 17, -22, -30, 44, 11, -26, 3, 4], ![-4, -1, 68, -71, -142, 146, 88, -93, -14, 19], ![-19, -4, 322, -350, -641, 694, 355, -406, -36, 62], ![-62, -19, 1050, -1042, -2210, 2087, 1376, -1257, -220, 212], ![-212, -62, 3585, -3614, -7402, 7118, 4419, -4136, -621, 628], ![-628, -212, 10614, -10231, -22454, 20230, 14026, -11909, -2252, 1891], ![-1891, -628, 31935, -30988, -66961, 60750, 41031, -35140, -6236, 5312]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 17, -22, -30, 44, 11, -26, 3, 4], ![-4, -1, 68, -71, -142, 146, 88, -93, -14, 19], ![-19, -4, 322, -350, -641, 694, 355, -406, -36, 62], ![-62, -19, 1050, -1042, -2210, 2087, 1376, -1257, -220, 212], ![-212, -62, 3585, -3614, -7402, 7118, 4419, -4136, -621, 628], ![-628, -212, 10614, -10231, -22454, 20230, 14026, -11909, -2252, 1891], ![-1891, -628, 31935, -30988, -66961, 60750, 41031, -35140, -6236, 5312], ![-5312, -1891, 89676, -84929, -190348, 166767, 119182, -97081, -19204, 15012]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 0, 17, -22, -30, 44, 11, -26, 3, 4], ![-4, -1, 68, -71, -142, 146, 88, -93, -14, 19], ![-19, -4, 322, -350, -641, 694, 355, -406, -36, 62], ![-62, -19, 1050, -1042, -2210, 2087, 1376, -1257, -220, 212], ![-212, -62, 3585, -3614, -7402, 7118, 4419, -4136, -621, 628], ![-628, -212, 10614, -10231, -22454, 20230, 14026, -11909, -2252, 1891], ![-1891, -628, 31935, -30988, -66961, 60750, 41031, -35140, -6236, 5312], ![-5312, -1891, 89676, -84929, -190348, 166767, 119182, -97081, -19204, 15012], ![-15012, -5312, 253313, -240588, -535289, 470180, 331899, -271130, -52045, 40844]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-4, -1]], ![[], [], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1]], ![[], [], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1]], ![[], [], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-212, -62, -19, -4, -1]], ![[], [], [], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-212, -62, -19, -4, -1], [-628, -212, -62, -19, -4, -1]], ![[], [], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-212, -62, -19, -4, -1], [-628, -212, -62, -19, -4, -1], [-1891, -628, -212, -62, -19, -4, -1]], ![[], [], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-212, -62, -19, -4, -1], [-628, -212, -62, -19, -4, -1], [-1891, -628, -212, -62, -19, -4, -1], [-5312, -1891, -628, -212, -62, -19, -4, -1]], ![[], [-1], [-4, -1], [-19, -4, -1], [-62, -19, -4, -1], [-212, -62, -19, -4, -1], [-628, -212, -62, -19, -4, -1], [-1891, -628, -212, -62, -19, -4, -1], [-5312, -1891, -628, -212, -62, -19, -4, -1], [-15012, -5312, -1891, -628, -212, -62, -19, -4, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 17, -22, -30, 44, 11, -26, 3, 4]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 17, -22, -30, 44, 11, -26, 3, 4], [-4, -1, 68, -71, -142, 146, 88, -93, -14, 19]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 17, -22, -30, 44, 11, -26, 3, 4], [-4, -1, 68, -71, -142, 146, 88, -93, -14, 19], [-19, -4, 322, -350, -641, 694, 355, -406, -36, 62]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 17, -22, -30, 44, 11, -26, 3, 4], [-4, -1, 68, -71, -142, 146, 88, -93, -14, 19], [-19, -4, 322, -350, -641, 694, 355, -406, -36, 62], [-62, -19, 1050, -1042, -2210, 2087, 1376, -1257, -220, 212]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 17, -22, -30, 44, 11, -26, 3, 4], [-4, -1, 68, -71, -142, 146, 88, -93, -14, 19], [-19, -4, 322, -350, -641, 694, 355, -406, -36, 62], [-62, -19, 1050, -1042, -2210, 2087, 1376, -1257, -220, 212], [-212, -62, 3585, -3614, -7402, 7118, 4419, -4136, -621, 628]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 17, -22, -30, 44, 11, -26, 3, 4], [-4, -1, 68, -71, -142, 146, 88, -93, -14, 19], [-19, -4, 322, -350, -641, 694, 355, -406, -36, 62], [-62, -19, 1050, -1042, -2210, 2087, 1376, -1257, -220, 212], [-212, -62, 3585, -3614, -7402, 7118, 4419, -4136, -621, 628], [-628, -212, 10614, -10231, -22454, 20230, 14026, -11909, -2252, 1891]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 17, -22, -30, 44, 11, -26, 3, 4], [-4, -1, 68, -71, -142, 146, 88, -93, -14, 19], [-19, -4, 322, -350, -641, 694, 355, -406, -36, 62], [-62, -19, 1050, -1042, -2210, 2087, 1376, -1257, -220, 212], [-212, -62, 3585, -3614, -7402, 7118, 4419, -4136, -621, 628], [-628, -212, 10614, -10231, -22454, 20230, 14026, -11909, -2252, 1891], [-1891, -628, 31935, -30988, -66961, 60750, 41031, -35140, -6236, 5312]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 17, -22, -30, 44, 11, -26, 3, 4], [-4, -1, 68, -71, -142, 146, 88, -93, -14, 19], [-19, -4, 322, -350, -641, 694, 355, -406, -36, 62], [-62, -19, 1050, -1042, -2210, 2087, 1376, -1257, -220, 212], [-212, -62, 3585, -3614, -7402, 7118, 4419, -4136, -621, 628], [-628, -212, 10614, -10231, -22454, 20230, 14026, -11909, -2252, 1891], [-1891, -628, 31935, -30988, -66961, 60750, 41031, -35140, -6236, 5312], [-5312, -1891, 89676, -84929, -190348, 166767, 119182, -97081, -19204, 15012]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 0, 17, -22, -30, 44, 11, -26, 3, 4], [-4, -1, 68, -71, -142, 146, 88, -93, -14, 19], [-19, -4, 322, -350, -641, 694, 355, -406, -36, 62], [-62, -19, 1050, -1042, -2210, 2087, 1376, -1257, -220, 212], [-212, -62, 3585, -3614, -7402, 7118, 4419, -4136, -621, 628], [-628, -212, 10614, -10231, -22454, 20230, 14026, -11909, -2252, 1891], [-1891, -628, 31935, -30988, -66961, 60750, 41031, -35140, -6236, 5312], [-5312, -1891, 89676, -84929, -190348, 166767, 119182, -97081, -19204, 15012], [-15012, -5312, 253313, -240588, -535289, 470180, 331899, -271130, -52045, 40844]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp441631331 : Fact (Nat.Prime 441631331) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 2
  a' := [1, 0, 1]
  b' := [0, 1, 1, 1]
  k := [1]
  f := [0, 1, 9, -10, -13, 24, 7, -12, 3, 3]
  g := [1, 1, 0, 1, 1, 1]
  h := [1, 1, 0, 1, 1, 1]
  a := [0, 0, 0, 0, 1]
  b := [1, 1, 1, 0, 0, 0, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 2
  a' := [5, 10, 3, 3, 1, 2, 6, 3]
  b' := [6, 0, 2, 9, 7, 2, 8, 0, 7]
  k := [5, 4, 1, 5, 6, 4, 4, 1, 1]
  f := [1, 2, 4, 0, -2, 6, 3, 0, 2, 1]
  g := [4, 6, 7, 5, 1, 7, 5, 7, 4, 1]
  h := [3, 1]
  a := [9, 6, 6, 5, 9, 8, 8, 10, 10]
  b := [9, 8, 0, 3, 10, 6, 2, 10, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD441631331 : CertificateDedekindCriterionLists l 441631331 where
  n := 2
  a' := [269819526, 114435637, 233820913, 256945780, 252452568, 287821735, 15841405, 408990930]
  b' := [399352644, 154140502, 122397986, 51642971, 318301214, 190372628, 187039361, 182519786, 101767007]
  k := [249569147, 382786252, 43705629, 367576690, 157125280, 71787587, 346980417, 236528569, 1]
  f := [36198112, 44598833, 58048279, 82419303, 75951548, 18584573, 50895025, 58608811, 78737884, 1]
  g := [155884987, 192062184, 249981412, 354933757, 327080759, 80033340, 219176356, 252395309, 339079948, 1]
  h := [102551379, 1]
  a := [322254051, 395898211, 390635767, 193546265, 7823912, 410946467, 66599147, 56982436, 235962524]
  b := [240013869, 23624034, 191173680, 440790234, 262630770, 86746452, 77898417, 213230042, 205668807]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![2, 11, 441631331]
  exp := ![1, 1, 1]
  pdgood := [2, 11, 441631331]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp11.out
    exact hp441631331.out
  a := [9715889282, -1574782099720, -473876748270, 4535645032812, -213378766976, -3492624576030, 829887083028, 670331575694, -215019510490]
  b := [-46317120580, -108705200716, 552590958100, 208968885721, -929997210894, 2353496711, 508368599037, -100039425415, -75633937989, 21501951049]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 441631331 T_ofList CD441631331

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

end VoightMaximalOrderD10R403

namespace VoightMaximalOrderD10R409

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5020731190625, [1, -5, -6, 50, -27, -48, 33, 14, -11, -1, 1], 1⟩
local notation "l" => [1, -5, -6, 50, -27, -48, 33, 14, -11, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -50, 27, 48, -33, -14, 11, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -50, 27, 48, -33, -14, 11, 1], ![-1, 4, 11, -44, -23, 75, 15, -47, -3, 12]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -50, 27, 48, -33, -14, 11, 1], ![-1, 4, 11, -44, -23, 75, 15, -47, -3, 12], ![-12, 59, 76, -589, 280, 553, -321, -153, 85, 9]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -50, 27, 48, -33, -14, 11, 1], ![-1, 4, 11, -44, -23, 75, 15, -47, -3, 12], ![-12, 59, 76, -589, 280, 553, -321, -153, 85, 9], ![-9, 33, 113, -374, -346, 712, 256, -447, -54, 94]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -50, 27, 48, -33, -14, 11, 1], ![-1, 4, 11, -44, -23, 75, 15, -47, -3, 12], ![-12, 59, 76, -589, 280, 553, -321, -153, 85, 9], ![-9, 33, 113, -374, -346, 712, 256, -447, -54, 94], ![-94, 461, 597, -4587, 2164, 4166, -2390, -1060, 587, 40]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -50, 27, 48, -33, -14, 11, 1], ![-1, 4, 11, -44, -23, 75, 15, -47, -3, 12], ![-12, 59, 76, -589, 280, 553, -321, -153, 85, 9], ![-9, 33, 113, -374, -346, 712, 256, -447, -54, 94], ![-94, 461, 597, -4587, 2164, 4166, -2390, -1060, 587, 40], ![-40, 106, 701, -1403, -3507, 4084, 2846, -2950, -620, 627]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -50, 27, 48, -33, -14, 11, 1], ![-1, 4, 11, -44, -23, 75, 15, -47, -3, 12], ![-12, 59, 76, -589, 280, 553, -321, -153, 85, 9], ![-9, 33, 113, -374, -346, 712, 256, -447, -54, 94], ![-94, 461, 597, -4587, 2164, 4166, -2390, -1060, 587, 40], ![-40, 106, 701, -1403, -3507, 4084, 2846, -2950, -620, 627], ![-627, 3095, 3868, -30649, 15526, 26589, -16607, -5932, 3947, 7]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -50, 27, 48, -33, -14, 11, 1], ![-1, 4, 11, -44, -23, 75, 15, -47, -3, 12], ![-12, 59, 76, -589, 280, 553, -321, -153, 85, 9], ![-9, 33, 113, -374, -346, 712, 256, -447, -54, 94], ![-94, 461, 597, -4587, 2164, 4166, -2390, -1060, 587, 40], ![-40, 106, 701, -1403, -3507, 4084, 2846, -2950, -620, 627], ![-627, 3095, 3868, -30649, 15526, 26589, -16607, -5932, 3947, 7], ![-7, -592, 3137, 3518, -30460, 15862, 26358, -16705, -5855, 3954]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 5, 6, -50, 27, 48, -33, -14, 11, 1], ![-1, 4, 11, -44, -23, 75, 15, -47, -3, 12], ![-12, 59, 76, -589, 280, 553, -321, -153, 85, 9], ![-9, 33, 113, -374, -346, 712, 256, -447, -54, 94], ![-94, 461, 597, -4587, 2164, 4166, -2390, -1060, 587, 40], ![-40, 106, 701, -1403, -3507, 4084, 2846, -2950, -620, 627], ![-627, 3095, 3868, -30649, 15526, 26589, -16607, -5932, 3947, 7], ![-7, -592, 3137, 3518, -30460, 15862, 26358, -16705, -5855, 3954], ![-3954, 19763, 23132, -194563, 110276, 159332, -114620, -28998, 26789, -1901]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1], [-94, -9, -12, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1], [-94, -9, -12, -1, -1], [-40, -94, -9, -12, -1, -1]], ![[], [], [], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1], [-94, -9, -12, -1, -1], [-40, -94, -9, -12, -1, -1], [-627, -40, -94, -9, -12, -1, -1]], ![[], [], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1], [-94, -9, -12, -1, -1], [-40, -94, -9, -12, -1, -1], [-627, -40, -94, -9, -12, -1, -1], [-7, -627, -40, -94, -9, -12, -1, -1]], ![[], [-1], [-1, -1], [-12, -1, -1], [-9, -12, -1, -1], [-94, -9, -12, -1, -1], [-40, -94, -9, -12, -1, -1], [-627, -40, -94, -9, -12, -1, -1], [-7, -627, -40, -94, -9, -12, -1, -1], [-3954, -7, -627, -40, -94, -9, -12, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -50, 27, 48, -33, -14, 11, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -50, 27, 48, -33, -14, 11, 1], [-1, 4, 11, -44, -23, 75, 15, -47, -3, 12]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -50, 27, 48, -33, -14, 11, 1], [-1, 4, 11, -44, -23, 75, 15, -47, -3, 12], [-12, 59, 76, -589, 280, 553, -321, -153, 85, 9]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -50, 27, 48, -33, -14, 11, 1], [-1, 4, 11, -44, -23, 75, 15, -47, -3, 12], [-12, 59, 76, -589, 280, 553, -321, -153, 85, 9], [-9, 33, 113, -374, -346, 712, 256, -447, -54, 94]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -50, 27, 48, -33, -14, 11, 1], [-1, 4, 11, -44, -23, 75, 15, -47, -3, 12], [-12, 59, 76, -589, 280, 553, -321, -153, 85, 9], [-9, 33, 113, -374, -346, 712, 256, -447, -54, 94], [-94, 461, 597, -4587, 2164, 4166, -2390, -1060, 587, 40]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -50, 27, 48, -33, -14, 11, 1], [-1, 4, 11, -44, -23, 75, 15, -47, -3, 12], [-12, 59, 76, -589, 280, 553, -321, -153, 85, 9], [-9, 33, 113, -374, -346, 712, 256, -447, -54, 94], [-94, 461, 597, -4587, 2164, 4166, -2390, -1060, 587, 40], [-40, 106, 701, -1403, -3507, 4084, 2846, -2950, -620, 627]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -50, 27, 48, -33, -14, 11, 1], [-1, 4, 11, -44, -23, 75, 15, -47, -3, 12], [-12, 59, 76, -589, 280, 553, -321, -153, 85, 9], [-9, 33, 113, -374, -346, 712, 256, -447, -54, 94], [-94, 461, 597, -4587, 2164, 4166, -2390, -1060, 587, 40], [-40, 106, 701, -1403, -3507, 4084, 2846, -2950, -620, 627], [-627, 3095, 3868, -30649, 15526, 26589, -16607, -5932, 3947, 7]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -50, 27, 48, -33, -14, 11, 1], [-1, 4, 11, -44, -23, 75, 15, -47, -3, 12], [-12, 59, 76, -589, 280, 553, -321, -153, 85, 9], [-9, 33, 113, -374, -346, 712, 256, -447, -54, 94], [-94, 461, 597, -4587, 2164, 4166, -2390, -1060, 587, 40], [-40, 106, 701, -1403, -3507, 4084, 2846, -2950, -620, 627], [-627, 3095, 3868, -30649, 15526, 26589, -16607, -5932, 3947, 7], [-7, -592, 3137, 3518, -30460, 15862, 26358, -16705, -5855, 3954]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 5, 6, -50, 27, 48, -33, -14, 11, 1], [-1, 4, 11, -44, -23, 75, 15, -47, -3, 12], [-12, 59, 76, -589, 280, 553, -321, -153, 85, 9], [-9, 33, 113, -374, -346, 712, 256, -447, -54, 94], [-94, 461, 597, -4587, 2164, 4166, -2390, -1060, 587, 40], [-40, 106, 701, -1403, -3507, 4084, 2846, -2950, -620, 627], [-627, 3095, 3868, -30649, 15526, 26589, -16607, -5932, 3947, 7], [-7, -592, 3137, 3518, -30460, 15862, 26358, -16705, -5855, 3954], [-3954, 19763, 23132, -194563, 110276, 159332, -114620, -28998, 26789, -1901]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp79 : Fact (Nat.Prime 79) := fact_iff.2 (by norm_num)
instance hp20337139 : Fact (Nat.Prime 20337139) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 3, 4]
  b' := [3, 1, 0, 3, 2]
  k := [1]
  f := [0, 1, 2, -10, 7, 10, -5, -2, 3, 1]
  g := [1, 0, 2, 0, 2, 1]
  h := [1, 0, 2, 0, 2, 1]
  a := [0, 0, 1, 2, 4]
  b := [1, 0, 3, 4, 3, 3, 3, 4, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD79 : CertificateDedekindCriterionLists l 79 where
  n := 2
  a' := [21, 40, 23, 55, 0, 22, 73, 62]
  b' := [4, 27, 50, 18, 57, 50, 71, 68, 37]
  k := [42, 51, 22, 27, 34, 52, 78, 6, 1]
  f := [5, 28, 25, 21, 31, 6, 7, 26, 20, 1]
  g := [11, 61, 53, 46, 66, 10, 16, 57, 42, 1]
  h := [36, 1]
  a := [33, 60, 24, 11, 68, 25, 24, 41, 7]
  b := [21, 38, 24, 20, 15, 72, 78, 34, 72]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD20337139 : CertificateDedekindCriterionLists l 20337139 where
  n := 2
  a' := [6683566, 7928965, 3620644, 4417770, 19097606, 17707306, 339338, 16370138]
  b' := [12682736, 12470144, 4878842, 20067886, 9243787, 1767836, 19045307, 10399950, 2700460]
  k := [1240909, 2856900, 12910870, 13079791, 12175676, 14858103, 15691689, 11326801, 1]
  f := [12864695, 8149870, 4725093, 5960493, 8218467, 7598250, 1814460, 12194371, 4086281, 1]
  g := [17829887, 11295351, 6548765, 8260974, 11390424, 10530831, 2514759, 16900848, 5663400, 1]
  h := [14673738, 1]
  a := [9402186, 6657018, 14734361, 20043944, 4963037, 16055350, 3042244, 6804272, 17251708]
  b := [11327241, 9862143, 9863402, 2021321, 13737800, 15961672, 1872309, 9265247, 3085431]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 79, 20337139]
  exp := ![1, 1, 1]
  pdgood := [5, 79, 20337139]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp79.out
    exact hp20337139.out
  a := [-1081177898770, -6454000599490, 9748569154707, 10917441462358, -13484845165113, -4440982550310, 5544957902611, 375053949278, -618602656920]
  b := [-217842213735, 313199091836, 2414183676499, -2324735382389, -2318137734245, 2227315118835, 663317262948, -692405259203, -43691421497, 61860265692]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 79 T_ofList CD79
    exact satisfiesDedekindCriterion_of_certificate_lists T l 20337139 T_ofList CD20337139

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

end VoightMaximalOrderD10R409

namespace VoightMaximalOrderD10R414

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5053539628125, [-1, 3, 13, -18, -41, 18, 38, -3, -11, 0, 1], 1⟩
local notation "l" => [-1, 3, 13, -18, -41, 18, 38, -3, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -13, 18, 41, -18, -38, 3, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -13, 18, 41, -18, -38, 3, 11, 0], ![0, 1, -3, -13, 18, 41, -18, -38, 3, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -13, 18, 41, -18, -38, 3, 11, 0], ![0, 1, -3, -13, 18, 41, -18, -38, 3, 11], ![11, -33, -142, 195, 438, -180, -377, 15, 83, 3]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -13, 18, 41, -18, -38, 3, 11, 0], ![0, 1, -3, -13, 18, 41, -18, -38, 3, 11], ![11, -33, -142, 195, 438, -180, -377, 15, 83, 3], ![3, 2, -72, -88, 318, 384, -294, -368, 48, 83]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -13, 18, 41, -18, -38, 3, 11, 0], ![0, 1, -3, -13, 18, 41, -18, -38, 3, 11], ![11, -33, -142, 195, 438, -180, -377, 15, 83, 3], ![3, 2, -72, -88, 318, 384, -294, -368, 48, 83], ![83, -246, -1077, 1422, 3315, -1176, -2770, -45, 545, 48]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -13, 18, 41, -18, -38, 3, 11, 0], ![0, 1, -3, -13, 18, 41, -18, -38, 3, 11], ![11, -33, -142, 195, 438, -180, -377, 15, 83, 3], ![3, 2, -72, -88, 318, 384, -294, -368, 48, 83], ![83, -246, -1077, 1422, 3315, -1176, -2770, -45, 545, 48], ![48, -61, -870, -213, 3390, 2451, -3000, -2626, 483, 545]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -13, 18, 41, -18, -38, 3, 11, 0], ![0, 1, -3, -13, 18, 41, -18, -38, 3, 11], ![11, -33, -142, 195, 438, -180, -377, 15, 83, 3], ![3, 2, -72, -88, 318, 384, -294, -368, 48, 83], ![83, -246, -1077, 1422, 3315, -1176, -2770, -45, 545, 48], ![48, -61, -870, -213, 3390, 2451, -3000, -2626, 483, 545], ![545, -1587, -7146, 8940, 22132, -6420, -18259, -1365, 3369, 483]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -13, 18, 41, -18, -38, 3, 11, 0], ![0, 1, -3, -13, 18, 41, -18, -38, 3, 11], ![11, -33, -142, 195, 438, -180, -377, 15, 83, 3], ![3, 2, -72, -88, 318, 384, -294, -368, 48, 83], ![83, -246, -1077, 1422, 3315, -1176, -2770, -45, 545, 48], ![48, -61, -870, -213, 3390, 2451, -3000, -2626, 483, 545], ![545, -1587, -7146, 8940, 22132, -6420, -18259, -1365, 3369, 483], ![483, -904, -7866, 1548, 28743, 13438, -24774, -16810, 3948, 3369]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -3, -13, 18, 41, -18, -38, 3, 11, 0], ![0, 1, -3, -13, 18, 41, -18, -38, 3, 11], ![11, -33, -142, 195, 438, -180, -377, 15, 83, 3], ![3, 2, -72, -88, 318, 384, -294, -368, 48, 83], ![83, -246, -1077, 1422, 3315, -1176, -2770, -45, 545, 48], ![48, -61, -870, -213, 3390, 2451, -3000, -2626, 483, 545], ![545, -1587, -7146, 8940, 22132, -6420, -18259, -1365, 3369, 483], ![483, -904, -7866, 1548, 28743, 13438, -24774, -16810, 3948, 3369], ![3369, -9624, -44701, 52776, 139677, -31899, -114584, -14667, 20249, 3948]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-83, -3, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-83, -3, -11, 0, -1], [-48, -83, -3, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-83, -3, -11, 0, -1], [-48, -83, -3, -11, 0, -1], [-545, -48, -83, -3, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-83, -3, -11, 0, -1], [-48, -83, -3, -11, 0, -1], [-545, -48, -83, -3, -11, 0, -1], [-483, -545, -48, -83, -3, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-83, -3, -11, 0, -1], [-48, -83, -3, -11, 0, -1], [-545, -48, -83, -3, -11, 0, -1], [-483, -545, -48, -83, -3, -11, 0, -1], [-3369, -483, -545, -48, -83, -3, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -13, 18, 41, -18, -38, 3, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -13, 18, 41, -18, -38, 3, 11, 0], [0, 1, -3, -13, 18, 41, -18, -38, 3, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -13, 18, 41, -18, -38, 3, 11, 0], [0, 1, -3, -13, 18, 41, -18, -38, 3, 11], [11, -33, -142, 195, 438, -180, -377, 15, 83, 3]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -13, 18, 41, -18, -38, 3, 11, 0], [0, 1, -3, -13, 18, 41, -18, -38, 3, 11], [11, -33, -142, 195, 438, -180, -377, 15, 83, 3], [3, 2, -72, -88, 318, 384, -294, -368, 48, 83]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -13, 18, 41, -18, -38, 3, 11, 0], [0, 1, -3, -13, 18, 41, -18, -38, 3, 11], [11, -33, -142, 195, 438, -180, -377, 15, 83, 3], [3, 2, -72, -88, 318, 384, -294, -368, 48, 83], [83, -246, -1077, 1422, 3315, -1176, -2770, -45, 545, 48]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -13, 18, 41, -18, -38, 3, 11, 0], [0, 1, -3, -13, 18, 41, -18, -38, 3, 11], [11, -33, -142, 195, 438, -180, -377, 15, 83, 3], [3, 2, -72, -88, 318, 384, -294, -368, 48, 83], [83, -246, -1077, 1422, 3315, -1176, -2770, -45, 545, 48], [48, -61, -870, -213, 3390, 2451, -3000, -2626, 483, 545]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -13, 18, 41, -18, -38, 3, 11, 0], [0, 1, -3, -13, 18, 41, -18, -38, 3, 11], [11, -33, -142, 195, 438, -180, -377, 15, 83, 3], [3, 2, -72, -88, 318, 384, -294, -368, 48, 83], [83, -246, -1077, 1422, 3315, -1176, -2770, -45, 545, 48], [48, -61, -870, -213, 3390, 2451, -3000, -2626, 483, 545], [545, -1587, -7146, 8940, 22132, -6420, -18259, -1365, 3369, 483]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -13, 18, 41, -18, -38, 3, 11, 0], [0, 1, -3, -13, 18, 41, -18, -38, 3, 11], [11, -33, -142, 195, 438, -180, -377, 15, 83, 3], [3, 2, -72, -88, 318, 384, -294, -368, 48, 83], [83, -246, -1077, 1422, 3315, -1176, -2770, -45, 545, 48], [48, -61, -870, -213, 3390, 2451, -3000, -2626, 483, 545], [545, -1587, -7146, 8940, 22132, -6420, -18259, -1365, 3369, 483], [483, -904, -7866, 1548, 28743, 13438, -24774, -16810, 3948, 3369]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -3, -13, 18, 41, -18, -38, 3, 11, 0], [0, 1, -3, -13, 18, 41, -18, -38, 3, 11], [11, -33, -142, 195, 438, -180, -377, 15, 83, 3], [3, 2, -72, -88, 318, 384, -294, -368, 48, 83], [83, -246, -1077, 1422, 3315, -1176, -2770, -45, 545, 48], [48, -61, -870, -213, 3390, 2451, -3000, -2626, 483, 545], [545, -1587, -7146, 8940, 22132, -6420, -18259, -1365, 3369, 483], [483, -904, -7866, 1548, 28743, 13438, -24774, -16810, 3948, 3369], [3369, -9624, -44701, 52776, 139677, -31899, -114584, -14667, 20249, 3948]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp2218289 : Fact (Nat.Prime 2218289) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 3
  a' := [2]
  b' := [0, 1, 0, 2]
  k := [1, 0, 1, 0, 2, 0, 2, 0, 1]
  f := [1, -1, -3, 6, 15, -6, -11, 1, 5]
  g := [2, 0, 0, 0, 2, 0, 1]
  h := [1, 0, 2, 0, 1]
  a := [1, 1, 1, 0, 1]
  b := [0, 0, 0, 2, 1, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [2]
  b' := [1, 2, 4, 3]
  k := [1]
  f := [1, 1, -1, 6, 10, -2, -6, 1, 3]
  g := [2, 2, 1, 2, 0, 1]
  h := [2, 2, 1, 2, 0, 1]
  a := [2, 2, 3, 1, 3]
  b := [2, 1, 4, 4, 4, 1, 4, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2218289 : CertificateDedekindCriterionLists l 2218289 where
  n := 2
  a' := [1533557, 127229, 782525, 446176, 9254, 1887868, 1081999, 2171016]
  b' := [1585155, 552239, 1359431, 89915, 1871029, 2031705, 1226051, 854331, 1977065]
  k := [1075483, 490942, 60445, 478105, 1998708, 1751747, 749073, 35718, 1]
  f := [1104589, 20269, 1299880, 1979832, 39909, 2062066, 336976, 1714627, 17716, 1]
  g := [1113554, 20433, 1310430, 1995900, 40232, 2078802, 339710, 1728543, 17859, 1]
  h := [2200430, 1]
  a := [392352, 546871, 1172424, 548625, 19209, 602462, 719880, 822851, 429394]
  b := [641786, 1930011, 669565, 419944, 1487696, 1789496, 982339, 686688, 1788895]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![3, 5, 2218289]
  exp := ![1, 1, 1]
  pdgood := [3, 5, 2218289]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp5.out
    exact hp2218289.out
  a := [-25263705, 101538744, 667778920, -55349326, -1241540502, -182866248, 568814032, 50556940, -73766240]
  b := [2670210, 35968133, -33129755, -197289732, 11416059, 223156506, 22770190, -73109976, -5055694, 7376624]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2218289 T_ofList CD2218289

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

end VoightMaximalOrderD10R414

namespace VoightMaximalOrderD10R416

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨5060778940625, [-1, -12, -6, 68, -21, -65, 28, 21, -10, -2, 1], 1⟩
local notation "l" => [-1, -12, -6, 68, -21, -65, 28, 21, -10, -2, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 12, 6, -68, 21, 65, -28, -21, 10, 2]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 12, 6, -68, 21, 65, -28, -21, 10, 2], ![2, 25, 24, -130, -26, 151, 9, -70, -1, 14]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 12, 6, -68, 21, 65, -28, -21, 10, 2], ![2, 25, 24, -130, -26, 151, 9, -70, -1, 14], ![14, 170, 109, -928, 164, 884, -241, -285, 70, 27]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 12, 6, -68, 21, 65, -28, -21, 10, 2], ![2, 25, 24, -130, -26, 151, 9, -70, -1, 14], ![14, 170, 109, -928, 164, 884, -241, -285, 70, 27], ![27, 338, 332, -1727, -361, 1919, 128, -808, -15, 124]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 12, 6, -68, 21, 65, -28, -21, 10, 2], ![2, 25, 24, -130, -26, 151, 9, -70, -1, 14], ![14, 170, 109, -928, 164, 884, -241, -285, 70, 27], ![27, 338, 332, -1727, -361, 1919, 128, -808, -15, 124], ![124, 1515, 1082, -8100, 877, 7699, -1553, -2476, 432, 233]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 12, 6, -68, 21, 65, -28, -21, 10, 2], ![2, 25, 24, -130, -26, 151, 9, -70, -1, 14], ![14, 170, 109, -928, 164, 884, -241, -285, 70, 27], ![27, 338, 332, -1727, -361, 1919, 128, -808, -15, 124], ![124, 1515, 1082, -8100, 877, 7699, -1553, -2476, 432, 233], ![233, 2920, 2913, -14762, -3207, 16022, 1175, -6446, -146, 898]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 12, 6, -68, 21, 65, -28, -21, 10, 2], ![2, 25, 24, -130, -26, 151, 9, -70, -1, 14], ![14, 170, 109, -928, 164, 884, -241, -285, 70, 27], ![27, 338, 332, -1727, -361, 1919, 128, -808, -15, 124], ![124, 1515, 1082, -8100, 877, 7699, -1553, -2476, 432, 233], ![233, 2920, 2913, -14762, -3207, 16022, 1175, -6446, -146, 898], ![898, 11009, 8308, -58151, 4096, 55163, -9122, -17683, 2534, 1650]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 12, 6, -68, 21, 65, -28, -21, 10, 2], ![2, 25, 24, -130, -26, 151, 9, -70, -1, 14], ![14, 170, 109, -928, 164, 884, -241, -285, 70, 27], ![27, 338, 332, -1727, -361, 1919, 128, -808, -15, 124], ![124, 1515, 1082, -8100, 877, 7699, -1553, -2476, 432, 233], ![233, 2920, 2913, -14762, -3207, 16022, 1175, -6446, -146, 898], ![898, 11009, 8308, -58151, 4096, 55163, -9122, -17683, 2534, 1650], ![1650, 20698, 20909, -103892, -23501, 111346, 8963, -43772, -1183, 5834]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 12, 6, -68, 21, 65, -28, -21, 10, 2], ![2, 25, 24, -130, -26, 151, 9, -70, -1, 14], ![14, 170, 109, -928, 164, 884, -241, -285, 70, 27], ![27, 338, 332, -1727, -361, 1919, 128, -808, -15, 124], ![124, 1515, 1082, -8100, 877, 7699, -1553, -2476, 432, 233], ![233, 2920, 2913, -14762, -3207, 16022, 1175, -6446, -146, 898], ![898, 11009, 8308, -58151, 4096, 55163, -9122, -17683, 2534, 1650], ![1650, 20698, 20909, -103892, -23501, 111346, 8963, -43772, -1183, 5834], ![5834, 71658, 55702, -375803, 18622, 355709, -52006, -113551, 14568, 10485]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-2, -1]], ![[], [], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1]], ![[], [], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-27, -14, -2, -1]], ![[], [], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-27, -14, -2, -1], [-124, -27, -14, -2, -1]], ![[], [], [], [], [-1], [-2, -1], [-14, -2, -1], [-27, -14, -2, -1], [-124, -27, -14, -2, -1], [-233, -124, -27, -14, -2, -1]], ![[], [], [], [-1], [-2, -1], [-14, -2, -1], [-27, -14, -2, -1], [-124, -27, -14, -2, -1], [-233, -124, -27, -14, -2, -1], [-898, -233, -124, -27, -14, -2, -1]], ![[], [], [-1], [-2, -1], [-14, -2, -1], [-27, -14, -2, -1], [-124, -27, -14, -2, -1], [-233, -124, -27, -14, -2, -1], [-898, -233, -124, -27, -14, -2, -1], [-1650, -898, -233, -124, -27, -14, -2, -1]], ![[], [-1], [-2, -1], [-14, -2, -1], [-27, -14, -2, -1], [-124, -27, -14, -2, -1], [-233, -124, -27, -14, -2, -1], [-898, -233, -124, -27, -14, -2, -1], [-1650, -898, -233, -124, -27, -14, -2, -1], [-5834, -1650, -898, -233, -124, -27, -14, -2, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 12, 6, -68, 21, 65, -28, -21, 10, 2]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 12, 6, -68, 21, 65, -28, -21, 10, 2], [2, 25, 24, -130, -26, 151, 9, -70, -1, 14]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 12, 6, -68, 21, 65, -28, -21, 10, 2], [2, 25, 24, -130, -26, 151, 9, -70, -1, 14], [14, 170, 109, -928, 164, 884, -241, -285, 70, 27]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 12, 6, -68, 21, 65, -28, -21, 10, 2], [2, 25, 24, -130, -26, 151, 9, -70, -1, 14], [14, 170, 109, -928, 164, 884, -241, -285, 70, 27], [27, 338, 332, -1727, -361, 1919, 128, -808, -15, 124]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 12, 6, -68, 21, 65, -28, -21, 10, 2], [2, 25, 24, -130, -26, 151, 9, -70, -1, 14], [14, 170, 109, -928, 164, 884, -241, -285, 70, 27], [27, 338, 332, -1727, -361, 1919, 128, -808, -15, 124], [124, 1515, 1082, -8100, 877, 7699, -1553, -2476, 432, 233]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 12, 6, -68, 21, 65, -28, -21, 10, 2], [2, 25, 24, -130, -26, 151, 9, -70, -1, 14], [14, 170, 109, -928, 164, 884, -241, -285, 70, 27], [27, 338, 332, -1727, -361, 1919, 128, -808, -15, 124], [124, 1515, 1082, -8100, 877, 7699, -1553, -2476, 432, 233], [233, 2920, 2913, -14762, -3207, 16022, 1175, -6446, -146, 898]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 12, 6, -68, 21, 65, -28, -21, 10, 2], [2, 25, 24, -130, -26, 151, 9, -70, -1, 14], [14, 170, 109, -928, 164, 884, -241, -285, 70, 27], [27, 338, 332, -1727, -361, 1919, 128, -808, -15, 124], [124, 1515, 1082, -8100, 877, 7699, -1553, -2476, 432, 233], [233, 2920, 2913, -14762, -3207, 16022, 1175, -6446, -146, 898], [898, 11009, 8308, -58151, 4096, 55163, -9122, -17683, 2534, 1650]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 12, 6, -68, 21, 65, -28, -21, 10, 2], [2, 25, 24, -130, -26, 151, 9, -70, -1, 14], [14, 170, 109, -928, 164, 884, -241, -285, 70, 27], [27, 338, 332, -1727, -361, 1919, 128, -808, -15, 124], [124, 1515, 1082, -8100, 877, 7699, -1553, -2476, 432, 233], [233, 2920, 2913, -14762, -3207, 16022, 1175, -6446, -146, 898], [898, 11009, 8308, -58151, 4096, 55163, -9122, -17683, 2534, 1650], [1650, 20698, 20909, -103892, -23501, 111346, 8963, -43772, -1183, 5834]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 12, 6, -68, 21, 65, -28, -21, 10, 2], [2, 25, 24, -130, -26, 151, 9, -70, -1, 14], [14, 170, 109, -928, 164, 884, -241, -285, 70, 27], [27, 338, 332, -1727, -361, 1919, 128, -808, -15, 124], [124, 1515, 1082, -8100, 877, 7699, -1553, -2476, 432, 233], [233, 2920, 2913, -14762, -3207, 16022, 1175, -6446, -146, 898], [898, 11009, 8308, -58151, 4096, 55163, -9122, -17683, 2534, 1650], [1650, 20698, 20909, -103892, -23501, 111346, 8963, -43772, -1183, 5834], [5834, 71658, 55702, -375803, 18622, 355709, -52006, -113551, 14568, 10485]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp5 : Fact (Nat.Prime 5) := fact_iff.2 (by norm_num)
instance hp17159 : Fact (Nat.Prime 17159) := fact_iff.2 (by norm_num)
instance hp94379 : Fact (Nat.Prime 94379) := fact_iff.2 (by norm_num)

def CD5 : CertificateDedekindCriterionLists l 5 where
  n := 2
  a' := [1, 4, 4]
  b' := [2, 0, 1, 4, 1]
  k := [1]
  f := [1, 4, 2, -12, 9, 17, -4, -1, 6, 2]
  g := [2, 2, 0, 2, 4, 1]
  h := [2, 2, 0, 2, 4, 1]
  a := [3, 4, 0, 4, 4]
  b := [4, 3, 1, 2, 0, 3, 1, 0, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD17159 : CertificateDedekindCriterionLists l 17159 where
  n := 2
  a' := [3499, 14577, 13410, 2402, 3620, 7033, 5345, 5582]
  b' := [10799, 2433, 7240, 8119, 1223, 15397, 2061, 7398, 7006]
  k := [13597, 10077, 7045, 3025, 16770, 14067, 10047, 1928, 1]
  f := [5219, 1214, 6244, 4672, 861, 14047, 12786, 2548, 909, 1]
  g := [5530, 1286, 6616, 4950, 912, 14884, 13547, 2699, 963, 1]
  h := [16194, 1]
  a := [13894, 16512, 8915, 3318, 10795, 15364, 13246, 14154, 10245]
  b := [10609, 5125, 7685, 14081, 13203, 7935, 8060, 7147, 6914]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD94379 : CertificateDedekindCriterionLists l 94379 where
  n := 2
  a' := [9461, 18787, 43998, 81435, 55156, 64576, 88516, 31938]
  b' := [54081, 51284, 17494, 12128, 91609, 86496, 45598, 40044, 27911]
  k := [34835, 19411, 5386, 54426, 81826, 14844, 14753, 36185, 1]
  f := [7115, 16449, 18907, 28801, 18211, 3135, 10001, 17193, 20126, 1]
  g := [23079, 53355, 61327, 93420, 59068, 10167, 32440, 55768, 65281, 1]
  h := [29096, 1]
  a := [40756, 52848, 89218, 13805, 93381, 15310, 45787, 52542, 68599]
  b := [93097, 24669, 74536, 32860, 5218, 76353, 38267, 16523, 25780]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![5, 17159, 94379]
  exp := ![1, 1, 1]
  pdgood := [5, 17159, 94379]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp5.out
    exact hp17159.out
    exact hp94379.out
  a := [51621292867, -23941984428, -779338617150, 985576463720, 605250866392, -1191641239004, 229253870156, 199378674992, -64191997840]
  b := [-4976544931, -44649582567, 23124541497, 254367266348, -286274792669, -64470260204, 173704046904, -34087125006, -21221707456, 6419199784]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
    exact satisfiesDedekindCriterion_of_certificate_lists T l 17159 T_ofList CD17159
    exact satisfiesDedekindCriterion_of_certificate_lists T l 94379 T_ofList CD94379

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

end VoightMaximalOrderD10R416

end TraceEuclidean
