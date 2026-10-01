import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk162
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

namespace VoightMaximalOrderD9R10

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨19936446593, [-1, -2, 16, -1, -30, 7, 17, -5, -3, 1], 1⟩
local notation "l" => [-1, -2, 16, -1, -30, 7, 17, -5, -3, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsNine := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsNine_irreducible row row_mem
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
def basisNumerator : Fin 9 → Fin 9 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 9 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -16, 1, 30, -7, -17, 5, 3]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -16, 1, 30, -7, -17, 5, 3], ![3, 7, -46, -13, 91, 9, -58, -2, 14]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -16, 1, 30, -7, -17, 5, 3], ![3, 7, -46, -13, 91, 9, -58, -2, 14], ![14, 31, -217, -32, 407, -7, -229, 12, 40]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -16, 1, 30, -7, -17, 5, 3], ![3, 7, -46, -13, 91, 9, -58, -2, 14], ![14, 31, -217, -32, 407, -7, -229, 12, 40], ![40, 94, -609, -177, 1168, 127, -687, -29, 132]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -16, 1, 30, -7, -17, 5, 3], ![3, 7, -46, -13, 91, 9, -58, -2, 14], ![14, 31, -217, -32, 407, -7, -229, 12, 40], ![40, 94, -609, -177, 1168, 127, -687, -29, 132], ![132, 304, -2018, -477, 3783, 244, -2117, -27, 367]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -16, 1, 30, -7, -17, 5, 3], ![3, 7, -46, -13, 91, 9, -58, -2, 14], ![14, 31, -217, -32, 407, -7, -229, 12, 40], ![40, 94, -609, -177, 1168, 127, -687, -29, 132], ![132, 304, -2018, -477, 3783, 244, -2117, -27, 367], ![367, 866, -5568, -1651, 10533, 1214, -5995, -282, 1074]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -16, 1, 30, -7, -17, 5, 3], ![3, 7, -46, -13, 91, 9, -58, -2, 14], ![14, 31, -217, -32, 407, -7, -229, 12, 40], ![40, 94, -609, -177, 1168, 127, -687, -29, 132], ![132, 304, -2018, -477, 3783, 244, -2117, -27, 367], ![367, 866, -5568, -1651, 10533, 1214, -5995, -282, 1074], ![1074, 2515, -16318, -4494, 30569, 3015, -17044, -625, 2940]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 2, -16, 1, 30, -7, -17, 5, 3], ![3, 7, -46, -13, 91, 9, -58, -2, 14], ![14, 31, -217, -32, 407, -7, -229, 12, 40], ![40, 94, -609, -177, 1168, 127, -687, -29, 132], ![132, 304, -2018, -477, 3783, 244, -2117, -27, 367], ![367, 866, -5568, -1651, 10533, 1214, -5995, -282, 1074], ![1074, 2515, -16318, -4494, 30569, 3015, -17044, -625, 2940], ![2940, 6954, -44525, -13378, 83706, 9989, -46965, -2344, 8195]]]
  s := ![![[], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [], [], [-1], [-3, -1], [-14, -3, -1]], ![[], [], [], [], [], [-1], [-3, -1], [-14, -3, -1], [-40, -14, -3, -1]], ![[], [], [], [], [-1], [-3, -1], [-14, -3, -1], [-40, -14, -3, -1], [-132, -40, -14, -3, -1]], ![[], [], [], [-1], [-3, -1], [-14, -3, -1], [-40, -14, -3, -1], [-132, -40, -14, -3, -1], [-367, -132, -40, -14, -3, -1]], ![[], [], [-1], [-3, -1], [-14, -3, -1], [-40, -14, -3, -1], [-132, -40, -14, -3, -1], [-367, -132, -40, -14, -3, -1], [-1074, -367, -132, -40, -14, -3, -1]], ![[], [-1], [-3, -1], [-14, -3, -1], [-40, -14, -3, -1], [-132, -40, -14, -3, -1], [-367, -132, -40, -14, -3, -1], [-1074, -367, -132, -40, -14, -3, -1], [-2940, -1074, -367, -132, -40, -14, -3, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 9 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 9) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 9) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 9) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 9 → Fin 9 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -16, 1, 30, -7, -17, 5, 3]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -16, 1, 30, -7, -17, 5, 3], [3, 7, -46, -13, 91, 9, -58, -2, 14]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -16, 1, 30, -7, -17, 5, 3], [3, 7, -46, -13, 91, 9, -58, -2, 14], [14, 31, -217, -32, 407, -7, -229, 12, 40]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -16, 1, 30, -7, -17, 5, 3], [3, 7, -46, -13, 91, 9, -58, -2, 14], [14, 31, -217, -32, 407, -7, -229, 12, 40], [40, 94, -609, -177, 1168, 127, -687, -29, 132]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -16, 1, 30, -7, -17, 5, 3], [3, 7, -46, -13, 91, 9, -58, -2, 14], [14, 31, -217, -32, 407, -7, -229, 12, 40], [40, 94, -609, -177, 1168, 127, -687, -29, 132], [132, 304, -2018, -477, 3783, 244, -2117, -27, 367]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -16, 1, 30, -7, -17, 5, 3], [3, 7, -46, -13, 91, 9, -58, -2, 14], [14, 31, -217, -32, 407, -7, -229, 12, 40], [40, 94, -609, -177, 1168, 127, -687, -29, 132], [132, 304, -2018, -477, 3783, 244, -2117, -27, 367], [367, 866, -5568, -1651, 10533, 1214, -5995, -282, 1074]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -16, 1, 30, -7, -17, 5, 3], [3, 7, -46, -13, 91, 9, -58, -2, 14], [14, 31, -217, -32, 407, -7, -229, 12, 40], [40, 94, -609, -177, 1168, 127, -687, -29, 132], [132, 304, -2018, -477, 3783, 244, -2117, -27, 367], [367, 866, -5568, -1651, 10533, 1214, -5995, -282, 1074], [1074, 2515, -16318, -4494, 30569, 3015, -17044, -625, 2940]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1], [1, 2, -16, 1, 30, -7, -17, 5, 3], [3, 7, -46, -13, 91, 9, -58, -2, 14], [14, 31, -217, -32, 407, -7, -229, 12, 40], [40, 94, -609, -177, 1168, 127, -687, -29, 132], [132, 304, -2018, -477, 3783, 244, -2117, -27, 367], [367, 866, -5568, -1651, 10533, 1214, -5995, -282, 1074], [1074, 2515, -16318, -4494, 30569, 3015, -17044, -625, 2940], [2940, 6954, -44525, -13378, 83706, 9989, -46965, -2344, 8195]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp169457 : Fact (Nat.Prime 169457) := fact_iff.2 (by norm_num)

def CD7 : CertificateDedekindCriterionLists l 7 where
  n := 3
  a' := [3, 4]
  b' := [3, 1, 1]
  k := [1]
  f := [1, 3, 3, 7, 12, 5, 4, 6, 2]
  g := [3, 2, 6, 1]
  h := [2, 5, 5, 2, 5, 5, 1]
  a := [6, 5, 3]
  b := [3, 2, 4, 3, 2, 1, 1, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD169457 : CertificateDedekindCriterionLists l 169457 where
  n := 2
  a' := [123807, 28798, 74460, 57087, 153381, 25874, 108640]
  b' := [164843, 15699, 15647, 85636, 103325, 161107, 69871, 155877]
  k := [5073, 72980, 110905, 132751, 92992, 108383, 136331, 1]
  f := [30213, 57394, 99489, 27942, 14995, 62627, 14611, 40744, 1]
  g := [50546, 96019, 166443, 46745, 25086, 104774, 24443, 68164, 1]
  h := [101290, 1]
  a := [32947, 142769, 135291, 41074, 133823, 78657, 26187, 39256]
  b := [110150, 28568, 130447, 89552, 46532, 112667, 151926, 130201]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![7, 169457]
  exp := ![1, 1]
  pdgood := [7, 169457]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp7.out
    exact hp169457.out
  a := [-1379807, 3468424, 11063678, -8265938, -12683449, 6389136, 3777705, -1644192]
  b := [96804, 1194459, -1072581, -3254638, 1641173, 2309475, -935365, -480641, 182688]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T l 169457 T_ofList CD169457

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

noncomputable def bOm : Basis (Fin 9) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 9 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 9
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 9 := T_degree

noncomputable def bQ : Basis (Fin 9) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 9) (Fin 9) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 9) :
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
          (∑ x : Fin 9,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 9,
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
        (List.ofFn fun i : Fin 9 =>
          (List.ofFn fun j : Fin 9 =>
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
      (voightPolynomialDiscriminantInput 9 row row_mem)
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

end VoightMaximalOrderD9R10

namespace VoightMaximalOrderD9R13

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨22384826361, [-1, 6, 0, -22, 3, 24, -1, -9, 0, 1], 1⟩
local notation "l" => [-1, 6, 0, -22, 3, 24, -1, -9, 0, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsNine := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsNine_irreducible row row_mem
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
def basisNumerator : Fin 9 → Fin 9 → ℤ := ![![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 9 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, 0, 22, -3, -24, 1, 9, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, 0, 22, -3, -24, 1, 9, 0], ![0, 1, -6, 0, 22, -3, -24, 1, 9]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, 0, 22, -3, -24, 1, 9, 0], ![0, 1, -6, 0, 22, -3, -24, 1, 9], ![9, -54, 1, 192, -27, -194, 6, 57, 1]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, 0, 22, -3, -24, 1, 9, 0], ![0, 1, -6, 0, 22, -3, -24, 1, 9], ![9, -54, 1, 192, -27, -194, 6, 57, 1], ![1, 3, -54, 23, 189, -51, -193, 15, 57]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, 0, 22, -3, -24, 1, 9, 0], ![0, 1, -6, 0, 22, -3, -24, 1, 9], ![9, -54, 1, 192, -27, -194, 6, 57, 1], ![1, 3, -54, 23, 189, -51, -193, 15, 57], ![57, -341, 3, 1200, -148, -1179, 6, 320, 15]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, 0, 22, -3, -24, 1, 9, 0], ![0, 1, -6, 0, 22, -3, -24, 1, 9], ![9, -54, 1, 192, -27, -194, 6, 57, 1], ![1, 3, -54, 23, 189, -51, -193, 15, 57], ![57, -341, 3, 1200, -148, -1179, 6, 320, 15], ![15, -33, -341, 333, 1155, -508, -1164, 141, 320]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, 0, 22, -3, -24, 1, 9, 0], ![0, 1, -6, 0, 22, -3, -24, 1, 9], ![9, -54, 1, 192, -27, -194, 6, 57, 1], ![1, 3, -54, 23, 189, -51, -193, 15, 57], ![57, -341, 3, 1200, -148, -1179, 6, 320, 15], ![15, -33, -341, 333, 1155, -508, -1164, 141, 320], ![320, -1905, -33, 6699, -627, -6525, -188, 1716, 141]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1], ![1, -6, 0, 22, -3, -24, 1, 9, 0], ![0, 1, -6, 0, 22, -3, -24, 1, 9], ![9, -54, 1, 192, -27, -194, 6, 57, 1], ![1, 3, -54, 23, 189, -51, -193, 15, 57], ![57, -341, 3, 1200, -148, -1179, 6, 320, 15], ![15, -33, -341, 333, 1155, -508, -1164, 141, 320], ![320, -1905, -33, 6699, -627, -6525, -188, 1716, 141], ![141, -526, -1905, 3069, 6276, -4011, -6384, 1081, 1716]]]
  s := ![![[], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-9, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-9, 0, -1], [-1, -9, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-9, 0, -1], [-1, -9, 0, -1], [-57, -1, -9, 0, -1]], ![[], [], [], [-1], [0, -1], [-9, 0, -1], [-1, -9, 0, -1], [-57, -1, -9, 0, -1], [-15, -57, -1, -9, 0, -1]], ![[], [], [-1], [0, -1], [-9, 0, -1], [-1, -9, 0, -1], [-57, -1, -9, 0, -1], [-15, -57, -1, -9, 0, -1], [-320, -15, -57, -1, -9, 0, -1]], ![[], [-1], [0, -1], [-9, 0, -1], [-1, -9, 0, -1], [-57, -1, -9, 0, -1], [-15, -57, -1, -9, 0, -1], [-320, -15, -57, -1, -9, 0, -1], [-141, -320, -15, -57, -1, -9, 0, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 9 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 9) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 9) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 9) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 9 → Fin 9 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, 0, 22, -3, -24, 1, 9, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, 0, 22, -3, -24, 1, 9, 0], [0, 1, -6, 0, 22, -3, -24, 1, 9]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, 0, 22, -3, -24, 1, 9, 0], [0, 1, -6, 0, 22, -3, -24, 1, 9], [9, -54, 1, 192, -27, -194, 6, 57, 1]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, 0, 22, -3, -24, 1, 9, 0], [0, 1, -6, 0, 22, -3, -24, 1, 9], [9, -54, 1, 192, -27, -194, 6, 57, 1], [1, 3, -54, 23, 189, -51, -193, 15, 57]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, 0, 22, -3, -24, 1, 9, 0], [0, 1, -6, 0, 22, -3, -24, 1, 9], [9, -54, 1, 192, -27, -194, 6, 57, 1], [1, 3, -54, 23, 189, -51, -193, 15, 57], [57, -341, 3, 1200, -148, -1179, 6, 320, 15]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, 0, 22, -3, -24, 1, 9, 0], [0, 1, -6, 0, 22, -3, -24, 1, 9], [9, -54, 1, 192, -27, -194, 6, 57, 1], [1, 3, -54, 23, 189, -51, -193, 15, 57], [57, -341, 3, 1200, -148, -1179, 6, 320, 15], [15, -33, -341, 333, 1155, -508, -1164, 141, 320]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, 0, 22, -3, -24, 1, 9, 0], [0, 1, -6, 0, 22, -3, -24, 1, 9], [9, -54, 1, 192, -27, -194, 6, 57, 1], [1, 3, -54, 23, 189, -51, -193, 15, 57], [57, -341, 3, 1200, -148, -1179, 6, 320, 15], [15, -33, -341, 333, 1155, -508, -1164, 141, 320], [320, -1905, -33, 6699, -627, -6525, -188, 1716, 141]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1], [1, -6, 0, 22, -3, -24, 1, 9, 0], [0, 1, -6, 0, 22, -3, -24, 1, 9], [9, -54, 1, 192, -27, -194, 6, 57, 1], [1, 3, -54, 23, 189, -51, -193, 15, 57], [57, -341, 3, 1200, -148, -1179, 6, 320, 15], [15, -33, -341, 333, 1155, -508, -1164, 141, 320], [320, -1905, -33, 6699, -627, -6525, -188, 1716, 141], [141, -526, -1905, 3069, 6276, -4011, -6384, 1081, 1716]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp73 : Fact (Nat.Prime 73) := fact_iff.2 (by norm_num)
instance hp577 : Fact (Nat.Prime 577) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 3
  a' := [1]
  b' := [1, 0, 2]
  k := [1]
  f := [1, 0, 2, 9, 1, -6, 3, 5, 1]
  g := [2, 2, 2, 1]
  h := [1, 2, 0, 0, 2, 1, 1]
  a := [1, 1, 1]
  b := [0, 1, 2, 2, 0, 1, 2, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD73 : CertificateDedekindCriterionLists l 73 where
  n := 2
  a' := [5, 36, 16, 54, 50, 24, 10]
  b' := [54, 46, 21, 4, 25, 14, 12, 17]
  k := [4, 55, 62, 36, 71, 45, 27, 1]
  f := [6, 9, 7, 5, 20, 4, 3, 16, 1]
  g := [19, 28, 21, 14, 63, 11, 9, 50, 1]
  h := [23, 1]
  a := [50, 47, 40, 11, 69, 7, 8, 9]
  b := [15, 70, 69, 49, 20, 57, 6, 64]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD577 : CertificateDedekindCriterionLists l 577 where
  n := 2
  a' := [242, 89, 529, 1, 440, 480, 292]
  b' := [433, 517, 223, 64, 533, 327, 104, 252]
  k := [128, 210, 372, 46, 576, 293, 102, 1]
  f := [361, 348, 255, 305, 89, 53, 259, 47, 1]
  g := [396, 381, 279, 334, 97, 58, 284, 51, 1]
  h := [526, 1]
  a := [120, 21, 235, 210, 415, 186, 435, 511]
  b := [64, 334, 549, 328, 446, 97, 455, 66]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![3, 73, 577]
  exp := ![2, 1, 1]
  pdgood := [3, 73, 577]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp73.out
    exact hp577.out
  a := [-202005, 3897204, 7793106, -19876128, -11921019, 17088732, 2761749, -3057066]
  b := [29514, 851539, -2273699, -2538578, 4975995, 1825055, -2578096, -306861, 339674]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 73 T_ofList CD73
    exact satisfiesDedekindCriterion_of_certificate_lists T l 577 T_ofList CD577

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

noncomputable def bOm : Basis (Fin 9) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 9 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 9
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 9 := T_degree

noncomputable def bQ : Basis (Fin 9) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 9) (Fin 9) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 9) :
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
          (∑ x : Fin 9,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 9,
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
        (List.ofFn fun i : Fin 9 =>
          (List.ofFn fun j : Fin 9 =>
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
      (voightPolynomialDiscriminantInput 9 row row_mem)
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

end VoightMaximalOrderD9R13

namespace VoightMaximalOrderD10R1

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨443952558373, [1, 12, 20, -22, -48, 14, 37, -3, -11, 0, 1], 1⟩
local notation "l" => [1, 12, 20, -22, -48, 14, 37, -3, -11, 0, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -20, 22, 48, -14, -37, 3, 11, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -20, 22, 48, -14, -37, 3, 11, 0], ![0, -1, -12, -20, 22, 48, -14, -37, 3, 11]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -20, 22, 48, -14, -37, 3, 11, 0], ![0, -1, -12, -20, 22, 48, -14, -37, 3, 11], ![-11, -132, -221, 230, 508, -132, -359, 19, 84, 3]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -20, 22, 48, -14, -37, 3, 11, 0], ![0, -1, -12, -20, 22, 48, -14, -37, 3, 11], ![-11, -132, -221, 230, 508, -132, -359, 19, 84, 3], ![-3, -47, -192, -155, 374, 466, -243, -350, 52, 84]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -20, 22, 48, -14, -37, 3, 11, 0], ![0, -1, -12, -20, 22, 48, -14, -37, 3, 11], ![-11, -132, -221, 230, 508, -132, -359, 19, 84, 3], ![-3, -47, -192, -155, 374, 466, -243, -350, 52, 84], ![-84, -1011, -1727, 1656, 3877, -802, -2642, 9, 574, 52]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -20, 22, 48, -14, -37, 3, 11, 0], ![0, -1, -12, -20, 22, 48, -14, -37, 3, 11], ![-11, -132, -221, 230, 508, -132, -359, 19, 84, 3], ![-3, -47, -192, -155, 374, 466, -243, -350, 52, 84], ![-84, -1011, -1727, 1656, 3877, -802, -2642, 9, 574, 52], ![-52, -708, -2051, -583, 4152, 3149, -2726, -2486, 581, 574]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -20, 22, 48, -14, -37, 3, 11, 0], ![0, -1, -12, -20, 22, 48, -14, -37, 3, 11], ![-11, -132, -221, 230, 508, -132, -359, 19, 84, 3], ![-3, -47, -192, -155, 374, 466, -243, -350, 52, 84], ![-84, -1011, -1727, 1656, 3877, -802, -2642, 9, 574, 52], ![-52, -708, -2051, -583, 4152, 3149, -2726, -2486, 581, 574], ![-574, -6940, -12188, 10577, 26969, -3884, -18089, -1004, 3828, 581]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -20, 22, 48, -14, -37, 3, 11, 0], ![0, -1, -12, -20, 22, 48, -14, -37, 3, 11], ![-11, -132, -221, 230, 508, -132, -359, 19, 84, 3], ![-3, -47, -192, -155, 374, 466, -243, -350, 52, 84], ![-84, -1011, -1727, 1656, 3877, -802, -2642, 9, 574, 52], ![-52, -708, -2051, -583, 4152, 3149, -2726, -2486, 581, 574], ![-574, -6940, -12188, 10577, 26969, -3884, -18089, -1004, 3828, 581], ![-581, -7546, -18560, 594, 38465, 18835, -25381, -16346, 5387, 3828]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, -12, -20, 22, 48, -14, -37, 3, 11, 0], ![0, -1, -12, -20, 22, 48, -14, -37, 3, 11], ![-11, -132, -221, 230, 508, -132, -359, 19, 84, 3], ![-3, -47, -192, -155, 374, 466, -243, -350, 52, 84], ![-84, -1011, -1727, 1656, 3877, -802, -2642, 9, 574, 52], ![-52, -708, -2051, -583, 4152, 3149, -2726, -2486, 581, 574], ![-574, -6940, -12188, 10577, 26969, -3884, -18089, -1004, 3828, 581], ![-581, -7546, -18560, 594, 38465, 18835, -25381, -16346, 5387, 3828], ![-3828, -46517, -84106, 65656, 184338, -15127, -122801, -13897, 25762, 5387]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1]], ![[], [], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1]], ![[], [], [], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-84, -3, -11, 0, -1]], ![[], [], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-84, -3, -11, 0, -1], [-52, -84, -3, -11, 0, -1]], ![[], [], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-84, -3, -11, 0, -1], [-52, -84, -3, -11, 0, -1], [-574, -52, -84, -3, -11, 0, -1]], ![[], [], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-84, -3, -11, 0, -1], [-52, -84, -3, -11, 0, -1], [-574, -52, -84, -3, -11, 0, -1], [-581, -574, -52, -84, -3, -11, 0, -1]], ![[], [-1], [0, -1], [-11, 0, -1], [-3, -11, 0, -1], [-84, -3, -11, 0, -1], [-52, -84, -3, -11, 0, -1], [-574, -52, -84, -3, -11, 0, -1], [-581, -574, -52, -84, -3, -11, 0, -1], [-3828, -581, -574, -52, -84, -3, -11, 0, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -20, 22, 48, -14, -37, 3, 11, 0]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -20, 22, 48, -14, -37, 3, 11, 0], [0, -1, -12, -20, 22, 48, -14, -37, 3, 11]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -20, 22, 48, -14, -37, 3, 11, 0], [0, -1, -12, -20, 22, 48, -14, -37, 3, 11], [-11, -132, -221, 230, 508, -132, -359, 19, 84, 3]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -20, 22, 48, -14, -37, 3, 11, 0], [0, -1, -12, -20, 22, 48, -14, -37, 3, 11], [-11, -132, -221, 230, 508, -132, -359, 19, 84, 3], [-3, -47, -192, -155, 374, 466, -243, -350, 52, 84]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -20, 22, 48, -14, -37, 3, 11, 0], [0, -1, -12, -20, 22, 48, -14, -37, 3, 11], [-11, -132, -221, 230, 508, -132, -359, 19, 84, 3], [-3, -47, -192, -155, 374, 466, -243, -350, 52, 84], [-84, -1011, -1727, 1656, 3877, -802, -2642, 9, 574, 52]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -20, 22, 48, -14, -37, 3, 11, 0], [0, -1, -12, -20, 22, 48, -14, -37, 3, 11], [-11, -132, -221, 230, 508, -132, -359, 19, 84, 3], [-3, -47, -192, -155, 374, 466, -243, -350, 52, 84], [-84, -1011, -1727, 1656, 3877, -802, -2642, 9, 574, 52], [-52, -708, -2051, -583, 4152, 3149, -2726, -2486, 581, 574]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -20, 22, 48, -14, -37, 3, 11, 0], [0, -1, -12, -20, 22, 48, -14, -37, 3, 11], [-11, -132, -221, 230, 508, -132, -359, 19, 84, 3], [-3, -47, -192, -155, 374, 466, -243, -350, 52, 84], [-84, -1011, -1727, 1656, 3877, -802, -2642, 9, 574, 52], [-52, -708, -2051, -583, 4152, 3149, -2726, -2486, 581, 574], [-574, -6940, -12188, 10577, 26969, -3884, -18089, -1004, 3828, 581]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -20, 22, 48, -14, -37, 3, 11, 0], [0, -1, -12, -20, 22, 48, -14, -37, 3, 11], [-11, -132, -221, 230, 508, -132, -359, 19, 84, 3], [-3, -47, -192, -155, 374, 466, -243, -350, 52, 84], [-84, -1011, -1727, 1656, 3877, -802, -2642, 9, 574, 52], [-52, -708, -2051, -583, 4152, 3149, -2726, -2486, 581, 574], [-574, -6940, -12188, 10577, 26969, -3884, -18089, -1004, 3828, 581], [-581, -7546, -18560, 594, 38465, 18835, -25381, -16346, 5387, 3828]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, -12, -20, 22, 48, -14, -37, 3, 11, 0], [0, -1, -12, -20, 22, 48, -14, -37, 3, 11], [-11, -132, -221, 230, 508, -132, -359, 19, 84, 3], [-3, -47, -192, -155, 374, 466, -243, -350, 52, 84], [-84, -1011, -1727, 1656, 3877, -802, -2642, 9, 574, 52], [-52, -708, -2051, -583, 4152, 3149, -2726, -2486, 581, 574], [-574, -6940, -12188, 10577, 26969, -3884, -18089, -1004, 3828, 581], [-581, -7546, -18560, 594, 38465, 18835, -25381, -16346, 5387, 3828], [-3828, -46517, -84106, 65656, 184338, -15127, -122801, -13897, 25762, 5387]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp61 : Fact (Nat.Prime 61) := fact_iff.2 (by norm_num)
instance hp397 : Fact (Nat.Prime 397) := fact_iff.2 (by norm_num)
instance hp757 : Fact (Nat.Prime 757) := fact_iff.2 (by norm_num)

def CD61 : CertificateDedekindCriterionLists l 61 where
  n := 2
  a' := [53, 49, 13, 52, 24, 52, 1]
  b' := [42, 41, 25, 55, 31, 12, 15, 38]
  k := [52, 19, 50, 39, 28, 54, 1]
  f := [20, 37, 46, 58, 50, 19, 6, 22, 16, 1]
  g := [33, 31, 47, 51, 33, 0, 10, 27, 1]
  h := [37, 34, 1]
  a := [2, 42, 40, 15, 53, 24, 19, 49]
  b := [21, 45, 33, 6, 8, 48, 50, 32, 12]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD397 : CertificateDedekindCriterionLists l 397 where
  n := 2
  a' := [151, 356, 259, 370, 350, 109, 387]
  b' := [47, 38, 16, 373, 237, 59, 11, 299]
  k := [270, 252, 112, 170, 158, 77, 1]
  f := [2, 69, 162, 110, 151, 127, 15, 74, 96, 1]
  g := [159, 393, 259, 363, 312, 30, 176, 237, 1]
  h := [5, 160, 1]
  a := [250, 128, 192, 211, 66, 80, 260, 382]
  b := [284, 329, 12, 142, 154, 170, 355, 7, 15]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD757 : CertificateDedekindCriterionLists l 757 where
  n := 2
  a' := [375, 120, 520, 193, 42, 55, 89, 238]
  b' := [428, 467, 260, 421, 591, 649, 87, 282, 310]
  k := [573, 423, 13, 691, 426, 541, 314, 183, 1]
  f := [69, 37, 140, 286, 122, 193, 219, 229, 179, 1]
  g := [182, 97, 369, 753, 319, 508, 576, 602, 470, 1]
  h := [287, 1]
  a := [578, 665, 485, 179, 513, 751, 388, 346, 564]
  b := [750, 75, 84, 51, 442, 273, 320, 266, 193]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![61, 397, 757]
  exp := ![1, 1, 1]
  pdgood := [61, 397, 757]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp61.out
    exact hp397.out
    exact hp757.out
  a := [471159529, 2496066120, 143900126, -10985164292, -7920012180, 6382900598, 5387707596, -659927920, -709849220]
  b := [-37735605, -553379689, -1656270543, -651243658, 2293464645, 1594212132, -847360632, -694937588, 65992792, 70984922]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 61 T_ofList CD61
    exact satisfiesDedekindCriterion_of_certificate_lists T l 397 T_ofList CD397
    exact satisfiesDedekindCriterion_of_certificate_lists T l 757 T_ofList CD757

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

end VoightMaximalOrderD10R1

namespace VoightMaximalOrderD10R3

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨617567936161, [1, -9, 18, 15, -47, -11, 39, 5, -12, -1, 1], 1⟩
local notation "l" => [1, -9, 18, 15, -47, -11, 39, 5, -12, -1, 1]
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
  a := ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, -18, -15, 47, 11, -39, -5, 12, 1]], ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, -18, -15, 47, 11, -39, -5, 12, 1], ![-1, 8, -9, -33, 32, 58, -28, -44, 7, 13]], ![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, -18, -15, 47, 11, -39, -5, 12, 1], ![-1, 8, -9, -33, 32, 58, -28, -44, 7, 13], ![-13, 116, -226, -204, 578, 175, -449, -93, 112, 20]], ![![0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, -18, -15, 47, 11, -39, -5, 12, 1], ![-1, 8, -9, -33, 32, 58, -28, -44, 7, 13], ![-13, 116, -226, -204, 578, 175, -449, -93, 112, 20], ![-20, 167, -244, -526, 736, 798, -605, -549, 147, 132]], ![![0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, -18, -15, 47, 11, -39, -5, 12, 1], ![-1, 8, -9, -33, 32, 58, -28, -44, 7, 13], ![-13, 116, -226, -204, 578, 175, -449, -93, 112, 20], ![-20, 167, -244, -526, 736, 798, -605, -549, 147, 132], ![-132, 1168, -2209, -2224, 5678, 2188, -4350, -1265, 1035, 279]], ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, -18, -15, 47, 11, -39, -5, 12, 1], ![-1, 8, -9, -33, 32, 58, -28, -44, 7, 13], ![-13, 116, -226, -204, 578, 175, -449, -93, 112, 20], ![-20, 167, -244, -526, 736, 798, -605, -549, 147, 132], ![-132, 1168, -2209, -2224, 5678, 2188, -4350, -1265, 1035, 279], ![-279, 2379, -3854, -6394, 10889, 8747, -8693, -5745, 2083, 1314]], ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, -18, -15, 47, 11, -39, -5, 12, 1], ![-1, 8, -9, -33, 32, 58, -28, -44, 7, 13], ![-13, 116, -226, -204, 578, 175, -449, -93, 112, 20], ![-20, 167, -244, -526, 736, 798, -605, -549, 147, 132], ![-132, 1168, -2209, -2224, 5678, 2188, -4350, -1265, 1035, 279], ![-279, 2379, -3854, -6394, 10889, 8747, -8693, -5745, 2083, 1314], ![-1314, 11547, -21273, -23564, 55364, 25343, -42499, -15263, 10023, 3397]], ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, -18, -15, 47, 11, -39, -5, 12, 1], ![-1, 8, -9, -33, 32, 58, -28, -44, 7, 13], ![-13, 116, -226, -204, 578, 175, -449, -93, 112, 20], ![-20, 167, -244, -526, 736, 798, -605, -549, 147, 132], ![-132, 1168, -2209, -2224, 5678, 2188, -4350, -1265, 1035, 279], ![-279, 2379, -3854, -6394, 10889, 8747, -8693, -5745, 2083, 1314], ![-1314, 11547, -21273, -23564, 55364, 25343, -42499, -15263, 10023, 3397], ![-3397, 29259, -49599, -72228, 136095, 92731, -107140, -59484, 25501, 13420]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![-1, 9, -18, -15, 47, 11, -39, -5, 12, 1], ![-1, 8, -9, -33, 32, 58, -28, -44, 7, 13], ![-13, 116, -226, -204, 578, 175, -449, -93, 112, 20], ![-20, 167, -244, -526, 736, 798, -605, -549, 147, 132], ![-132, 1168, -2209, -2224, 5678, 2188, -4350, -1265, 1035, 279], ![-279, 2379, -3854, -6394, 10889, 8747, -8693, -5745, 2083, 1314], ![-1314, 11547, -21273, -23564, 55364, 25343, -42499, -15263, 10023, 3397], ![-3397, 29259, -49599, -72228, 136095, 92731, -107140, -59484, 25501, 13420], ![-13420, 117383, -212301, -250899, 558512, 283715, -430649, -174240, 101556, 38921]]]
  s := ![![[], [], [], [], [], [], [], [], [], []], ![[], [], [], [], [], [], [], [], [], [-1]], ![[], [], [], [], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [], [], [], [-1], [-1, -1], [-13, -1, -1]], ![[], [], [], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-20, -13, -1, -1]], ![[], [], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-20, -13, -1, -1], [-132, -20, -13, -1, -1]], ![[], [], [], [], [-1], [-1, -1], [-13, -1, -1], [-20, -13, -1, -1], [-132, -20, -13, -1, -1], [-279, -132, -20, -13, -1, -1]], ![[], [], [], [-1], [-1, -1], [-13, -1, -1], [-20, -13, -1, -1], [-132, -20, -13, -1, -1], [-279, -132, -20, -13, -1, -1], [-1314, -279, -132, -20, -13, -1, -1]], ![[], [], [-1], [-1, -1], [-13, -1, -1], [-20, -13, -1, -1], [-132, -20, -13, -1, -1], [-279, -132, -20, -13, -1, -1], [-1314, -279, -132, -20, -13, -1, -1], [-3397, -1314, -279, -132, -20, -13, -1, -1]], ![[], [-1], [-1, -1], [-13, -1, -1], [-20, -13, -1, -1], [-132, -20, -13, -1, -1], [-279, -132, -20, -13, -1, -1], [-1314, -279, -132, -20, -13, -1, -1], [-3397, -1314, -279, -132, -20, -13, -1, -1], [-13420, -3397, -1314, -279, -132, -20, -13, -1, -1]]]
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
def Table : Fin 10 → Fin 10 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, -18, -15, 47, 11, -39, -5, 12, 1]], ![[0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, -18, -15, 47, 11, -39, -5, 12, 1], [-1, 8, -9, -33, 32, 58, -28, -44, 7, 13]], ![[0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, -18, -15, 47, 11, -39, -5, 12, 1], [-1, 8, -9, -33, 32, 58, -28, -44, 7, 13], [-13, 116, -226, -204, 578, 175, -449, -93, 112, 20]], ![[0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, -18, -15, 47, 11, -39, -5, 12, 1], [-1, 8, -9, -33, 32, 58, -28, -44, 7, 13], [-13, 116, -226, -204, 578, 175, -449, -93, 112, 20], [-20, 167, -244, -526, 736, 798, -605, -549, 147, 132]], ![[0, 0, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, -18, -15, 47, 11, -39, -5, 12, 1], [-1, 8, -9, -33, 32, 58, -28, -44, 7, 13], [-13, 116, -226, -204, 578, 175, -449, -93, 112, 20], [-20, 167, -244, -526, 736, 798, -605, -549, 147, 132], [-132, 1168, -2209, -2224, 5678, 2188, -4350, -1265, 1035, 279]], ![[0, 0, 0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, -18, -15, 47, 11, -39, -5, 12, 1], [-1, 8, -9, -33, 32, 58, -28, -44, 7, 13], [-13, 116, -226, -204, 578, 175, -449, -93, 112, 20], [-20, 167, -244, -526, 736, 798, -605, -549, 147, 132], [-132, 1168, -2209, -2224, 5678, 2188, -4350, -1265, 1035, 279], [-279, 2379, -3854, -6394, 10889, 8747, -8693, -5745, 2083, 1314]], ![[0, 0, 0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, -18, -15, 47, 11, -39, -5, 12, 1], [-1, 8, -9, -33, 32, 58, -28, -44, 7, 13], [-13, 116, -226, -204, 578, 175, -449, -93, 112, 20], [-20, 167, -244, -526, 736, 798, -605, -549, 147, 132], [-132, 1168, -2209, -2224, 5678, 2188, -4350, -1265, 1035, 279], [-279, 2379, -3854, -6394, 10889, 8747, -8693, -5745, 2083, 1314], [-1314, 11547, -21273, -23564, 55364, 25343, -42499, -15263, 10023, 3397]], ![[0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, -18, -15, 47, 11, -39, -5, 12, 1], [-1, 8, -9, -33, 32, 58, -28, -44, 7, 13], [-13, 116, -226, -204, 578, 175, -449, -93, 112, 20], [-20, 167, -244, -526, 736, 798, -605, -549, 147, 132], [-132, 1168, -2209, -2224, 5678, 2188, -4350, -1265, 1035, 279], [-279, 2379, -3854, -6394, 10889, 8747, -8693, -5745, 2083, 1314], [-1314, 11547, -21273, -23564, 55364, 25343, -42499, -15263, 10023, 3397], [-3397, 29259, -49599, -72228, 136095, 92731, -107140, -59484, 25501, 13420]], ![[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [-1, 9, -18, -15, 47, 11, -39, -5, 12, 1], [-1, 8, -9, -33, 32, 58, -28, -44, 7, 13], [-13, 116, -226, -204, 578, 175, -449, -93, 112, 20], [-20, 167, -244, -526, 736, 798, -605, -549, 147, 132], [-132, 1168, -2209, -2224, 5678, 2188, -4350, -1265, 1035, 279], [-279, 2379, -3854, -6394, 10889, 8747, -8693, -5745, 2083, 1314], [-1314, 11547, -21273, -23564, 55364, 25343, -42499, -15263, 10023, 3397], [-3397, 29259, -49599, -72228, 136095, 92731, -107140, -59484, 25501, 13420], [-13420, 117383, -212301, -250899, 558512, 283715, -430649, -174240, 101556, 38921]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0] [] (by decide)

instance hp11 : Fact (Nat.Prime 11) := fact_iff.2 (by norm_num)
instance hp43 : Fact (Nat.Prime 43) := fact_iff.2 (by norm_num)
instance hp67 : Fact (Nat.Prime 67) := fact_iff.2 (by norm_num)

def CD11 : CertificateDedekindCriterionLists l 11 where
  n := 5
  a' := [3]
  b' := [4, 4]
  k := [1]
  f := [4, 7, 1, 0, 9, 7, -1, 4, 3, 1]
  g := [5, 2, 1]
  h := [9, 10, 0, 1, 10, 9, 0, 8, 1]
  a := [5, 8]
  b := [5, 0, 0, 5, 0, 4, 8, 9, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD43 : CertificateDedekindCriterionLists l 43 where
  n := 2
  a' := [19, 21, 17, 1, 16, 36, 10, 15]
  b' := [41, 35, 2, 5, 41, 5, 15, 4, 27]
  k := [15, 21, 14, 4, 21, 2, 7, 6, 1]
  f := [5, 3, 6, 0, 17, 7, 17, 13, 11, 1]
  g := [12, 6, 15, 0, 38, 14, 42, 29, 24, 1]
  h := [18, 1]
  a := [16, 2, 42, 22, 30, 8, 13, 2, 29]
  b := [40, 11, 26, 35, 34, 28, 29, 31, 14]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD67 : CertificateDedekindCriterionLists l 67 where
  n := 2
  a' := [22, 64, 53, 24, 6, 23, 13, 7]
  b' := [54, 30, 49, 16, 2, 7, 9, 61, 29]
  k := [64, 8, 10, 20, 52, 65, 4, 49, 1]
  f := [5, 41, 17, 29, 39, 23, 20, 33, 16, 1]
  g := [8, 65, 26, 46, 60, 35, 32, 52, 24, 1]
  h := [42, 1]
  a := [65, 4, 34, 45, 47, 4, 54, 30, 58]
  b := [60, 6, 37, 19, 1, 31, 1, 32, 9]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![11, 43, 67]
  exp := ![1, 1, 1]
  pdgood := [11, 43, 67]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp11.out
    exact hp43.out
    exact hp67.out
  a := [2317709, -14593140, 1738926, 66099458, -43511575, -48514936, 31465985, 8606326, -4318240]
  b := [254002, -2923161, 8999138, -3643046, -13948860, 9069167, 6574596, -4135777, -903815, 431824]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
    exact satisfiesDedekindCriterion_of_certificate_lists T l 43 T_ofList CD43
    exact satisfiesDedekindCriterion_of_certificate_lists T l 67 T_ofList CD67

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

end VoightMaximalOrderD10R3

end TraceEuclidean
