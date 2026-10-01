import TraceEuclidean.DegreeFiveCriticalIrreducibility
import TraceEuclidean.ExplicitResultantCertificate
import TraceEuclidean.CriticalFieldBridge
import TraceEuclidean.VoightIntegralBasisCertificate
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.CertifyAdjoinRootCore
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.MaximalAPI
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.CertificateDedekind
import Mathlib.Tactic

set_option linter.all false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

namespace TraceEuclidean
namespace DegreeFiveCritical22

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨126032, [-2, 6, 0, -6, 0, 1], 1⟩
local notation "l" => [-2, 6, 0, -6, 0, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ degreeFiveCriticalRows := by decide
lemma T_irreducible : Irreducible T :=
  degreeFiveCriticalRows_irreducible row row_mem
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
def basisNumerator : Fin 5 → Fin 5 → ℤ := ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1], ![2, -6, 0, 6, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1], ![2, -6, 0, 6, 0], ![0, 2, -6, 0, 6]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1], ![2, -6, 0, 6, 0], ![0, 2, -6, 0, 6], ![12, -36, 2, 30, 0]], ![![0, 0, 0, 0, 1], ![2, -6, 0, 6, 0], ![0, 2, -6, 0, 6], ![12, -36, 2, 30, 0], ![0, 12, -36, 2, 30]]]
  s := ![![[], [], [], [], []], ![[], [], [], [], [-1]], ![[], [], [], [-1], [0, -1]], ![[], [], [-1], [0, -1], [-6, 0, -1]], ![[], [-1], [0, -1], [-6, 0, -1], [0, -6, 0, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 5 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 5) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 5) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 5) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 5 → Fin 5 → List ℤ := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1], [2, -6, 0, 6, 0]], ![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1], [2, -6, 0, 6, 0], [0, 2, -6, 0, 6]], ![[0, 0, 0, 1, 0], [0, 0, 0, 0, 1], [2, -6, 0, 6, 0], [0, 2, -6, 0, 6], [12, -36, 2, 30, 0]], ![[0, 0, 0, 0, 1], [2, -6, 0, 6, 0], [0, 2, -6, 0, 6], [12, -36, 2, 30, 0], [0, 12, -36, 2, 30]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp7877 : Fact (Nat.Prime 7877) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 5
  a' := []
  b' := [1]
  k := [1]
  f := [1, -3, 0, 3]
  g := [0, 1]
  h := [0, 0, 0, 0, 1]
  a := [1]
  b := [1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD7877 : CertificateDedekindCriterionLists l 7877 where
  n := 2
  a' := [2237, 3502, 3520]
  b' := [6601, 2683, 2195, 6997]
  k := [5089, 1288, 4018, 1]
  f := [406, 859, 2273, 1497, 1]
  g := [545, 1153, 3051, 2009, 1]
  h := [5868, 1]
  a := [1054, 2042, 309, 2095]
  b := [3175, 6635, 1059, 5782]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![2, 7877]
  exp := ![1, 1]
  pdgood := [2, 7877]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp7877.out
  a := [21067, 41748, -6120, -13530]
  b := [9648, -7151, -14844, 1224, 2706]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7877 T_ofList CD7877

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

noncomputable def bOm : Basis (Fin 5) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 5 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 5
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 5 := T_degree

noncomputable def bQ : Basis (Fin 5) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 5) (Fin 5) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 5) :
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
          (∑ x : Fin 5,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 5,
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
    intro i j hji
    fin_cases i <;> fin_cases j <;>
      simp_all [P, basisNumerator, basisDenominator]
  rw [Matrix.det_of_upperTriangular htriangular]
  norm_num [P, basisNumerator, basisDenominator, row,
    Fin.prod_univ_succ]


def resultantState00 : Matrix (Fin 9) (Fin 9) ℚ :=
  ![
    ![6, 0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 6, 0, 0, 0, 6, -2, 0, 0],
    ![-18, 0, 6, 0, 0, 0, 6, -2, 0],
    ![0, -18, 0, 6, 0, -6, 0, 6, -2],
    ![5, 0, -18, 0, 6, 0, -6, 0, 6],
    ![0, 5, 0, -18, 0, 1, 0, -6, 0],
    ![0, 0, 5, 0, -18, 0, 1, 0, -6],
    ![0, 0, 0, 5, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 5, 0, 0, 0, 1]
  ]

def resultantState01 : Matrix (Fin 9) (Fin 9) ℚ :=
  ![
    ![6, 0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 6, 0, 0, 0, 6, -2, 0, 0],
    ![0, 0, 6, 0, 0, -6, 6, -2, 0],
    ![0, -18, 0, 6, 0, -6, 0, 6, -2],
    ![5, 0, -18, 0, 6, 0, -6, 0, 6],
    ![0, 5, 0, -18, 0, 1, 0, -6, 0],
    ![0, 0, 5, 0, -18, 0, 1, 0, -6],
    ![0, 0, 0, 5, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 5, 0, 0, 0, 1]
  ]

def resultantState02 : Matrix (Fin 9) (Fin 9) ℚ :=
  ![
    ![6, 0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 6, 0, 0, 0, 6, -2, 0, 0],
    ![0, 0, 6, 0, 0, -6, 6, -2, 0],
    ![0, -18, 0, 6, 0, -6, 0, 6, -2],
    ![0, 0, -18, 0, 6, (5 : ℚ) / 3, -6, 0, 6],
    ![0, 5, 0, -18, 0, 1, 0, -6, 0],
    ![0, 0, 5, 0, -18, 0, 1, 0, -6],
    ![0, 0, 0, 5, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 5, 0, 0, 0, 1]
  ]

def resultantState03 : Matrix (Fin 9) (Fin 9) ℚ :=
  ![
    ![6, 0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 6, 0, 0, 0, 6, -2, 0, 0],
    ![0, 0, 6, 0, 0, -6, 6, -2, 0],
    ![0, 0, 0, 6, 0, 12, -6, 6, -2],
    ![0, 0, -18, 0, 6, (5 : ℚ) / 3, -6, 0, 6],
    ![0, 5, 0, -18, 0, 1, 0, -6, 0],
    ![0, 0, 5, 0, -18, 0, 1, 0, -6],
    ![0, 0, 0, 5, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 5, 0, 0, 0, 1]
  ]

def resultantState04 : Matrix (Fin 9) (Fin 9) ℚ :=
  ![
    ![6, 0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 6, 0, 0, 0, 6, -2, 0, 0],
    ![0, 0, 6, 0, 0, -6, 6, -2, 0],
    ![0, 0, 0, 6, 0, 12, -6, 6, -2],
    ![0, 0, -18, 0, 6, (5 : ℚ) / 3, -6, 0, 6],
    ![0, 0, 0, -18, 0, -4, (5 : ℚ) / 3, -6, 0],
    ![0, 0, 5, 0, -18, 0, 1, 0, -6],
    ![0, 0, 0, 5, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 5, 0, 0, 0, 1]
  ]

def resultantState05 : Matrix (Fin 9) (Fin 9) ℚ :=
  ![
    ![6, 0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 6, 0, 0, 0, 6, -2, 0, 0],
    ![0, 0, 6, 0, 0, -6, 6, -2, 0],
    ![0, 0, 0, 6, 0, 12, -6, 6, -2],
    ![0, 0, 0, 0, 6, (-49 : ℚ) / 3, 12, -6, 6],
    ![0, 0, 0, -18, 0, -4, (5 : ℚ) / 3, -6, 0],
    ![0, 0, 5, 0, -18, 0, 1, 0, -6],
    ![0, 0, 0, 5, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 5, 0, 0, 0, 1]
  ]

def resultantState06 : Matrix (Fin 9) (Fin 9) ℚ :=
  ![
    ![6, 0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 6, 0, 0, 0, 6, -2, 0, 0],
    ![0, 0, 6, 0, 0, -6, 6, -2, 0],
    ![0, 0, 0, 6, 0, 12, -6, 6, -2],
    ![0, 0, 0, 0, 6, (-49 : ℚ) / 3, 12, -6, 6],
    ![0, 0, 0, -18, 0, -4, (5 : ℚ) / 3, -6, 0],
    ![0, 0, 0, 0, -18, 5, -4, (5 : ℚ) / 3, -6],
    ![0, 0, 0, 5, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 5, 0, 0, 0, 1]
  ]

def resultantState07 : Matrix (Fin 9) (Fin 9) ℚ :=
  ![
    ![6, 0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 6, 0, 0, 0, 6, -2, 0, 0],
    ![0, 0, 6, 0, 0, -6, 6, -2, 0],
    ![0, 0, 0, 6, 0, 12, -6, 6, -2],
    ![0, 0, 0, 0, 6, (-49 : ℚ) / 3, 12, -6, 6],
    ![0, 0, 0, 0, 0, 32, (-49 : ℚ) / 3, 12, -6],
    ![0, 0, 0, 0, -18, 5, -4, (5 : ℚ) / 3, -6],
    ![0, 0, 0, 5, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 5, 0, 0, 0, 1]
  ]

def resultantState08 : Matrix (Fin 9) (Fin 9) ℚ :=
  ![
    ![6, 0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 6, 0, 0, 0, 6, -2, 0, 0],
    ![0, 0, 6, 0, 0, -6, 6, -2, 0],
    ![0, 0, 0, 6, 0, 12, -6, 6, -2],
    ![0, 0, 0, 0, 6, (-49 : ℚ) / 3, 12, -6, 6],
    ![0, 0, 0, 0, 0, 32, (-49 : ℚ) / 3, 12, -6],
    ![0, 0, 0, 0, -18, 5, -4, (5 : ℚ) / 3, -6],
    ![0, 0, 0, 0, 0, -10, 5, -4, (5 : ℚ) / 3],
    ![0, 0, 0, 0, 5, 0, 0, 0, 1]
  ]

def resultantState09 : Matrix (Fin 9) (Fin 9) ℚ :=
  ![
    ![6, 0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 6, 0, 0, 0, 6, -2, 0, 0],
    ![0, 0, 6, 0, 0, -6, 6, -2, 0],
    ![0, 0, 0, 6, 0, 12, -6, 6, -2],
    ![0, 0, 0, 0, 6, (-49 : ℚ) / 3, 12, -6, 6],
    ![0, 0, 0, 0, 0, 32, (-49 : ℚ) / 3, 12, -6],
    ![0, 0, 0, 0, 0, -44, 32, (-49 : ℚ) / 3, 12],
    ![0, 0, 0, 0, 0, -10, 5, -4, (5 : ℚ) / 3],
    ![0, 0, 0, 0, 5, 0, 0, 0, 1]
  ]

def resultantState10 : Matrix (Fin 9) (Fin 9) ℚ :=
  ![
    ![6, 0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 6, 0, 0, 0, 6, -2, 0, 0],
    ![0, 0, 6, 0, 0, -6, 6, -2, 0],
    ![0, 0, 0, 6, 0, 12, -6, 6, -2],
    ![0, 0, 0, 0, 6, (-49 : ℚ) / 3, 12, -6, 6],
    ![0, 0, 0, 0, 0, 32, (-49 : ℚ) / 3, 12, -6],
    ![0, 0, 0, 0, 0, -44, 32, (-49 : ℚ) / 3, 12],
    ![0, 0, 0, 0, 0, -10, 5, -4, (5 : ℚ) / 3],
    ![0, 0, 0, 0, 0, (245 : ℚ) / 18, -10, 5, -4]
  ]

def resultantState11 : Matrix (Fin 9) (Fin 9) ℚ :=
  ![
    ![6, 0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 6, 0, 0, 0, 6, -2, 0, 0],
    ![0, 0, 6, 0, 0, -6, 6, -2, 0],
    ![0, 0, 0, 6, 0, 12, -6, 6, -2],
    ![0, 0, 0, 0, 6, (-49 : ℚ) / 3, 12, -6, 6],
    ![0, 0, 0, 0, 0, 32, (-49 : ℚ) / 3, 12, -6],
    ![0, 0, 0, 0, 0, 0, (229 : ℚ) / 24, (1 : ℚ) / 6, (15 : ℚ) / 4],
    ![0, 0, 0, 0, 0, -10, 5, -4, (5 : ℚ) / 3],
    ![0, 0, 0, 0, 0, (245 : ℚ) / 18, -10, 5, -4]
  ]

def resultantState12 : Matrix (Fin 9) (Fin 9) ℚ :=
  ![
    ![6, 0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 6, 0, 0, 0, 6, -2, 0, 0],
    ![0, 0, 6, 0, 0, -6, 6, -2, 0],
    ![0, 0, 0, 6, 0, 12, -6, 6, -2],
    ![0, 0, 0, 0, 6, (-49 : ℚ) / 3, 12, -6, 6],
    ![0, 0, 0, 0, 0, 32, (-49 : ℚ) / 3, 12, -6],
    ![0, 0, 0, 0, 0, 0, (229 : ℚ) / 24, (1 : ℚ) / 6, (15 : ℚ) / 4],
    ![0, 0, 0, 0, 0, 0, (-5 : ℚ) / 48, (-1 : ℚ) / 4, (-5 : ℚ) / 24],
    ![0, 0, 0, 0, 0, (245 : ℚ) / 18, -10, 5, -4]
  ]

def resultantState13 : Matrix (Fin 9) (Fin 9) ℚ :=
  ![
    ![6, 0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 6, 0, 0, 0, 6, -2, 0, 0],
    ![0, 0, 6, 0, 0, -6, 6, -2, 0],
    ![0, 0, 0, 6, 0, 12, -6, 6, -2],
    ![0, 0, 0, 0, 6, (-49 : ℚ) / 3, 12, -6, 6],
    ![0, 0, 0, 0, 0, 32, (-49 : ℚ) / 3, 12, -6],
    ![0, 0, 0, 0, 0, 0, (229 : ℚ) / 24, (1 : ℚ) / 6, (15 : ℚ) / 4],
    ![0, 0, 0, 0, 0, 0, (-5 : ℚ) / 48, (-1 : ℚ) / 4, (-5 : ℚ) / 24],
    ![0, 0, 0, 0, 0, 0, (-5275 : ℚ) / 1728, (-5 : ℚ) / 48, (-139 : ℚ) / 96]
  ]

def resultantState14 : Matrix (Fin 9) (Fin 9) ℚ :=
  ![
    ![6, 0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 6, 0, 0, 0, 6, -2, 0, 0],
    ![0, 0, 6, 0, 0, -6, 6, -2, 0],
    ![0, 0, 0, 6, 0, 12, -6, 6, -2],
    ![0, 0, 0, 0, 6, (-49 : ℚ) / 3, 12, -6, 6],
    ![0, 0, 0, 0, 0, 32, (-49 : ℚ) / 3, 12, -6],
    ![0, 0, 0, 0, 0, 0, (229 : ℚ) / 24, (1 : ℚ) / 6, (15 : ℚ) / 4],
    ![0, 0, 0, 0, 0, 0, 0, (-341 : ℚ) / 1374, (-115 : ℚ) / 687],
    ![0, 0, 0, 0, 0, 0, (-5275 : ℚ) / 1728, (-5 : ℚ) / 48, (-139 : ℚ) / 96]
  ]

def resultantState15 : Matrix (Fin 9) (Fin 9) ℚ :=
  ![
    ![6, 0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 6, 0, 0, 0, 6, -2, 0, 0],
    ![0, 0, 6, 0, 0, -6, 6, -2, 0],
    ![0, 0, 0, 6, 0, 12, -6, 6, -2],
    ![0, 0, 0, 0, 6, (-49 : ℚ) / 3, 12, -6, 6],
    ![0, 0, 0, 0, 0, 32, (-49 : ℚ) / 3, 12, -6],
    ![0, 0, 0, 0, 0, 0, (229 : ℚ) / 24, (1 : ℚ) / 6, (15 : ℚ) / 4],
    ![0, 0, 0, 0, 0, 0, 0, (-341 : ℚ) / 1374, (-115 : ℚ) / 687],
    ![0, 0, 0, 0, 0, 0, 0, (-2515 : ℚ) / 49464, (-341 : ℚ) / 1374]
  ]

def resultantState16 : Matrix (Fin 9) (Fin 9) ℚ :=
  ![
    ![6, 0, 0, 0, 0, -2, 0, 0, 0],
    ![0, 6, 0, 0, 0, 6, -2, 0, 0],
    ![0, 0, 6, 0, 0, -6, 6, -2, 0],
    ![0, 0, 0, 6, 0, 12, -6, 6, -2],
    ![0, 0, 0, 0, 6, (-49 : ℚ) / 3, 12, -6, 6],
    ![0, 0, 0, 0, 0, 32, (-49 : ℚ) / 3, 12, -6],
    ![0, 0, 0, 0, 0, 0, (229 : ℚ) / 24, (1 : ℚ) / 6, (15 : ℚ) / 4],
    ![0, 0, 0, 0, 0, 0, 0, (-341 : ℚ) / 1374, (-115 : ℚ) / 687],
    ![0, 0, 0, 0, 0, 0, 0, 0, (-7877 : ℚ) / 36828]
  ]

def resultantOperation01 : RowOperation 9 :=
  RowOperation.add 2 0 (3)

def resultantOperation02 : RowOperation 9 :=
  RowOperation.add 4 0 ((-5 : ℚ) / 6)

def resultantOperation03 : RowOperation 9 :=
  RowOperation.add 3 1 (3)

def resultantOperation04 : RowOperation 9 :=
  RowOperation.add 5 1 ((-5 : ℚ) / 6)

def resultantOperation05 : RowOperation 9 :=
  RowOperation.add 4 2 (3)

def resultantOperation06 : RowOperation 9 :=
  RowOperation.add 6 2 ((-5 : ℚ) / 6)

def resultantOperation07 : RowOperation 9 :=
  RowOperation.add 5 3 (3)

def resultantOperation08 : RowOperation 9 :=
  RowOperation.add 7 3 ((-5 : ℚ) / 6)

def resultantOperation09 : RowOperation 9 :=
  RowOperation.add 6 4 (3)

def resultantOperation10 : RowOperation 9 :=
  RowOperation.add 8 4 ((-5 : ℚ) / 6)

def resultantOperation11 : RowOperation 9 :=
  RowOperation.add 6 5 ((11 : ℚ) / 8)

def resultantOperation12 : RowOperation 9 :=
  RowOperation.add 7 5 ((5 : ℚ) / 16)

def resultantOperation13 : RowOperation 9 :=
  RowOperation.add 8 5 ((-245 : ℚ) / 576)

def resultantOperation14 : RowOperation 9 :=
  RowOperation.add 7 6 ((5 : ℚ) / 458)

def resultantOperation15 : RowOperation 9 :=
  RowOperation.add 8 6 ((5275 : ℚ) / 16488)

def resultantOperation16 : RowOperation 9 :=
  RowOperation.add 8 7 ((-2515 : ℚ) / 12276)

def resultantMatrix : Matrix (Fin 9) (Fin 9) ℚ :=
  resultantState00

def resultantOperations : List (RowOperation 9) :=
  [
    resultantOperation01,
    resultantOperation02,
    resultantOperation03,
    resultantOperation04,
    resultantOperation05,
    resultantOperation06,
    resultantOperation07,
    resultantOperation08,
    resultantOperation09,
    resultantOperation10,
    resultantOperation11,
    resultantOperation12,
    resultantOperation13,
    resultantOperation14,
    resultantOperation15,
    resultantOperation16
  ]

def resultantReduced : Matrix (Fin 9) (Fin 9) ℚ :=
  resultantState16

lemma resultantStep01 :
    resultantOperation01.apply resultantState00 = resultantState01 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [resultantOperation01, resultantState00, resultantState01,
      RowOperation.apply, Matrix.updateRow,
      Equiv.swap_apply_def] <;>
    norm_num

lemma resultantStep02 :
    resultantOperation02.apply resultantState01 = resultantState02 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [resultantOperation02, resultantState01, resultantState02,
      RowOperation.apply, Matrix.updateRow,
      Equiv.swap_apply_def] <;>
    norm_num

lemma resultantStep03 :
    resultantOperation03.apply resultantState02 = resultantState03 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [resultantOperation03, resultantState02, resultantState03,
      RowOperation.apply, Matrix.updateRow,
      Equiv.swap_apply_def] <;>
    norm_num

lemma resultantStep04 :
    resultantOperation04.apply resultantState03 = resultantState04 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [resultantOperation04, resultantState03, resultantState04,
      RowOperation.apply, Matrix.updateRow,
      Equiv.swap_apply_def] <;>
    norm_num

lemma resultantStep05 :
    resultantOperation05.apply resultantState04 = resultantState05 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [resultantOperation05, resultantState04, resultantState05,
      RowOperation.apply, Matrix.updateRow,
      Equiv.swap_apply_def] <;>
    norm_num

lemma resultantStep06 :
    resultantOperation06.apply resultantState05 = resultantState06 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [resultantOperation06, resultantState05, resultantState06,
      RowOperation.apply, Matrix.updateRow,
      Equiv.swap_apply_def] <;>
    norm_num

lemma resultantStep07 :
    resultantOperation07.apply resultantState06 = resultantState07 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [resultantOperation07, resultantState06, resultantState07,
      RowOperation.apply, Matrix.updateRow,
      Equiv.swap_apply_def] <;>
    norm_num

lemma resultantStep08 :
    resultantOperation08.apply resultantState07 = resultantState08 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [resultantOperation08, resultantState07, resultantState08,
      RowOperation.apply, Matrix.updateRow,
      Equiv.swap_apply_def] <;>
    norm_num

lemma resultantStep09 :
    resultantOperation09.apply resultantState08 = resultantState09 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [resultantOperation09, resultantState08, resultantState09,
      RowOperation.apply, Matrix.updateRow,
      Equiv.swap_apply_def] <;>
    norm_num

lemma resultantStep10 :
    resultantOperation10.apply resultantState09 = resultantState10 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [resultantOperation10, resultantState09, resultantState10,
      RowOperation.apply, Matrix.updateRow,
      Equiv.swap_apply_def] <;>
    norm_num

lemma resultantStep11 :
    resultantOperation11.apply resultantState10 = resultantState11 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [resultantOperation11, resultantState10, resultantState11,
      RowOperation.apply, Matrix.updateRow,
      Equiv.swap_apply_def] <;>
    norm_num

lemma resultantStep12 :
    resultantOperation12.apply resultantState11 = resultantState12 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [resultantOperation12, resultantState11, resultantState12,
      RowOperation.apply, Matrix.updateRow,
      Equiv.swap_apply_def] <;>
    norm_num

lemma resultantStep13 :
    resultantOperation13.apply resultantState12 = resultantState13 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [resultantOperation13, resultantState12, resultantState13,
      RowOperation.apply, Matrix.updateRow,
      Equiv.swap_apply_def] <;>
    norm_num

lemma resultantStep14 :
    resultantOperation14.apply resultantState13 = resultantState14 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [resultantOperation14, resultantState13, resultantState14,
      RowOperation.apply, Matrix.updateRow,
      Equiv.swap_apply_def] <;>
    norm_num

lemma resultantStep15 :
    resultantOperation15.apply resultantState14 = resultantState15 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [resultantOperation15, resultantState14, resultantState15,
      RowOperation.apply, Matrix.updateRow,
      Equiv.swap_apply_def] <;>
    norm_num

lemma resultantStep16 :
    resultantOperation16.apply resultantState15 = resultantState16 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [resultantOperation16, resultantState15, resultantState16,
      RowOperation.apply, Matrix.updateRow,
      Equiv.swap_apply_def] <;>
    norm_num

lemma resultantMatrix_eq :
    ((Int.castRingHom ℚ).mapMatrix
      (voightResultantMatrixInt 5 row)) = resultantMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [resultantMatrix, resultantState00,
      voightResultantMatrixInt, voightCoefficientInt,
      voightDerivativeCoefficientInt, row] <;>
    decide

lemma resultant_replay :
    RowOperation.applyAll resultantOperations resultantMatrix =
      resultantReduced := by
  change RowOperation.applyAll
      [resultantOperation01,
    resultantOperation02,
    resultantOperation03,
    resultantOperation04,
    resultantOperation05,
    resultantOperation06,
    resultantOperation07,
    resultantOperation08,
    resultantOperation09,
    resultantOperation10,
    resultantOperation11,
    resultantOperation12,
    resultantOperation13,
    resultantOperation14,
    resultantOperation15,
    resultantOperation16] resultantState00 =
    resultantState16
  rw [RowOperation.applyAll, resultantStep01]
  rw [RowOperation.applyAll, resultantStep02]
  rw [RowOperation.applyAll, resultantStep03]
  rw [RowOperation.applyAll, resultantStep04]
  rw [RowOperation.applyAll, resultantStep05]
  rw [RowOperation.applyAll, resultantStep06]
  rw [RowOperation.applyAll, resultantStep07]
  rw [RowOperation.applyAll, resultantStep08]
  rw [RowOperation.applyAll, resultantStep09]
  rw [RowOperation.applyAll, resultantStep10]
  rw [RowOperation.applyAll, resultantStep11]
  rw [RowOperation.applyAll, resultantStep12]
  rw [RowOperation.applyAll, resultantStep13]
  rw [RowOperation.applyAll, resultantStep14]
  rw [RowOperation.applyAll, resultantStep15]
  rw [RowOperation.applyAll, resultantStep16]
  rfl

lemma resultantReduced_triangular :
    resultantReduced.BlockTriangular id := by
  intro i j hji
  fin_cases i <;> fin_cases j <;>
    simp_all [resultantReduced, resultantState16]

lemma resultantReduced_diagonal :
    (∏ i, resultantReduced i i) =
      RowOperation.multiplierAll resultantOperations *
        (voightExpectedResultantInt 5 row : ℚ) := by
  norm_num [resultantReduced, resultantState16,
    resultantOperations,
    resultantOperation01,
    resultantOperation02,
    resultantOperation03,
    resultantOperation04,
    resultantOperation05,
    resultantOperation06,
    resultantOperation07,
    resultantOperation08,
    resultantOperation09,
    resultantOperation10,
    resultantOperation11,
    resultantOperation12,
    resultantOperation13,
    resultantOperation14,
    resultantOperation15,
    resultantOperation16,
    RowOperation.multiplierAll, RowOperation.multiplier,
    voightExpectedResultantInt, row, Fin.prod_univ_succ] <;>
  simp [RowOperation.multiplier, Equiv.swap_apply_def]

lemma resultant_det :
    ((Int.castRingHom ℚ).mapMatrix
      (voightResultantMatrixInt 5 row)).det =
        (voightExpectedResultantInt 5 row : ℚ) := by
  rw [resultantMatrix_eq]
  exact det_eq_of_explicit_row_reduction
    resultantMatrix resultantReduced resultantOperations
    (voightExpectedResultantInt 5 row : ℚ)
    resultant_replay resultantReduced_triangular
    resultantReduced_diagonal

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
      (voightPolynomial_discr_eq_of_resultant_det 5 row
        (by norm_num) (by decide) (by decide) resultant_det)
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


/-- Transport this explicit critical-row certificate to any number field
generated by an algebraic integer with the same integral minimal polynomial. -/
theorem field_discriminant_eq_recorded_of_minpoly
    {L : Type*} [Field L] [NumberField L]
    (a : NumberField.RingOfIntegers L)
    (hpoly : T = minpoly ℤ (a : L))
    (hgen : IntermediateField.adjoin ℚ {(a : L)} = ⊤) :
    NumberField.discr L = (row.fieldDiscriminant : ℤ) := by
  exact numberField_discr_eq_of_adjoinRoot_model
    field_discriminant_eq_recorded a hpoly hgen

end

end DegreeFiveCritical22
end TraceEuclidean
