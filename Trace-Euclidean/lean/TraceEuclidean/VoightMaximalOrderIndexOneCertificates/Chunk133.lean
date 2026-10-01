import TraceEuclidean.VoightMaximalOrderIndexOneCertificates.Chunk129
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

namespace VoightMaximalOrderD7R69

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨98167689, [-1, 9, -18, -1, 16, -4, -3, 1], 1⟩
local notation "l" => [-1, 9, -18, -1, 16, -4, -3, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSeven := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSeven_irreducible row row_mem
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
def basisNumerator : Fin 7 → Fin 7 → ℤ := ![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 7 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![1, -9, 18, 1, -16, 4, 3]], ![![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![1, -9, 18, 1, -16, 4, 3], ![3, -26, 45, 21, -47, -4, 13]], ![![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![1, -9, 18, 1, -16, 4, 3], ![3, -26, 45, 21, -47, -4, 13], ![13, -114, 208, 58, -187, 5, 35]], ![![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![1, -9, 18, 1, -16, 4, 3], ![3, -26, 45, 21, -47, -4, 13], ![13, -114, 208, 58, -187, 5, 35], ![35, -302, 516, 243, -502, -47, 110]], ![![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![1, -9, 18, 1, -16, 4, 3], ![3, -26, 45, 21, -47, -4, 13], ![13, -114, 208, 58, -187, 5, 35], ![35, -302, 516, 243, -502, -47, 110], ![110, -955, 1678, 626, -1517, -62, 283]], ![![0, 0, 0, 0, 0, 0, 1], ![1, -9, 18, 1, -16, 4, 3], ![3, -26, 45, 21, -47, -4, 13], ![13, -114, 208, 58, -187, 5, 35], ![35, -302, 516, 243, -502, -47, 110], ![110, -955, 1678, 626, -1517, -62, 283], ![283, -2437, 4139, 1961, -3902, -385, 787]]]
  s := ![![[], [], [], [], [], [], []], ![[], [], [], [], [], [], [-1]], ![[], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [-1], [-3, -1], [-13, -3, -1]], ![[], [], [], [-1], [-3, -1], [-13, -3, -1], [-35, -13, -3, -1]], ![[], [], [-1], [-3, -1], [-13, -3, -1], [-35, -13, -3, -1], [-110, -35, -13, -3, -1]], ![[], [-1], [-3, -1], [-13, -3, -1], [-35, -13, -3, -1], [-110, -35, -13, -3, -1], [-283, -110, -35, -13, -3, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 7 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 7) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 7) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 7) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 7 → Fin 7 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [1, -9, 18, 1, -16, 4, 3]], ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [1, -9, 18, 1, -16, 4, 3], [3, -26, 45, 21, -47, -4, 13]], ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [1, -9, 18, 1, -16, 4, 3], [3, -26, 45, 21, -47, -4, 13], [13, -114, 208, 58, -187, 5, 35]], ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [1, -9, 18, 1, -16, 4, 3], [3, -26, 45, 21, -47, -4, 13], [13, -114, 208, 58, -187, 5, 35], [35, -302, 516, 243, -502, -47, 110]], ![[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [1, -9, 18, 1, -16, 4, 3], [3, -26, 45, 21, -47, -4, 13], [13, -114, 208, 58, -187, 5, 35], [35, -302, 516, 243, -502, -47, 110], [110, -955, 1678, 626, -1517, -62, 283]], ![[0, 0, 0, 0, 0, 0, 1], [1, -9, 18, 1, -16, 4, 3], [3, -26, 45, 21, -47, -4, 13], [13, -114, 208, 58, -187, 5, 35], [35, -302, 516, 243, -502, -47, 110], [110, -955, 1678, 626, -1517, -62, 283], [283, -2437, 4139, 1961, -3902, -385, 787]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp109 : Fact (Nat.Prime 109) := fact_iff.2 (by norm_num)
instance hp100069 : Fact (Nat.Prime 100069) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 2
  a' := [2]
  b' := [2, 2]
  k := [2, 1, 1, 1]
  f := [1, -2, 8, 2, -3, 3, 2]
  g := [1, 1, 2, 1, 2, 1]
  h := [2, 1, 1]
  a := [0, 0, 0, 1, 2]
  b := [1, 2, 2, 1, 0, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD109 : CertificateDedekindCriterionLists l 109 where
  n := 2
  a' := [63, 39, 92, 71, 9]
  b' := [6, 49, 74, 0, 84, 53]
  k := [66, 33, 26, 93, 72, 1]
  f := [5, 13, 7, 13, 2, 14, 1]
  g := [32, 82, 39, 81, 9, 89, 1]
  h := [17, 1]
  a := [67, 63, 24, 65, 19, 11]
  b := [10, 94, 64, 61, 43, 98]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD100069 : CertificateDedekindCriterionLists l 100069 where
  n := 2
  a' := [76174, 47967, 43610, 75309, 39126]
  b' := [26908, 59060, 94129, 90839, 44510, 93548]
  k := [92066, 58039, 70360, 6699, 32707, 1]
  f := [82721, 15633, 11436, 70079, 43994, 13680, 1]
  g := [98882, 18686, 13670, 83770, 52588, 16352, 1]
  h := [83714, 1]
  a := [90521, 69401, 79699, 4629, 70081, 33297]
  b := [48074, 51756, 75015, 83258, 38231, 66772]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![3, 109, 100069]
  exp := ![1, 1, 1]
  pdgood := [3, 109, 100069]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp109.out
    exact hp100069.out
  a := [255054363, -140686740, -479376870, 234555752, 137429545, -64690206]
  b := [31975214, -142785367, 37048306, 125623316, -45840041, -23593417, 9241458]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 109 T_ofList CD109
    exact satisfiesDedekindCriterion_of_certificate_lists T l 100069 T_ofList CD100069

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

noncomputable def bOm : Basis (Fin 7) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 7 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 7
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 7 := T_degree

noncomputable def bQ : Basis (Fin 7) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 7) (Fin 7) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 7) :
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
          (∑ x : Fin 7,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 7,
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
        (List.ofFn fun i : Fin 7 =>
          (List.ofFn fun j : Fin 7 =>
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
      (voightPolynomialDiscriminantInput 7 row row_mem)
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

end VoightMaximalOrderD7R69

namespace VoightMaximalOrderD7R71

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨99230049, [1, -4, -2, 12, 3, -7, -1, 1], 1⟩
local notation "l" => [1, -4, -2, 12, 3, -7, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSeven := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSeven_irreducible row row_mem
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
def basisNumerator : Fin 7 → Fin 7 → ℤ := ![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 7 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-1, 4, 2, -12, -3, 7, 1]], ![![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-1, 4, 2, -12, -3, 7, 1], ![-1, 3, 6, -10, -15, 4, 8]], ![![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-1, 4, 2, -12, -3, 7, 1], ![-1, 3, 6, -10, -15, 4, 8], ![-8, 31, 19, -90, -34, 41, 12]], ![![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-1, 4, 2, -12, -3, 7, 1], ![-1, 3, 6, -10, -15, 4, 8], ![-8, 31, 19, -90, -34, 41, 12], ![-12, 40, 55, -125, -126, 50, 53]], ![![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-1, 4, 2, -12, -3, 7, 1], ![-1, 3, 6, -10, -15, 4, 8], ![-8, 31, 19, -90, -34, 41, 12], ![-12, 40, 55, -125, -126, 50, 53], ![-53, 200, 146, -581, -284, 245, 103]], ![![0, 0, 0, 0, 0, 0, 1], ![-1, 4, 2, -12, -3, 7, 1], ![-1, 3, 6, -10, -15, 4, 8], ![-8, 31, 19, -90, -34, 41, 12], ![-12, 40, 55, -125, -126, 50, 53], ![-53, 200, 146, -581, -284, 245, 103], ![-103, 359, 406, -1090, -890, 437, 348]]]
  s := ![![[], [], [], [], [], [], []], ![[], [], [], [], [], [], [-1]], ![[], [], [], [], [], [-1], [-1, -1]], ![[], [], [], [], [-1], [-1, -1], [-8, -1, -1]], ![[], [], [], [-1], [-1, -1], [-8, -1, -1], [-12, -8, -1, -1]], ![[], [], [-1], [-1, -1], [-8, -1, -1], [-12, -8, -1, -1], [-53, -12, -8, -1, -1]], ![[], [-1], [-1, -1], [-8, -1, -1], [-12, -8, -1, -1], [-53, -12, -8, -1, -1], [-103, -53, -12, -8, -1, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 7 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 7) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 7) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 7) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 7 → Fin 7 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-1, 4, 2, -12, -3, 7, 1]], ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-1, 4, 2, -12, -3, 7, 1], [-1, 3, 6, -10, -15, 4, 8]], ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-1, 4, 2, -12, -3, 7, 1], [-1, 3, 6, -10, -15, 4, 8], [-8, 31, 19, -90, -34, 41, 12]], ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-1, 4, 2, -12, -3, 7, 1], [-1, 3, 6, -10, -15, 4, 8], [-8, 31, 19, -90, -34, 41, 12], [-12, 40, 55, -125, -126, 50, 53]], ![[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-1, 4, 2, -12, -3, 7, 1], [-1, 3, 6, -10, -15, 4, 8], [-8, 31, 19, -90, -34, 41, 12], [-12, 40, 55, -125, -126, 50, 53], [-53, 200, 146, -581, -284, 245, 103]], ![[0, 0, 0, 0, 0, 0, 1], [-1, 4, 2, -12, -3, 7, 1], [-1, 3, 6, -10, -15, 4, 8], [-8, 31, 19, -90, -34, 41, 12], [-12, 40, 55, -125, -126, 50, 53], [-53, 200, 146, -581, -284, 245, 103], [-103, 359, 406, -1090, -890, 437, 348]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp3675187 : Fact (Nat.Prime 3675187) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 3
  a' := [0, 2, 0, 1]
  b' := [1, 0, 1, 2, 1]
  k := [1, 1, 0, 0, 0, 1, 2, 1, 1]
  f := [0, 2, 2, -3, 0, 3, 1]
  g := [1, 1, 2, 0, 1, 1]
  h := [1, 1, 1]
  a := [0, 2]
  b := [1, 2, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3675187 : CertificateDedekindCriterionLists l 3675187 where
  n := 2
  a' := [2406663, 874440, 986064, 329208, 746183]
  b' := [2928872, 2308961, 1049094, 773604, 1589227, 2938292]
  k := [2724, 2950945, 3057342, 2660594, 79598, 1]
  f := [900941, 1788286, 175717, 1092946, 1326234, 918366, 1]
  g := [1841772, 3655749, 359212, 2234283, 2711187, 1877392, 1]
  h := [1797794, 1]
  a := [3249030, 1040092, 755123, 2491544, 2077309, 2740918]
  b := [107114, 163428, 1092892, 1855842, 1875362, 934269]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![3, 3675187]
  exp := ![1, 1]
  pdgood := [3, 3675187]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp3675187.out
  a := [-29329107, -131508852, -8548846, 145325684, 18517584, -29468152]
  b := [-10088667, 6540561, 46697630, 4548790, -29317852, -3246760, 4209736]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3675187 T_ofList CD3675187

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

noncomputable def bOm : Basis (Fin 7) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 7 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 7
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 7 := T_degree

noncomputable def bQ : Basis (Fin 7) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 7) (Fin 7) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 7) :
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
          (∑ x : Fin 7,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 7,
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
        (List.ofFn fun i : Fin 7 =>
          (List.ofFn fun j : Fin 7 =>
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
      (voightPolynomialDiscriminantInput 7 row row_mem)
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

end VoightMaximalOrderD7R71

namespace VoightMaximalOrderD7R85

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨107680489, [1, -6, 3, 17, -1, -8, 0, 1], 1⟩
local notation "l" => [1, -6, 3, 17, -1, -8, 0, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSeven := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSeven_irreducible row row_mem
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
def basisNumerator : Fin 7 → Fin 7 → ℤ := ![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 7 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -17, 1, 8, 0]], ![![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -17, 1, 8, 0], ![0, -1, 6, -3, -17, 1, 8]], ![![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -17, 1, 8, 0], ![0, -1, 6, -3, -17, 1, 8], ![-8, 48, -25, -130, 5, 47, 1]], ![![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -17, 1, 8, 0], ![0, -1, 6, -3, -17, 1, 8], ![-8, 48, -25, -130, 5, 47, 1], ![-1, -2, 45, -42, -129, 13, 47]], ![![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -17, 1, 8, 0], ![0, -1, 6, -3, -17, 1, 8], ![-8, 48, -25, -130, 5, 47, 1], ![-1, -2, 45, -42, -129, 13, 47], ![-47, 281, -143, -754, 5, 247, 13]], ![![0, 0, 0, 0, 0, 0, 1], ![-1, 6, -3, -17, 1, 8, 0], ![0, -1, 6, -3, -17, 1, 8], ![-8, 48, -25, -130, 5, 47, 1], ![-1, -2, 45, -42, -129, 13, 47], ![-47, 281, -143, -754, 5, 247, 13], ![-13, 31, 242, -364, -741, 109, 247]]]
  s := ![![[], [], [], [], [], [], []], ![[], [], [], [], [], [], [-1]], ![[], [], [], [], [], [-1], [0, -1]], ![[], [], [], [], [-1], [0, -1], [-8, 0, -1]], ![[], [], [], [-1], [0, -1], [-8, 0, -1], [-1, -8, 0, -1]], ![[], [], [-1], [0, -1], [-8, 0, -1], [-1, -8, 0, -1], [-47, -1, -8, 0, -1]], ![[], [-1], [0, -1], [-8, 0, -1], [-1, -8, 0, -1], [-47, -1, -8, 0, -1], [-13, -47, -1, -8, 0, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 7 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 7) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 7) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 7) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 7 → Fin 7 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -17, 1, 8, 0]], ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -17, 1, 8, 0], [0, -1, 6, -3, -17, 1, 8]], ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -17, 1, 8, 0], [0, -1, 6, -3, -17, 1, 8], [-8, 48, -25, -130, 5, 47, 1]], ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -17, 1, 8, 0], [0, -1, 6, -3, -17, 1, 8], [-8, 48, -25, -130, 5, 47, 1], [-1, -2, 45, -42, -129, 13, 47]], ![[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -17, 1, 8, 0], [0, -1, 6, -3, -17, 1, 8], [-8, 48, -25, -130, 5, 47, 1], [-1, -2, 45, -42, -129, 13, 47], [-47, 281, -143, -754, 5, 247, 13]], ![[0, 0, 0, 0, 0, 0, 1], [-1, 6, -3, -17, 1, 8, 0], [0, -1, 6, -3, -17, 1, 8], [-8, 48, -25, -130, 5, 47, 1], [-1, -2, 45, -42, -129, 13, 47], [-47, 281, -143, -754, 5, 247, 13], [-13, 31, 242, -364, -741, 109, 247]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0] [] (by decide)

instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp2197561 : Fact (Nat.Prime 2197561) := fact_iff.2 (by norm_num)

def CD7 : CertificateDedekindCriterionLists l 7 where
  n := 2
  a' := [2, 2, 4, 2]
  b' := [0, 0, 4, 4, 1]
  k := [2, 1, 6, 1]
  f := [1, 4, 3, 2, 5, 4, 1]
  g := [4, 3, 4, 6, 3, 1]
  h := [2, 4, 1]
  a := [4, 6, 2, 4, 4]
  b := [1, 6, 6, 3, 6, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD2197561 : CertificateDedekindCriterionLists l 2197561 where
  n := 2
  a' := [1337317, 1199061, 172101, 1037962, 1749320]
  b' := [565770, 1042773, 466359, 587412, 48175, 440967]
  k := [559353, 104272, 1380153, 1913504, 671304, 1]
  f := [568410, 1701349, 1220904, 85752, 1781681, 284386, 1]
  g := [670879, 2008056, 1440999, 101210, 2102870, 335652, 1]
  h := [1861909, 1]
  a := [1323762, 496054, 1360519, 702365, 2001635, 2047873]
  b := [1292456, 928266, 1270386, 1501169, 173930, 149688]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 2
  p := ![7, 2197561]
  exp := ![1, 1]
  pdgood := [7, 2197561]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp7.out
    exact hp2197561.out
  a := [-96229085, -240220500, 73193901, 207991428, -8695617, -37483502]
  b := [-18602002, 37590333, 83778257, -15590565, -41952572, 1242231, 5354786]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2197561 T_ofList CD2197561

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

noncomputable def bOm : Basis (Fin 7) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 7 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 7
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 7 := T_degree

noncomputable def bQ : Basis (Fin 7) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 7) (Fin 7) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 7) :
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
          (∑ x : Fin 7,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 7,
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
        (List.ofFn fun i : Fin 7 =>
          (List.ofFn fun j : Fin 7 =>
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
      (voightPolynomialDiscriminantInput 7 row row_mem)
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

end VoightMaximalOrderD7R85

namespace VoightMaximalOrderD7R96

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨114477761, [1, 3, -12, 1, 14, -4, -3, 1], 1⟩
local notation "l" => [1, 3, -12, 1, 14, -4, -3, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSeven := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSeven_irreducible row row_mem
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
def basisNumerator : Fin 7 → Fin 7 → ℤ := ![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 7 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-1, -3, 12, -1, -14, 4, 3]], ![![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-1, -3, 12, -1, -14, 4, 3], ![-3, -10, 33, 9, -43, -2, 13]], ![![0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-1, -3, 12, -1, -14, 4, 3], ![-3, -10, 33, 9, -43, -2, 13], ![-13, -42, 146, 20, -173, 9, 37]], ![![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-1, -3, 12, -1, -14, 4, 3], ![-3, -10, 33, 9, -43, -2, 13], ![-13, -42, 146, 20, -173, 9, 37], ![-37, -124, 402, 109, -498, -25, 120]], ![![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 1], ![-1, -3, 12, -1, -14, 4, 3], ![-3, -10, 33, 9, -43, -2, 13], ![-13, -42, 146, 20, -173, 9, 37], ![-37, -124, 402, 109, -498, -25, 120], ![-120, -397, 1316, 282, -1571, -18, 335]], ![![0, 0, 0, 0, 0, 0, 1], ![-1, -3, 12, -1, -14, 4, 3], ![-3, -10, 33, 9, -43, -2, 13], ![-13, -42, 146, 20, -173, 9, 37], ![-37, -124, 402, 109, -498, -25, 120], ![-120, -397, 1316, 282, -1571, -18, 335], ![-335, -1125, 3623, 981, -4408, -231, 987]]]
  s := ![![[], [], [], [], [], [], []], ![[], [], [], [], [], [], [-1]], ![[], [], [], [], [], [-1], [-3, -1]], ![[], [], [], [], [-1], [-3, -1], [-13, -3, -1]], ![[], [], [], [-1], [-3, -1], [-13, -3, -1], [-37, -13, -3, -1]], ![[], [], [-1], [-3, -1], [-13, -3, -1], [-37, -13, -3, -1], [-120, -37, -13, -3, -1]], ![[], [-1], [-3, -1], [-13, -3, -1], [-37, -13, -3, -1], [-120, -37, -13, -3, -1], [-335, -120, -37, -13, -3, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 7 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 7) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 7) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 7) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 7 → Fin 7 → List ℤ := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-1, -3, 12, -1, -14, 4, 3]], ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-1, -3, 12, -1, -14, 4, 3], [-3, -10, 33, 9, -43, -2, 13]], ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-1, -3, 12, -1, -14, 4, 3], [-3, -10, 33, 9, -43, -2, 13], [-13, -42, 146, 20, -173, 9, 37]], ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-1, -3, 12, -1, -14, 4, 3], [-3, -10, 33, 9, -43, -2, 13], [-13, -42, 146, 20, -173, 9, 37], [-37, -124, 402, 109, -498, -25, 120]], ![[0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1], [-1, -3, 12, -1, -14, 4, 3], [-3, -10, 33, 9, -43, -2, 13], [-13, -42, 146, 20, -173, 9, 37], [-37, -124, 402, 109, -498, -25, 120], [-120, -397, 1316, 282, -1571, -18, 335]], ![[0, 0, 0, 0, 0, 0, 1], [-1, -3, 12, -1, -14, 4, 3], [-3, -10, 33, 9, -43, -2, 13], [-13, -42, 146, 20, -173, 9, 37], [-37, -124, 402, 109, -498, -25, 120], [-120, -397, 1316, 282, -1571, -18, 335], [-335, -1125, 3623, 981, -4408, -231, 987]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0] [] (by decide)

instance hp29 : Fact (Nat.Prime 29) := fact_iff.2 (by norm_num)
instance hp31 : Fact (Nat.Prime 31) := fact_iff.2 (by norm_num)
instance hp4391 : Fact (Nat.Prime 4391) := fact_iff.2 (by norm_num)

def CD29 : CertificateDedekindCriterionLists l 29 where
  n := 3
  a' := [15, 7, 16, 1]
  b' := [9, 1, 23, 11, 23]
  k := [5, 15, 28, 12, 9, 16, 12, 11, 1]
  f := [3, 5, 6, 6, 6, 4, 1]
  g := [22, 15, 20, 20, 22, 1]
  h := [4, 4, 1]
  a := [25, 12, 16, 27, 24]
  b := [23, 6, 16, 2, 28, 5]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD31 : CertificateDedekindCriterionLists l 31 where
  n := 2
  a' := [26, 9, 22, 8, 10]
  b' := [5, 25, 23, 26, 1, 19]
  k := [19, 27, 21, 8, 11, 1]
  f := [17, 13, 4, 21, 19, 4, 1]
  g := [22, 16, 4, 27, 24, 4, 1]
  h := [24, 1]
  a := [18, 27, 21, 10, 21, 19]
  b := [27, 1, 4, 23, 10, 12]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD4391 : CertificateDedekindCriterionLists l 4391 where
  n := 2
  a' := [2104, 1009, 1454, 139, 1879]
  b' := [1532, 620, 2444, 2063, 2702, 3346]
  k := [1797, 3724, 862, 1215, 1934, 1]
  f := [178, 32, 885, 872, 865, 884, 1]
  g := [637, 114, 3167, 3118, 3093, 3161, 1]
  h := [1227, 1]
  a := [3104, 145, 2649, 3635, 3459, 4318]
  b := [4275, 1265, 867, 1180, 1569, 73]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
  n := 3
  p := ![29, 31, 4391]
  exp := ![1, 1, 1]
  pdgood := [29, 31, 4391]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp29.out
    exact hp31.out
    exact hp4391.out
  a := [46305127, -282159000, -365189370, 297666344, 134511201, -71701098]
  b := [-14119206, -65205775, 81582304, 103318932, -57282905, -23605749, 10243014]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
    exact satisfiesDedekindCriterion_of_certificate_lists T l 31 T_ofList CD31
    exact satisfiesDedekindCriterion_of_certificate_lists T l 4391 T_ofList CD4391

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

noncomputable def bOm : Basis (Fin 7) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 7 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 7
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 7 := T_degree

noncomputable def bQ : Basis (Fin 7) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 7) (Fin 7) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 7) :
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
          (∑ x : Fin 7,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 7,
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
        (List.ofFn fun i : Fin 7 =>
          (List.ofFn fun j : Fin 7 =>
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
      (voightPolynomialDiscriminantInput 7 row row_mem)
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

end VoightMaximalOrderD7R96

end TraceEuclidean
