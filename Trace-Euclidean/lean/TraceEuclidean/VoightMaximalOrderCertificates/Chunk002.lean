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

namespace VoightMaximalOrderD5R197

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨595792, [-8, 6, 10, -6, -2, 1], 2⟩
local notation "l" => [-8, 6, 10, -6, -2, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsFive := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsFive_irreducible row row_mem
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

def basisDenominator : ℤ := 2
def basisNumerator : Fin 5 → Fin 5 → ℤ := ![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 2], ![4, -3, -5, 3, 2]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 2], ![8, -6, -10, 6, 4], ![8, -2, -13, 1, 10]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 2], ![8, -6, -10, 6, 4], ![16, -4, -26, 2, 20], ![40, -22, -52, 17, 22]], ![![0, 0, 0, 0, 1], ![4, -3, -5, 3, 2], ![8, -2, -13, 1, 10], ![40, -22, -52, 17, 22], ![44, -13, -66, 7, 39]]]
  s := ![![[], [], [], [], []], ![[], [], [], [], [-2]], ![[], [], [], [-4], [-4, -2]], ![[], [], [-4], [-8, -4], [-20, -4, -2]], ![[], [-2], [-4, -2], [-20, -4, -2], [-22, -10, -2, -1]]]
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
def Table : Fin 5 → Fin 5 → List ℤ := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 2], [4, -3, -5, 3, 2]], ![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 2], [8, -6, -10, 6, 4], [8, -2, -13, 1, 10]], ![[0, 0, 0, 1, 0], [0, 0, 0, 0, 2], [8, -6, -10, 6, 4], [16, -4, -26, 2, 20], [40, -22, -52, 17, 22]], ![[0, 0, 0, 0, 1], [4, -3, -5, 3, 2], [8, -2, -13, 1, 10], [40, -22, -52, 17, 22], [44, -13, -66, 7, 39]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp23 : Fact (Nat.Prime 23) := fact_iff.2 (by norm_num)
instance hp1619 : Fact (Nat.Prime 1619) := fact_iff.2 (by norm_num)

def CD23 : CertificateDedekindCriterionLists l 23 where
  n := 2
  a' := [2, 21, 6]
  b' := [18, 9, 0, 10]
  k := [14, 14, 20, 1]
  f := [4, 11, 1, 5, 1]
  g := [7, 21, 1, 9, 1]
  h := [12, 1]
  a := [1, 3, 4, 10]
  b := [16, 21, 13, 13]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD1619 : CertificateDedekindCriterionLists l 1619 where
  n := 2
  a' := [1169, 1450, 1241]
  b' := [1039, 562, 1449, 904]
  k := [980, 309, 498, 1]
  f := [920, 1220, 400, 210, 1]
  g := [1088, 1442, 472, 248, 1]
  h := [1369, 1]
  a := [1363, 766, 1452, 1101]
  b := [462, 1271, 1530, 518]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 3
  p := ![2, 23, 1619]
  exp := ![2, 1, 1]
  pdgood := [23, 1619]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp23.out
    exact hp1619.out
  a := [5308, 94140, 14825, -26500]
  b := [31902, 13872, -33754, -5085, 5300]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 23 T_ofList CD23
    exact satisfiesDedekindCriterion_of_certificate_lists T l 1619 T_ofList CD1619

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 3
  n := 2
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 0], [0, 1, 1, 1, 0]], ![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 1, 1, 0]], ![[0, 0, 0, 1, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 1, 0]], ![[0, 0, 0, 0, 1], [0, 1, 1, 1, 0], [0, 0, 1, 1, 0], [0, 0, 0, 1, 0], [0, 1, 0, 1, 1]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]]
  b2 := ![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 1]]
  v := ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]]
  w := ![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 1]]
  wFrob := ![![1, 0, 0, 0, 0], ![0, 1, 1, 1, 1]]
  v_ind := ![1, 2, 3]
  w_ind := ![0, 1]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![0, 1, 1, 1, 1], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 1, 1, 1, 1], ![0, 0, 0, 1, 0]]
  a := ![![![-3, -4, 4], ![-8, -23, 8], ![-32, -88, 25]], ![![0, 1, 0], ![0, 0, 1], ![0, 0, 0]], ![![0, 0, 1], ![0, 0, 0], ![-6, -10, 6]], ![![-2, -4, 4], ![-8, -22, 8], ![-32, -88, 26]], ![![0, 0, 0], ![-6, -10, 6], ![-4, -26, 2]]]
  c := ![![![2, 2], ![8, 8], ![32, 24]], ![![0, 0], ![0, 0], ![0, 1]], ![![0, 0], ![0, 1], ![4, 2]], ![![2, 2], ![8, 8], ![32, 24]], ![![0, 1], ![4, 2], ![8, 10]]]
  d := ![![![2, 2, 2], ![-80, -272, 56]], ![![2, 0, 0], ![-6, -10, 6]], ![![0, 2, 0], ![-4, -26, 2]], ![![2, 2, 2], ![-80, -272, 56]], ![![0, 0, 2], ![-44, -104, 34]]]
  e := ![![![0, 1], ![96, 73]], ![![0, 0], ![4, 2]], ![![0, 0], ![8, 10]], ![![1, 1], ![96, 74]], ![![0, 0], ![40, 22]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 0, Sum.inl 1), (Sum.inl 0, Sum.inl 2), (Sum.inr 0, Sum.inr 0), (Sum.inl 0, Sum.inr 1)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [2]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 2 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M2
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2] D q hq hbad)
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
    have hcheck :
        (List.ofFn fun i : Fin 5 =>
          (List.ofFn fun j : Fin 5 =>
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
      (voightPolynomialDiscriminantInput 5 row row_mem)
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

end VoightMaximalOrderD5R197

namespace VoightMaximalOrderD5R200

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨600268, [-4, 6, 6, -7, -1, 1], 2⟩
local notation "l" => [-4, 6, 6, -7, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsFive := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsFive_irreducible row row_mem
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

def basisDenominator : ℤ := 2
def basisNumerator : Fin 5 → Fin 5 → ℤ := ![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 1, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, -1, -1, 2], ![2, -3, -4, 3, 2]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, -1, -1, 2], ![4, -6, -7, 6, 2], ![4, -4, -14, -1, 10]], ![![0, 0, 0, 1, 0], ![0, 0, -1, -1, 2], ![4, -6, -7, 6, 2], ![4, -2, -20, -7, 16], ![20, -26, -43, 17, 18]], ![![0, 0, 0, 0, 1], ![2, -3, -4, 3, 2], ![4, -4, -14, -1, 10], ![20, -26, -43, 17, 18], ![30, -32, -86, 5, 49]]]
  s := ![![[], [], [], [], []], ![[], [], [], [], [-2]], ![[], [], [], [-4], [-4, -2]], ![[], [], [-4], [-4, -4], [-20, -4, -2]], ![[], [-2], [-4, -2], [-20, -4, -2], [-30, -13, -3, -1]]]
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
def Table : Fin 5 → Fin 5 → List ℤ := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, -1, -1, 2], [2, -3, -4, 3, 2]], ![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, -1, -1, 2], [4, -6, -7, 6, 2], [4, -4, -14, -1, 10]], ![[0, 0, 0, 1, 0], [0, 0, -1, -1, 2], [4, -6, -7, 6, 2], [4, -2, -20, -7, 16], [20, -26, -43, 17, 18]], ![[0, 0, 0, 0, 1], [2, -3, -4, 3, 2], [4, -4, -14, -1, 10], [20, -26, -43, 17, 18], [30, -32, -86, 5, 49]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp150067 : Fact (Nat.Prime 150067) := fact_iff.2 (by norm_num)

def CD150067 : CertificateDedekindCriterionLists l 150067 where
  n := 2
  a' := [143451, 17778, 4320]
  b' := [4865, 87532, 85695, 148987]
  k := [147529, 77537, 14340, 1]
  f := [18370, 41456, 21916, 37174, 1]
  g := [40622, 91672, 48462, 82203, 1]
  h := [67863, 1]
  a := [6018, 95682, 96874, 76405]
  b := [147763, 109683, 57896, 73662]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 2
  p := ![2, 150067]
  exp := ![2, 1]
  pdgood := [150067]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp150067.out
  a := [84149, 637137, 11577, -163415]
  b := [156144, 28321, -223706, -8852, 32683]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 150067 T_ofList CD150067

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 1
  n := 4
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 1, 0], [0, 1, 0, 1, 0]], ![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0]], ![[0, 0, 0, 1, 0], [0, 0, 1, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 1, 0]], ![[0, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 0, 1, 0], [0, 0, 1, 1, 0], [0, 0, 0, 1, 1]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 1, 1, 1, 0]]
  b2 := ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 0, 1]]
  v := ![![0, 1, 1, 1, 0]]
  w := ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 0, 1]]
  wFrob := ![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]
  v_ind := ![3]
  w_ind := ![0, 2, 3, 4]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1], ![0, 1, 1, 1, 0], ![0, 1, 0, 1, 0], ![0, 0, 0, 1, 0]]
  a := ![![![-1]], ![![20]], ![![4]], ![![-2]], ![![-2]]]
  c := ![![![4, 10, -23, 10]], ![![13, 14, -55, 15]], ![![6, 11, -33, 13]], ![![4, 10, -24, 11]], ![![4, 10, -23, 10]]]
  d := ![![![2], ![-2], ![10], ![44]], ![![0], ![6], ![4], ![14]], ![![2], ![0], ![12], ![50]], ![![2], ![-2], ![12], ![52]], ![![2], ![-2], ![10], ![44]]]
  e := ![![![1, 0, -1, 0], ![0, 2, -2, 2], ![4, 2, -16, 4], ![24, 19, -95, 23]], ![![1, 0, -1, 1], ![2, 2, -9, 2], ![6, 11, -31, 12], ![36, 65, -172, 62]], ![![0, 0, 0, 0], ![0, 0, -2, 2], ![4, 2, -20, 6], ![30, 30, -130, 36]], ![![0, 1, -1, 0], ![0, 0, -1, 2], ![4, 1, -17, 4], ![26, 19, -104, 24]], ![![0, 0, -1, 0], ![0, 1, -2, 2], ![4, 2, -17, 4], ![24, 19, -95, 22]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 0, Sum.inr 1), (Sum.inr 0, Sum.inr 1), (Sum.inr 1, Sum.inr 1)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [2]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 2 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M2
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2] D q hq hbad)
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
    have hcheck :
        (List.ofFn fun i : Fin 5 =>
          (List.ofFn fun j : Fin 5 =>
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
      (voightPolynomialDiscriminantInput 5 row row_mem)
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

end VoightMaximalOrderD5R200

namespace VoightMaximalOrderD5R204

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨609872, [-3, 7, 8, -8, -1, 1], 4⟩
local notation "l" => [-3, 7, 8, -8, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsFive := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsFive_irreducible row row_mem
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

def basisDenominator : ℤ := 2
def basisNumerator : Fin 5 → Fin 5 → ℤ := ![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![1, 1, 1, 1, 0], ![1, 0, 0, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-1, -1, -1, 2, 0], ![-1, 0, 0, 1, 1], ![-3, -7, -8, 8, 1]], ![![0, 0, 1, 0, 0], ![-1, -1, -1, 2, 0], ![-1, 0, 0, 0, 2], ![-4, -8, -8, 9, 2], ![-3, -2, -7, 0, 9]], ![![0, 0, 0, 1, 0], ![-1, 0, 0, 1, 1], ![-4, -8, -8, 9, 2], ![-6, -9, -12, 10, 7], ![-13, -34, -41, 33, 10]], ![![0, 0, 0, 0, 1], ![-3, -7, -8, 8, 1], ![-3, -2, -7, 0, 9], ![-13, -34, -41, 33, 10], ![-9, -8, -32, -2, 34]]]
  s := ![![[], [], [], [], []], ![[], [], [], [], [-2]], ![[], [], [], [-2], [-2, -2]], ![[], [], [-2], [-3, -1], [-11, -2, -1]], ![[], [-2], [-2, -2], [-11, -2, -1], [-9, -9, -1, -1]]]
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
def Table : Fin 5 → Fin 5 → List ℤ := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [-1, -1, -1, 2, 0], [-1, 0, 0, 1, 1], [-3, -7, -8, 8, 1]], ![[0, 0, 1, 0, 0], [-1, -1, -1, 2, 0], [-1, 0, 0, 0, 2], [-4, -8, -8, 9, 2], [-3, -2, -7, 0, 9]], ![[0, 0, 0, 1, 0], [-1, 0, 0, 1, 1], [-4, -8, -8, 9, 2], [-6, -9, -12, 10, 7], [-13, -34, -41, 33, 10]], ![[0, 0, 0, 0, 1], [-3, -7, -8, 8, 1], [-3, -2, -7, 0, 9], [-13, -34, -41, 33, 10], [-9, -8, -32, -2, 34]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp47 : Fact (Nat.Prime 47) := fact_iff.2 (by norm_num)
instance hp811 : Fact (Nat.Prime 811) := fact_iff.2 (by norm_num)

def CD47 : CertificateDedekindCriterionLists l 47 where
  n := 2
  a' := [32, 4, 39]
  b' := [25, 44, 34, 2]
  k := [35, 27, 0, 1]
  f := [3, 22, 14, 12, 1]
  g := [6, 45, 27, 23, 1]
  h := [23, 1]
  a := [46, 42, 22, 10]
  b := [32, 9, 41, 37]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD811 : CertificateDedekindCriterionLists l 811 where
  n := 2
  a' := [159, 282, 41]
  b' := [132, 382, 165, 598]
  k := [114, 168, 15, 1]
  f := [703, 389, 48, 7, 1]
  g := [710, 392, 48, 7, 1]
  h := [803, 1]
  a := [336, 615, 359, 19]
  b := [532, 196, 452, 792]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 3
  p := ![2, 47, 811]
  exp := ![2, 1, 1]
  pdgood := [47, 811]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp47.out
    exact hp811.out
  a := [-16483, 67881, 3174, -16455]
  b := [14717, 11936, -24507, -1293, 3291]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 47 T_ofList CD47
    exact satisfiesDedekindCriterion_of_certificate_lists T l 811 T_ofList CD811

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 4
  n := 1
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 1, 1, 0, 0], [1, 0, 0, 1, 1], [1, 1, 0, 0, 1]], ![[0, 0, 1, 0, 0], [1, 1, 1, 0, 0], [1, 0, 0, 0, 0], [0, 0, 0, 1, 0], [1, 0, 1, 0, 1]], ![[0, 0, 0, 1, 0], [1, 0, 0, 1, 1], [0, 0, 0, 1, 0], [0, 1, 0, 0, 1], [1, 0, 1, 1, 0]], ![[0, 0, 0, 0, 1], [1, 1, 0, 0, 1], [1, 0, 1, 0, 1], [1, 0, 1, 1, 0], [1, 0, 0, 0, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0]]
  v := ![![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0]]
  v_ind := ![1, 2, 3, 4]
  w_ind := ![0]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 1, 1, 0, 0], ![1, 0, 0, 0, 1], ![1, 0, 1, 0, 0]]
  a := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![0, 0, 2, 1], ![-8, -8, 10, 2], ![-9, -12, 10, 7], ![-34, -41, 34, 10]], ![![0, 1, 2, 0], ![0, 0, 2, 2], ![-8, -8, 10, 3], ![-8, -14, 8, 10]], ![![-6, -8, 8, 2], ![-2, -6, 0, 10], ![-34, -41, 34, 10], ![-8, -32, -2, 36]], ![![0, 0, 2, 0], ![0, 2, 0, 2], ![-8, -8, 10, 2], ![-2, -6, 0, 10]]]
  c := ![![![0], ![0], ![0], ![0]], ![![-1], ![5], ![4], ![26]], ![![-1], ![-2], ![4], ![3]], ![![5], ![-2], ![26], ![-2]], ![![0], ![-2], ![5], ![-2]]]
  d := ![![![0, 0, 0, 0]], ![![0, 0, 2, 0]], ![![2, 2, 0, 0]], ![![0, 0, 0, 2]], ![![0, 2, 0, 0]]]
  e := ![![![1]], ![![0]], ![![-2]], ![![0]], ![![0]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 2, Sum.inl 0), (Sum.inl 0, Sum.inl 1), (Sum.inl 2, Sum.inl 1), (Sum.inl 2, Sum.inr 0)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [2]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 2 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M2
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2] D q hq hbad)
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
    have hcheck :
        (List.ofFn fun i : Fin 5 =>
          (List.ofFn fun j : Fin 5 =>
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
      (voightPolynomialDiscriminantInput 5 row row_mem)
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

end VoightMaximalOrderD5R204

namespace VoightMaximalOrderD5R207

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨617072, [-4, 12, 6, -8, -1, 1], 4⟩
local notation "l" => [-4, 12, 6, -8, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsFive := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsFive_irreducible row row_mem
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

def basisDenominator : ℤ := 2
def basisNumerator : Fin 5 → Fin 5 → ℤ := ![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 1, 1, 0], ![0, 0, 0, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, -1, 2, 0], ![0, 0, 0, 0, 1], ![2, -6, -6, 6, 2]], ![![0, 0, 1, 0, 0], ![0, 0, -1, 2, 0], ![0, 0, 1, -2, 2], ![2, -6, -6, 6, 2], ![4, -10, -12, 0, 10]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1], ![2, -6, -6, 6, 2], ![3, -8, -9, 3, 6], ![12, -33, -35, 18, 15]], ![![0, 0, 0, 0, 1], ![2, -6, -6, 6, 2], ![4, -10, -12, 0, 10], ![12, -33, -35, 18, 15], ![30, -78, -88, 20, 48]]]
  s := ![![[], [], [], [], []], ![[], [], [], [], [-2]], ![[], [], [], [-2], [-4, -2]], ![[], [], [-2], [-3, -1], [-12, -3, -1]], ![[], [-2], [-4, -2], [-12, -3, -1], [-30, -12, -3, -1]]]
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
def Table : Fin 5 → Fin 5 → List ℤ := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, -1, 2, 0], [0, 0, 0, 0, 1], [2, -6, -6, 6, 2]], ![[0, 0, 1, 0, 0], [0, 0, -1, 2, 0], [0, 0, 1, -2, 2], [2, -6, -6, 6, 2], [4, -10, -12, 0, 10]], ![[0, 0, 0, 1, 0], [0, 0, 0, 0, 1], [2, -6, -6, 6, 2], [3, -8, -9, 3, 6], [12, -33, -35, 18, 15]], ![[0, 0, 0, 0, 1], [2, -6, -6, 6, 2], [4, -10, -12, 0, 10], [12, -33, -35, 18, 15], [30, -78, -88, 20, 48]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp38567 : Fact (Nat.Prime 38567) := fact_iff.2 (by norm_num)

def CD38567 : CertificateDedekindCriterionLists l 38567 where
  n := 2
  a' := [4527, 14669, 31172]
  b' := [30626, 9608, 25567, 30774]
  k := [24154, 27107, 31560, 1]
  f := [3091, 2546, 927, 3185, 1]
  g := [34031, 28021, 10198, 35063, 1]
  h := [3503, 1]
  a := [16058, 14033, 14341, 3539]
  b := [28398, 29099, 31993, 35028]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 2
  p := ![2, 38567]
  exp := ![3, 1]
  pdgood := [38567]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp38567.out
  a := [-6532, 73026, 4929, -20805]
  b := [23534, 7340, -28389, -1818, 4161]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 38567 T_ofList CD38567

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 2
  n := 3
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 1], [0, 0, 0, 0, 0]], ![[0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]], ![[0, 0, 0, 1, 0], [0, 0, 0, 0, 1], [0, 0, 0, 0, 0], [1, 0, 1, 1, 0], [0, 1, 1, 0, 1]], ![[0, 0, 0, 0, 1], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 1, 1, 0, 1], [0, 0, 0, 0, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 1, 1, 0, 0], ![0, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 1, 0, 1, 0]]
  v := ![![0, 1, 1, 0, 0], ![0, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 1, 0, 1, 0]]
  wFrob := ![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0]]
  v_ind := ![2, 4]
  w_ind := ![0, 2, 3]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0], ![0, 0, 1, 1, 1], ![0, 1, 1, 0, 0], ![0, 0, 1, 0, 1], ![0, 0, 1, 0, 0]]
  a := ![![![1, 0], ![0, 1]], ![![-24, 17], ![-135, 73]], ![![0, 2], ![-18, 12]], ![![-18, 14], ![-100, 58]], ![![0, 2], ![-12, 10]]]
  c := ![![![0, 0, 0], ![0, 0, 0]], ![![-2, -5, 6], ![4, -12, 19]], ![![-1, -1, 1], ![0, -2, 3]], ![![0, -2, 3], ![7, -4, 10]], ![![0, 0, 0], ![2, 1, 0]]]
  d := ![![![0, 0], ![0, 0], ![0, 0]], ![![2, 2], ![-14, 6], ![-112, 54]], ![![2, 0], ![0, 0], ![-10, 6]], ![![2, 2], ![-14, 4], ![-94, 40]], ![![2, 0], ![-2, 0], ![-12, 4]]]
  e := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]], ![![-1, -2, 1], ![-6, -7, 8], ![-17, -33, 36]], ![![0, 0, 0], ![-2, -2, 2], ![-6, -8, 8]], ![![0, -1, 0], ![-6, -7, 8], ![-16, -30, 32]], ![![0, -1, 0], ![-2, -1, 2], ![-6, -8, 8]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 0, Sum.inr 0), (Sum.inl 1, Sum.inr 0), (Sum.inl 1, Sum.inr 1)]
  hindab := by decide
  hmul1 := by decide
  hmul2 := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [2]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateLists K 2 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M2
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2] D q hq hbad)
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
    have hcheck :
        (List.ofFn fun i : Fin 5 =>
          (List.ofFn fun j : Fin 5 =>
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
      (voightPolynomialDiscriminantInput 5 row row_mem)
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

end VoightMaximalOrderD5R207

end TraceEuclidean
