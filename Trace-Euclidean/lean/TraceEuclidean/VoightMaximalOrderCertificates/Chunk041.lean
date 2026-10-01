import TraceEuclidean.VoightMaximalOrderCertificates.Chunk037
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

namespace VoightMaximalOrderD6R290

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨7997584, [-2, -4, 12, 5, -7, -1, 1], 2⟩
local notation "l" => [-2, -4, 12, 5, -7, -1, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSix := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSix_irreducible row row_mem
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
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![2, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 2, 0], ![0, 0, 0, 1, 0, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, -1, 0, 2], ![1, 2, -6, -3, 4, 1]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, -1, 0, 2], ![2, 4, -12, -6, 7, 2], ![1, 3, -4, -13, 1, 9]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, -1, 0, 2], ![2, 4, -12, -6, 7, 2], ![2, 6, -8, -25, 2, 16], ![9, 19, -51, -32, 23, 11]], ![![0, 0, 0, 0, 1, 0], ![0, 0, 0, -1, 0, 2], ![2, 4, -12, -6, 7, 2], ![2, 6, -8, -25, 2, 16], ![16, 34, -90, -58, 39, 20], ![11, 31, -47, -107, 12, 57]], ![![0, 0, 0, 0, 0, 1], ![1, 2, -6, -3, 4, 1], ![1, 3, -4, -13, 1, 9], ![9, 19, -51, -32, 23, 11], ![11, 31, -47, -107, 12, 57], ![33, 72, -181, -131, 72, 46]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-2]], ![[], [], [], [], [-4], [-2, -2]], ![[], [], [], [-4], [-4, -4], [-18, -2, -2]], ![[], [], [-4], [-4, -4], [-32, -4, -4], [-22, -18, -2, -2]], ![[], [-2], [-2, -2], [-18, -2, -2], [-22, -18, -2, -2], [-66, -12, -10, -1, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 6 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 6) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 6) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 6) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, -1, 0, 2], [1, 2, -6, -3, 4, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, -1, 0, 2], [2, 4, -12, -6, 7, 2], [1, 3, -4, -13, 1, 9]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, -1, 0, 2], [2, 4, -12, -6, 7, 2], [2, 6, -8, -25, 2, 16], [9, 19, -51, -32, 23, 11]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, -1, 0, 2], [2, 4, -12, -6, 7, 2], [2, 6, -8, -25, 2, 16], [16, 34, -90, -58, 39, 20], [11, 31, -47, -107, 12, 57]], ![[0, 0, 0, 0, 0, 1], [1, 2, -6, -3, 4, 1], [1, 3, -4, -13, 1, 9], [9, 19, -51, -32, 23, 11], [11, 31, -47, -107, 12, 57], [33, 72, -181, -131, 72, 46]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp101 : Fact (Nat.Prime 101) := fact_iff.2 (by norm_num)

def CD7 : CertificateDedekindCriterionLists l 7 where
  n := 2
  a' := [1]
  b' := [6, 5]
  k := [5, 5, 1]
  f := [1, 4, 2, 3, 3, 1]
  g := [5, 4, 5, 2, 1]
  h := [1, 4, 1]
  a := [6, 0, 0, 5]
  b := [6, 3, 6, 2, 2]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD101 : CertificateDedekindCriterionLists l 101 where
  n := 2
  a' := [58, 6, 95]
  b' := [10, 46, 24, 52]
  k := [15, 36, 1]
  f := [10, 38, 64, 60, 23, 1]
  g := [24, 73, 98, 68, 1]
  h := [42, 32, 1]
  a := [45, 4, 39, 72]
  b := [36, 28, 4, 70, 29]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 3
  p := ![2, 7, 101]
  exp := ![2, 1, 1]
  pdgood := [7, 101]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp7.out
    exact hp101.out
  a := [-1154, -768, 2157, 320, -564]
  b := [-130, 758, 288, -583, -69, 94]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T l 101 T_ofList CD101

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
  m := 4
  n := 2
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 1, 0, 1, 1, 1]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0], [1, 1, 1, 0, 1, 1]], ![[0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 1, 1, 1, 0, 1]], ![[0, 0, 0, 0, 0, 1], [1, 0, 0, 1, 0, 1], [1, 1, 0, 1, 1, 1], [1, 1, 1, 0, 1, 1], [1, 1, 1, 1, 0, 1], [1, 0, 1, 1, 0, 0]]]
  hTMod := by decide
  hle := by decide
  b1 := ![![0, 1, 1, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 1]]
  b2 := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0]]
  v := ![![0, 1, 1, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 1, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 1]]
  w := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0]]
  v_ind := ![2, 3, 4, 5]
  w_ind := ![0, 4]
  hmod1 := by decide
  hmod2 := by decide
  hindv := by decide
  hindw := by decide
  hvFrobKer := by decide
  hwFrobComp := by decide
  g := ![![1, 0, 0, 0, 0, 0], ![0, 0, 1, 1, 1, 1], ![1, 1, 0, 0, 0, 1], ![1, 1, 1, 1, 1, 1], ![0, 0, 1, 1, 0, 0], ![0, 0, 0, 1, 1, 0]]
  a := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]], ![![-22, -23, 14, 16], ![-77, -67, 37, 34], ![-163, -199, 65, 98], ![-282, -282, 109, 124]], ![![-8, -15, 5, 10], ![-56, -34, 28, 12], ![-52, -111, 17, 60], ![-187, -134, 76, 49]], ![![-20, -22, 14, 16], ![-76, -66, 38, 34], ![-162, -200, 66, 100], ![-288, -285, 113, 126]], ![![0, 0, 2, 2], ![-12, -6, 8, 4], ![-20, -30, 10, 18], ![-54, -44, 24, 20]], ![![-12, -8, 8, 6], ![-20, -32, 10, 20], ![-98, -84, 42, 38], ![-98, -138, 36, 68]]]
  c := ![![![0, 0], ![0, 0], ![0, 0], ![0, 0]], ![![-6, 20], ![-10, 69], ![-33, 187], ![-35, 290]], ![![-4, 12], ![-1, 42], ![-24, 90], ![-7, 160]], ![![-6, 19], ![-10, 68], ![-34, 187], ![-35, 294]], ![![-1, -1], ![-1, 7], ![-7, 25], ![-5, 48]], ![![-2, 8], ![-8, 26], ![-10, 90], ![-24, 125]]]
  d := ![![![0, 0, 0, 0], ![0, 0, 0, 0]], ![![2, 2, 2, 2], ![-12, -6, 10, 6]], ![![0, 0, 0, 2], ![-10, -6, 8, 2]], ![![2, 2, 2, 2], ![-10, -6, 10, 6]], ![![2, 2, 0, 0], ![0, 2, 2, 0]], ![![0, 2, 2, 0], ![0, -2, 2, 4]]]
  e := ![![![1, 0], ![0, 1]], ![![-1, -3], ![-2, 6]], ![![0, 1], ![0, 7]], ![![0, -2], ![-2, 6]], ![![0, -2], ![0, -2]], ![![0, -2], ![-2, 0]]]
  ab_ind := ![(Sum.inl 0, Sum.inl 0), (Sum.inl 1, Sum.inl 0), (Sum.inl 3, Sum.inl 0), (Sum.inl 3, Sum.inl 1), (Sum.inl 0, Sum.inr 0), (Sum.inl 3, Sum.inr 1)]
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

noncomputable def bOm : Basis (Fin 6) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 6 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 6
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 6 := T_degree

noncomputable def bQ : Basis (Fin 6) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 6) :
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
          (∑ x : Fin 6,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 6,
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
        (List.ofFn fun i : Fin 6 =>
          (List.ofFn fun j : Fin 6 =>
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
      (voightPolynomialDiscriminantInput 6 row row_mem)
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

end VoightMaximalOrderD6R290

namespace VoightMaximalOrderD6R294

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨8098573, [-29, -37, 32, 19, -11, -2, 1], 27⟩
local notation "l" => [-29, -37, 32, 19, -11, -2, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSix := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSix_irreducible row row_mem
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

def basisDenominator : ℤ := 9
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![9, 0, 0, 0, 0, 0], ![0, 9, 0, 0, 0, 0], ![0, 0, 9, 0, 0, 0], ![0, 0, 0, 9, 0, 0], ![3, 3, 0, 0, 3, 0], ![5, 6, 7, 6, 2, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-1, -1, 0, 0, 3, 0], ![-1, -1, -2, -2, -2, 3], ![0, 1, -6, -4, 3, 4]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![-1, -1, 0, 0, 3, 0], ![-3, -4, -7, -6, -6, 9], ![4, 6, -15, -10, 7, 6], ![1, 5, -29, -28, -6, 25]], ![![0, 0, 0, 1, 0, 0], ![-1, -1, 0, 0, 3, 0], ![-3, -4, -7, -6, -6, 9], ![12, 18, -46, -31, 21, 18], ![3, 13, -44, -53, -26, 45], ![34, 60, -133, -117, 3, 82]], ![![0, 0, 0, 0, 1, 0], ![-1, -1, -2, -2, -2, 3], ![4, 6, -15, -10, 7, 6], ![3, 13, -44, -53, -26, 45], ![26, 42, -69, -58, 9, 35], ![38, 77, -148, -157, -36, 114]], ![![0, 0, 0, 0, 0, 1], ![0, 1, -6, -4, 3, 4], ![1, 5, -29, -28, -6, 25], ![34, 60, -133, -117, 3, 82], ![38, 77, -148, -157, -36, 114], ![113, 210, -387, -380, -44, 265]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-9]], ![[], [], [], [], [-27], [-36, -9]], ![[], [], [], [-81], [-54, -27], [-225, -36, -9]], ![[], [], [-27], [-54, -27], [-135, -18, -9], [-249, -75, -12, -3]], ![[], [-9], [-36, -9], [-225, -36, -9], [-249, -75, -12, -3], [-685, -163, -39, -6, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 6 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 6) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 6) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 6) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [-1, -1, 0, 0, 3, 0], [-1, -1, -2, -2, -2, 3], [0, 1, -6, -4, 3, 4]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [-1, -1, 0, 0, 3, 0], [-3, -4, -7, -6, -6, 9], [4, 6, -15, -10, 7, 6], [1, 5, -29, -28, -6, 25]], ![[0, 0, 0, 1, 0, 0], [-1, -1, 0, 0, 3, 0], [-3, -4, -7, -6, -6, 9], [12, 18, -46, -31, 21, 18], [3, 13, -44, -53, -26, 45], [34, 60, -133, -117, 3, 82]], ![[0, 0, 0, 0, 1, 0], [-1, -1, -2, -2, -2, 3], [4, 6, -15, -10, 7, 6], [3, 13, -44, -53, -26, 45], [26, 42, -69, -58, 9, 35], [38, 77, -148, -157, -36, 114]], ![[0, 0, 0, 0, 0, 1], [0, 1, -6, -4, 3, 4], [1, 5, -29, -28, -6, 25], [34, 60, -133, -117, 3, 82], [38, 77, -148, -157, -36, 114], [113, 210, -387, -380, -44, 265]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp7 : Fact (Nat.Prime 7) := fact_iff.2 (by norm_num)
instance hp3373 : Fact (Nat.Prime 3373) := fact_iff.2 (by norm_num)

def CD7 : CertificateDedekindCriterionLists l 7 where
  n := 3
  a' := [4]
  b' := [3, 5]
  k := [1]
  f := [5, 11, -1, -1, 3, 1]
  g := [6, 4, 1]
  h := [1, 6, 0, 1, 1]
  a := [3, 4]
  b := [0, 4, 1, 1, 3]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD3373 : CertificateDedekindCriterionLists l 3373 where
  n := 2
  a' := [2424, 720, 2164, 3254]
  b' := [1797, 894, 493, 1206, 1373]
  k := [2219, 2693, 2597, 2618, 1]
  f := [389, 1558, 372, 2054, 801, 1]
  g := [636, 2547, 607, 3358, 1308, 1]
  h := [2063, 1]
  a := [1484, 2258, 679, 962, 3277]
  b := [572, 2971, 1934, 961, 96]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
  n := 3
  p := ![3, 7, 3373]
  exp := ![3, 1, 1]
  pdgood := [7, 3373]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp3.out
    exact hp7.out
    exact hp3373.out
  a := [-166349, 162234, 368514, -11218, -57072]
  b := [113152, 234915, -14284, -102204, -1301, 9512]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3373 T_ofList CD3373

noncomputable def M3 : MaximalOrderCertificateOfUnramifiedLists 3 O Om hm where
  n := 6
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [2, 2, 0, 0, 0, 0], [2, 2, 1, 1, 1, 0], [0, 1, 0, 2, 0, 1]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [2, 2, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0], [1, 0, 0, 2, 1, 0], [1, 2, 1, 2, 0, 1]], ![[0, 0, 0, 1, 0, 0], [2, 2, 0, 0, 0, 0], [0, 2, 2, 0, 0, 0], [0, 0, 2, 2, 0, 0], [0, 1, 1, 1, 1, 0], [1, 0, 2, 0, 0, 1]], ![[0, 0, 0, 0, 1, 0], [2, 2, 1, 1, 1, 0], [1, 0, 0, 2, 1, 0], [0, 1, 1, 1, 1, 0], [2, 0, 0, 2, 0, 2], [2, 2, 2, 2, 0, 0]], ![[0, 0, 0, 0, 0, 1], [0, 1, 0, 2, 0, 1], [1, 2, 1, 2, 0, 1], [1, 0, 2, 0, 0, 1], [2, 2, 2, 2, 0, 0], [2, 0, 0, 1, 1, 1]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 2, 2, 0, 0], ![0, 1, 2, 1, 0, 0], ![1, 0, 0, 0, 1, 0], ![2, 2, 1, 0, 1, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [3]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 3 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M3
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [3] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 6) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 6 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 6
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 6 := T_degree

noncomputable def bQ : Basis (Fin 6) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 6) :
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
          (∑ x : Fin 6,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 6,
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
        (List.ofFn fun i : Fin 6 =>
          (List.ofFn fun j : Fin 6 =>
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
      (voightPolynomialDiscriminantInput 6 row row_mem)
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

end VoightMaximalOrderD6R294

namespace VoightMaximalOrderD6R295

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨8142201, [-8, -12, 12, 15, -6, -3, 1], 8⟩
local notation "l" => [-8, -12, 12, 15, -6, -3, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSix := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSix_irreducible row row_mem
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

def basisDenominator : ℤ := 4
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![4, 0, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0], ![0, 0, 4, 0, 0, 0], ![0, 0, 0, 4, 0, 0], ![0, 2, 0, 2, 2, 0], ![0, 0, 3, 2, 1, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, -1, 0, -1, 2, 0], ![0, 0, -1, -1, 0, 2], ![2, 2, -6, -6, 2, 4]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, -1, 0, -1, 2, 0], ![0, 1, -3, -1, -2, 4], ![4, 5, -12, -12, 2, 8], ![8, 16, -24, -26, -4, 20]], ![![0, 0, 0, 1, 0, 0], ![0, -1, 0, -1, 2, 0], ![0, 1, -3, -1, -2, 4], ![8, 9, -21, -24, 6, 12], ![16, 32, -45, -50, -8, 36], ![40, 74, -100, -114, -12, 72]], ![![0, 0, 0, 0, 1, 0], ![0, 0, -1, -1, 0, 2], ![4, 5, -12, -12, 2, 8], ![16, 32, -45, -50, -8, 36], ![44, 85, -111, -127, -18, 83], ![93, 187, -226, -263, -47, 170]], ![![0, 0, 0, 0, 0, 1], ![2, 2, -6, -6, 2, 4], ![8, 16, -24, -26, -4, 20], ![40, 74, -100, -114, -12, 72], ![93, 187, -226, -263, -47, 170], ![194, 393, -455, -538, -101, 339]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-4]], ![[], [], [], [], [-8], [-16, -4]], ![[], [], [], [-16], [-32, -8], [-80, -16, -4]], ![[], [], [-8], [-32, -8], [-88, -20, -4], [-186, -48, -10, -2]], ![[], [-4], [-16, -4], [-80, -16, -4], [-186, -48, -10, -2], [-388, -103, -26, -5, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 6 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 6) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 6) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 6) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, -1, 0, -1, 2, 0], [0, 0, -1, -1, 0, 2], [2, 2, -6, -6, 2, 4]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, -1, 0, -1, 2, 0], [0, 1, -3, -1, -2, 4], [4, 5, -12, -12, 2, 8], [8, 16, -24, -26, -4, 20]], ![[0, 0, 0, 1, 0, 0], [0, -1, 0, -1, 2, 0], [0, 1, -3, -1, -2, 4], [8, 9, -21, -24, 6, 12], [16, 32, -45, -50, -8, 36], [40, 74, -100, -114, -12, 72]], ![[0, 0, 0, 0, 1, 0], [0, 0, -1, -1, 0, 2], [4, 5, -12, -12, 2, 8], [16, 32, -45, -50, -8, 36], [44, 85, -111, -127, -18, 83], [93, 187, -226, -263, -47, 170]], ![[0, 0, 0, 0, 0, 1], [2, 2, -6, -6, 2, 4], [8, 16, -24, -26, -4, 20], [40, 74, -100, -114, -12, 72], [93, 187, -226, -263, -47, 170], [194, 393, -455, -538, -101, 339]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp17 : Fact (Nat.Prime 17) := fact_iff.2 (by norm_num)
instance hp73 : Fact (Nat.Prime 73) := fact_iff.2 (by norm_num)

def CD3 : CertificateDedekindCriterionLists l 3 where
  n := 3
  a' := [1]
  b' := [0, 1]
  k := [1]
  f := [3, 4, -3, -5, 3, 1]
  g := [1, 0, 1]
  h := [1, 0, 2, 0, 1]
  a := [0, 2]
  b := [1, 0, 0, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD17 : CertificateDedekindCriterionLists l 17 where
  n := 2
  a' := [8, 9, 7, 4]
  b' := [11, 6, 8, 0, 6]
  k := [4, 12, 14, 11, 1]
  f := [4, 4, 9, 3, 3, 1]
  g := [6, 5, 16, 5, 4, 1]
  h := [10, 1]
  a := [15, 5, 2, 8, 2]
  b := [10, 1, 2, 11, 15]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD73 : CertificateDedekindCriterionLists l 73 where
  n := 2
  a' := [13, 29, 6, 62]
  b' := [37, 26, 25, 36, 46]
  k := [4, 54, 60, 46, 1]
  f := [8, 12, 8, 5, 10, 1]
  g := [48, 68, 44, 28, 58, 1]
  h := [12, 1]
  a := [26, 5, 4]
  b := [47, 41, 69]
  c := [32]
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
  n := 4
  p := ![2, 3, 17, 73]
  exp := ![3, 2, 1, 1]
  pdgood := [3, 17, 73]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp3.out
    exact hp17.out
    exact hp73.out
  a := [59697, -229215, 46905, 88311, -27930]
  b := [-47244, -1375, 77727, -15587, -17046, 4655]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
    exact satisfiesDedekindCriterion_of_certificate_lists T l 17 T_ofList CD17
    exact satisfiesDedekindCriterion_of_certificate_lists T l 73 T_ofList CD73

noncomputable def M2 : MaximalOrderCertificateOfUnramifiedLists 2 O Om hm where
  n := 6
  t := 3
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0], [0, 0, 1, 1, 0, 0], [0, 0, 0, 0, 0, 0]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]], ![[0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0], [0, 1, 1, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0]], ![[0, 0, 0, 0, 1, 0], [0, 0, 1, 1, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 1, 1, 1, 0, 1], [1, 1, 0, 1, 1, 0]], ![[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [1, 1, 0, 1, 1, 0], [0, 1, 1, 0, 1, 1]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [2]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 2 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M2
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [2] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 6) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 6 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 6
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 6 := T_degree

noncomputable def bQ : Basis (Fin 6) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 6) :
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
          (∑ x : Fin 6,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 6,
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
        (List.ofFn fun i : Fin 6 =>
          (List.ofFn fun j : Fin 6 =>
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
      (voightPolynomialDiscriminantInput 6 row row_mem)
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

end VoightMaximalOrderD6R295

namespace VoightMaximalOrderD6R298

open Polynomial Module BigOperators Classical Matrix

noncomputable section

def row : VoightPolynomialRow := ⟨8248384, [2, -6, -2, 14, -5, -3, 1], 3⟩
local notation "l" => [2, -6, -2, 14, -5, -3, 1]
noncomputable def T : ℤ[X] := row.polynomial
lemma T_ofList : ofList l = T := by rfl
lemma row_mem : row ∈ voightPolynomialRowsSix := by native_decide
lemma T_irreducible : Irreducible T :=
  voightPolynomialRowsSix_irreducible row row_mem
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

def basisDenominator : ℤ := 3
def basisNumerator : Fin 6 → Fin 6 → ℤ := ![![3, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0], ![0, 0, 0, 3, 0, 0], ![0, 0, 0, 0, 3, 0], ![2, 1, 0, 2, 2, 1]]

noncomputable def BQ : SubalgebraBuilderLists 6 ℤ ℚ K T l where
  d := basisDenominator
  hlen := rfl
  htr := rfl
  hofL := T_ofList.symm
  hm := rfl
  B := basisNumerator
  a := ![![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-2, -1, 0, -2, -2, 3], ![-4, 1, 1, -8, -1, 5]], ![![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-2, -1, 0, -2, -2, 3], ![-8, 3, 2, -20, -1, 9], ![-18, 2, 6, -37, -11, 22]], ![![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![-2, -1, 0, -2, -2, 3], ![-8, 3, 2, -20, -1, 9], ![-34, 2, 12, -68, -27, 42], ![-66, 15, 24, -148, -37, 77]], ![![0, 0, 0, 0, 1, 0], ![-2, -1, 0, -2, -2, 3], ![-8, 3, 2, -20, -1, 9], ![-34, 2, 12, -68, -27, 42], ![-114, 35, 44, -270, -56, 129], ![-234, 48, 92, -518, -151, 274]], ![![0, 0, 0, 0, 0, 1], ![-4, 1, 1, -8, -1, 5], ![-18, 2, 6, -37, -11, 22], ![-66, 15, 24, -148, -37, 77], ![-234, 48, 92, -518, -151, 274], ![-466, 106, 185, -1046, -289, 542]]]
  s := ![![[], [], [], [], [], []], ![[], [], [], [], [], [-3]], ![[], [], [], [], [-9], [-15, -3]], ![[], [], [], [-9], [-27, -9], [-66, -15, -3]], ![[], [], [-9], [-27, -9], [-126, -27, -9], [-231, -66, -15, -3]], ![[], [-3], [-15, -3], [-66, -15, -3], [-231, -66, -15, -3], [-473, -131, -34, -7, -1]]]
  h := Adj
  honed := by decide
  hd := by norm_num [basisDenominator]
  hcc := by decide
  hin := by decide
  hsymma := by decide
  hc_le := by decide

lemma T_degree : T.natDegree = 6 := (SubalgebraBuilderOfList T l BQ).hdeg

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K
noncomputable def O : Subalgebra ℤ K := subalgebraOfBuilderLists T l BQ
def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)
noncomputable def B' : Basis (Fin 6) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)
instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 6) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ
lemma timesTableO_basis_apply (i : Fin 6) :
    ((timesTableO.basis i).val : K) =
      Adj.map (C (algebraMap ℤ ℚ basisDenominator)⁻¹ *
        map (algebraMap ℤ ℚ)
          (ofList (List.ofFn (basisNumerator i)))) := by
  exact basisOfBuilderLists_apply T l BQ i
def Table : Fin 6 → Fin 6 → List ℤ := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-2, -1, 0, -2, -2, 3], [-4, 1, 1, -8, -1, 5]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-2, -1, 0, -2, -2, 3], [-8, 3, 2, -20, -1, 9], [-18, 2, 6, -37, -11, 22]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [-2, -1, 0, -2, -2, 3], [-8, 3, 2, -20, -1, 9], [-34, 2, 12, -68, -27, 42], [-66, 15, 24, -148, -37, 77]], ![[0, 0, 0, 0, 1, 0], [-2, -1, 0, -2, -2, 3], [-8, 3, 2, -20, -1, 9], [-34, 2, 12, -68, -27, 42], [-114, 35, 44, -270, -56, 129], [-234, 48, 92, -518, -151, 274]], ![[0, 0, 0, 0, 0, 1], [-4, 1, 1, -8, -1, 5], [-18, 2, 6, -37, -11, 22], [-66, 15, 24, -148, -37, 77], [-234, 48, 92, -518, -151, 274], [-466, 106, 185, -1046, -289, 542]]]
lemma timesTableO_eq_Table : ∀ i j, Table i j = List.ofFn (timesTableO.table i j) := by
  decide
lemma hroot_mem : θ ∈ O := by
  exact root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0] [] (by decide)

instance hp2 : Fact (Nat.Prime 2) := fact_iff.2 (by norm_num)
instance hp3 : Fact (Nat.Prime 3) := fact_iff.2 (by norm_num)
instance hp359 : Fact (Nat.Prime 359) := fact_iff.2 (by norm_num)

def CD2 : CertificateDedekindCriterionLists l 2 where
  n := 4
  a' := [1]
  b' := [1, 1]
  k := [1, 1, 0, 1, 0, 1, 1]
  f := [-1, 3, 1, -7, 3, 2]
  g := [0, 1, 1, 1]
  h := [0, 0, 0, 1]
  a := [1, 0, 1]
  b := [1, 1, 0, 1]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

def CD359 : CertificateDedekindCriterionLists l 359 where
  n := 2
  a' := [183, 226, 96]
  b' := [263, 221, 308, 335]
  k := [298, 61, 1]
  f := [18, 212, 302, 161, 27, 1]
  g := [202, 314, 173, 29, 1]
  h := [32, 327, 1]
  a := [175, 51, 305, 83]
  b := [235, 328, 331, 220, 276]
  c := []
  hdvdpow := rfl
  hcop := rfl
  hf := by rfl
  habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
  n := 3
  p := ![2, 3, 359]
  exp := ![2, 2, 1]
  pdgood := [2, 359]
  hsub := by decide
  hp := by
    intro i
    fin_cases i
    exact hp2.out
    exact hp3.out
    exact hp359.out
  a := [-53466, -143032, 141061, 62142, -32160]
  b := [-19976, 19106, 55305, -33965, -13037, 5360]
  hab := by decide
  hd := by
    intro q hq
    fin_cases hq
    exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
    exact satisfiesDedekindCriterion_of_certificate_lists T l 359 T_ofList CD359

noncomputable def M3 : MaximalOrderCertificateOfUnramifiedLists 3 O Om hm where
  n := 6
  t := 2
  hpos := by decide
  TT := timesTableO
  B' := B'
  T := Table
  heq := timesTableO_eq_Table
  TMod := ![![[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]], ![[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 2, 0, 1, 1, 0], [2, 1, 1, 1, 2, 2]], ![[0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 2, 0, 1, 1, 0], [1, 0, 2, 1, 2, 0], [0, 2, 0, 2, 1, 1]], ![[0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [1, 2, 0, 1, 1, 0], [1, 0, 2, 1, 2, 0], [2, 2, 0, 1, 0, 0], [0, 0, 0, 2, 2, 2]], ![[0, 0, 0, 0, 1, 0], [1, 2, 0, 1, 1, 0], [1, 0, 2, 1, 2, 0], [2, 2, 0, 1, 0, 0], [0, 2, 2, 0, 1, 0], [0, 0, 2, 1, 2, 1]], ![[0, 0, 0, 0, 0, 1], [2, 1, 1, 1, 2, 2], [0, 2, 0, 2, 1, 1], [0, 0, 0, 2, 2, 2], [0, 0, 2, 1, 2, 1], [2, 1, 2, 1, 2, 2]]]
  hTMod := by decide
  hle := by decide
  w := ![![1, 0, 0, 0, 0, 0], ![1, 2, 2, 0, 1, 0], ![0, 2, 0, 1, 1, 0], ![1, 0, 1, 2, 2, 0], ![0, 2, 2, 1, 2, 0], ![1, 0, 1, 1, 2, 1]]
  wFrob := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]
  w_ind := ![0, 1, 2, 3, 4, 5]
  hindw := by decide
  hwFrobComp := by decide

theorem candidate_order_eq_integralClosure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro q hq
  by_cases hbad : q ∈ [3]
  · fin_cases hbad
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 3 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M3
  · haveI : Fact (Nat.Prime q) := fact_iff.2 hq
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int
      Adj T_monic hm ?_ hroot_mem
      (satisfiesDedekindAlmostAllLists_of_certificate T l T_ofList [3] D q hq hbad)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

noncomputable def bOm : Basis (Fin 6) ℤ (NumberField.RingOfIntegers K) :=
  timesTableO.basis.map
    (Subalgebra.equivOfEq O Om candidate_order_eq_integralClosure).toLinearEquiv

lemma bOm_discr : Algebra.discr ℤ bOm = NumberField.discr K :=
  NumberField.discr_eq_discr K bOm

noncomputable def pb : PowerBasis ℚ K :=
  AdjoinRoot.powerBasis hirr.out.ne_zero

lemma pb_dim : pb.dim = 6 := by
  change (map (algebraMap ℤ ℚ) T).natDegree = 6
  calc
    (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree :=
      T_monic.natDegree_map (algebraMap ℤ ℚ)
    _ = 6 := T_degree

noncomputable def bQ : Basis (Fin 6) ℚ K :=
  pb.basis.reindex (finCongr pb_dim)

lemma pb_gen : pb.gen = Adj.root := by
  unfold pb
  rw [AdjoinRoot.powerBasis_gen]
  exact (AdjoinRoot.isAdjoinRoot_root_eq_root
    (map (algebraMap ℤ ℚ) T)).symm

def P : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j => (basisNumerator j i : ℚ) / (basisDenominator : ℚ)

lemma bQ_apply (i : Fin 6) :
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
          (∑ x : Fin 6,
            Adj.map (C ((algebraMap ℤ ℚ) (basisNumerator j x)) * X ^ (x : ℕ))) =
        ∑ x : Fin 6,
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
        (List.ofFn fun i : Fin 6 =>
          (List.ofFn fun j : Fin 6 =>
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
      (voightPolynomialDiscriminantInput 6 row row_mem)
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

end VoightMaximalOrderD6R298

end TraceEuclidean
