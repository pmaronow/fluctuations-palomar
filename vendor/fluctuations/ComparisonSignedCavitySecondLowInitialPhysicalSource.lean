module

public import ComparisonSignedCavitySecondLowJointWordBudget
public import ComparisonSignedCavitySmallCutAtomicKernels

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
open scoped BigOperators NNReal
set_option maxHeartbeats 30000000

theorem native_second_low_raw_rest_eq_small_cut_moving_one
    (n U : ℕ) (b h K : ℕ → ℝ) :
    restLowKernel n U b h = nativeSmallCutMovingRestKernel n U b h K 1 := by
  funext j σ τ
  unfold restLowKernel nativeSmallCutMovingRestKernel
  split_ifs <;> simp [deletedOverlap,joinSpin]

theorem native_second_low_scalar_eq_small_cut_moving_zero
    (n U : ℕ) (b h K : ℕ → ℝ) (j : ℕ) (σ τ : Spin n) :
    nativeSecondLowScalarValue U K j = nativeSmallCutMovingRestKernel n U b h K 0 j σ τ := by
  unfold nativeSecondLowScalarValue nativeSmallCutMovingRestKernel
  split_ifs <;> simp

theorem native_second_low_error_eq_small_cut_old_error
    (n U : ℕ) (b h K : ℕ → ℝ) :
    nativeSecondLowErrorKernel n U b h K = nativeSmallCutOldErrorRestKernel n U b h K := by
  funext j σ τ
  unfold nativeSecondLowErrorKernel nativeSmallCutOldErrorRestKernel restLowKernel nativeSecondLowScalarValue
  split_ifs <;> simp [deletedOverlap,joinSpin]

def nativeSecondLowPhysicalQQKKPayload (n U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
    (P : T.cavityLeft.Assignment → ℝ) (a z f c e d : T.Slot) (σ : T.Assignment) : ℝ :=
  P (T.cavityAssignment σ).1 *
    (restLowKernel n U b h (T.splitIndex f c) (T.atSlot σ f).1 (T.atSlot σ c).1 *
      restLowKernel n U b h (T.splitIndex e d) (T.atSlot σ e).1 (T.atSlot σ d).1 -
      nativeSecondLowScalarValue U K (T.splitIndex f c) *
        nativeSecondLowScalarValue U K (T.splitIndex e d)) *
    siteMonomial T σ [a,z,f,c,e,d]

theorem native_second_low_physical_QQKK_eq_two_initial_products
    (n U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (P : T.cavityLeft.Assignment → ℝ)
    (a z f c e d : T.Slot) :
    nativeSecondLowPhysicalQQKKPayload n U b h K T P a z f c e d =
      fun σ =>
        nativeOldInitialRowProduct n T P (nativeSmallCutOldErrorRestKernel n U b h K) f c
          (fun k : Fin 2 => nativeSmallCutOrdinaryRestKernel n U b h K (![false,true] k) (![1,0] k))
          ![e,a] ![d,z] σ +
        nativeOldInitialRowProduct n T P (nativeSmallCutOldErrorRestKernel n U b h K) e d
          (fun k : Fin 2 => nativeSmallCutOrdinaryRestKernel n U b h K (![false,true] k) (![0,0] k))
          ![f,a] ![c,z] σ := by
  funext σ
  unfold nativeSecondLowPhysicalQQKKPayload
  rw [←native_second_low_error_eq_small_cut_old_error]
  simp only [nativeOldInitialRowProduct,nativeRestRowKernel,Fin.prod_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  simp only [nativeSmallCutOrdinaryRestKernel,Bool.false_eq_true,ite_false,ite_true]
  simp_rw [←native_second_low_raw_rest_eq_small_cut_moving_one n U b h K,
    ←native_second_low_scalar_eq_small_cut_moving_zero n U b h K]
  simp only [nativeSecondLowErrorKernel,siteMonomial]
  ring

theorem native_second_low_physical_QQKK_expect_eq_two_initial_products
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
    (P : T.cavityLeft.Assignment → ℝ) (a z f c e d : T.Slot) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
      (nativeSecondLowPhysicalQQKKPayload n U b h K T P a z f c e d) 0 =
      T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
        (nativeOldInitialRowProduct n T P (nativeSmallCutOldErrorRestKernel n U b h K) f c
          (fun k : Fin 2 => nativeSmallCutOrdinaryRestKernel n U b h K (![false,true] k) (![1,0] k))
          ![e,a] ![d,z]) 0 +
      T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
        (nativeOldInitialRowProduct n T P (nativeSmallCutOldErrorRestKernel n U b h K) e d
          (fun k : Fin 2 => nativeSmallCutOrdinaryRestKernel n U b h K (![false,true] k) (![0,0] k))
          ![f,a] ![c,z]) 0 := by
  rw [native_second_low_physical_QQKK_eq_two_initial_products]
  simp only [ClockTree.disorderExpect,mul_add,Finset.sum_add_distrib]

theorem native_second_low_joint_word_eq_original_physical_payload
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment → ℝ) (a z : T.Slot)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (hs : s ∈ r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t ∈ s.tree.markedAttach 0) :
    nativeSecondLowWordValue n q U b h K P a z p r s t =
      t.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
        (nativeSecondLowPhysicalQQKKPayload n U b h K t.tree (nativeSecondLowOldTest P p r s t)
          (t.embed (s.embed (r.embed (p.embed a)))) (t.embed (s.embed (r.embed (p.embed z))))
          (t.embed (s.embed (r.embed p.mark))) (t.embed (s.embed r.mark)) (t.embed s.mark) t.mark) 0 := by
  unfold nativeSecondLowWordValue
  rw [←cut_full_monomial_eq_retained n q U b h K t.tree ho]
  congr 1
  funext σ
  rw [native_second_low_joint_rest_test_final_slots n U b h K P p r s hs t ht]
  simp only [nativeSecondLowPhysicalQQKKPayload,insertedSiteSlots,
    List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    t.tree.atSlot_cavityLeft]

end OAI.SKFluctuations.Cavity
