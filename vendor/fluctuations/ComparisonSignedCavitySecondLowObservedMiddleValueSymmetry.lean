module

public import ComparisonSignedCavitySecondLowHighDisorderPair
public import ComparisonSignedCavitySecondLowActualLowFieldDirection

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open scoped BigOperators NNReal
set_option maxHeartbeats 30000000

def nativeSecondLowObservedMiddleQQValue (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (s : T.Slot) (high : ℕ)
    (P : T.cavityLeft.Assignment → ℝ) (F G : T.cavityLeft.Assignment → Spin n) (i j : ℕ) : ℝ :=
  ((nativeHighMarkedRows T s high 0).map fun p => p.coeff *
    ((nativeHighMarkedRows p.tree (p.embed s) high 0).map fun r => r.coeff *
      (r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (fun τ =>
          let old := p.restRestrict (r.restRestrict τ)
          P old * (restLowKernel n U b h i (F old) (p.restSpin (r.restRestrict τ)) *
            restLowKernel n U b h j (G old) (r.restSpin τ))) 0 *
        fullScalarCutGamma r.tree U K (r.embed p.mark) r.mark)).sum).sum

theorem native_second_low_observed_middle_QQ_eq_original_full_pair
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (high : ℕ) (P : T.cavityLeft.Assignment → ℝ)
    (F G : T.cavityLeft.Assignment → Spin n) (i j : ℕ) :
    nativeSecondLowObservedMiddleQQValue n q U b h K T s high P F G i j =
      nativeSecondLowHighOldDependentDisorderPair (fullWeight n) (fullFeature n) T s high 0 0
        (cutFullVariance n q U 0 0 b h K)
        (fun σ => P (T.cavityAssignment σ).1)
        (fun σ => nativeSecondLowActualFieldDirection n U b h i (F (T.cavityAssignment σ).1))
        (fun σ => nativeSecondLowActualFieldDirection n U b h j (G (T.cavityAssignment σ).1)) 0 := by
  unfold nativeSecondLowObservedMiddleQQValue nativeSecondLowHighOldDependentDisorderPair
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro r _
  congr 1
  unfold fullScalarCutGamma
  rw [← cut_full_monomial_eq_retained n q U b h K r.tree ho
    (fun τ =>
      let old := p.restRestrict (r.restRestrict τ)
      P old * (restLowKernel n U b h i (F old) (p.restSpin (r.restRestrict τ)) *
        restLowKernel n U b h j (G old) (r.restSpin τ))) [r.embed p.mark,r.mark]]
  congr 1
  funext σ
  have hp := p.restSpin_actual (r.restrict σ)
  rw [r.restRestrict_actual] at hp
  simp only [p.spin_at,r.restrict_at] at hp
  have hr := r.restSpin_actual σ
  simp only [r.spin_at] at hr
  simp only [fullFeature_native_second_low_actual_field_direction,
    p.restRestrict_actual,r.restRestrict_actual,siteMonomial,p.spin_at,r.spin_at,r.restrict_at]
  rw [←hp,←hr]
  ring

theorem native_second_low_observed_middle_QQ_value_edge_order_symm
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (high : ℕ) (P : T.cavityLeft.Assignment → ℝ)
    (F G : T.cavityLeft.Assignment → Spin n) (i j : ℕ) :
    nativeSecondLowObservedMiddleQQValue n q U b h K T s high P F G i j =
      nativeSecondLowObservedMiddleQQValue n q U b h K T s high P G F j i := by
  rw [native_second_low_observed_middle_QQ_eq_original_full_pair n q U b h K T ho,
    native_second_low_observed_middle_QQ_eq_original_full_pair n q U b h K T ho]
  exact native_second_low_high_old_dependent_disorder_pair_symm (fullWeight_pos n)
    (fullFeature n) T s high 0 ho 0 (cutFullVariance n q U 0 0 b h K) _ _ _ 0

def nativeSecondLowObservedMiddleQQKKValue (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (s : T.Slot) (high : ℕ)
    (P : T.cavityLeft.Assignment → ℝ) (F G : T.cavityLeft.Assignment → Spin n) (i j : ℕ) : ℝ :=
  ((nativeHighMarkedRows T s high 0).map fun p => p.coeff *
    ((nativeHighMarkedRows p.tree (p.embed s) high 0).map fun r => r.coeff *
      (r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
        (fun τ =>
          let old := p.restRestrict (r.restRestrict τ)
          P old * (restLowKernel n U b h i (F old) (p.restSpin (r.restRestrict τ)) *
            restLowKernel n U b h j (G old) (r.restSpin τ) -
              (if i < U then K i else 0) * (if j < U then K j else 0))) 0 *
        fullScalarCutGamma r.tree U K (r.embed p.mark) r.mark)).sum).sum

private theorem native_second_low_middle_rest_expect_difference
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) (P F : T.Assignment → ℝ) (c : ℝ) :
    T.disorderExpect (restWeight n) (restFeature n) 0 q (fun σ => P σ * (F σ-c)) 0 =
      T.disorderExpect (restWeight n) (restFeature n) 0 q (fun σ => P σ * F σ) 0 -
        c * T.disorderExpect (restWeight n) (restFeature n) 0 q P 0 := by
  unfold ClockTree.disorderExpect
  simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  ring

private theorem native_second_low_middle_list_sub {α : Type*} (L : List α) (F G : α → ℝ) :
    (L.map (fun z => F z-G z)).sum = (L.map F).sum-(L.map G).sum := by
  induction L with
  | nil => simp
  | cons z L ih => simp only [List.map_cons,List.sum_cons,ih]; ring

theorem native_second_low_observed_middle_QQKK_eq_QQ_sub_scalar_baseline
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
    (s : T.Slot) (high : ℕ) (P : T.cavityLeft.Assignment → ℝ)
    (F G : T.cavityLeft.Assignment → Spin n) (i j : ℕ) :
    nativeSecondLowObservedMiddleQQKKValue n q U b h K T s high P F G i j =
      nativeSecondLowObservedMiddleQQValue n q U b h K T s high P F G i j -
        ((nativeHighMarkedRows T s high 0).map fun p => p.coeff *
          ((nativeHighMarkedRows p.tree (p.embed s) high 0).map fun r => r.coeff *
            (((if i < U then K i else 0) * (if j < U then K j else 0)) *
              r.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
                (fun τ => P (p.restRestrict (r.restRestrict τ))) 0 *
              fullScalarCutGamma r.tree U K (r.embed p.mark) r.mark)).sum).sum := by
  unfold nativeSecondLowObservedMiddleQQKKValue nativeSecondLowObservedMiddleQQValue
  simp_rw [native_second_low_middle_rest_expect_difference]
  simp_rw [sub_mul,mul_sub,native_second_low_middle_list_sub]
  simp_rw [mul_sub,native_second_low_middle_list_sub]

theorem native_second_low_observed_middle_QQKK_value_edge_order_symm
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (high : ℕ) (P : T.cavityLeft.Assignment → ℝ)
    (F G : T.cavityLeft.Assignment → Spin n) (i j : ℕ) :
    nativeSecondLowObservedMiddleQQKKValue n q U b h K T s high P F G i j =
      nativeSecondLowObservedMiddleQQKKValue n q U b h K T s high P G F j i := by
  rw [native_second_low_observed_middle_QQKK_eq_QQ_sub_scalar_baseline,
    native_second_low_observed_middle_QQKK_eq_QQ_sub_scalar_baseline,
    native_second_low_observed_middle_QQ_value_edge_order_symm n q U b h K T ho]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro r _
  ring

theorem native_second_low_constant_middle_QQKK_value_edge_order_symm
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (high : ℕ) (F G : T.cavityLeft.Assignment → Spin n) (i j : ℕ) :
    nativeSecondLowObservedMiddleQQKKValue n q U b h K T s high (fun _ => 1) F G i j =
      nativeSecondLowObservedMiddleQQKKValue n q U b h K T s high (fun _ => 1) G F j i :=
  native_second_low_observed_middle_QQKK_value_edge_order_symm n q U b h K T ho s high (fun _ => 1) F G i j

end OAI.SKFluctuations.Cavity
