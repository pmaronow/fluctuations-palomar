module

public import ComparisonSignedCavitySecondLowEntryFourBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open scoped BigOperators
variable {S : Type} {as : List PositiveMass} {T : ClockTree S as}
set_option maxHeartbeats 30000000

theorem native_second_low_marked_list_profile_abs_le
    (ps : List (MarkedPlacement T)) (F R : MarkedPlacement T → ℝ)
    (hF : ∀p∈ps,|F p| ≤ R p) :
    |(ps.map (fun p=>p.coeff*F p)).sum| ≤ (ps.map (fun p=>|p.coeff| * R p)).sum := by
  induction ps with
  | nil=>simp
  | cons p ps ih=>
    simp only [List.map_cons,List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add
      (by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hF p List.mem_cons_self) (abs_nonneg _))
      (ih (fun q hq=>hF q (List.mem_cons_of_mem p hq))))

theorem native_second_low_first_entry_four_average_profile_abs_le
    (T : ClockTree S as) (U : ℕ) (ho : MassOrdered 0 as)
    {rBound : ℕ} (hT : T.leaves ≤ rBound)
    (F : (p : MarkedPlacement T) → (r : MarkedPlacement p.tree) →
      (s : MarkedPlacement r.tree) → MarkedPlacement s.tree → ℝ)
    (R : MarkedPlacement T → ℝ) (hR : ∀p∈T.markedAttach 0,0 ≤ R p)
    {D : ℝ} (hD : 0 ≤ D)
    (hF : ∀p∈T.markedAttach 0,∀r∈p.tree.markedAttach 0,
      ∀s∈r.tree.markedAttach 0,∀t∈s.tree.markedAttach 0,|F p r s t| ≤ D*R p) :
    |nativeSecondLowEntryFourAverage T U true F| ≤
      2*(rBound+1)*(rBound+2)*(rBound+3)*D*
        ((nativeSecondLowUnobservedEntryRows T U 0).map (fun p=>|p.coeff| * R p)).sum := by
  let B:ℝ:=2*(rBound+2)*(rBound+3)*D
  let A:ℝ:=2*(rBound+1)*B
  have hB:0 ≤ B:=by dsimp [B];positivity
  have hA:0 ≤ A:=by dsimp [A];positivity
  have Hr (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
      |OAI.SKFluctuations.Cavity.nativeSecondLowDoubleAverage r.tree (F p r)| ≤ B*R p := by
    have Hleaves:r.tree.leaves ≤ rBound+2:=by
      have HP:=T.markedAttach_leaves 0 p hp
      have HR:=p.tree.markedAttach_leaves 0 r hr
      omega
    convert marked_pair_weight_abs_le r.tree ho Hleaves (F p r)
      (mul_nonneg hD (hR p hp)) (hF p hp r hr) using 1
    · rfl
    · dsimp [B];push_cast;ring
  let inner:=fun p : MarkedPlacement T=>((p.tree.markedAttach 0).map (fun r=>r.coeff*
    OAI.SKFluctuations.Cavity.nativeSecondLowDoubleAverage r.tree (F p r))).sum
  have Hinner (p : MarkedPlacement T) (hp : p∈T.markedAttach 0):|inner p| ≤ A*R p:=by
    have H:=marked_list_weight_abs_le (p.tree.markedAttach 0) _ (Hr p hp)
    have Hleaf:(p.tree.leaves:ℝ) ≤ rBound+1:=by
      exact_mod_cast (T.markedAttach_leaves 0 p hp).trans (Nat.add_le_add_right hT 1)
    rw [p.tree.markedAttach_variation ho] at H
    apply H.trans
    have HH:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hleaf (by norm_num : (0:ℝ) ≤ 2))
      (mul_nonneg hB (hR p hp))
    convert HH using 1 <;> (try dsimp [A]) <;> ring
  have Houter:=native_second_low_marked_list_profile_abs_le (nativeSecondLowUnobservedEntryRows T U 0)
    inner (fun p=>A*R p) (fun p hp=>Hinner p ((mem_nativeSecondLowUnobservedEntryRows T U 0 p).mp hp).1)
  have HE:((nativeSecondLowUnobservedEntryRows T U 0).map (fun p=>|p.coeff| * (A*R p))).sum=
      A*((nativeSecondLowUnobservedEntryRows T U 0).map (fun p=>|p.coeff| * R p)).sum:=by
    have Hfun:(fun p : MarkedPlacement T=>|p.coeff| * (A*R p))=
        (fun p : MarkedPlacement T=>A*(|p.coeff| * R p)):=by funext p;ring
    rw [Hfun,List.sum_map_mul_left]
  rw [HE] at Houter
  unfold nativeSecondLowEntryFourAverage
  simp only [nativeSecondLowBudgetEntryRows,ite_true,Bool.not_true,Bool.false_eq_true,ite_false]
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (div_le_div_of_nonneg_right Houter (by norm_num)).trans_eq
  dsimp [A,B]
  ring

theorem native_second_low_second_entry_four_average_profile_abs_le
    (T : ClockTree S as) (U : ℕ) (ho : MassOrdered 0 as)
    {rBound : ℕ} (hT : T.leaves ≤ rBound)
    (F : (p : MarkedPlacement T) → (r : MarkedPlacement p.tree) →
      (s : MarkedPlacement r.tree) → MarkedPlacement s.tree → ℝ)
    (R : (p : MarkedPlacement T) → MarkedPlacement p.tree → ℝ)
    (allowed : MarkedPlacement T → Prop)
    (hR : ∀p∈T.markedAttach 0,∀r∈p.tree.markedAttach 0,0 ≤ R p r)
    {D C : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hF : ∀p∈T.markedAttach 0,allowed p → ∀r∈p.tree.markedAttach 0,
      ∀s∈r.tree.markedAttach 0,∀t∈s.tree.markedAttach 0,|F p r s t| ≤ D*R p r)
    (hzero : ∀p∈T.markedAttach 0,¬allowed p → ∀r∈p.tree.markedAttach 0,
      ∀s∈r.tree.markedAttach 0,∀t∈s.tree.markedAttach 0,F p r s t=0)
    (hcost : ∀p∈T.markedAttach 0,allowed p →
      ((nativeSecondLowUnobservedEntryRows p.tree U 0).map (fun r=>|r.coeff| * R p r)).sum ≤ C) :
    |nativeSecondLowEntryFourAverage T U false F| ≤
      2*rBound*(rBound+2)*(rBound+3)*D*C := by
  classical
  let B:ℝ:=2*(rBound+2)*(rBound+3)*D
  have hB:0 ≤ B:=by dsimp [B];positivity
  let inner:=fun p : MarkedPlacement T=>((nativeSecondLowUnobservedEntryRows p.tree U 0).map (fun r=>r.coeff*
    OAI.SKFluctuations.Cavity.nativeSecondLowDoubleAverage r.tree (F p r))).sum
  have Hinner (p : MarkedPlacement T) (hp : p∈T.markedAttach 0):|inner p| ≤ B*C:=by
    have Hleaves (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0):r.tree.leaves ≤ rBound+2:=by
      have HP:=T.markedAttach_leaves 0 p hp
      have HR:=p.tree.markedAttach_leaves 0 r hr
      omega
    by_cases HA : allowed p
    · have Hr (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0):
          |OAI.SKFluctuations.Cavity.nativeSecondLowDoubleAverage r.tree (F p r)| ≤ B*R p r:=by
        convert marked_pair_weight_abs_le r.tree ho (Hleaves r hr) (F p r)
          (mul_nonneg hD (hR p hp r hr)) (hF p hp HA r hr) using 1
        · rfl
        · dsimp [B];push_cast;ring
      have HH:=native_second_low_marked_list_profile_abs_le (nativeSecondLowUnobservedEntryRows p.tree U 0)
        _ (fun r=>B*R p r) (fun r hr=>Hr r ((mem_nativeSecondLowUnobservedEntryRows p.tree U 0 r).mp hr).1)
      have HE:((nativeSecondLowUnobservedEntryRows p.tree U 0).map (fun r=>|r.coeff| * (B*R p r))).sum=
          B*((nativeSecondLowUnobservedEntryRows p.tree U 0).map (fun r=>|r.coeff| * R p r)).sum:=by
        have Hfun:(fun r : MarkedPlacement p.tree=>|r.coeff| * (B*R p r))=
            (fun r : MarkedPlacement p.tree=>B*(|r.coeff| * R p r)):=by funext r;ring
        rw [Hfun,List.sum_map_mul_left]
      rw [HE] at HH
      exact HH.trans (mul_le_mul_of_nonneg_left (hcost p hp HA) hB)
    · have Hr (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0):
          |OAI.SKFluctuations.Cavity.nativeSecondLowDoubleAverage r.tree (F p r)| ≤ (0:ℝ):=by
        have HH:=marked_pair_weight_abs_le r.tree ho (Hleaves r hr) (F p r) (D:=0) le_rfl (by
          intro s hs t ht
          rw [hzero p hp HA r hr s hs t ht,abs_zero])
        simpa only [OAI.SKFluctuations.Cavity.nativeSecondLowDoubleAverage,mul_zero] using HH
      have HH:=marked_list_weight_abs_le (nativeSecondLowUnobservedEntryRows p.tree U 0) _
        (fun r hr=>Hr r ((mem_nativeSecondLowUnobservedEntryRows p.tree U 0 r).mp hr).1)
      simp only [mul_zero] at HH
      exact HH.trans (mul_nonneg hB hC)
  have Houter:=marked_list_weight_abs_le (T.markedAttach 0) inner Hinner
  rw [T.markedAttach_variation ho] at Houter
  simp only [sub_zero] at Houter
  have Hleaf:(T.leaves:ℝ) ≤ rBound:=Nat.cast_le.mpr hT
  have Hbound:=Houter.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left Hleaf (by norm_num : (0:ℝ) ≤ 2)) (mul_nonneg hB hC))
  unfold nativeSecondLowEntryFourAverage
  simp only [nativeSecondLowBudgetEntryRows,Bool.false_eq_true,ite_false,Bool.not_false,ite_true]
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (div_le_div_of_nonneg_right Hbound (by norm_num)).trans_eq
  dsimp [B]
  ring

end OAI.SKFluctuations.Hierarchy.ClockTree
