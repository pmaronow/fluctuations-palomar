module

public import ComparisonNativeActualInheritedHistoryGeometry
public import ComparisonSignedCavityMinimumSourceClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 6000000
namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem inverse_radius_le_regular_cap
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    M.R u ≤ M.z+u/cl := by
  have hr:=comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u
  by_cases hz : M.z ≤ M.R u
  · have H:=(M.regular (M.R u) ⟨hz,hr.2⟩).1
    change cl*M.R u ≤ M.alpha.val.val (M.R u) at H
    rw [comparisonSweepQuantile_spec M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha hu] at H
    have H': M.R u ≤ u/cl := (le_div_iff₀ hcl).mpr (by nlinarith only [H])
    linarith [M.hz.1]
  · exact (not_le.mp hz).le.trans (le_add_of_nonneg_right (div_nonneg hu.1 hcl.le))

theorem comparison_field_le_regular_cap
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u ≤
      M.lam*M.z+(M.lam/cl)*u := by
  have hr:=(comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u).1
  have H:=mul_le_mul_of_nonneg_right (laplaceComparisonStrength_le M.context.d M.hlam.le (M.R u)) hr
  have H':=mul_le_mul_of_nonneg_left (M.inverse_radius_le_regular_cap hcl hu) M.hlam.le
  apply H.trans
  convert H' using 1; ring

def actualHistoryStrengthSum
    (ps : List (NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)) : ℝ :=
  (ps.map (fun P=>P.lam)).sum

def actualHistoryRegularCapSum
    (ps : List (NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)) : ℝ :=
  (ps.map (fun P=>P.lam*P.z)).sum

theorem actual_history_field_le_regular_caps
    (ps : List (NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock))
    (hcl : 0 < cl) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    historyFieldAddition (ps.map (fun P=>P.toHistoryTerm)) u ≤
      actualHistoryRegularCapSum ps+(actualHistoryStrengthSum ps/cl)*u := by
  induction ps with
  | nil => simp [historyFieldAddition,actualHistoryRegularCapSum,actualHistoryStrengthSum]
  | cons P ps ih =>
    have H:=add_le_add (P.comparison_field_le_regular_cap hcl hu) ih
    change P.toHistoryTerm.fieldAddition u+_ ≤ _ at H
    simpa only [List.map_cons,historyFieldAddition,actualHistoryRegularCapSum,actualHistoryStrengthSum,
      List.sum_cons,List.map_cons,add_div,add_mul,add_assoc,add_left_comm,add_comm] using H

theorem actual_history_matrix_reduction_zero
    (ps : List (NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)) :
    historyMatrixReduction (ps.map (fun P=>P.toHistoryTerm)) 0=actualHistoryStrengthSum ps := by
  induction ps with
  | nil => rfl
  | cons P ps ih =>
    have hR : P.R 0=0:=comparisonSweepQuantile_zero P.context.hc P.context.hk
      P.context.hkc P.context.hm P.context.hM P.alpha
    simp only [List.map_cons,historyMatrixReduction,ComparisonHistoryTerm.matrixReduction,
      toHistoryTerm_quantile,ih,actualHistoryStrengthSum,List.map_cons,List.sum_cons]
    change laplaceComparisonStrength P.context.d P.lam (P.R 0)+_ = P.lam+_
    rw [hR]
    simp [laplaceComparisonStrength,comparisonStrength,laplaceComparisonShape]

theorem actual_shell_history_strength_sum_le
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (ps : List (NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock))
    {T epsilon shell : ℝ} (hepsilon : 0 ≤ epsilon)
    (hb : ∀u,M.b u=historyMatrixClock T epsilon shell (ps.map (fun P=>P.toHistoryTerm)) u) :
    actualHistoryStrengthSum ps ≤ T := by
  have hb0:=hb 0
  simp only [historyMatrixClock,actual_history_matrix_reduction_zero] at hb0
  have hs : initialShellMatrixClock T epsilon shell 0 ≤ T := by
    unfold initialShellMatrixClock
    split_ifs <;> linarith
  linarith [M.hlb,M.hlam]

theorem actual_shell_history_field_le_regular_caps
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (ps : List (NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock))
    (hcl : 0 < cl) {T epsilon shell : ℝ} (hepsilon : 0 ≤ epsilon)
    (hb : ∀u,M.b u=historyMatrixClock T epsilon shell (ps.map (fun P=>P.toHistoryTerm)) u)
    (hh : ∀u,M.h u=historyFieldClock (ps.map (fun P=>P.toHistoryTerm)) u)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    M.h u ≤ actualHistoryRegularCapSum ps+(T/cl)*u := by
  rw [hh]
  exact (actual_history_field_le_regular_caps ps hcl hu).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (M.actual_shell_history_strength_sum_le ps hepsilon hb) hcl.le) hu.1))

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
