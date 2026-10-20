module

public import ComparisonNativeActualHistorySupportSpinSelectionsAlong
public import ComparisonNativeActualSpinRadiusOrder

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology
set_option maxHeartbeats 12000000

theorem actual_selected_bad_history_radius_spin_between_support_along
    {m delta cl cu Az C0 Ct D Bclock T Slocal c0 : ℝ} (hT : 0 < T)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (epsilon shell : ℝ)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (d : ActualInheritedLocalScalarLimitData hT Slocal M htotal)
    (s : NonnegativeMassProfile)
    (Hspin : ∀t : ℝ,Tendsto (fun n=>orderedPathS (dim n+1) (M n).bf (M n).hf
      ((M n).alpha.val.val ((M n).xs*t))/(M n).xs) atTop (𝓝 (s.mass t)))
    {a b t : ℝ} (hat : a < t) (htb : t < b)
    (hasupport : ∀eps : ℝ,0 < eps → d.V.mass (a-eps) < d.V.mass (a+eps))
    (hbsupport : ∀eps : ℝ,0 < eps → d.V.mass (b-eps) < d.V.mass (b+eps)) :
    s.mass t∈Icc a b := by
  obtain ⟨ns,hns,w,Hr,Hs⟩ := exists_actual_selected_bad_history_support_spin_selections_along
    hT hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim root M W hcanonical hWlim
    epsilon shell hb hh Hhistory htotal d a hasupport
  have Hlower : a ≤ s.mass t := by
    apply le_of_tendsto_of_tendsto Hs ((Hspin t).comp hns)
    filter_upwards [Hr.eventually (gt_mem_nhds hat)] with j hj
    apply div_le_div_of_nonneg_right _ (M (ns j)).hxs.le
    apply (M (ns j)).mass_mean_le_radius_mean_of_radius_le (w j).property
    have H := (div_lt_iff₀ (M (ns j)).hxs).mp hj
    simpa only [mul_comm] using H.le
  obtain ⟨ms,hms,z,Hr',Hs'⟩ := exists_actual_selected_bad_history_support_spin_selections_along
    hT hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim root M W hcanonical hWlim
    epsilon shell hb hh Hhistory htotal d b hbsupport
  have Hupper : s.mass t ≤ b := by
    apply le_of_tendsto_of_tendsto ((Hspin t).comp hms) Hs'
    filter_upwards [Hr'.eventually (lt_mem_nhds htb)] with j hj
    apply div_le_div_of_nonneg_right _ (M (ms j)).hxs.le
    apply (M (ms j)).radius_mean_le_mass_mean_of_le_radius (z j).property
    have H := (lt_div_iff₀ (M (ms j)).hxs).mp hj
    simpa only [mul_comm] using H.le
  exact ⟨Hlower,Hupper⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
