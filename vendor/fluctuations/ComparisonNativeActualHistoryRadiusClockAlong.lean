module

public import ComparisonHighStrengthUniformClock
public import ComparisonNativeActualInitialCompactClockAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 8000000

theorem actual_selected_bad_history_radius_clock_control_along
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (C a b : ℝ) (hC : 0 < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hshell : 0 < shell) (hTemp : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (hmass : ∀ᶠn in atTop,∀t∈Icc a b,
      (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs) :
    let S := fun n t=>orderedPathS (dim n+1) (M n).bf (M n).hf
      ((M n).alpha.val.val ((M n).xs*t))
    let q := fun n t=>actualMixedClock (dim n+1) (M n).bf (M n).hf
      ((M n).alpha.val.val ((M n).xs*t))/((T-epsilon)*(M n).xs)
    ∃Cs Q : ℝ,0 < Cs ∧ 0 < Q ∧
      (∀ᶠn in atTop,∀t∈Icc a b,0 ≤ S n t ∧ S n t ≤ Cs*(M n).xs ∧ q n t∈Icc (0:ℝ) Q) ∧
      TendstoUniformlyOn (fun n t=>
        (((M n).b ((M n).alpha.val.val ((M n).xs*t))-(T-epsilon))*S n t+
          (M n).h ((M n).alpha.val.val ((M n).xs*t)))/(M n).xs^3)
        (fun _=>0) atTop (Icc a b) := by
  intro S q
  have Hnear := actual_selected_bad_shell_history_near_bare_clocks
    hm hdelta hcl hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin hdim
    epsilon shell hshell hb hh Hhistory (fun n=>(M n).xs)
    (Eventually.of_forall (fun _=>le_rfl)) hxs
  have Hfield : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) (C*(M n).xs),|(M n).h u| ≤ (M n).xs^3 := by
    filter_upwards [Hnear C 1 hC.le zero_lt_one] with n hn u hu
    simpa only [one_mul] using (hn u hu).2
  obtain ⟨Q,hQ,HQ⟩ := actual_initial_compact_clock_range_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M hxs
    (hTemp.trans_le (sub_le_self T hepsilon)) hTemp htotal C hC Hfield
  obtain ⟨B,hB,HB⟩ := eventually_actual_minimum_mass_mean_upper (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cs := B*(1+C)
  have hCs : 0 < Cs := by dsimp only [Cs];positivity
  have HS : ∀ᶠn in atTop,∀t∈Icc a b,0 ≤ S n t ∧ S n t ≤ Cs*(M n).xs := by
    filter_upwards [hdim.eventually HB,hmass] with n hn hmN t ht
    let u := (M n).alpha.val.val ((M n).xs*t)
    have hu : u∈Icc (0:ℝ) 1 := (M n).alpha.val.property.1 _
    refine ⟨(M n).mass_mean_nonneg hu,?_⟩
    by_cases hzero : u=0
    · change orderedPathS (dim n+1) (M n).bf (M n).hf u ≤ _
      simp only [hzero,orderedPathS,orderedPathPair_zero]
      exact mul_nonneg hCs.le (M n).hxs.le
    · have H := hn (M n) u ⟨lt_of_le_of_ne hu.1 (Ne.symm hzero),hu.2⟩
      have Hmul := mul_le_mul_of_nonneg_left (hmN t ht) hB.le
      dsimp only [S,Cs,u] at *
      nlinarith only [H,Hmul]
  refine ⟨Cs,Q,hCs,hQ,?_,?_⟩
  · filter_upwards [HS,HQ,hmass] with n hn hqn hmN t ht
    exact ⟨(hn t ht).1,(hn t ht).2,hqn
      ⟨(M n).alpha.val.val ((M n).xs*t),(M n).alpha.val.property.1 _⟩ (hmN t ht)⟩
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro eps heps
    let e := eps/(2*(Cs+1))
    have he : 0 < e := by dsimp only [e];positivity
    filter_upwards [HS,hmass,Hnear C e hC.le he] with n hn hmN hnear t ht
    let u := (M n).alpha.val.val ((M n).xs*t)
    have hu : u∈Icc (0:ℝ) (C*(M n).xs) := ⟨((M n).alpha.val.property.1 _).1,hmN t ht⟩
    obtain ⟨hbN,hhN⟩ := hnear u hu
    have Hmul := mul_le_mul hbN (hn t ht).2 (hn t ht).1
      (mul_nonneg he.le (sq_nonneg (M n).xs))
    have Habs := abs_add_le (((M n).b u-(T-epsilon))*S n t) ((M n).h u)
    rw [abs_mul,abs_of_nonneg (hn t ht).1] at Habs
    have Hbound : |(((M n).b u-(T-epsilon))*S n t+(M n).h u)/(M n).xs^3| ≤ (Cs+1)*e := by
      rw [abs_div,abs_of_pos (pow_pos (M n).hxs 3)]
      apply (div_le_iff₀ (pow_pos (M n).hxs 3)).mpr
      nlinarith only [Habs,Hmul,hhN]
    have Heq : (Cs+1)*e=eps/2 := by dsimp only [e];field_simp
    have Hlt := Hbound.trans_lt (show (Cs+1)*e < eps by rw [Heq];linarith)
    simpa only [Real.dist_eq,zero_sub,abs_neg,u] using Hlt

end OAI.SKFluctuations.LaplaceWindowFormalization
