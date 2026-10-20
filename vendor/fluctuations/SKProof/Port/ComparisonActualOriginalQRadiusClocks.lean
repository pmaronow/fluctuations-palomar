module

public import SKProof.Port.ComparisonActualOriginalQInitialCompactClock
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
theorem actual_comparable_context_positive_radius_clock_control_original_q
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (c C a b : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (hmass : ∀ᶠn in atTop,∀t∈Icc a b,
      c*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*t) ∧
        (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs) :
    let S := fun n t=>orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf
      ((M n).alpha.val.val ((M n).xs*t))
    let q := fun n t=>actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf
      ((M n).alpha.val.val ((M n).xs*t))/(T*(M n).xs)
    ∃Cs Q : ℝ,0 < Cs ∧ 0 < Q ∧
      (∀ᶠn in atTop,∀t∈Icc a b,0 ≤ S n t ∧ S n t ≤ Cs*(M n).xs ∧ q n t∈Icc (0:ℝ) Q) ∧
      TendstoUniformlyOn (fun n t=>
        (((M n).b ((M n).alpha.val.val ((M n).xs*t))-T)*S n t+
          (M n).h ((M n).alpha.val.val ((M n).xs*t)))/(M n).xs^3)
        (fun _=>0) atTop (Icc a b) := by
  have hTemp : 0 < T := G.hT
  intro S q
  have Hnear:=fun epsilon hepsilon=>G.positive_band_clocks_original_q c C epsilon hc hC.le hepsilon
  have Hfield : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) (C*(M n).xs),|(M n).h u| ≤ (M n).xs^3 := by
    simpa only [one_mul] using G.initial_field_clock_original_q C 1 hC zero_lt_one
  obtain ⟨Q,hQ,HQ⟩ := actual_initial_compact_clock_range_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M G hxs
    (G.hT) hTemp htotal C hC Hfield
  obtain ⟨B,hB,HB⟩ := eventually_actual_mass_mean_upper_original_q (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cs := B*(1+C)
  have hCs : 0 < Cs := by dsimp only [Cs];positivity
  have HS : ∀ᶠn in atTop,∀t∈Icc a b,0 ≤ S n t ∧ S n t ≤ Cs*(M n).xs := by
    filter_upwards [hdim.eventually HB,G.eventually_geometric_gates_original_q,hmass] with n hn hngate hmN t ht
    let u := (M n).alpha.val.val ((M n).xs*t)
    have hu : u∈Icc (0:ℝ) 1 := (M n).alpha.val.property.1 _
    refine ⟨(M n).mass_mean_nonneg hu,?_⟩
    by_cases hzero : u=0
    · change orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u ≤ _
      simp only [hzero,orderedPathS,orderedPathPair_zero]
      exact mul_nonneg hCs.le (M n).hxs.le
    · have H := hn (M n) hngate.2 hngate.1 u ⟨lt_of_le_of_ne hu.1 (Ne.symm hzero),hu.2⟩
      have Hmul := mul_le_mul_of_nonneg_left ((hmN t ht).2) hB.le
      dsimp only [S,Cs,u] at *
      nlinarith only [H,Hmul]
  refine ⟨Cs,Q,hCs,hQ,?_,?_⟩
  · filter_upwards [HS,HQ,hmass] with n hn hqn hmN t ht
    exact ⟨(hn t ht).1,(hn t ht).2,hqn
      ⟨(M n).alpha.val.val ((M n).xs*t),(M n).alpha.val.property.1 _⟩ ((hmN t ht).2)⟩
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro eps heps
    let e := eps/(2*(Cs+1))
    have he : 0 < e := by dsimp only [e];positivity
    filter_upwards [HS,hmass,Hnear e he] with n hn hmN hnear t ht
    let u := (M n).alpha.val.val ((M n).xs*t)
    have hu : u∈Icc (c*(M n).xs) (min (C*(M n).xs) 1) :=
      ⟨(hmN t ht).1,le_min (hmN t ht).2 ((M n).alpha.val.property.1 _).2⟩
    obtain ⟨hbN,hhN⟩ := hnear u hu
    have Hmul := mul_le_mul hbN (hn t ht).2 (hn t ht).1
      (mul_nonneg he.le (sq_nonneg (M n).xs))
    have Habs := abs_add_le (((M n).b u-T)*S n t) ((M n).h u)
    rw [abs_mul,abs_of_nonneg (hn t ht).1] at Habs
    have Hbound : |(((M n).b u-T)*S n t+(M n).h u)/(M n).xs^3| ≤ (Cs+1)*e := by
      rw [abs_div,abs_of_pos (pow_pos (M n).hxs 3)]
      apply (div_le_iff₀ (pow_pos (M n).hxs 3)).mpr
      nlinarith only [Habs,Hmul,hhN]
    have Heq : (Cs+1)*e=eps/2 := by dsimp only [e];field_simp
    have Hlt := Hbound.trans_lt (show (Cs+1)*e < eps by rw [Heq];linarith)
    simpa only [Real.dist_eq,zero_sub,abs_neg,u] using Hlt

theorem actual_comparable_context_radius_clock_bounds_original_q
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (C a b : ℝ) (hC : 0 < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (hmass : ∀ᶠn in atTop,∀t∈Icc a b,
      (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs) :
    let S := fun n t=>orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf
      ((M n).alpha.val.val ((M n).xs*t))
    let q := fun n t=>actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf
      ((M n).alpha.val.val ((M n).xs*t))/(T*(M n).xs)
    ∃Cs Q : ℝ,0 < Cs ∧ 0 < Q ∧
      (∀ᶠn in atTop,∀t∈Icc a b,0 ≤ S n t ∧ S n t ≤ Cs*(M n).xs ∧ q n t∈Icc (0:ℝ) Q) := by
  have hTemp : 0 < T := G.hT
  intro S q
  have Hfield : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) (C*(M n).xs),|(M n).h u| ≤ (M n).xs^3 := by
    simpa only [one_mul] using G.initial_field_clock_original_q C 1 hC zero_lt_one
  obtain ⟨Q,hQ,HQ⟩ := actual_initial_compact_clock_range_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M G hxs
    (G.hT) hTemp htotal C hC Hfield
  obtain ⟨B,hB,HB⟩ := eventually_actual_mass_mean_upper_original_q (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cs := B*(1+C)
  have hCs : 0 < Cs := by dsimp only [Cs];positivity
  have HS : ∀ᶠn in atTop,∀t∈Icc a b,0 ≤ S n t ∧ S n t ≤ Cs*(M n).xs := by
    filter_upwards [hdim.eventually HB,G.eventually_geometric_gates_original_q,hmass] with n hn hngate hmN t ht
    let u := (M n).alpha.val.val ((M n).xs*t)
    have hu : u∈Icc (0:ℝ) 1 := (M n).alpha.val.property.1 _
    refine ⟨(M n).mass_mean_nonneg hu,?_⟩
    by_cases hzero : u=0
    · change orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u ≤ _
      simp only [hzero,orderedPathS,orderedPathPair_zero]
      exact mul_nonneg hCs.le (M n).hxs.le
    · have H := hn (M n) hngate.2 hngate.1 u ⟨lt_of_le_of_ne hu.1 (Ne.symm hzero),hu.2⟩
      have Hmul := mul_le_mul_of_nonneg_left (hmN t ht) hB.le
      dsimp only [S,Cs,u] at *
      nlinarith only [H,Hmul]
  refine ⟨Cs,Q,hCs,hQ,?_⟩
  filter_upwards [HS,HQ,hmass] with n hn hqn hmN t ht
  exact ⟨(hn t ht).1,(hn t ht).2,hqn
    ⟨(M n).alpha.val.val ((M n).xs*t),(M n).alpha.val.property.1 _⟩ (hmN t ht)⟩
end OAI.SKFluctuations.LaplaceWindowFormalization
