module

public import ComparisonActualHighOnlyInverseClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 12000000

theorem eventually_actual_high_only_overlap_moment_normalized
    (ell : ℕ) (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃K : ℝ,0 < K ∧ ∀ᶠ n in atTop,
      ∀a : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      a.data.s ≤ 1/4 → a.data.s ≤ a.xs → ∀u∈Ioc (0:ℝ) 1,
        pathPairMoment (uniformWeight n) (finiteFeature n) (completedPathClock n a.bf a.hf)
          (fun sigma tau=>|orderedOverlap n sigma tau|^(2*(ell+1))) u ≤
            K*(a.xs+u)^(2*(ell+1)) := by
  obtain ⟨K,hK,hamp⟩:=comparison_minimum_retained_overlap_moment_normalized
    (D:=D) ell Bclock hm hdelta hroom hcl hcu hAz (by norm_num : (0:ℝ)<1/3) hC0 hCt
  have hlog : ∀ᶠ n : ℕ in atTop,1 ≤ Real.log (n:ℝ):=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  refine ⟨K,hK,?_⟩
  filter_upwards [hamp,eventually_comparisonLowerScale_depth hC0 hm,hlog,
    eventually_ge_atTop (1:ℕ)] with n hnamp hndepth hnlog hn1
  intro a hs hsxs u hu
  let w:=a.data
  let g:=laplaceComparisonStrength w.d a.lam
  have hN1 : (1:ℝ) ≤ w.N:=by exact_mod_cast hn1
  have hnd : 1/w.N ≤ w.d:=by
    have HH:=hndepth w.E w.d w.hE w.hd a.hlower
    have HS : comparisonLowerScale n w.E w.d ≤ w.d:=by
      unfold comparisonLowerScale
      exact (div_le_iff₀ w.hd).mpr (by simpa only [pow_two] using a.hupper)
    exact HH.trans HS
  have hr0 : (0:ℝ)∈Icc (0:ℝ) (1/4):=by norm_num
  have hs0 : w.s∈Icc (0:ℝ) (1/4):=⟨w.hs.1,hs⟩
  have hslow : ∀r∈Icc a.z 1,(1/3)/Real.log (n:ℝ) ≤ 1-comparisonLogSlope g r:=by
    intro r hr
    exact laplaceComparisonStrength_uniform_slope hN1 hnlog w.hd hnd a.hlam a.hld
      ⟨a.hz.1.trans hr.1,hr.2⟩
  have hp : ∀r∈Ioc (0:ℝ) 1,comparisonLogSlope g r∈Icc (0:ℝ) 1:=by
    intro r _hr
    exact ⟨(laplaceComparisonStrength_logSlope_mem w.hd.ne' a.hlam.ne' r).1,
      (laplaceComparisonStrength_logSlope_mem w.hd.ne' a.hlam.ne' r).2.le⟩
  have hfeas (beta : w.Profile):=w.original_clocks_admissible_high_only beta a.lam_mem
  have hpoint:=hnamp w.hn w.hE w.hd hr0 hs0 g a.alpha
    (laplaceComparisonStrength_contDiff w.d a.lam)
    (fun r _=>laplaceComparisonStrength_pos w.d a.hlam r) hp
    w.b w.h (fun beta=>(hfeas beta).1) (fun beta=>(hfeas beta).2.1)
    (fun beta=>(hfeas beta).2.2.1) (fun beta=>(hfeas beta).2.2.2)
    a.optimizer.inverse_minimum ⟨u,hu.1⟩ hu.2 a.xs a.z a.hxs a.hscale hsxs
    w.hU.le a.hz a.hzxs a.hdD a.hupper a.hlower a.htest a.regular hslow
    (w.hh.mono (Icc_subset_Icc w.hs.1 le_rfl)) (by
      obtain ⟨hbf,hhf⟩:=w.original_clock_eq_high_only a.alpha a.lam
      rw [hhf]
      exact a.clockBudget)
  obtain ⟨hbf,hhf⟩:=w.original_clock_eq_high_only a.alpha a.lam
  rw [hbf,hhf] at hpoint
  exact hpoint

theorem eventually_actual_high_only_B_normalized
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃K : ℝ,0 < K ∧ ∀ᶠ n in atTop,
      ∀a : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      a.data.s ≤ 1/4 → a.data.s ≤ a.xs → ∀u∈Ioc (0:ℝ) 1,
        orderedPathB n a.bf a.hf u ≤ K*(a.xs+u)^2 := by
  obtain ⟨K,hK,hamp⟩:=eventually_actual_high_only_overlap_moment_normalized
    (D:=D) 0 Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨K,hK,?_⟩
  filter_upwards [hamp] with n hn
  intro a hs hsxs u hu
  have H:=hn a hs hsxs u hu
  have HP:=orderedPathPair_eq_completed n a.data.hn a.bf a.hf a.bf_monotone a.hf_monotone
    (fun sigma tau=>(orderedOverlap n sigma tau)^2) hu
  have HA : (fun sigma tau : Spin n=>|orderedOverlap n sigma tau|^(2*(0+1)))=
      fun sigma tau=>(orderedOverlap n sigma tau)^2:=by
    funext sigma tau
    norm_num
  rw [HA,←HP] at H
  simpa only [orderedPathB,Nat.zero_add,Nat.mul_one] using H

end OAI.SKFluctuations.LaplaceWindowFormalization
