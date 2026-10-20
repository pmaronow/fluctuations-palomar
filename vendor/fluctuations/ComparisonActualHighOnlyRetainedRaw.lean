module

public import ComparisonActualHighOnlyOverlapAmplitude
public import ComparisonSignedCavityActualMinimumResampling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy Cavity
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 10000000

theorem eventually_actual_high_only_original_boundary_raw
    (ell : ℕ) (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀a : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      a.data.s ≤ 1/4 → a.data.s ≤ a.xs →
      ∀u : PositiveMass,u.val≤1 →
      ∀extra : List PositiveMass,(∀v∈extra,v.val≤1) →
      ∃us : List PositiveMass,(∀v∈us,v.val≤1) ∧ u∈us ∧ (∀v∈extra,v∈us) ∧
        ∀ᶠ j : ℕ in atTop,
          let as:=finiteCutMasses us j
          let steps:=sampleClockSteps (completedPathClock n a.bf a.hf) 0 as
          let Q:=stepClockValues (fun i=>(completedPathClock n a.bf a.hf 0 i:ℝ)) steps
          (physicalRawRatio n (ell+1) steps 0 a.xs
            (Measure.pi fun i=>gaussianReal 0 (completedPathClock n a.bf a.hf 0 i)) id measurable_id)^2≤2*C ∧
          ∀low : ℕ,low≤as.length →
            (physicalRawRatio n (ell+1) (originalBoundaryTailSteps n as Q low)
              (physicalCutMass 0 steps low) a.xs (originalBoundaryPrefixLaw n as Q low)
              id measurable_id)^2≤2*C := by
  obtain ⟨C,hC,hraw⟩ := comparison_minimum_finite_raw_ratio_retaining
    (D:=D) ell Bclock hm hdelta hroom hcl hcu hAz (by norm_num : (0:ℝ)<1/3) hC0 hCt
  have hlog : ∀ᶠ n : ℕ in atTop,1≤Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  refine ⟨C,hC,?_⟩
  filter_upwards [hraw,eventually_comparisonLowerScale_depth hC0 hm,hlog,
    eventually_ge_atTop (1:ℕ)] with n hnraw hndepth hnlog hn1
  intro a hs hsxs u hu extra hextra
  let w:=a.data
  have hN1 : (1:ℝ)≤w.N := by exact_mod_cast hn1
  have hnd : 1/w.N≤w.d := by
    have hh:=hndepth w.E w.d w.hE w.hd a.hlower
    have hs : comparisonLowerScale n w.E w.d≤w.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ w.hd).mpr (by simpa only [pow_two] using a.hupper)
    exact hh.trans hs
  have hr0 : (0:ℝ)∈Icc (0:ℝ) (1/4) := by norm_num
  have hs0 : w.s∈Icc (0:ℝ) (1/4) := ⟨w.hs.1,hs⟩
  let g:=laplaceComparisonStrength w.d a.lam
  have hslow : ∀r∈Icc a.z 1,(1/3)/Real.log (n:ℝ)≤1-comparisonLogSlope g r := by
    intro r hr
    exact laplaceComparisonStrength_uniform_slope hN1 hnlog w.hd hnd
      a.hlam a.hld ⟨a.hz.1.trans hr.1,hr.2⟩
  have hfeas (beta : w.Profile):=w.original_clocks_admissible_high_only beta a.lam_mem
  obtain ⟨us,hus,huus,hextraus,hfinite⟩ := hnraw w.hn w.hE w.hd hr0 hs0 g a.alpha
    (laplaceComparisonStrength_contDiff w.d a.lam)
    (fun r _=>laplaceComparisonStrength_pos w.d a.hlam r)
    (fun r _=>⟨(laplaceComparisonStrength_logSlope_mem w.hd.ne' a.hlam.ne' r).1,
      (laplaceComparisonStrength_logSlope_mem w.hd.ne' a.hlam.ne' r).2.le⟩)
    w.b w.h (fun beta=>(hfeas beta).1) (fun beta=>(hfeas beta).2.1)
    (fun beta=>(hfeas beta).2.2.1) (fun beta=>(hfeas beta).2.2.2)
    a.optimizer.inverse_minimum u hu extra hextra a.xs a.z a.hxs a.hscale hsxs
    w.hU.le a.hz a.hzxs a.hdD a.hupper a.hlower a.htest a.regular hslow
    (w.hh.mono (Icc_subset_Icc w.hs.1 le_rfl)) (by
      obtain ⟨hbf,hhf⟩:=w.original_clock_eq_high_only a.alpha a.lam
      rw [hhf]
      exact a.clockBudget)
  obtain ⟨hbf,hhf⟩:=w.original_clock_eq_high_only a.alpha a.lam
  rw [hbf,hhf] at hfinite
  refine ⟨us,hus,huus,hextraus,?_⟩
  filter_upwards [hfinite] with j hj
  dsimp only at hj ⊢
  change (physicalRawRatio n (ell+1)
    (sampleClockSteps (completedPathClock n a.bf a.hf) 0 (finiteCutMasses us j)) 0 a.xs
    (Measure.pi fun i=>gaussianReal 0 (completedPathClock n a.bf a.hf 0 i))
    id measurable_id)^2≤2*C at hj
  refine ⟨hj,?_⟩
  intro low hlow
  have h:=original_boundary_raw_ratio_le_sampled n (ell+1)
    (completedPathClock n a.bf a.hf) (finiteCutMasses us j)
    (finiteCutMasses_ordered us hus j) low hlow a.hxs
  dsimp only at h
  apply (pow_le_pow_left₀ ?_ h 2).trans hj
  exact zero_le_one.trans (physicalRawRatio_one_le _ _ _ _ _ _ _ _)

end OAI.SKFluctuations.LaplaceWindowFormalization
