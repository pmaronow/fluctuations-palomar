module

public import VariableEndpointComparisonPotential
public import ComparisonAveragedChildMovementGain

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000

theorem comparison_native_trial_quantile_eq {c:ℝ} {k M:ℝ → ℝ}
    (hc:0 < c) (hk:ContinuousOn k (Icc (0:ℝ) 1))
    (hkc:∀r∈Icc (0:ℝ) 1,c ≤ k r) (hm:MonotoneOn M (Icc (0:ℝ) 1)) (hM:0 ≤ M 1)
    (γ:inverseIntegralConstraints 0 0 k M) (Rhat:ℝ → ℝ)
    (hb:∀u∈Icc (0:ℝ) 1,Rhat u∈Icc (0:ℝ) 1)
    (hgraph:∀u∈Icc (0:ℝ) 1,γ.val.val (Rhat u)=u)
    {u:ℝ} (hu:u∈Icc (0:ℝ) 1) :
    comparisonSweepQuantile hc hk hkc hm hM γ u=Rhat u := by
  calc
    _ = comparisonSweepQuantile hc hk hkc hm hM γ (γ.val.val (Rhat u)):=by rw [hgraph u hu]
    _ = _:=comparisonSweepQuantile_inverse hc hk hkc hm hM γ (hb u hu)

theorem comparison_native_child_trial_clocks {c dp lp dc lc:ℝ} {k M:ℝ → ℝ}
    (hc:0 < c) (hk:ContinuousOn k (Icc (0:ℝ) 1))
    (hkc:∀r∈Icc (0:ℝ) 1,c ≤ k r) (hm:MonotoneOn M (Icc (0:ℝ) 1)) (hM:0 ≤ M 1)
    (α γ:inverseIntegralConstraints 0 0 k M) (b h Z:ℝ → ℝ)
    (hdp:dp≠0) (hlp:0 < lp) (hdc:dc≠0) (hlc:0 < lc)
    (hb:MonotoneOn b (Icc (0:ℝ) 1)) (hh:MonotoneOn h (Icc (0:ℝ) 1))
    (hroom:lp+lc ≤ b 0) (hh0:0 ≤ h 0)
    (hZm:MonotoneOn Z (Icc (0:ℝ) 1)) (hZb:∀u∈Icc (0:ℝ) 1,Z u∈Icc (0:ℝ) 1) :
    let R:=comparisonSweepQuantile hc hk hkc hm hM α
    let Rhat:=comparisonSweepQuantile hc hk hkc hm hM γ
    AveragedMovementClocks b h (fun u=>laplaceComparisonStrength dp lp (R u)) R
      (fun u=>laplaceComparisonStrength dc lc (Z u)) Z
      (fun u=>laplaceComparisonStrength dp lp (Rhat u)) Rhat := by
  let R:=comparisonSweepQuantile hc hk hkc hm hM α
  let Rhat:=comparisonSweepQuantile hc hk hkc hm hM γ
  have hlb:lp ≤ b 0:=by linarith
  have hparent:=comparisonVariableEndpoint_clocks_admissible hc hk hkc hm hM b h hdp hlp.le hlb hb hh hh0 α
  have htrial:=comparisonVariableEndpoint_clocks_admissible hc hk hkc hm hM b h hdp hlp.le hlb hb hh hh0 γ
  have hDanti:AntitoneOn (fun u=>laplaceComparisonStrength dc lc (Z u)) (Icc (0:ℝ) 1):=by
    intro u hu v hv huv
    exact (laplaceComparisonStrength_monotonicities hdc hlc (r₀:=0) le_rfl).1
      (hZb u hu) (hZb v hv) (hZm hu hv huv)
  have hDfield:MonotoneOn (fun u=>laplaceComparisonStrength dc lc (Z u)*Z u) (Icc (0:ℝ) 1):=by
    intro u hu v hv huv
    exact (laplaceComparisonStrength_monotonicities hdc hlc (r₀:=0) le_rfl).2
      (hZb u hu) (hZb v hv) (hZm hu hv huv)
  refine ⟨?_,?_,htrial.1,htrial.2.1,?_,?_,htrial.2.2.1,htrial.2.2.2⟩
  · intro u hu v hv huv
    exact sub_le_sub (hparent.1 hu hv huv) (hDanti hu hv huv)
  · have hh':=hparent.2.1.add hDfield
    exact hh'
  · have he:=laplaceComparisonStrength_le dp hlp.le (R 0)
    have hD:=laplaceComparisonStrength_le dc hlc.le (Z 0)
    linarith
  · have he:0 ≤ laplaceComparisonStrength dp lp (R 0)*R 0:=
      mul_nonneg (laplaceComparisonStrength_pos dp hlp (R 0)).le
        (comparisonSweepQuantile_bounds hc hk hkc hm hM α 0).1
    have hD:0 ≤ laplaceComparisonStrength dc lc (Z 0)*Z 0:=
      mul_nonneg (laplaceComparisonStrength_pos dc hlc (Z 0)).le (hZb 0 (by norm_num)).1
    linarith

theorem comparison_native_actual_optimizer_movement_gain
    {c dp lp dc lc err:ℝ} {k M:ℝ → ℝ}
    (hc:0 < c) (hk:ContinuousOn k (Icc (0:ℝ) 1))
    (hkc:∀r∈Icc (0:ℝ) 1,c ≤ k r) (hm:MonotoneOn M (Icc (0:ℝ) 1)) (hM:0 ≤ M 1)
    (n:ℕ) (hn:0 < n) (α γ:inverseIntegralConstraints 0 0 k M) (b h Z:ℝ → ℝ)
    (hdp:dp≠0) (hlp:0 < lp) (hdc:dc≠0) (hlc:0 < lc)
    (hb:MonotoneOn b (Icc (0:ℝ) 1)) (hh:MonotoneOn h (Icc (0:ℝ) 1))
    (hroom:lp+lc ≤ b 0) (hh0:0 ≤ h 0)
    (hZc:ContinuousOn Z (Icc (0:ℝ) 1)) (hZm:MonotoneOn Z (Icc (0:ℝ) 1))
    (hZb:∀u∈Icc (0:ℝ) 1,Z u∈Icc (0:ℝ) 1)
    (hminimum:∀β:inverseIntegralConstraints 0 0 k M,
      comparisonVariableEndpointObjective hc hk hkc hm hM n b h dp lp α ≤
        comparisonVariableEndpointObjective hc hk hkc hm hM n b h dp lp β)
    (hgap:∀u∈Icc (0:ℝ) 1,
      comparisonSweepQuantile hc hk hkc hm hM γ u≠comparisonSweepQuantile hc hk hkc hm hM α u →
      Z u≠comparisonSweepQuantile hc hk hkc hm hM α u)
    (hfraction:∀u∈Icc (0:ℝ) 1,
      (comparisonSweepQuantile hc hk hkc hm hM γ u-comparisonSweepQuantile hc hk hkc hm hM α u)/
        (Z u-comparisonSweepQuantile hc hk hkc hm hM α u)∈Ico (0:ℝ)
          (laplaceComparisonStrength dc lc (Z u)/
            (laplaceComparisonStrength dp lp (comparisonSweepQuantile hc hk hkc hm hM α u)+
              laplaceComparisonStrength dc lc (Z u))))
    (hchild:pathCompensatedPressure n
      (fun u=>b u-laplaceComparisonStrength dp lp (comparisonSweepQuantile hc hk hkc hm hM α u))
      (fun u=>h u+laplaceComparisonStrength dp lp (comparisonSweepQuantile hc hk hkc hm hM α u)*
        comparisonSweepQuantile hc hk hkc hm hM α u)
      (fun u=>laplaceComparisonStrength dc lc (Z u)) Z 0 ≤
      realOrderedSKPathPressure n
        (fun u=>b u-laplaceComparisonStrength dp lp (comparisonSweepQuantile hc hk hkc hm hM α u))
        (fun u=>h u+laplaceComparisonStrength dp lp (comparisonSweepQuantile hc hk hkc hm hM α u)*
          comparisonSweepQuantile hc hk hkc hm hM α u) 0+err) :
    let R:=comparisonSweepQuantile hc hk hkc hm hM α
    let Rhat:=comparisonSweepQuantile hc hk hkc hm hM γ
    (∫u in (0:ℝ)..1,laplaceComparisonStrength dp lp (R u)*(Rhat u-R u)*(Z u-R u)) ≤ 4*err := by
  let R:=comparisonSweepQuantile hc hk hkc hm hM α
  let Rhat:=comparisonSweepQuantile hc hk hkc hm hM γ
  let omega:=fun u=>(Rhat u-R u)/(Z u-R u)
  have hRbounds:∀u∈Icc (0:ℝ) 1,R u∈Icc (0:ℝ) 1:=fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α u
  have hhBounds:∀u∈Icc (0:ℝ) 1,Rhat u∈Icc (0:ℝ) 1:=fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM γ u
  have hmove:∀u∈Icc (0:ℝ) 1,Rhat u=R u+omega u*(Z u-R u):=by
    intro u hu
    by_cases he:Rhat u=R u
    · simp only [omega,he,sub_self,zero_div,zero_mul,add_zero]
    · have hz:Z u-R u≠0:=sub_ne_zero.mpr (hgap u hu he)
      dsimp only [omega]
      rw [div_mul_cancel₀ _ hz]
      ring
  have hRc:ContinuousOn R (Icc (0:ℝ) 1):=(comparisonSweepQuantile_continuous hc hk hkc hm hM α).continuousOn
  have hhc:ContinuousOn Rhat (Icc (0:ℝ) 1):=(comparisonSweepQuantile_continuous hc hk hkc hm hM γ).continuousOn
  have hclocks:=comparison_native_child_trial_clocks hc hk hkc hm hM α γ b h Z hdp hlp hdc hlc hb hh hroom hh0 hZm hZb
  have hhat:∀u∈Icc (0:ℝ) 1,laplaceComparisonStrength dp lp (Rhat u) ≤
      laplaceComparisonStrength dp lp (R u)/(1-omega u):=by
    intro u hu
    have he:0 ≤ laplaceComparisonStrength dp lp (R u):=(laplaceComparisonStrength_pos dp hlp (R u)).le
    have hD:0 < laplaceComparisonStrength dc lc (Z u):=laplaceComparisonStrength_pos dc hlc (Z u)
    have hratio:laplaceComparisonStrength dc lc (Z u)/
      (laplaceComparisonStrength dp lp (R u)+laplaceComparisonStrength dc lc (Z u)) ≤ 1:=
      (div_le_one₀ (add_pos_of_nonneg_of_pos he hD)).mpr (by linarith)
    exact comparison_movement_strength_upper (laplaceComparisonStrength dp lp)
      (fun q _=>(laplaceComparisonStrength_pos dp hlp q).le)
      (laplaceComparisonStrength_monotonicities hdp hlp (r₀:=0) le_rfl).1
      (by simpa only [mul_comm] using (laplaceComparisonStrength_monotonicities hdp hlp (r₀:=0) le_rfl).2)
      (hRbounds u hu) (hZb u hu) (hhBounds u hu)
      ⟨(hfraction u hu).1,(hfraction u hu).2.trans_le hratio⟩ (hmove u hu)
  have hgain:=actual_averaged_child_movement_gain n hn b h
    (fun u=>laplaceComparisonStrength dp lp (R u)) R
    (fun u=>laplaceComparisonStrength dc lc (Z u)) Z
    (fun u=>laplaceComparisonStrength dp lp (Rhat u)) Rhat omega
    (fun u _=>(laplaceComparisonStrength_pos dp hlp (R u)).le)
    (fun u _=>laplaceComparisonStrength_pos dc hlc (Z u))
    (fun u hu=>(hfraction u hu).1) (fun u hu=>(hfraction u hu).2) hhat hmove
    ((laplaceComparisonStrength_contDiff dp lp).continuous.comp_continuousOn hRc)
    ((laplaceComparisonStrength_contDiff dc lc).continuous.comp_continuousOn hZc)
    ((laplaceComparisonStrength_contDiff dp lp).continuous.comp_continuousOn hhc)
    hRc hZc hhc hclocks (hminimum γ) hchild
  have heq:(∫u in (0:ℝ)..1,laplaceComparisonStrength dp lp (R u)*(Rhat u-R u)*(Z u-R u))=
      ∫u in (0:ℝ)..1,laplaceComparisonStrength dp lp (R u)*omega u*(Z u-R u)^2:=by
    apply intervalIntegral.integral_congr
    intro u hu
    have huI:u∈Icc (0:ℝ) 1:=by simpa only [uIcc_of_le zero_le_one] using hu
    dsimp only
    rw [hmove u huI]
    ring
  change (∫u in (0:ℝ)..1,laplaceComparisonStrength dp lp (R u)*(Rhat u-R u)*(Z u-R u)) ≤ 4*err
  rw [heq]
  exact hgain

end OAI.SKFluctuations.LaplaceWindowFormalization
