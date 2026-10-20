module

public import ComparisonActualShiftedParentData
public import ComparisonAveragedChildMovementGain

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 18000000

private theorem actual_two_branch_intervalIntegrable
    {s : ℝ} (hs : s∈Icc (0:ℝ) 1) {f g q : ℝ→ℝ}
    (hf : ContinuousOn f (Icc s 1)) (hg : ContinuousOn g (Icc (0:ℝ) 1))
    (heq : ∀u∈Icc (0:ℝ) 1,q u=if s≤u then f u else g u) :
    IntervalIntegrable q volume 0 1 := by
  have H:=cutoff_intervalIntegrable hs (hf.sub (hg.mono (Icc_subset_Icc hs.1 le_rfl)))
  apply IntervalIntegrable.congr (f:=fun u=>(if s≤u then f u-g u else 0)+g u)
    (g:=q) ?_ (H.add ((by simpa only [uIcc_of_le zero_le_one] using hg : ContinuousOn g (uIcc (0:ℝ) 1))).intervalIntegrable)
  intro u hu
  rw [uIoc_of_le zero_le_one] at hu
  rw [heq u ⟨hu.1.le,hu.2⟩]
  by_cases h : s≤u
  · simp only [h,ite_true]
    ring
  · simp only [h,ite_false,zero_add]

namespace ActualShiftedParentData
variable {n : ℕ} {delta : ℝ} (a : ActualShiftedParentData n delta)

theorem optimizer_all_mass_child_movement_gain
    (P : ActualShiftedParentMinimum a)
    (child : NativeChildBarrierParameters n delta) (beta : child.Profile)
    {childLam : ℝ} (hchildLam : 0 < childLam)
    (hroom : childLam ≤ a.b 0-a.coefficient P.alpha 0)
    (hattained :
      variableEndpointComparisonSweepObjective child.hc child.hk child.hkc child.hm child.hM n
        (fun u=>a.b u-a.coefficient P.alpha u)
        (fun u=>a.h u+a.coefficient P.alpha u*a.R P.alpha u) child.d childLam beta=
      variableEndpointComparisonSweepMinimum child.hc child.hk child.hkc child.hm child.hM n
        (fun u=>a.b u-a.coefficient P.alpha u)
        (fun u=>a.h u+a.coefficient P.alpha u*a.R P.alpha u) child.d childLam)
    (gamma : a.Profile)
    (hgap : ∀u∈Icc a.s 1,a.R gamma u≠a.R P.alpha u → child.R beta u≠a.R P.alpha u)
    (hfraction : ∀u∈Icc a.s 1,
      (a.R gamma u-a.R P.alpha u)/(child.R beta u-a.R P.alpha u)∈Ico (0:ℝ)
        (laplaceComparisonStrength child.d childLam (child.R beta u)/
          (laplaceComparisonStrength a.d a.lam (a.R P.alpha u)+
            laplaceComparisonStrength child.d childLam (child.R beta u)))) :
    (∫u in (0:ℝ)..1,a.coefficient P.alpha u*(a.R gamma u-a.R P.alpha u)*
      (child.R beta u-a.R P.alpha u)) ≤
      4*variableEndpointComparisonSweepCost child.hc child.hk child.hkc child.hm child.hM n
        (fun u=>a.b u-a.coefficient P.alpha u)
        (fun u=>a.h u+a.coefficient P.alpha u*a.R P.alpha u) child.d childLam := by
  let R:=a.R P.alpha
  let Rhat:=a.R gamma
  let Z:=child.R beta
  let e:=a.coefficient P.alpha
  let eh:=a.coefficient gamma
  let D:=fun u=>laplaceComparisonStrength child.d childLam (Z u)
  let omega:=fun u=>(Rhat u-R u)/(Z u-R u)
  let cost:=fun u=>(e u*R u+D u*Z u-eh u*Rhat u)^2/(e u+D u-eh u)
  have HR : Continuous R:=omittedSweepQuantile_continuous a.hr1 a.hs a.hc a.hk a.hkc a.hm a.hM P.alpha
  have HRhat : Continuous Rhat:=omittedSweepQuantile_continuous a.hr1 a.hs a.hc a.hk a.hkc a.hm a.hM gamma
  have HZ : Continuous Z:=comparisonSweepQuantile_continuous child.hc child.hk child.hkc child.hm child.hM beta
  have HDc : Continuous D:=(laplaceComparisonStrength_contDiff child.d childLam).continuous.comp HZ
  have HEc : Continuous (fun u=>laplaceComparisonStrength a.d a.lam (R u)):=
    (laplaceComparisonStrength_contDiff a.d a.lam).continuous.comp HR
  have HHc : Continuous (fun u=>laplaceComparisonStrength a.d a.lam (Rhat u)):=
    (laplaceComparisonStrength_contDiff a.d a.lam).continuous.comp HRhat
  have HEhi : ∀u∈Icc a.s 1,e u=laplaceComparisonStrength a.d a.lam (R u):=by
    intro u hu
    simp only [e,R,ActualShiftedParentData.coefficient,omittedStrengthCoefficient,ite_eq_left hu.1]
  have HHhi : ∀u∈Icc a.s 1,eh u=laplaceComparisonStrength a.d a.lam (Rhat u):=by
    intro u hu
    simp only [eh,Rhat,ActualShiftedParentData.coefficient,omittedStrengthCoefficient,ite_eq_left hu.1]
  have HElo : ∀u<a.s,e u=0 ∧ eh u=0 ∧ Rhat u=R u ∧ omega u=0:=by
    intro u hu
    have H1:=a.radius_before P.alpha hu.le
    have H2:=a.radius_before gamma hu.le
    have Hsame : Rhat u=R u:=H2.trans H1.symm
    refine ⟨?_,?_,Hsame,?_⟩
    · simp only [e,ActualShiftedParentData.coefficient,omittedStrengthCoefficient,ite_eq_right (not_le.mpr hu)]
    · simp only [eh,ActualShiftedParentData.coefficient,omittedStrengthCoefficient,ite_eq_right (not_le.mpr hu)]
    · simp only [omega,Hsame,sub_self,zero_div]
  have HErange : ∀u,0≤e u:=by
    intro u
    dsimp only [e,ActualShiftedParentData.coefficient,omittedStrengthCoefficient]
    split_ifs
    · exact (laplaceComparisonStrength_pos a.d a.hlam _).le
    · exact le_rfl
  have HHrange : ∀u,0≤eh u:=by
    intro u
    dsimp only [eh,ActualShiftedParentData.coefficient,omittedStrengthCoefficient]
    split_ifs
    · exact (laplaceComparisonStrength_pos a.d a.hlam _).le
    · exact le_rfl
  have HDrange : ∀u,0<D u:=fun u=>laplaceComparisonStrength_pos child.d hchildLam _
  have HRb : ∀u,R u∈Icc (0:ℝ) 1:=fun u=>
    (Icc_subset_Icc a.hr0 le_rfl) (omittedSweepQuantile_bounds a.hr1 a.hs a.hc a.hk a.hkc a.hm a.hM P.alpha u)
  have HHb : ∀u,Rhat u∈Icc (0:ℝ) 1:=fun u=>
    (Icc_subset_Icc a.hr0 le_rfl) (omittedSweepQuantile_bounds a.hr1 a.hs a.hc a.hk a.hkc a.hm a.hM gamma u)
  have HZb : ∀u,Z u∈Icc (0:ℝ) 1:=fun u=>comparisonSweepQuantile_bounds child.hc child.hk child.hkc child.hm child.hM beta u
  have Hfrac : ∀u∈Icc (0:ℝ) 1,omega u∈Ico (0:ℝ) (D u/(e u+D u)):=by
    intro u hu
    by_cases hus : a.s≤u
    · rw [HEhi u ⟨hus,hu.2⟩]
      exact hfraction u ⟨hus,hu.2⟩
    · rcases HElo u (lt_of_not_ge hus) with ⟨he0,_,_,ho0⟩
      rw [he0,ho0,zero_add,div_self (HDrange u).ne']
      exact ⟨le_rfl,zero_lt_one⟩
  have Hmove : ∀u∈Icc (0:ℝ) 1,Rhat u=R u+omega u*(Z u-R u):=by
    intro u hu
    by_cases he : Rhat u=R u
    · simp only [omega,he,sub_self,zero_div,zero_mul,add_zero]
    · have hus : a.s≤u:=by
        by_contra hs
        exact he (HElo u (lt_of_not_ge hs)).2.2.1
      have Hne : Z u-R u≠0:=sub_ne_zero.mpr (hgap u ⟨hus,hu.2⟩ he)
      dsimp only [omega]
      rw [div_mul_cancel₀ _ Hne]
      ring
  have Hupper : ∀u∈Icc (0:ℝ) 1,eh u≤e u/(1-omega u):=by
    intro u hu
    by_cases hus : a.s≤u
    · rw [HEhi u ⟨hus,hu.2⟩,HHhi u ⟨hus,hu.2⟩]
      have Hratio : D u/(e u+D u)≤1:=
        (div_le_one₀ (add_pos_of_nonneg_of_pos (HErange u) (HDrange u))).mpr (by linarith [HErange u])
      exact comparison_movement_strength_upper (laplaceComparisonStrength a.d a.lam)
        (fun q _=>(laplaceComparisonStrength_pos a.d a.hlam q).le)
        (laplaceComparisonStrength_monotonicities a.hd.ne' a.hlam (r₀:=0) le_rfl).1
        (by simpa only [mul_comm] using (laplaceComparisonStrength_monotonicities a.hd.ne' a.hlam (r₀:=0) le_rfl).2)
        (HRb u) (HZb u) (HHb u) ⟨(Hfrac u hu).1,(Hfrac u hu).2.trans_le Hratio⟩ (Hmove u hu)
    · rcases HElo u (lt_of_not_ge hus) with ⟨he0,hh0,_,ho0⟩
      simp only [he0,hh0,ho0,sub_zero,zero_div,le_refl]
  have Hpos : ∀u∈Icc (0:ℝ) 1,0<e u+D u-eh u:=fun u hu=>
    (movement_strength_positive (HErange u) (HDrange u) (Hfrac u hu).1 (Hfrac u hu).2 (Hupper u hu)).2
  have HEhigh : ContinuousOn e (Icc a.s 1):=HEc.continuousOn.congr HEhi
  have HHhigh : ContinuousOn eh (Icc a.s 1):=HHc.continuousOn.congr HHhi
  have HcostHigh : ContinuousOn cost (Icc a.s 1):=by
    exact (((HEhigh.mul HR.continuousOn).add (HDc.continuousOn.mul HZ.continuousOn)).sub
      (HHhigh.mul HRhat.continuousOn)).pow 2 |>.div
        ((HEhigh.add HDc.continuousOn).sub HHhigh)
        (fun u hu=>(Hpos u ⟨a.hs.1.trans hu.1,hu.2⟩).ne')
  have Hlowcost : ∀u<a.s,cost u=D u*(Z u)^2:=by
    intro u hu
    rcases HElo u hu with ⟨he0,hh0,_,_⟩
    dsimp only [cost]
    rw [he0,hh0]
    have hdne: D u≠0:=(HDrange u).ne'
    simp only [zero_mul,zero_add,sub_zero]
    field_simp [hdne]
  have HcostInt : IntervalIntegrable cost volume 0 1:=by
    apply actual_two_branch_intervalIntegrable a.hs HcostHigh
      (HDc.mul (HZ.pow 2)).continuousOn
    intro u hu
    by_cases hus : a.s≤u
    · simp only [ite_eq_left hus]
    · simpa only [ite_eq_right hus,Pi.mul_apply,Pi.pow_apply] using Hlowcost u (lt_of_not_ge hus)
  have HcostAE : ∀ᵐu∂volume,u∈Icc (0:ℝ) 1 → ContinuousWithinAt cost (Icc (0:ℝ) 1) u:=by
    have Hne : ∀ᵐu:ℝ∂volume,u≠a.s:=by simp [ae_iff]
    filter_upwards [Hne] with u hne
    intro hu
    have HEw : ContinuousWithinAt e (Icc (0:ℝ) 1) u:=
      cutoff_continuousWithinAt HEc.continuousOn hu hne
    have HHw : ContinuousWithinAt eh (Icc (0:ℝ) 1) u:=
      cutoff_continuousWithinAt HHc.continuousOn hu hne
    exact (((HEw.mul HR.continuousAt.continuousWithinAt).add
      (HDc.continuousAt.continuousWithinAt.mul HZ.continuousAt.continuousWithinAt)).sub
      (HHw.mul HRhat.continuousAt.continuousWithinAt)).pow 2 |>.div
        ((HEw.add HDc.continuousAt.continuousWithinAt).sub HHw) (Hpos u hu).ne'
  have HEint : IntervalIntegrable (fun u=>e u*(R u)^2) volume 0 1:=by
    apply cutoff_eq_intervalIntegrable a.hs ((HEhigh.mul (HR.pow 2).continuousOn))
    intro u hu
    by_cases hus : a.s≤u
    · simp only [ite_eq_left hus,Pi.mul_apply,Pi.pow_apply]
    · simp only [ite_eq_right hus,Pi.mul_apply,Pi.pow_apply,(HElo u (lt_of_not_ge hus)).1,zero_mul]
  have HHint : IntervalIntegrable (fun u=>eh u*(Rhat u)^2) volume 0 1:=by
    apply cutoff_eq_intervalIntegrable a.hs ((HHhigh.mul (HRhat.pow 2).continuousOn))
    intro u hu
    by_cases hus : a.s≤u
    · simp only [ite_eq_left hus,Pi.mul_apply,Pi.pow_apply]
    · simp only [ite_eq_right hus,Pi.mul_apply,Pi.pow_apply,(HElo u (lt_of_not_ge hus)).2.1,zero_mul]
  have HGint : IntervalIntegrable (fun u=>e u*(Rhat u-R u)*(Z u-R u)) volume 0 1:=by
    apply cutoff_eq_intervalIntegrable a.hs (HEhigh.mul (HRhat.sub HR).continuousOn |>.mul (HZ.sub HR).continuousOn)
    intro u hu
    by_cases hus : a.s≤u
    · simp only [ite_eq_left hus,Pi.mul_apply,Pi.sub_apply]
    · simp only [ite_eq_right hus,Pi.mul_apply,Pi.sub_apply,(HElo u (lt_of_not_ge hus)).1,zero_mul]
  have Hbudget : ∀u∈Icc (0:ℝ) 1,e u+D u≤a.lam+childLam:=by
    intro u hu
    have HE : e u≤a.lam:=by
      by_cases hus : a.s≤u
      · rw [HEhi u ⟨hus,hu.2⟩]
        exact laplaceComparisonStrength_le a.d a.hlam.le _
      · rw [(HElo u (lt_of_not_ge hus)).1]
        exact a.hlam.le
    have HD : D u≤childLam:=laplaceComparisonStrength_le child.d hchildLam.le _
    linarith only [HE,HD]
  have HP:=a.clockAdmissible P.alpha
  have HT:=a.clockAdmissible gamma
  have HC:=comparisonVariableEndpoint_clocks_admissible child.hc child.hk child.hkc child.hm child.hM
    (fun u=>a.b u-e u) (fun u=>a.h u+e u*R u) child.hd.ne' hchildLam.le hroom HP.1 HP.2.1
    (HP.2.2.2 0 ⟨le_rfl,zero_le_one⟩) beta
  have Hclocks : AveragedMovementClocks a.b a.h e R D Z eh Rhat:=
    ⟨HC.1,HC.2.1,HT.1,HT.2.1,HC.2.2.1,HC.2.2.2,
      HT.2.2.1 0 ⟨le_rfl,zero_le_one⟩,HT.2.2.2 0 ⟨le_rfl,zero_le_one⟩⟩
  have Hchild : pathCompensatedPressure n (fun u=>a.b u-e u) (fun u=>a.h u+e u*R u) D Z 0≤
      realOrderedSKPathPressure n (fun u=>a.b u-e u) (fun u=>a.h u+e u*R u) 0+
        variableEndpointComparisonSweepCost child.hc child.hk child.hkc child.hm child.hM n
          (fun u=>a.b u-e u) (fun u=>a.h u+e u*R u) child.d childLam:=by
    change variableEndpointComparisonSweepObjective child.hc child.hk child.hkc child.hm child.hM n
      (fun u=>a.b u-e u) (fun u=>a.h u+e u*R u) child.d childLam beta≤_
    rw [hattained]
    unfold variableEndpointComparisonSweepCost
    linarith
  exact actual_averaged_extended_child_movement_gain n a.hn a.b a.h e R D Z eh Rhat omega
    (fun u _=>HErange u) (fun u _=>HDrange u) (fun u _=>HHrange u)
    (fun u _=>HRb u) (fun u _=>HZb u) (fun u hu=>(Hfrac u hu).1) (fun u hu=>(Hfrac u hu).2)
    Hupper Hmove Hbudget HcostAE HEint (HDc.mul (HZ.pow 2)).continuousOn.intervalIntegrable
    HHint HcostInt HGint Hclocks (P.minimum gamma) Hchild

end ActualShiftedParentData
end OAI.SKFluctuations.LaplaceWindowFormalization
