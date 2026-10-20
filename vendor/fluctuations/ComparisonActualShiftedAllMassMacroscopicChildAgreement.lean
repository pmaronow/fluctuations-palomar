module

public import ComparisonActualShiftedAllMassAbsoluteDisagreementMass
public import ComparisonNativeOuterAbsoluteDisagreementMass
public import FinitePhysicalPropagationBarrierSelectionTransfer

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 14000000

theorem actual_shifted_allmass_successful_child_fixed_mass_agreement
    {m delta C0 D c0 xlo:ℝ} (hm:0 < m) (hdelta:0 < delta) (hC0:0 < C0) (hc0:0 < c0) (hxlo:0 < xlo)
    (N:ℕ→ℕ) (hN:Tendsto N atTop atTop)
    (a:(n:ℕ)→ActualShiftedAllMassParentChildCall (N n) delta) (x:ℕ→ℝ)
    (hx:∀n,x n∈Icc xlo 1)
    (hnum:∀n,(a n).context.d ≤ D ∧ Real.sqrt (N n:ℝ)*(a n).context.E ≤ (a n).context.d^2 ∧
      (N n:ℝ)^(-(2:ℝ)/3+m)*(a n).context.d ≤ C0*(a n).context.E ∧
      comparisonLowerScale (N n) (a n).context.E (a n).context.d ≤ x n)
    (hchild:∀ᶠn in atTop,(a n).childRadius=c0*x n ∧ (a n).childLam=(c0*x n)^2 ∧
      (a n).err ≤ (N n:ℝ)^(20*delta)*actualChildErrorBudget (N n) delta c0 (a n).context.d (a n).lam (x n))
    (hs:Tendsto (fun n=>(a n).context.s) atTop (𝓝 0))
    (hr:Tendsto (fun n=>(a n).context.r0) atTop (𝓝 0))
    (hweak:Tendsto (fun n=>(a n).e (x n)/(x n)^2) atTop (𝓝 0)):
    ∀left right eps theta:ℝ,0 < left → left < right → right ≤ 1 → 0 < eps → 0 < theta →
      ∀ᶠn in atTop,volume (physicalPropagationDisagreementMassSet (a n).R (a n).Z left right eps)<ENNReal.ofReal theta:=by
  intro left right eps theta hleft _hlr hright heps htheta
  let step:=eps/3
  have hstep:0 < step:=by dsimp [step];positivity
  obtain ⟨J,hJ⟩:=exists_nat_gt (1/(step*xlo))
  have hJ':1 < (J:ℝ)*(step*xlo):=(div_lt_iff₀ (mul_pos hstep hxlo)).mp hJ
  let ell:=theta/(4*((J:ℝ)+1))
  have hell:0 < ell:=by dsimp [ell];positivity
  obtain ⟨eta,heta,_heta1,Hmass⟩:=eventually_actual_shifted_allmass_absolute_disagreement_mass_le
    (Dbound:=D) (eps:=step) (ell:=ell) J hdelta (show 0 < 1/C0 by positivity) hm hc0 hstep hell
  have Hweak:=hweak.eventually (gt_mem_nhds (pow_pos heta 3))
  have Hs:=hs.eventually (gt_mem_nhds hleft)
  have Hr:=hr.eventually (gt_mem_nhds (show 0 < (step*xlo)/(4*((J:ℝ)+2)) by positivity))
  filter_upwards [hN.eventually Hmass,Hweak,Hs,Hr,hchild] with n hn hw hsn hrn hc
  have hxpos:0 < x n:=hxlo.trans_le (hx n).1
  have hlo:(1/C0)*(N n:ℝ)^(-(2:ℝ)/3+m)*(a n).context.d ≤ (a n).context.E:=by
    have H:=mul_le_mul_of_nonneg_left (hnum n).2.2.1 (show 0 ≤ 1/C0 by positivity)
    simpa only [←mul_assoc,one_div_mul_cancel hC0.ne',one_mul] using H
  have hwe:(a n).e (x n) ≤ eta^3*(x n)^2:=(div_le_iff₀ (sq_pos_of_pos hxpos)).mp hw.le
  have hcap:∀u∈Icc left right,(a n).R u ≤ (J:ℝ)*(step*x n):=by
    intro u _
    have Hx:=mul_le_mul_of_nonneg_left (hx n).1 (show 0 ≤ (J:ℝ)*step by positivity)
    exact ((a n).radius_bounds u).2.trans (by nlinarith only [hJ',Hx])
  have horigin:(a n).context.r0 ≤ (step*x n)/(4*((J:ℝ)+2)):=
    hrn.le.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hx n).1 hstep.le) (by positivity))
  have H:=hn (a n) (x n) left right (hnum n).1 (hnum n).2.1 hlo ⟨hxpos,(hx n).2⟩
    (hnum n).2.2.2 (a n).hld hwe hc.1 hc.2.1 hc.2.2 horigin hsn.le hright hcap
  have Hsub:physicalPropagationDisagreementMassSet (a n).R (a n).Z left right eps ⊆
      {u | u∈Icc left right ∧ 3*(step*x n) ≤ |(a n).Z u-(a n).R u|}:=by
    intro u hu
    refine ⟨hu.1,?_⟩
    have Hx:=mul_le_mul_of_nonneg_left (hx n).2 heps.le
    dsimp only [step]
    nlinarith only [Hx,hu.2.le]
  have Hsmall:=native_disagreement_measure_coefficient_lt J htheta hxpos
  have Hlast:ENNReal.ofReal (theta*x n) ≤ ENNReal.ofReal theta:=
    ENNReal.ofReal_le_ofReal (by nlinarith [mul_le_mul_of_nonneg_left (hx n).2 htheta.le])
  exact ((measure_mono Hsub).trans H).trans_lt (Hsmall.trans_le Hlast)

end OAI.SKFluctuations.LaplaceWindowFormalization
