module

public import ComparisonActualHighOnlyAbsoluteDisagreementMass
public import ComparisonActualHighOnlyOverlapMinimum
public import ComparisonNativeOuterAbsoluteDisagreementMass
public import FinitePhysicalPropagationBarrierSelectionTransfer

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 16000000
namespace ActualHighOnlyOverlapMinimum

theorem actual_high_only_successful_child_fixed_mass_agreement
    {m delta cl cu Az C0 Ct D Bclock c0 xlo : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0) (hc0 : 0 < c0) (hxlo : 0 < xlo)
    (N : ℕ→ℕ) (hN : Tendsto N atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (N n) m delta cl cu Az C0 Ct D Bclock)
    (a : (n:ℕ)→ActualHighOnlyChildBarrierCall (N n) delta)
    (hxs : ∀n,(M n).xs∈Icc xlo 1)
    (hparent : ∀n,(a n).context.E=(M n).context.E ∧ (a n).context.d=(M n).context.d ∧
      (a n).lam=(M n).lam ∧ (a n).R=(M n).R ∧ (a n).context.s=(M n).context.s)
    (hchild : ∀ᶠn in atTop,(a n).childRadius=c0*(M n).xs ∧ (a n).childLam=(c0*(M n).xs)^2 ∧
      (a n).err ≤ (N n:ℝ)^(20*delta)*actualChildErrorBudget (N n) delta c0
        (M n).context.d (M n).lam (M n).xs)
    (hs : Tendsto (fun n=>(M n).context.s) atTop (𝓝 0))
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam ((M n).xs)/(M n).xs^2)
      atTop (𝓝 0)) :
    ∀left right eps theta : ℝ,0 < left → left < right → right ≤ 1 → 0 < eps → 0 < theta →
      ∀ᶠn in atTop,volume (physicalPropagationDisagreementMassSet (M n).R (a n).Z left right eps)<ENNReal.ofReal theta := by
  intro left right eps theta hleft _hlr hright heps htheta
  let step := eps/3
  obtain ⟨J,hJ⟩ := exists_nat_gt (1/(step*xlo))
  have hstep : 0 < step := by dsimp [step];positivity
  have hJ' : 1 < (J:ℝ)*(step*xlo) := (div_lt_iff₀ (mul_pos hstep hxlo)).mp hJ
  let ell := theta/(4*((J:ℝ)+1))
  have hell : 0 < ell := by dsimp [ell];positivity
  obtain ⟨eta,heta,heta1,Hmass⟩ := eventually_actual_high_only_absolute_disagreement_mass_le
    (Dbound:=D) (eps:=step) (ell:=ell) J hdelta (show 0 < 1/C0 by positivity) hm hc0 hstep hell
  have Hweak := hweak.eventually (gt_mem_nhds (pow_pos heta 3))
  have Hs := hs.eventually (gt_mem_nhds hleft)
  filter_upwards [hN.eventually Hmass,Hweak,Hs,hchild] with n hn hw hsn hc
  rcases hparent n with ⟨he,hd,hl,hR,hsame⟩
  have hlo : (1/C0)*(N n:ℝ)^(-(2:ℝ)/3+m)*(a n).context.d ≤ (a n).context.E := by
    rw [hd,he]
    have H := mul_le_mul_of_nonneg_left (M n).hlower (show 0 ≤ 1/C0 by positivity)
    simpa only [←mul_assoc,one_div_mul_cancel hC0.ne',one_mul] using H
  have hwe : (a n).e (M n).xs ≤ eta^3*(M n).xs^2 := by
    have H := (div_le_iff₀ (sq_pos_of_pos (M n).hxs)).mp hw.le
    simpa only [ActualHighOnlyChildBarrierCall.e,hd,hl] using H
  have hcap : ∀u∈Icc left right,(a n).R u ≤ (J:ℝ)*(step*(M n).xs) := by
    intro u _
    have Hx := mul_le_mul_of_nonneg_left (hxs n).1 (show 0 ≤ (J:ℝ)*step by positivity)
    have Hr := (a n).radius_bounds u
    exact Hr.2.trans (by nlinarith only [hJ',Hx])
  have H := hn (a n) (M n).xs left right
    (by simpa only [hd] using (M n).hdD)
    (by simpa only [hd,he] using (M n).hupper) hlo ⟨(M n).hxs,(hxs n).2⟩
    (by simpa only [hd,he] using (M n).hscale)
    (by simpa only [hd,hl] using (M n).hld) hwe hc.1 hc.2.1
    (by simpa only [hd,hl] using hc.2.2)
    (by rw [hsame];exact hsn.le) hright hcap
  have Hsub : physicalPropagationDisagreementMassSet (M n).R (a n).Z left right eps ⊆
      {u | u∈Icc left right ∧ 3*(step*(M n).xs) ≤ |(a n).Z u-(a n).R u|} := by
    intro u hu
    refine ⟨hu.1,?_⟩
    rw [hR]
    have Hx := mul_le_mul_of_nonneg_left (hxs n).2 heps.le
    dsimp only [step]
    nlinarith only [Hx,hu.2.le]
  have Hsmall := native_disagreement_measure_coefficient_lt J htheta (M n).hxs
  have Hlast : ENNReal.ofReal (theta*(M n).xs) ≤ ENNReal.ofReal theta :=
    ENNReal.ofReal_le_ofReal (by nlinarith [mul_le_mul_of_nonneg_left (hxs n).2 htheta.le])
  exact ((measure_mono Hsub).trans H).trans_lt (Hsmall.trans_le Hlast)

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
