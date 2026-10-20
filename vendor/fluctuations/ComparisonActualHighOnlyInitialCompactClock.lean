module

public import ComparisonActualHighOnlyComparableContext
public import ComparisonActualHighOnlyAnalyticBasics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace ActualHighOnlyOverlapMinimum

 theorem actual_initial_compact_clock_range_along
    {m delta cl cu Az C0 Ct D Bclock Tamb t : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (Gctx : HighOnlyActualComparableBandContext M Tamb)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hTamb : 0 < Tamb) (ht : 0 < t)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Tamb)
    (C : ℝ) (hC : 0 < C)
    (hnear : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) (C*(M n).xs), |(M n).h u| ≤ (M n).xs^3) :
    ∃Rclock : ℝ,0 < Rclock ∧ ∀ᶠn in atTop,∀w : ParisiFinite.OrderPoint,
      (w:ℝ) ≤ C*(M n).xs →
        actualMixedClock (dim n+1) (M n).bf (M n).hf w/(t*(M n).xs) ∈ Icc (0:ℝ) Rclock := by
  obtain ⟨B,hB,Hmean⟩:=eventually_actual_high_only_mass_mean_upper (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cs:=B*(1+C)
  let Cr:=(Az+1/cl)*(1+C)
  let Rc:=(1+Tamb*(Cs+Cr))/t
  have hCs : 0 < Cs:=by dsimp only [Cs];positivity
  have hCr : 0 < Cr:=by dsimp only [Cr];positivity
  have hRc : 0 < Rc:=by dsimp only [Rc];positivity
  refine ⟨Rc,hRc,?_⟩
  filter_upwards [hdim.eventually Hmean,Gctx.eventually_geometric_gates,hnear,hxs.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))]
    with n hnmean hngate hnnear hnx w hw
  have hs0:=(M n).mass_mean_nonneg w.property
  have hr:=(omittedSweepQuantile_bounds zero_le_one ⟨(M n).data.hs.1,(M n).data.hs1⟩ (M n).context.hc (M n).context.hk (M n).context.hkc
    (M n).context.hm (M n).context.hM (M n).alpha (w:ℝ))
  have hh0:=(M n).hh0.trans ((M n).hh (by norm_num) w.property w.property.1)
  have hS : orderedPathS (dim n+1) (M n).bf (M n).hf w ≤ Cs*(M n).xs:=by
    by_cases hw0 : (w:ℝ)=0
    · simp only [hw0,orderedPathS,orderedPathPair_zero]
      exact mul_nonneg hCs.le (M n).hxs.le
    · have H:=hnmean (M n) hngate.2 hngate.1 w ⟨lt_of_le_of_ne w.property.1 (Ne.symm hw0),w.property.2⟩
      have HH:=mul_le_mul_of_nonneg_left (show (M n).xs+(w:ℝ) ≤ (1+C)*(M n).xs by linarith only [hw]) hB.le
      exact H.trans (by dsimp only [Cs];nlinarith only [HH])
  have hR : (M n).R w ≤ Cr*(M n).xs:=by
    have H:=(M n).inverse_radius_le_source_mass hcl hAz w.property
    have HH:=mul_le_mul_of_nonneg_left (show (M n).xs+(w:ℝ) ≤ (1+C)*(M n).xs by linarith only [hw])
      (show 0 ≤ Az+1/cl by positivity)
    exact H.trans (by dsimp only [Cr];nlinarith only [HH])
  let e:=(M n).coefficient w
  have he0 : 0 ≤ e:=(M n).coefficient_nonneg w
  have heb : e ≤ (M n).b w:=by
    have H:=((M n).bf w).coe_nonneg
    rw [((M n).inherited_clock_coe w.property).1] at H
    exact sub_nonneg.mp H
  have hbT : (M n).b w ≤ Tamb:=by linarith only [htotal n w w.property,hh0]
  have heT : e ≤ Tamb:=heb.trans hbT
  have hhh : (M n).h w ≤ (M n).xs:=by
    have H:=(le_abs_self ((M n).h w)).trans (hnnear w ⟨w.property.1,hw⟩)
    have HX: (M n).xs^3 ≤ (M n).xs:=by nlinarith only [(M n).hxs,hnx,sq_nonneg ((M n).xs),mul_nonneg (M n).hxs.le (sub_nonneg.mpr hnx)]
    exact H.trans HX
  rw [(M n).inherited_mixed_clock_eq_nativeScalarClock w.property]
  have hlow : 0 ≤ comparisonNativeScalarClock ((M n).h w) ((M n).b w) e ((M n).R w)
      (orderedPathS (dim n+1) (M n).bf (M n).hf w):=by
    unfold comparisonNativeScalarClock
    exact add_nonneg (add_nonneg hh0 (mul_nonneg he0 hr.1)) (mul_nonneg (sub_nonneg.mpr heb) hs0)
  have HER:=mul_le_mul heT hR hr.1 hTamb.le
  have HBS:=mul_le_mul hbT hS hs0 hTamb.le
  have hup : comparisonNativeScalarClock ((M n).h w) ((M n).b w) e ((M n).R w)
      (orderedPathS (dim n+1) (M n).bf (M n).hf w) ≤ (1+Tamb*(Cs+Cr))*(M n).xs:=by
    unfold comparisonNativeScalarClock
    nlinarith only [HER,HBS,hhh,mul_nonneg he0 hs0]
  refine ⟨div_nonneg hlow (mul_pos ht (M n).hxs).le,?_⟩
  apply (div_le_iff₀ (mul_pos ht (M n).hxs)).mpr
  exact hup.trans_eq (by dsimp only [Rc];field_simp [ht.ne'])

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
