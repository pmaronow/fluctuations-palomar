module

public import ComparisonNativeActualFullWeightedMass
public import ComparisonNativeActualInitialMassChargesAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace NativeOverlapMinimum

 theorem actual_high_strength_full_weighted_mass_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Tamb t : ℝ}
    (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hroom : 0 < 3*m+delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/(M n).xs^2) atTop atTop)
    (C : ℝ) (hC : 0 ≤ C) (v : ℕ→ℝ) (hv : ∀n,v n ∈ Icc (0:ℝ) 1)
    (hvc : ∀n,v n ≤ C*(M n).xs)
    (hTamb : 0 < Tamb) (ht : 0 < t)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Tamb)
    (hcav0 : Tendsto (fun n=>∫w : ParisiFinite.OrderPoint,
      |(M n).inheritedScalarCavityResidual hTamb (htotal n) w/(M n).xs^3|
      ∂comparisonNormalizedClockMass (M n).xs (v n)) atTop (𝓝 0))
    (hbare0 : Tendsto (fun n=>∫w : ParisiFinite.OrderPoint,
      |(((M n).b w-t)*orderedPathS (dim n+1) (M n).bf (M n).hf w+(M n).h w)/(M n).xs^3|
      ∂comparisonNormalizedClockMass (M n).xs (v n)) atTop (𝓝 0))
    (Rclock : ℝ)
    (hclock : ∀ᶠn in atTop,∀w : ParisiFinite.OrderPoint,(w:ℝ) ≤ v n →
      actualMixedClock (dim n+1) (M n).bf (M n).hf w/(t*(M n).xs) ∈ Icc (0:ℝ) Rclock)
    (g : ℝ→ℝ)
    (hG : TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse hTamb ((M n).inheritedScalarMassProfile hTamb (htotal n))) t (M n).xs)
      g atTop (Icc (0:ℝ) Rclock)) (hg : ContinuousOn g (Icc (0:ℝ) Rclock)) :
    (∀n,Integrable (fun w : ParisiFinite.OrderPoint =>
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R w)*
        (orderedPathS (dim n+1) (M n).bf (M n).hf w-(M n).R w)/(M n).xs^3)
      (comparisonNormalizedClockMass (M n).xs (v n))) ∧
    Tendsto (fun n=>∫w : ParisiFinite.OrderPoint,
      |laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R w)*
        (orderedPathS (dim n+1) (M n).bf (M n).hf w-(M n).R w)/(M n).xs^3|
      ∂comparisonNormalizedClockMass (M n).xs (v n)) atTop (𝓝 0) := by
  classical
  let nu:=fun n=>comparisonNormalizedClockMass (M n).xs (v n)
  let Gamma:=fun n=>scalarCovarianceResponse hTamb ((M n).inheritedScalarMassProfile hTamb (htotal n))
  let h0:=fun n (w : ParisiFinite.OrderPoint)=>(M n).h w
  let b0:=fun n (w : ParisiFinite.OrderPoint)=>(M n).b w
  let S:=fun n (w : ParisiFinite.OrderPoint)=>orderedPathS (dim n+1) (M n).bf (M n).hf w
  let rad:=fun n (w : ParisiFinite.OrderPoint)=>(M n).R w
  let e:=fun n w=>laplaceComparisonStrength (M n).context.d (M n).lam (rad n w)
  let weighted:=fun n w=>e n w*(S n w-rad n w)/(M n).xs^3
  let cavity:=fun n (w : ParisiFinite.OrderPoint)=>(M n).inheritedScalarCavityResidual hTamb (htotal n) w/(M n).xs^3
  let bare:=fun n w=>((b0 n w-t)*S n w+h0 n w)/(M n).xs^3
  let clock:=fun n (w : ParisiFinite.OrderPoint)=>actualMixedClock (dim n+1) (M n).bf (M n).hf w/(t*(M n).xs)
  let G:=fun n=>comparisonRescaledScalarResponse (Gamma n) t (M n).xs
  have hw n : Integrable (weighted n) (nu n):=(M n).original_weighted_mismatch_integrable _ _
  have hc n : Integrable (cavity n) (nu n):=(M n).inherited_scalar_cavity_residual_normalized_integrable hTamb (htotal n) _ _
  have hb n : Integrable (bare n) (nu n):=(M n).inherited_bare_residual_integrable (T:=t) _ _
  obtain ⟨eta,heta,hetalim,Hoff⟩:=actual_high_strength_off_floor_weighted_mass_saving_along hdelta hcl hAz dim hdim M hlarge C hC
  let Q n:=∃p : (M n).Potential,∀z∈Icc (0:ℝ) 1,z ≤ C*(M n).xs →
    (∫u in 0..z,p.offFloorWeightedDiscrepancy u)/(M n).xs^4 ≤ eta n
  let F n : Set ParisiFinite.OrderPoint:=if H : Q n then (Classical.choose H).originalOrderFloor else ∅
  have hF n : MeasurableSet (F n):=by
    dsimp only [F];split
    · rename_i H
      exact (Classical.choose H).originalOrderFloor_measurable
    · exact MeasurableSet.empty
  have Hfloor : Tendsto (fun n=>(nu n).real (F n)) atTop (𝓝 0):=by
    apply squeeze_zero (fun _=>measureReal_nonneg) _
      (actual_floor_mass_ratio_tendsto_zero_along hC0 hroom dim hdim M (fun n=>(M n).xs) (fun _=>le_rfl))
    intro n
    dsimp only [F]
    split
    · rename_i H
      exact (Classical.choose H).originalOrderFloor_normalized_mass_le _ (M n).hxs
    · rw [measureReal_empty]
      exact div_nonneg (mul_nonneg (Real.rpow_nonneg (M n).context.hN.le _) (M n).context.hU.le) (M n).hxs.le
  have Hclock : ∀ᶠn in atTop,∀ᵐw∂nu n,w∈F n → clock n w∈Icc (0:ℝ) Rclock:=by
    filter_upwards [hclock] with n hn
    have HH:∀ᵐw∂(uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v n},
        w∈F n → clock n w∈Icc (0:ℝ) Rclock:=by
      filter_upwards [ae_restrict_mem (measurableSet_le measurable_subtype_coe measurable_const)] with w hw _
      exact hn w hw
    rw [ae_iff] at HH ⊢
    change (ENNReal.ofReal (1/(M n).xs) • (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v n}) _=0
    rw [Measure.smul_apply,HH,smul_zero]
  have Heq n w : weighted n w=t*G n (clock n w)+t*cavity n w+bare n w:=by
    have H:=comparison_scalar_weighted_error_reconstruction_on Gamma h0 b0 e S rad
      (fun n=>(M n).xs) ht.ne' (fun n=>(M n).hxs.ne') n w
    have Hclockeq : comparisonScalarMassClockOn h0 b0 e S rad n w=
        actualMixedClock (dim n+1) (M n).bf (M n).hf w :=
      ((M n).inherited_mixed_clock_eq_nativeScalarClock w.property).symm
    rw [Hclockeq] at H
    exact H
  have HfloorW:=comparison_scalar_floor_weighted_L1_tendsto nu (fun _=>inferInstance)
    F hF weighted cavity bare clock G g ht hw hc hb Heq Hclock hG hg Hfloor hcav0 hbare0
  have HoffW : Tendsto (fun n=>∫w in (F n)ᶜ,|weighted n w|∂nu n) atTop (𝓝 0):=by
    apply squeeze_zero' (Eventually.of_forall (fun _=>integral_nonneg (fun _=>abs_nonneg _))) _ hetalim
    filter_upwards [Hoff] with n hn
    have Hn : Q n:=hn
    dsimp only [F];rw [dite_eq_left Hn]
    rw [(Classical.choose Hn).original_off_floor_weighted_integral_exact (hv n)]
    exact Classical.choose_spec Hn (v n) (hv n) (hvc n)
  refine ⟨hw,?_⟩
  have Hsum:=HfloorW.add HoffW
  simp only [zero_add] at Hsum
  apply Hsum.congr'
  exact Eventually.of_forall (fun n=>integral_add_compl (hF n) (hw n).abs)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
