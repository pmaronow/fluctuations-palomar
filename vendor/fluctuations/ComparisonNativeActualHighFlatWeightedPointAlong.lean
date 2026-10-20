module

public import ComparisonNativeActualFlatCapMismatch
public import ComparisonSignedCavityMinimumSourceClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 18000000
namespace NativeOverlapMinimum

theorem actual_high_strength_flat_weighted_point_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/(M n).xs^2)
      atTop atTop)
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠn in atTop,∃p : (M n).Potential,
      ∀ᵐu,u∈Icc (0:ℝ) 1 → u ≤ C*(M n).xs → p.H ((M n).R u) ≤ 0 →
        |laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)*
          (orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u)|/(M n).xs^3 ≤
          Real.log ((1+(M n).context.U)/(M n).context.U)/(M n).context.N^delta := by
  let K:=(Az+1/cl)*(1+C)
  have hK:0 < K:=by dsimp only [K];positivity
  have HPow:=(((tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop).comp
    ((tendsto_add_atTop_nat 1).comp hdim)).eventually (eventually_ge_atTop 2)
  have Hflat:=comparison_strength_eventually_flat_of_divergence
    (fun n=>(M n).context.d) (fun n=>(M n).lam) (fun n=>(M n).xs)
    (Eventually.of_forall (fun n=>⟨(M n).context.hd,(M n).hlam,(M n).hxs,(M n).hld⟩)) hlarge hK
  filter_upwards [HPow,Hflat] with n hnPow hnFlat
  obtain ⟨p⟩:=(M n).exists_potential (by simpa only [NativeOverlapContext.N,Function.comp_def] using hnPow)
  refine ⟨p,?_⟩
  have hx:0 < (M n).xs:=(M n).hxs
  have HF:∀r∈Icc (0:ℝ) (K*(M n).xs),
      comparisonLogSlope (laplaceComparisonStrength (M n).context.d (M n).lam) r=0:=by
    intro r hr
    have ht:r/(M n).xs∈Icc (0:ℝ) K:=⟨div_nonneg hr.1 hx.le,(div_le_iff₀ hx).mpr hr.2⟩
    have H:=(hnFlat (r/(M n).xs) ht).2.1
    simpa only [mul_div_cancel₀ r hx.ne'] using H
  filter_upwards [p.flat_nonpositive_abs_mismatch_ae_mass HF] with u hu hui hux hnonpos
  have HR:=(M n).inverse_radius_le_source_mass hcl hAz hui
  have hR:(M n).R u ≤ K*(M n).xs:=by
    have HH:=mul_le_mul_of_nonneg_left (show (M n).xs+u ≤ (1+C)*(M n).xs by linarith only [hux])
      (show 0 ≤ Az+1/cl by positivity)
    exact HR.trans (by convert HH using 1;dsimp only [K];ring)
  have Hm:=hu hui hR hnonpos
  have he:=laplaceComparisonStrength_pos (M n).context.d (M n).hlam ((M n).R u)
  rw [abs_mul,abs_of_pos he]
  have Hmajor:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left Hm he.le) (pow_pos hx 3).le
  exact Hmajor.trans ((M n).weighted_cap_travel_normalized_le ((M n).R u))

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
