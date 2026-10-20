module

public import ComparisonScalarClosureIdentification

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 3000000

theorem comparison_scalar_closure_identification_combined_bare
    (Gamma : ℕ → ℝ → ℝ) (h0 b0 e s x : ℕ → ℝ) (g : ℝ → ℝ)
    {T t hl sl : ℝ} {A : Set ℝ}
    (hT : T≠0) (hx0 : ∀n,x n≠0) (hx : Tendsto x atTop (𝓝 0))
    (he : Tendsto (fun n=>e n/(x n)^2) atTop (𝓝 hl))
    (hs : Tendsto (fun n=>s n/x n) atTop (𝓝 sl))
    (hz : Tendsto (fun n=>((b0 n-T)*s n+h0 n)/(x n)^3) atTop (𝓝 0))
    (hG : TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse (Gamma n) T (x n)) g atTop A)
    (hgc : ContinuousWithinAt g A sl)
    (hKA : ∀ᶠn in atTop,comparisonNativeScalarClock (h0 n) (b0 n) (e n) (x n*t) (s n)/(T*x n)∈A)
    (hrho : Tendsto (fun n=>(s n-Gamma n (comparisonNativeScalarClock (h0 n) (b0 n) (e n)
      (x n*t) (s n)))/(x n)^3) atTop (𝓝 0)) :
    g sl=hl/T*(sl-t) := by
  have hclock : Tendsto (fun n=>comparisonNativeScalarClock (h0 n) (b0 n) (e n)
      (x n*t) (s n)/(T*x n)) atTop (𝓝 sl) := by
    have H := hs.sub (((hx.pow 2).div_const T).mul ((he.mul (hs.sub_const t)).sub hz))
    simpa only [comparison_scalar_clock_scaled_exact hT (hx0 _),zero_pow (by norm_num : 2≠0),
      zero_div,zero_mul,sub_zero] using H
  have hscalar := hG.tendsto_comp hgc (tendsto_nhdsWithin_iff.mpr ⟨hclock,hKA⟩)
  have hright := (hscalar.add hrho).add (hz.div_const T)
  have hleft := (he.div_const T).mul (hs.sub_const t)
  have H : Tendsto (fun n=>(e n/(x n)^2)/T*(s n/x n-t)) atTop (𝓝 (g sl)) := by
    convert hright using 1
    · ext n
      exact comparison_scalar_response_closure_exact (Gamma n) hT (hx0 n)
    · simp
  exact tendsto_nhds_unique H hleft

end OAI.SKFluctuations.LaplaceWindowFormalization
