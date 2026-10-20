module

public import ComparisonNativeStarCapSaving

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4000000

theorem eventually_comparison_actual_buffer_polynomial (k : ℕ) (Bclock : ℝ)
    {m delta gamma c1 saving Q K Cprof Ccap Fcap cFloor Ddepth Lcap : ℝ}
    (hm : 0 < m) (hdelta : 0 ≤ delta) (hgamma : 0 < gamma) (hmargin : delta<3*m)
    (hsaving : saving<(3*m-delta)/8-c1)
    (hK : 1 ≤ K) (hCprof : 0 ≤ Cprof) (hCcap : 0 ≤ Ccap)
    (hcFloor : 0 < cFloor) (hDepth : 0 ≤ Ddepth) (hLcap : 0 ≤ Lcap) :
    ∀ᶠn:ℕ in atTop,∀
      (steps:List (GaussianStep (FeatureIndex n))) (ha:OrderedSteps 0 steps)
      (q0:FeatureIndex n → ℝ≥0) (xs:ℝ) (hxs:0 < xs)
      (w:PhysicalBandWindow n steps xs) (dfield:GaussianStep (FeatureIndex n) → ℝ≥0)
      (d lam E x L v:ℝ),
      0 < d  →  0 < lam  →  lam ≤ d^2  →  0 < E  → 
      gamma*(n:ℝ)^(-(2:ℝ)/3+m)*d ≤ E  →  E ≤ d^2/Real.sqrt n  → 
      0 < x  →  (n:ℝ)^delta*Real.sqrt n*E/Real.sqrt lam ≤ x  →  x ≤ w.a  → 
      w.A ≤ comparisonCap n delta (comparisonSmallMass n E) (comparisonConstraintLength n E d) E d (Cprof*w.a)  → 
      (∀st∈steps,∀i:Fin n,st.2 (Sum.inl i)=dfield st)  → 
      physicalFieldDuration dfield steps ≤ Bclock  → 
      (∀s∈Ioc w.a w.b,w.D₀ ≤ physicalFieldDuration dfield (steps.take (radiusGridCut w.radius (s+w.η)))-
        physicalFieldDuration dfield (steps.take (radiusGridCut w.radius s)))  → 
      (∀r∈Icc (2*w.a) ((2:ℝ)^w.depth*w.b),w.D₀ ≤
        physicalFieldDuration dfield (steps.take (radiusGridCut w.radius r))-
        physicalFieldDuration dfield (steps.take (radiusGridCut w.radius (3*r/4))))  → 
      physicalRawRatio n (k+1) steps 0 xs (Measure.pi fun i=>gaussianReal 0 (q0 i)) id measurable_id ≤ Q  → 
      w.b ≤ K*w.a  →  w.mass ≤ K*w.C*w.a  →  0 < L  →  0 < w.A  → 
      w.η=(1/Real.sqrt (w.A*((n:ℝ)*laplaceComparisonStrength d lam w.a*w.a^4)))*w.a  → 
      (1/Real.sqrt (w.A*((n:ℝ)*laplaceComparisonStrength d lam w.a*w.a^4)))*w.a*
        laplaceComparisonStrength d lam w.a/L ≤ w.D₀  → 
      w.C ≤ Ccap  →  w.F ≤ Fcap  →  cFloor ≤ w.c₀  →  1 ≤ Real.log (n:ℝ)  → 
      (w.depth:ℝ) ≤ Ddepth*Real.log (n:ℝ)  →  L ≤ Lcap*Real.log (n:ℝ)  → 
      (n:ℝ)^(-c1)*w.a ≤ w.mass  →  w.a ≤ v  → 
      physicalBufferCenteredNorm n steps q0 (physicalWindowWeight steps 0 w.selected)
        (2*(k+1):ℕ) ≤ (n:ℝ)^(-saving)*v := by
  let R:=((2*(Cprof+1)+(Cprof+1)^2)/gamma^3)
  have hR : 0 ≤ R := by dsimp only [R];positivity
  filter_upwards [NativeStarBuffer.eventually_physical_buffer_polynomial_native_scale k Bclock
    (by linarith : 0 < 3*m-delta) hR hsaving hK hCcap hcFloor hDepth hLcap,
    eventually_comparison_star_actual_cap_saving hm hdelta hgamma hCprof,
    eventually_gt_atTop (0:ℕ)] with n hn hcap hn0
  intro steps ha q0 xs hxs w dfield d lam E x L v hd hlam hld hE hlo hup hx hrange hxa hAcap
    hfield hB hfirst hdyad hQ hb hm hL hA heta hclock hC hF hc hlog hdepth hLmax hmass hav
  have hN : 0 < (n:ℝ) := by exact_mod_cast hn0
  have hwa : 0 < w.a := hx.trans_le hxa
  have hg := laplaceComparisonStrength_pos d hlam w.a
  have hactual := hcap d lam E x w.a hd hlam hld hE hlo hup hx hrange hxa
  have hratio : w.A/((n:ℝ)*laplaceComparisonStrength d lam w.a*w.a^4) ≤ R*(n:ℝ)^(-(3*m-delta)) :=
    (div_le_div_of_nonneg_right hAcap (by positivity)).trans hactual
  exact hn steps ha q0 xs hxs w dfield (laplaceComparisonStrength d lam w.a) L v
    hfield hB hfirst hdyad hQ hb hm hg hL hA heta hclock hC hF hc hlog hdepth hLmax hratio hmass hav

end OAI.SKFluctuations.LaplaceWindowFormalization
