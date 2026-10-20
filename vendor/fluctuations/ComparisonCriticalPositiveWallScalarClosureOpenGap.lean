module

public import ComparisonCriticalPositiveWallScalarClosureCompact
public import ComparisonCriticalPositiveWallScalarClockCompactRange
public import ComparisonCriticalPositiveWallRadiusDefectFromEq19
public import ComparisonActualHighWallOriginsAlong
public import ComparisonAECompactIntervalExhaustion

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000

theorem critical_positive_wall_scalar_closure_open_gap_of_physical_radius_L1
    {m delta cl cu Az C0 Ct D Bclock Tloc T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hTloc : 0 < Tloc) (hT : 0 < T)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hTeq : ∀n,(M n).data.T=T)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (alpha : ℕ→boundedMassProfiles)
    (V : ℝ→ℝ)
    (hCDF : ∀r,Tendsto (fun n=>(M n).alpha.val.val ((M n).xs*r)/(M n).xs)
      atTop (𝓝 (V r)))
    (s : NonnegativeMassProfile)
    (hspin : ∀r,Tendsto (fun n=>(M n).actualScaledRadiusSpin r)
      atTop (𝓝 (s.mass r)))
    (g : ℝ→ℝ)
    (hG : ∀Q>0,TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse hTloc (alpha n)) T (M n).xs) g atTop (Icc (0:ℝ) Q))
    (hgc : ∀Q>0,ContinuousOn g (Icc (0:ℝ) Q))
    {a b : ℝ} (ha : 0 ≤ a)
    (hL1 : ∀u∈Ioo a b,∀v∈Ioo a b,u<v→
      Tendsto (fun n=>(∫r in Ioo ((M n).xs*u) ((M n).xs*v),
        |(M n).radiusS r-scalarCovarianceResponse hTloc (alpha n)
          (actualMixedClock (dim n+1) (M n).bf (M n).hf
            ((M n).alpha.val.val r))|)/(M n).xs^4) atTop (𝓝 0)) :
    ∀ᵐt∂volume.restrict (Ioo a b),
      g (s.mass t)=laplaceComparisonShape t/T*(s.mass t-t) := by
  have Hrmin := ActualHighWallOverlapMinimum.rmin_over_larger_scale_tendsto_zero
    hdelta dim hdim M (fun n=>(M n).xs) (fun n=>(hfixed n).ge)
  apply comparison_ae_on_open_interval_of_compact_interiors
  intro u hu v hv huv
  have hu0 : 0 < u := ha.trans_lt hu.1
  obtain ⟨Q0,hQ0,Hclock⟩ := eventually_critical_positive_wall_scalar_clock_compact_range
    hm hdelta (by linarith only [hmargin,hdelta]) hcl hcu hAz hC0 hCt hT
    dim hdim M hfixed hTeq hx Hrmin V hCDF hu0 huv.le
  let Q := max Q0 (s.mass v+1)
  have hQ : 0 < Q := hQ0.trans_le (le_max_left _ _)
  have Hrange : ∀ᶠn in atTop,∀t∈Icc u v,
      actualMixedClock (dim n+1) (M n).bf (M n).hf
        ((M n).alpha.val.val ((M n).xs*t))/(T*(M n).xs)∈Icc (0:ℝ) Q := by
    filter_upwards [Hclock] with n hn t ht
    exact ⟨(hn t ht).1,(hn t ht).2.trans (le_max_left _ _)⟩
  have Hspinrange : ∀t∈Icc u v,s.mass t∈Icc (0:ℝ) Q := by
    intro t ht
    refine ⟨s.nonneg t,?_⟩
    have H := s.monotone ht.2
    have H' : s.mass v ≤ Q := by
      dsimp only [Q]
      linarith [le_max_right Q0 (s.mass v+1)]
    exact H.trans H'
  exact critical_positive_wall_scalar_closure_compact_of_physical_radius_L1
    hTloc hT dim M hfixed hTeq hx Hrmin alpha g s.mass hu0 huv.le
    (fun t _=>hspin t) (hG Q hQ)
    (fun t ht=>(hgc Q hQ) _ (Hspinrange t ht)) Hrange
    (hL1 u hu v hv huv)

end OAI.SKFluctuations.LaplaceWindowFormalization
