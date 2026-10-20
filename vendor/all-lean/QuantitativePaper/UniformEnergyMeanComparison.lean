module

public import QuantitativePaper.UniformEnergyMeanPrebound
public import QuantitativePaper.SixthWindowAsymptotics

@[expose] public section

/-! Uniform mean-deficit consequence of the literal improved comparison.
The model mean, Chen tangent and diagonal cancellation are actual; only
the separately proved comparison estimate is consumed by this reduction. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 1400000

theorem energy_mean_uniform_of_trial_comparison (β0 Ctrial Cerror L : ℝ)
    (hβ0 : 1<β0) (htrialC : 0≤Ctrial) (herrorC : 0≤Cerror)
    (hL : 0<L) (hLβ : L≤β0/2)
    (htrial : ∀β : ℝ,β0≤β→∀lam : ℝ,lam∈Ioc (0:ℝ) L→
      scalarEnergyValue β lam-scalarEnergyValue β 0≤Ctrial*lam^5)
    (hcomparison : ∀n : ℕ,0<n→∀β : ℝ,β0≤β→∀lam : ℝ,lam∈Ioc (0:ℝ) L→
      energyComparisonError n β lam≤Cerror*((n:ℝ)^(-(2/3:ℝ))+
        (n:ℝ)^(-(3/4:ℝ))*lam^(-(1/2:ℝ))+Real.log (2+(n:ℝ))/((n:ℝ)*lam))) :
    ∃Cmean : ℝ,0<Cmean ∧ ∃N0 : ℕ,1≤N0 ∧ ∀n : ℕ,N0≤n→∀β : ℝ,β0≤β→
      energyMeanDeficit n β≤Cmean*(n:ℝ)^(-(2/3:ℝ)) := by
  have htilt : Tendsto (fun n : ℕ=>(n:ℝ)^(-(2/15:ℝ))) atTop (𝓝 0):=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<2/15)).comp tendsto_natCast_atTop_atTop
  have herr:=tendsto_sixth_comparison_remainder 1 Cerror
  obtain ⟨Ns,hNs⟩:=eventually_atTop.1
    ((htilt.eventually_le_const (by positivity : (0:ℝ)<L/2)).and
      (herr.eventually_le_const (by norm_num : Cerror*(1:ℝ)^(-(5:ℝ))<Cerror+1)))
  let N0:=max 1 Ns
  let Cmean:=32*Ctrial+2*(Cerror+1)
  refine ⟨Cmean,by dsimp only [Cmean];positivity,N0,le_max_left _ _,?_⟩
  intro n hn0 β hb
  have hn1 : 1≤n:=(le_max_left _ _).trans hn0
  have hn : 0<n:=Nat.zero_lt_one.trans_le hn1
  have hnR : 0<(n:ℝ):=by exact_mod_cast hn
  have hβ : 0<β:=zero_lt_one.trans (hβ0.trans_le hb)
  let lam:=(n:ℝ)^(-(2/15:ℝ))
  have hlam : 0<lam:=Real.rpow_pos_of_pos hnR _
  have hsmall:=hNs n ((le_max_right _ _).trans hn0)
  have hlam2 : 2*lam≤L:=by dsimp only [lam];linarith [hsmall.1]
  have hfrac : (2*lam)/β∈Ioo (0:ℝ) 1:=⟨div_pos (by positivity) hβ,
    (div_lt_one hβ).2 (by linarith [hlam2.trans hLβ])⟩
  have hp : lam^5=(n:ℝ)^(-(2/3:ℝ)):=by
    dsimp only [lam]
    rw [←Real.rpow_mul_natCast hnR.le]
    norm_num
  have hnerror : energyComparisonError n β lam≤(Cerror+1)*lam^5:=by
    have he:=sixth_comparison_error_normalization (n:ℝ) 1 lam
      (energyComparisonError n β lam) Cerror hnR (by norm_num) herrorC hlam
      (by dsimp only [lam];simp)
      (hcomparison n hn β hb lam ⟨hlam,by linarith⟩)
    have hnorm : energyComparisonError n β lam/lam^5≤Cerror+1:=
      he.trans (by simpa only [Real.one_rpow,one_mul] using hsmall.2)
    exact (div_le_iff₀ (pow_pos hlam 5)).mp hnorm
  have hm:=energyMeanDeficit_midpoint_bound n hn β hβ lam Ctrial hlam hfrac
    (htrial β hb (2*lam) ⟨by positivity,hlam2⟩)
  have hh : energyMeanDeficit n β≤Cmean*lam^5:=by
    dsimp only [Cmean]
    nlinarith
  simpa only [hp] using hh

end QuantitativePaper
