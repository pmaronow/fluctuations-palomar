module

public import QuantitativePaper.UniformFluctuationConsequencesTail
public import QuantitativePaper.UniformEnergyMeanComparison
public import QuantitativePaper.ShortVarianceMeanProposition
public import QuantitativePaper.UniformEnergyPowersReduction
public import QuantitativePaper.GroundFluctuationPassage

@[expose] public section

/-! All four actual finite/ground fluctuation powers, with common
constants. The improved comparison is the only remaining external input
to this supporting application. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 1800000

theorem energy_ground_four_powers_of_comparison (β0 Cerror Lerror : ℝ)
    (hβ0 : 1<β0) (hCerror : 0≤Cerror) (hLerror : Lerror∈Ioc (0:ℝ) 1)
    (hcomparison : ∀n : ℕ,0<n→∀β : ℝ,β0≤β→∀lam : ℝ,lam∈Ioc (0:ℝ) Lerror→
      energyComparisonError n β lam≤Cerror*((n:ℝ)^(-(2/3:ℝ))+
        (n:ℝ)^(-(3/4:ℝ))*lam^(-(1/2:ℝ))+Real.log (2+(n:ℝ))/((n:ℝ)*lam))) :
    ∃c C : ℝ,∃N0 : ℕ,0<c ∧ 0<C ∧ 1≤N0 ∧ ∀n : ℕ,N0≤n→
      (∀β : ℝ,β0≤β→
        c*(n:ℝ)^(4/15:ℝ)≤variance (energyFreeEnergy n β) (couplingLaw n) ∧
        variance (energyFreeEnergy n β) (couplingLaw n)≤C*(n:ℝ)^(7/15:ℝ) ∧
        c*(n:ℝ)^(-(11/12:ℝ))≤energyMeanDeficit n β ∧
        energyMeanDeficit n β≤C*(n:ℝ)^(-(2/3:ℝ))) ∧
      c*(n:ℝ)^(4/15:ℝ)≤groundStateVariance n ∧
      groundStateVariance n≤C*(n:ℝ)^(7/15:ℝ) ∧
      c*(n:ℝ)^(-(11/12:ℝ))≤groundMeanDeficit n ∧
      groundMeanDeficit n≤C*(n:ℝ)^(-(2/3:ℝ)) := by
  obtain ⟨c0,Ctrial,Lcost,hc0,hCtrial,hLcost,hLcost1,hLcostβ,hcost⟩:=scalar_fisher_lower β0 hβ0
  let L:=min Lcost Lerror
  have hL : 0<L:=lt_min hLcost hLerror.1
  have hLβ : L≤β0/2:=(min_le_left _ _).trans hLcostβ
  obtain ⟨Cmean,hCmean,Nmean,hNmean,hmean⟩:=
    energy_mean_uniform_of_trial_comparison β0 Ctrial Cerror L hβ0
      (zero_le_one.trans hCtrial) hCerror hL hLβ
      (fun β hb lam hlam=>(hcost β hb lam ⟨hlam.1,hlam.2.trans (min_le_left _ _)⟩).2)
      (fun n hn β hb lam hlam=>hcomparison n hn β hb lam
        ⟨hlam.1,hlam.2.trans (min_le_right _ _)⟩)
  obtain ⟨Ax,xstar,cx,Cx,Ntail,hAx,hxs,hcx,hCx,hNtail,htails⟩:=
    energy_ground_matching_tails_of_comparison β0 Cerror Lerror hβ0 hCerror hLerror hcomparison
  have hs : Tendsto (fun n : ℕ=>Ax*(n:ℝ)^(-(2/3:ℝ))) atTop (𝓝 0):=by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<2/3)).comp
      tendsto_natCast_atTop_atTop).const_mul Ax
  obtain ⟨Ns,hNs⟩:=eventually_atTop.1 (hs.eventually_le_const hxs)
  let Nt:=max 1 (max Ntail Ns)
  let Aprob:=Cx*Ax^(6/5:ℝ)
  have hAprob : 0<Aprob:=by dsimp only [Aprob];positivity
  have htail (n : ℕ) (hn0 : Nt≤n) (β : ℝ) (hb : β0≤β) :
      Real.exp (-Aprob*(n:ℝ)^(1/5:ℝ))≤(couplingLaw n).real
        {g | (n:ℝ)*(scalarEnergyValue β 0+Ax*(n:ℝ)^(-(2/3:ℝ)))≤energyFreeEnergy n β g} := by
    have hn : 0<n:=Nat.zero_lt_one.trans_le ((le_max_left _ _).trans hn0)
    have hnR : 0<(n:ℝ):=by exact_mod_cast hn
    have hnt : Ntail≤n:=(le_max_left _ _).trans ((le_max_right _ _).trans hn0)
    have hns : Ns≤n:=(le_max_right _ _).trans ((le_max_right _ _).trans hn0)
    have hh:=((htails n hnt (Ax*(n:ℝ)^(-(2/3:ℝ))) le_rfl (hNs n hns)).1 β hb).1
    have hp : (n:ℝ)*(Ax*(n:ℝ)^(-(2/3:ℝ)))^(6/5:ℝ)=
        Ax^(6/5:ℝ)*(n:ℝ)^(1/5:ℝ) := by
      rw [Real.mul_rpow hAx.le (Real.rpow_nonneg hnR.le _),←Real.rpow_mul hnR.le]
      norm_num
      have he : (n:ℝ)*(n:ℝ)^(-(4/5:ℝ))=(n:ℝ)^(1/5:ℝ):=by
        calc
          _=(n:ℝ)^(1:ℝ)*(n:ℝ)^(-(4/5:ℝ)) := by rw [Real.rpow_one]
          _=(n:ℝ)^((1:ℝ)+(-(4/5:ℝ))) := (Real.rpow_add hnR _ _).symm
          _=_ := by congr 1;norm_num
      calc
        _=Ax^(6/5:ℝ)*((n:ℝ)*(n:ℝ)^(-(4/5:ℝ))) := by ring
        _=_ := by rw [he]
    convert hh using 1
    congr 1
    dsimp only [Aprob]
    rw [show -Cx*(n:ℝ)*(Ax*(n:ℝ)^(-(2/3:ℝ)))^(6/5:ℝ)=
      -Cx*((n:ℝ)*(Ax*(n:ℝ)^(-(2/3:ℝ)))^(6/5:ℝ)) by ring,hp]
    ring
  obtain ⟨cshort,hcshort,hshort⟩:=short_variance_mean β0 hβ0
  obtain ⟨c,C,Nf,hc,hC,hfinite⟩:=uniform_energy_powers_of_mean_and_tail
    β0 cshort Cmean Aprob Ax hβ0 hcshort hCmean hAprob hAx Nmean Nt hshort hmean htail
  let N0:=max 1 Nf
  refine ⟨c,C,N0,hc,hC,le_max_left _ _,?_⟩
  intro n hn0
  have hfin:=hfinite n ((le_max_right _ _).trans hn0)
  have hvar:=tendsto_energyVariance_groundStateVariance n
  have hm:=tendsto_energyMeanDeficit_groundMeanDeficit n
  refine ⟨hfin,?_,?_,?_,?_⟩
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds hvar
      ((eventually_ge_atTop β0).mono fun β hb=>(hfin β hb).1)
  · exact le_of_tendsto_of_tendsto hvar tendsto_const_nhds
      ((eventually_ge_atTop β0).mono fun β hb=>(hfin β hb).2.1)
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds hm
      ((eventually_ge_atTop β0).mono fun β hb=>(hfin β hb).2.2.1)
  · exact le_of_tendsto_of_tendsto hm tendsto_const_nhds
      ((eventually_ge_atTop β0).mono fun β hb=>(hfin β hb).2.2.2)

end QuantitativePaper
