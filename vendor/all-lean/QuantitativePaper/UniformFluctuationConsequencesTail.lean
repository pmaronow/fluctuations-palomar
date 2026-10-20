module

public import QuantitativePaper.UniformFluctuationConsequencesWindow
public import QuantitativePaper.SixthWindowUniformConstants

@[expose] public section

/-! Actual finite-temperature and ground matching tails, with one set of
constants, from the genuine comparison and closed scalar floor estimates. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativePaper
set_option maxHeartbeats 1400000

theorem energy_ground_matching_tails_of_comparison (β0 Cerror Lerror : ℝ)
    (hβ0 : 1<β0) (hCerror : 0≤Cerror) (hLerror : Lerror∈Ioc (0:ℝ) 1)
    (hcomparison : ∀n : ℕ,0<n→∀β : ℝ,β0≤β→∀lam : ℝ,lam∈Ioc (0:ℝ) Lerror→
      energyComparisonError n β lam≤Cerror*((n:ℝ)^(-(2/3:ℝ))+
        (n:ℝ)^(-(3/4:ℝ))*lam^(-(1/2:ℝ))+Real.log (2+(n:ℝ))/((n:ℝ)*lam))) :
    ∃Ax xstar cx Cx : ℝ,∃N0 : ℕ,
      0<Ax ∧ 0<xstar ∧ 0<cx ∧ 0<Cx ∧ 1≤N0 ∧ ∀n : ℕ,N0≤n→
      ∀x : ℝ,Ax*(n:ℝ)^(-(2/3:ℝ))≤x→x≤xstar→
        (∀β : ℝ,β0≤β→
          Real.exp (-Cx*(n:ℝ)*x^(6/5:ℝ))≤
            (couplingLaw n).real {g | (n:ℝ)*(scalarEnergyValue β 0+x)≤energyFreeEnergy n β g} ∧
          (couplingLaw n).real {g | (n:ℝ)*(scalarEnergyValue β 0+x)≤energyFreeEnergy n β g}≤
            Real.exp (-cx*(n:ℝ)*x^(6/5:ℝ))) ∧
        Real.exp (-Cx*(n:ℝ)*x^(6/5:ℝ))≤
          (couplingLaw n).real {g | (n:ℝ)*(groundScalarValue+x)≤groundState n g} ∧
        (couplingLaw n).real {g | (n:ℝ)*(groundScalarValue+x)≤groundState n g}≤
          Real.exp (-cx*(n:ℝ)*x^(6/5:ℝ)) := by
  obtain ⟨a,C,A,L,Nw,ha,hC,haC,hA,hL,hL1,hNw,hwindow⟩:=
    energy_ground_sixth_window_of_comparison β0 Cerror Lerror hβ0 hCerror hLerror hcomparison
  obtain ⟨Nt,Ax,xstar,cx,Cx,hAx,hxs,hcx,hCx,hconvert⟩:=
    sixth_window_uniform_constants a C A L ha hC haC hA hL
  let N0:=max Nw Nt
  refine ⟨Ax,xstar,cx,Cx,N0,hAx,hxs,hcx,hCx,hNw.trans (le_max_left _ _),?_⟩
  intro n hn0 x hxlo hxhi
  have hnw : Nw≤n:=(le_max_left _ _).trans hn0
  have hnt : Nt≤n:=(le_max_right _ _).trans hn0
  have hwin:=hwindow n hnw
  refine ⟨?_,?_⟩
  · intro β hb
    have hXm : Measurable (fun g=>energyFreeEnergy n β g-(n:ℝ)*scalarEnergyValue β 0):=
      (((continuous_logPartition n β).div_const β).sub continuous_const).measurable
    have hh:=hconvert n hnt (Couplings n) (couplingLaw n)
      (fun g=>energyFreeEnergy n β g-(n:ℝ)*scalarEnergyValue β 0) hXm
      (fun s _ _=>integrable_exp_scalarCenteredEnergy n β s)
      (hwin.1 β hb).1 (hwin.1 β hb).2 x hxlo hxhi
    have he : {g | (n:ℝ)*x≤energyFreeEnergy n β g-(n:ℝ)*scalarEnergyValue β 0}=
        {g | (n:ℝ)*(scalarEnergyValue β 0+x)≤energyFreeEnergy n β g} := by
      ext g
      simp only [mem_setOf_eq]
      constructor <;> intro hg <;> nlinarith
    simpa only [he] using hh
  · have hXm : Measurable (fun g=>groundState n g-(n:ℝ)*groundScalarValue):=
      ((continuous_groundState n).sub continuous_const).measurable
    have hh:=hconvert n hnt (Couplings n) (couplingLaw n)
      (fun g=>groundState n g-(n:ℝ)*groundScalarValue) hXm
      (fun s _ _=>integrable_exp_scalarCenteredGround n s)
      hwin.2.1 hwin.2.2 x hxlo hxhi
    have he : {g | (n:ℝ)*x≤groundState n g-(n:ℝ)*groundScalarValue}=
        {g | (n:ℝ)*(groundScalarValue+x)≤groundState n g} := by
      ext g
      simp only [mem_setOf_eq]
      constructor <;> intro hg <;> nlinarith
    simpa only [he] using hh

end QuantitativePaper
