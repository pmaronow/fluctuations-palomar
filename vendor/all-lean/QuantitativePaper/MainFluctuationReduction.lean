module

public import QuantitativePaper.MainFluctuationTargets
public import QuantitativePaper.UniformFluctuationConsequencesPowers

@[expose] public section

/-! Literal main-theorem assembly from the actual improved comparison.
This file is supporting: its explicit comparison hypothesis is discharged
by the final model-only theorem wrappers. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
namespace QuantitativePaper
set_option maxHeartbeats 1400000

def UniformAbsoluteComparisonHypothesis : Prop :=
  ∀β0 : ℝ,1<β0→∃C L : ℝ,0<C ∧ L∈Ioc (0:ℝ) 1 ∧
    ∀n : ℕ,0<n→∀β : ℝ,β0≤β→∀lam : ℝ,lam∈Ioc (0:ℝ) L→
      energyComparisonError n β lam≤C*((n:ℝ)^(-(2/3:ℝ))+
        (n:ℝ)^(-(3/4:ℝ))*lam^(-(1/2:ℝ))+Real.log (2+(n:ℝ))/((n:ℝ)*lam))

theorem main_ground_fluctuations_of_comparison (hcomp : UniformAbsoluteComparisonHypothesis) :
    MainGroundFluctuationsTarget := by
  obtain ⟨Ce,L,hCe,hL,hc⟩:=hcomp 2 (by norm_num)
  obtain ⟨c,C,N0,hcp,hCp,hN0,hpowers⟩:=energy_ground_four_powers_of_comparison
    2 Ce L (by norm_num) hCe.le hL hc
  refine ⟨c,C,N0,hcp,hCp,hN0,?_⟩
  intro n hn
  simpa only [groundMeanDeficit] using (hpowers n hn).2

theorem main_fixed_temperature_fluctuations_of_comparison
    (hcomp : UniformAbsoluteComparisonHypothesis) : MainFixedTemperatureFluctuationsTarget := by
  intro β hβ
  let β0:=(β+1)/2
  have hb0 : 1<β0:=by dsimp only [β0];linarith
  have hb : β0≤β:=by dsimp only [β0];linarith
  obtain ⟨Ce,L,hCe,hL,hc⟩:=hcomp β0 hb0
  obtain ⟨c,C,N0,hcp,hCp,hN0,hpowers⟩:=energy_ground_four_powers_of_comparison
    β0 Ce L hb0 hCe.le hL hc
  obtain ⟨co,Co,hco,hCo,hfinite⟩:=fixed_temperature_four_powers_of_energy β c C
    (zero_lt_one.trans hβ) hcp hCp N0 hN0 (fun n hn=>(hpowers n hn).1 β hb)
  exact ⟨co,Co,N0,hco,hCo,hN0,hfinite⟩

theorem main_upper_tails_of_comparison (hcomp : UniformAbsoluteComparisonHypothesis) :
    MainUpperTailsTarget := by
  intro β hβ
  let β0:=(β+1)/2
  have hb0 : 1<β0:=by dsimp only [β0];linarith
  have hb : β0≤β:=by dsimp only [β0];linarith
  obtain ⟨Ce,L,hCe,hL,hc⟩:=hcomp β0 hb0
  obtain ⟨A,xstar,c,C,N0,hA,hxs,hcp,hCp,hN0,htails⟩:=
    energy_ground_matching_tails_of_comparison β0 Ce L hb0 hCe.le hL hc
  obtain ⟨Ao,xo,co,Co,hAo,hxo,hco,hCo,hfinite⟩:=fixed_temperature_tails_of_energy
    β A xstar c C (zero_lt_one.trans hβ) hA hxs hcp hCp N0 hN0
    (fun n hn x hlo hhi=>(htails n hn x hlo hhi).1 β hb)
  exact ⟨Ao,xo,co,Co,N0,hAo,hxo,hco,hCo,hN0,hfinite⟩

theorem main_uniform_upper_tails_of_comparison (hcomp : UniformAbsoluteComparisonHypothesis) :
    MainUniformUpperTailsTarget := by
  obtain ⟨Ce,L,hCe,hL,hc⟩:=hcomp 2 (by norm_num)
  obtain ⟨A,xstar,c,C,N0,hA,hxs,hcp,hCp,hN0,htails⟩:=
    energy_ground_matching_tails_of_comparison 2 Ce L (by norm_num) hCe.le hL hc
  refine ⟨A,xstar,c,C,N0,hA,hxs,hcp,hCp,hN0,?_⟩
  intro n hn x hlo hhi
  simpa only [scalarEnergyValue_zero_eq_pressure_scaled] using htails n hn x hlo hhi

end QuantitativePaper
