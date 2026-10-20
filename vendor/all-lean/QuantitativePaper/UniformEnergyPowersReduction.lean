module

public import QuantitativePaper.UniformEnergyVarianceLower
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-! Actual SK fluctuation algebra and threshold selection. The uniform
scalar/comparison moment estimates are supplied by their separate proved
manuscript results when this reduction is applied. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 1400000

theorem uniform_energy_powers_of_mean_and_tail (β0 cshort Cmean A K : ℝ)
    (hβ0 : 1<β0) (hcshort : 0<cshort) (hCmean : 0<Cmean) (hA : 0<A) (hK : 0<K)
    (Nmean Ntail : ℕ)
    (hshort : ∀n : ℕ,0<n→∀β : ℝ,β0≤β→
      cshort*((variance (energyFreeEnergy n β) (couplingLaw n)+1/2)/(n:ℝ))^(5/4:ℝ)≤energyMeanDeficit n β)
    (hmean : ∀n : ℕ,Nmean≤n→∀β : ℝ,β0≤β→energyMeanDeficit n β≤Cmean*(n:ℝ)^(-(2/3:ℝ)))
    (htail : ∀n : ℕ,Ntail≤n→∀β : ℝ,β0≤β→Real.exp (-A*(n:ℝ)^(1/5:ℝ))≤(couplingLaw n).real
      {g | (n:ℝ)*(scalarEnergyValue β 0+K*(n:ℝ)^(-(2/3:ℝ)))≤energyFreeEnergy n β g}) :
    ∃c C : ℝ,∃N0 : ℕ,0<c ∧ 0<C ∧ ∀n : ℕ,N0≤n→∀β : ℝ,β0≤β→
      c*(n:ℝ)^(4/15:ℝ)≤variance (energyFreeEnergy n β) (couplingLaw n) ∧
      variance (energyFreeEnergy n β) (couplingLaw n)≤C*(n:ℝ)^(7/15:ℝ) ∧
      c*(n:ℝ)^(-(11/12:ℝ))≤energyMeanDeficit n β ∧
      energyMeanDeficit n β≤C*(n:ℝ)^(-(2/3:ℝ)) := by
  let d:=varianceTailRate*K/A
  have hd : 0<d := by dsimp only [d];unfold varianceTailRate;positivity
  have hp1 : Tendsto (fun n : ℕ=>A*(n:ℝ)^(1/5:ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hA ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/5)).comp
      tendsto_natCast_atTop_atTop)
  have hp2 : Tendsto (fun n : ℕ=>d^2*(n:ℝ)^(4/15:ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (sq_pos_of_pos hd) ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<4/15)).comp
      tendsto_natCast_atTop_atTop)
  obtain ⟨Ns,hNs⟩ := eventually_atTop.1
    ((hp1.eventually_ge_atTop (Real.log 3)).and (hp2.eventually_ge_atTop 2))
  let k:=d^2/2
  have hk : 0<k := by dsimp only [k];positivity
  let c:=min k (cshort*k^(5/4:ℝ))
  let C:=max Cmean ((Cmean/cshort)^(4/5:ℝ))
  let N0:=max 1 (max Ns (max Nmean Ntail))
  refine ⟨c,C,N0,lt_min hk (by positivity),(hCmean.trans_le (le_max_left _ _)),?_⟩
  intro n hn0 β hβ0β
  have hn1 : 1≤n := (le_max_left _ _).trans hn0
  have hn : 0<n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  have hns : Ns≤n := (le_max_left _ _).trans ((le_max_right _ _).trans hn0)
  have hnm : Nmean≤n := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans hn0))
  have hnt : Ntail≤n := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans hn0))
  have hβ : 1≤β := hβ0.le.trans hβ0β
  have hvLower : k*(n:ℝ)^(4/15:ℝ)≤variance (energyFreeEnergy n β) (couplingLaw n) :=
    energy_variance_lower_of_window_tail n hn β A K hβ hA hK (htail n hnt β hβ0β)
      (hNs n hns).1 (hNs n hns).2
  have hm := hmean n hnm β hβ0β
  have hs := hshort n hn β hβ0β
  have hvUpper := variance_upper_of_mean_power (n:ℝ)
    (variance (energyFreeEnergy n β) (couplingLaw n)) (energyMeanDeficit n β)
    cshort Cmean hnR (variance_nonneg _ _) hcshort hCmean hs hm
  have hmLower := mean_lower_of_variance_power (n:ℝ)
    (variance (energyFreeEnergy n β) (couplingLaw n)) (energyMeanDeficit n β)
    cshort k hnR hcshort.le hk hvLower hs
  refine ⟨?_,?_,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans hvLower
  · exact hvUpper.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans hmLower
  · exact hm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

end QuantitativePaper
