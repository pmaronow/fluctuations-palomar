module

public import QuantitativePaper.SixthWindowEnergy
public import QuantitativePaper.SixthWindowAsymptotics

@[expose] public section

/-! The actual finite SK sixth-power cumulant window from the scalar floor
cost bounds and the literal improved comparison estimate. The cutoff is
selected here, uniformly in temperature; no model cumulant bound is supplied. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativePaper
set_option maxHeartbeats 1400000

theorem energy_sixth_window_of_uniform_cost_comparison (β0 c0 C0 L Cerror : ℝ)
    (hβ0 : 1<β0) (hc0 : 0<c0) (hC0 : 0<C0) (hL : 0<L)
    (hLβ : L≤β0/2) (hCerror : 0≤Cerror)
    (hcost : ∀β : ℝ,β0≤β→∀lam : ℝ,lam∈Ioc (0:ℝ) L→
      c0*lam^5≤ scalarEnergyValue β lam-scalarEnergyValue β 0 ∧
      scalarEnergyValue β lam-scalarEnergyValue β 0≤C0*lam^5)
    (hcomparison : ∀n : ℕ,0<n→∀β : ℝ,β0≤β→∀lam : ℝ,lam∈Ioc (0:ℝ) L→
      energyComparisonError n β lam≤Cerror*((n:ℝ)^(-(2/3:ℝ))+
        (n:ℝ)^(-(3/4:ℝ))*lam^(-(1/2:ℝ))+Real.log (2+(n:ℝ))/((n:ℝ)*lam))) :
    ∃A : ℝ,0<A ∧ ∃N0 : ℕ,1≤N0 ∧ ∀n : ℕ,N0≤n→∀β : ℝ,β0≤β→
      (∀lam : ℝ,0<lam→lam≤L→scalarCenteredEnergyLogMoment n β lam≤C0*(n:ℝ)*lam^6) ∧
      (∀lam : ℝ,A*(n:ℝ)^(-(2/15:ℝ))≤lam→lam≤L→
        c0/2*(n:ℝ)*lam^6≤ scalarCenteredEnergyLogMoment n β lam) := by
  obtain ⟨A,hA,N0,hN0,hsmall⟩:=exists_sixth_window_error_cutoff c0 Cerror hc0 hCerror
  refine ⟨A,hA,N0,hN0,?_⟩
  intro n hn0 β hβ0β
  have hn : 0<n := lt_of_lt_of_le Nat.zero_lt_one (hN0.trans hn0)
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  have hβ : 0<β := (zero_lt_one.trans hβ0).trans_le hβ0β
  have hfrac {lam : ℝ} (hl : 0<lam) (hu : lam≤L) : lam/β∈Ioo (0:ℝ) 1 := by
    refine ⟨div_pos hl hβ,(div_lt_one hβ).2 ?_⟩
    have hh:=hu.trans hLβ
    linarith
  refine ⟨fun lam hl hu=>energy_sixth_moment_upper n hn β hβ lam C0 hl
    (hfrac hl hu) (hcost β hβ0β lam ⟨hl,hu⟩).2,?_⟩
  intro lam hcut hu
  have hl : 0<lam := (by positivity : 0<A*(n:ℝ)^(-(2/15:ℝ))).trans_le hcut
  have he : energyComparisonError n β lam≤c0/4*lam^5 := by
    have hh:=sixth_comparison_error_normalization (n:ℝ) A lam
      (energyComparisonError n β lam) Cerror hnR hA hCerror hl hcut
      (hcomparison n hn β hβ0β lam ⟨hl,hu⟩)
    exact (div_le_iff₀ (pow_pos hl 5)).mp (hh.trans (hsmall n hn0).1)
  have hd : lam^2/4≤c0/4*(n:ℝ)*lam^6 := by
    have hh:=sixth_diagonal_error_normalization (n:ℝ) A lam hnR hA hl hcut
    have hr:=(div_le_iff₀ (by positivity : 0<(n:ℝ)*lam^6)).mp
      (hh.trans (hsmall n hn0).2)
    simpa only [mul_assoc] using hr
  exact energy_sixth_moment_lower n hn β lam c0 hl (hcost β hβ0β lam ⟨hl,hu⟩).1 he hd

end QuantitativePaper
