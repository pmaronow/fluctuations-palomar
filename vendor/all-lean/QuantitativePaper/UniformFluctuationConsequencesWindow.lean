module

public import QuantitativePaper.ScalarFisherLowerProposition
public import QuantitativePaper.SixthWindowUniformReduction

@[expose] public section

/-! Genuine finite and ground cumulant-window application. Only the
manuscript's separately proved improved comparison is supplied here. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 1400000

theorem energy_ground_sixth_window_of_comparison (β0 Cerror Lerror : ℝ)
    (hβ0 : 1<β0) (hCerror : 0≤Cerror) (hLerror : Lerror∈Ioc (0:ℝ) 1)
    (hcomparison : ∀n : ℕ,0<n→∀β : ℝ,β0≤β→∀lam : ℝ,lam∈Ioc (0:ℝ) Lerror→
      energyComparisonError n β lam≤Cerror*((n:ℝ)^(-(2/3:ℝ))+
        (n:ℝ)^(-(3/4:ℝ))*lam^(-(1/2:ℝ))+Real.log (2+(n:ℝ))/((n:ℝ)*lam))) :
    ∃a C A L : ℝ,∃N0 : ℕ,
      0<a ∧ 0<C ∧ a≤C ∧ 0<A ∧ 0<L ∧ L≤1 ∧ 1≤N0 ∧
      ∀n : ℕ,N0≤n→
        (∀β : ℝ,β0≤β→
          (∀lam : ℝ,0<lam→lam≤L→scalarCenteredEnergyLogMoment n β lam≤C*(n:ℝ)*lam^6) ∧
          (∀lam : ℝ,A*(n:ℝ)^(-(2/15:ℝ))≤lam→lam≤L→
            a*(n:ℝ)*lam^6≤ scalarCenteredEnergyLogMoment n β lam)) ∧
        (∀lam : ℝ,0<lam→lam≤L→scalarCenteredGroundLogMoment n lam≤C*(n:ℝ)*lam^6) ∧
        (∀lam : ℝ,A*(n:ℝ)^(-(2/15:ℝ))≤lam→lam≤L→
          a*(n:ℝ)*lam^6≤ scalarCenteredGroundLogMoment n lam) := by
  obtain ⟨c0,C0,Lcost,hc0,hC0,hLcost,hLcost1,hLcostβ,hcostFull⟩:=scalar_fisher_lower β0 hβ0
  let L:=min Lcost Lerror
  have hL : 0<L:=lt_min hLcost hLerror.1
  have hL1 : L≤1:=(min_le_left _ _).trans hLcost1
  have hLβ : L≤β0/2:=(min_le_left _ _).trans hLcostβ
  have hcost (β : ℝ) (hb : β0≤β) (lam : ℝ) (hlam : lam∈Ioc (0:ℝ) L) :=
    hcostFull β hb lam ⟨hlam.1,hlam.2.trans (min_le_left _ _)⟩
  have hC0p : 0<C0:=zero_lt_one.trans_le hC0
  obtain ⟨A,hA,N0,hN0,hwindow⟩:=energy_sixth_window_of_uniform_cost_comparison
    β0 c0 C0 L Cerror hβ0 hc0 hC0p hL hLβ hCerror hcost
    (fun n hn β hb lam hlam=>hcomparison n hn β hb lam
      ⟨hlam.1,hlam.2.trans (min_le_right _ _)⟩)
  let C:=max C0 (c0/2)
  have hCp : 0<C:=hC0p.trans_le (le_max_left _ _)
  refine ⟨c0/2,C,A,L,N0,by positivity,hCp,le_max_right _ _,hA,hL,hL1,hN0,?_⟩
  intro n hn0
  have hn : 0<n:=Nat.zero_lt_one.trans_le (hN0.trans hn0)
  have hnR : 0<(n:ℝ):=by exact_mod_cast hn
  have hupper (β : ℝ) (hb : β0≤β) (lam : ℝ) (hl : 0<lam) (hu : lam≤L) :
      scalarCenteredEnergyLogMoment n β lam≤C*(n:ℝ)*lam^6:=
    ((hwindow n hn0 β hb).1 lam hl hu).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hnR.le) (pow_nonneg hl.le _))
  refine ⟨fun β hb=>⟨hupper β hb,(hwindow n hn0 β hb).2⟩,?_,?_⟩
  · intro lam hl hu
    exact le_of_tendsto_of_tendsto (scalarCenteredEnergyLogMoment_ground_limit n lam)
      tendsto_const_nhds ((eventually_ge_atTop β0).mono
        (fun β hb=>hupper β hb lam hl hu))
  · intro lam hcut hu
    have hl : 0<lam:=(by positivity : 0<A*(n:ℝ)^(-(2/15:ℝ))).trans_le hcut
    exact (ground_sixth_moment_bounds_of_energy n lam
      (c0/2*(n:ℝ)*lam^6) (C*(n:ℝ)*lam^6) β0
      (fun β hb=>⟨(hwindow n hn0 β hb).2 lam hcut hu,hupper β hb lam hl hu⟩)).1

end QuantitativePaper
