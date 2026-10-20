module

public import ComparisonActualHighWallCriticalCapExhaustion
public import ComparisonActualHighWallWholeThermalCore
public import ComparisonActualHighWallFloorThermalDistinct
public import ComparisonActualHighWallOuterThermal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 500000
namespace ActualHighWallOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eventually_actual_high_wall_critical_band_thermal_rate
    {c C : ℝ} (hc : 0 < c) (hC : c < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D) :
    ∃K : ℝ,0<K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock),
      a.xs=a.data.d → comparisonSmallMass a.data.N a.data.E≤c*a.data.d →
      32*a.data.s<c*a.data.d → 2*a.data.N^(-(10:ℝ))<comparisonSmallMass a.data.N a.data.E →
      1≤Real.log a.data.N → C*a.data.d≤1 →
      (∫u in Ioo (c*a.data.d) (C*a.data.d),
        orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2) ≤
        10*C*a.data.N^(-actualMassSavingExponent m delta)*a.data.d^3*
          (Nat.ceil (Real.log (1/comparisonSmallMass a.data.N a.data.E)/Real.log 2)+1)+
        (∫u in 0..min (8*a.criticalMassCoverBase) 1,a.shiftedNativeModel.thermal u)+
        K*(a.data.d+C*a.data.d)^2*a.data.N^(-delta)*
          comparisonSmallMass a.data.N a.data.E := by
  have HC:=eventually_actual_high_wall_critical_cap_contact_thermal_rate
    (Bclock:=Bclock) hc hC hm hdelta hroom hcl hcu hAz hC0 hCt hD
  obtain ⟨K,hK,HF⟩:=eventually_actual_high_wall_floor_thermal_on_band
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨K,hK,?_⟩
  filter_upwards [HC,HF] with n hnC hnF
  intro a hfixed hU hstart hcutU hlog hhi
  obtain ⟨P⟩:=a.exists_potential
  let model:=a.shiftedNativeModel
  let lo:=c*a.data.d
  let hi:=C*a.data.d
  let A:=model.massSlice lo hi
  have hlohi:lo≤hi:=mul_le_mul_of_nonneg_right hC.le a.data.hd.le
  have hslo:a.data.s≤lo:=by dsimp only [lo] at *;linarith [a.data.hs.1]
  have hloI:lo∈Icc a.data.s 1:=⟨hslo,hlohi.trans hhi⟩
  have hhiI:hi∈Icc a.data.s 1:=⟨hslo.trans hlohi,hhi⟩
  have hA:MeasurableSet A:=measurableSet_Ioo
  have hAD:A⊆Ioo a.data.rmin 1:=fun r hr=>
    ⟨(model.R_bounds lo).1.trans_lt hr.1,hr.2.trans_le (model.R_bounds hi).2⟩
  have hscale:∀r∈A,lo≤a.alpha.val.val r ∧ a.alpha.val.val r≤hi:=by
    intro r hr
    have HL:=a.alpha.val.property.2 hr.1.le
    have HR:=a.alpha.val.property.2 hr.2.le
    rw [model.R_spec hloI] at HL
    rw [model.R_spec hhiI] at HR
    exact ⟨HL,HR⟩
  have Hcap:=hnC a hfixed hU hstart hcutU hlog P A hA hAD hscale
  rw [P.cap_contact_massSlice_integral hloI hhiI hlohi,
    intervalIntegral.integral_of_le hlohi,integral_Ioc_eq_integral_Ioo] at Hcap
  have Hfloor:=hnF a P lo hi hslo hlohi hhi
  rw [hfixed] at Hfloor
  change (∫u in Ioo lo hi,model.thermal u) ≤ _
  rw [P.mass_thermal_slab_decomposition hslo hlohi hhi]
  dsimp only [lo,hi,model] at Hcap Hfloor ⊢
  linarith only [Hcap,Hfloor]

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
