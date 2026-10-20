module

public import ComparisonActualHighOnlyMacroscopicScalarCompetitor
public import ComparisonActualHighOnlyMacroscopicEndpointCost
public import ComparisonShiftedQuantileCDF

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 7000000
namespace ActualHighOnlyComparisonData
variable {n : ℕ} {delta : ℝ} (a : ActualHighOnlyComparisonData n delta)

theorem radiusUnitBounds (alpha : a.Profile) (u : ℝ) (_hu : u∈Icc (0:ℝ) 1) :
    a.R alpha u∈Icc (0:ℝ) 1 :=
  omittedSweepQuantile_bounds zero_le_one ⟨a.hs.1,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha u

def inverseSequence (alpha : a.Profile) : ComparisonShiftedInverseSequence where
  origin:=fun _=>0
  u0:=fun _=>a.s
  c:=fun _=>a.k 1
  k:=fun _=>a.k
  M:=fun _=>a.M
  hwork:=fun _=>zero_le_one
  hc:=fun _=>a.hc
  hk:=fun _=>a.hk
  hkc:=fun _=>a.hkc
  hm:=fun _=>a.hm
  hM:=fun _=>a.hM
  alpha:=fun _=>alpha

theorem radius_cdf_on (alpha : a.Profile) {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    (quantileMassProfile (a.R alpha) (a.radiusUnitBounds alpha)).val r=
      alpha.val.val r := by
  exact (a.inverseSequence alpha).radius_cdf_eq_inverse (fun _=>le_rfl) 0 hr

theorem radius_massProfile_eq_of_scalar (alpha : a.Profile)
    (hscalar : alpha.val∈scalarProfiles) :
    quantileMassProfile (a.R alpha) (a.radiusUnitBounds alpha)=alpha.val := by
  apply Subtype.ext
  funext r
  by_cases hr0:r<0
  · exact ((quantileMassProfile_mem (a.R alpha) (a.radiusUnitBounds alpha)).1 r hr0).trans
      (hscalar.1 r hr0).symm
  · by_cases hr1:1<r
    · exact ((quantileMassProfile_mem (a.R alpha) (a.radiusUnitBounds alpha)).2 r hr1).trans
        (hscalar.2 r hr1).symm
    · exact a.radius_cdf_on alpha ⟨not_lt.mp hr0,not_lt.mp hr1⟩

theorem macroScalarTrial_scalarProfile {eta Q : ℝ} (alpha : MacroInverseClass eta Q)
    (heta : 0<eta) (hfloor : ∀r∈Icc (0:ℝ) 1,a.k r≤eta/2)
    (hcap : ∀u∈Icc (0:ℝ) 1,Q≤a.M u) :
    (a.macroScalarTrial alpha heta hfloor hcap).val∈scalarProfiles := by
  constructor
  · intro r hr
    simp only [macroScalarTrial,macroInitialMassInVariableClass,macroInitialMassProfile,ite_eq_left hr]
  · intro r hr
    have Halpha:alpha.val.val r=1:=by
      have H:=alpha.val.property.2 hr.le
      rw [alpha.property.2.1] at H
      exact le_antisymm (alpha.val.property.1 r).2 H
    change (macroInitialMassProfile alpha ⟨a.hs.1,a.hs1⟩).val r=1
    rw [macroInitialMassProfile_on alpha ⟨a.hs.1,a.hs1⟩ (zero_le_one.trans hr.le),Halpha]
    ring

theorem physicalScalarQuantileValue_of_scalar {T : ℝ} (hT : 0<T)
    (alpha : a.Profile) (hscalar : alpha.val∈scalarProfiles) :
    physicalScalarQuantileValue n T (a.R alpha)=scalarParisiValue hT alpha.val := by
  rw [←scalar_physical_quantile_value n a.hn hT (a.R alpha)
    ((a.radiusProfile alpha).property.2.monotoneOn _)
    (a.radiusUnitBounds alpha),a.radius_massProfile_eq_of_scalar alpha hscalar]

end ActualHighOnlyComparisonData
end OAI.SKFluctuations.LaplaceWindowFormalization
