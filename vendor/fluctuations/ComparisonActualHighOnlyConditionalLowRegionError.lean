module

public import ComparisonActualHighOnlyConditionalFiniteWallSource

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 14000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
variable (a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)

def conditionalLowRadiusRegion (V:ℝ):Set ℝ:=Ioo (0:ℝ) 1∩{r|a.alpha.val.val r ≤ V}

theorem conditionalLowRadiusRegion_measurable (V:ℝ):MeasurableSet (a.conditionalLowRadiusRegion V):=
  measurableSet_Ioo.inter (measurableSet_le a.alpha.val.property.2.measurable measurable_const)

theorem error_profile_level_mask_zero_high_only (V:ℝ) :
    (∫u in 0..1,({r|a.alpha.val.val r=V}:Set ℝ).indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u)=0 := by
  apply Eq.trans ?_ (intervalIntegral.integral_zero : (∫u in (0:ℝ)..1,(0:ℝ))=0)
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne V] with u huV hu
  have hui:u∈Ioc (0:ℝ) 1:=by simpa only [uIoc_of_le zero_le_one] using hu
  by_cases hlow:u < a.data.s
  · rw [a.comparisonErrorDensity_low_zero hlow,mul_zero]
  · have HS:a.alpha.val.val (a.R u)=u:=a.shiftedNativeModel.R_spec ⟨le_of_not_gt hlow,hui.2⟩
    have Hnot:a.R u∉({r|a.alpha.val.val r=V}:Set ℝ):=by
      intro H
      exact huV (HS.symm.trans H)
    rw [indicator_of_notMem Hnot,zero_mul]

theorem error_low_radius_region_le_prefix_high_only {V:ℝ} (hV:V∈Icc (0:ℝ) 1) :
    (∫u in 0..1,(a.conditionalLowRadiusRegion V).indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u) ≤
      ∫u in 0..V,a.comparisonErrorDensity u := by
  apply a.error_mask_integral_le_mass_prefix_high_only _ (a.conditionalLowRadiusRegion_measurable V) hV
  intro u hu HS
  have hhigh:a.data.s < u:=a.radius_high_mass HS.1.1
  have HR:a.alpha.val.val (a.R u)=u:=a.shiftedNativeModel.R_spec ⟨hhigh.le,hu.2⟩
  exact HR ▸ HS.2

variable {a}

theorem Potential.conditional_wall_contact_mem_high_only
    (P:a.Potential) (F:Finset (ordConnectedSection P.negativeSet))
    {r:ℝ} (hr:r∈Ioo (0:ℝ) 1) (hc:r∈P.contactSet)
    (hupper:a.alpha.val.val r ≤ min (32*a.data.s) 1)
    (hne:a.alpha.val.val r≠min (32*a.data.s) 1) : r∈P.conditionalWallSupport F := by
  have hαr: a.alpha.val.val r∈Icc a.data.s 1:=
    inverseConstraint_mass_mem zero_le_one a.data.hc a.data.hk a.data.hkc a.alpha (Ioo_subset_Icc_self hr)
  have hcut:min (32*a.data.s) 1∈Icc a.data.s 1:=
    ⟨le_min (by linarith [a.data.hs.1]) a.data.hs1,min_le_right _ _⟩
  have H:=a.shiftedNativeModel.R_strictMonoOn hαr hcut (lt_of_le_of_ne hupper hne)
  rw [a.shiftedNativeModel.R_inverse (Ioo_subset_Icc_self hr)] at H
  exact ⟨⟨hr.1,H⟩,Or.inr hc.2⟩

theorem Potential.conditional_wall_cap_mem_high_only
    (P:a.Potential) (F:Finset (ordConnectedSection P.negativeSet)) (t:F)
    (hleft:0 < (P.capFamily F t).left)
    (hupper:a.alpha.val.val (P.capFamily F t).right ≤ min (32*a.data.s) 1)
    {r:ℝ} (hr:r∈Ioo (P.capFamily F t).left (P.capFamily F t).right) : r∈P.conditionalWallSupport F := by
  have H:(P.capFamily F t).right ≤ a.R (min (32*a.data.s) 1):=by
    calc (P.capFamily F t).right=a.R (a.alpha.val.val (P.capFamily F t).right):=
           (a.shiftedNativeModel.R_inverse ⟨(P.capFamily F t).hleft.trans (P.capFamily F t).hlt.le,
             (P.capFamily F t).hright⟩).symm
         _ ≤ a.R (min (32*a.data.s) 1):=a.shiftedNativeModel.R_monotone hupper
  refine ⟨⟨hleft.trans hr.1,hr.2.trans_le H⟩,Or.inl ?_⟩
  exact ⟨⟨t,hleft,hupper⟩,hr⟩

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
