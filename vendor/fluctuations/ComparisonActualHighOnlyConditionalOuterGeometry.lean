module

public import ComparisonActualHighOnlyConditionalOrdinaryPrice
public import ComparisonActualHighOnlyLocalDiameterBudgetDefinitions
public import ComparisonLocalCapPhysicalSize

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 3000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem conditional_outer_radius_geometry_high_only
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) (hs : a.data.s < v/2)
    (houter : 4*cu*Az*a.xs ≤ v) :
    v/(2*cu) ≤ a.R (v/2) ∧ a.z ≤ a.R (v/2) ∧
      a.R (min (16*v) 1) ≤ 16*v/cl ∧
      a.R (min (16*v) 1) ≤ (32*cu/cl)*a.R (v/2) := by
  have Hsmall : a.alpha.val.val a.z ≤ v/2 := by
    have Hreg := (a.regular a.z ⟨le_rfl,a.hz.2⟩).2
    have Hz := mul_le_mul_of_nonneg_left a.hzxs hcu.le
    nlinarith only [Hreg,Hz,houter,hv]
  have Hmono := a.shiftedNativeModel.R_monotone Hsmall
  rw [a.shiftedNativeModel.R_inverse a.hz] at Hmono
  change a.z ≤ a.R (v/2) at Hmono
  have hleft : v/2∈Icc a.data.s 1 := ⟨hs.le,by linarith⟩
  have HleftSpec := a.shiftedNativeModel.R_spec hleft
  change a.alpha.val.val (a.R (v/2))=v/2 at HleftSpec
  have HleftReg := a.regular _ ⟨Hmono,(a.shiftedNativeModel.R_bounds _).2⟩
  rw [HleftSpec] at HleftReg
  have Hlower : v/(2*cu) ≤ a.R (v/2) := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hcu)).mpr
    nlinarith only [HleftReg.2]
  have Hmin : v/2 ≤ min (16*v) 1 := le_min (by linarith) (by linarith)
  have HrightMono := a.shiftedNativeModel.R_monotone Hmin
  change a.R (v/2) ≤ a.R (min (16*v) 1) at HrightMono
  have HrightSpec := a.shiftedNativeModel.R_spec
    (show min (16*v) 1∈Icc a.data.s 1 from ⟨hs.le.trans Hmin,min_le_right _ _⟩)
  change a.alpha.val.val (a.R (min (16*v) 1))=min (16*v) 1 at HrightSpec
  have HrightReg := (a.regular _ ⟨Hmono.trans HrightMono,(a.shiftedNativeModel.R_bounds _).2⟩).1
  rw [HrightSpec] at HrightReg
  have Hupper : a.R (min (16*v) 1) ≤ 16*v/cl := by
    apply (le_div_iff₀ hcl).mpr
    nlinarith only [HrightReg,min_le_left (16*v) 1]
  have Hratio : a.R (min (16*v) 1) ≤ (32*cu/cl)*a.R (v/2) := by
    have Hcl : cl*a.R (min (16*v) 1) ≤ 32*cu*a.R (v/2) := by
      nlinarith only [HrightReg,min_le_left (16*v) 1,HleftReg.2]
    have Hdiv : a.R (min (16*v) 1) ≤ (32*cu*a.R (v/2))/cl := by
      apply (le_div_iff₀ hcl).mpr
      simpa only [mul_comm] using Hcl
    exact Hdiv.trans_eq (by ring)
  exact ⟨Hlower,Hmono,Hupper,Hratio⟩

theorem conditional_outer_strength_geometry_high_only
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) (hs : a.data.s < v/2)
    (houter : 4*cu*Az*a.xs ≤ v) :
    a.data.N*laplaceComparisonStrength a.data.d a.lam (a.R (v/2)) ≤
      (32*cu/cl)*a.canonicalMassPower v := by
  have Hgeom := a.conditional_outer_radius_geometry_high_only hcl hcu hAz hv hv1 hs houter
  have hRleft : 0 < a.R (v/2) := (div_pos hv (mul_pos (by norm_num) hcu)).trans_le Hgeom.1
  have Hmin : v/2 ≤ min (16*v) 1 := le_min (by linarith) (by linarith)
  have Hmono := a.shiftedNativeModel.R_monotone Hmin
  change a.R (v/2) ≤ a.R (min (16*v) 1) at Hmono
  have Hprod := (laplaceComparisonStrength_monotonicities a.data.hd.ne' a.hlam (r₀:=0) le_rfl).2
    (a.shiftedNativeModel.R_bounds _) (a.shiftedNativeModel.R_bounds _) Hmono
  change laplaceComparisonStrength a.data.d a.lam (a.R (v/2))*a.R (v/2) ≤
    laplaceComparisonStrength a.data.d a.lam (a.R (min (16*v) 1))*a.R (min (16*v) 1) at Hprod
  have hg : 0 ≤ laplaceComparisonStrength a.data.d a.lam (a.R (min (16*v) 1)) :=
    (laplaceComparisonStrength_pos a.data.d a.hlam _).le
  have Hratio := mul_le_mul_of_nonneg_right Hgeom.2.2.2 hg
  have Hg : laplaceComparisonStrength a.data.d a.lam (a.R (v/2)) ≤
      (32*cu/cl)*laplaceComparisonStrength a.data.d a.lam (a.R (min (16*v) 1)) := by
    apply le_of_mul_le_mul_right (a:=a.R (v/2)) _ hRleft
    nlinarith only [Hprod,Hratio]
  have H := mul_le_mul_of_nonneg_left Hg a.data.hN.le
  simpa only [canonicalMassPower,mul_assoc,mul_left_comm] using H

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
