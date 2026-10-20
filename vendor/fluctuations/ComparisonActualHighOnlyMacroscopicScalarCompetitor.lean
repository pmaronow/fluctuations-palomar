module

public import ComparisonActualHighOnlyOverlapMinimum
public import ActualComparisonScalarUpper
public import ScalarProfileL1Stability

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 8000000

def macroInitialMassProfile {eta Q : ℝ} (alpha : MacroInverseClass eta Q)
    {s : ℝ} (hs : s∈Icc (0:ℝ) 1) : boundedMassProfiles :=
  ⟨fun r=>if r<0 then 0 else s+(1-s)*alpha.val.val r,by
    constructor
    · intro r
      dsimp only
      split_ifs with hr
      · exact ⟨le_rfl,zero_le_one⟩
      · have ha:=alpha.val.property.1 r
        exact ⟨add_nonneg hs.1 (mul_nonneg (sub_nonneg.mpr hs.2) ha.1),by
          have H:=mul_le_mul_of_nonneg_left ha.2 (sub_nonneg.mpr hs.2)
          linarith⟩
    · intro r t hrt
      by_cases hr : r < 0
      · by_cases ht : t < 0
        · simp only [ite_eq_left hr,ite_eq_left ht]
          exact le_rfl
        · simp only [ite_eq_left hr,ite_eq_right ht]
          exact add_nonneg hs.1
            (mul_nonneg (sub_nonneg.mpr hs.2) (alpha.val.property.1 t).1)
      · by_cases ht : t < 0
        · exact False.elim (hr (hrt.trans_lt ht))
        · simp only [ite_eq_right hr,ite_eq_right ht]
          exact add_le_add le_rfl
            (mul_le_mul_of_nonneg_left (alpha.val.property.2 hrt) (sub_nonneg.mpr hs.2))⟩

theorem macroInitialMassProfile_on {eta Q s : ℝ} (alpha : MacroInverseClass eta Q)
    (hs : s∈Icc (0:ℝ) 1) {r : ℝ} (hr : 0≤r) :
    (macroInitialMassProfile alpha hs).val r=s+(1-s)*alpha.val.val r := by
  simp only [macroInitialMassProfile,ite_eq_right (not_lt.mpr hr)]

theorem macroInitialMassProfile_zero {eta Q s : ℝ} (alpha : MacroInverseClass eta Q)
    (hs : s∈Icc (0:ℝ) 1) : (macroInitialMassProfile alpha hs).val 0=s := by
  rw [macroInitialMassProfile_on alpha hs le_rfl,alpha.property.1]
  ring

theorem macroInitialMassProfile_one {eta Q s : ℝ} (alpha : MacroInverseClass eta Q)
    (hs : s∈Icc (0:ℝ) 1) : (macroInitialMassProfile alpha hs).val 1=1 := by
  rw [macroInitialMassProfile_on alpha hs zero_le_one,alpha.property.2.1]
  ring

theorem macroInitialMassProfile_pointwise_error {eta Q s : ℝ}
    (alpha : MacroInverseClass eta Q) (hs : s∈Icc (0:ℝ) 1) (r : ℝ) :
    |(macroInitialMassProfile alpha hs).val r-alpha.val.val r| ≤ s := by
  by_cases hr : r < 0
  · have hz:alpha.val.val r=0 := by
      have H:=alpha.val.property.2 hr.le
      rw [alpha.property.1] at H
      exact le_antisymm H (alpha.val.property.1 r).1
    simp only [macroInitialMassProfile,ite_eq_left hr,hz,sub_self,abs_zero]
    exact hs.1
  · rw [macroInitialMassProfile_on alpha hs (not_lt.mp hr)]
    have H:=alpha.val.property.1 r
    apply abs_le.mpr
    constructor <;> nlinarith [mul_nonneg hs.1 H.1,mul_le_mul_of_nonneg_left H.2 hs.1]

theorem macroInitialMassProfile_scalar_error {eta Q s T : ℝ} (hT : 0<T)
    (alpha : MacroInverseClass eta Q) (hs : s∈Icc (0:ℝ) 1) :
    |scalarParisiValue hT (macroInitialMassProfile alpha hs)-scalarParisiValue hT alpha.val| ≤ T*s := by
  have H:=scalarParisiValue_L1_comparison hT (macroInitialMassProfile alpha hs) alpha.val
  have Hi:=intervalIntegral_abs_le_unit_bound
    (f:=fun r=>|(macroInitialMassProfile alpha hs).val r-alpha.val.val r|) (C:=s)
    (fun r _=>by simpa only [abs_abs] using macroInitialMassProfile_pointwise_error alpha hs r)
  exact H.trans (mul_le_mul_of_nonneg_left ((le_abs_self _).trans Hi) hT.le)

def macroInitialMassInVariableClass {eta Q s : ℝ} (alpha : MacroInverseClass eta Q)
    (hs : s∈Icc (0:ℝ) (1/2)) (heta : 0<eta)
    (k M : ℝ→ℝ) (hk : ContinuousOn k (Icc (0:ℝ) 1))
    (hm : MonotoneOn M (Icc (0:ℝ) 1))
    (hfloor : ∀r∈Icc (0:ℝ) 1,k r≤eta/2)
    (hcap : ∀u∈Icc (0:ℝ) 1,Q≤M u) : inverseIntegralConstraints 0 s k M := by
  let hs1:s∈Icc (0:ℝ) 1:=⟨hs.1,hs.2.trans (by norm_num)⟩
  refine ⟨macroInitialMassProfile alpha hs1,
    macroInitialMassProfile_zero alpha hs1,macroInitialMassProfile_one alpha hs1,?_⟩
  intro x hx y hy hxy
  have hsub:Icc x y⊆Icc (0:ℝ) 1:=Icc_subset_Icc hx.1 hy.2
  have hgap:=alpha.property.2.2 x hx y hy hxy
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hgap
  have hi : IntervalIntegrable (fun r=>M ((macroInitialMassProfile alpha hs1).val r)) volume x y := by
    exact (show Monotone (fun r=>M ((macroInitialMassProfile alpha hs1).val r)) from
      fun r t hrt=>hm ((macroInitialMassProfile alpha hs1).property.1 r)
        ((macroInitialMassProfile alpha hs1).property.1 t)
        ((macroInitialMassProfile alpha hs1).property.2 hrt)).intervalIntegrable
  have HL:=intervalIntegral.integral_mono_on (μ:=volume) hxy
    ((hk.mono hsub).intervalIntegrable_of_Icc hxy) (intervalIntegrable_const (c:=eta/2))
    (fun r hr=>hfloor r (hsub hr))
  have HU:=intervalIntegral.integral_mono_on hxy (intervalIntegrable_const (c:=Q)) hi
    (fun r _=>hcap ((macroInitialMassProfile alpha hs1).val r)
      ((macroInitialMassProfile alpha hs1).property.1 r))
  rw [macroInitialMassProfile_on alpha hs1 hy.1,macroInitialMassProfile_on alpha hs1 hx.1]
  simp only [intervalIntegral.integral_const,smul_eq_mul] at HL HU
  have hg0:0≤alpha.val.val y-alpha.val.val x:=sub_nonneg.mpr (alpha.val.property.2 hxy)
  have HLgap:=mul_le_mul_of_nonneg_left hgap.1 (sub_nonneg.mpr hs1.2)
  constructor
  · apply HL.trans
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (mul_nonneg heta.le (by linarith [hs.2] : 0≤1/2-s))]
  · apply le_trans _ HU
    have HS:=mul_le_mul_of_nonneg_right (show 1-s≤1 by linarith [hs.1]) hg0
    nlinarith [hgap.2]

namespace ActualHighOnlyComparisonData

def macroScalarTrial {n : ℕ} {delta eta Q : ℝ}
    (a : ActualHighOnlyComparisonData n delta) (alpha : MacroInverseClass eta Q) (heta : 0<eta)
    (hfloor : ∀r∈Icc (0:ℝ) 1,a.k r≤eta/2)
    (hcap : ∀u∈Icc (0:ℝ) 1,Q≤a.M u) : a.Profile :=
  macroInitialMassInVariableClass alpha a.hs heta a.k a.M a.hk a.hm hfloor hcap

end ActualHighOnlyComparisonData
end OAI.SKFluctuations.LaplaceWindowFormalization
