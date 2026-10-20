module

public import ComparisonActualHighWallScalarLimitData
public import ComparisonActualHighWallCriticalUnconditionalCenteringCaps

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 11000000

namespace ActualHighWallOverlapMinimum

theorem actual_high_wall_critical_radius_cdf_caps_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0)) :
    ∀R : ℝ,0<R→∃A : ℝ,∀ᶠn in atTop,
      ((M n).actualRadiusMassProfile.val ((M n).xs*R))/(M n).xs≤A := by
  intro R hR
  let A:=cu*(R+Az)+1
  have hA : 0≤A := by dsimp only [A]; positivity
  have Hunit := (hxlim.const_mul R).eventually
    (eventually_le_nhds (show R*(0:ℝ)<1 by simp))
  refine ⟨A,?_⟩
  filter_upwards [Hunit] with n hnUnit
  let r:=(M n).xs*R
  have hr0 : 0≤r := mul_nonneg (M n).hxs.le hR.le
  have hr1 : r≤1 := by simpa only [mul_comm,r] using hnUnit
  have Halpha : (M n).alpha.val.val r≤cu*(R+Az)*(M n).xs := by
    by_cases hbelow : r<(M n).z
    · have Hmono := (M n).alpha.val.property.2 hbelow.le
      have Hreg := ((M n).regular (M n).z ⟨le_rfl,(M n).hz.2⟩).2
      have Hz := mul_le_mul_of_nonneg_left (M n).hzxs hcu.le
      have Hextra : 0≤cu*R*(M n).xs :=
        mul_nonneg (mul_nonneg hcu.le hR.le) (M n).hxs.le
      nlinarith only [Hmono,Hreg,Hz,Hextra]
    · have Hreg := ((M n).regular r ⟨le_of_not_gt hbelow,hr1⟩).2
      have Hextra : 0≤cu*Az*(M n).xs :=
        mul_nonneg (mul_nonneg hcu.le hAz) (M n).hxs.le
      dsimp only [r] at Hreg ⊢
      nlinarith only [Hreg,Hextra]
  let Q:=ActualHighWallOverlapMinimum.actualInverseSequence M
  have Hdiff : |(M n).actualRadiusMassProfile.val r-(M n).alpha.val.val r|≤(M n).data.s :=
    Q.radius_cdf_error_le_omitted_mass (fun i=>(M i).data.hrbounds.1.le) n r
  have Hmass : (M n).actualRadiusMassProfile.val r≤A*(M n).xs := by
    have H := (abs_le.mp Hdiff).2
    dsimp only [A]
    nlinarith only [H,Halpha,(M n).hsxs]
  exact (div_le_iff₀ (M n).hxs).mpr Hmass

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
