module

public import ComparisonPhysicalCapScale
public import ComparisonActualHighWallThetaZeroSelectedScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 12000000

theorem eventually_original_q_constraint_length_lower_draft
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 ≤ m) (hC0 : 0 < C0) :
    ∀ᶠ n : ℕ in atTop,
      ∀ Q : ActualThetaZeroOverlapMinimum
          (n+1) m delta cl cu Az C0 Ct D Bclock,
        Q.data.N^(-(1:ℝ)) ≤
          comparisonConstraintLength Q.data.N Q.data.E Q.data.d := by
  have hgamma : 0 < 1/C0 := one_div_pos.mpr hC0
  have Hreal := comparison_physical_cap_length_eventually
    (m:=m) (gamma:=1/C0) hm hgamma
  have HN : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  filter_upwards [HN.eventually Hreal] with n hn
  intro Q
  have hN : 1 ≤ Q.data.N := by
    dsimp only [ActualHighWallData.N]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hlower : (1/C0)*Q.data.N^(-(2:ℝ)/3+m)*Q.data.d ≤
      Q.data.E := by
    have H := mul_le_mul_of_nonneg_left Q.hlower
      (by positivity : 0 ≤ 1/C0)
    have Heq : (1/C0)*(C0*Q.data.E)=Q.data.E := by
      field_simp [hC0.ne']
    rw [Heq] at H
    simpa only [mul_assoc] using H
  have hupper : Q.data.E ≤ Q.data.d^2/Real.sqrt Q.data.N := by
    have hroot : 0 < Real.sqrt Q.data.N :=
      Real.sqrt_pos.mpr Q.data.hN
    apply (le_div_iff₀ hroot).mpr
    calc
      _ = Real.sqrt Q.data.N*Q.data.E := mul_comm _ _
      _ ≤ Q.data.d^2 := Q.hupper
  have Hcap := hn Q.data.d Q.data.E Q.data.hd Q.data.hd1
    Q.data.hE (by simpa only [ActualHighWallData.N] using hlower)
    (by simpa only [ActualHighWallData.N] using hupper)
  simpa only [ActualHighWallData.N,comparisonConditionalCapLength,
    comparisonConstraintLength,comparisonLowerScale] using Hcap

end OAI.SKFluctuations.LaplaceWindowFormalization
