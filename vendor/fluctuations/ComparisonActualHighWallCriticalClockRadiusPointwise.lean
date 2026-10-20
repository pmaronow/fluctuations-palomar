module

public import ComparisonActualHighWallStarClockDistinct
public import ComparisonActualHighWallStarPreparatory

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 5000000

namespace ActualHighWallOverlapMinimum

theorem high_mass_mixed_clock_radius_abs_le_mean_radius_abs
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hsmall : M.data.d^2 ≤ M.data.T)
    {u : ℝ} (hu : u∈Icc M.data.s 1) :
    |actualMixedClock (n+1) M.bf M.hf u/M.data.T-
      M.data.wallRadius M.alpha u| ≤
      |orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u| := by
  let e:=M.data.g (M.data.wallRadius M.alpha u)
  have hTpos : 0<M.data.T := M.data.hepsilon.1.trans M.data.hepsilon.2
  have he0 : 0≤e :=
    (laplaceComparisonStrength_pos M.data.d (sq_pos_of_pos M.data.hd) _).le
  have heT : e≤M.data.T :=
    (laplaceComparisonStrength_le M.data.d (sq_nonneg M.data.d) _).trans hsmall
  have hcoef0 : 0≤1-e/M.data.T :=
    sub_nonneg.mpr ((div_le_one₀ hTpos).mpr heT)
  have hcoef1 : 1-e/M.data.T≤1 :=
    sub_le_self _ (div_nonneg he0 hTpos.le)
  have he : actualMixedClock (n+1) M.bf M.hf u/M.data.T-
      M.data.wallRadius M.alpha u=
      (1-e/M.data.T)*
        (orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u) := by
    have hK:=M.high_mass_clock_compensation hu
    dsimp only [e]
    field_simp [hTpos.ne']
    nlinarith only [hK]
  rw [he,abs_mul,abs_of_nonneg hcoef0]
  exact mul_le_of_le_one_left (abs_nonneg _) hcoef1

theorem low_mass_mixed_clock_radius_abs_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    |actualMixedClock (n+1) M.bf M.hf u/M.data.T-
      M.data.wallRadius M.alpha u| ≤
      |orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u|+
        2*M.data.wallRadius M.alpha u+(M.hf u:ℝ)/M.data.T := by
  let S:=orderedPathS (n+1) M.bf M.hf u
  let R:=M.data.wallRadius M.alpha u
  let q:=actualMixedClock (n+1) M.bf M.hf u/M.data.T
  have hTpos : 0<M.data.T := M.data.hepsilon.1.trans M.data.hepsilon.2
  have hS : 0≤S := M.mass_mean_nonneg hu
  have hR : 0≤R := M.data.hrbounds.1.le.trans (M.data.wallRadius_bounds M.alpha u).1
  have hb : (M.bf u:ℝ)≤M.data.T := by
    have H:=M.data.total_clock_le M.alpha u hu
    linarith [NNReal.coe_nonneg (M.hf u)]
  have hq0 : 0≤q := by
    dsimp only [q,actualMixedClock]
    exact div_nonneg (add_nonneg (NNReal.coe_nonneg _)
      (mul_nonneg (NNReal.coe_nonneg _) hS)) hTpos.le
  have hq : q≤S+(M.hf u:ℝ)/M.data.T := by
    apply (div_le_iff₀ hTpos).mpr
    have H:=mul_le_mul_of_nonneg_right hb hS
    change (M.hf u:ℝ)+(M.bf u:ℝ)*S≤
      (S+(M.hf u:ℝ)/M.data.T)*M.data.T
    calc
      (M.hf u:ℝ)+(M.bf u:ℝ)*S≤(M.hf u:ℝ)+M.data.T*S := by
        simpa only [add_comm] using add_le_add_left H (M.hf u:ℝ)
      _=(S+(M.hf u:ℝ)/M.data.T)*M.data.T := by field_simp [hTpos.ne']; ring
  have hSbound : S≤|S-R|+R := by
    have H:=le_abs_self (S-R)
    linarith only [H]
  have Htri : |q-R|≤q+R := by
    calc
      |q-R|≤|q-0|+|0-R| := abs_sub_le q 0 R
      _=q+R := by simp only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hq0,abs_of_nonneg hR]
  dsimp only [q,R,S] at *
  linarith only [Htri,hq,hSbound]

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
