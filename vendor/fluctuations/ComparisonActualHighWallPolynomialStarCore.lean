module

public import ComparisonActualHighWallStarBandParameters

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem Potential.exists_polynomial_calibrated_star
    (P : M.Potential) {a z c C W eta : ℝ}
    (ha : M.data.s≤ a) (haz : a< z) (hz : z≤1) (hc : 0< c) (hW : 0< W)
    (hdW : M.data.d≤ W) (hclock : W^2≤ M.data.T/2)
    (htravel : M.cavityCapTravel≤ c*W/32)
    (hsize : M.data.N^(-eta)≤ c^2/64)
    (haway : ∀u∈Ioo a z,M.data.rmin+M.cavityCapTravel< M.data.wallRadius M.alpha u)
    (hband : ∀u∈Ioo a z,c*W≤ M.data.wallRadius M.alpha u ∧ M.data.wallRadius M.alpha u≤ C*W)
    (hthermal : (∫u in Ioo a z,orderedPathB (n+1) M.bf M.hf u-
        (orderedPathS (n+1) M.bf M.hf u)^2)<
      (M.data.N^(-eta)*W^2)*((z-a)-M.data.N^(-delta)*comparisonSmallMass M.data.N M.data.E)) :
    ∃u∈Ioo a z,P.H (M.data.wallRadius M.alpha u)≤0 ∧
      orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2≤ M.data.N^(-eta)*W^2 ∧
      |orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u|≤ c*W/4 ∧
      (3*c/4)*W≤ orderedPathS (n+1) M.bf M.hf u ∧
      orderedPathS (n+1) M.bf M.hf u≤(C+c/4)*W ∧
      (3*M.data.T*c/8)*W≤ actualMixedClock (n+1) M.bf M.hf u ∧
      |actualMixedClock (n+1) M.bf M.hf u-M.data.T*orderedPathS (n+1) M.bf M.hf u|≤(c/4)*W^3 := by
  let t:=M.data.N^(-eta)*W^2
  have ht : 0≤ t:=mul_nonneg (Real.rpow_nonneg M.data.hN.le _) (sq_nonneg W)
  obtain ⟨u,hu,hH,hdefect,hmismatch⟩:=P.exists_thermal_good_star_off_floor ha haz hz ht haway hthermal
  have htp : t≤(c*W)^2/64:=by
    have H:=mul_le_mul_of_nonneg_right hsize (sq_nonneg W)
    dsimp only [t]
    nlinarith only [H]
  have htravel2:=pow_le_pow_left₀ M.cavityCapTravel_nonneg htravel 2
  have hsq : (orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u)^2≤(c*W/4)^2:=by
    nlinarith only [hmismatch,htravel2,htp,sq_nonneg (c*W)]
  have habs : |orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u|≤ c*W/4:=by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤ c*W/4)).mp
    simpa only [sq_abs] using hsq
  have hmeanlo : (3*c/4)*W≤ orderedPathS (n+1) M.bf M.hf u:=by
    nlinarith only [(abs_le.mp habs).1,(abs_le.mp habs).2,(hband u hu).1]
  have hmeanhi : orderedPathS (n+1) M.bf M.hf u≤(C+c/4)*W:=by
    nlinarith only [(abs_le.mp habs).1,(abs_le.mp habs).2,(hband u hu).2]
  have HK:=M.selected_high_mass_clock_calibration ⟨ha.trans hu.1.le,hu.2.le.trans hz⟩
    hc hW hdW hclock hmeanlo habs
  exact ⟨u,hu,hH,hdefect,habs,hmeanlo,hmeanhi,HK.1,HK.2⟩

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
