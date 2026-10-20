module

public import ComparisonActualHighOnlyContactGeometry
public import VariableEndpointPhysicalRegularity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem radiusS_lipschitz
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    {a z : ℝ} (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1)
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>M.b (M.alpha.val.val r)) (Icc a z))
    (hfield : LipschitzOnWith Kh (fun r=>M.h (M.alpha.val.val r)) (Icc a z)) :
    ∃K,LipschitzOnWith K M.radiusS (Icc a z) := by
  let α:=M.alpha
  let d:=M.data.d
  let lam:=M.lam
  let b:=M.b
  let h:=M.h
  let R := M.R
  let g := laplaceComparisonStrength d lam
  let bf:=M.bf
  let hf:=M.hf
  have hbf:=M.bf_monotone
  have hhf:=M.hf_monotone
  have hsub : Icc a z⊆Icc (0:ℝ) 1 := Icc_subset_Icc ha.le hz
  have hα : MapsTo α.val.val (Icc a z) (Ioc (0:ℝ) 1) := by
    intro r hr
    have hh := inverseConstraint_strictMonoOn M.data.hc M.data.hk M.data.hkc α.property
      (by norm_num : (0:ℝ)∈Icc 0 1) (hsub hr) (ha.trans_le hr.1)
    rw [α.property.1] at hh
    exact ⟨M.data.hs.1.trans_lt hh,(α.val.property.1 r).2⟩
  obtain ⟨Kg,hg⟩ := (laplaceComparisonStrength_contDiff d lam).contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_Icc (0:ℝ) 1) isCompact_Icc
  obtain ⟨Kf,hfLip⟩ := ((laplaceComparisonStrength_contDiff d lam).mul contDiff_id).contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_Icc (0:ℝ) 1) isCompact_Icc
  let K := Kb+Kh+Kg+Kf
  have hclock (j : FeatureIndex (n+1)) : LipschitzOnWith K
      (fun r=>(completedPathClock (n+1) bf hf (α.val.val r) j:ℝ)) (Icc a z) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hRx := omittedSweepQuantile_inverse zero_le_one ⟨M.data.hs.1,M.data.hs1⟩ M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM α (hsub hx)
    have hRy := omittedSweepQuantile_inverse zero_le_one ⟨M.data.hs.1,M.data.hs1⟩ M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM α (hsub hy)
    have hbnd := hparent.dist_le_mul x hx y hy
    have hhbnd := hfield.dist_le_mul x hx y hy
    have hgbnd := hg.dist_le_mul x (hsub hx) y (hsub hy)
    have hfbnd := hfLip.dist_le_mul x (hsub hx) y (hsub hy)
    change dist (g x*x) (g y*y) ≤ (Kf:ℝ)*dist x y at hfbnd
    cases j with
    | inl j=>
      change dist (hf (α.val.val x):ℝ) (hf (α.val.val y):ℝ) ≤ (K:ℝ)*dist x y
      have HMx:=M.high_clock_coe (inverseConstraint_mass_mem zero_le_one M.data.hc M.data.hk M.data.hkc α (hsub hx))
      have HMy:=M.high_clock_coe (inverseConstraint_mass_mem zero_le_one M.data.hc M.data.hk M.data.hkc α (hsub hy))
      rw [HMx.2,HMy.2]
      change dist (h (α.val.val x)+g (R (α.val.val x))*R (α.val.val x)) (h (α.val.val y)+g (R (α.val.val y))*R (α.val.val y)) ≤ _
      rw [show R (α.val.val x)=x from hRx,show R (α.val.val y)=y from hRy]
      have hdsum : dist (h (α.val.val x)+g x*x) (h (α.val.val y)+g y*y) ≤
          dist (h (α.val.val x)) (h (α.val.val y))+dist (g x*x) (g y*y) := by
        simp only [Real.dist_eq]
        have he : h (α.val.val x)+g x*x-(h (α.val.val y)+g y*y)=
            (h (α.val.val x)-h (α.val.val y))+(g x*x-g y*y) := by ring
        rw [he]
        exact abs_add_le _ _
      dsimp only [K] at ⊢
      simp only [NNReal.coe_add] at ⊢
      nlinarith [hdsum,Kb.coe_nonneg,Kg.coe_nonneg,dist_nonneg (x:=x) (y:=y)]
    | inr j=>
      change dist (bf (α.val.val x):ℝ) (bf (α.val.val y):ℝ) ≤ (K:ℝ)*dist x y
      have HMx:=M.high_clock_coe (inverseConstraint_mass_mem zero_le_one M.data.hc M.data.hk M.data.hkc α (hsub hx))
      have HMy:=M.high_clock_coe (inverseConstraint_mass_mem zero_le_one M.data.hc M.data.hk M.data.hkc α (hsub hy))
      rw [HMx.1,HMy.1]
      change dist (b (α.val.val x)-g (R (α.val.val x))) (b (α.val.val y)-g (R (α.val.val y))) ≤ _
      rw [show R (α.val.val x)=x from hRx,show R (α.val.val y)=y from hRy]
      have hdsub : dist (b (α.val.val x)-g x) (b (α.val.val y)-g y) ≤
          dist (b (α.val.val x)) (b (α.val.val y))+dist (g x) (g y) := by
        simp only [Real.dist_eq]
        have he : b (α.val.val x)-g x-(b (α.val.val y)-g y)=
            (b (α.val.val x)-b (α.val.val y)) + -(g x-g y) := by ring
        rw [he]
        simpa only [abs_neg] using abs_add_le (b (α.val.val x)-b (α.val.val y)) (-(g x-g y))
      dsimp only [K] at ⊢
      simp only [NNReal.coe_add] at ⊢
      nlinarith [hdsub,Kf.coe_nonneg,Kh.coe_nonneg,dist_nonneg (x:=x) (y:=y)]
  exact ⟨_,physicalOrderedPathS_comp_lipschitzOn n dphys e bf hf hbf hhf α.val.val _ K hα hclock⟩

theorem radiusS_absolutelyContinuous
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    {a z : ℝ} (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1)
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>M.b (M.alpha.val.val r)) (Icc a z))
    (hfield : LipschitzOnWith Kh (fun r=>M.h (M.alpha.val.val r)) (Icc a z)) :
    AbsolutelyContinuousOnInterval M.radiusS a z := by
  obtain ⟨K,HK⟩:=M.radiusS_lipschitz dphys e ha haz hz Kb Kh hparent hfield
  rw [←uIcc_of_le haz] at HK
  exact HK.absolutelyContinuousOnInterval

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
