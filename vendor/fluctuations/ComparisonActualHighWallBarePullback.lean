module

public import ComparisonActualHighWallInnovation
public import ComparisonNativeClockRegularity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000

theorem wallPsi_lipschitzOn
    {s tau : ℝ} (hs : 0 < s) (htau : 0 < tau) :
    LipschitzOnWith (Real.toNNReal (1/(tau*Real.log ((s+tau)/tau))))
      (wallPsi s tau) (Icc 0 s) := by
  have hlog:=wallPsi_log_pos hs htau
  apply (convex_Icc (0:ℝ) s).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun u hu=>(wallPsi_hasDerivAt hs htau hu.2).hasDerivWithinAt)
  intro u hu
  have hden : 0 < s-u+tau:=by linarith [hu.2]
  apply NNReal.coe_le_coe.mp
  change |1/((s-u+tau)*Real.log ((s+tau)/tau))| ≤
    (Real.toNNReal (1/(tau*Real.log ((s+tau)/tau))):ℝ)
  rw [Real.coe_toNNReal _ (by positivity),abs_of_nonneg (by positivity)]
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul_of_nonneg_right (by linarith [hu.2]) hlog.le

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem pullback_clock_regularity_of_mass_cut
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (b h : ℝ→ℝ) {s : ℝ} (hs : s∈Icc (0:ℝ) 1)
    (Hbranch : ∀l r,0 ≤ l → l ≤ r → r ≤ 1 → (r < s ∨ s ≤ l) →
      ∃Kb Kh : ℝ≥0,LipschitzOnWith Kb b (Icc l r) ∧ LipschitzOnWith Kh h (Icc l r)) :
    NativePullbackClockRegularity M.alpha.val.val b h 0 1 := by
  let cut:=M.R s
  have Hcut : cut∈Icc (0:ℝ) 1:=comparisonSweepQuantile_bounds M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.alpha s
  have Hspec : M.alpha.val.val cut=s:=comparisonSweepQuantile_spec M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.alpha hs
  have Halpha:=inverseIntegralConstraints_lipschitz M.context.hm M.context.hM M.alpha.property
  refine Or.inr ⟨cut,?_⟩
  intro l r hl hlr hr hside
  have Hl : l∈Icc (0:ℝ) 1:=⟨hl,hlr.trans hr⟩
  have Hr : r∈Icc (0:ℝ) 1:=⟨hl.trans hlr,hr⟩
  have Hside : M.alpha.val.val r < s ∨ s ≤ M.alpha.val.val l:=by
    rcases hside with Hleft|Hright
    · have H:=inverseConstraint_strictMonoOn M.context.hc M.context.hk M.context.hkc
        M.alpha.property Hr Hcut Hleft
      exact Or.inl (by simpa only [Hspec] using H)
    · exact Or.inr (by simpa only [Hspec] using M.alpha.val.property.2 Hright)
  obtain ⟨Kb,Kh,Hb,Hh⟩:=Hbranch (M.alpha.val.val l) (M.alpha.val.val r)
    (M.alpha.val.property.1 l).1 (M.alpha.val.property.2 hlr) (M.alpha.val.property.1 r).2 Hside
  have Hmap : MapsTo M.alpha.val.val (Icc l r) (Icc (M.alpha.val.val l) (M.alpha.val.val r)):=by
    intro x hx
    exact ⟨M.alpha.val.property.2 hx.1,M.alpha.val.property.2 hx.2⟩
  have Ha:=Halpha.mono (Icc_subset_Icc hl hr)
  exact ⟨Kb*⟨M.context.M 1,M.context.hM⟩,Kh*⟨M.context.M 1,M.context.hM⟩,
    Hb.comp Ha Hmap,Hh.comp Ha Hmap⟩

end NativeOverlapMinimum

private theorem real_lipschitzOn_const_mul {f : ℝ→ℝ} {S : Set ℝ} {K : ℝ≥0}
    (H : LipschitzOnWith K f S) (c : ℝ) :
    LipschitzOnWith (‖c‖₊*K) (fun x=>c*f x) S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have HH:=H.dist_le_mul x hx y hy
  simp only [Real.dist_eq] at HH ⊢
  rw [←mul_sub,abs_mul]
  simp only [NNReal.coe_mul,coe_nnnorm,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left HH (abs_nonneg c)).trans_eq (by ring)

namespace ActualHighWallData
variable {n : ℕ} {delta : ℝ} (a : ActualHighWallData n delta)

theorem changed_clocks_mass_cut_branches (alpha : a.Profile)
    (l r : ℝ) (hl : 0 ≤ l) (_hlr : l ≤ r) (hr : r ≤ 1)
    (Hside : r < a.s ∨ a.s ≤ l) :
    ∃Kb Kh : ℝ≥0,
      LipschitzOnWith Kb (fun u=>(a.bf alpha u:ℝ)) (Icc l r) ∧
      LipschitzOnWith Kh (fun u=>(a.hf alpha u:ℝ)) (Icc l r) := by
  rcases Hside with Hleft|Hright
  · let c:=a.theta*wallLowStrength a.T a.epsilon*wallLowRadius a.d a.rmin a.epsilon
    have Hpsi:=real_lipschitzOn_const_mul (wallPsi_lipschitzOn a.hs.1 a.htau) c
    have Hlow : Icc l r⊆Icc (0:ℝ) a.s:=Icc_subset_Icc hl Hleft.le
    refine ⟨0,‖c‖₊*Real.toNNReal (1/(a.tau*Real.log ((a.s+a.tau)/a.tau))),?_,?_⟩
    · apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      have Hx : x∈Icc (0:ℝ) 1:=⟨hl.trans hx.1,hx.2.trans hr⟩
      have Hy : y∈Icc (0:ℝ) 1:=⟨hl.trans hy.1,hy.2.trans hr⟩
      rw [(a.clock_coe alpha Hx).1,(a.clock_coe alpha Hy).1]
      dsimp only [b]
      rw [wallChangedMatrix_below a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
        a.T a.epsilon a.theta alpha (hx.2.trans_lt Hleft),
        wallChangedMatrix_below a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
        a.T a.epsilon a.theta alpha (hy.2.trans_lt Hleft)]
      simp
    · apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      have Hx : x∈Icc (0:ℝ) 1:=⟨hl.trans hx.1,hx.2.trans hr⟩
      have Hy : y∈Icc (0:ℝ) 1:=⟨hl.trans hy.1,hy.2.trans hr⟩
      rw [(a.clock_coe alpha Hx).2,(a.clock_coe alpha Hy).2]
      dsimp only [h]
      rw [wallChangedField_below a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
        a.T a.epsilon a.theta a.tau a.d alpha (hx.2.trans_lt Hleft),
        wallChangedField_below a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
        a.T a.epsilon a.theta a.tau a.d alpha (hy.2.trans_lt Hleft)]
      exact Hpsi.dist_le_mul x (Hlow hx) y (Hlow hy)
  · obtain ⟨Kb,Hb⟩:=a.hg.contDiffOn.exists_lipschitzOnWith (by norm_num)
      (convex_Icc a.rmin 1) isCompact_Icc
    obtain ⟨Kh,Hh⟩:=(a.hg.mul contDiff_id).contDiffOn.exists_lipschitzOnWith (by norm_num)
      (convex_Icc a.rmin 1) isCompact_Icc
    let Kr : ℝ≥0:=⟨1/(a.k 1),div_nonneg zero_le_one a.hc.le⟩
    have HR : LipschitzOnWith Kr (a.wallRadius alpha) (Icc l r):=
      (a.wallRadius_lipschitz alpha).lipschitzOnWith
    have Hmap : MapsTo (a.wallRadius alpha) (Icc l r) (Icc a.rmin 1):=
      fun u _=>a.wallRadius_bounds alpha u
    have HB:=Hb.comp HR Hmap
    have HH:=Hh.comp HR Hmap
    refine ⟨Kb*Kr,Kh*Kr,?_,?_⟩
    · apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      have Hx : x∈Icc a.s 1:=⟨Hright.trans hx.1,hx.2.trans hr⟩
      have Hy : y∈Icc a.s 1:=⟨Hright.trans hy.1,hy.2.trans hr⟩
      have Hbx : (a.bf alpha x:ℝ)=a.T-a.g (a.wallRadius alpha x):=by
        rw [(a.clock_coe alpha ⟨a.hs.1.le.trans Hx.1,Hx.2⟩).1]
        dsimp only [b]
        rw [wallChangedMatrix_on a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
          a.T a.epsilon a.theta alpha Hx]
        unfold wallRadius comparisonCalibrationConstrainedRadius
        rw [IccExtend_of_mem _ _ Hx]
        rfl
      have Hby : (a.bf alpha y:ℝ)=a.T-a.g (a.wallRadius alpha y):=by
        rw [(a.clock_coe alpha ⟨a.hs.1.le.trans Hy.1,Hy.2⟩).1]
        dsimp only [b]
        rw [wallChangedMatrix_on a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
          a.T a.epsilon a.theta alpha Hy]
        unfold wallRadius comparisonCalibrationConstrainedRadius
        rw [IccExtend_of_mem _ _ Hy]
        rfl
      rw [Hbx,Hby]
      simpa only [Function.comp_def,Real.dist_eq,show a.T-a.g (a.wallRadius alpha x)-
        (a.T-a.g (a.wallRadius alpha y))=-(a.g (a.wallRadius alpha x)-a.g (a.wallRadius alpha y)) by ring,
        abs_neg] using HB.dist_le_mul x hx y hy
    · apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      rw [a.high_field_clock alpha ⟨Hright.trans hx.1,hx.2.trans hr⟩,
        a.high_field_clock alpha ⟨Hright.trans hy.1,hy.2.trans hr⟩]
      exact HH.dist_le_mul x hx y hy

theorem changed_pullback_clock_regularity (alpha : a.Profile)
    {N : ℕ} {m deltac cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum N m deltac cl cu Az C0 Ct D Bclock) :
    NativePullbackClockRegularity M.alpha.val.val
      (fun u=>(a.bf alpha u:ℝ)) (fun u=>(a.hf alpha u:ℝ)) 0 1 :=
  M.pullback_clock_regularity_of_mass_cut _ _ ⟨a.hs.1.le,a.hs1⟩
    (a.changed_clocks_mass_cut_branches alpha)

end ActualHighWallData
end OAI.SKFluctuations.LaplaceWindowFormalization
