module

public import ComparisonNativeActualGeneralBareHistory
public import ComparisonNativeClockRegularity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000

private theorem real_lipschitzOn_add {f g : ℝ→ℝ} {s : Set ℝ} {Kf Kg : ℝ≥0}
    (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s) :
    LipschitzOnWith (Kf+Kg) (fun x=>f x+g x) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have Hf:=hf.dist_le_mul x hx y hy
  have Hg:=hg.dist_le_mul x hx y hy
  simp only [Real.dist_eq] at Hf Hg ⊢
  rw [show f x+g x-(f y+g y)=(f x-f y)+(g x-g y) by ring]
  exact (abs_add_le _ _).trans (by change _≤((Kf:ℝ)+(Kg:ℝ))*|x-y|;nlinarith)

private theorem real_lipschitzOn_sub {f g : ℝ→ℝ} {s : Set ℝ} {Kf Kg : ℝ≥0}
    (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s) :
    LipschitzOnWith (Kf+Kg) (fun x=>f x-g x) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have Hf:=hf.dist_le_mul x hx y hy
  have Hg:=hg.dist_le_mul x hx y hy
  simp only [Real.dist_eq] at Hf Hg ⊢
  rw [show f x-g x-(f y-g y)=(f x-f y)-(g x-g y) by ring]
  exact (abs_sub _ _).trans (by change _≤((Kf:ℝ)+(Kg:ℝ))*|x-y|;nlinarith)

theorem NativePullbackClockRegularity.perturb_by_lipschitz
    {alpha b h f g : ℝ→ℝ} {a z : ℝ} {Ka Kf Kg : ℝ≥0}
    (H : NativePullbackClockRegularity alpha b h a z)
    (Halpha : LipschitzOnWith Ka alpha (Icc a z))
    (Hf : LipschitzWith Kf f) (Hg : LipschitzWith Kg g) :
    NativePullbackClockRegularity alpha (fun u=>b u-f u) (fun u=>h u+g u) a z := by
  have HF:=Hf.comp_lipschitzOnWith Halpha
  have HG:=Hg.comp_lipschitzOnWith Halpha
  rcases H with ⟨Kb,Kh,Hb,Hh⟩|⟨s,Hs⟩
  · exact Or.inl ⟨Kb+Kf*Ka,Kh+Kg*Ka,real_lipschitzOn_sub Hb HF,real_lipschitzOn_add Hh HG⟩
  · refine Or.inr ⟨s,?_⟩
    intro l r hal hlr hrz hside
    obtain ⟨Kb,Kh,Hb,Hh⟩:=Hs l r hal hlr hrz hside
    exact ⟨Kb+Kf*Ka,Kh+Kg*Ka,
      real_lipschitzOn_sub Hb (HF.mono (Icc_subset_Icc hal hrz)),
      real_lipschitzOn_add Hh (HG.mono (Icc_subset_Icc hal hrz))⟩

theorem NativePullbackClockRegularity.perturb_by_history
    {alpha b h : ℝ→ℝ} {a z : ℝ} {Ka : ℝ≥0}
    (H : NativePullbackClockRegularity alpha b h a z)
    (Halpha : LipschitzOnWith Ka alpha (Icc a z)) (ts : List ComparisonHistoryTerm) :
    NativePullbackClockRegularity alpha (fun u=>b u-historyMatrixReduction ts u)
      (fun u=>h u+historyFieldAddition ts u) a z := by
  obtain ⟨Kf,Hf⟩:=historyMatrixReduction_lipschitz ts
  obtain ⟨Kg,Hg⟩:=historyFieldAddition_lipschitz ts
  exact H.perturb_by_lipschitz Halpha Hf Hg

namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 : ℝ} {dim : ℕ→ℕ}

theorem ActualWeakSelectedHistoryChain.pullback_general_bare
    {root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (H : ActualWeakSelectedHistoryChain c0 root M)
    (Hbare : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val
      (root n).b (root n).h 0 1) :
    ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1 := by
  obtain ⟨ps,Hps⟩:=H.literal_readout_general_bare
  filter_upwards [Hbare,Hps] with n hn hnps
  have Halpha:=inverseIntegralConstraints_lipschitz (M n).context.hm (M n).context.hM (M n).alpha.property
  have Hp:=hn.perturb_by_history Halpha ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm))
  have Hb : (M n).b=(fun u=>(root n).b u-
    historyMatrixReduction ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm)) u):=
    funext hnps.2.1
  have Hh : (M n).h=(fun u=>(root n).h u+
    historyFieldAddition ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm)) u):=
    funext hnps.2.2
  rw [Hb,Hh]
  exact Hp

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
