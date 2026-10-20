module

public import ComparisonActualHighWallDescendantSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 8000000
namespace ActualHighWallData
variable {n : ℕ} {delta : ℝ} (a : ActualHighWallData n delta)

theorem changed_low_matrix_lower_of_small_epsilon (alpha : a.Profile)
    (heps : a.epsilon ≤ a.T/4) {u : ℝ} (hus : u<a.s) :
    5*a.T/8 ≤ a.b alpha u := by
  dsimp only [b]
  rw [wallChangedMatrix_below a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
    a.T a.epsilon a.theta alpha hus]
  have hL:=wallLowStrength_bounds a.hepsilon
  have H:=mul_le_mul_of_nonneg_right a.htheta.2 hL.1
  simp only [one_mul] at H
  linarith

theorem changed_high_matrix_lower (alpha : a.Profile) {u : ℝ} (hu : u∈Icc a.s 1) :
    a.T-a.d^2 ≤ a.b alpha u := by
  dsimp only [b]
  rw [wallChangedMatrix_on a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
    a.T a.epsilon a.theta alpha hu]
  have H:=laplaceComparisonStrength_le a.d (sq_nonneg a.d)
    (constrainedQuantile a.hr a.hc a.hk a.hkc a.hm a.hM alpha ⟨u,hu⟩)
  linarith

theorem changed_global_matrix_lower_of_small_epsilon (alpha : a.Profile)
    (heps : a.epsilon ≤ a.T/4) (hd : a.d^2 ≤ 3*a.T/8) :
    ∀u∈Icc (0:ℝ) 1,5*a.T/8 ≤ a.b alpha u := by
  intro u hu
  by_cases hus : u<a.s
  · exact a.changed_low_matrix_lower_of_small_epsilon alpha heps hus
  · have H:=a.changed_high_matrix_lower alpha ⟨le_of_not_gt hus,hu.2⟩
    linarith

theorem changed_high_gap_fixed (alpha : a.Profile)
    (heps : a.T/4 ≤ a.epsilon) (hd : a.d^2 ≤ a.T/8) :
    ∀u∈Ico (0:ℝ) a.s,a.b alpha u+a.T/8 ≤ a.b alpha a.s := by
  intro u hu
  have hT : 0<a.T:=a.hepsilon.1.trans a.hepsilon.2
  exact a.parent_high_gap alpha (by linarith) hu

theorem changed_fixed_margin_alternative (alpha : a.Profile) (hd : a.d^2 ≤ a.T/8) :
    (∀u∈Icc (0:ℝ) 1,5*a.T/8 ≤ a.b alpha u) ∨
      ((∀u∈Icc a.s 1,7*a.T/8 ≤ a.b alpha u) ∧
        ∀u∈Ico (0:ℝ) a.s,a.b alpha u+a.T/8 ≤ a.b alpha a.s) := by
  have hT : 0<a.T:=a.hepsilon.1.trans a.hepsilon.2
  rcases le_total a.epsilon (a.T/4) with heps|heps
  · exact Or.inl (a.changed_global_matrix_lower_of_small_epsilon alpha heps (by linarith))
  · exact Or.inr ⟨fun u hu=>by linarith [a.changed_high_matrix_lower alpha hu],
      a.changed_high_gap_fixed alpha heps hd⟩

def fixedMarginChildData (alpha : a.Profile) {Echild dchild : ℝ}
    (hEchild : 0<Echild) (hdchild : 0<dchild)
    (hd : a.d^2 ≤ a.T/8) (hdroom : dchild^2 ≤ a.T/8) :
    ActualHighOnlyComparisonData n delta := by
  by_cases heps : a.epsilon < a.T/4
  · exact a.globalChildData alpha hEchild hdchild (by
      have H:=a.changed_global_matrix_lower_of_small_epsilon alpha heps.le (by
        have hT : 0<a.T:=a.hepsilon.1.trans a.hepsilon.2
        linarith) 0 (by norm_num)
      have hT : 0<a.T:=a.hepsilon.1.trans a.hepsilon.2
      linarith)
  · exact a.highOnlyChildData alpha hEchild hdchild (by linarith [le_of_not_gt heps])

theorem fixedMarginChildData_literal (alpha : a.Profile) {Echild dchild : ℝ}
    (hEchild : 0<Echild) (hdchild : 0<dchild)
    (hd : a.d^2 ≤ a.T/8) (hdroom : dchild^2 ≤ a.T/8) :
    let child:=a.fixedMarginChildData alpha hEchild hdchild hd hdroom
    child.E=Echild ∧ child.d=dchild ∧ child.b=a.b alpha ∧ child.h=a.h alpha ∧
      child.s=(if a.epsilon<a.T/4 then 0 else a.s) := by
  dsimp only [fixedMarginChildData]
  split_ifs <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end ActualHighWallData
end OAI.SKFluctuations.LaplaceWindowFormalization
