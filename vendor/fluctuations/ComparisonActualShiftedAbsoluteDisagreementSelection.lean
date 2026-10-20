module

public import ComparisonActualShiftedCloseSeparationExclusion
public import SelectivePropagationWorkingTransfer

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 7000000

theorem actual_shifted_absolute_disagreement_selects_close_band
    {n : ℕ} {delta : ℝ} (a : ActualShiftedParentChildCall n delta)
    (J : ℕ) {leftBand rightBand step L q : ℝ}
    (ha : a.context.s ≤ leftBand) (hb : rightBand ≤ 1) (hstep : 0 < step) (hL : 0 < L)
    (hq : 0 ≤ q) (hwidth : 2*q*((J:ℝ)+2)*step ≤ L)
    (hRupper : ∀u∈Icc leftBand rightBand,a.R u ≤ (J:ℝ)*step)
    (hbadmass : 2*(J+1:ℝ≥0∞)*ENNReal.ofReal L <
      volume {u | u∈Icc leftBand rightBand ∧ 3*step ≤ |a.Z u-a.R u|}) :
    ∃y start middle finish : ℝ,
      y∈Ioc (0:ℝ) 1 ∧ 2*step ≤ y ∧ y ≤ ((J:ℝ)+2)*step ∧
      start∈Icc leftBand rightBand ∧ finish∈Icc leftBand rightBand ∧
      a.context.s ≤ start ∧ start < middle ∧ middle ≤ finish ∧ finish ≤ 1 ∧
      q*y ≤ middle-start ∧ q*y ≤ finish-middle ∧
      ((y ≤ a.Z start ∧ ∀u∈Icc middle finish,a.R u ≤ (1-1/((J:ℝ)+2))*y) ∨
       (a.Z finish ≤ (1-1/((J:ℝ)+2))*y ∧
         (∀u∈Icc (0:ℝ) finish,a.R u ≤ ((J:ℝ)+2)*y) ∧
         ∀u∈Icc start middle,y ≤ a.R u)) := by
  have hRm := omittedSweepQuantile_monotone a.context.hr1 a.context.hs a.context.hc a.context.hk a.context.hkc
    a.context.hm a.context.hM a.alpha
  have hRc := omittedSweepQuantile_continuous a.context.hr1 a.context.hs a.context.hc a.context.hk a.context.hkc
    a.context.hm a.context.hM a.alpha
  have ha0 : 0 ≤ leftBand := a.context.hs.1.trans ha
  obtain ⟨j,left,right,hl,hr,hw,hsep⟩:=selective_propagation_absolute_disagreement_selects_working_interval
    J (hRm.monotoneOn _) (a.child_radius_monotone.monotoneOn _) hRc.continuousOn a.child_radius_continuous.continuousOn ha0 hb hstep
    (fun u hu=>⟨(a.radius_bounds u).1,hRupper u hu⟩)
    (fun u hu=>(a.child_radius_bounds u).1) hbadmass
  let y:=(((j:ℕ):ℝ)+2)*step
  let middle:=(left+right)/2
  have hj0 : (0:ℝ) ≤ ((j:ℕ):ℝ) := Nat.cast_nonneg _
  have hJ0 : (0:ℝ) ≤ (J:ℝ) := Nat.cast_nonneg _
  have hj : ((j:ℕ):ℝ) ≤ (J:ℝ) := by exact_mod_cast Nat.le_of_lt_succ j.isLt
  have hy : 0 < y := by dsimp [y];positivity
  have hylo : 2*step ≤ y := by dsimp [y];nlinarith
  have hyhi : y ≤ ((J:ℝ)+2)*step := by dsimp [y];nlinarith
  have hdiv : y/((J:ℝ)+2) ≤ step := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have hgrid : (((j:ℕ):ℝ)+1)*step ≤ (1-1/((J:ℝ)+2))*y := by
    have he : (1-1/((J:ℝ)+2))*y=y-y/((J:ℝ)+2) := by ring
    rw [he]
    dsimp [y] at hdiv ⊢
    nlinarith
  have hlr : left < right := by linarith
  have hmid : left < middle := by dsimp [middle];linarith
  have hmidr : middle ≤ right := by dsimp [middle];linarith
  have hlmem : left∈Icc left right := ⟨le_rfl,hlr.le⟩
  have hrmem : right∈Icc left right := ⟨hlr.le,le_rfl⟩
  have hy1 : y ≤ 1 := by
    rcases hsep with hup|hdown
    · exact (hup left hlmem).2.trans (a.child_radius_bounds left).2
    · exact (hdown left hlmem).2.trans (a.radius_bounds left).2
  have hqy : q*y ≤ L/2 := by
    have hh:=mul_le_mul_of_nonneg_left hyhi hq
    nlinarith
  refine ⟨y,left,middle,right,⟨hy,hy1⟩,hylo,hyhi,hl,hr,ha.trans hl.1,hmid,hmidr,
    hr.2.trans hb,?_,?_,?_⟩
  · dsimp [middle];linarith
  · dsimp [middle];linarith
  · rcases hsep with hup|hdown
    · left
      refine ⟨(hup left hlmem).2,?_⟩
      intro u hu
      exact ((hup u ⟨hmid.le.trans hu.1,hu.2⟩).1).trans hgrid
    · right
      refine ⟨(hdown right hrmem).1.trans hgrid,?_,?_⟩
      · intro u hu
        have huR : a.R u ≤ a.R right := hRm hu.2
        have hRright:=hRupper right hr
        have hh : (J:ℝ)*step ≤ ((J:ℝ)+2)*y := by
          have h1:=mul_le_mul_of_nonneg_left hylo (show 0 ≤ (J:ℝ)+2 by positivity)
          nlinarith
        exact huR.trans (hRright.trans hh)
      · intro u hu
        exact (hdown u ⟨hu.1,hu.2.trans hmidr⟩).2

end OAI.SKFluctuations.LaplaceWindowFormalization
