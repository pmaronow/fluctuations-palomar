module

public import FinitePhysicalPropagationBarrierSelectionMeasure
public import FinitePhysicalPropagationBarrierSelectionTransfer
public import FinitePhysicalPropagationProducerSelection
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter
open scoped Topology ENNReal
set_option maxHeartbeats 4000000

def selectivePropagationWorkingExtension (f : ℝ → ℝ) : ℝ → ℝ :=
  IccExtend zero_le_one (fun u : Icc (0 : ℝ) 1 => f u)

theorem selective_propagation_working_extension_eq (f : ℝ → ℝ)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    selectivePropagationWorkingExtension f u = f u :=
  IccExtend_of_mem zero_le_one _ hu

theorem selective_propagation_working_extension_monotone {f : ℝ → ℝ}
    (hf : MonotoneOn f (Icc (0 : ℝ) 1)) :
    Monotone (selectivePropagationWorkingExtension f) := by
  apply Monotone.IccExtend zero_le_one
  intro u v huv
  exact hf u.property v.property huv

theorem selective_propagation_working_extension_continuous {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Continuous (selectivePropagationWorkingExtension f) :=
  (continuousOn_iff_continuous_domRestrict.mp hf).Icc_extend' (h := zero_le_one)

theorem selective_propagation_absolute_disagreement_selects_working_interval
    (J : ℕ) {R Z : ℝ → ℝ}
    (hR : MonotoneOn R (Icc (0 : ℝ) 1))
    (hZ : MonotoneOn Z (Icc (0 : ℝ) 1))
    (hRc : ContinuousOn R (Icc (0 : ℝ) 1))
    (hZc : ContinuousOn Z (Icc (0 : ℝ) 1))
    {a b step L : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hstep : 0 < step)
    (hRrange : ∀ u ∈ Icc a b, 0 ≤ R u ∧ R u ≤ (J : ℝ)*step)
    (hZ0 : ∀ u ∈ Icc a b, 0 ≤ Z u)
    (hbadmass : 2*(J+1 : ℝ≥0∞)*ENNReal.ofReal L <
      volume {u | u ∈ Icc a b ∧ 3*step ≤ |Z u-R u|}) :
    ∃ j : Fin (J+1), ∃ left right : ℝ,
      left ∈ Icc a b ∧ right ∈ Icc a b ∧ L < right-left ∧
      ((∀ u ∈ Icc left right,
        R u ≤ (((j : ℕ) : ℝ)+1)*step ∧ (((j : ℕ) : ℝ)+2)*step ≤ Z u) ∨
       (∀ u ∈ Icc left right,
        Z u ≤ (((j : ℕ) : ℝ)+1)*step ∧ (((j : ℕ) : ℝ)+2)*step ≤ R u)) := by
  have heR u (hu : u ∈ Icc a b) : selectivePropagationWorkingExtension R u = R u :=
    selective_propagation_working_extension_eq R (Icc_subset_Icc ha hb hu)
  have heZ u (hu : u ∈ Icc a b) : selectivePropagationWorkingExtension Z u = Z u :=
    selective_propagation_working_extension_eq Z (Icc_subset_Icc ha hb hu)
  have hset : {u | u ∈ Icc a b ∧ 3*step ≤ |selectivePropagationWorkingExtension Z u-
      selectivePropagationWorkingExtension R u|} =
      {u | u ∈ Icc a b ∧ 3*step ≤ |Z u-R u|} := by
    ext u
    constructor <;> intro hu <;>
      simpa only [mem_ofPred_eq,heR u hu.1, heZ u hu.1] using hu
  obtain ⟨j,left,right,hl,hr,hw,hsep⟩ :=
    physical_propagation_absolute_disagreement_selects_interval J
      (selective_propagation_working_extension_monotone hR)
      (selective_propagation_working_extension_monotone hZ)
      (selective_propagation_working_extension_continuous hRc)
      (selective_propagation_working_extension_continuous hZc) hstep
      (fun u hu => by simpa only [heR u hu] using hRrange u hu)
      (fun u hu => by simpa only [heZ u hu] using hZ0 u hu)
      (by simpa only [hset] using hbadmass)
  have hsub : Icc left right ⊆ Icc a b := Icc_subset_Icc hl.1 hr.2
  refine ⟨j,left,right,hl,hr,hw,?_⟩
  rcases hsep with hup | hdown
  · left
    intro u hu
    simpa only [heR u (hsub hu), heZ u (hsub hu)] using hup u hu
  · right
    intro u hu
    simpa only [heR u (hsub hu), heZ u (hsub hu)] using hdown u hu

theorem selective_propagation_upward_disagreement_selects_barrier_band
    (R Z : ℝ → ℝ) (hRm : Monotone R) (hRc : Continuous R)
    (hZm : MonotoneOn Z (Icc (0 : ℝ) 1))
    (hZc : ContinuousOn Z (Icc (0 : ℝ) 1))
    (hZb : ∀ u ∈ Icc (0 : ℝ) 1, Z u ∈ Icc (0 : ℝ) 1)
    (J : ℕ) {leftBand rightBand step L q : ℝ}
    (ha : 0 ≤ leftBand) (hb : rightBand ≤ 1) (hstep : 0 < step)
    (hRrange : ∀ u ∈ Icc leftBand rightBand,
      0 ≤ R u ∧ 4*R u ≤ (J : ℝ)*step) (hq : 0 ≤ q)
    (hwidth : q*((J : ℝ)+1)*step/2 ≤ L)
    (hbadmass : (J+1 : ℝ≥0∞)*ENNReal.ofReal L <
      volume {u | u ∈ Icc leftBand rightBand ∧ 3*step ≤ Z u-4*R u}) :
    ∃ y start stop finish : ℝ,
      0 < y ∧ y ≤ 1/4 ∧ step/4 ≤ y ∧ y ≤ ((J : ℝ)+1)*step/4 ∧
      start ∈ Icc leftBand rightBand ∧ finish ∈ Icc leftBand rightBand ∧
      0 ≤ start ∧ start < stop ∧ stop ≤ finish ∧ finish ≤ 1 ∧
      L < 2*(stop-start) ∧ q*y ≤ finish-stop ∧ 4*y ≤ Z start ∧
      (∀ u ∈ Icc stop finish, R u ≤ y) := by
  have heZ u (hu : u ∈ Icc leftBand rightBand) :
      selectivePropagationWorkingExtension Z u = Z u :=
    selective_propagation_working_extension_eq Z (Icc_subset_Icc ha hb hu)
  have hset : {u | u ∈ Icc leftBand rightBand ∧
      3*step ≤ selectivePropagationWorkingExtension Z u-4*R u} =
      {u | u ∈ Icc leftBand rightBand ∧ 3*step ≤ Z u-4*R u} := by
    ext u
    constructor <;> intro hu <;> simpa only [mem_ofPred_eq,heZ u hu.1] using hu
  obtain ⟨j,left,right,hl,hr,hlength,hsep⟩ :=
    physical_propagation_upward_disagreement_selects_interval J
      (a := leftBand) (b := rightBand) (L := L)
      (hRm.const_mul (by norm_num : (0 : ℝ) ≤ 4))
      (selective_propagation_working_extension_monotone hZm)
      (continuous_const.mul hRc)
      (selective_propagation_working_extension_continuous hZc) hstep
      (fun u hu _ => ⟨mul_nonneg (by norm_num) (hRrange u hu).1,
        (hRrange u hu).2⟩)
      (by simpa only [hset] using hbadmass)
  let y : ℝ := (((j : ℕ) : ℝ)+1)*step/4
  let stop : ℝ := (left+right)/2
  have hj : (j : ℕ) ≤ J := Nat.le_of_lt_succ j.isLt
  have hjR : ((j : ℕ) : ℝ) ≤ (J : ℝ) := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
  have hy : 0 < y := by dsimp [y]; positivity
  have hylo : step/4 ≤ y := by dsimp [y]; nlinarith
  have hyhi : y ≤ ((J : ℝ)+1)*step/4 := by dsimp [y]; nlinarith
  have hL0 : 0 ≤ L := (by positivity : 0 ≤ q*((J : ℝ)+1)*step/2).trans hwidth
  have hlr : left < right := by linarith
  have hleft : left ∈ Icc left right := ⟨le_rfl,hlr.le⟩
  have hZleft := (hsep left hleft).2
  rw [heZ left hl] at hZleft
  have hZlarge : 4*y ≤ Z left := by dsimp [y]; nlinarith
  have hy4 : y ≤ 1/4 := by
    have hZbound := (hZb left (Icc_subset_Icc ha hb hl)).2
    linarith
  have hstop : left < stop := by dsimp [stop]; linarith
  have hstopright : stop ≤ right := by dsimp [stop]; linarith
  have hreserved : q*y ≤ right-stop := by
    have hqy := mul_le_mul_of_nonneg_left hyhi hq
    dsimp [stop]
    nlinarith
  have hrampLength : L < 2*(stop-left) := by dsimp [stop]; linarith
  refine ⟨y,left,stop,right,hy,hy4,hylo,hyhi,hl,hr,ha.trans hl.1,hstop,
    hstopright,hr.2.trans hb,hrampLength,hreserved,hZlarge,?_⟩
  intro u hu
  have hRu := (hsep u ⟨hstop.le.trans hu.1,hu.2⟩).1
  dsimp [y]
  linarith

theorem selective_propagation_reserved_ramp_speed_bound
    {y Y L start stop : ℝ} (hL : 0 < L) (hy : 0 ≤ y) (hyY : y ≤ Y)
    (hwidth : L < 2*(stop-start)) :
    2*y/(stop-start) ≤ 4*Y/L := by
  have hgap : 0 < stop-start := by linarith
  have hY : 0 ≤ Y := hy.trans hyY
  apply (div_le_div_iff₀ hgap hL).mpr
  nlinarith

theorem selective_propagation_transfer_working_child_linear_profile
    (R Z : ℕ → ℝ → ℝ) (x : ℕ → ℝ) {kappa : ℝ} (hkappa : 0 < kappa)
    (hx : ∀ n, 0 < x n) (hx0 : Tendsto x atTop (𝓝 0))
    (hR : ∀ n, MonotoneOn (R n) (Icc (0 : ℝ) 1))
    (hZ : ∀ n, MonotoneOn (Z n) (Icc (0 : ℝ) 1))
    (hchild : ∀ v : ℝ, 0 < v → Tendsto (fun n => Z n (x n*v)/x n)
      atTop (𝓝 (kappa*v)))
    (hagreement : ∀ a b eps theta : ℝ, 0 < a → a < b → 0 < eps → 0 < theta →
      ∀ᶠ n in atTop, volume (physicalPropagationDisagreementMassSet (R n) (Z n)
        (x n*a) (x n*b) (eps*x n)) < ENNReal.ofReal (theta*x n)) :
    ∀ v : ℝ, 0 < v → Tendsto (fun n => R n (x n*v)/x n)
      atTop (𝓝 (kappa*v)) := by
  let Re := fun n => selectivePropagationWorkingExtension (R n)
  let Ze := fun n => selectivePropagationWorkingExtension (Z n)
  have hsmall v (hv : 0 < v) : ∀ᶠ n in atTop, x n*v ∈ Icc (0 : ℝ) 1 := by
    have ht : Tendsto (fun n => x n*v) atTop (𝓝 0) := by simpa using hx0.mul_const v
    filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
    exact ⟨mul_nonneg (hx n).le hv.le,hn.le⟩
  have hchildExt v (hv : 0 < v) : Tendsto (fun n => Ze n (x n*v)/x n)
      atTop (𝓝 (kappa*v)) := by
    apply (hchild v hv).congr'
    filter_upwards [hsmall v hv] with n hn
    rw [show Ze n (x n*v) = Z n (x n*v) from
      selective_propagation_working_extension_eq (Z n) hn]
  have hagreementExt a b eps theta (ha : 0 < a) (hab : a < b)
      (heps : 0 < eps) (htheta : 0 < theta) :
      ∀ᶠ n in atTop, volume (physicalPropagationDisagreementMassSet (Re n) (Ze n)
        (x n*a) (x n*b) (eps*x n)) < ENNReal.ofReal (theta*x n) := by
    filter_upwards [hsmall b (ha.trans hab),hagreement a b eps theta ha hab heps htheta]
      with n hnb hn
    have hset : physicalPropagationDisagreementMassSet (Re n) (Ze n)
        (x n*a) (x n*b) (eps*x n) =
        physicalPropagationDisagreementMassSet (R n) (Z n)
          (x n*a) (x n*b) (eps*x n) := by
      ext u
      have hworking (hu : u ∈ Icc (x n*a) (x n*b)) : u ∈ Icc (0 : ℝ) 1 :=
        ⟨(mul_nonneg (hx n).le ha.le).trans hu.1,hu.2.trans hnb.2⟩
      constructor <;> intro hu <;>
        simpa only [physicalPropagationDisagreementMassSet,mem_ofPred_eq,Re,Ze,
          selective_propagation_working_extension_eq (R n) (hworking hu.1),
          selective_propagation_working_extension_eq (Z n) (hworking hu.1)] using hu
    simpa only [hset] using hn
  have hparentExt := physical_propagation_transfer_actual_child_linear_profile Re Ze x hkappa
    (Eventually.of_forall hx)
    (fun n => selective_propagation_working_extension_monotone (hR n))
    (fun n => selective_propagation_working_extension_monotone (hZ n)) hchildExt hagreementExt
  intro v hv
  apply (hparentExt v hv).congr'
  filter_upwards [hsmall v hv] with n hn
  rw [show Re n (x n*v) = R n (x n*v) from
    selective_propagation_working_extension_eq (R n) hn]

end OAI.SKFluctuations.LaplaceWindowFormalization
