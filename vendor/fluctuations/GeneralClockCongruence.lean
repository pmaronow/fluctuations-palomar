module

public import GeneralMacroPressureLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def unitClockExtension (f : ℝ → ℝ) (u : ℝ) : ℝ := f (projIcc 0 1 (by norm_num) u)

theorem unitClockExtension_eq_on (f : ℝ → ℝ) : EqOn (unitClockExtension f) f (Icc (0:ℝ) 1) := by
  intro u hu
  simp only [unitClockExtension,projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1) hu]

theorem unitClockExtension_monotone (f : ℝ → ℝ) (hf : MonotoneOn f (Icc (0:ℝ) 1)) :
    Monotone (unitClockExtension f) := by
  intro u v huv
  exact hf (projIcc 0 1 (by norm_num) u).property (projIcc 0 1 (by norm_num) v).property
    (monotone_projIcc (by norm_num : (0:ℝ) ≤ 1) huv)

theorem physicalPressure_congr_on (n : ℕ) (hn : 0 < n) (b h b' h' : ℝ → ℝ)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hb' : MonotoneOn b' (Icc (0:ℝ) 1)) (hh' : MonotoneOn h' (Icc (0:ℝ) 1))
    (hb0 : 0 ≤ b 0) (hh0 : 0 ≤ h 0) (hb0' : 0 ≤ b' 0) (hh0' : 0 ≤ h' 0)
    (heb : EqOn b b' (Icc (0:ℝ) 1)) (heh : EqOn h h' (Icc (0:ℝ) 1)) :
    realOrderedSKPathPressure n b h 0=realOrderedSKPathPressure n b' h' 0 := by
  have hp := realOrderedSKPathPressure_uniform_comparison n hn b h b' h' (B := 0) (H := 0)
    hb hh hb' hh' hb0 hh0 hb0' hh0'
    (fun u hu => by simp only [heb hu,sub_self,abs_zero,le_refl])
    (fun u hu => by simp only [heh hu,sub_self,abs_zero,le_refl]) 0
  norm_num at hp
  exact sub_eq_zero.mp hp

theorem scalarQuantileValue_congr_on (b h b' h' q : ℝ → ℝ)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hb' : MonotoneOn b' (Icc (0:ℝ) 1)) (hh' : MonotoneOn h' (Icc (0:ℝ) 1))
    (hbn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ b u) (hhn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u)
    (hbn' : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ b' u) (hhn' : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h' u)
    (heb : EqOn b b' (Icc (0:ℝ) 1)) (heh : EqOn h h' (Icc (0:ℝ) 1))
    (hq : q ∈ unitMassQuantiles) :
    generalScalarQuantileValue b h q=generalScalarQuantileValue b' h' q := by
  have hf (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
      (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hbn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ b u) :
      MonotoneOn (fun u => h u+b u*q u) (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    exact add_le_add (hh hu hv huv)
      (mul_le_mul (hb hu hv huv) (hq.1 hu hv huv) (hq.2 u hu).1 (hbn v hv))
  have hp := physicalPressure_congr_on 1 (by norm_num) (fun _ => 0)
    (fun u => h u+b u*q u) (fun _ => 0) (fun u => h' u+b' u*q u)
    (fun _ _ _ _ _ => le_rfl) (hf b h hb hh hbn)
    (fun _ _ _ _ _ => le_rfl) (hf b' h' hb' hh' hbn') le_rfl
    (add_nonneg (hhn 0 (by norm_num)) (mul_nonneg (hbn 0 (by norm_num)) (hq.2 0 (by norm_num)).1))
    le_rfl (add_nonneg (hhn' 0 (by norm_num))
      (mul_nonneg (hbn' 0 (by norm_num)) (hq.2 0 (by norm_num)).1))
    (fun _ _ => rfl) (fun u hu => by dsimp only; rw [heb hu,heh hu])
  have hi : (∫u in (0:ℝ)..1,b u*q u^2)=(∫u in (0:ℝ)..1,b' u*q u^2) := by
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [heb (by simpa using hu)]
  exact congrArg₂ (fun x y : ℝ => x+(1/4:ℝ)*y) hp hi

theorem generalScalarMinimum_congr_on (b h b' h' : ℝ → ℝ)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hb' : MonotoneOn b' (Icc (0:ℝ) 1)) (hh' : MonotoneOn h' (Icc (0:ℝ) 1))
    (hbn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ b u) (hhn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u)
    (hbn' : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ b' u) (hhn' : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h' u)
    (heb : EqOn b b' (Icc (0:ℝ) 1)) (heh : EqOn h h' (Icc (0:ℝ) 1)) :
    generalScalarMinimum b h=generalScalarMinimum b' h' := by
  unfold generalScalarMinimum generalScalarQuantileValues
  congr 1
  apply image_congr
  intro q hq
  exact scalarQuantileValue_congr_on b h b' h' q hb hh hb' hh' hbn hhn hbn' hhn' heb heh hq

theorem generalMacroPressure_tendsto_on (b h : ℝ → ℝ) {W bstar : ℝ}
    (hW : 0 < W) (hbstar : 0 < bstar) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hbb : ∀ u ∈ Icc (0:ℝ) 1, b u ∈ Icc (0:ℝ) W)
    (hbl : ∀ u ∈ Icc (0:ℝ) 1, bstar ≤ b u)
    (hhn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u) :
    Tendsto (fun n : ℕ => realOrderedSKPathPressure n b h 0) atTop
      (𝓝 (generalScalarMinimum b h)) := by
  let bc := unitClockExtension b
  let hc := unitClockExtension h
  have hbcm : Monotone bc := unitClockExtension_monotone b hb
  have hhcm : Monotone hc := unitClockExtension_monotone h hh
  have hbcb : ∀ u ∈ Icc (0:ℝ) 1, bc u ∈ Icc (0:ℝ) W := by
    intro u hu; simpa only [bc,unitClockExtension_eq_on b hu] using hbb u hu
  have hbcl : ∀ u ∈ Icc (0:ℝ) 1, bstar ≤ bc u := by
    intro u hu; simpa only [bc,unitClockExtension_eq_on b hu] using hbl u hu
  have hhcn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ hc u := by
    intro u hu; simpa only [hc,unitClockExtension_eq_on h hu] using hhn u hu
  have ht := generalMacroPressure_tendsto bc hc hW hbstar (hbcm.monotoneOn _) (hhcm.monotoneOn _)
    hbcm.measurable hbcb hbcl hhcn
  have href := generalScalarMinimum_congr_on bc hc b h (hbcm.monotoneOn _) (hhcm.monotoneOn _)
    hb hh (fun u hu => (hbcb u hu).1) hhcn (fun u hu => (hbb u hu).1) hhn
    (unitClockExtension_eq_on b) (unitClockExtension_eq_on h)
  rw [href] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  exact physicalPressure_congr_on n hn bc hc b h (hbcm.monotoneOn _) (hhcm.monotoneOn _) hb hh
    (hbcb 0 (by norm_num)).1 (hhcn 0 (by norm_num)) (hbb 0 (by norm_num)).1
    (hhn 0 (by norm_num)) (unitClockExtension_eq_on b) (unitClockExtension_eq_on h)

theorem generalMacroPressure_tendsto_of_l1_on (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) (bseq hseq : ℕ → ℝ → ℝ) (b h : ℝ → ℝ)
    {W bstar : ℝ} (hW : 0 < W) (hbstar : 0 < bstar)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hbb : ∀ u ∈ Icc (0:ℝ) 1, b u ∈ Icc (0:ℝ) W)
    (hbl : ∀ u ∈ Icc (0:ℝ) 1, bstar ≤ b u)
    (hhn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u)
    (hbs : ∀ n, MonotoneOn (bseq n) (Icc (0:ℝ) 1))
    (hhs : ∀ n, MonotoneOn (hseq n) (Icc (0:ℝ) 1))
    (hbs0 : ∀ n, 0 ≤ bseq n 0) (hhs0 : ∀ n, 0 ≤ hseq n 0)
    (hbdist : Tendsto (fun n => ∫u in (0:ℝ)..1,|bseq n u-b u|) atTop (𝓝 0))
    (hhdist : Tendsto (fun n => ∫u in (0:ℝ)..1,|hseq n u-h u|) atTop (𝓝 0)) :
    Tendsto (fun n => realOrderedSKPathPressure (N n) (bseq n) (hseq n) 0) atTop
      (𝓝 (generalScalarMinimum b h)) := by
  have hbcm := unitClockExtension_monotone b hb
  have hhcm := unitClockExtension_monotone h hh
  have hbcb : ∀ u ∈ Icc (0:ℝ) 1, unitClockExtension b u ∈ Icc (0:ℝ) W := by
    intro u hu; simpa only [unitClockExtension_eq_on b hu] using hbb u hu
  have hbcl : ∀ u ∈ Icc (0:ℝ) 1, bstar ≤ unitClockExtension b u := by
    intro u hu; simpa only [unitClockExtension_eq_on b hu] using hbl u hu
  have hhcn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ unitClockExtension h u := by
    intro u hu; simpa only [unitClockExtension_eq_on h hu] using hhn u hu
  have hd (f : ℝ → ℝ) (fseq : ℕ → ℝ → ℝ) (n : ℕ) :
      (∫u in (0:ℝ)..1,|fseq n u-unitClockExtension f u|)=(∫u in (0:ℝ)..1,|fseq n u-f u|) := by
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [unitClockExtension_eq_on f (by simpa using hu)]
  have ht := generalMacroPressure_tendsto_of_l1 N hN bseq hseq
    (unitClockExtension b) (unitClockExtension h) hW hbstar (hbcm.monotoneOn _)
    (hhcm.monotoneOn _) hbcm.measurable hbcb hbcl hhcn hbs hhs hbs0 hhs0
    (by simpa only [hd b bseq] using hbdist) (by simpa only [hd h hseq] using hhdist)
  rwa [generalScalarMinimum_congr_on (unitClockExtension b) (unitClockExtension h) b h
    (hbcm.monotoneOn _) (hhcm.monotoneOn _) hb hh (fun u hu => (hbcb u hu).1)
    hhcn (fun u hu => (hbb u hu).1) hhn (unitClockExtension_eq_on b)
    (unitClockExtension_eq_on h)] at ht

end OAI.SKFluctuations.LaplaceWindowFormalization
