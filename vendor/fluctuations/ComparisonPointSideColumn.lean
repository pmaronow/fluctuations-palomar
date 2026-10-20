module

public import ComparisonContactSideTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory
open scoped BigOperators
open WholeUnitSideKernel
set_option maxHeartbeats 1800000

def pointLeftSquare (s t : ℝ) : ℝ :=
  (Ici s).indicator (fun t => (t⁻¹)^2) t

def pointRightSquare (width s t : ℝ) : ℝ :=
  (Iic s).indicator (fun t => ((width-t)⁻¹)^2) t

def pointSideColumn (δ width s : ℝ) : ℝ :=
  (∫t in δ..width-δ, pointLeftSquare s t) +
  (∫t in δ..width-δ, pointRightSquare width s t)

private theorem invSquare_intervalIntegrable {δ b : ℝ} (hδ : 0<δ) (hb : δ ≤ b) :
    IntervalIntegrable (fun t : ℝ => (t⁻¹)^2) volume δ b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hb]
  exact (continuous_id.continuousOn.inv₀ (fun t ht => by
    change t≠0
    linarith [ht.1])).pow 2

theorem pointLeftSquare_intervalIntegrable {δ width : ℝ}
    (hδ : 0<δ) (hwidth : 2*δ ≤ width) (s : ℝ) :
    IntervalIntegrable (pointLeftSquare s) volume δ (width-δ) := by
  have hi := invSquare_intervalIntegrable hδ (by linarith : δ ≤ width-δ)
  exact ⟨hi.1.indicator measurableSet_Ici, hi.2.indicator measurableSet_Ici⟩

theorem pointRightSquare_intervalIntegrable {δ width : ℝ}
    (hδ : 0<δ) (hwidth : 2*δ ≤ width) (s : ℝ) :
    IntervalIntegrable (pointRightSquare width s) volume δ (width-δ) := by
  have hi : IntervalIntegrable (fun t : ℝ => ((width-t)⁻¹)^2) volume δ (width-δ) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith : δ ≤ width-δ)]
    exact ((continuous_const.sub continuous_id).continuousOn.inv₀ (fun t ht => by
      change width-t≠0
      linarith [ht.2])).pow 2
  exact ⟨hi.1.indicator measurableSet_Iic, hi.2.indicator measurableSet_Iic⟩

theorem pointSideColumn_nonneg {δ width : ℝ} (hwidth : 2*δ ≤ width) (s : ℝ) :
    0 ≤ pointSideColumn δ width s := by
  apply add_nonneg
  all_goals
    apply intervalIntegral.integral_nonneg_of_forall (by linarith : δ ≤ width-δ)
    intro t
    apply indicator_nonneg
    intro _ _
    exact sq_nonneg _

private theorem integral_supported_abs_le {a b L R C : ℝ} (hab : a ≤ b)
    (hLR : L ≤ R) (hC : 0 ≤ C) (f : ℝ→ℝ)
    (hb : ∀t∈Ioc a b, |f t| ≤ (Icc L R).indicator (fun _ => C) t) :
    |∫t in a..b,f t| ≤ C*(R-L) := by
  have hi : Integrable ((Icc L R).indicator (fun _ : ℝ => C)) :=
    (integrableOn_const (show volume (Icc L R)≠⊤ by simp)).integrable_indicator measurableSet_Icc
  have hh := intervalIntegral.norm_integral_le_of_norm_le (f:=f) hab
    (ae_of_all _ (fun t ht => by simpa only [Real.norm_eq_abs] using hb t ht))
    ⟨hi.integrableOn, hi.integrableOn⟩
  have hm := integral_mono_measure (μ:=volume.restrict (Ioc a b)) Measure.restrict_le_self
    (ae_of_all _ (fun t => indicator_nonneg (fun _ _ => hC) t)) hi
  simp only [intervalIntegral.integral_of_le hab] at hh
  have he : (∫t, (Icc L R).indicator (fun _ : ℝ => C) t)=C*(R-L) := by
    rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
      Real.volume_real_Icc, max_eq_left (sub_nonneg.mpr hLR)]
    ring
  simpa only [Real.norm_eq_abs,intervalIntegral.integral_of_le hab] using hh.trans (hm.trans_eq he)

private theorem square_difference_bound {u v C : ℝ}
    (hu : u∈Icc (0:ℝ) C) (hv : v∈Icc (0:ℝ) C) : |u-v| ≤ C := by
  apply abs_le.mpr
  constructor <;> linarith [hu.1,hu.2,hv.1,hv.2]

private theorem invSquare_le {δ t : ℝ} (hδ : 0<δ) (ht : δ ≤ t) :
    (t⁻¹)^2 ≤ (δ⁻¹)^2 := by
  exact pow_le_pow_left₀ (inv_nonneg.mpr (hδ.le.trans ht))
    (inv_le_inv₀ (hδ.trans_le ht) hδ |>.mpr ht) 2

private theorem pointLeftSquare_bounds {δ width t : ℝ} (hδ : 0<δ)
    (ht : t∈Icc δ (width-δ)) (s : ℝ) : pointLeftSquare s t∈Icc (0:ℝ) ((δ⁻¹)^2) := by
  by_cases hs : t∈Ici s
  · simp only [pointLeftSquare,indicator_of_mem hs]
    exact ⟨sq_nonneg _,invSquare_le hδ ht.1⟩
  · simp only [pointLeftSquare,indicator_of_notMem hs]
    exact ⟨le_rfl,sq_nonneg _⟩

private theorem pointRightSquare_bounds {δ width t : ℝ} (hδ : 0<δ)
    (ht : t∈Icc δ (width-δ)) (s : ℝ) : pointRightSquare width s t∈Icc (0:ℝ) ((δ⁻¹)^2) := by
  by_cases hs : t∈Iic s
  · simp only [pointRightSquare,indicator_of_mem hs]
    exact ⟨sq_nonneg _,invSquare_le hδ (by linarith [ht.2])⟩
  · simp only [pointRightSquare,indicator_of_notMem hs]
    exact ⟨le_rfl,sq_nonneg _⟩

theorem pointSideColumn_stability {δ width : ℝ} (hδ : 0<δ)
    (hwidth : 2*δ ≤ width) (s r : ℝ) :
    |pointSideColumn δ width s-pointSideColumn δ width r| ≤ 
      2*(δ⁻¹)^2*|s-r| := by
  have hab : δ ≤ width-δ := by linarith
  have hl := integral_supported_abs_le hab (show min s r  ≤  max s r from min_le_max) (sq_nonneg (δ⁻¹))
    (fun t => pointLeftSquare s t-pointLeftSquare r t) (by
      intro t ht
      by_cases hm : t∈Icc (min s r) (max s r)
      · rw [indicator_of_mem hm]
        exact square_difference_bound (pointLeftSquare_bounds hδ ⟨ht.1.le,ht.2⟩ s)
          (pointLeftSquare_bounds hδ ⟨ht.1.le,ht.2⟩ r)
      · rw [indicator_of_notMem hm]
        have hcases : t < min s r ∨ max s r < t := by
          simpa only [mem_Icc,not_and_or,not_le] using hm
        rcases hcases with htlo|hthi
        · simp [pointLeftSquare,show ¬s ≤ t by linarith [min_le_left s r],
            show ¬r ≤ t by linarith [min_le_right s r]]
        · simp [pointLeftSquare,show s ≤ t by linarith [le_max_left s r],
            show r ≤ t by linarith [le_max_right s r]])
  have hr := integral_supported_abs_le hab (show min s r  ≤  max s r from min_le_max) (sq_nonneg (δ⁻¹))
    (fun t => pointRightSquare width s t-pointRightSquare width r t) (by
      intro t ht
      by_cases hm : t∈Icc (min s r) (max s r)
      · rw [indicator_of_mem hm]
        exact square_difference_bound (pointRightSquare_bounds hδ ⟨ht.1.le,ht.2⟩ s)
          (pointRightSquare_bounds hδ ⟨ht.1.le,ht.2⟩ r)
      · rw [indicator_of_notMem hm]
        have hcases : t < min s r ∨ max s r < t := by
          simpa only [mem_Icc,not_and_or,not_le] using hm
        rcases hcases with htlo|hthi
        · simp [pointRightSquare,show t ≤ s by linarith [min_le_left s r],
            show t ≤ r by linarith [min_le_right s r]]
        · simp [pointRightSquare,show ¬t ≤ s by linarith [le_max_left s r],
            show ¬t ≤ r by linarith [le_max_right s r]])
  rw [intervalIntegral.integral_sub (pointLeftSquare_intervalIntegrable hδ hwidth s)
    (pointLeftSquare_intervalIntegrable hδ hwidth r)] at hl
  rw [intervalIntegral.integral_sub (pointRightSquare_intervalIntegrable hδ hwidth s)
    (pointRightSquare_intervalIntegrable hδ hwidth r)] at hr
  have hsum := abs_add_le
    ((∫t in δ..width-δ,pointLeftSquare s t)-(∫t in δ..width-δ,pointLeftSquare r t))
    ((∫t in δ..width-δ,pointRightSquare width s t)-(∫t in δ..width-δ,pointRightSquare width r t))
  rw [max_sub_min_eq_abs] at hl hr
  dsimp only [pointSideColumn]
  have he : ((∫t in δ..width-δ,pointLeftSquare s t)+(∫t in δ..width-δ,pointRightSquare width s t))-
      ((∫t in δ..width-δ,pointLeftSquare r t)+(∫t in δ..width-δ,pointRightSquare width r t))=
      ((∫t in δ..width-δ,pointLeftSquare s t)-(∫t in δ..width-δ,pointLeftSquare r t))+
      ((∫t in δ..width-δ,pointRightSquare width s t)-(∫t in δ..width-δ,pointRightSquare width r t)) := by ring
  rw [he]
  nlinarith [abs_sub_comm s r]

theorem pointSideColumn_lipschitz {δ width : ℝ} (hδ : 0 < δ)
    (hwidth : 2*δ ≤ width) :
    LipschitzWith (Real.toNNReal (2*(δ⁻¹)^2)) (pointSideColumn δ width) := by
  apply LipschitzWith.of_dist_le_mul
  intro s r
  simpa only [Real.dist_eq,Real.coe_toNNReal _ (by positivity : 0 ≤ 2*(δ⁻¹)^2)]
    using pointSideColumn_stability hδ hwidth s r

theorem pointSideColumn_continuous {δ width : ℝ} (hδ : 0 < δ)
    (hwidth : 2*δ ≤ width) : Continuous (pointSideColumn δ width) :=
  (pointSideColumn_lipschitz hδ hwidth).continuous

private theorem leftSquare_bounds {δ width L R t : ℝ} (hδ : 0 < δ)
    (hLR : L < R) (ht : t∈Icc δ (width-δ)) :
    (left 0 L R t)^2∈Icc (0:ℝ) ((δ⁻¹)^2) := by
  have hb := left_bounds hLR (by linarith [ht.1] : (0:ℝ) < t)
  refine ⟨sq_nonneg _,?_⟩
  exact (pow_le_pow_left₀ hb.1 (by simpa only [sub_zero] using hb.2) 2).trans
    (invSquare_le hδ ht.1)

private theorem rightSquare_bounds {δ width L R t : ℝ} (hδ : 0 < δ)
    (hLR : L < R) (ht : t∈Icc δ (width-δ)) :
    (right width L R t)^2∈Icc (0:ℝ) ((δ⁻¹)^2) := by
  have hb := right_bounds hLR (by linarith [ht.2] : t < width)
  refine ⟨sq_nonneg _,?_⟩
  exact (pow_le_pow_left₀ hb.1 hb.2 2).trans
    (invSquare_le hδ (by linarith [ht.2]))

theorem sideSquareColumn_point_stability (x : ℕ → ℝ) (i : ℕ)
    {δ width s : ℝ} (hδ : 0 < δ) (hwidth : 2*δ ≤ width)
    (hLR : x i < x (i+1)) (hs : s∈Icc (x i) (x (i+1))) :
    |sideSquareColumn x δ width i-pointSideColumn δ width s| ≤
      2*(δ⁻¹)^2*(x (i+1)-x i) := by
  have hab : δ ≤ width-δ := by linarith
  have hμ : x (i+1)-x i≠0 := sub_ne_zero.mpr hLR.ne'
  have hl := integral_supported_abs_le hab hLR.le (sq_nonneg (δ⁻¹))
    (fun t => (left 0 (x i) (x (i+1)) t)^2-pointLeftSquare s t) (by
      intro t ht
      by_cases hm : t∈Icc (x i) (x (i+1))
      · rw [indicator_of_mem hm]
        exact square_difference_bound (leftSquare_bounds hδ hLR ⟨ht.1.le,ht.2⟩)
          (pointLeftSquare_bounds hδ ⟨ht.1.le,ht.2⟩ s)
      · rw [indicator_of_notMem hm]
        have hcases : t < x i ∨ x (i+1) < t := by
          simpa only [mem_Icc,not_and_or,not_le] using hm
        rcases hcases with htlo|hthi
        · simp [left,leftFraction,pointLeftSquare,min_eq_left htlo.le,
            min_eq_left (htlo.le.trans hLR.le),show ¬s ≤ t by linarith [hs.1]]
        · simp [left,leftFraction,pointLeftSquare,min_eq_right hthi.le,
            min_eq_right (hLR.le.trans hthi.le),hμ,show s ≤ t by linarith [hs.2]])
  have hr := integral_supported_abs_le hab hLR.le (sq_nonneg (δ⁻¹))
    (fun t => (right width (x i) (x (i+1)) t)^2-pointRightSquare width s t) (by
      intro t ht
      by_cases hm : t∈Icc (x i) (x (i+1))
      · rw [indicator_of_mem hm]
        exact square_difference_bound (rightSquare_bounds hδ hLR ⟨ht.1.le,ht.2⟩)
          (pointRightSquare_bounds hδ ⟨ht.1.le,ht.2⟩ s)
      · rw [indicator_of_notMem hm]
        have hcases : t < x i ∨ x (i+1) < t := by
          simpa only [mem_Icc,not_and_or,not_le] using hm
        rcases hcases with htlo|hthi
        · simp [right,rightFraction,pointRightSquare,max_eq_right htlo.le,
            max_eq_right (htlo.le.trans hLR.le),hμ,show t ≤ s by linarith [hs.1]]
        · simp [right,rightFraction,pointRightSquare,max_eq_left hthi.le,
            max_eq_left (hLR.le.trans hthi.le),show ¬t ≤ s by linarith [hs.2]])
  have hiL : IntervalIntegrable (fun t => (left 0 (x i) (x (i+1)) t)^2)
      volume δ (width-δ) := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab,zero_add,Pi.pow_def] using
      (left_continuousOn (a:=0) (b:=width-δ) hδ hLR).pow 2
  have hiR : IntervalIntegrable (fun t => (right width (x i) (x (i+1)) t)^2)
      volume δ (width-δ) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact ((right_continuousOn (a:=0) hδ hLR).mono
      (Icc_subset_Icc hδ.le le_rfl)).pow 2
  rw [intervalIntegral.integral_sub hiL (pointLeftSquare_intervalIntegrable hδ hwidth s)] at hl
  rw [intervalIntegral.integral_sub hiR (pointRightSquare_intervalIntegrable hδ hwidth s)] at hr
  have hsum := abs_add_le
    ((∫t in δ..width-δ,(left 0 (x i) (x (i+1)) t)^2)-(∫t in δ..width-δ,pointLeftSquare s t))
    ((∫t in δ..width-δ,(right width (x i) (x (i+1)) t)^2)-(∫t in δ..width-δ,pointRightSquare width s t))
  dsimp only [sideSquareColumn,pointSideColumn]
  have he : ((∫t in δ..width-δ,(left 0 (x i) (x (i+1)) t)^2)+
      (∫t in δ..width-δ,(right width (x i) (x (i+1)) t)^2))-
      ((∫t in δ..width-δ,pointLeftSquare s t)+(∫t in δ..width-δ,pointRightSquare width s t))=
      ((∫t in δ..width-δ,(left 0 (x i) (x (i+1)) t)^2)-(∫t in δ..width-δ,pointLeftSquare s t))+
      ((∫t in δ..width-δ,(right width (x i) (x (i+1)) t)^2)-(∫t in δ..width-δ,pointRightSquare width s t)) := by ring
  rw [he]
  nlinarith

theorem sideSquareColumn_point_transfer (x : ℕ → ℝ) (i : ℕ)
    {δ width s r mesh error : ℝ} (hδ : 0 < δ) (hwidth : 2*δ ≤ width)
    (hLR : x i < x (i+1)) (hs : s∈Icc (x i) (x (i+1)))
    (hmesh : x (i+1)-x i ≤ mesh) (herror : |s-r| ≤ error) :
    |sideSquareColumn x δ width i-pointSideColumn δ width r| ≤
      2*(δ⁻¹)^2*(mesh+error) := by
  have ha := sideSquareColumn_point_stability x i hδ hwidth hLR hs
  have hb := pointSideColumn_stability hδ hwidth s r
  have hc := abs_sub_le (sideSquareColumn x δ width i)
    (pointSideColumn δ width s) (pointSideColumn δ width r)
  have h0 : 0 ≤ 2*(δ⁻¹)^2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hmesh h0
  have h2 := mul_le_mul_of_nonneg_left herror h0
  nlinarith

private theorem pointLeftSquare_mass {width t : ℝ} (ht : 0 < t) (htw : t < width) :
    (∫s in 0..width,pointLeftSquare s t)=t⁻¹ := by
  have he : (fun s => pointLeftSquare s t)=(Iic t).indicator (fun _ : ℝ => (t⁻¹)^2) := by
    funext s
    by_cases hs : s ≤ t <;> simp [pointLeftSquare,hs]
  rw [he,intervalIntegral.integral_of_le (ht.le.trans htw.le),
    setIntegral_indicator measurableSet_Iic,Ioc_inter_Iic,min_eq_right htw.le,
    setIntegral_const,smul_eq_mul,Real.volume_real_Ioc,sub_zero,max_eq_left ht.le]
  field_simp

private theorem pointRightSquare_mass {width t : ℝ} (ht : 0 < t) (htw : t < width) :
    (∫s in 0..width,pointRightSquare width s t)=(width-t)⁻¹ := by
  have he : (fun s => pointRightSquare width s t)=
      (Ici t).indicator (fun _ : ℝ => ((width-t)⁻¹)^2) := by
    funext s
    by_cases hs : t ≤ s <;> simp [pointRightSquare,hs]
  have hi : Ioc (0:ℝ) width∩Ici t=Icc t width := by
    ext s
    simp only [mem_inter_iff,mem_Ioc,mem_Ici,mem_Icc]
    constructor
    · intro hs
      exact ⟨hs.2,hs.1.2⟩
    · intro hs
      exact ⟨⟨ht.trans_le hs.1,hs.2⟩,hs.1⟩
  rw [he,intervalIntegral.integral_of_le (ht.le.trans htw.le),
    setIntegral_indicator measurableSet_Ici,hi,setIntegral_const,smul_eq_mul,
    Real.volume_real_Icc,max_eq_left (sub_nonneg.mpr htw.le)]
  field_simp

theorem pointSideColumn_mass_integral {δ width : ℝ} (hδ : 0 < δ)
    (hwidth : 2*δ ≤ width) :
    (∫s in 0..width,pointSideColumn δ width s)=
      2*Real.log ((width-δ)/δ) := by
  have hab : δ ≤ width-δ := by linarith
  have hw0 : 0 ≤ width := by linarith
  let μ := volume.restrict (Ioc (0:ℝ) width)
  let ν := volume.restrict (Ioc δ (width-δ))
  have : IsFiniteMeasure μ := ⟨by simp [μ]⟩
  have hinv : Integrable (fun t : ℝ => (t⁻¹)^2) ν :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (invSquare_intervalIntegrable hδ hab)
  have hpairL : Integrable (fun p : ℝ×ℝ => pointLeftSquare p.1 p.2) (μ.prod ν) := by
    have hh := (hinv.comp_snd μ).indicator
      (measurableSet_le measurable_fst measurable_snd)
    convert hh using 1
    funext p
    by_cases hp : p.1 ≤ p.2 <;> simp [pointLeftSquare,hp]
  have hrightInv : IntervalIntegrable (fun t : ℝ => ((width-t)⁻¹)^2) volume δ (width-δ) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact ((continuous_const.sub continuous_id).continuousOn.inv₀ (fun t ht => by
      change width-t≠0
      linarith [ht.2])).pow 2
  have hinvR : Integrable (fun t : ℝ => ((width-t)⁻¹)^2) ν :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hrightInv
  have hpairR : Integrable (fun p : ℝ×ℝ => pointRightSquare width p.1 p.2) (μ.prod ν) := by
    have hh := (hinvR.comp_snd μ).indicator
      (measurableSet_le measurable_snd measurable_fst)
    convert hh using 1
    funext p
    by_cases hp : p.2 ≤ p.1 <;> simp [pointRightSquare,hp]
  have hleftOuter : IntervalIntegrable (fun s => ∫t in δ..width-δ,pointLeftSquare s t)
      volume 0 width := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hw0).mpr
    simpa only [μ,ν,IntegrableOn,intervalIntegral.integral_of_le hab] using hpairL.integral_prod_left
  have hrightOuter : IntervalIntegrable (fun s => ∫t in δ..width-δ,pointRightSquare width s t)
      volume 0 width := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hw0).mpr
    simpa only [μ,ν,IntegrableOn,intervalIntegral.integral_of_le hab] using hpairR.integral_prod_left
  have hswapL : (∫s in 0..width,∫t in δ..width-δ,pointLeftSquare s t)=
      ∫t in δ..width-δ,∫s in 0..width,pointLeftSquare s t := by
    simpa only [μ,ν,intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hw0,
      Function.uncurry] using integral_integral_swap hpairL
  have hswapR : (∫s in 0..width,∫t in δ..width-δ,pointRightSquare width s t)=
      ∫t in δ..width-δ,∫s in 0..width,pointRightSquare width s t := by
    simpa only [μ,ν,intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hw0,
      Function.uncurry] using integral_integral_swap hpairR
  have heL : (∫t in δ..width-δ,∫s in 0..width,pointLeftSquare s t)=
      ∫t in δ..width-δ,t⁻¹ := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact pointLeftSquare_mass (hδ.trans_le ht.1) (by linarith [ht.2])
  have heR : (∫t in δ..width-δ,∫s in 0..width,pointRightSquare width s t)=
      ∫t in δ..width-δ,(width-t)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact pointRightSquare_mass (hδ.trans_le ht.1) (by linarith [ht.2])
  have hlogL : (∫t in δ..width-δ,t⁻¹)=Real.log ((width-δ)/δ) :=
    integral_inv_of_pos hδ (hδ.trans_le hab)
  have hlogR : (∫t in δ..width-δ,(width-t)⁻¹)=Real.log ((width-δ)/δ) := by
    rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t⁻¹) width]
    have he : width-(width-δ)=δ := by ring
    rw [he,hlogL]
  change (∫s in 0..width,(∫t in δ..width-δ,pointLeftSquare s t)+
    (∫t in δ..width-δ,pointRightSquare width s t))=_
  rw [intervalIntegral.integral_add hleftOuter hrightOuter,hswapL,hswapR,heL,heR,hlogL,hlogR]
  ring

theorem pointSideColumn_mass_integral_le_log {δ width : ℝ} (hδ : 0 < δ)
    (hwidth : 2*δ ≤ width) :
    (∫s in 0..width,pointSideColumn δ width s) ≤ 2*Real.log (width/δ) := by
  rw [pointSideColumn_mass_integral hδ hwidth]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  apply Real.log_le_log
  · exact div_pos (by linarith) hδ
  · exact div_le_div_of_nonneg_right (by linarith : width-δ ≤ width) hδ.le

end OAI.SKFluctuations.LaplaceWindowFormalization
