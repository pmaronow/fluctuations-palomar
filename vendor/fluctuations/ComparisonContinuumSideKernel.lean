module

public import ComparisonDirectConcentration
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open MeasureTheory Set
open scoped BigOperators

def leftFraction (L R i : ℝ) : ℝ := min i R - min i L
def rightFraction (L R i : ℝ) : ℝ := max i R - max i L
def left (a L R i : ℝ) : ℝ := leftFraction L R i / (R-L) / (i-a)
def right (b L R i : ℝ) : ℝ := rightFraction L R i / (R-L) / (b-i)

theorem leftFraction_bounds {L R i : ℝ} (hLR : L ≤ R) :
    leftFraction L R i ∈ Icc (0:ℝ) (R-L) := by
  constructor
  · exact sub_nonneg.mpr (min_le_min_left i hLR)
  · rcases le_total i L with hi|hi
    · simp only [leftFraction,min_eq_left hi,min_eq_left (hi.trans hLR),sub_self]
      exact sub_nonneg.mpr hLR
    · rcases le_total i R with hj|hj
      · simp only [leftFraction,min_eq_left hj,min_eq_right hi]
        linarith
      · simp only [leftFraction,min_eq_right hj,min_eq_right (hLR.trans hj)]
        exact le_rfl

theorem rightFraction_bounds {L R i : ℝ} (hLR : L ≤ R) :
    rightFraction L R i ∈ Icc (0:ℝ) (R-L) := by
  constructor
  · exact sub_nonneg.mpr (max_le_max_left i hLR)
  · rcases le_total i L with hi|hi
    · simp only [rightFraction,max_eq_right hi,max_eq_right (hi.trans hLR)]
      exact le_rfl
    · rcases le_total i R with hj|hj
      · simp only [rightFraction,max_eq_right hj,max_eq_left hi]
        linarith
      · simp only [rightFraction,max_eq_left hj,max_eq_left (hLR.trans hj),sub_self]
        exact sub_nonneg.mpr hLR

theorem left_bounds {a L R i : ℝ} (hLR : L < R) (hai : a < i) :
    left a L R i ∈ Icc (0:ℝ) (i-a)⁻¹ := by
  have hf := leftFraction_bounds (i:=i) hLR.le
  have hμ : 0 < R-L := sub_pos.mpr hLR
  have hs : leftFraction L R i/(R-L) ≤ 1 := (div_le_one hμ).mpr hf.2
  constructor
  · exact div_nonneg (div_nonneg hf.1 hμ.le) (sub_pos.mpr hai).le
  · simpa only [left,one_div] using div_le_div_of_nonneg_right hs (sub_pos.mpr hai).le

theorem right_bounds {b L R i : ℝ} (hLR : L < R) (hib : i < b) :
    right b L R i ∈ Icc (0:ℝ) (b-i)⁻¹ := by
  have hf := rightFraction_bounds (i:=i) hLR.le
  have hμ : 0 < R-L := sub_pos.mpr hLR
  have hs : rightFraction L R i/(R-L) ≤ 1 := (div_le_one hμ).mpr hf.2
  constructor
  · exact div_nonneg (div_nonneg hf.1 hμ.le) (sub_pos.mpr hib).le
  · simpa only [right,one_div] using div_le_div_of_nonneg_right hs (sub_pos.mpr hib).le

theorem left_continuousOn {a b δ L R : ℝ} (hδ : 0 < δ) (hLR : L < R) :
    ContinuousOn (left a L R) (Icc (a+δ) b) := by
  apply ContinuousOn.div
  · exact ((continuous_id.min continuous_const).sub
      (continuous_id.min continuous_const)).continuousOn.div_const _
  · exact (continuous_id.sub continuous_const).continuousOn
  · intro i hi
    have : a < i := by linarith [hi.1]
    exact sub_ne_zero.mpr (ne_of_gt this)

theorem right_continuousOn {a b δ L R : ℝ} (hδ : 0 < δ) (hLR : L < R) :
    ContinuousOn (right b L R) (Icc a (b-δ)) := by
  apply ContinuousOn.div
  · exact ((continuous_id.max continuous_const).sub
      (continuous_id.max continuous_const)).continuousOn.div_const _
  · exact (continuous_const.sub continuous_id).continuousOn
  · intro i hi
    have : i < b := by linarith [hi.2]
    exact sub_ne_zero.mpr (ne_of_gt this)

theorem left_intervalIntegrable {a b δ L R : ℝ} (hδ : 0 < δ)
    (hδb : δ ≤ b-a) (hLR : L < R) :
    IntervalIntegrable (left a L R) volume (a+δ) b := by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le (by linarith : a+δ ≤ b)] using left_continuousOn hδ hLR

theorem right_intervalIntegrable {a b δ L R : ℝ} (hδ : 0 < δ)
    (hδb : δ ≤ b-a) (hLR : L < R) :
    IntervalIntegrable (right b L R) volume a (b-δ) := by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le (by linarith : a ≤ b-δ)] using right_continuousOn hδ hLR

theorem left_column_integral_le {a b δ L R : ℝ} (hδ : 0 < δ)
    (hδb : δ ≤ b-a) (hLR : L < R) :
    (∫i in (a+δ)..b,left a L R i) ≤ Real.log ((b-a)/δ) := by
  have hab : a+δ ≤ b := by linarith
  have hi : IntervalIntegrable (fun i:ℝ=>(i-a)⁻¹) volume (a+δ) b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (continuous_id.sub continuous_const).continuousOn
    intro i hi
    have hii : i∈Icc (a+δ) b := by simpa only [uIcc_of_le hab] using hi
    change i-a≠0
    exact sub_ne_zero.mpr (by linarith [hii.1])
  have hle := intervalIntegral.integral_mono_on hab (left_intervalIntegrable hδ hδb hLR) hi
    (fun i hi=>(left_bounds hLR (by linarith [hi.1])).2)
  have he : (∫i in (a+δ)..b,(i-a)⁻¹)=Real.log ((b-a)/δ) := by
    rw [intervalIntegral.integral_comp_sub_right (fun x:ℝ=>x⁻¹) a]
    have hsub : a+δ-a=δ := by ring
    rw [hsub,integral_inv_of_pos hδ (by linarith)]
  exact hle.trans_eq he

theorem right_column_integral_le {a b δ L R : ℝ} (hδ : 0 < δ)
    (hδb : δ ≤ b-a) (hLR : L < R) :
    (∫i in a..(b-δ),right b L R i) ≤ Real.log ((b-a)/δ) := by
  have hab : a ≤ b-δ := by linarith
  have hi : IntervalIntegrable (fun i:ℝ=>(b-i)⁻¹) volume a (b-δ) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (continuous_const.sub continuous_id).continuousOn
    intro i hi
    have hii : i∈Icc a (b-δ) := by simpa only [uIcc_of_le hab] using hi
    change b-i≠0
    exact sub_ne_zero.mpr (by linarith [hii.2])
  have hle := intervalIntegral.integral_mono_on hab (right_intervalIntegrable hδ hδb hLR) hi
    (fun i hi=>(right_bounds hLR (by linarith [hi.2])).2)
  have he : (∫i in a..(b-δ),(b-i)⁻¹)=Real.log ((b-a)/δ) := by
    rw [intervalIntegral.integral_comp_sub_left (fun x:ℝ=>x⁻¹) b]
    have hsub : b-(b-δ)=δ := by ring
    rw [hsub,integral_inv_of_pos hδ (by linarith)]
  exact hle.trans_eq he

theorem left_weighted_column_integral_le {ι : Type*} (units : Finset ι)
    (L R weight : ι → ℝ) {a b δ : ℝ} (hδ : 0 < δ) (hδb : δ ≤ b-a)
    (hunit : ∀u∈units,L u < R u) (hw : ∀u∈units,0 ≤ weight u) :
    (∫i in (a+δ)..b,∑u∈units,weight u*left a (L u) (R u) i) ≤ Real.log ((b-a)/δ)*(∑u∈units,weight u) := by
  rw [intervalIntegral.integral_finsetSum (fun u hu=>
    (left_intervalIntegrable hδ hδb (hunit u hu)).const_mul (weight u))]
  calc
    _ ≤ ∑u∈units,weight u*Real.log ((b-a)/δ) := by
      apply Finset.sum_le_sum
      intro u hu
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (left_column_integral_le hδ hδb (hunit u hu)) (hw u hu)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _; ring

theorem right_weighted_column_integral_le {ι : Type*} (units : Finset ι)
    (L R weight : ι → ℝ) {a b δ : ℝ} (hδ : 0 < δ) (hδb : δ ≤ b-a)
    (hunit : ∀u∈units,L u < R u) (hw : ∀u∈units,0 ≤ weight u) :
    (∫i in a..(b-δ),∑u∈units,weight u*right b (L u) (R u) i) ≤ Real.log ((b-a)/δ)*(∑u∈units,weight u) := by
  rw [intervalIntegral.integral_finsetSum (fun u hu=>
    (right_intervalIntegrable hδ hδb (hunit u hu)).const_mul (weight u))]
  calc
    _ ≤ ∑u∈units,weight u*Real.log ((b-a)/δ) := by
      apply Finset.sum_le_sum
      intro u hu
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (right_column_integral_le hδ hδb (hunit u hu)) (hw u hu)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _; ring

theorem left_fraction_sum (x : ℕ → ℝ) (K : ℕ) (i : ℝ) :
    (∑u∈Finset.range K,leftFraction (x u) (x (u+1)) i)=min i (x K)-min i (x 0) := by
  simp only [leftFraction]
  exact Finset.sum_range_sub (fun u=>min i (x u)) K

theorem right_fraction_sum (x : ℕ → ℝ) (K : ℕ) (i : ℝ) :
    (∑u∈Finset.range K,rightFraction (x u) (x (u+1)) i)=max i (x K)-max i (x 0) := by
  simp only [rightFraction]
  exact Finset.sum_range_sub (fun u=>max i (x u)) K

theorem left_row_normalized (x : ℕ → ℝ) (K : ℕ) {a b i : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hai : a < i) (hib : i ≤ b)
    (hunit : ∀u∈Finset.range K,x u < x (u+1)) :
    (∑u∈Finset.range K,(x (u+1)-x u)*left a (x u) (x (u+1)) i)=1 := by
  have hterm (u : ℕ) (hu : u∈Finset.range K) :
      (x (u+1)-x u)*left a (x u) (x (u+1)) i=
        leftFraction (x u) (x (u+1)) i/(i-a) := by
    unfold left
    have hμ : x (u+1)-x u≠0 := sub_ne_zero.mpr (ne_of_gt (hunit u hu))
    field_simp
  rw [Finset.sum_congr rfl hterm,← Finset.sum_div,left_fraction_sum,hstart,hend]
  rw [min_eq_left hib,min_eq_right hai.le,div_self (sub_ne_zero.mpr (ne_of_gt hai))]

theorem right_row_normalized (x : ℕ → ℝ) (K : ℕ) {a b i : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hai : a ≤ i) (hib : i < b)
    (hunit : ∀u∈Finset.range K,x u < x (u+1)) :
    (∑u∈Finset.range K,(x (u+1)-x u)*right b (x u) (x (u+1)) i)=1 := by
  have hterm (u : ℕ) (hu : u∈Finset.range K) :
      (x (u+1)-x u)*right b (x u) (x (u+1)) i=
        rightFraction (x u) (x (u+1)) i/(b-i) := by
    unfold right
    have hμ : x (u+1)-x u≠0 := sub_ne_zero.mpr (ne_of_gt (hunit u hu))
    field_simp
  rw [Finset.sum_congr rfl hterm,← Finset.sum_div,right_fraction_sum,hstart,hend]
  rw [max_eq_right hib.le,max_eq_left hai,div_self (sub_ne_zero.mpr (ne_of_gt hib))]

end OAI.SKFluctuations.WholeUnitSideKernel
