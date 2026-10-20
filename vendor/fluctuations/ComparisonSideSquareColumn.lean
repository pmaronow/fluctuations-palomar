module

public import ComparisonContinuumSideKernel

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open MeasureTheory Set

theorem integral_inv_square_sub_of_pos {a l b : ℝ} (hal : a < l) (hlb : l ≤ b) :
    (∫t in l..b,((t-a)⁻¹)^2)=(l-a)⁻¹-(b-a)⁻¹ := by
  rw [intervalIntegral.integral_comp_sub_right (fun x:ℝ=>(x⁻¹)^2) a]
  have hn : (0:ℝ)∉uIcc (l-a) (b-a) := by
    rw [uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  have h := integral_zpow (a:=l-a) (b:=b-a) (n:=(-2:ℤ)) (Or.inr ⟨by norm_num,hn⟩)
  norm_num [zpow_neg,inv_pow] at h ⊢
  exact h.trans (by ring)

theorem left_square_column_le_reciprocal {a b δ L R : ℝ}
    (hδ : 0 < δ) (hδb : δ ≤ b-a) (hLR : L < R) (hLb : L ≤ b) :
    (∫t in (a+δ)..b,(left a L R t)^2) ≤ (max δ (L-a))⁻¹ := by
  have hab : a+δ ≤ b := by linarith
  have hleft := (left_intervalIntegrable hδ hδb hLR)
  have hleftSq : IntervalIntegrable (fun t=>(left a L R t)^2) volume (a+δ) b := by
    apply ContinuousOn.intervalIntegrable (μ:=volume)
    simpa [uIcc_of_le hab,Pi.pow_def] using (left_continuousOn hδ hLR).pow 2
  let l := max (a+δ) L
  have hal : a < l := (by linarith : a < a+δ).trans_le (le_max_left _ _)
  have hlb : l ≤ b := max_le hab hLb
  have hsubset : Icc l b⊆Icc (a+δ) b := Icc_subset_Icc (le_max_left _ _) le_rfl
  have hiSq : IntervalIntegrable (fun t=>(left a L R t)^2) volume l b :=
    hleftSq.mono_set (by simpa only [uIcc_of_le hlb,uIcc_of_le hab] using hsubset)
  have hinv : IntervalIntegrable (fun t=>((t-a)⁻¹)^2) volume l b := by
    apply ContinuousOn.intervalIntegrable (μ:=volume)
    simpa [uIcc_of_le hlb,Pi.pow_def,Pi.inv_def] using
      ((continuous_id.sub continuous_const).continuousOn.inv₀ (fun (t:ℝ) (ht:t∈Icc l b)=>by
        change t-a≠0
        exact sub_ne_zero.mpr (by linarith [ht.1]))).pow 2
  have heq : (∫t in (a+δ)..b,(left a L R t)^2)=(∫t in l..b,(left a L R t)^2) := by
    by_cases hL:L ≤ a+δ
    · simp only [l,max_eq_left hL]
    · have hL' : a+δ ≤ L := (not_le.mp hL).le
      have hl : l=L := max_eq_right hL'
      rw [hl] at hiSq ⊢
      have hlow : (∫t in (a+δ)..L,(left a L R t)^2)=0 := by
        calc
          _ = ∫t in (a+δ)..L,(0:ℝ) := intervalIntegral.integral_congr (fun t ht=>by
            rw [uIcc_of_le hL'] at ht
            have htL : t ≤ L := ht.2
            simp [left,leftFraction,min_eq_left htL,min_eq_left (htL.trans hLR.le)])
          _ = 0 := by simp
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hleftSq.mono_set (by
          rw [uIcc_of_le hL',uIcc_of_le hab]
          exact Icc_subset_Icc le_rfl hLb)) hiSq,hlow,zero_add]
  rw [heq]
  have hm := intervalIntegral.integral_mono_on hlb hiSq hinv (fun t ht=>by
    have hb := left_bounds hLR (hal.trans_le ht.1)
    exact pow_le_pow_left₀ hb.1 hb.2 2)
  rw [integral_inv_square_sub_of_pos hal hlb] at hm
  have he : l-a=max δ (L-a) := by
    dsimp only [l]
    rw [← max_sub_sub_right]
    congr 1
    ring
  rw [he] at hm
  exact hm.trans (sub_le_self _ (inv_nonneg.mpr (by linarith)))

theorem right_eq_reflected_left (b L R t : ℝ) :
    right b L R t=left (-b) (-R) (-L) (-t) := by
  unfold right left rightFraction leftFraction
  simp only [min_neg_neg]
  congr 1 <;> ring

theorem right_square_column_le_reciprocal {a b δ L R : ℝ}
    (hδ : 0 < δ) (hδb : δ ≤ b-a) (hLR : L < R) (haR : a ≤ R) :
    (∫t in a..(b-δ),(right b L R t)^2) ≤ (max δ (b-R))⁻¹ := by
  have h := left_square_column_le_reciprocal (a:=-b) (b:=-a)
    (L:=-R) (R:=-L) hδ (by linarith) (by linarith) (by linarith)
  have he : (∫t in a..(b-δ),(right b L R t)^2)=
      (∫t in (-b+δ)..(-a),(left (-b) (-R) (-L) t)^2) := by
    simp_rw [right_eq_reflected_left]
    have hr := intervalIntegral.integral_comp_neg (fun t:ℝ=>(left (-b) (-R) (-L) t)^2) (a:=a) (b:=b-δ)
    convert hr using 1 <;> congr 1 <;> ring
  rw [he]
  convert h using 1 <;> ring

end OAI.SKFluctuations.WholeUnitSideKernel
