module
public import SKConstants.ParisiContinuumEquilibrium
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Hierarchy.TimeChainRepresentation

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.SK.Analytic

def gridCDF (α : ℝ → ℝ) (h : ℝ) (r : ℝ) : ℝ := α ((⌊r/h⌋ : ℤ) * h)

theorem gridCDF_mono {α : ℝ → ℝ} (hα : Monotone α) {h : ℝ} (hh : 0 < h) :
    Monotone (gridCDF α h) := by
  intro x y hxy
  apply hα
  apply mul_le_mul_of_nonneg_right _ hh.le
  exact_mod_cast Int.floor_mono ((div_le_div_iff_of_pos_right hh).mpr hxy)

theorem gridCDF_bounds {α : ℝ → ℝ} (hα : Monotone α) {h : ℝ} (hh : 0 < h) (r : ℝ) :
    α (r-h) ≤ gridCDF α h r ∧ gridCDF α h r ≤ α r := by
  constructor
  · apply hα
    have H := mul_le_mul_of_nonneg_right (Int.sub_one_lt_floor (r/h)).le hh.le
    nlinarith [div_mul_cancel₀ r hh.ne']
  · apply hα
    exact (mul_le_mul_of_nonneg_right (Int.floor_le (r/h)) hh.le).trans_eq
      (div_mul_cancel₀ r hh.ne')

theorem gridCDF_eq_cell (α : ℝ → ℝ) {h : ℝ} (hh : 0 < h) (i : ℕ)
    {r : ℝ} (hr : r ∈ Ico ((i:ℝ)*h) (((i+1:ℕ):ℝ)*h)) :
    gridCDF α h r = α ((i:ℝ)*h) := by
  unfold gridCDF
  have hf : ⌊r/h⌋ = (i : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor
    · exact (le_div_iff₀ hh).mpr (by simpa using hr.1)
    · exact (div_lt_iff₀ hh).mpr (by simpa [Nat.cast_add, Nat.cast_one] using hr.2)
  rw [hf]
  simp

theorem gridCDF_integral_abs_error {α : ℝ → ℝ} (hα : Monotone α)
    (ha : ∀ r, α r ∈ Icc (0:ℝ) 1) {h T : ℝ} (hh : 0 < h) (hT : 0 ≤ T) :
    (∫ r in (0:ℝ)..T, |gridCDF α h r-α r|) ≤ h := by
  have hi (a b : ℝ) : IntervalIntegrable α volume a b := hα.intervalIntegrable
  have hig (a b : ℝ) : IntervalIntegrable (gridCDF α h) volume a b :=
    (gridCDF_mono hα hh).intervalIntegrable
  have his (a b : ℝ) : IntervalIntegrable (fun r => α (r-h)) volume a b :=
    (hα.comp (show Monotone (fun r : ℝ => r-h) from fun a b hab => sub_le_sub_right hab h)).intervalIntegrable
  have he (r : ℝ) : |gridCDF α h r-α r| ≤ α r-α (r-h) := by
    obtain ⟨hlo,hup⟩ := gridCDF_bounds hα hh r
    rw [abs_of_nonpos (sub_nonpos.mpr hup)]
    linarith
  have H := intervalIntegral.integral_mono hT ((hig 0 T).sub (hi 0 T)).abs
    ((hi 0 T).sub (his 0 T)) (fun r => he r)
  refine H.trans ?_
  rw [intervalIntegral.integral_sub (hi 0 T) (his 0 T),
    intervalIntegral.integral_comp_sub_right]
  have hs := intervalIntegral.integral_add_adjacent_intervals (hi (-h) 0) (hi 0 T)
  have ht := intervalIntegral.integral_add_adjacent_intervals (hi (-h) (T-h)) (hi (T-h) T)
  have hlo : 0 ≤ ∫ r in -h..(0:ℝ), α r :=
    intervalIntegral.integral_nonneg (by linarith) (fun r _ => (ha r).1)
  have hup : (∫ r in T-h..T, α r) ≤ h := by
    calc
      _ ≤ ∫ _r in T-h..T, (1:ℝ) := intervalIntegral.integral_mono (by linarith)
        (hi (T-h) T) intervalIntegrable_const (fun r => (ha r).2)
      _ = h := by simp
  simp only [zero_sub]
  linarith

theorem gridCDF_interval_integral_abs_error {α : ℝ → ℝ} (hα : Monotone α)
    (ha : ∀ r, α r ∈ Icc (0:ℝ) 1) {h s T : ℝ} (hh : 0 < h) (hsT : s ≤ T) :
    (∫ r in s..T, |gridCDF α h r-α r|) ≤ h := by
  have hi (a b : ℝ) : IntervalIntegrable α volume a b := hα.intervalIntegrable
  have hig (a b : ℝ) : IntervalIntegrable (gridCDF α h) volume a b :=
    (gridCDF_mono hα hh).intervalIntegrable
  have his (a b : ℝ) : IntervalIntegrable (fun r => α (r-h)) volume a b :=
    (hα.comp (show Monotone (fun r : ℝ => r-h) from fun a b hab => sub_le_sub_right hab h)).intervalIntegrable
  have he (r : ℝ) : |gridCDF α h r-α r| ≤ α r-α (r-h) := by
    obtain ⟨hlo,hup⟩ := gridCDF_bounds hα hh r
    rw [abs_of_nonpos (sub_nonpos.mpr hup)]
    linarith
  refine (intervalIntegral.integral_mono hsT ((hig s T).sub (hi s T)).abs
    ((hi s T).sub (his s T)) (fun r => he r)).trans ?_
  rw [intervalIntegral.integral_sub (hi s T) (his s T),
    intervalIntegral.integral_comp_sub_right]
  have hs := intervalIntegral.integral_add_adjacent_intervals (hi (s-h) s) (hi s T)
  have ht := intervalIntegral.integral_add_adjacent_intervals (hi (s-h) (T-h)) (hi (T-h) T)
  have hlo : 0 ≤ ∫ r in s-h..s, α r :=
    intervalIntegral.integral_nonneg (by linarith) (fun r _ => (ha r).1)
  have hup : (∫ r in T-h..T, α r) ≤ h := by
    calc
      _ ≤ ∫ _r in T-h..T, (1:ℝ) := intervalIntegral.integral_mono (by linarith)
        (hi (T-h) T) intervalIntegrable_const (fun r => (ha r).2)
      _ = h := by simp
  linarith

theorem gridCDF_right_continuous (α : ℝ → ℝ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    ContinuousWithinAt (gridCDF α h) (Ici x) x := by
  let k : ℤ := ⌊x/h⌋
  have hxb : x < ((k:ℝ)+1)*h := by
    have H := Int.lt_floor_add_one (x/h)
    exact (div_lt_iff₀ hh).mp H
  have he : (fun r => gridCDF α h r) =ᶠ[𝓝[Ici x] x] (fun _ => gridCDF α h x) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hxb)] with r hr hrb
    have hfr : ⌊r/h⌋ = k := Int.floor_eq_iff.mpr
      ⟨(le_div_iff₀ hh).mpr ((mul_le_mul_of_nonneg_right (Int.floor_le (x/h)) hh.le).trans
        (by rw [div_mul_cancel₀ _ hh.ne']; exact hr)),
       (div_lt_iff₀ hh).mpr hrb⟩
    simp only [gridCDF, hfr]
    rfl
  exact tendsto_const_nhds.congr' he.symm

def gridStieltjesCDF (α : ℝ → ℝ) (hα : Monotone α) (h : ℝ) (hh : 0 < h) :
    StieltjesFunction ℝ where
  toFun := gridCDF α h
  mono' := gridCDF_mono hα hh
  right_continuous' := gridCDF_right_continuous α hh

end SKConstants.ParisiFullSupport
