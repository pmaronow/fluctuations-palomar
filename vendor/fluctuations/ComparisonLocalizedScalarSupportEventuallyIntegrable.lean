module

public import ComparisonLocalizedScalarSupport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 7000000

theorem comparison_scalar_zero_of_localized_mass_eventually_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : ℕ→Measure Ω) (hfinite : ∀n,IsFiniteMeasure (mu n))
    (radius clock : ℕ→Ω→ℝ) (G : ℕ→ℝ→ℝ) (g : ℝ→ℝ)
    (F : ℝ→ℕ→Set Ω) {C t R : ℝ} (hC : 0 < C) (ht : 0 < t) (htR : t < R)
    (hF : ∀a > 0,a < C → ∀n,MeasurableSet (F a n))
    (hremoved : ∀a > 0,a < C → ∀n,(mu n).real (F a n)ᶜ ≤ a)
    (hr : ∀n,Measurable (radius n))
    (hmass : ∀eps > 0,∃c : ℝ,0 < c ∧
      ∀ᶠn in atTop,c ≤ (mu n).real {w | |radius n w-t| < eps})
    (hloc : ∀a > 0,a < C →
      (∀ᶠn in atTop,Integrable (fun w=>|G n (clock n w)|) ((mu n).restrict (F a n))) ∧
      (∀ᶠn in atTop,Integrable (fun w=>|clock n w-radius n w|) ((mu n).restrict (F a n))) ∧
      Tendsto (fun n=>∫w,|G n (clock n w)|∂(mu n).restrict (F a n)) atTop (𝓝 0) ∧
      Tendsto (fun n=>∫w,|clock n w-radius n w|∂(mu n).restrict (F a n)) atTop (𝓝 0))
    (hG : TendstoUniformlyOn G g atTop (Icc (0:ℝ) R))
    (hg : ContinuousAt g t) : g t=0 := by
  have hsel eps (heps : 0 < eps) : ∀ᶠn in atTop,∃w,
      |radius n w-t| < eps ∧ |G n (clock n w)|+|clock n w-radius n w| < eps := by
    obtain ⟨c,hc,Hmass⟩:=hmass eps heps
    let a:=min (C/2) (c/2)
    have ha : 0 < a := lt_min (by positivity) (by positivity)
    have haC : a < C := (min_le_left _ _).trans_lt (by linarith)
    have hac : a ≤ c/2 := min_le_right _ _
    obtain ⟨hGi,hKi,hG0,hK0⟩:=hloc a ha haC
    have Hz:=hG0.add hK0
    have Hsmall:=Hz.eventually (eventually_lt_nhds (show (0:ℝ)+0 < (c/2)*eps by
      simpa only [zero_add] using mul_pos (div_pos hc (by norm_num : (0:ℝ)<2)) heps))
    filter_upwards [Hmass,Hsmall,hGi,hKi] with n hn hs hGiN hKiN
    let _ : IsFiniteMeasure (mu n):=hfinite n
    have hA : MeasurableSet {w | |radius n w-t| < eps} :=
      measurableSet_lt ((hr n).sub_const t).abs measurable_const
    have hm:=comparison_restricted_positive_mass (mu n) _ (F a n) (hF a ha haC n)
      hn (hremoved a ha haC n) hac
    obtain ⟨w,hw,he⟩:=comparison_positive_mass_small_error_point ((mu n).restrict (F a n)) _ hA
      (fun w=>|G n (clock n w)|+|clock n w-radius n w|) (hGiN.add hKiN)
      (fun _=>add_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity) heps hm
      (by rw [integral_add hGiN hKiN];exact hs)
    exact ⟨w,hw,he⟩
  let eps:=fun j : ℕ=>1/((j:ℝ)+1)
  have heps j : 0 < eps j := by dsimp [eps];positivity
  have hN j:=eventually_atTop.mp (hsel (eps j) (heps j))
  choose N hN using hN
  let ns:=fun j=>max j (N j)
  have hns : Tendsto ns atTop atTop := tendsto_atTop_mono (fun _=>le_max_left _ _) tendsto_id
  have hex j:=hN j (ns j) (le_max_right _ _)
  choose w hw using hex
  have heps0 : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have Hradabs : Tendsto (fun j=>|radius (ns j) (w j)-t|) atTop (𝓝 0) :=
    squeeze_zero (fun _=>abs_nonneg _) (fun j=>(hw j).1.le) heps0
  have Hrad : Tendsto (fun j=>radius (ns j) (w j)) atTop (𝓝 t) := by
    have H : Tendsto (fun j=>radius (ns j) (w j)-t) atTop (𝓝 0) :=
      (tendsto_zero_iff_norm_tendsto_zero).mpr (by simpa only [Real.norm_eq_abs] using Hradabs)
    simpa only [sub_add_cancel,zero_add] using H.add_const t
  have Hdiffabs : Tendsto (fun j=>|clock (ns j) (w j)-radius (ns j) (w j)|) atTop (𝓝 0) :=
    squeeze_zero (fun _=>abs_nonneg _) (fun j=>by linarith [(hw j).2,abs_nonneg (G (ns j) (clock (ns j) (w j)))]) heps0
  have Hdiff : Tendsto (fun j=>clock (ns j) (w j)-radius (ns j) (w j)) atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).mpr (by simpa only [Real.norm_eq_abs] using Hdiffabs)
  have Hclock : Tendsto (fun j=>clock (ns j) (w j)) atTop (𝓝 t) := by
    simpa only [sub_add_cancel,zero_add] using Hdiff.add Hrad
  have HGabs : Tendsto (fun j=>|G (ns j) (clock (ns j) (w j))|) atTop (𝓝 0) :=
    squeeze_zero (fun _=>abs_nonneg _) (fun j=>by linarith [(hw j).2,abs_nonneg (clock (ns j) (w j)-radius (ns j) (w j))]) heps0
  have HGzero : Tendsto (fun j=>G (ns j) (clock (ns j) (w j))) atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).mpr (by simpa only [Real.norm_eq_abs] using HGabs)
  have Hmem : ∀ᶠj in atTop,clock (ns j) (w j)∈Icc (0:ℝ) R := by
    filter_upwards [Hclock.eventually (eventually_gt_nhds ht),Hclock.eventually (eventually_lt_nhds htR)]
      with j hj0 hjR
    exact ⟨hj0.le,hjR.le⟩
  have H:=(hG.seq_tendstoUniformlyOn ns hns).tendsto_comp hg.continuousWithinAt
    (tendsto_nhdsWithin_iff.mpr ⟨Hclock,Hmem⟩)
  exact tendsto_nhds_unique H HGzero

end OAI.SKFluctuations.LaplaceWindowFormalization
