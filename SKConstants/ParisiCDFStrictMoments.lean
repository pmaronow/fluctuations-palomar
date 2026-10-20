module

public import SKConstants.ParisiCDFCurvatureFields
public import SKConstants.ParisiCDFSymmetry
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Parisi.CDFSupportGap

@[expose] public section

/-!
Strict positivity of actual feedback moments.  The first three generic lemmas
are adapted from OpenAI math, Apache-2.0, commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb,
Diffusion/Diffusion.lean and Moments/StrictMoments.lean.  They apply directly to
the constructed finite-temperature drift and its actual Brownian law.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.ZeroTemperatureSK.WeakIto SKConstantsOAI.SK.Analytic

variable {Ω : Type*} [MeasurableSpace Ω]

lemma independent_gaussian_sum_interval_pos (P : Measure Ω) [IsProbabilityMeasure P]
    {Y Z : Ω → ℝ} (hY : Measurable Y) (hZ : Measurable Z) {v : ℝ≥0} (hv : v ≠ 0)
    (hLaw : HasLaw Z (gaussianReal 0 v) P) (hi : IndepFun Y Z P)
    {a b : ℝ} (hab : a < b) : 0 < P {ξ | Y ξ+Z ξ ∈ Ioo a b} := by
  let S : Set (ℝ × ℝ) := {p | p.1+p.2 ∈ Ioo a b}
  have hS : MeasurableSet S := measurableSet_Ioo.preimage (measurable_fst.add measurable_snd)
  have he := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable).mp hi
  apply pos_iff_ne_zero.mpr
  intro hz
  have hp : ((P.map Y).prod (gaussianReal 0 v)) S=0 := by
    rw [← hLaw.map_eq,← he,Measure.map_apply (hY.prodMk hZ) hS]
    exact hz
  obtain ⟨y,hy⟩ := (Measure.measure_prod_null hS |>.mp hp).exists
  have hy0 := gaussianReal_absolutelyContinuous' 0 hv hy
  have hsec : Prod.mk y ⁻¹' S=Ioo (a-y) (b-y) := by
    ext z
    change (a < y+z ∧ y+z < b) ↔ (a-y < z ∧ z < b-y)
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  rw [hsec,Real.volume_Ioo,ENNReal.ofReal_eq_zero] at hy0
  linarith

lemma BoundedLipschitzDrift.solution_interval_pos (b : BoundedLipschitzDrift) (W : BrownianSystem Ω)
    (t : ℝ≥0) (ht : 0 < (t:ℝ)) {a c : ℝ} (hac : a < c) :
    0 < W.law {ξ | b.solution W.driver t ξ ∈ Ioo a c} := by
  let := W.isProbability
  have hD : 0 < (b.bound:ℝ)+1 := by positivity
  have hw : 0 < (c-a)/(4*((b.bound:ℝ)+1)) := div_pos (sub_pos.mpr hac) (by positivity)
  obtain ⟨h,hh0,hh⟩ := exists_between (lt_min ht hw)
  have hht : h < (t:ℝ) := (lt_min_iff.mp hh).1
  have hhw : 4*((b.bound:ℝ)+1)*h < c-a := by
    have h1 := (lt_div_iff₀ (by positivity : (0:ℝ) < 4*((b.bound:ℝ)+1))).mp (lt_min_iff.mp hh).2
    nlinarith
  have hdh : 2*(b.bound:ℝ)*h < c-a := by nlinarith [b.bound.coe_nonneg]
  let H : ℝ≥0 := ⟨h,hh0.le⟩
  let S : ℝ≥0 := ⟨(t:ℝ)-h,sub_nonneg.mpr hht.le⟩
  have htime : S+H=t := by apply NNReal.coe_injective;change (t:ℝ)-h+h=t;ring
  have hi := adapted_indep_increment W.brownian.toIsPreBrownianReal W.measurable S H (b.solution_adapted W S)
  have hLaw := W.brownian.toIsPreBrownianReal.hasLaw_sub (S+H) S
  have hv : nndist ((S+H:ℝ≥0):ℝ) (S:ℝ)=H := by
    apply NNReal.coe_injective
    rw [coe_nndist,Real.dist_eq,NNReal.coe_add,add_sub_cancel_left,abs_of_nonneg H.coe_nonneg]
  have hLaw' : HasLaw (fun ξ => W.B (S+H) ξ-W.B S ξ) (gaussianReal 0 H) W.law := by
    convert hLaw using 1
    congr 1
    exact hv.symm
  have hp := independent_gaussian_sum_interval_pos W.law (b.solution_measurable W S)
    ((W.measurable (S+H)).sub (W.measurable S)) (show H ≠ 0 from ne_of_gt hh0) hLaw' hi
    (a := a+(b.bound:ℝ)*h) (b := c-(b.bound:ℝ)*h) (by linarith)
  apply hp.trans_le
  apply measure_mono_ae
  filter_upwards [b.solution_increment W S H] with ξ hξ hmem
  rw [htime,← NNReal.coe_add,htime] at hξ
  have hd := b.displacement_bound W S t ξ
  have he : |(t:ℝ)-(S:ℝ)|=h := by change |(t:ℝ)-((t:ℝ)-h)|=h; rw [sub_sub_cancel,abs_of_pos hh0]
  rw [he] at hd
  rcases abs_le.mp hd with ⟨hdl,hdu⟩
  change a+(b.bound:ℝ)*h < b.solution W.driver S ξ+(W.B (S+H) ξ-W.B S ξ) ∧
    b.solution W.driver S ξ+(W.B (S+H) ξ-W.B S ξ) < c-(b.bound:ℝ)*h at hmem
  rw [htime] at hmem
  change a < b.solution W.driver t ξ ∧ b.solution W.driver t ξ < c
  rw [hξ]
  constructor <;> linarith [hmem.1,hmem.2]

lemma integral_pos_of_interval_support {P : Measure Ω} {X : Ω → ℝ} {f : ℝ → ℝ}
    (hX : ∀ a b : ℝ, a < b → 0 < P {ξ | X ξ ∈ Ioo a b})
    (hf : Continuous f) (hn : ∀ x, 0 ≤ f x) (hi : Integrable (fun ξ => f (X ξ)) P)
    (hne : ∃ x, f x ≠ 0) : 0 < ∫ ξ, f (X ξ) ∂P := by
  obtain ⟨x,hx⟩ := hne
  have he : ∀ᶠ y in 𝓝 x, f y ≠ 0 := hf.continuousAt.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hx)
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp he
  apply (integral_pos_iff_support_of_nonneg (fun ξ => hn (X ξ)) hi).mpr
  apply (hX (x-ε) (x+ε) (by linarith)).trans_le
  apply measure_mono
  intro ξ hξ
  change f (X ξ) ≠ 0
  apply hball
  rw [Real.dist_eq,abs_lt]
  change x-ε < X ξ ∧ X ξ < x+ε at hξ
  constructor <;> linarith [hξ.1,hξ.2]

lemma scalarCDFValue_linear_lower_bound (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1)
    {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) :
    ∃ C : ℝ, ∀ x, |x|-C ≤ scalarCDFValue β α q (Real.toNNReal (1-q)) x := by
  let C := scalarTimeMassConstantK β 1*(1-q)+|β| *Real.sqrt (1-q)*standardGaussianAbsMoment
  refine ⟨C, fun x => ?_⟩
  have H := scalarCDFValue_time_modulus β α ha h1 hq.1 hq.2 le_rfl x
  rw [sub_self, Real.toNNReal_zero, scalarCDFValue_duration_zero β ha α.mono 1] at H
  have hs := (softAbs_bounds (by norm_num : (0:ℝ)<1) x).1
  have he : scalarSpinTerminal x = softAbs 1 x := by simp [scalarSpinTerminal, softAbs]
  rw [← he] at hs
  have hh := (abs_le.mp H).1
  dsimp only [C]
  linarith

lemma scalarCDF_curvature_not_identically_zero (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T q : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (hq : q ∈ Icc (0:ℝ) T) :
    ∃ x, compactCDFJet β α T 1 q x ≠ 0 := by
  by_contra hn
  push Not at hn
  have hG := ((compactCDFGradient_family β α ha h1 hβ hT0 hT1).regular q).smooth
  have hg0 : compactCDFGradient β α T q 0=0 := by
    have ht : Real.toNNReal (1-q) ≤ 1 := by
      rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
      linarith [hq.1]
    have H := SKConstants.parisiCDFGradient_odd β ha α.mono q _ ht 0
    simp only [neg_zero] at H
    unfold compactCDFGradient
    rw [cdfStripTime_eq hq]
    linarith
  have hdz (x : ℝ) : deriv (compactCDFGradient β α T q) x=0 := by
    simpa only [compactCDFJet, iteratedDeriv_one] using hn x
  have hg (x : ℝ) : compactCDFGradient β α T q x=0 :=
    (is_const_of_deriv_eq_zero (hG.differentiable (by simp)) hdz x 0).trans hg0
  have hremaining : Real.toNNReal (1-q) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    linarith [hq.1]
  have hV := scalarCDFValue_regular β ha α.mono q _ hremaining
  have hv (x : ℝ) : scalarCDFValue β α q (Real.toNNReal (1-q)) x=
      scalarCDFValue β α q (Real.toNNReal (1-q)) 0 := by
    apply is_const_of_deriv_eq_zero (hV.1.differentiable (by simp))
    intro y
    rw [(scalarCDFValue_hasDerivAt β ha α.mono q _ hremaining y).deriv]
    simpa only [compactCDFGradient, cdfStripTime_eq hq] using hg y
  obtain ⟨C,hC⟩ := scalarCDFValue_linear_lower_bound β α ha h1
    ⟨hq.1,hq.2.trans hT1.le⟩
  let x := scalarCDFValue β α q (Real.toNNReal (1-q)) 0+C+1
  have H := hC x
  rw [hv x] at H
  have hx := le_abs_self x
  dsimp only [x] at hx H
  linarith

lemma boundedSmoothFamily_pow {F : ℝ → ℝ → ℝ} (hF : BoundedSmoothFamily F) (k : ℕ) :
    BoundedSmoothFamily (fun t x => (F t x)^k) := by
  induction k with
  | zero =>
    simpa only [pow_zero] using BoundedSmoothFamily.timeConst
      (d := fun _ : ℝ => (1:ℝ)) measurable_const (C := 1) (by intro t; norm_num)
  | succ k ih => simpa only [pow_succ] using ih.mul hF

lemma scalarCDF_third_not_identically_zero (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T q : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (hq : q ∈ Icc (0:ℝ) T) :
    ∃ x, compactCDFJet β α T 2 q x ≠ 0 := by
  by_contra hn
  push Not at hn
  have hF := compactCDFGradient_family β α ha h1 hβ hT0 hT1
  have hH := ((hF.iteratedDeriv 1).regular q).smooth
  have hc (x : ℝ) : compactCDFJet β α T 1 q x=compactCDFJet β α T 1 q 0 := by
    apply is_const_of_deriv_eq_zero (hH.differentiable (by simp))
    intro y
    change deriv (compactCDFJet β α T 1 q) y=0
    rw [(compactCDFJet_hasDerivAt β α ha h1 hβ hT0 hT1 1 q y).deriv]
    exact hn y
  let c := compactCDFJet β α T 1 q 0
  have hremaining : Real.toNNReal (1-q) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    linarith [hq.1]
  have hg0 : compactCDFJet β α T 0 q 0=0 := by
    simp only [compactCDFJet, iteratedDeriv_zero, compactCDFGradient, cdfStripTime_eq hq]
    exact scalarCDFGradient_zero β ha α.mono q _ hremaining
  have hd (x : ℝ) : HasDerivAt (fun y => compactCDFJet β α T 0 q y-c*y) 0 x := by
    have H := (compactCDFJet_hasDerivAt β α ha h1 hβ hT0 hT1 0 q x).sub
      ((hasDerivAt_id x).const_mul c)
    change HasDerivAt (fun y => compactCDFJet β α T 0 q y-c*y)
      (compactCDFJet β α T 1 q x-c*1) x at H
    have hz : compactCDFJet β α T 1 q x-c*1=0 := by rw [hc x]; dsimp [c]; ring
    rw [hz] at H
    exact H
  have hg (x : ℝ) : compactCDFJet β α T 0 q x=c*x := by
    have H := is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt)
      (fun y => (hd y).deriv) x 0
    rw [hg0,mul_zero,sub_zero] at H
    linarith
  have hz : c=0 := by
    by_contra hc0
    have H := (scalarCDF_derivative_bounds β ha α.mono q _ hremaining (2/c)).1
    have he : scalarCDFGradient β α q (Real.toNNReal (1-q)) (2/c)=c*(2/c) := by
      simpa only [compactCDFJet, iteratedDeriv_zero, compactCDFGradient, cdfStripTime_eq hq] using hg (2/c)
    rw [he,mul_div_cancel₀ _ hc0] at H
    norm_num at H
  obtain ⟨x,hx⟩ := scalarCDF_curvature_not_identically_zero β α ha h1 hβ hT0 hT1 hq
  exact hx ((hc x).trans hz)

lemma compactCDFJet_even_moment_pos (W : BrownianSystem Ω) (β : ℝ)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (h1 : α 1 = 1) (hβ : β ≠ 0) {T q : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (hq0 : 0 < q)
    (n k : ℕ) (hk : 0 < k) (hne : ∃ x, compactCDFJet β α T n q x ≠ 0) :
    0 < ∫ w, (compactCDFJet β α T n q
      (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal (β^2*q)) w))^(2*k) ∂W.law := by
  let := W.isProbability
  let F := (compactCDFGradient_family β α ha h1 hβ hT0 hT1).iteratedDeriv n
  let b := finiteTemperatureCDFDrift β α ha h1
  let v := Real.toNNReal (β^2*q)
  have hv : 0 < (v:ℝ) := by
    rw [Real.coe_toNNReal _ (mul_nonneg (sq_nonneg β) hq0.le)]
    exact mul_pos (sq_pos_of_ne_zero hβ) hq0
  have hX := b.solution_measurable W v
  have hi := integrable_family_comp (P := W.law) (boundedSmoothFamily_pow F (2*k)) q hX
  apply integral_pos_of_interval_support
    (fun a c hac => SKConstants.ParisiFullSupport.BoundedLipschitzDrift.solution_interval_pos b W v hv hac)
    (((F.regular q).smooth.continuous).pow _)
    (fun x => by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) k) hi
  obtain ⟨x,hx⟩ := hne
  exact ⟨x,pow_ne_zero _ hx⟩

theorem actualCDF_curvature_quartic_pos (W : BrownianSystem Ω) (β : ℝ)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (h1 : α 1 = 1) (hβ : β ≠ 0) {T q : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (hq : q ∈ Icc (0:ℝ) T) (hq0 : 0 < q) :
    0 < ∫ w, (compactCDFJet β α T 1 q
      (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal (β^2*q)) w))^4 ∂W.law :=
  compactCDFJet_even_moment_pos W β α ha h1 hβ hT0 hT1 hq0 1 2 (by decide)
    (scalarCDF_curvature_not_identically_zero β α ha h1 hβ hT0 hT1 hq)

theorem actualCDF_third_square_pos (W : BrownianSystem Ω) (β : ℝ)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (h1 : α 1 = 1) (hβ : β ≠ 0) {T q : ℝ}
    (hT0 : 0 ≤ T) (hT1 : T < 1) (hq : q ∈ Icc (0:ℝ) T) (hq0 : 0 < q) :
    0 < ∫ w, (compactCDFJet β α T 2 q
      (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal (β^2*q)) w))^2 ∂W.law :=
  compactCDFJet_even_moment_pos W β α ha h1 hβ hT0 hT1 hq0 2 1 (by decide)
    (scalarCDF_third_not_identically_zero β α ha h1 hβ hT0 hT1 hq)

end SKConstants.ParisiFullSupport
