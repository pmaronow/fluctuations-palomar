module

public import SKConstants.ScalarDeterministicWeightedPaths
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants
set_option backward.isDefEq.respectTransparency false

lemma scalarStieltjes_discrete_parts (f X : ℝ → ℝ) (a : ℕ → ℝ) (N : ℕ) :
    (∑ i ∈ Finset.range N,f (a i)*(X (a (i+1))-X (a i))) =
      f (a N)*X (a N)-f (a 0)*X (a 0)-
        ∑ i ∈ Finset.range N,X (a (i+1))*(f (a (i+1))-f (a i)) := by
  have hterm (i : ℕ) : f (a i)*(X (a (i+1))-X (a i)) =
      (f (a (i+1))*X (a (i+1))-f (a i)*X (a i))-
        X (a (i+1))*(f (a (i+1))-f (a i)) := by ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib,Finset.sum_range_sub (fun i => f (a i)*X (a i)) N]

lemma scalarStieltjes_integral_const (f : StieltjesFunction ℝ) {a b : ℝ}
    (hab : a ≤ b) (c : ℝ) :
    (∫ _s in a..b,c ∂f.measure) = c*(f b-f a) := by
  rw [intervalIntegral.integral_of_le hab,setIntegral_const]
  simp only [Measure.real,f.measure_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr (f.mono hab)),
    smul_eq_mul]
  ring

lemma scalarStieltjes_interval_error_bound (f : StieltjesFunction ℝ) (X : ℝ → ℝ)
    (hX : Continuous X) {a b ε : ℝ} (hab : a ≤ b)
    (hε : ∀ s ∈ Icc a b,|X b-X s| ≤ ε) :
    |X b*(f b-f a)-(∫ s in a..b,X s ∂f.measure)| ≤ ε*(f b-f a) := by
  have hi : IntervalIntegrable X f.measure a b :=
    (hX.continuousOn.integrableOn_compact isCompact_uIcc).intervalIntegrable
  have he : X b*(f b-f a)-(∫ s in a..b,X s ∂f.measure) =
      ∫ s in a..b,X b-X s ∂f.measure := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi,
      scalarStieltjes_integral_const f hab]
  rw [he,intervalIntegral.integral_of_le hab]
  have H := norm_setIntegral_le_of_norm_le_const
    (μ := f.measure) (s := Ioc a b) (f := fun s => X b-X s)
    (by rw [f.measure_Ioc];exact ENNReal.ofReal_lt_top)
    (fun s hs => by simpa only [Real.norm_eq_abs] using hε s ⟨hs.1.le,hs.2⟩)
  simpa only [Real.norm_eq_abs,Measure.real,f.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (f.mono hab))] using H

lemma scalarStieltjes_sum_error_bound (f : StieltjesFunction ℝ) (X : ℝ → ℝ)
    (hX : Continuous X) (a : ℕ → ℝ) (N : ℕ) (ε : ℝ)
    (ha : ∀ i<N,a i ≤ a (i+1))
    (hε : ∀ i<N,∀ s∈Icc (a i) (a (i+1)),|X (a (i+1))-X s| ≤ ε) :
    |(∑ i∈Finset.range N,f (a i)*(X (a (i+1))-X (a i)))-
      (f (a N)*X (a N)-f (a 0)*X (a 0)-(∫ s in a 0..a N,X s ∂f.measure))| ≤
      ε*(f (a N)-f (a 0)) := by
  let E : ℕ → ℝ := fun i => X (a (i+1))*(f (a (i+1))-f (a i))-
    ∫ s in a i..a (i+1),X s ∂f.measure
  have he : (∑ i∈Finset.range N,f (a i)*(X (a (i+1))-X (a i)))-
      (f (a N)*X (a N)-f (a 0)*X (a 0)-(∫ s in a 0..a N,X s ∂f.measure)) =
      -(∑ i∈Finset.range N,E i) := by
    rw [scalarStieltjes_discrete_parts]
    have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := f.measure)
      (a := a) (n := N) (fun i hi =>
        (hX.continuousOn.integrableOn_compact isCompact_uIcc).intervalIntegrable)
    rw [← hsum]
    simp only [E,Finset.sum_sub_distrib]
    ring
  rw [he,abs_neg]
  calc
    _ ≤ ∑ i∈Finset.range N,|E i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i∈Finset.range N,ε*(f (a (i+1))-f (a i)) :=
      Finset.sum_le_sum (fun i hi => scalarStieltjes_interval_error_bound f X hX
        (ha i (Finset.mem_range.mp hi)) (hε i (Finset.mem_range.mp hi)))
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_range_sub (fun i => f (a i)) N]

theorem scalarStieltjes_left_sums_tendsto (f : StieltjesFunction ℝ) (X : ℝ → ℝ)
    (hX : Continuous X) (T : ℝ) (hT : 0 ≤ T)
    (a : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (δ : ℕ → ℝ)
    (ha0 : ∀ l,a l 0 = 0) (haN : ∀ l,a l (N l) = T)
    (ha : ∀ l i,i ≤ N l → a l i ∈ Icc 0 T)
    (hmono : ∀ l i,i<N l → a l i ≤ a l (i+1))
    (hmesh : ∀ l i,i<N l → a l (i+1)-a l i ≤ δ l)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun l => ∑ i∈Finset.range (N l),f (a l i)*(X (a l (i+1))-X (a l i)))
      atTop (𝓝 (f T*X T-f 0*X 0-(∫ s in (0 : ℝ)..T,X s ∂f.measure))) := by
  let C := f T-f 0
  have hC : 0 ≤ C := sub_nonneg.mpr (f.mono hT)
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  let η := ε/(C+1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hu : UniformContinuousOn X (Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hX.continuousOn
  obtain ⟨d,hd,hUC⟩ := Metric.uniformContinuousOn_iff.mp hu η hη
  obtain ⟨L,hL⟩ := eventually_atTop.mp (hδ.eventually (eventually_lt_nhds hd))
  refine ⟨L,fun l hl => ?_⟩
  have hBound := scalarStieltjes_sum_error_bound f X hX (a l) (N l) η (hmono l) (by
    intro i hi s hs
    have hiN : i+1 ≤ N l := hi
    have hb := ha l (i+1) hiN
    have hsT : s ∈ Icc 0 T := ⟨(ha l i hi.le).1.trans hs.1,hs.2.trans hb.2⟩
    have hDist : dist (a l (i+1)) s < d := by
      rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hs.2)]
      exact (sub_le_sub_left hs.1 _).trans_lt ((hmesh l i hi).trans_lt (hL l hl))
    exact (show |X (a l (i+1))-X s| < η by
      simpa only [Real.dist_eq] using hUC _ hb _ hsT hDist).le)
  rw [ha0 l,haN l] at hBound
  have hηC : η*C < ε := by
    dsimp only [η]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by linarith : 0 < C+1)).mpr
    nlinarith
  simpa only [Real.dist_eq] using hBound.trans_lt hηC

def scalarStieltjesMeshSum (f : StieltjesFunction ℝ) (T : ℝ≥0)
    (B : ScalarContinuousPath T) (a : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (l : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N l), f (a l i) *
    (IccExtend T.coe_nonneg B (a l (i+1))-IccExtend T.coe_nonneg B (a l i))

theorem scalarStieltjesMeshSum_tendsto_weightedPath (f : StieltjesFunction ℝ)
    (hf : Continuous f) (T : ℝ≥0) (B : ScalarContinuousPath T)
    (a : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (δ : ℕ → ℝ)
    (ha0 : ∀ l,a l 0 = 0) (haN : ∀ l,a l (N l) = T)
    (ha : ∀ l i,i ≤ N l → a l i ∈ Icc 0 (T : ℝ))
    (hmono : ∀ l i,i<N l → a l i ≤ a l (i+1))
    (hmesh : ∀ l i,i<N l → a l (i+1)-a l i ≤ δ l)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (scalarStieltjesMeshSum f T B a N) atTop
      (𝓝 (scalarStieltjesWeightedPath f hf T B ⟨T,T.coe_nonneg,le_rfl⟩-
        f 0*B ⟨0,le_rfl,T.coe_nonneg⟩)) := by
  have H := scalarStieltjes_left_sums_tendsto f (IccExtend T.coe_nonneg B)
    B.continuous.Icc_extend' T T.coe_nonneg a N δ ha0 haN ha hmono hmesh hδ
  convert H using 1
  · rfl
  · change 𝓝 (f T*B _-(∫ s in (0 : ℝ)..T,IccExtend T.coe_nonneg B s ∂f.measure)-
      f 0*B _) = _
    simp only [IccExtend,Function.comp_apply,projIcc_of_mem _ ⟨T.coe_nonneg,le_rfl⟩,
      projIcc_of_mem _ ⟨le_rfl,T.coe_nonneg⟩]
    congr 1
    ring

def scalarStieltjesDyadicTime (T : ℝ≥0) (l i : ℕ) : ℝ :=
  (T : ℝ)*(i : ℝ)/(2^l : ℝ)

def scalarStieltjesDyadicSum (f : StieltjesFunction ℝ) (T : ℝ≥0)
    (B : ScalarContinuousPath T) (l : ℕ) : ℝ :=
  scalarStieltjesMeshSum f T B (scalarStieltjesDyadicTime T) (fun l => 2^l) l

lemma scalarStieltjesDyadicTime_zero (T : ℝ≥0) (l : ℕ) :
    scalarStieltjesDyadicTime T l 0 = 0 := by simp [scalarStieltjesDyadicTime]

lemma scalarStieltjesDyadicTime_end (T : ℝ≥0) (l : ℕ) :
    scalarStieltjesDyadicTime T l (2^l) = T := by
  simp [scalarStieltjesDyadicTime]

lemma scalarStieltjesDyadicTime_mem (T : ℝ≥0) (l i : ℕ) (hi : i ≤ 2^l) :
    scalarStieltjesDyadicTime T l i ∈ Icc 0 (T : ℝ) := by
  have hP : (0 : ℝ)<2^l := by positivity
  constructor
  · dsimp only [scalarStieltjesDyadicTime]
    positivity
  · dsimp only [scalarStieltjesDyadicTime]
    apply (div_le_iff₀ hP).mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hi) T.coe_nonneg

lemma scalarStieltjesDyadicTime_step (T : ℝ≥0) (l i : ℕ) :
    scalarStieltjesDyadicTime T l (i+1)-scalarStieltjesDyadicTime T l i =
      (T : ℝ)/2^l := by
  simp only [scalarStieltjesDyadicTime,Nat.cast_add,Nat.cast_one]
  ring

lemma scalarStieltjesDyadicTime_mono (T : ℝ≥0) (l i : ℕ) :
    scalarStieltjesDyadicTime T l i ≤ scalarStieltjesDyadicTime T l (i+1) := by
  have H := scalarStieltjesDyadicTime_step T l i
  have : (0 : ℝ) ≤ (T : ℝ)/2^l := by positivity
  linarith

lemma scalarStieltjesDyadic_width_tendsto (T : ℝ≥0) :
    Tendsto (fun l : ℕ => (T : ℝ)/2^l) atTop (𝓝 0) := by
  have H := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1 : ℝ)/2 < 1)).const_mul (T : ℝ)
  simpa only [div_pow,one_pow,mul_zero,mul_one_div] using H

theorem scalarStieltjesDyadicSum_tendsto (f : StieltjesFunction ℝ) (hf : Continuous f)
    (T : ℝ≥0) (B : ScalarContinuousPath T) :
    Tendsto (scalarStieltjesDyadicSum f T B) atTop
      (𝓝 (scalarStieltjesWeightedPath f hf T B ⟨T,T.coe_nonneg,le_rfl⟩-
        f 0*B ⟨0,le_rfl,T.coe_nonneg⟩)) := by
  exact scalarStieltjesMeshSum_tendsto_weightedPath f hf T B
    (scalarStieltjesDyadicTime T) (fun l => 2^l) (fun l => (T : ℝ)/2^l)
    (scalarStieltjesDyadicTime_zero T) (scalarStieltjesDyadicTime_end T)
    (scalarStieltjesDyadicTime_mem T)
    (fun l i _ => scalarStieltjesDyadicTime_mono T l i)
    (fun l i _ => (scalarStieltjesDyadicTime_step T l i).le)
    (scalarStieltjesDyadic_width_tendsto T)

theorem continuous_scalarStieltjesMeshSum (f : StieltjesFunction ℝ) (T : ℝ≥0)
    (a : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (l : ℕ) :
    Continuous (fun B : ScalarContinuousPath T => scalarStieltjesMeshSum f T B a N l) := by
  unfold scalarStieltjesMeshSum IccExtend
  fun_prop

def scalarStieltjesDyadicSumAt (f : StieltjesFunction ℝ) (T : ℝ≥0)
    (B : ScalarContinuousPath T) (u : ℝ≥0) (l : ℕ) : ℝ :=
  scalarStieltjesMeshSum f T B (scalarStieltjesDyadicTime u) (fun l => 2^l) l

theorem scalarStieltjesDyadicSumAt_tendsto (f : StieltjesFunction ℝ)
    (hf : Continuous f) (T u : ℝ≥0) (hu : u ≤ T) (B : ScalarContinuousPath T) :
    Tendsto (scalarStieltjesDyadicSumAt f T B u) atTop
      (𝓝 (scalarStieltjesWeightedPath f hf T B ⟨u,u.coe_nonneg,hu⟩-
        f 0*B ⟨0,le_rfl,T.coe_nonneg⟩)) := by
  have H := scalarStieltjes_left_sums_tendsto f (IccExtend T.coe_nonneg B)
    B.continuous.Icc_extend' u u.coe_nonneg
    (scalarStieltjesDyadicTime u) (fun l => 2^l) (fun l => (u : ℝ)/2^l)
    (scalarStieltjesDyadicTime_zero u) (scalarStieltjesDyadicTime_end u)
    (scalarStieltjesDyadicTime_mem u)
    (fun l i _ => scalarStieltjesDyadicTime_mono u l i)
    (fun l i _ => (scalarStieltjesDyadicTime_step u l i).le)
    (scalarStieltjesDyadic_width_tendsto u)
  convert H using 1
  · rfl
  · change 𝓝 (f u*B _-(∫ s in (0 : ℝ)..u,IccExtend T.coe_nonneg B s ∂f.measure)-
      f 0*B _) = _
    have hp : projIcc (0 : ℝ) (T : ℝ) T.coe_nonneg (u : ℝ) =
        ⟨u,u.coe_nonneg,hu⟩ := projIcc_of_mem _ ⟨u.coe_nonneg,hu⟩
    simp only [IccExtend,Function.comp_apply,hp,
      projIcc_of_mem _ ⟨le_rfl,T.coe_nonneg⟩]
    congr 1
    ring

theorem scalarStieltjesDyadicSumAt_tendsto_of_zero (f : StieltjesFunction ℝ)
    (hf : Continuous f) (T u : ℝ≥0) (hu : u ≤ T) (B : ScalarContinuousPath T)
    (hB0 : B ⟨0,le_rfl,T.coe_nonneg⟩ = 0) :
    Tendsto (scalarStieltjesDyadicSumAt f T B u) atTop
      (𝓝 (scalarStieltjesWeightedPath f hf T B ⟨u,u.coe_nonneg,hu⟩)) := by
  simpa only [hB0,mul_zero,sub_zero] using
    scalarStieltjesDyadicSumAt_tendsto f hf T u hu B

theorem scalarTwoDriverWeightedPath_dyadic_tendsto (f g : StieltjesFunction ℝ)
    (hf : Continuous f) (hg : Continuous g) (T u : ℝ≥0) (hu : u ≤ T)
    (B D : ScalarContinuousPath T)
    (hB0 : B ⟨0,le_rfl,T.coe_nonneg⟩ = 0)
    (hD0 : D ⟨0,le_rfl,T.coe_nonneg⟩ = 0) :
    Tendsto (fun l => -scalarStieltjesDyadicSumAt f T B u l+
      scalarStieltjesDyadicSumAt g T D u l) atTop
      (𝓝 (scalarTwoDriverWeightedPath f g hf hg T (B,D) ⟨u,u.coe_nonneg,hu⟩)) := by
  exact (scalarStieltjesDyadicSumAt_tendsto_of_zero f hf T u hu B hB0).neg.add
    (scalarStieltjesDyadicSumAt_tendsto_of_zero g hg T u hu D hD0)

theorem scalarStieltjes_interval_left_sums_tendsto (f : StieltjesFunction ℝ) (X : ℝ → ℝ)
    (hX : Continuous X) (S T : ℝ) (hST : S ≤ T)
    (a : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (δ : ℕ → ℝ)
    (ha0 : ∀ l,a l 0 = S) (haN : ∀ l,a l (N l) = T)
    (ha : ∀ l i,i ≤ N l → a l i ∈ Icc S T)
    (hmono : ∀ l i,i<N l → a l i ≤ a l (i+1))
    (hmesh : ∀ l i,i<N l → a l (i+1)-a l i ≤ δ l)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun l => ∑ i∈Finset.range (N l),f (a l i)*(X (a l (i+1))-X (a l i)))
      atTop (𝓝 (f T*X T-f S*X S-(∫ s in S..T,X s ∂f.measure))) := by
  let C := f T-f S
  have hC : 0 ≤ C := sub_nonneg.mpr (f.mono hST)
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  let η := ε/(C+1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hu : UniformContinuousOn X (Icc S T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hX.continuousOn
  obtain ⟨d,hd,hUC⟩ := Metric.uniformContinuousOn_iff.mp hu η hη
  obtain ⟨L,hL⟩ := eventually_atTop.mp (hδ.eventually (eventually_lt_nhds hd))
  refine ⟨L,fun l hl => ?_⟩
  have hBound := scalarStieltjes_sum_error_bound f X hX (a l) (N l) η (hmono l) (by
    intro i hi s hs
    have hiN : i+1 ≤ N l := hi
    have hb := ha l (i+1) hiN
    have hsT : s ∈ Icc S T := ⟨(ha l i hi.le).1.trans hs.1,hs.2.trans hb.2⟩
    have hDist : dist (a l (i+1)) s < d := by
      rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hs.2)]
      exact (sub_le_sub_left hs.1 _).trans_lt ((hmesh l i hi).trans_lt (hL l hl))
    exact (show |X (a l (i+1))-X s| < η by
      simpa only [Real.dist_eq] using hUC _ hb _ hsT hDist).le)
  rw [ha0 l,haN l] at hBound
  have hηC : η*C < ε := by
    dsimp only [η]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by linarith : 0 < C+1)).mpr
    nlinarith
  simpa only [Real.dist_eq] using hBound.trans_lt hηC

def scalarStieltjesDyadicIntervalTime (S T : ℝ≥0) (l i : ℕ) : ℝ :=
  (S : ℝ)+scalarStieltjesDyadicTime (T-S) l i

def scalarStieltjesDyadicIntervalSum (f : StieltjesFunction ℝ) (H : ℝ≥0)
    (B : ScalarContinuousPath H) (S T : ℝ≥0) (l : ℕ) : ℝ :=
  scalarStieltjesMeshSum f H B (scalarStieltjesDyadicIntervalTime S T) (fun l => 2^l) l

theorem scalarStieltjesDyadicIntervalSum_tendsto (f : StieltjesFunction ℝ)
    (hf : Continuous f) (H S T : ℝ≥0) (hST : S ≤ T) (hTH : T ≤ H)
    (B : ScalarContinuousPath H) :
    Tendsto (scalarStieltjesDyadicIntervalSum f H B S T) atTop
      (𝓝 (scalarStieltjesWeightedPath f hf H B ⟨T,T.coe_nonneg,hTH⟩-
        scalarStieltjesWeightedPath f hf H B ⟨S,S.coe_nonneg,hST.trans hTH⟩)) := by
  have hTS : (S : ℝ)+(T-S : ℝ≥0) = T := by
    exact_mod_cast add_tsub_cancel_of_le hST
  have Hlim := scalarStieltjes_interval_left_sums_tendsto f (IccExtend H.coe_nonneg B)
    B.continuous.Icc_extend' S T (by exact_mod_cast hST)
    (scalarStieltjesDyadicIntervalTime S T) (fun l => 2^l)
    (fun l => (T-S : ℝ≥0)/2^l)
    (fun l => by simp [scalarStieltjesDyadicIntervalTime,scalarStieltjesDyadicTime_zero])
    (fun l => by simpa only [scalarStieltjesDyadicIntervalTime,scalarStieltjesDyadicTime_end] using hTS)
    (by
      intro l i hi
      have h := scalarStieltjesDyadicTime_mem (T-S) l i hi
      dsimp only [scalarStieltjesDyadicIntervalTime]
      constructor <;> linarith [h.1,h.2])
    (fun l i _ => by
      dsimp only [scalarStieltjesDyadicIntervalTime]
      linarith [scalarStieltjesDyadicTime_mono (T-S) l i])
    (fun l i _ => by
      dsimp only [scalarStieltjesDyadicIntervalTime]
      linarith [scalarStieltjesDyadicTime_step (T-S) l i])
    (scalarStieltjesDyadic_width_tendsto (T-S))
  convert Hlim using 1
  · rfl
  · change 𝓝 ((f T*B _-(∫ s in (0 : ℝ)..T,IccExtend H.coe_nonneg B s ∂f.measure))-
      (f S*B _-(∫ s in (0 : ℝ)..S,IccExtend H.coe_nonneg B s ∂f.measure))) = _
    have hpT : projIcc (0 : ℝ) (H : ℝ) H.coe_nonneg (T : ℝ) =
        ⟨T,T.coe_nonneg,hTH⟩ := projIcc_of_mem _ ⟨T.coe_nonneg,hTH⟩
    have hpS : projIcc (0 : ℝ) (H : ℝ) H.coe_nonneg (S : ℝ) =
        ⟨S,S.coe_nonneg,hST.trans hTH⟩ := projIcc_of_mem _ ⟨S.coe_nonneg,hST.trans hTH⟩
    have hi (a b : ℝ) : IntervalIntegrable (IccExtend H.coe_nonneg B) f.measure a b :=
      (B.continuous.Icc_extend'.continuousOn.integrableOn_compact isCompact_uIcc).intervalIntegrable
    have hAdd := intervalIntegral.integral_add_adjacent_intervals (hi 0 S) (hi S T)
    simp only [IccExtend,Function.comp_apply,hpT,hpS]
    congr 1
    dsimp only [IccExtend,Function.comp_apply] at hAdd
    linarith

end SKConstants
