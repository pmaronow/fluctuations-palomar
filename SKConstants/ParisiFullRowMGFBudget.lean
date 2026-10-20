module
public import SKConstants.ParisiFullNormalizedRows

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators InnerProductSpace
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK ParisiFullSupport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]
local instance ParisiFullRowMGFBudget_localInstance1 (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

def actualParisiJoinedGrid (β : ℝ) (t : ℕ → ℝ≥0) (n : ℕ) (q : ℕ → ℝ≥0) (k : ℕ) : ℝ≥0 :=
  if k ≤ n then t k else parisiEquilibriumPhysicalEndpoint β+q (k-n)

lemma actualParisiJoinedGrid_pre (β : ℝ) (t : ℕ → ℝ≥0) (n : ℕ) (q : ℕ → ℝ≥0)
    (k : ℕ) (hk : k ≤ n) : actualParisiJoinedGrid β t n q k=t k := by
  simp only [actualParisiJoinedGrid,hk,ite_true]

lemma actualParisiJoinedGrid_post (β : ℝ) (t : ℕ → ℝ≥0) (n : ℕ) (q : ℕ → ℝ≥0)
    (htn : t n=parisiEquilibriumPhysicalEndpoint β) (hq0 : q 0=0) (k : ℕ) :
    actualParisiJoinedGrid β t n q (n+k)=parisiEquilibriumPhysicalEndpoint β+q k := by
  by_cases hk : k=0
  · subst k
    simp only [add_zero,actualParisiJoinedGrid_pre β t n q n le_rfl,htn,hq0]
  · simp only [actualParisiJoinedGrid,show ¬n+k≤n by omega,ite_false,Nat.add_sub_cancel_left]

lemma actualParisiJoinedGrid_monotone (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (n : ℕ) (htn : t n=parisiEquilibriumPhysicalEndpoint β) (q : ℕ → ℝ≥0) (hq : Monotone q) :
    Monotone (actualParisiJoinedGrid β t n q) := by
  intro i j hij
  by_cases hi : i ≤ n
  · rw [actualParisiJoinedGrid_pre β t n q i hi]
    by_cases hj : j ≤ n
    · rw [actualParisiJoinedGrid_pre β t n q j hj]
      exact ht hij
    · rw [actualParisiJoinedGrid,ite_eq_right hj]
      exact (ht hi).trans (by rw [htn]; exact le_add_of_nonneg_right bot_le)
  · have hj : ¬j ≤ n := by omega
    simp only [actualParisiJoinedGrid,hi,hj,ite_false]
    exact add_le_add le_rfl (hq (Nat.sub_le_sub_right hij n))

lemma actualParisiJoinedGrid_strictMono (β : ℝ) (t : ℕ → ℝ≥0) (ht : StrictMono t)
    (n : ℕ) (htn : t n=parisiEquilibriumPhysicalEndpoint β) (q : ℕ → ℝ≥0)
    (hq : StrictMono q) (hq0 : q 0=0) : StrictMono (actualParisiJoinedGrid β t n q) := by
  intro i j hij
  by_cases hi : i ≤ n
  · rw [actualParisiJoinedGrid_pre β t n q i hi]
    by_cases hj : j ≤ n
    · rw [actualParisiJoinedGrid_pre β t n q j hj]
      exact ht hij
    · rw [actualParisiJoinedGrid,ite_eq_right hj]
      have hqi : 0 < q (j-n) := by
        rw [←hq0]
        exact hq (by omega)
      exact (ht.monotone hi).trans_lt (by rw [htn]; exact lt_add_of_pos_right _ hqi)
  · have hj : ¬j ≤ n := by omega
    simp only [actualParisiJoinedGrid,hi,hj,ite_false]
    exact add_lt_add_of_le_of_lt le_rfl (hq (show i-n<j-n by omega))

theorem actualParisiJoinedPosteriorForm_hasSubgaussianMGF
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (n : ℕ) (htn : t n=parisiEquilibriumPhysicalEndpoint β) (q : ℕ → ℝ≥0)
    (hq : Monotone q) (hq0 : q 0=0) (c : ℕ → ℝ) (m : ℕ) :
    HasSubgaussianMGF (fun w => ∑ i ∈ Finset.range (n+m),c i*
      actualParisiMagnetizationIncrement W β (actualParisiJoinedGrid β t n q i)
        (actualParisiJoinedGrid β t n q (i+1)) w)
      (∑ i ∈ Finset.range (n+m),‖c i‖₊^2*
        (actualParisiJoinedGrid β t n q (i+1)-actualParisiJoinedGrid β t n q i)) W.law := by
  let d := fun j => c (n+j)
  have H := actualParisiFullWeightedForm_hasSubgaussianMGF W β hβ t ht c n htn q hq d m
  have he (w : Ω) : (∑ i ∈ Finset.range (n+m),c i*
      actualParisiMagnetizationIncrement W β (actualParisiJoinedGrid β t n q i)
        (actualParisiJoinedGrid β t n q (i+1)) w)=actualParisiFullWeightedForm W β t c n q d m w := by
    rw [Finset.sum_range_add]
    apply congrArg₂ (fun x y : ℝ => x+y)
    · apply Finset.sum_congr rfl
      intro i hi
      have hi' : i<n := Finset.mem_range.mp hi
      simp only [actualParisiJoinedGrid_pre β t n q i (by omega),
        actualParisiJoinedGrid_pre β t n q (i+1) (by omega),actualParisiMagnetizationIncrement,
        actualParisiMagnetizationObservable,actualParisiFullWeightedForm]
    · apply Finset.sum_congr rfl
      intro j hj
      simp only [Nat.add_comm j n,show n+j+1=n+(j+1) by omega,
        actualParisiJoinedGrid_post β t n q htn hq0,actualParisiMagnetizationIncrement,
        actualParisiMagnetizationObservable,actualParisiFullWeightedForm,d,NNReal.coe_add]
  have hproxy : (∑ i ∈ Finset.range (n+m),‖c i‖₊^2*
        (actualParisiJoinedGrid β t n q (i+1)-actualParisiJoinedGrid β t n q i))=
      preCDFWeightedProxy t c n+preCDFWeightedProxy q d m := by
    rw [Finset.sum_range_add]
    simp only [preCDFWeightedProxy]
    apply congrArg₂ (fun x y : ℝ≥0 => x+y)
    · apply Finset.sum_congr rfl
      intro i hi
      have hi' : i<n := Finset.mem_range.mp hi
      simp only [preCDFWeightedProxy,actualParisiJoinedGrid_pre β t n q i (by omega),
        actualParisiJoinedGrid_pre β t n q (i+1) (by omega)]
      apply NNReal.eq
      simp only [NNReal.coe_mul,NNReal.coe_pow,coe_nnnorm,Real.norm_eq_abs,sq_abs,NNReal.coe_mk]
    · apply Finset.sum_congr rfl
      intro j hj
      simp only [preCDFWeightedProxy,Nat.add_comm j n,show n+j+1=n+(j+1) by omega,
        actualParisiJoinedGrid_post β t n q htn hq0,add_tsub_add_eq_tsub_left,d]
      apply NNReal.eq
      simp only [NNReal.coe_mul,NNReal.coe_pow,coe_nnnorm,Real.norm_eq_abs,sq_abs,NNReal.coe_mk]
  rw [hproxy]
  exact H.congr (ae_of_all _ (fun w => (he w).symm))

def actualParisiPosteriorRowMGFProxy (W : BrownianSystem Ω) (β : ℝ) (H : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal (1/actualParisiContinuationR W β ((H-parisiEquilibriumPhysicalEndpoint β:ℝ≥0):ℝ))

lemma actualParisiPosteriorRowMGFProxy_pos (W : BrownianSystem Ω) (β : ℝ) (H : ℝ≥0) :
    0 < actualParisiPosteriorRowMGFProxy W β H := by
  exact Real.toNNReal_pos.mpr (one_div_pos.mpr (actualParisiContinuationR_pos W β _))

lemma actualParisiPosteriorRowMGFProxy_coe (W : BrownianSystem Ω) (β : ℝ) (H : ℝ≥0) :
    (actualParisiPosteriorRowMGFProxy W β H:ℝ)=
      1/actualParisiContinuationR W β ((H-parisiEquilibriumPhysicalEndpoint β:ℝ≥0):ℝ) :=
  Real.coe_toNNReal _ (one_div_pos.mpr (actualParisiContinuationR_pos W β _)).le

lemma actualParisiPosteriorIntervalScale_duration_budget
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (S T H : ℝ≥0) (hST : S < T) (hTH : T ≤ H) :
    T-S ≤ actualParisiPosteriorRowMGFProxy W β H*(actualParisiPosteriorIntervalScale W β S T)^2 := by
  have hr := actualParisiContinuationR_pos W β ((H-parisiEquilibriumPhysicalEndpoint β:ℝ≥0):ℝ)
  have HB := actualParisiFullOverlap_drop_ge W β hβ S T H hST.le hTH
  apply NNReal.coe_le_coe.mp
  rw [NNReal.coe_sub hST.le,NNReal.coe_mul,NNReal.coe_pow,
    actualParisiPosteriorIntervalScale_sq W β hβ S T hST]
  rw [actualParisiPosteriorRowMGFProxy_coe,one_div,inv_mul_eq_div]
  exact (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using HB)

theorem actualParisiNormalizedJoinedPosteriorRow_hasSubgaussianMGF
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : StrictMono t)
    (n : ℕ) (htn : t n=parisiEquilibriumPhysicalEndpoint β) (q : ℕ → ℝ≥0)
    (hq : StrictMono q) (hq0 : q 0=0) (m : ℕ) (a : EuclideanSpace ℝ (Fin (n+m))) :
    HasSubgaussianMGF
      (fun w => ⟪actualParisiNormalizedPosteriorRow W β (actualParisiJoinedGrid β t n q) (n+m) w,a⟫_ℝ)
      (actualParisiPosteriorRowMGFProxy W β (parisiEquilibriumPhysicalEndpoint β+q m)*‖a‖₊^2) W.law := by
  let u := actualParisiJoinedGrid β t n q
  let K := actualParisiPosteriorRowMGFProxy W β (parisiEquilibriumPhysicalEndpoint β+q m)
  let s : Fin (n+m) → ℝ≥0 := fun i => actualParisiPosteriorIntervalScale W β (u i) (u (i+1))
  let c : ℕ → ℝ := fun k => if hk : k<n+m then a ⟨k,hk⟩/(s ⟨k,hk⟩:ℝ) else 0
  have hu : StrictMono u := actualParisiJoinedGrid_strictMono β t ht n htn q hq hq0
  have hend : u (n+m)=parisiEquilibriumPhysicalEndpoint β+q m :=
    actualParisiJoinedGrid_post β t n q htn hq0 m
  have hs (i : Fin (n+m)) : 0 < s i := actualParisiPosteriorIntervalScale_pos W β hβ _ _
    (hu (Nat.lt_succ_self _))
  have hb (i : Fin (n+m)) : u (i+1)-u i ≤ K*(s i)^2 := by
    apply actualParisiPosteriorIntervalScale_duration_budget W β hβ _ _ _ (hu (Nat.lt_succ_self _))
    rw [←hend]
    exact hu.monotone (by omega)
  have he (w : Ω) : ⟪actualParisiNormalizedPosteriorRow W β u (n+m) w,a⟫_ℝ=
      ∑ i ∈ Finset.range (n+m),c i*actualParisiMagnetizationIncrement W β (u i) (u (i+1)) w := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct,Pi.star_apply,star_trivial,actualParisiNormalizedPosteriorRow,WithLp.ofLp_toLp]
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [c,Finset.mem_range.mp hk,dite_true]
    ring
  have hp : (∑ i ∈ Finset.range (n+m),‖c i‖₊^2*(u (i+1)-u i)) ≤ K*‖a‖₊^2 := by
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_sum,NNReal.coe_mul,NNReal.coe_pow,coe_nnnorm,EuclideanSpace.real_norm_sq_eq]
    rw [Finset.mul_sum,Finset.sum_fin_eq_sum_range]
    apply Finset.sum_le_sum
    intro k hk
    have hk' := Finset.mem_range.mp hk
    let i : Fin (n+m) := ⟨k,hk'⟩
    have hsi : (s i:ℝ)≠0 := (NNReal.coe_pos.mpr (hs i)).ne'
    have HI := NNReal.coe_le_coe.mpr (hb i)
    simp only [NNReal.coe_mul,NNReal.coe_pow] at HI
    simp only [c,hk',dite_true,Real.norm_eq_abs,sq_abs]
    change (a i/(s i:ℝ))^2*((u (i+1)-u i:ℝ≥0):ℝ) ≤ (K:ℝ)*(a i)^2
    calc
      _ ≤ (a i/(s i:ℝ))^2*((K:ℝ)*(s i:ℝ)^2) :=
        mul_le_mul_of_nonneg_left HI (sq_nonneg _)
      _ = _ := by field_simp
  have H := actualParisiJoinedPosteriorForm_hasSubgaussianMGF W β hβ t ht.monotone n htn q hq.monotone hq0 c m
  have H' := Concentration.hasSubgaussianMGF_of_proxy_le H hp
  exact H'.congr (ae_of_all _ (fun w => (he w).symm))

theorem actualParisiNormalizedJoinedPosteriorRow_unit_hasSubgaussianMGF
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : StrictMono t)
    (n : ℕ) (htn : t n=parisiEquilibriumPhysicalEndpoint β) (q : ℕ → ℝ≥0)
    (hq : StrictMono q) (hq0 : q 0=0) (m : ℕ) (a : EuclideanSpace ℝ (Fin (n+m))) (ha : ‖a‖ ≤ 1) :
    HasSubgaussianMGF
      (fun w => ⟪actualParisiNormalizedPosteriorRow W β (actualParisiJoinedGrid β t n q) (n+m) w,a⟫_ℝ)
      (actualParisiPosteriorRowMGFProxy W β (parisiEquilibriumPhysicalEndpoint β+q m)) W.law := by
  apply Concentration.hasSubgaussianMGF_of_proxy_le
    (actualParisiNormalizedJoinedPosteriorRow_hasSubgaussianMGF W β hβ t ht n htn q hq hq0 m a)
  apply mul_le_of_le_one_right (by positivity)
  exact pow_le_one₀ (by positivity) (show ‖a‖₊ ≤ 1 from ha)

lemma actualParisiPosteriorRowMGFProxy_one_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (H : ℝ≥0) :
    1 ≤ actualParisiPosteriorRowMGFProxy W β H := by
  apply NNReal.coe_le_coe.mp
  rw [NNReal.coe_one,actualParisiPosteriorRowMGFProxy_coe]
  have hr := actualParisiContinuationR_pos W β ((H-parisiEquilibriumPhysicalEndpoint β:ℝ≥0):ℝ)
  apply (le_div_iff₀ hr).mpr
  simp only [one_mul]
  have hb : 0 < β^2 := sq_pos_of_pos (zero_lt_one.trans hβ)
  have hb1 : 1 ≤ β^2 := by nlinarith
  exact (actualParisiContinuationR_le_inverse_beta_sq W β hβ _).trans
    ((div_le_iff₀ hb).mpr (by simpa only [one_mul] using hb1))

theorem actualParisiPosteriorRowMGFProxy_global_bound
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ,0 < C ∧ ∀ H : ℝ≥0,
      (actualParisiPosteriorRowMGFProxy W β H:ℝ) ≤ C*Real.exp ((H:ℝ)/2)*Real.sqrt (1+(H:ℝ)) := by
  obtain ⟨c,hc,hlower⟩ := actualParisiContinuationR_global_lower W β hβ
  refine ⟨1/c,one_div_pos.mpr hc,?_⟩
  intro H
  let v : ℝ := ((H-parisiEquilibriumPhysicalEndpoint β:ℝ≥0):ℝ)
  have hv : 0 ≤ v := NNReal.coe_nonneg _
  have hvH : v ≤ (H:ℝ) := NNReal.coe_le_coe.mpr tsub_le_self
  have hs : 0 < Real.sqrt (1+v) := Real.sqrt_pos.mpr (by linarith)
  have hr := actualParisiContinuationR_pos W β v
  have he : (1/c*Real.exp (v/2)*Real.sqrt (1+v))*(c*(Real.exp (-v/2)/Real.sqrt (1+v)))=1 := by
    field_simp
    rw [←Real.exp_add]
    simp only [add_neg_cancel,Real.exp_zero,mul_one]
  have HB := mul_le_mul_of_nonneg_left (hlower v hv)
    (show 0 ≤ 1/c*Real.exp (v/2)*Real.sqrt (1+v) by positivity)
  rw [he] at HB
  rw [actualParisiPosteriorRowMGFProxy_coe]
  change 1/actualParisiContinuationR W β v ≤ _
  calc
    _ ≤ 1/c*Real.exp (v/2)*Real.sqrt (1+v) := (div_le_iff₀ hr).mpr HB
    _ ≤ _ := by gcongr

end SKConstants
