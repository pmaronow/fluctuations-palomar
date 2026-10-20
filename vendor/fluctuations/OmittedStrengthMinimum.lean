module

public import OmittedStrengthLogDerivative
public import OmittedConstrainedForwardGeometry
public import WallEnvelope

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal
section
variable {r0 u0 c : ℝ} {k M : ℝ → ℝ}
variable (hr0 : 0≤r0) (hr : r0≤1) (hu : u0∈Icc (0:ℝ) 1)
variable (hc : 0<c) (hk : ContinuousOn k (Icc r0 1))
variable (hkc : ∀ r∈Icc r0 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem omittedSweepQuantile_monotone (α : inverseIntegralConstraints r0 u0 k M) :
    Monotone (omittedSweepQuantile hr hu hc hk hkc hm hM α) := by
  apply Monotone.IccExtend hu.2
  intro u v huv
  exact (inverseConstraintOrderIso hr hc hk hkc hm hM α).symm.monotone huv

theorem omittedSweepQuantile_continuous (α : inverseIntegralConstraints r0 u0 k M) :
    Continuous (omittedSweepQuantile hr hu hc hk hkc hm hM α) :=
  (omittedSweepQuantile_lipschitz hr hu hc hk hkc hm hM α).continuous

theorem omittedStrengthCoefficient_eq_original (d lam : ℝ)
    (α : inverseIntegralConstraints r0 u0 k M) :
    omittedStrengthCoefficient d u0 (omittedSweepQuantile hr hu hc hk hkc hm hM α) lam=
      omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM
        (laplaceComparisonStrength d lam) (laplaceComparisonStrength_contDiff d lam).continuous α) := by
  ext u
  by_cases hu' : u0≤u <;> simp [omittedStrengthCoefficient,omittedSweepQuantile,
    omittedExtension,IccExtend,constrainedCoefficient,constrainedQuantileMap,hu',Function.comp_def]

def omittedComparisonSweepObjective (n : ℕ) (b h : ℝ → ℝ) (d lam : ℝ)
    (α : inverseIntegralConstraints r0 u0 k M) : ℝ :=
  omittedStrengthSweepObjective n b h d u0 (omittedSweepQuantile hr hu hc hk hkc hm hM α) lam

theorem omittedComparisonSweepObjective_eq_inverse (n : ℕ) (b h : ℝ → ℝ) (d lam : ℝ)
    (α : inverseIntegralConstraints r0 u0 k M) :
    omittedComparisonSweepObjective hr hu hc hk hkc hm hM n b h d lam α=
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM (laplaceComparisonStrength d lam)
        (laplaceComparisonStrength_contDiff d lam).continuous n b h 0 α := by
  rw [inverseCompensatedPressure_eq]
  unfold omittedComparisonSweepObjective omittedStrengthSweepObjective pathCompensatedPressure
  rw [←omittedStrengthCoefficient_eq_original hr hu hc hk hkc hm hM d lam α]
  rfl

include hr0
theorem omittedComparisonSweep_clocks_admissible (b h : ℝ → ℝ) {d lam : ℝ}
    (hd : d≠0) (hlam : 0≤lam) (hlcut : lam≤b u0)
    (hcross : ∀u∈Ico (0:ℝ) u0,b u+lam≤b u0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hb0 : 0≤b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0)
    (α : inverseIntegralConstraints r0 u0 k M) :
    let e := omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM
      (laplaceComparisonStrength d lam) (laplaceComparisonStrength_contDiff d lam).continuous α)
    let q := omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM
      (fun r=>laplaceComparisonStrength d lam r*r)
      ((laplaceComparisonStrength_contDiff d lam).continuous.mul continuous_id) α)
    MonotoneOn (fun u=>b u-e u) (Icc (0:ℝ) 1) ∧
      MonotoneOn (fun u=>h u+q u) (Icc (0:ℝ) 1) ∧
      0≤b 0-e 0 ∧ 0≤h 0+q 0 := by
  dsimp only
  have he := omittedStrengthCoefficient_eq_original hr hu hc hk hkc hm hM d lam α
  have hq : omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM
      (fun r=>laplaceComparisonStrength d lam r*r)
      ((laplaceComparisonStrength_contDiff d lam).continuous.mul continuous_id) α)=
      fun u=>omittedStrengthCoefficient d u0 (omittedSweepQuantile hr hu hc hk hkc hm hM α) lam u*
        omittedSweepQuantile hr hu hc hk hkc hm hM α u := by
    ext u
    by_cases hu' : u0≤u <;> simp [omittedStrengthCoefficient,omittedSweepQuantile,
      omittedExtension,IccExtend,constrainedCoefficient,constrainedQuantileMap,hu',Function.comp_def]
  rw [←he,hq]
  have ha := omittedStrengthSweep_clocks_admissible b h _ hu hd hlam hlcut hcross hb hb0 hh hh0
    ((omittedSweepQuantile_monotone hr hu hc hk hkc hm hM α).monotoneOn _)
    (fun u _=>⟨hr0.trans (omittedSweepQuantile_bounds hr hu hc hk hkc hm hM α u).1,
      (omittedSweepQuantile_bounds hr hu hc hk hkc hm hM α u).2⟩)
  exact ⟨ha.1,ha.2.1,ha.2.2.1 0 (by norm_num),ha.2.2.2 0 (by norm_num)⟩

def omittedComparisonSweepMinimum (n : ℕ) (b h : ℝ → ℝ) (d lam : ℝ) : ℝ :=
  sInf (Set.range (omittedComparisonSweepObjective hr hu hc hk hkc hm hM n b h d lam))

theorem omittedComparisonSweepMinimum_attained (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ)
    {d lam : ℝ} (hd : d≠0) (hlam : 0≤lam) (hlcut : lam≤b u0)
    (hcross : ∀u∈Ico (0:ℝ) u0,b u+lam≤b u0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hb0 : 0≤b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0)
    (hMc : Continuous M) (hne : (inverseIntegralConstraints r0 u0 k M).Nonempty) :
    ∃α:inverseIntegralConstraints r0 u0 k M,
      omittedComparisonSweepObjective hr hu hc hk hkc hm hM n b h d lam α=
        omittedComparisonSweepMinimum hr hu hc hk hkc hm hM n b h d lam ∧
      ∀γ,omittedComparisonSweepMinimum hr hu hc hk hkc hm hM n b h d lam≤
        omittedComparisonSweepObjective hr hu hc hk hkc hm hM n b h d lam γ := by
  have hfeas γ := omittedComparisonSweep_clocks_admissible hr0 hr hu hc hk hkc hm hM
    b h hd hlam hlcut hcross hb hb0 hh hh0 γ
  obtain ⟨α,hα⟩ := inverseCompensatedPressure_minimum hr hu.2 hc hk hkc hm hM
    (laplaceComparisonStrength d lam) (laplaceComparisonStrength_contDiff d lam).continuous hMc hne
    n hn b h (fun γ=>(hfeas γ).1) (fun γ=>(hfeas γ).2.1)
    (fun γ=>(hfeas γ).2.2.1) (fun γ=>(hfeas γ).2.2.2) 0
  have hmin (γ) : omittedComparisonSweepObjective hr hu hc hk hkc hm hM n b h d lam α ≤
      omittedComparisonSweepObjective hr hu hc hk hkc hm hM n b h d lam γ := by
    rw [omittedComparisonSweepObjective_eq_inverse hr hu hc hk hkc hm hM,
      omittedComparisonSweepObjective_eq_inverse hr hu hc hk hkc hm hM]
    exact hα γ
  have heq : omittedComparisonSweepMinimum hr hu hc hk hkc hm hM n b h d lam=
      omittedComparisonSweepObjective hr hu hc hk hkc hm hM n b h d lam α := by
    apply IsLeast.csInf_eq
    refine ⟨Set.mem_range_self α,?_⟩
    rintro _ ⟨γ,rfl⟩
    exact hmin γ
  exact ⟨α,heq.symm,fun γ=>heq.symm ▸ hmin γ⟩

theorem omittedComparisonSweepMinimum_lipschitz (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ)
    {d L : ℝ} (hd : d≠0) (hLcut : L≤b u0)
    (hcross : ∀u∈Ico (0:ℝ) u0,b u+L≤b u0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hb0 : 0≤b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0)
    (hMc : Continuous M) (hne : (inverseIntegralConstraints r0 u0 k M).Nonempty) :
    LipschitzOnWith 1 (omittedComparisonSweepMinimum hr hu hc hk hkc hm hM n b h d) (Icc (0:ℝ) L) := by
  apply WallSweep.minimum_lipschitzOn
    (fun lam α=>omittedComparisonSweepObjective hr hu hc hk hkc hm hM n b h d lam α)
  · intro lam hlam
    exact omittedComparisonSweepMinimum_attained hr0 hr hu hc hk hkc hm hM n hn b h hd hlam.1
      (hlam.2.trans hLcut) (fun u hum=>by linarith [hcross u hum,hlam.2]) hb hb0 hh hh0 hMc hne
  · intro α
    exact omittedStrengthSweepObjective_lipschitz n hn b h _ hu hd hLcut hcross hb hb0 hh hh0
      ((omittedSweepQuantile_monotone hr hu hc hk hkc hm hM α).monotoneOn _)
      (fun u _=>⟨hr0.trans (omittedSweepQuantile_bounds hr hu hc hk hkc hm hM α u).1,
        (omittedSweepQuantile_bounds hr hu hc hk hkc hm hM α u).2⟩)
      (omittedSweepQuantile_continuous hr hu hc hk hkc hm hM α).continuousOn

theorem omittedComparisonSweepMinimum_zero (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ)
    {d : ℝ} (hd : d≠0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hb0 : 0≤b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0)
    (hMc : Continuous M) (hne : (inverseIntegralConstraints r0 u0 k M).Nonempty) :
    omittedComparisonSweepMinimum hr hu hc hk hkc hm hM n b h d 0=realOrderedSKPathPressure n b h 0 := by
  obtain ⟨α,he,_⟩ := omittedComparisonSweepMinimum_attained hr0 hr hu hc hk hkc hm hM n hn b h hd le_rfl
    (hb0.trans (hb (by norm_num) hu hu.1)) (fun u hum=>by simpa using hb ⟨hum.1,hum.2.le.trans hu.2⟩ hu hum.2.le)
    hb hb0 hh hh0 hMc hne
  exact he.symm.trans (omittedStrengthSweepObjective_zero n b h _ d u0)

theorem omittedComparisonSweepMinimum_monotone (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ)
    {d L : ℝ} (hd : d≠0) (hLcut : L≤b u0)
    (hcross : ∀u∈Ico (0:ℝ) u0,b u+L≤b u0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hb0 : 0≤b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0)
    (hMc : Continuous M) (hne : (inverseIntegralConstraints r0 u0 k M).Nonempty) :
    MonotoneOn (omittedComparisonSweepMinimum hr hu hc hk hkc hm hM n b h d) (Icc (0:ℝ) L) := by
  intro lam hlam lam' hlam' hll
  obtain ⟨α,he,_⟩ := omittedComparisonSweepMinimum_attained hr0 hr hu hc hk hkc hm hM n hn b h hd
    hlam'.1 (hlam'.2.trans hLcut) (fun u hum=>by linarith [hcross u hum,hlam'.2]) hb hb0 hh hh0 hMc hne
  obtain ⟨_,_,hmin⟩ := omittedComparisonSweepMinimum_attained hr0 hr hu hc hk hkc hm hM n hn b h hd
    hlam.1 (hlam.2.trans hLcut) (fun u hum=>by linarith [hcross u hum,hlam.2]) hb hb0 hh hh0 hMc hne
  exact (hmin α).trans ((omittedStrengthSweepObjective_monotone n hn b h _ hu hd hLcut hcross hb hb0 hh hh0
    ((omittedSweepQuantile_monotone hr hu hc hk hkc hm hM α).monotoneOn _)
    (fun u _=>⟨hr0.trans (omittedSweepQuantile_bounds hr hu hc hk hkc hm hM α u).1,
      (omittedSweepQuantile_bounds hr hu hc hk hkc hm hM α u).2⟩)
    (omittedSweepQuantile_continuous hr hu hc hk hkc hm hM α).continuousOn hlam hlam' hll).trans_eq he)

def omittedComparisonSweepCost (n : ℕ) (b h : ℝ → ℝ) (d lam : ℝ) : ℝ :=
  omittedComparisonSweepMinimum hr hu hc hk hkc hm hM n b h d lam-realOrderedSKPathPressure n b h 0

theorem omittedComparisonSweepCost_lipschitz (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ)
    {d L : ℝ} (hd : d≠0) (hLcut : L≤b u0)
    (hcross : ∀u∈Ico (0:ℝ) u0,b u+L≤b u0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hb0 : 0≤b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0)
    (hMc : Continuous M) (hne : (inverseIntegralConstraints r0 u0 k M).Nonempty) :
    LipschitzOnWith 1 (omittedComparisonSweepCost hr hu hc hk hkc hm hM n b h d) (Icc (0:ℝ) L) := by
  have hlip := omittedComparisonSweepMinimum_lipschitz hr0 hr hu hc hk hkc hm hM n hn b h hd hLcut hcross hb hb0 hh hh0 hMc hne
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro lam hlam lam' hlam'
  simpa only [omittedComparisonSweepCost,Real.dist_eq,sub_sub_sub_cancel_right] using hlip.dist_le_mul lam hlam lam' hlam'

theorem omittedComparisonSweepCost_monotone (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ)
    {d L : ℝ} (hd : d≠0) (hLcut : L≤b u0)
    (hcross : ∀u∈Ico (0:ℝ) u0,b u+L≤b u0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hb0 : 0≤b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0)
    (hMc : Continuous M) (hne : (inverseIntegralConstraints r0 u0 k M).Nonempty) :
    MonotoneOn (omittedComparisonSweepCost hr hu hc hk hkc hm hM n b h d) (Icc (0:ℝ) L) := by
  intro lam hlam lam' hlam' hll
  exact sub_le_sub_right (omittedComparisonSweepMinimum_monotone hr0 hr hu hc hk hkc hm hM n hn b h hd hLcut hcross hb hb0 hh hh0 hMc hne hlam hlam' hll) _

theorem omittedComparisonSweepCost_zero (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ)
    {d : ℝ} (hd : d≠0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hb0 : 0≤b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0)
    (hMc : Continuous M) (hne : (inverseIntegralConstraints r0 u0 k M).Nonempty) :
    omittedComparisonSweepCost hr hu hc hk hkc hm hM n b h d 0=0 := by
  unfold omittedComparisonSweepCost
  rw [omittedComparisonSweepMinimum_zero hr0 hr hu hc hk hkc hm hM n hn b h hd hb hb0 hh hh0 hMc hne,sub_self]

theorem omittedComparisonSweepCost_nonneg (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ)
    {d L lam : ℝ} (hd : d≠0) (hLcut : L≤b u0)
    (hcross : ∀u∈Ico (0:ℝ) u0,b u+L≤b u0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hb0 : 0≤b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0)
    (hMc : Continuous M) (hne : (inverseIntegralConstraints r0 u0 k M).Nonempty)
    (hlam : lam∈Icc (0:ℝ) L) :
    0≤omittedComparisonSweepCost hr hu hc hk hkc hm hM n b h d lam := by
  have hmon := omittedComparisonSweepMinimum_monotone hr0 hr hu hc hk hkc hm hM n hn b h hd hLcut hcross
    hb hb0 hh hh0 hMc hne (⟨le_rfl,hlam.1.trans hlam.2⟩ : (0:ℝ)∈Icc (0:ℝ) L) hlam hlam.1
  rw [omittedComparisonSweepMinimum_zero hr0 hr hu hc hk hkc hm hM n hn b h hd hb hb0 hh hh0 hMc hne] at hmon
  exact sub_nonneg.mpr hmon

theorem omittedComparisonSweepMinimum_ae_log_derivative_le (n : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ) {d L : ℝ} (hd : d≠0) (hL : 0<L) (hLcut : L≤b u0)
    (hcross : ∀u∈Ico (0:ℝ) u0,b u+L≤b u0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hb0 : 0≤b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0)
    (hMc : Continuous M) (hne : (inverseIntegralConstraints r0 u0 k M).Nonempty) :
    ∀ᵐ lam ∂volume.restrict (Ioo (0:ℝ) L),
      ∃α:inverseIntegralConstraints r0 u0 k M,
        omittedComparisonSweepObjective hr hu hc hk hkc hm hM n b h d lam α=
          omittedComparisonSweepMinimum hr hu hc hk hkc hm hM n b h d lam ∧
        let R := omittedSweepQuantile hr hu hc hk hkc hm hM α
        let e := omittedStrengthCoefficient d u0 R lam
        let bf := fun u=>(b u-e u).toNNReal
        let hf := fun u=>(h u+e u*R u).toNNReal
        lam*deriv (omittedComparisonSweepMinimum hr hu hc hk hkc hm hM n b h d) lam≤
          (1/4:ℝ)*(∫u in (0:ℝ)..1,e u*((orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
            (orderedPathS n bf hf u-R u)^2)) := by
  have hlip := omittedComparisonSweepMinimum_lipschitz hr0 hr hu hc hk hkc hm hM n hn b h hd hLcut hcross hb hb0 hh hh0 hMc hne
  have hlip' : LipschitzOnWith 1 (omittedComparisonSweepMinimum hr hu hc hk hkc hm hM n b h d)
      (uIcc (0:ℝ) L) := by simpa only [uIcc_of_le hL.le] using hlip
  have hac := hlip'.absolutelyContinuousOnInterval
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [hac.ae_differentiableAt] with lam hdiff hlam
  obtain ⟨α,hcontact,hmin⟩ := omittedComparisonSweepMinimum_attained hr0 hr hu hc hk hkc hm hM n hn b h hd
    hlam.1.le (hlam.2.le.trans hLcut) (fun u hum=>by linarith [hcross u hum,hlam.2]) hb hb0 hh hh0 hMc hne
  have hbound : ∀ᶠ l in 𝓝 lam,
      omittedComparisonSweepMinimum hr hu hc hk hkc hm hM n b h d l≤
        omittedComparisonSweepObjective hr hu hc hk hkc hm hM n b h d l α := by
    filter_upwards [Icc_mem_nhds hlam.1 hlam.2] with l hl
    obtain ⟨_,_,hlmin⟩ := omittedComparisonSweepMinimum_attained hr0 hr hu hc hk hkc hm hM n hn b h hd
      hl.1 (hl.2.trans hLcut) (fun u hum=>by linarith [hcross u hum,hl.2]) hb hb0 hh hh0 hMc hne
    exact hlmin α
  have hq := (omittedSweepQuantile_monotone hr hu hc hk hkc hm hM α).monotoneOn (Icc u0 1)
  have hqb := fun u (_:u∈Icc u0 1)=>
    (⟨hr0.trans (omittedSweepQuantile_bounds hr hu hc hk hkc hm hM α u).1,
      (omittedSweepQuantile_bounds hr hu hc hk hkc hm hM α u).2⟩ : omittedSweepQuantile hr hu hc hk hkc hm hM α u∈Icc (0:ℝ) 1)
  have hqc : ContinuousOn (omittedSweepQuantile hr hu hc hk hkc hm hM α) (Icc u0 1) :=
    (omittedSweepQuantile_continuous hr hu hc hk hkc hm hM α).continuousOn
  have hder := omittedStrengthSweepObjective_hasDerivAt n hn b h _ hu hd hLcut hcross hb hb0 hh hh0 hq hqb hqc hlam
  have hdiff' := hdiff (by rw [uIcc_of_le hL.le];exact ⟨hlam.1.le,hlam.2.le⟩)
  have he := WallSweep.minimum_derivative_eq hcontact hbound hdiff'.hasDerivAt hder
  refine ⟨α,hcontact,?_⟩
  dsimp only
  rw [he,←hder.deriv]
  exact omittedStrengthSweep_log_derivative_le n hn b h _ hu hd hLcut hcross hb hb0 hh hh0 hq hqb hqc hlam

omit hr0 in
theorem omittedComparisonSweepCost_deriv_eq_minimum (n : ℕ) (b h : ℝ → ℝ) (d lam : ℝ) :
    deriv (omittedComparisonSweepCost hr hu hc hk hkc hm hM n b h d) lam=
      deriv (omittedComparisonSweepMinimum hr hu hc hk hkc hm hM n b h d) lam := deriv_sub_const _

theorem omittedComparisonSweepCost_ae_log_derivative_le (n : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ) {d L : ℝ} (hd : d≠0) (hL : 0<L) (hLcut : L≤b u0)
    (hcross : ∀u∈Ico (0:ℝ) u0,b u+L≤b u0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hb0 : 0≤b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0)
    (hMc : Continuous M) (hne : (inverseIntegralConstraints r0 u0 k M).Nonempty) :
    ∀ᵐ lam ∂volume.restrict (Ioo (0:ℝ) L),
      ∃α:inverseIntegralConstraints r0 u0 k M,
        omittedComparisonSweepObjective hr hu hc hk hkc hm hM n b h d lam α=
          omittedComparisonSweepMinimum hr hu hc hk hkc hm hM n b h d lam ∧
        let R := omittedSweepQuantile hr hu hc hk hkc hm hM α
        let e := omittedStrengthCoefficient d u0 R lam
        let bf := fun u=>(b u-e u).toNNReal
        let hf := fun u=>(h u+e u*R u).toNNReal
        lam*deriv (omittedComparisonSweepCost hr hu hc hk hkc hm hM n b h d) lam≤
          (1/4:ℝ)*(∫u in (0:ℝ)..1,e u*((orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
            (orderedPathS n bf hf u-R u)^2)) := by
  simp_rw [omittedComparisonSweepCost_deriv_eq_minimum hr hu hc hk hkc hm hM]
  exact omittedComparisonSweepMinimum_ae_log_derivative_le hr0 hr hu hc hk hkc hm hM n hn b h hd hL hLcut hcross hb hb0 hh hh0 hMc hne

end
end OAI.SKFluctuations.LaplaceWindowFormalization
