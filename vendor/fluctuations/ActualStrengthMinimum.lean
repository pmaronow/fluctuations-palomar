module

public import ActualStrengthEnvelope

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀ r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

def comparisonSweepQuantile (α : inverseIntegralConstraints 0 0 k M) : ℝ → ℝ :=
  IccExtend zero_le_one (constrainedQuantileMap zero_le_one hc hk hkc hm hM α)

theorem comparisonSweepQuantile_eq (α : inverseIntegralConstraints 0 0 k M)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    comparisonSweepQuantile hc hk hkc hm hM α u=
      constrainedQuantile zero_le_one hc hk hkc hm hM α ⟨u,hu⟩ := by
  exact IccExtend_of_mem zero_le_one _ hu

theorem comparisonSweepQuantile_continuous (α : inverseIntegralConstraints 0 0 k M) :
    Continuous (comparisonSweepQuantile hc hk hkc hm hM α) :=
  (constrainedQuantileMap zero_le_one hc hk hkc hm hM α).continuous.Icc_extend' (h:=zero_le_one)

theorem comparisonSweepQuantile_monotone (α : inverseIntegralConstraints 0 0 k M) :
    Monotone (comparisonSweepQuantile hc hk hkc hm hM α) := by
  apply Monotone.IccExtend zero_le_one
  intro u v huv
  exact (inverseConstraintOrderIso zero_le_one hc hk hkc hm hM α).symm.monotone huv

theorem comparisonSweepQuantile_bounds (α : inverseIntegralConstraints 0 0 k M) (u : ℝ) :
    comparisonSweepQuantile hc hk hkc hm hM α u∈Icc (0:ℝ) 1 :=
  (constrainedQuantile zero_le_one hc hk hkc hm hM α (projIcc 0 1 zero_le_one u)).property

theorem fullMassCoefficient_eq_sweepQuantile (g : ℝ → ℝ) (hg : Continuous g)
    (α : inverseIntegralConstraints 0 0 k M) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    omittedExtension zero_le_one
      (constrainedCoefficient zero_le_one hc hk hkc hm hM g hg α) u=
        g (comparisonSweepQuantile hc hk hkc hm hM α u) := by
  rw [fullMassCoefficient_eq zero_le_one hc hk hkc hm hM g hg α hu,
    comparisonSweepQuantile_eq hc hk hkc hm hM α hu]

def comparisonSweepObjective (n : ℕ) (b : ℝ → ℝ) (d lam : ℝ)
    (α : inverseIntegralConstraints 0 0 k M) : ℝ :=
  strengthSweepObjective n b d (comparisonSweepQuantile hc hk hkc hm hM α) lam

theorem comparisonSweepObjective_eq_inverse (n : ℕ) (hn : 0<n)
    (b : ℝ → ℝ) {d lam : ℝ} (hd : d≠0) (hlam : 0≤lam) (hlb : lam≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (α : inverseIntegralConstraints 0 0 k M) :
    comparisonSweepObjective hc hk hkc hm hM n b d lam α=
      inverseCompensatedPressure zero_le_one zero_le_one hc hk hkc hm hM
        (laplaceComparisonStrength d lam) (laplaceComparisonStrength_contDiff d lam).continuous
        n b (fun _=>0) 0 α := by
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let g := laplaceComparisonStrength d lam
  have hg : Continuous g := (laplaceComparisonStrength_contDiff d lam).continuous
  have ha := strengthSweep_clocks_admissible b R hd hlam hlb hb
    ((comparisonSweepQuantile_monotone hc hk hkc hm hM α).monotoneOn _)
    (fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α u)
  let e := omittedExtension zero_le_one
    (constrainedCoefficient zero_le_one hc hk hkc hm hM g hg α)
  let q := omittedExtension zero_le_one
    (constrainedCoefficient zero_le_one hc hk hkc hm hM (fun r=>g r*r) (hg.mul continuous_id) α)
  let p := omittedExtension zero_le_one
    (constrainedCoefficient zero_le_one hc hk hkc hm hM (fun r=>g r*r^2) (hg.mul (continuous_id.pow 2)) α)
  have he (u : ℝ) (hu : u∈Icc (0:ℝ) 1) : e u=g (R u) :=
    fullMassCoefficient_eq_sweepQuantile hc hk hkc hm hM g hg α hu
  have hq (u : ℝ) (hu : u∈Icc (0:ℝ) 1) : q u=g (R u)*R u :=
    fullMassCoefficient_eq_sweepQuantile hc hk hkc hm hM _ (hg.mul continuous_id) α hu
  have hp (u : ℝ) (hu : u∈Icc (0:ℝ) 1) : p u=g (R u)*(R u)^2 :=
    fullMassCoefficient_eq_sweepQuantile hc hk hkc hm hM _ (hg.mul (continuous_id.pow 2)) α hu
  have hemono : MonotoneOn (fun u=>b u-e u) (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    change b u-e u≤b v-e v
    rw [he u hu,he v hv]
    exact ha.1 hu hv huv
  have hqmono : MonotoneOn q (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    rw [hq u hu,hq v hv]
    exact ha.2.1 hu hv huv
  have he0 : 0≤b 0-e 0 := by
    rw [he 0 (by norm_num)]
    exact ha.2.2.1 0 (by norm_num)
  have hq0 : 0≤q 0 := by
    rw [hq 0 (by norm_num)]
    exact ha.2.2.2 0 (by norm_num)
  have hpeq := realOrderedSKPathPressure_uniform_comparison n hn
    (fun u=>b u-g (R u)) (fun u=>g (R u)*R u) (fun u=>b u-e u) q
    ha.1 ha.2.1 hemono hqmono (ha.2.2.1 0 (by norm_num))
    (ha.2.2.2 0 (by norm_num)) he0 hq0 (B:=0) (H:=0)
    (by intro u hu;rw [he u hu];simp) (by intro u hu;rw [hq u hu];simp) 0
  have hP : realOrderedSKPathPressure n (fun u=>b u-g (R u)) (fun u=>g (R u)*R u) 0=
      realOrderedSKPathPressure n (fun u=>b u-e u) q 0 := by
    apply sub_eq_zero.mp
    exact abs_eq_zero.mp (le_antisymm (by simpa using hpeq) (abs_nonneg _))
  change realOrderedSKPathPressure n (fun u=>b u-g (R u)) (fun u=>g (R u)*R u) 0+
      (1/4:ℝ)*(∫ u in (0:ℝ)..1,g (R u)*(R u)^2)=
    realOrderedSKPathPressure n (fun u=>b u-e u) (fun u=>0+q u) 0+
      (1/4:ℝ)*(∫ u in (0:ℝ)..1,p u)
  simp only [zero_add]
  rw [hP]
  congr 2
  apply intervalIntegral.integral_congr
  intro u hu
  exact (hp u (by simpa only [uIcc_of_le zero_le_one] using hu)).symm

def comparisonSweepMinimum (n : ℕ) (b : ℝ → ℝ) (d : ℝ) (lam : ℝ) : ℝ :=
  sInf (Set.range (comparisonSweepObjective hc hk hkc hm hM n b d lam))

theorem comparisonSweepMinimum_attained (n : ℕ) (hn : 0<n)
    (b : ℝ → ℝ) {d lam : ℝ} (hd : d≠0) (hlam : 0≤lam) (hlb : lam≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hMc : Continuous M)
    (hne : (inverseIntegralConstraints 0 0 k M).Nonempty) :
    ∃ α : inverseIntegralConstraints 0 0 k M,
      comparisonSweepObjective hc hk hkc hm hM n b d lam α=
        comparisonSweepMinimum hc hk hkc hm hM n b d lam ∧
      ∀ β, comparisonSweepMinimum hc hk hkc hm hM n b d lam≤
        comparisonSweepObjective hc hk hkc hm hM n b d lam β := by
  have hmstrength := laplaceComparisonStrength_monotonicities_nonneg hd hlam
  obtain ⟨α,hα⟩ := fullMassComparison_minimum zero_le_one hc hk hkc hm hM hMc hne
    le_rfl b hb (laplaceComparisonStrength d lam) (laplaceComparisonStrength_contDiff d lam).continuous
    hmstrength.1 hmstrength.2 (fun r _=>laplaceComparisonStrength_nonneg d r hlam)
    (fun r _=>(laplaceComparisonStrength_le d hlam r).trans hlb) n hn 0
  have hmin (β) : comparisonSweepObjective hc hk hkc hm hM n b d lam α≤
      comparisonSweepObjective hc hk hkc hm hM n b d lam β := by
    rw [comparisonSweepObjective_eq_inverse hc hk hkc hm hM n hn b hd hlam hlb hb α,
      comparisonSweepObjective_eq_inverse hc hk hkc hm hM n hn b hd hlam hlb hb β]
    exact hα β
  have heq : comparisonSweepMinimum hc hk hkc hm hM n b d lam=
      comparisonSweepObjective hc hk hkc hm hM n b d lam α := by
    apply IsLeast.csInf_eq
    refine ⟨Set.mem_range_self α,?_⟩
    rintro _ ⟨β,rfl⟩
    exact hmin β
  exact ⟨α,heq.symm,fun β=>heq.symm ▸ hmin β⟩

theorem comparisonSweepMinimum_lipschitz (n : ℕ) (hn : 0<n)
    (b : ℝ → ℝ) {d L : ℝ} (hd : d≠0) (hLb : L≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hMc : Continuous M)
    (hne : (inverseIntegralConstraints 0 0 k M).Nonempty) :
    LipschitzOnWith 1 (comparisonSweepMinimum hc hk hkc hm hM n b d) (Icc (0:ℝ) L) := by
  apply WallSweep.minimum_lipschitzOn
    (fun lam α=>comparisonSweepObjective hc hk hkc hm hM n b d lam α)
  · intro lam hlam
    exact comparisonSweepMinimum_attained hc hk hkc hm hM n hn b hd hlam.1
      (hlam.2.trans hLb) hb hMc hne
  · intro α
    exact strengthSweepObjective_lipschitz n hn b _ hd hLb hb
      ((comparisonSweepQuantile_monotone hc hk hkc hm hM α).monotoneOn _)
      (fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α u)
      (comparisonSweepQuantile_continuous hc hk hkc hm hM α)

theorem comparisonSweepMinimum_monotone (n : ℕ) (hn : 0<n)
    (b : ℝ → ℝ) {d L : ℝ} (hd : d≠0) (hLb : L≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hMc : Continuous M)
    (hne : (inverseIntegralConstraints 0 0 k M).Nonempty) :
    MonotoneOn (comparisonSweepMinimum hc hk hkc hm hM n b d) (Icc (0:ℝ) L) := by
  intro lam hlam lam' hlam' hll
  obtain ⟨α,he,_⟩ := comparisonSweepMinimum_attained hc hk hkc hm hM n hn b hd
    hlam'.1 (hlam'.2.trans hLb) hb hMc hne
  obtain ⟨_,_,hmin⟩ := comparisonSweepMinimum_attained hc hk hkc hm hM n hn b hd
    hlam.1 (hlam.2.trans hLb) hb hMc hne
  exact (hmin α).trans ((strengthSweepObjective_monotone n hn b _ hd hLb hb
    ((comparisonSweepQuantile_monotone hc hk hkc hm hM α).monotoneOn _)
    (fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α u)
    (comparisonSweepQuantile_continuous hc hk hkc hm hM α) hlam hlam' hll).trans_eq he)

theorem comparisonSweepMinimum_zero (n : ℕ) (hn : 0<n)
    (b : ℝ → ℝ) {d : ℝ} (hd : d≠0) (hb0 : 0≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hMc : Continuous M)
    (hne : (inverseIntegralConstraints 0 0 k M).Nonempty) :
    comparisonSweepMinimum hc hk hkc hm hM n b d 0=
      realOrderedSKPathPressure n b (fun _=>0) 0 := by
  obtain ⟨α,he,_⟩ := comparisonSweepMinimum_attained hc hk hkc hm hM n hn b hd
    le_rfl hb0 hb hMc hne
  exact he.symm.trans (strengthSweepObjective_zero n b _ d)

def comparisonSweepCost (n : ℕ) (b : ℝ → ℝ) (d lam : ℝ) : ℝ :=
  comparisonSweepMinimum hc hk hkc hm hM n b d lam-
    realOrderedSKPathPressure n b (fun _=>0) 0

theorem comparisonSweepCost_zero (n : ℕ) (hn : 0<n)
    (b : ℝ → ℝ) {d : ℝ} (hd : d≠0) (hb0 : 0≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hMc : Continuous M)
    (hne : (inverseIntegralConstraints 0 0 k M).Nonempty) :
    comparisonSweepCost hc hk hkc hm hM n b d 0=0 := by
  unfold comparisonSweepCost
  rw [comparisonSweepMinimum_zero hc hk hkc hm hM n hn b hd hb0 hb hMc hne,sub_self]

theorem comparisonSweepCost_lipschitz (n : ℕ) (hn : 0<n)
    (b : ℝ → ℝ) {d L : ℝ} (hd : d≠0) (hLb : L≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hMc : Continuous M)
    (hne : (inverseIntegralConstraints 0 0 k M).Nonempty) :
    LipschitzOnWith 1 (comparisonSweepCost hc hk hkc hm hM n b d) (Icc (0:ℝ) L) := by
  have h := comparisonSweepMinimum_lipschitz hc hk hkc hm hM n hn b hd hLb hb hMc hne
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro lam hlam lam' hlam'
  simpa only [comparisonSweepCost,Real.dist_eq,sub_sub_sub_cancel_right] using
    h.dist_le_mul lam hlam lam' hlam'

theorem comparisonSweepCost_monotone (n : ℕ) (hn : 0<n)
    (b : ℝ → ℝ) {d L : ℝ} (hd : d≠0) (hLb : L≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hMc : Continuous M)
    (hne : (inverseIntegralConstraints 0 0 k M).Nonempty) :
    MonotoneOn (comparisonSweepCost hc hk hkc hm hM n b d) (Icc (0:ℝ) L) := by
  intro lam hlam lam' hlam' hll
  exact sub_le_sub_right
    (comparisonSweepMinimum_monotone hc hk hkc hm hM n hn b hd hLb hb hMc hne hlam hlam' hll) _

theorem comparisonSweepCost_nonneg (n : ℕ) (hn : 0<n)
    (b : ℝ → ℝ) {d L lam : ℝ} (hd : d≠0) (hLb : L≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hMc : Continuous M)
    (hne : (inverseIntegralConstraints 0 0 k M).Nonempty) (hlam : lam∈Icc (0:ℝ) L) :
    0≤comparisonSweepCost hc hk hkc hm hM n b d lam := by
  have hL : 0≤L := hlam.1.trans hlam.2
  have h := comparisonSweepCost_monotone hc hk hkc hm hM n hn b hd hLb hb hMc hne
    (⟨le_rfl,hL⟩ : (0:ℝ)∈Icc (0:ℝ) L) hlam hlam.1
  rwa [comparisonSweepCost_zero hc hk hkc hm hM n hn b hd (hL.trans hLb) hb hMc hne] at h

theorem comparisonSweepMinimum_ae_log_derivative_le (n : ℕ) (hn : 0<n)
    (b : ℝ → ℝ) {d L : ℝ} (hd : d≠0) (hL : 0<L) (hLb : L≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hMc : Continuous M)
    (hne : (inverseIntegralConstraints 0 0 k M).Nonempty) :
    ∀ᵐ lam ∂volume.restrict (Ioo (0:ℝ) L),
      ∃ α : inverseIntegralConstraints 0 0 k M,
        comparisonSweepObjective hc hk hkc hm hM n b d lam α=
          comparisonSweepMinimum hc hk hkc hm hM n b d lam ∧
        let R := comparisonSweepQuantile hc hk hkc hm hM α
        let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
        let hf := fun u=>(laplaceComparisonStrength d lam (R u)*R u).toNNReal
        lam*deriv (comparisonSweepMinimum hc hk hkc hm hM n b d) lam≤
          (1/4:ℝ)*(∫ u in (0:ℝ)..1,laplaceComparisonStrength d lam (R u)*
            ((orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
              (orderedPathS n bf hf u-R u)^2)) := by
  have hlip := comparisonSweepMinimum_lipschitz hc hk hkc hm hM n hn b hd hLb hb hMc hne
  have hlip' : LipschitzOnWith 1 (comparisonSweepMinimum hc hk hkc hm hM n b d)
      (uIcc (0:ℝ) L) := by simpa only [uIcc_of_le hL.le] using hlip
  have hac := hlip'.absolutelyContinuousOnInterval
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [hac.ae_differentiableAt] with lam hdiff hlam
  obtain ⟨α,hcontact,hmin⟩ := comparisonSweepMinimum_attained hc hk hkc hm hM n hn b hd
    hlam.1.le (hlam.2.le.trans hLb) hb hMc hne
  have hbound : ∀ᶠ l in 𝓝 lam,
      comparisonSweepMinimum hc hk hkc hm hM n b d l≤
        comparisonSweepObjective hc hk hkc hm hM n b d l α := by
    filter_upwards [Icc_mem_nhds hlam.1 hlam.2] with l hl
    obtain ⟨_,_,hlmin⟩ := comparisonSweepMinimum_attained hc hk hkc hm hM n hn b hd
      hl.1 (hl.2.trans hLb) hb hMc hne
    exact hlmin α
  have hq := comparisonSweepQuantile_monotone hc hk hkc hm hM α
  have hqb := fun u (_ : u∈Icc (0:ℝ) 1)=>comparisonSweepQuantile_bounds hc hk hkc hm hM α u
  have hqc := comparisonSweepQuantile_continuous hc hk hkc hm hM α
  have hder := strengthSweepObjective_hasDerivAt n hn b _ hd hLb hb (hq.monotoneOn _) hqb hqc hlam
  have hdiff' := hdiff (by rw [uIcc_of_le hL.le]; exact ⟨hlam.1.le,hlam.2.le⟩)
  have he := WallSweep.minimum_derivative_eq hcontact hbound hdiff'.hasDerivAt hder
  refine ⟨α,hcontact,?_⟩
  dsimp only
  rw [he,← hder.deriv]
  exact strengthSweep_log_derivative_le n hn b _ hd hLb hb (hq.monotoneOn _) hqb hqc hlam

theorem comparisonSweepCost_deriv_eq_minimum (n : ℕ) (b : ℝ → ℝ) (d lam : ℝ) :
    deriv (comparisonSweepCost hc hk hkc hm hM n b d) lam=
      deriv (comparisonSweepMinimum hc hk hkc hm hM n b d) lam :=
  deriv_sub_const _

theorem comparisonSweepCost_ae_log_derivative_le (n : ℕ) (hn : 0<n)
    (b : ℝ → ℝ) {d L : ℝ} (hd : d≠0) (hL : 0<L) (hLb : L≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hMc : Continuous M)
    (hne : (inverseIntegralConstraints 0 0 k M).Nonempty) :
    ∀ᵐ lam ∂volume.restrict (Ioo (0:ℝ) L),
      ∃ α : inverseIntegralConstraints 0 0 k M,
        comparisonSweepObjective hc hk hkc hm hM n b d lam α=
          comparisonSweepMinimum hc hk hkc hm hM n b d lam ∧
        let R := comparisonSweepQuantile hc hk hkc hm hM α
        let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
        let hf := fun u=>(laplaceComparisonStrength d lam (R u)*R u).toNNReal
        lam*deriv (comparisonSweepCost hc hk hkc hm hM n b d) lam≤
          (1/4:ℝ)*(∫ u in (0:ℝ)..1,laplaceComparisonStrength d lam (R u)*
            ((orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
              (orderedPathS n bf hf u-R u)^2)) := by
  simp_rw [comparisonSweepCost_deriv_eq_minimum]
  exact comparisonSweepMinimum_ae_log_derivative_le hc hk hkc hm hM n hn b hd hL hLb hb hMc hne

end
end OAI.SKFluctuations.LaplaceWindowFormalization
