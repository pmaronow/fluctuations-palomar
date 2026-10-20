module

public import VariableEndpointStrengthEnvelope
public import VariableEndpointComparisonPotential

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal
section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

def variableEndpointComparisonSweepObjective (n : ℕ) (b h : ℝ → ℝ) (d lam : ℝ)
    (α : inverseIntegralConstraints 0 0 k M) : ℝ :=
  variableEndpointStrengthSweepObjective n b h d (comparisonSweepQuantile hc hk hkc hm hM α) lam

theorem variableEndpointComparisonSweepObjective_eq_inverse (n : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ) {d lam : ℝ} (hd : d≠0) (hlam : 0≤lam) (hlb : lam≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (α : inverseIntegralConstraints 0 0 k M) :
    variableEndpointComparisonSweepObjective hc hk hkc hm hM n b h d lam α=
      inverseCompensatedPressure zero_le_one zero_le_one hc hk hkc hm hM
        (laplaceComparisonStrength d lam) (laplaceComparisonStrength_contDiff d lam).continuous
        n b h 0 α := by
  exact comparisonVariableEndpointObjective_eq_inverse hc hk hkc hm hM n hn b h hd hlam hlb hb hh hh0 α

def variableEndpointComparisonSweepMinimum (n : ℕ) (b h : ℝ → ℝ) (d : ℝ) (lam : ℝ) : ℝ :=
  sInf (Set.range (variableEndpointComparisonSweepObjective hc hk hkc hm hM n b h d lam))

theorem variableEndpointComparisonSweepMinimum_attained (n : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ) {d lam : ℝ} (hd : d≠0) (hlam : 0≤lam) (hlb : lam≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hMc : Continuous M)
    (hne : (inverseIntegralConstraints 0 0 k M).Nonempty) :
    ∃ α : inverseIntegralConstraints 0 0 k M,
      variableEndpointComparisonSweepObjective hc hk hkc hm hM n b h d lam α=
        variableEndpointComparisonSweepMinimum hc hk hkc hm hM n b h d lam ∧
      ∀ β, variableEndpointComparisonSweepMinimum hc hk hkc hm hM n b h d lam≤
        variableEndpointComparisonSweepObjective hc hk hkc hm hM n b h d lam β := by
  obtain ⟨α,hα⟩ := comparisonVariableEndpointMinimum_attained hc hk hkc hm hM n hn b h hd hlam hlb hb hh hh0 hMc hne
  have hmin (β) : variableEndpointComparisonSweepObjective hc hk hkc hm hM n b h d lam α ≤
      variableEndpointComparisonSweepObjective hc hk hkc hm hM n b h d lam β := hα β
  have heq : variableEndpointComparisonSweepMinimum hc hk hkc hm hM n b h d lam=
      variableEndpointComparisonSweepObjective hc hk hkc hm hM n b h d lam α := by
    apply IsLeast.csInf_eq
    refine ⟨Set.mem_range_self α,?_⟩
    rintro _ ⟨β,rfl⟩
    exact hmin β
  exact ⟨α,heq.symm,fun β=>heq.symm ▸ hmin β⟩

theorem variableEndpointComparisonSweepMinimum_lipschitz (n : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ) {d L : ℝ} (hd : d≠0) (hLb : L≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hMc : Continuous M)
    (hne : (inverseIntegralConstraints 0 0 k M).Nonempty) :
    LipschitzOnWith 1 (variableEndpointComparisonSweepMinimum hc hk hkc hm hM n b h d) (Icc (0:ℝ) L) := by
  apply WallSweep.minimum_lipschitzOn
    (fun lam α=>variableEndpointComparisonSweepObjective hc hk hkc hm hM n b h d lam α)
  · intro lam hlam
    exact variableEndpointComparisonSweepMinimum_attained hc hk hkc hm hM n hn b h hd hlam.1
      (hlam.2.trans hLb) hb hh hh0 hMc hne
  · intro α
    exact variableEndpointStrengthSweepObjective_lipschitz n hn b h _ hd hLb hb hh hh0
      ((comparisonSweepQuantile_monotone hc hk hkc hm hM α).monotoneOn _)
      (fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α u)
      (comparisonSweepQuantile_continuous hc hk hkc hm hM α)

theorem variableEndpointComparisonSweepMinimum_monotone (n : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ) {d L : ℝ} (hd : d≠0) (hLb : L≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hMc : Continuous M)
    (hne : (inverseIntegralConstraints 0 0 k M).Nonempty) :
    MonotoneOn (variableEndpointComparisonSweepMinimum hc hk hkc hm hM n b h d) (Icc (0:ℝ) L) := by
  intro lam hlam lam' hlam' hll
  obtain ⟨α,he,_⟩ := variableEndpointComparisonSweepMinimum_attained hc hk hkc hm hM n hn b h hd
    hlam'.1 (hlam'.2.trans hLb) hb hh hh0 hMc hne
  obtain ⟨_,_,hmin⟩ := variableEndpointComparisonSweepMinimum_attained hc hk hkc hm hM n hn b h hd
    hlam.1 (hlam.2.trans hLb) hb hh hh0 hMc hne
  exact (hmin α).trans ((variableEndpointStrengthSweepObjective_monotone n hn b h _ hd hLb hb hh hh0
    ((comparisonSweepQuantile_monotone hc hk hkc hm hM α).monotoneOn _)
    (fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α u)
    (comparisonSweepQuantile_continuous hc hk hkc hm hM α) hlam hlam' hll).trans_eq he)

theorem variableEndpointComparisonSweepMinimum_zero (n : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ) {d : ℝ} (hd : d≠0) (hb0 : 0≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hMc : Continuous M)
    (hne : (inverseIntegralConstraints 0 0 k M).Nonempty) :
    variableEndpointComparisonSweepMinimum hc hk hkc hm hM n b h d 0=
      realOrderedSKPathPressure n b h 0 := by
  obtain ⟨α,he,_⟩ := variableEndpointComparisonSweepMinimum_attained hc hk hkc hm hM n hn b h hd
    le_rfl hb0 hb hh hh0 hMc hne
  exact he.symm.trans (variableEndpointStrengthSweepObjective_zero n b h _ d)

def variableEndpointComparisonSweepCost (n : ℕ) (b h : ℝ → ℝ) (d lam : ℝ) : ℝ :=
  variableEndpointComparisonSweepMinimum hc hk hkc hm hM n b h d lam-
    realOrderedSKPathPressure n b h 0

theorem variableEndpointComparisonSweepCost_zero (n : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ) {d : ℝ} (hd : d≠0) (hb0 : 0≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hMc : Continuous M)
    (hne : (inverseIntegralConstraints 0 0 k M).Nonempty) :
    variableEndpointComparisonSweepCost hc hk hkc hm hM n b h d 0=0 := by
  unfold variableEndpointComparisonSweepCost
  rw [variableEndpointComparisonSweepMinimum_zero hc hk hkc hm hM n hn b h hd hb0 hb hh hh0 hMc hne,sub_self]

theorem variableEndpointComparisonSweepCost_lipschitz (n : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ) {d L : ℝ} (hd : d≠0) (hLb : L≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hMc : Continuous M)
    (hne : (inverseIntegralConstraints 0 0 k M).Nonempty) :
    LipschitzOnWith 1 (variableEndpointComparisonSweepCost hc hk hkc hm hM n b h d) (Icc (0:ℝ) L) := by
  have hboundProof := variableEndpointComparisonSweepMinimum_lipschitz hc hk hkc hm hM n hn b h hd hLb hb hh hh0 hMc hne
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro lam hlam lam' hlam'
  simpa only [variableEndpointComparisonSweepCost,Real.dist_eq,sub_sub_sub_cancel_right] using
    hboundProof.dist_le_mul lam hlam lam' hlam'

theorem variableEndpointComparisonSweepCost_monotone (n : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ) {d L : ℝ} (hd : d≠0) (hLb : L≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hMc : Continuous M)
    (hne : (inverseIntegralConstraints 0 0 k M).Nonempty) :
    MonotoneOn (variableEndpointComparisonSweepCost hc hk hkc hm hM n b h d) (Icc (0:ℝ) L) := by
  intro lam hlam lam' hlam' hll
  exact sub_le_sub_right
    (variableEndpointComparisonSweepMinimum_monotone hc hk hkc hm hM n hn b h hd hLb hb hh hh0 hMc hne hlam hlam' hll) _

theorem variableEndpointComparisonSweepCost_nonneg (n : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ) {d L lam : ℝ} (hd : d≠0) (hLb : L≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hMc : Continuous M)
    (hne : (inverseIntegralConstraints 0 0 k M).Nonempty) (hlam : lam∈Icc (0:ℝ) L) :
    0≤variableEndpointComparisonSweepCost hc hk hkc hm hM n b h d lam := by
  have hL : 0≤L := hlam.1.trans hlam.2
  have hboundProof := variableEndpointComparisonSweepCost_monotone hc hk hkc hm hM n hn b h hd hLb hb hh hh0 hMc hne
    (⟨le_rfl,hL⟩ : (0:ℝ)∈Icc (0:ℝ) L) hlam hlam.1
  rwa [variableEndpointComparisonSweepCost_zero hc hk hkc hm hM n hn b h hd (hL.trans hLb) hb hh hh0 hMc hne] at hboundProof

theorem variableEndpointComparisonSweepMinimum_ae_log_derivative_le (n : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ) {d L : ℝ} (hd : d≠0) (hL : 0<L) (hLb : L≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hMc : Continuous M)
    (hne : (inverseIntegralConstraints 0 0 k M).Nonempty) :
    ∀ᵐ lam ∂volume.restrict (Ioo (0:ℝ) L),
      ∃ α : inverseIntegralConstraints 0 0 k M,
        variableEndpointComparisonSweepObjective hc hk hkc hm hM n b h d lam α=
          variableEndpointComparisonSweepMinimum hc hk hkc hm hM n b h d lam ∧
        let R := comparisonSweepQuantile hc hk hkc hm hM α
        let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
        let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
        lam*deriv (variableEndpointComparisonSweepMinimum hc hk hkc hm hM n b h d) lam≤
          (1/4:ℝ)*(∫ u in (0:ℝ)..1,laplaceComparisonStrength d lam (R u)*
            ((orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
              (orderedPathS n bf hf u-R u)^2)) := by
  have hlip := variableEndpointComparisonSweepMinimum_lipschitz hc hk hkc hm hM n hn b h hd hLb hb hh hh0 hMc hne
  have hlip' : LipschitzOnWith 1 (variableEndpointComparisonSweepMinimum hc hk hkc hm hM n b h d)
      (uIcc (0:ℝ) L) := by simpa only [uIcc_of_le hL.le] using hlip
  have hac := hlip'.absolutelyContinuousOnInterval
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [hac.ae_differentiableAt] with lam hdiff hlam
  obtain ⟨α,hcontact,hmin⟩ := variableEndpointComparisonSweepMinimum_attained hc hk hkc hm hM n hn b h hd
    hlam.1.le (hlam.2.le.trans hLb) hb hh hh0 hMc hne
  have hbound : ∀ᶠ l in 𝓝 lam,
      variableEndpointComparisonSweepMinimum hc hk hkc hm hM n b h d l≤
        variableEndpointComparisonSweepObjective hc hk hkc hm hM n b h d l α := by
    filter_upwards [Icc_mem_nhds hlam.1 hlam.2] with l hl
    obtain ⟨_,_,hlmin⟩ := variableEndpointComparisonSweepMinimum_attained hc hk hkc hm hM n hn b h hd
      hl.1 (hl.2.trans hLb) hb hh hh0 hMc hne
    exact hlmin α
  have hq := comparisonSweepQuantile_monotone hc hk hkc hm hM α
  have hqb := fun u (_ : u∈Icc (0:ℝ) 1)=>comparisonSweepQuantile_bounds hc hk hkc hm hM α u
  have hqc := comparisonSweepQuantile_continuous hc hk hkc hm hM α
  have hder := variableEndpointStrengthSweepObjective_hasDerivAt n hn b h _ hd hLb hb hh hh0 (hq.monotoneOn _) hqb hqc hlam
  have hdiff' := hdiff (by rw [uIcc_of_le hL.le]; exact ⟨hlam.1.le,hlam.2.le⟩)
  have he := WallSweep.minimum_derivative_eq hcontact hbound hdiff'.hasDerivAt hder
  refine ⟨α,hcontact,?_⟩
  dsimp only
  rw [he,← hder.deriv]
  exact variableEndpointStrengthSweep_log_derivative_le n hn b h _ hd hLb hb hh hh0 (hq.monotoneOn _) hqb hqc hlam

theorem variableEndpointComparisonSweepCost_deriv_eq_minimum (n : ℕ) (b h : ℝ → ℝ) (d lam : ℝ) :
    deriv (variableEndpointComparisonSweepCost hc hk hkc hm hM n b h d) lam=
      deriv (variableEndpointComparisonSweepMinimum hc hk hkc hm hM n b h d) lam :=
  deriv_sub_const _

theorem variableEndpointComparisonSweepCost_ae_log_derivative_le (n : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ) {d L : ℝ} (hd : d≠0) (hL : 0<L) (hLb : L≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hMc : Continuous M)
    (hne : (inverseIntegralConstraints 0 0 k M).Nonempty) :
    ∀ᵐ lam ∂volume.restrict (Ioo (0:ℝ) L),
      ∃ α : inverseIntegralConstraints 0 0 k M,
        variableEndpointComparisonSweepObjective hc hk hkc hm hM n b h d lam α=
          variableEndpointComparisonSweepMinimum hc hk hkc hm hM n b h d lam ∧
        let R := comparisonSweepQuantile hc hk hkc hm hM α
        let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
        let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
        lam*deriv (variableEndpointComparisonSweepCost hc hk hkc hm hM n b h d) lam≤
          (1/4:ℝ)*(∫ u in (0:ℝ)..1,laplaceComparisonStrength d lam (R u)*
            ((orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
              (orderedPathS n bf hf u-R u)^2)) := by
  simp_rw [variableEndpointComparisonSweepCost_deriv_eq_minimum]
  exact variableEndpointComparisonSweepMinimum_ae_log_derivative_le hc hk hkc hm hM n hn b h hd hL hLb hb hh hh0 hMc hne

end
end OAI.SKFluctuations.LaplaceWindowFormalization
