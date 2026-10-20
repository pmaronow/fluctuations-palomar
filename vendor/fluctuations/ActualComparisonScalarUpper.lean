module

public import ActualComparisonVariationalLimit
public import ConcreteStrengthSweep

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem actualComparisonPressure_le_scalar (n : ℕ) (hn : 0 < n) {T : ℝ} (hT : 0 ≤ T)
    (e r : ℝ → ℝ) (he : AntitoneOn e (Icc (0:ℝ) 1))
    (heb : ∀ u ∈ Icc (0:ℝ) 1, e u ∈ Icc (0:ℝ) T)
    (her : MonotoneOn (fun u => e u*r u) (Icc (0:ℝ) 1))
    (hr : MonotoneOn r (Icc (0:ℝ) 1))
    (hrn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ r u) :
    pathCompensatedPressure n (fun _ => T) (fun _ => 0) e r 0 ≤
      physicalScalarQuantileValue n T r := by
  have hb : MonotoneOn (fun u => T-e u) (Icc (0:ℝ) 1) :=
    fun _ hu _ hv huv => sub_le_sub_left (he hu hv huv) T
  have hbn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ T-e u :=
    fun u hu => sub_nonneg.mpr (heb u hu).2
  have hfield : (fun u => e u*r u+(T-e u)*r u)=(fun u => T*r u) := by
    funext u; ring
  have hp := pathCompensatedPressure_lower n hn (fun u => T-e u) (fun u => e u*r u)
    (fun u => T-e u) r hbn hb her (hbn 0 (by norm_num))
    (mul_nonneg (heb 0 (by norm_num)).1 (hrn 0 (by norm_num)))
    (by simpa only [sub_self] using (show MonotoneOn (fun _ => (0:ℝ)) (Icc (0:ℝ) 1)
      from fun _ _ _ _ _ => le_rfl))
    (by rw [hfield]; exact fun _ hu _ hv huv => mul_le_mul_of_nonneg_left (hr hu hv huv) hT)
    (by simp) (by
      rw [show e 0*r 0+(T-e 0)*r 0=T*r 0 by ring]
      exact mul_nonneg hT (hrn 0 (by norm_num)))
    (by intro u hu v hv huv
        exact mul_le_mul (hb hu hv huv) (sq_le_sq₀ (hrn u hu) (hrn v hv) |>.mpr (hr hu hv huv))
          (sq_nonneg _) (hbn v hv)) 0
  have hi := joint_radius_penalty_integrable e r her hr (fun u hu => (heb u hu).1) hrn
  have hj := weighted_quantile_power_integrable (fun u => T-e u) r hb hr hbn hrn 2
  have hk := weighted_quantile_power_integrable (fun _ => T) r
    (fun _ _ _ _ _ => le_rfl) hr (fun _ _ => hT) hrn 2
  have heq : (∫u in (0:ℝ)..1,(T-e u)*r u^2)+(∫u in (0:ℝ)..1,e u*r u^2)=
      T*(∫u in (0:ℝ)..1,r u^2) := by
    rw [← intervalIntegral.integral_add hj hi,← intervalIntegral.integral_const_mul]
    congr 1
    funext u; ring
  unfold pathCompensatedPressure at hp ⊢
  simp only [sub_self,zero_add] at hp ⊢
  rw [hfield] at hp
  unfold physicalScalarQuantileValue
  linarith

def macroInverseInVariableClass {η Q : ℝ} (α : MacroInverseClass η Q)
    (k M : ℝ → ℝ) (hk : ContinuousOn k (Icc (0:ℝ) 1))
    (hm : MonotoneOn M (Icc (0:ℝ) 1))
    (hfloor : ∀ r ∈ Icc (0:ℝ) 1,k r ≤ η)
    (hcap : ∀ u ∈ Icc (0:ℝ) 1,Q ≤ M u) : inverseIntegralConstraints 0 0 k M := by
  refine ⟨α.val,α.property.1,α.property.2.1,?_⟩
  intro x hx y hy hxy
  have hsub : Icc x y ⊆ Icc (0:ℝ) 1 := Icc_subset_Icc hx.1 hy.2
  have hi : IntervalIntegrable (fun r => M (α.val.val r)) volume x y := by
    apply (show MonotoneOn (fun r => M (α.val.val r)) (uIcc x y) from ?_).intervalIntegrable
    intro r _ s _ hrs
    exact hm (α.val.property.1 r) (α.val.property.1 s) (α.val.property.2 hrs)
  have hl := intervalIntegral.integral_mono_on (μ := volume) hxy
    ((hk.mono hsub).intervalIntegrable_of_Icc hxy) (intervalIntegrable_const (c := η))
    (fun r hr => hfloor r (hsub hr))
  have hu := intervalIntegral.integral_mono_on hxy (intervalIntegrable_const (c := Q)) hi
    (fun r _ => hcap (α.val.val r) (α.val.property.1 r))
  exact ⟨hl.trans (α.property.2.2 x hx y hy hxy).1,
    (α.property.2.2 x hx y hy hxy).2.trans hu⟩

theorem macroInverseInVariableClass_quantile {η Q c : ℝ} (hη : 0 < η) (hQ : 1 < Q)
    (α : MacroInverseClass η Q) (k M : ℝ → ℝ) (hc : 0 < c)
    (hk : ContinuousOn k (Icc (0:ℝ) 1)) (hkc : ∀ r ∈ Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (hfloor : ∀ r ∈ Icc (0:ℝ) 1,k r ≤ η) (hcap : ∀ u ∈ Icc (0:ℝ) 1,Q ≤ M u)
    {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    comparisonSweepQuantile hc hk hkc hm hM (macroInverseInVariableClass α k M hk hm hfloor hcap) u=
      macroInverseQuantile hη hQ α u := by
  rw [comparisonSweepQuantile_eq hc hk hkc hm hM _ hu]
  apply (inverseConstraint_strictMonoOn hη continuousOn_const (fun _ _ => le_rfl) α.property).injOn
    (constrainedQuantile zero_le_one hc hk hkc hm hM _ ⟨u,hu⟩).property
    (macroInverseQuantile_bounds hη hQ α u)
  exact (constrainedQuantile_spec zero_le_one hc hk hkc hm hM
    (macroInverseInVariableClass α k M hk hm hfloor hcap) ⟨u,hu⟩).trans
    (macroInverseQuantile_spec hη hQ α hu).symm

section
variable {c : ℝ} {k M : ℝ → ℝ} (hc : 0 < c)
    (hk : ContinuousOn k (Icc (0:ℝ) 1)) (hkc : ∀ r ∈ Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparisonSweepQuantile_spec (α : inverseIntegralConstraints 0 0 k M)
    {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    α.val.val (comparisonSweepQuantile hc hk hkc hm hM α u)=u := by
  rw [comparisonSweepQuantile_eq hc hk hkc hm hM α hu]
  exact constrainedQuantile_spec zero_le_one hc hk hkc hm hM α ⟨u,hu⟩

theorem comparisonSweepInverseProfile_mem (α : inverseIntegralConstraints 0 0 k M) :
    α.val ∈ scalarProfiles := by
  constructor
  · intro r hr
    apply le_antisymm
    · simpa only [α.property.1] using α.val.property.2 hr.le
    · exact (α.val.property.1 r).1
  · intro r hr
    apply le_antisymm
    · exact (α.val.property.1 r).2
    · simpa only [α.property.2.1] using α.val.property.2 hr.le

theorem comparisonSweepQuantile_cdf_eq (α : inverseIntegralConstraints 0 0 k M)
    {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) :
    (quantileMassProfile (comparisonSweepQuantile hc hk hkc hm hM α)
      (fun u _ => comparisonSweepQuantile_bounds hc hk hkc hm hM α u)).val r=α.val.val r := by
  rw [quantileMassProfile_cdf _ ((comparisonSweepQuantile_monotone hc hk hkc hm hM α).monotoneOn _)]
  have he : {u : ParisiFinite.OrderPoint | comparisonSweepQuantile hc hk hkc hm hM α u ≤ r}=
      {u : ParisiFinite.OrderPoint | (u:ℝ) ≤ α.val.val r} := by
    ext u
    change comparisonSweepQuantile hc hk hkc hm hM α u ≤ r ↔ (u:ℝ) ≤ α.val.val r
    constructor
    · intro hu
      have hh := α.val.property.2 hu
      rwa [comparisonSweepQuantile_spec hc hk hkc hm hM α u.property] at hh
    · intro hu
      by_contra h
      have hh := inverseConstraint_strictMonoOn hc hk hkc α.property hr
        (comparisonSweepQuantile_bounds hc hk hkc hm hM α u) (lt_of_not_ge h)
      rw [comparisonSweepQuantile_spec hc hk hkc hm hM α u.property] at hh
      exact (not_lt.mpr hu) hh
  rw [he]
  exact uniformOrderMass_atMost (α.val.property.1 r)

theorem comparisonSweepQuantile_massProfile_eq (α : inverseIntegralConstraints 0 0 k M) :
    quantileMassProfile (comparisonSweepQuantile hc hk hkc hm hM α)
      (fun u _ => comparisonSweepQuantile_bounds hc hk hkc hm hM α u)=α.val := by
  apply Subtype.ext
  funext r
  by_cases hr0 : r < 0
  · rw [(quantileMassProfile_mem _ _).1 r hr0,(comparisonSweepInverseProfile_mem α).1 r hr0]
  · by_cases hr1 : 1 < r
    · rw [(quantileMassProfile_mem _ _).2 r hr1,(comparisonSweepInverseProfile_mem α).2 r hr1]
    · exact comparisonSweepQuantile_cdf_eq hc hk hkc hm hM α ⟨not_lt.mp hr0,not_lt.mp hr1⟩

theorem physicalScalarQuantileValue_comparisonSweep {β : ℝ≥0} (hβ : 0 < β)
    (n : ℕ) (hn : 0 < n) (α : inverseIntegralConstraints 0 0 k M) :
    physicalScalarQuantileValue n ((β:ℝ)^2) (comparisonSweepQuantile hc hk hkc hm hM α)=
      scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α.val := by
  rw [← scalar_physical_quantile_value n hn _ _
    ((comparisonSweepQuantile_monotone hc hk hkc hm hM α).monotoneOn _)
    (fun u _ => comparisonSweepQuantile_bounds hc hk hkc hm hM α u),
    comparisonSweepQuantile_massProfile_eq hc hk hkc hm hM α]

end

theorem eventually_comparison_scalar_reference_competitor {β : ℝ≥0} (hβ : 0 < β)
    {δ epsilon : ℝ} (hδ : 0 < δ) (heps : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ U L E d : ℝ, 0 < U → 0 < L → L ≤ U → 0 < E → 0 ≤ d →
      ∃ α : inverseIntegralConstraints 0 0 (comparisonFloor (n:ℝ) δ U)
        (comparisonCap (n:ℝ) δ U L E d),
        scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α.val ≤
          normalizedScalarParisiReference β+epsilon := by
  obtain ⟨j,hj,hj1⟩ := (eventually_macro_scalar_reference_competitor hβ heps).and
    (eventually_gt_atTop (1:ℕ)) |>.exists
  let hη := macroDensityFloor_pos (n := j) (by omega)
  let hQ := macroDensityCap_gt_one hj1
  obtain ⟨γ,hγ⟩ := hj hη hQ
  rw [macroInverseQuantile_massProfile_eq hη hQ γ] at hγ
  have hp : Tendsto (fun n : ℕ => (n:ℝ)^δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hi : Tendsto (fun n : ℕ => 1/(n:ℝ)^δ) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_div] using tendsto_inv_atTop_zero.comp hp
  have hcube : Tendsto (fun n : ℕ => 1/((n:ℝ)^δ)^3) atTop (𝓝 0) := by
    simpa only [div_pow,one_pow,zero_pow (by norm_num : (3:ℕ)≠0)] using hi.pow 3
  filter_upwards [hcube.eventually (eventually_le_nhds hη),hp.eventually (eventually_ge_atTop
    (macroDensityCap j)),eventually_gt_atTop (0:ℕ)] with n hfloor hcap hn
  intro U L E d hU hL hLU hE hd
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  let k := comparisonFloor (n:ℝ) δ U
  let M := comparisonCap (n:ℝ) δ U L E d
  have hk : ContinuousOn k (Icc (0:ℝ) 1) := comparisonFloor_continuousOn hn0 hU le_rfl
  have hm : MonotoneOn M (Icc (0:ℝ) 1) := comparisonCap_monotoneOn hn0 hU.le hL hE hd
  have hkη : ∀ r ∈ Icc (0:ℝ) 1,k r ≤ macroDensityFloor j :=
    fun r hr => (comparisonFloor_le_inv_cube hn0 hU hr.1).trans hfloor
  have hMQ : ∀ u ∈ Icc (0:ℝ) 1,macroDensityCap j ≤ M u :=
    fun u hu => hcap.trans (comparisonCap_ge hn0 hU hL hLU hE hd hu.1)
  exact ⟨macroInverseInVariableClass γ k M hk hm hkη hMQ,hγ⟩

theorem comparisonSweepObjective_bounds {β : ℝ≥0} (hβ : 0 < β)
    {c : ℝ} {k M : ℝ → ℝ} (hc : 0 < c)
    (hk : ContinuousOn k (Icc (0:ℝ) 1)) (hkc : ∀ r ∈ Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (n : ℕ) (hn : 0 < n) {d lam : ℝ} (hd : d ≠ 0) (hlam : 0 ≤ lam)
    (hlT : lam ≤ (β:ℝ)^2) (α : inverseIntegralConstraints 0 0 k M) :
    realOrderedSKPathPressure n (fun _ => (β:ℝ)^2) (fun _ => 0) 0 ≤
      comparisonSweepObjective hc hk hkc hm hM n (fun _ => (β:ℝ)^2) d lam α ∧
    comparisonSweepObjective hc hk hkc hm hM n (fun _ => (β:ℝ)^2) d lam α ≤
      scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α.val := by
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let e := fun u => laplaceComparisonStrength d lam (R u)
  have hR : MonotoneOn R (Icc (0:ℝ) 1) :=
    (comparisonSweepQuantile_monotone hc hk hkc hm hM α).monotoneOn _
  have hRb : ∀ u ∈ Icc (0:ℝ) 1,R u ∈ Icc (0:ℝ) 1 :=
    fun u _ => comparisonSweepQuantile_bounds hc hk hkc hm hM α u
  have hgs := laplaceComparisonStrength_monotonicities_nonneg hd hlam
  have he : AntitoneOn e (Icc (0:ℝ) 1) :=
    fun _ hu _ hv huv => hgs.1 (hRb _ hu) (hRb _ hv) (hR hu hv huv)
  have heb : ∀ u ∈ Icc (0:ℝ) 1,e u ∈ Icc (0:ℝ) ((β:ℝ)^2) :=
    fun u _ => ⟨laplaceComparisonStrength_nonneg d _ hlam,
      (laplaceComparisonStrength_le d hlam _).trans hlT⟩
  have her : MonotoneOn (fun u => e u*R u) (Icc (0:ℝ) 1) :=
    fun _ hu _ hv huv => hgs.2 (hRb _ hu) (hRb _ hv) (hR hu hv huv)
  have hbase := strengthSweep_clocks_admissible (fun _ => (β:ℝ)^2) R hd hlam hlT
    (fun _ _ _ _ _ => le_rfl) hR hRb
  have hpen : MonotoneOn (fun u => e u*R u^2) (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    have hp := mul_le_mul (her hu hv huv) (hR hu hv huv) (hRb u hu).1
      (mul_nonneg (heb v hv).1 (hRb v hv).1)
    nlinarith
  have hlo := pathCompensatedPressure_lower n hn (fun _ => (β:ℝ)^2) (fun _ => 0) e R
    (fun u hu => (heb u hu).1) (fun _ _ _ _ _ => le_rfl) (fun _ _ _ _ _ => le_rfl)
    (sq_nonneg _) le_rfl hbase.1 (by simpa only [zero_add] using hbase.2.1)
    (hbase.2.2.1 0 (by norm_num)) (by simpa only [zero_add] using hbase.2.2.2 0 (by norm_num)) hpen 0
  have hup := actualComparisonPressure_le_scalar n hn (sq_nonneg (β:ℝ)) e R he heb her hR
    (fun u hu => (hRb u hu).1)
  rw [physicalScalarQuantileValue_comparisonSweep hc hk hkc hm hM hβ n hn α] at hup
  constructor
  · simpa only [comparisonSweepObjective,strengthSweepObjective,pathCompensatedPressure,zero_add,e,R] using hlo
  · simpa only [comparisonSweepObjective,strengthSweepObjective,pathCompensatedPressure,zero_add,e,R] using hup

theorem eventually_concrete_comparison_minimum_upper_reference {β : ℝ≥0} (hβ : 0 < β)
    {δ epsilon : ℝ} (hδ : 0 < δ) (heps : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 0 < n) (U L E d lam : ℝ) (hU : 0 < U) (hL : 0 < L)
      (hLU : L ≤ U) (hE : 0 < E) (hd : 0 < d) (hlam : 0 ≤ lam) (hlT : lam ≤ (β:ℝ)^2),
      let k := comparisonFloor (n:ℝ) δ U
      let M := comparisonCap (n:ℝ) δ U L E d
      let hc := comparisonFloor_pos (by positivity : 0 < (n:ℝ)) hU (by norm_num : (0:ℝ) ≤ 1)
      let hk := comparisonFloor_continuousOn (by positivity : 0 < (n:ℝ)) hU (r₀ := 0) le_rfl
      let hkc := fun r (hr : r ∈ Icc (0:ℝ) 1) =>
        comparisonFloor_lower_on (by positivity : 0 < (n:ℝ)) hU le_rfl hr
      let hm := comparisonCap_monotoneOn (by positivity : 0 < (n:ℝ)) hU.le hL
        hE hd.le
      let hM := comparisonCap_nonneg (by positivity : 0 < (n:ℝ)) hU.le hL
        hE hd.le zero_le_one
      ∀ α : inverseIntegralConstraints 0 0 k M,
        (∀ γ : inverseIntegralConstraints 0 0 k M,
          comparisonSweepObjective hc hk hkc hm hM n (fun _ => (β:ℝ)^2) d lam α ≤
            comparisonSweepObjective hc hk hkc hm hM n (fun _ => (β:ℝ)^2) d lam γ) →
        comparisonSweepObjective hc hk hkc hm hM n (fun _ => (β:ℝ)^2) d lam α ≤
          normalizedScalarParisiReference β+epsilon := by
  filter_upwards [eventually_comparison_scalar_reference_competitor hβ hδ heps,
    eventually_gt_atTop (0:ℕ)] with n htrial hn
  intro hn' U L E d lam hU hL hLU hE hd hlam hlT
  dsimp only
  intro α hmin
  obtain ⟨γ,hγ⟩ := htrial U L E d hU hL hLU hE hd.le
  exact (hmin γ).trans ((comparisonSweepObjective_bounds hβ _ _ _ _ _ n hn hd.ne' hlam hlT γ).2.trans hγ)

end OAI.SKFluctuations.LaplaceWindowFormalization
