module

public import ActualComparisonPotential
public import MacroNegativeRegion

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

theorem comparisonSweepQuantile_inverse (α : inverseIntegralConstraints 0 0 k M)
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    comparisonSweepQuantile hc hk hkc hm hM α (α.val.val r)=r := by
  have hs := inverseConstraint_strictMonoOn hc hk hkc α.property
  have ha := α.val.property.1 r
  apply hs.injOn (comparisonSweepQuantile_bounds hc hk hkc hm hM α _) hr
  rw [comparisonSweepQuantile_eq hc hk hkc hm hM α ha]
  exact constrainedQuantile_spec zero_le_one hc hk hkc hm hM α ⟨α.val.val r,ha⟩

theorem comparisonSweep_density_nonneg (α : inverseIntegralConstraints 0 0 k M) (r : ℝ) :
    0≤deriv α.val.val r := α.val.property.2.deriv_nonneg

theorem orderedPathPair_zero (n : ℕ) (b h : ℝ → ℝ≥0) (P : Spin n → Spin n → ℝ) :
    orderedPathPair n b h P 0=0 := by
  simp [orderedPathPair,pathPairMoment]

theorem comparisonSweep_radius_moments (n : ℕ) (hn : 0<n) (b : ℝ → ℝ)
    {d lam : ℝ} (hd : d≠0) (hlam : 0≤lam) (hlb : lam≤b 0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (α : inverseIntegralConstraints 0 0 k M) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let S := fun r=>orderedPathS n bf hf (α.val.val r)
    let B := fun r=>orderedPathB n bf hf (α.val.val r)
    MonotoneOn S (Icc (0:ℝ) 1) ∧ MonotoneOn B (Icc (0:ℝ) 1) ∧
      (∀ r∈Icc (0:ℝ) 1,S r∈Icc (0:ℝ) 1 ∧ B r∈Icc ((S r)^2) 1) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(laplaceComparisonStrength d lam (R u)*R u).toNNReal
  have ha := strengthSweep_clocks_admissible b R hd hlam hlb hb
    ((comparisonSweepQuantile_monotone hc hk hkc hm hM α).monotoneOn _)
    (fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α u)
  have hbf := toNNReal_monotoneOn ha.1
  have hhf := toNNReal_monotoneOn ha.2.1
  have hstrict := inverseConstraint_strictMonoOn hc hk hkc α.property
  have hpos (r : ℝ) (hr : r∈Ioc (0:ℝ) 1) : α.val.val r∈Ioc (0:ℝ) 1 := by
    have hs := hstrict (by norm_num) ⟨hr.1.le,hr.2⟩ hr.1
    rw [α.property.1] at hs
    exact ⟨hs,(α.val.property.1 r).2⟩
  have hbounds (r : ℝ) (hr : r∈Icc (0:ℝ) 1) :
      orderedPathS n bf hf (α.val.val r)∈Icc (0:ℝ) 1 ∧
      orderedPathB n bf hf (α.val.val r)∈Icc ((orderedPathS n bf hf (α.val.val r))^2) 1 := by
    by_cases hr0 : r=0
    · subst r
      rw [α.property.1]
      simp only [orderedPathS,orderedPathB,orderedPathPair_zero]
      norm_num
    · have hs := orderedPath_SK_bounds n hn bf hf hbf hhf
        (hpos r ⟨lt_of_le_of_ne hr.1 (Ne.symm hr0),hr.2⟩)
      exact ⟨⟨hs.1,hs.2.1⟩,⟨hs.2.2.1,hs.2.2.2⟩⟩
  refine ⟨?_,?_,hbounds⟩
  · intro r hr t ht hrt
    by_cases hr0 : r=0
    · subst r
      change orderedPathS n bf hf (α.val.val 0)≤orderedPathS n bf hf (α.val.val t)
      rw [α.property.1]
      simp only [orderedPathS,orderedPathPair_zero]
      exact (hbounds t ht).1.1
    · exact (orderedPath_SK_monotone n hn bf hf hbf hhf).1
        (hpos r ⟨lt_of_le_of_ne hr.1 (Ne.symm hr0),hr.2⟩)
        (hpos t ⟨lt_of_lt_of_le (lt_of_le_of_ne hr.1 (Ne.symm hr0)) hrt,ht.2⟩)
        (α.val.property.2 hrt)
  · intro r hr t ht hrt
    by_cases hr0 : r=0
    · subst r
      change orderedPathB n bf hf (α.val.val 0)≤orderedPathB n bf hf (α.val.val t)
      rw [α.property.1]
      simp only [orderedPathB,orderedPathPair_zero]
      exact (sq_nonneg _).trans (hbounds t ht).2.1
    · exact (orderedPath_SK_monotone n hn bf hf hbf hhf).2
        (hpos r ⟨lt_of_le_of_ne hr.1 (Ne.symm hr0),hr.2⟩)
        (hpos t ⟨lt_of_lt_of_le (lt_of_le_of_ne hr.1 (Ne.symm hr0)) hrt,ht.2⟩)
        (α.val.property.2 hrt)

theorem comparisonSweep_mismatch_substitution (α : inverseIntegralConstraints 0 0 k M)
    (S : ℝ → ℝ) :
    (∫u in (0:ℝ)..1,(S u-comparisonSweepQuantile hc hk hkc hm hM α u)^2)=
      ∫r in Icc (0:ℝ) 1,deriv α.val.val r*(S (α.val.val r)-r)^2 := by
  exact macro_mass_defect_substitution
    (inverseIntegralConstraints_lipschitz hm hM α.property)
    (inverseConstraint_strictMonoOn hc hk hkc α.property)
    (inverseConstraint_image zero_le_one hm hM α)
    (fun r hr=>comparisonSweepQuantile_inverse hc hk hkc hm hM α hr)
    (Eventually.of_forall (fun r _=>comparisonSweep_density_nonneg α r))

include hc hk hkc hm hM in
theorem comparisonSweep_thermal_substitution (α : inverseIntegralConstraints 0 0 k M)
    (S B : ℝ → ℝ) :
    (∫u in (0:ℝ)..1,B u-(S u)^2)=
      ∫r in Icc (0:ℝ) 1,deriv α.val.val r*(B (α.val.val r)-(S (α.val.val r))^2) := by
  have himage := inverseConstraint_image zero_le_one hm hM α
  rw [intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc,
    ← himage,lipschitz_interval_integral_image zero_le_one
      (inverseIntegralConstraints_lipschitz hm hM α.property)
      (inverseConstraint_strictMonoOn hc hk hkc α.property).injOn,himage]
  apply setIntegral_congr_ae measurableSet_Icc
  filter_upwards [] with r _
  rw [abs_of_nonneg (comparisonSweep_density_nonneg α r)]

end
end OAI.SKFluctuations.LaplaceWindowFormalization
