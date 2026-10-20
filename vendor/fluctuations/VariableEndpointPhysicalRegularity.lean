module

public import PhysicalComparisonClockRegularity
public import ComparisonFiniteHistory
public import VariableEndpointComparisonPotential

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 1000000
section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
theorem actual_variableEndpoint_radius_overlap_lipschitz
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    {d lam : ℝ} (hd : d≠0) (hlam : 0 ≤ lam) (hlb : lam ≤ b 0)
    (α : inverseIntegralConstraints 0 0 k M) {a z : ℝ}
    (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1) (Kb : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>b (α.val.val r)) (Icc a z))
    (Kh : ℝ≥0) (hfield : LipschitzOnWith Kh (fun r=>h (α.val.val r)) (Icc a z)) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    ∃K,LipschitzOnWith K (fun r=>orderedPathS (n+1) bf hf (α.val.val r)) (Icc a z) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let g := laplaceComparisonStrength d lam
  let bf := fun u=>(b u-g (R u)).toNNReal
  let hf := fun u=>(h u+g (R u)*R u).toNNReal
  have had := comparisonVariableEndpoint_clocks_admissible hc hk hkc hm hM b h hd hlam hlb hb hh hh0 α
  have hbf := toNNReal_monotoneOn had.1
  have hhf := toNNReal_monotoneOn had.2.1
  have hbn u (hu : u∈Icc (0:ℝ) 1) : 0 ≤ b u-g (R u) :=
    had.2.2.1.trans (had.1 (by norm_num) hu hu.1)
  have hhn u (hu : u∈Icc (0:ℝ) 1) : 0 ≤ h u+g (R u)*R u :=
    had.2.2.2.trans (had.2.1 (by norm_num) hu hu.1)
  have hsub : Icc a z⊆Icc (0:ℝ) 1 := Icc_subset_Icc ha.le hz
  have hα : MapsTo α.val.val (Icc a z) (Ioc (0:ℝ) 1) := by
    intro r hr
    have hh := inverseConstraint_strictMonoOn hc hk hkc α.property
      (by norm_num : (0:ℝ)∈Icc 0 1) (hsub hr) (ha.trans_le hr.1)
    rw [α.property.1] at hh
    exact ⟨hh,(α.val.property.1 r).2⟩
  obtain ⟨Kg,hg⟩ := (laplaceComparisonStrength_contDiff d lam).contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_Icc (0:ℝ) 1) isCompact_Icc
  obtain ⟨Kf,hfLip⟩ := ((laplaceComparisonStrength_contDiff d lam).mul contDiff_id).contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_Icc (0:ℝ) 1) isCompact_Icc
  let K := Kb+Kh+Kg+Kf
  have hclock (j : FeatureIndex (n+1)) : LipschitzOnWith K
      (fun r=>(completedPathClock (n+1) bf hf (α.val.val r) j:ℝ)) (Icc a z) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hRx := comparisonSweepQuantile_inverse hc hk hkc hm hM α (hsub hx)
    have hRy := comparisonSweepQuantile_inverse hc hk hkc hm hM α (hsub hy)
    have hbnd := hparent.dist_le_mul x hx y hy
    have hhbnd := hfield.dist_le_mul x hx y hy
    have hgbnd := hg.dist_le_mul x (hsub hx) y (hsub hy)
    have hfbnd := hfLip.dist_le_mul x (hsub hx) y (hsub hy)
    change dist (g x*x) (g y*y) ≤ (Kf:ℝ)*dist x y at hfbnd
    cases j with
    | inl j=>
      change dist (hf (α.val.val x):ℝ) (hf (α.val.val y):ℝ) ≤ (K:ℝ)*dist x y
      simp only [hf,R,g] at ⊢
      rw [Real.coe_toNNReal _ (hhn _ (α.val.property.1 x)),
        Real.coe_toNNReal _ (hhn _ (α.val.property.1 y))]
      change dist (h (α.val.val x)+g (R (α.val.val x))*R (α.val.val x)) (h (α.val.val y)+g (R (α.val.val y))*R (α.val.val y)) ≤ _
      rw [show R (α.val.val x)=x from hRx,show R (α.val.val y)=y from hRy]
      have hdsum : dist (h (α.val.val x)+g x*x) (h (α.val.val y)+g y*y) ≤
          dist (h (α.val.val x)) (h (α.val.val y))+dist (g x*x) (g y*y) := by
        simp only [Real.dist_eq]
        have he : h (α.val.val x)+g x*x-(h (α.val.val y)+g y*y)=
            (h (α.val.val x)-h (α.val.val y))+(g x*x-g y*y) := by ring
        rw [he]
        exact abs_add_le _ _
      dsimp only [K] at ⊢
      simp only [NNReal.coe_add] at ⊢
      nlinarith [hdsum,Kb.coe_nonneg,Kg.coe_nonneg,dist_nonneg (x:=x) (y:=y)]
    | inr j=>
      change dist (bf (α.val.val x):ℝ) (bf (α.val.val y):ℝ) ≤ (K:ℝ)*dist x y
      simp only [bf,R,g] at ⊢
      rw [Real.coe_toNNReal _ (hbn _ (α.val.property.1 x)),
        Real.coe_toNNReal _ (hbn _ (α.val.property.1 y))]
      change dist (b (α.val.val x)-g (R (α.val.val x))) (b (α.val.val y)-g (R (α.val.val y))) ≤ _
      rw [show R (α.val.val x)=x from hRx,show R (α.val.val y)=y from hRy]
      have hdsub : dist (b (α.val.val x)-g x) (b (α.val.val y)-g y) ≤
          dist (b (α.val.val x)) (b (α.val.val y))+dist (g x) (g y) := by
        simp only [Real.dist_eq]
        have he : b (α.val.val x)-g x-(b (α.val.val y)-g y)=
            (b (α.val.val x)-b (α.val.val y)) + -(g x-g y) := by ring
        rw [he]
        simpa only [abs_neg] using abs_add_le (b (α.val.val x)-b (α.val.val y)) (-(g x-g y))
      dsimp only [K] at ⊢
      simp only [NNReal.coe_add] at ⊢
      nlinarith [hdsub,Kf.coe_nonneg,Kh.coe_nonneg,dist_nonneg (x:=x) (y:=y)]
  exact ⟨_,physicalOrderedPathS_comp_lipschitzOn n dphys e bf hf hbf hhf α.val.val _ K hα hclock⟩

theorem actual_variableEndpoint_radius_overlap_absolutelyContinuous
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    {d lam : ℝ} (hd : d≠0) (hlam : 0 ≤ lam) (hlb : lam ≤ b 0)
    (α : inverseIntegralConstraints 0 0 k M) {a z : ℝ}
    (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1) (Kb : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>b (α.val.val r)) (Icc a z))
    (Kh : ℝ≥0) (hfield : LipschitzOnWith Kh (fun r=>h (α.val.val r)) (Icc a z)) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    AbsolutelyContinuousOnInterval (fun r=>orderedPathS (n+1) bf hf (α.val.val r)) a z := by
  obtain ⟨K,hK⟩ := actual_variableEndpoint_radius_overlap_lipschitz hc hk hkc hm hM n dphys e b h hb hh hh0
    hd hlam hlb α ha haz hz Kb hparent Kh hfield
  rw [←uIcc_of_le haz] at hK
  exact hK.absolutelyContinuousOnInterval

theorem actual_finiteHistory_radius_overlap_absolutelyContinuous
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (T ε s : ℝ) (ts : List ComparisonHistoryTerm)
    (hb : MonotoneOn (historyMatrixClock T ε s ts) (Icc (0:ℝ) 1))
    (hh : MonotoneOn (historyFieldClock ts) (Icc (0:ℝ) 1))
    (hh0 : 0 ≤ historyFieldClock ts 0)
    {d lam : ℝ} (hd : d≠0) (hlam : 0 ≤ lam)
    (hlb : lam ≤ historyMatrixClock T ε s ts 0)
    (α : inverseIntegralConstraints 0 0 k M) {a z : ℝ}
    (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1)
    (hbranch : α.val.val z < s ∨ s ≤ α.val.val a) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(historyMatrixClock T ε s ts u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(historyFieldClock ts u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    AbsolutelyContinuousOnInterval (fun r=>orderedPathS (n+1) bf hf (α.val.val r)) a z := by
  obtain ⟨Kb,hKb⟩ := historyMatrixClock_inverse_lipschitz hc hk hkc hm hM α T ε s ts ha.le haz hz hbranch
  obtain ⟨Kh,hKh⟩ := historyFieldClock_inverse_lipschitz hc hk hkc hm hM α ts ha.le haz hz
  exact actual_variableEndpoint_radius_overlap_absolutelyContinuous hc hk hkc hm hM n dphys e
    (historyMatrixClock T ε s ts) (historyFieldClock ts) hb hh hh0 hd hlam hlb α ha haz hz Kb hKb Kh hKh
end
end OAI.SKFluctuations.LaplaceWindowFormalization
