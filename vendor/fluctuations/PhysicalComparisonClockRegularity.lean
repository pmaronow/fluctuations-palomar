module

public import PhysicalOverlapPathRegularity
public import ComparisonPhysicalGeometry

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

theorem comparisonSweepQuantile_lipschitz (α : inverseIntegralConstraints 0 0 k M) :
    LipschitzWith ⟨1/c,by positivity⟩ (comparisonSweepQuantile hc hk hkc hm hM α) := by
  have hq := constrainedQuantile_lipschitz zero_le_one hc hk hkc hm hM α
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := hq.dist_le_mul (projIcc 0 1 zero_le_one x) (projIcc 0 1 zero_le_one y)
  change dist (comparisonSweepQuantile hc hk hkc hm hM α x)
    (comparisonSweepQuantile hc hk hkc hm hM α y) ≤ (1/c)*
      dist (projIcc 0 1 zero_le_one x) (projIcc 0 1 zero_le_one y) at hh
  apply hh.trans
  change (1/c)*dist _ _ ≤ (1/c)*dist x y
  have hp := (LipschitzWith.projIcc zero_le_one).dist_le_mul x y
  change dist _ _ ≤ (1:ℝ)*dist x y at hp
  simpa only [one_mul] using mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 1/c)

theorem comparisonSweepStrength_lipschitz (α : inverseIntegralConstraints 0 0 k M)
    (d lam : ℝ) :
    ∃K,LipschitzWith K (fun u=>laplaceComparisonStrength d lam
      (comparisonSweepQuantile hc hk hkc hm hM α u)) := by
  obtain ⟨K,hK⟩ := (laplaceComparisonStrength_contDiff d lam).contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_Icc (0:ℝ) 1) isCompact_Icc
  refine ⟨K*⟨1/c,by positivity⟩,LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  have hh := hK.dist_le_mul _ (comparisonSweepQuantile_bounds hc hk hkc hm hM α x)
    _ (comparisonSweepQuantile_bounds hc hk hkc hm hM α y)
  have hq := (comparisonSweepQuantile_lipschitz hc hk hkc hm hM α).dist_le_mul x y
  change dist _ _ ≤ (1/c)*dist x y at hq
  apply hh.trans
  change (K:ℝ)*dist _ _ ≤ (K:ℝ)*(1/c)*dist x y
  convert mul_le_mul_of_nonneg_left hq K.coe_nonneg using 1 <;> ring

theorem actual_comparison_radius_overlap_lipschitz
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    {d lam : ℝ} (hd : d≠0) (hlam : 0 ≤ lam) (hlb : lam ≤ b 0)
    (α : inverseIntegralConstraints 0 0 k M) {a z : ℝ}
    (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1) (Kb : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>b (α.val.val r)) (Icc a z)) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(laplaceComparisonStrength d lam (R u)*R u).toNNReal
    ∃K,LipschitzOnWith K (fun r=>orderedPathS (n+1) bf hf (α.val.val r)) (Icc a z) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let g := laplaceComparisonStrength d lam
  let bf := fun u=>(b u-g (R u)).toNNReal
  let hf := fun u=>(g (R u)*R u).toNNReal
  have had := strengthSweep_clocks_admissible b R hd hlam hlb hb
    ((comparisonSweepQuantile_monotone hc hk hkc hm hM α).monotoneOn _)
    (fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α u)
  have hbf := toNNReal_monotoneOn had.1
  have hhf := toNNReal_monotoneOn had.2.1
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
  let K := Kb+Kg+Kf
  have hclock (j : FeatureIndex (n+1)) : LipschitzOnWith K
      (fun r=>(completedPathClock (n+1) bf hf (α.val.val r) j:ℝ)) (Icc a z) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hRx := comparisonSweepQuantile_inverse hc hk hkc hm hM α (hsub hx)
    have hRy := comparisonSweepQuantile_inverse hc hk hkc hm hM α (hsub hy)
    have hbnd := hparent.dist_le_mul x hx y hy
    have hgbnd := hg.dist_le_mul x (hsub hx) y (hsub hy)
    have hfbnd := hfLip.dist_le_mul x (hsub hx) y (hsub hy)
    cases j with
    | inl j=>
      change dist (hf (α.val.val x):ℝ) (hf (α.val.val y):ℝ) ≤ (K:ℝ)*dist x y
      simp only [hf,R,g] at ⊢
      rw [Real.coe_toNNReal _ (had.2.2.2 _ (α.val.property.1 x)),
        Real.coe_toNNReal _ (had.2.2.2 _ (α.val.property.1 y))]
      change dist (g (R (α.val.val x))*R (α.val.val x)) (g (R (α.val.val y))*R (α.val.val y)) ≤ _
      rw [show R (α.val.val x)=x from hRx,show R (α.val.val y)=y from hRy]
      dsimp only [K] at ⊢
      simp only [NNReal.coe_add] at ⊢
      exact hfbnd.trans (by nlinarith [Kb.coe_nonneg,Kg.coe_nonneg,dist_nonneg (x:=x) (y:=y)])
    | inr j=>
      change dist (bf (α.val.val x):ℝ) (bf (α.val.val y):ℝ) ≤ (K:ℝ)*dist x y
      simp only [bf,R,g] at ⊢
      rw [Real.coe_toNNReal _ (had.2.2.1 _ (α.val.property.1 x)),
        Real.coe_toNNReal _ (had.2.2.1 _ (α.val.property.1 y))]
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
      nlinarith [hdsub,Kf.coe_nonneg,dist_nonneg (x:=x) (y:=y)]
  exact ⟨_,physicalOrderedPathS_comp_lipschitzOn n dphys e bf hf hbf hhf α.val.val _ K hα hclock⟩

theorem actual_comparison_radius_overlap_absolutelyContinuous
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    {d lam : ℝ} (hd : d≠0) (hlam : 0 ≤ lam) (hlb : lam ≤ b 0)
    (α : inverseIntegralConstraints 0 0 k M) {a z : ℝ}
    (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1) (Kb : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>b (α.val.val r)) (Icc a z)) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(laplaceComparisonStrength d lam (R u)*R u).toNNReal
    AbsolutelyContinuousOnInterval (fun r=>orderedPathS (n+1) bf hf (α.val.val r)) a z := by
  obtain ⟨K,hK⟩ := actual_comparison_radius_overlap_lipschitz hc hk hkc hm hM n dphys e b hb
    hd hlam hlb α ha haz hz Kb hparent
  rw [←uIcc_of_le haz] at hK
  exact hK.absolutelyContinuousOnInterval
end
end OAI.SKFluctuations.LaplaceWindowFormalization
