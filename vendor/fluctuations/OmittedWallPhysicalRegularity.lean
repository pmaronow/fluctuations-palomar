module

public import WallClockGeometry
public import OmittedConstrainedForwardGeometry
public import PhysicalOverlapPathRegularity

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Set Hierarchy
open scoped Topology NNReal
section
variable {rmin s c : ℝ} {k M : ℝ → ℝ}
variable (hr : rmin≤1) (hs1 : s≤1) (hc : 0<c)
variable (hk : ContinuousOn k (Icc rmin 1)) (hkc : ∀r∈Icc rmin 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)
variable (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)

theorem actual_wall_radius_overlap_lipschitz
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    {T ε θ τ d : ℝ} (hs : 0<s) (hτ : 0<τ) (hrmin : 0≤rmin)
    (hε : ε∈Ioo (0:ℝ) T) (hθ : θ∈Icc (0:ℝ) 1)
    (hdepsilon : d^2≤ε) (hginitial : g rmin=d^2)
    (hganti : AntitoneOn g (Icc rmin 1))
    (hgrmono : MonotoneOn (fun r=>g r*r) (Icc rmin 1))
    (hgbound : ∀r∈Icc rmin 1,g r≤d^2)
    (α : inverseIntegralConstraints rmin s k M) {a z : ℝ}
    (ha : rmin<a) (haz : a≤z) (hz : z≤1) :
    let bf := fun u=>(wallChangedMatrix hr hs1 hc hk hkc hm hM g hg.continuous T ε θ α u).toNNReal
    let hf := fun u=>(wallChangedField hr hs1 hc hk hkc hm hM g hg.continuous T ε θ τ d α u).toNNReal
    ∃K,LipschitzOnWith K (fun r=>orderedPathS (n+1) bf hf (α.val.val r)) (Icc a z) := by
  dsimp only
  let bf := fun u=>(wallChangedMatrix hr hs1 hc hk hkc hm hM g hg.continuous T ε θ α u).toNNReal
  let hf := fun u=>(wallChangedField hr hs1 hc hk hkc hm hM g hg.continuous T ε θ τ d α u).toNNReal
  have had := wall_changed_clocks_admissible hr hs1 hc hk hkc hm hM g hg.continuous
    hs hτ hrmin hε hθ hdepsilon hginitial hganti hgrmono hgbound α
  have hbf := toNNReal_monotoneOn had.1
  have hhf := toNNReal_monotoneOn had.2.1
  have hsub : Icc a z⊆Icc rmin 1 := Icc_subset_Icc ha.le hz
  have hα : ∀r∈Icc a z,α.val.val r∈Icc s 1 := by
    intro r hr'
    exact (inverseConstraintMap α ⟨r,hsub hr'⟩).property
  have hαpos : MapsTo α.val.val (Icc a z) (Ioc (0:ℝ) 1) :=
    fun r hr'=>⟨hs.trans_le (hα r hr').1,(hα r hr').2⟩
  have hq (r : ℝ) (hr' : r∈Icc a z) :
      (constrainedQuantile hr hc hk hkc hm hM α ⟨α.val.val r,hα r hr'⟩:ℝ)=r := by
    rw [←omittedSweepQuantile_eq hr ⟨hs.le,hs1⟩ hc hk hkc hm hM α (hα r hr')]
    exact omittedSweepQuantile_inverse hr ⟨hs.le,hs1⟩ hc hk hkc hm hM α (hsub hr')
  have hme (r : ℝ) (hr' : r∈Icc a z) :
      wallChangedMatrix hr hs1 hc hk hkc hm hM g hg.continuous T ε θ α (α.val.val r)=T-g r := by
    rw [wallChangedMatrix_on hr hs1 hc hk hkc hm hM g hg.continuous T ε θ α (hα r hr'),hq r hr']
  have hfe (r : ℝ) (hr' : r∈Icc a z) :
      wallChangedField hr hs1 hc hk hkc hm hM g hg.continuous T ε θ τ d α (α.val.val r)=g r*r := by
    rw [wallChangedField_on hr hs1 hc hk hkc hm hM g hg.continuous T ε θ τ d α (hα r hr'),hq r hr']
  obtain ⟨Kg,hgLip⟩ := hg.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_Icc rmin 1) isCompact_Icc
  obtain ⟨Kf,hfLip⟩ := (hg.mul contDiff_id).contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_Icc rmin 1) isCompact_Icc
  have hnonm (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
      0≤wallChangedMatrix hr hs1 hc hk hkc hm hM g hg.continuous T ε θ α u :=
    had.2.2.1.trans (had.1 (by norm_num) hu hu.1)
  have hnonf (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
      0≤wallChangedField hr hs1 hc hk hkc hm hM g hg.continuous T ε θ τ d α u :=
    had.2.2.2.trans (had.2.1 (by norm_num) hu hu.1)
  have hunit (r : ℝ) : α.val.val r∈Icc (0:ℝ) 1 := α.val.property.1 r
  have hclock (j : FeatureIndex (n+1)) : LipschitzOnWith (Kg+Kf)
      (fun r=>(completedPathClock (n+1) bf hf (α.val.val r) j:ℝ)) (Icc a z) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    cases j with
    | inl j=>
      change dist (hf (α.val.val x):ℝ) (hf (α.val.val y):ℝ)≤_
      rw [show (hf (α.val.val x):ℝ)=wallChangedField hr hs1 hc hk hkc hm hM g hg.continuous T ε θ τ d α (α.val.val x)
        from Real.coe_toNNReal _ (hnonf _ (hunit x)),
        show (hf (α.val.val y):ℝ)=wallChangedField hr hs1 hc hk hkc hm hM g hg.continuous T ε θ τ d α (α.val.val y)
        from Real.coe_toNNReal _ (hnonf _ (hunit y)),hfe x hx,hfe y hy]
      have hh := hfLip.dist_le_mul x (hsub hx) y (hsub hy)
      change dist (g x*x) (g y*y)≤(Kf:ℝ)*dist x y at hh
      apply hh.trans
      simp only [NNReal.coe_add]
      nlinarith [Kg.coe_nonneg,dist_nonneg (x:=x) (y:=y)]
    | inr j=>
      change dist (bf (α.val.val x):ℝ) (bf (α.val.val y):ℝ)≤_
      rw [show (bf (α.val.val x):ℝ)=wallChangedMatrix hr hs1 hc hk hkc hm hM g hg.continuous T ε θ α (α.val.val x)
        from Real.coe_toNNReal _ (hnonm _ (hunit x)),
        show (bf (α.val.val y):ℝ)=wallChangedMatrix hr hs1 hc hk hkc hm hM g hg.continuous T ε θ α (α.val.val y)
        from Real.coe_toNNReal _ (hnonm _ (hunit y)),hme x hx,hme y hy]
      have hh := hgLip.dist_le_mul x (hsub hx) y (hsub hy)
      have he : dist (T-g x) (T-g y)=dist (g x) (g y) := by
        simp only [Real.dist_eq]
        have he' : T-g x-(T-g y)=-(g x-g y) := by ring
        rw [he',abs_neg]
      rw [he]
      apply hh.trans
      simp only [NNReal.coe_add]
      nlinarith [Kf.coe_nonneg,dist_nonneg (x:=x) (y:=y)]
  exact ⟨_,physicalOrderedPathS_comp_lipschitzOn n dphys e bf hf hbf hhf α.val.val _ (Kg+Kf) hαpos hclock⟩

theorem actual_wall_radius_overlap_absolutelyContinuous
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    {T ε θ τ d : ℝ} (hs : 0<s) (hτ : 0<τ) (hrmin : 0≤rmin)
    (hε : ε∈Ioo (0:ℝ) T) (hθ : θ∈Icc (0:ℝ) 1)
    (hdepsilon : d^2≤ε) (hginitial : g rmin=d^2)
    (hganti : AntitoneOn g (Icc rmin 1))
    (hgrmono : MonotoneOn (fun r=>g r*r) (Icc rmin 1))
    (hgbound : ∀r∈Icc rmin 1,g r≤d^2)
    (α : inverseIntegralConstraints rmin s k M) {a z : ℝ}
    (ha : rmin<a) (haz : a≤z) (hz : z≤1) :
    let bf := fun u=>(wallChangedMatrix hr hs1 hc hk hkc hm hM g hg.continuous T ε θ α u).toNNReal
    let hf := fun u=>(wallChangedField hr hs1 hc hk hkc hm hM g hg.continuous T ε θ τ d α u).toNNReal
    AbsolutelyContinuousOnInterval (fun r=>orderedPathS (n+1) bf hf (α.val.val r)) a z := by
  obtain ⟨K,hK⟩ := actual_wall_radius_overlap_lipschitz hr hs1 hc hk hkc hm hM g hg
    n dphys e hs hτ hrmin hε hθ hdepsilon hginitial hganti hgrmono hgbound α ha haz hz
  rw [←uIcc_of_le haz] at hK
  exact hK.absolutelyContinuousOnInterval

end
end OAI.SKFluctuations.LaplaceWindowFormalization
