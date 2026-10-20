module

public import ConcreteWallParameters

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem concreteWallPressure_step_of_actual_mean
    (n dim : ℕ) (e : Fin (dim+1) ≃ FeatureIndex (n+1))
    {T ε δ E d s A cutoff highError : ℝ}
    (hn1 : 1<((n+1:ℕ):ℝ)) (hlogn : 1 ≤ Real.log ((n+1:ℕ):ℝ))
    (hE : 0<E) (hd : 0<d) (hd1 : d ≤ 1) (hs : s∈Ioc (0:ℝ) (1/2))
    (hq : 2 ≤ ((n+1:ℕ):ℝ)^δ) (hu : comparisonSmallMass ((n+1:ℕ):ℝ) E ≤ d)
    (hε : ε∈Ioo 0 T) (hdepsilon : d^2 ≤ ε)
    (hcutoff : 0<cutoff) (hcutoff1 : cutoff ≤ 1) (hA : 0 ≤ A) :
    let N : ℝ := (n+1:ℕ)
    let rmin := concreteWallRadius N δ E d s
    let k := concreteWallFloor N δ E
    let M := concreteWallCap N δ E d
    let hN : 0<N := by positivity
    let hrBounds := concreteWallRadius_bounds hN hE hd hd1 hs.1.le hq hu
    let hr : rmin ≤ 1 := hrBounds.2.2.trans (by norm_num : (1/2:ℝ) ≤ 1)
    let hs1 : s ≤ 1 := hs.2.trans (by norm_num : (1/2:ℝ) ≤ 1)
    let c := k 1
    let hc : 0<c := comparisonFloor_pos hN (concreteWallSmallMass_pos hN hE) (by norm_num)
    let hk : ContinuousOn k (Icc rmin 1) := comparisonFloor_continuousOn (δ:=δ)
      hN (concreteWallSmallMass_pos hN hE) hrBounds.1.le
    let hkc : ∀ r∈Icc rmin 1,c ≤ k r := fun r hr => comparisonFloor_lower_on (δ:=δ)
      hN (concreteWallSmallMass_pos hN hE) hrBounds.1.le hr
    let hm : MonotoneOn M (Icc (0:ℝ) 1) := comparisonCap_monotoneOn (δ:=δ)
      hN (concreteWallSmallMass_pos hN hE).le (concreteWallConstraintLength_pos hN hE hd) hE hd.le
    let hM : 0 ≤ M 1 := comparisonCap_nonneg (δ:=δ) hN (concreteWallSmallMass_pos hN hE).le
      (concreteWallConstraintLength_pos hN hE hd) hE hd.le zero_le_one
    let g := laplaceComparisonStrength d (d^2)
    let hg := (laplaceComparisonStrength_contDiff d (d^2)).continuous
    (wallMinimumValue hr hs1 hc hk hkc hm hM g hg T ε
      (N^(-(10:ℝ))) d (n+1) 0 0  ≤  physicalShellPressure (n+1) T s ε+highError) →
    (∀ θ∈Ioo cutoff 1, ∀ α : inverseIntegralConstraints rmin s k M,
      wallObjective hr hs1 hc hk hkc hm hM g hg T ε θ (N^(-(10:ℝ))) d (n+1) 0 α =
        wallMinimumValue hr hs1 hc hk hkc hm hM g hg T ε (N^(-(10:ℝ))) d (n+1) 0 θ →
      ∀ u∈Ioo (0:ℝ) s, orderedPathS (n+1)
        (fun v => (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α v).toNNReal)
        (fun v => (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ (N^(-(10:ℝ))) d α v).toNNReal) u<A) →
    physicalShellPressure (n+1) T s (PositiveLaplaceAssembly.wallStep T ε)-
      physicalShellPressure (n+1) T s ε  ≤ 
      highError+wallLowStrength T ε/4*(wallPhysicalCostU s A (n+1)+
        2*s*(wallLowRadius d rmin ε)^2)+
        (wallLowStrength T ε*wallPhysicalCostV T ε d rmin s A (n+1)/4)*(-Real.log cutoff)+
        wallLipschitzConstant T ε d rmin*cutoff := by
  dsimp only
  intro hcomparison hmean
  have hN : 0<((n+1:ℕ):ℝ) := by positivity
  have hr := concreteWallRadius_bounds hN hE hd hd1 hs.1.le hq hu
  have hgmono := laplaceComparisonStrength_monotonicities hd.ne' (sq_pos_of_pos hd) hr.1.le
  exact physicalShellPressure_wall_step_of_actual_mean _ _ _ _ _ _ _ _ _ n dim e hs.1 hn1 hlogn
    hε hd.ne' hr.1 hdepsilon (concreteWallStrength_initial hN hE hd hd1 hs.1.le hq hu)
    hgmono.1 hgmono.2 (fun r _ => (laplaceComparisonStrength_pos d (sq_pos_of_pos hd) r).le)
    (fun r _ => laplaceComparisonStrength_le d (sq_nonneg d) r)
    (concreteWallCap_continuous _ _ _ _)
    (concreteWallConstraints_nonempty hN hE hd hd1 ⟨hs.1.le,hs.2⟩ hq hu)
    hcutoff hcutoff1 hA hcomparison hmean

end OAI.SKFluctuations.LaplaceWindowFormalization
