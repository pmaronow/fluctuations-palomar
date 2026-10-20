module

public import ComparisonSignedCavityCalibratedStarSubtreeProjection
public import ComparisonActualHighWallStarSubtreeProjection
public import ComparisonActualHighWallObservedCalibration

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_high_wall_calibrated_star_subtree_projection_fourth
    (Bclock Cmass : ℝ) (hCmass : 0 ≤ Cmass)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=M.data.d
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
          partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W →
        ∀(T : ClockTree (Spin n) tail) (s t : T.Slot),s≠t →
        ∀v : ℝ,W ≤ v →
          M.data.wallRadius M.alpha (partitionPoint 0 as (pre.length+mid.length+T.splitIndex s t))=v →
          M.data.wallRadius M.alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → M.z ≤ v/2 →
          let qs:=nativeStarSuffixClock n pre mid q
          (∫z,nativeSubtreeExteriorProjectionFourth n T s t (ClockTree.single tail) (fun _=>1)
            (ClockTree.singleSlot tail) qs qs (twinPrefixBRoot z) (twinPrefixDRoot z)
            ∂nativeTwinPrefixDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
              ((n:ℝ)/(n+1:ℕ))^4*(C*(n:ℝ)^(-eta)*savedProjectedScale M.xs W v)^4 ∧
          (∫z,nativeSubtreeExteriorProjectionFourth n T s t (ClockTree.single tail) (fun _=>1)
            (ClockTree.singleSlot tail) qs qs (exteriorForestStarRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
              ((n:ℝ)/(n+1:ℕ))^4*(C*(n:ℝ)^(-eta)*savedProjectedScale M.xs W v)^4 := by
  obtain ⟨Cr,hCr,H⟩:=eventually_actual_high_wall_star_subtree_projection_fourth
    Bclock Cmass (1/24) hCmass (by positivity)
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  refine ⟨2*(2*C0)^3*Real.sqrt Cr,by positivity,?_⟩
  filter_upwards [H,eventually_ge_atTop (2:ℕ)] with n hn hn2
  intro M hfixed L us hus hret hmesh
  filter_upwards [hn M L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut hmass T s t hst v hWv hvr hlow hz
  let W:=M.data.d
  have hW : 0<W:=M.data.hd
  have hv : 0<v:=hW.trans_le hWv
  have hv1 : v ≤ 1 := by
    rw [←hvr]
    exact (M.data.wallRadius_bounds M.alpha _).2
  obtain ⟨hcritical,hduration⟩:=M.observed_fixed_calibration_scales hn2 hm.le hC0 hWv hv1
  have Hfour:=hk pre mid tail hcut W (by rw [hfixed]) hmass T s t hst
    ((2*C0)*M.xs) v (by exact mul_pos (by positivity) M.hxs)
    (by rw [hfixed];exact hWv) hcritical hvr hlow hz hduration
  have he : 2*(n:ℝ)^(-eta)*savedWeightedExteriorScale ((2*C0)*M.xs) W v (Cr*W)=
      (2*(2*C0)^3*Real.sqrt Cr)*(n:ℝ)^(-eta)*savedProjectedScale M.xs W v := by
    rw [savedWeightedExteriorScale_scaled_raw hW hv hCr.le]
    ring
  simpa only [he] using Hfour

end OAI.SKFluctuations.Cavity
