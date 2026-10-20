module

public import ComparisonSignedCavityCalibratedStarSubtreeProjection
public import ComparisonSignedCavityInheritedStarSubtreeProjection

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_calibrated_minimum_inherited_star_subtree_projection_fourth
    (Bclock Temp Cf Cmass Ccal : ℝ) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcal : 1 ≤ Ccal)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
          partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W →
        ∀(T : ClockTree (Spin n) tail) (s t : T.Slot),s≠t →
        ∀v : ℝ,W ≤ v →
          M.R (partitionPoint 0 as (pre.length+mid.length+T.splitIndex s t))=v →
          M.R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → M.z ≤ v/2 →
          let qs:=nativeStarSuffixClock n pre mid q
          (∫z,nativeSubtreeExteriorProjectionFourth n T s t (ClockTree.single tail) (fun _=>1)
            (ClockTree.singleSlot tail) qs qs (twinPrefixBRoot z) (twinPrefixDRoot z)
            ∂nativeTwinPrefixDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
              ((n:ℝ)/(n+1:ℕ))^4*(C*(n:ℝ)^(-eta)*savedProjectedScale M.xs W v)^4 ∧
          (∫z,nativeSubtreeExteriorProjectionFourth n T s t (ClockTree.single tail) (fun _=>1)
            (ClockTree.singleSlot tail) qs qs (exteriorForestStarRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
              ((n:ℝ)/(n+1:ℕ))^4*(C*(n:ℝ)^(-eta)*savedProjectedScale M.xs W v)^4 := by
  have hCcal0 : 0<Ccal:=zero_lt_one.trans_le hCcal
  obtain ⟨Cr,hCr,H⟩:=eventually_actual_minimum_inherited_star_subtree_projection_fourth
    Bclock Temp Cf Cmass (1/(24*Ccal^3)) hCf hCmass (by positivity)
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  refine ⟨2*(2*C0)^3*Real.sqrt Cr,by positivity,?_⟩
  filter_upwards [H,eventually_ge_atTop (2:ℕ)] with n hn hn2
  intro M hsource hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut hmass T s t hst v hWv hvr hlow hz
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
  have hW : 0<W:=M.hxs.trans_le (le_max_left _ _)
  have hv : 0<v:=hW.trans_le hWv
  have hv1 : v ≤ 1 := by
    rw [←hvr]
    exact (comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha _).2
  obtain ⟨hcritical,hduration⟩:=native_minimum_observed_calibration_scales
    M hn2 hm.le hC0 hCcal hcompare hWv hv1
  have Hfour:=hk pre mid tail hcut W (le_max_left _ _) hmass T s t hst
    ((2*C0)*M.xs) v (by exact mul_pos (by positivity) M.hxs)
    ((le_max_left _ _).trans hWv) hcritical hvr hlow hz hduration
  have he : 2*(n:ℝ)^(-eta)*savedWeightedExteriorScale ((2*C0)*M.xs) W v (Cr*W)=
      (2*(2*C0)^3*Real.sqrt Cr)*(n:ℝ)^(-eta)*savedProjectedScale M.xs W v := by
    rw [savedWeightedExteriorScale_scaled_raw hW hv hCr.le]
    ring
  simpa only [he] using Hfour

end OAI.SKFluctuations.Cavity
