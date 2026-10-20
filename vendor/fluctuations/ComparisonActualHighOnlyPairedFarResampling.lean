module

public import ComparisonSignedCavityActualRestBoundaryResampling
public import ComparisonActualHighOnlyPairedFarPhysicalRaw
public import ComparisonActualHighOnlyPairedFarSavedSchedule

@[expose] public section
noncomputable section
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
theorem eventually_actual_minimum_inherited_rest_all_high_resampling_high_only
    (ell : ℕ) (Bclock Temp Cf Ccal Rmacro F : ℝ) (hCf : 0 ≤ Cf)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∀ᶠn : ℕ in atTop,
      ∀a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      a.data.s ≤ 1/4 → a.data.s ≤ a.xs →
        ActualHighOnlySmallSourceClocks a Temp Cf → a.xs ≤ 1 →
      a.xs^2 ≤ Ccal^2*laplaceComparisonStrength a.context.d a.lam a.xs→
      ∀(L : ℕ) (us : List PositiveMass),(∀v∈us,v.val ≤ 1) →
        (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ a.xs →
      ∀ᶠj : ℕ in atTop,
        let as:=finiteCutMasses us j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(a.bf (partitionPoint 0 as j):ℝ)) (fun _=>(a.hf (partitionPoint 0 as j):ℝ))
        let Q:=fun j=>restFiniteRealVariance n (q j)
        let W:=max a.xs (Real.sqrt (laplaceComparisonStrength a.context.d a.lam a.xs))
        ∀(low high : ℕ),high ≤ as.length→W ≤ Rmacro/2→
          4*W ≤ a.R (partitionPoint 0 as high)→
          a.z ≤ min (a.R (partitionPoint 0 as high)/8) (Rmacro/4)→
          a.R (partitionPoint 0 as low) ≤ min (a.R (partitionPoint 0 as high)/8) (Rmacro/4)→
          originalBoundaryResamplingMoment n (ell+1) as Q low high ≤
            (2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*a.xs) W
              (partitionPoint 0 as high))^(2*(ell+1)) := by
  obtain ⟨Cr,hCr,HR⟩:=eventually_actual_minimum_inherited_rest_physical_raw_ratio_high_only (D:=D)
    ell Bclock Temp Cf hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  have HS:=eventually_actual_rest_all_high_resampling_from_raw_high_only (delta:=delta) (Az:=Az) (Ct:=Ct) (D:=D)
    ell Bclock Ccal Rmacro F Cr hCr.le hm hgap hcl hcu hC0 hCcal hmacro hRhalf hFmass hFradius
  filter_upwards [HR,HS] with n hraw hsave
  intro M hs0 hsxs hsource hxs hcompare L us hus hret hmesh
  filter_upwards [hraw M hs0 hsxs hsource hxs L us hus hret hmesh,hsave M hcompare us hus] with k hk hksave
  dsimp only at hksave ⊢
  apply hksave
  rw [←native_sampled_rest_root_variance_eq n M.bf M.hf (finiteCutMasses us k)] at hk
  exact hk

end OAI.SKFluctuations.Cavity
