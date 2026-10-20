module

public import ComparisonActualHighWallRestAllHighResampling
public import ComparisonActualHighWallRestPhysicalRaw
public import ComparisonSignedCavityActualRestBoundaryResampling

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_high_wall_rest_all_high_resampling
    (ell : ℕ) (Bclock Rmacro F : ℝ)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∀ᶠn : ℕ in atTop,
      ∀a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      a.xs=a.data.d →
      ∀(L : ℕ) (us : List PositiveMass),(∀v∈us,v.val ≤ 1) →
        (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ a.xs →
      ∀ᶠj : ℕ in atTop,
        let as:=finiteCutMasses us j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(a.bf (partitionPoint 0 as j):ℝ)) (fun _=>(a.hf (partitionPoint 0 as j):ℝ))
        let Q:=fun j=>restFiniteRealVariance n (q j)
        let W:=a.data.d
        ∀(low high : ℕ),high ≤ as.length→W ≤ Rmacro/2→
          4*W ≤ a.data.wallRadius a.alpha (partitionPoint 0 as high)→
          a.z ≤ min (a.data.wallRadius a.alpha (partitionPoint 0 as high)/8) (Rmacro/4)→
          a.data.wallRadius a.alpha (partitionPoint 0 as low) ≤ min (a.data.wallRadius a.alpha (partitionPoint 0 as high)/8) (Rmacro/4)→
          originalBoundaryResamplingMoment n (ell+1) as Q low high ≤
            (2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*a.xs) W
              (partitionPoint 0 as high))^(2*(ell+1)) := by
  obtain ⟨Cr,hCr,HR⟩:=eventually_actual_high_wall_rest_physical_raw_ratio (D:=D)
    ell Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  have HS:=eventually_actual_high_wall_rest_all_high_resampling_from_raw (delta:=delta) (Az:=Az) (Ct:=Ct) (D:=D)
    ell Bclock Rmacro F Cr hCr.le hm hgap hcl hcu hC0 hmacro hRhalf hFmass hFradius
  filter_upwards [HR,HS] with n hraw hsave
  intro M hwork L us hus hret hmesh
  filter_upwards [hraw M L us hus hret hmesh,hsave M hwork us hus] with k hk hksave
  dsimp only at hksave ⊢
  apply hksave
  rw [←native_sampled_rest_root_variance_eq n M.bf M.hf (finiteCutMasses us k)] at hk
  exact hk

end OAI.SKFluctuations.Cavity
