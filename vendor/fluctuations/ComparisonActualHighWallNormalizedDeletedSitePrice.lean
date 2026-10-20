module

public import ComparisonActualHighWallResourceDeletedSitePrice
public import ComparisonActualGeneralResourceDeletedSiteReadout
public import ComparisonSignedCavityActualResourceScalarScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_normalized_resource_deleted_site_cubic_price
    (degree : ℕ) (Bclock Cmass : ℝ) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let center:=nativePhysicalResourceCenter n M.bf M.hf as
        ∀(U₀ U i star k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed k T P → seed.length+k≤degree →
          i ≤ star → star<as.length →
          partitionPoint 0 as i≤Cmass*M.data.d → partitionPoint 0 as star≤Cmass*M.data.d →
        ∀s t : T.Slot,
          |(M.data.d⁻¹)^k*nativeOriginalResourceSiteDeletedDifference P 0
            (finitePhysicalCavitySquareVariance n U₀ as b h 1 1) 0 U b h K center s t|≤
            |P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*M.data.d^3) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_resource_deleted_site_cubic_price
    (D:=D) (degree+1) Bclock Cmass hCmass hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro U₀ U i star k seed T P hP hdepth hi hs hmi hms s t
  have hdegree : P.resources.length≤degree+1:=by rw [hP.total_factor_depth];omega
  have HP:=hj U₀ U i star T P hdegree hi hs hmi hms s t
  have hnorm : 0<(M.data.d⁻¹)^k:=pow_pos (inv_pos.mpr M.data.hd) _
  rw [abs_mul,abs_of_pos hnorm]
  apply (mul_le_mul_of_nonneg_left HP hnorm.le).trans_eq
  calc
    (M.data.d⁻¹)^k*(C*|P.coefficient| *M.data.d^3*nativeResourceScale M.data.d M.data.d 1 P.resources)=
      C*|P.coefficient| *M.data.d^3*((M.data.d⁻¹)^k*nativeResourceScale M.data.d M.data.d 1 P.resources):=by ring
    _=C*|P.coefficient| *M.data.d^3*nativeResourceScale M.data.d M.data.d 1 seed:=by
      rw [hP.normalized_saved_scale M.data.d M.data.d 1 M.data.hd.ne',one_pow,mul_one]
    _=|P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*M.data.d^3):=by ring

end OAI.SKFluctuations.Cavity
