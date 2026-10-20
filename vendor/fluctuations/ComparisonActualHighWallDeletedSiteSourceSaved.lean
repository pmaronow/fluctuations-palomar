module

public import ComparisonActualHighWallNormalizedDeletedSiteSaved

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_deleted_site_source_saved_price
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
        ∀(U i star k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed k T P → seed.length+k≤degree →
          i ≤ star → star<as.length →
          partitionPoint 0 as i≤Cmass*M.data.d → partitionPoint 0 as star≤Cmass*M.data.d →
          |(M.data.d⁻¹)^k*actualGeneralOriginalResourceDeletedSiteSource M.bf M.hf U P| ≤
            |P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*((n+1:ℕ):ℝ)^(-m)*M.data.d^3) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_normalized_resource_deleted_site_saved_price
    (D:=D) degree Bclock Cmass hCmass hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro U i star k seed T P hP hdepth hi hs hmi hms
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  have HP:=hj U U i star k seed g.tree (P.retarget 0) hP.retarget hdepth hi hs hmi hms
    (g.embed P.live.test.target) g.mark
  have HF:=hj U U i star k seed g.tree (P.retarget 0).freeze hP.retarget.freeze hdepth hi hs hmi hms
    (g.embed P.live.test.target) g.mark
  simp only [NativeResourceTerm.freeze,abs_neg] at HF
  change _≤|P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*((n+1:ℕ):ℝ)^(-m)*M.data.d^3) at HP HF
  rw [actual_general_original_deleted_site_source_eq_two_resources M.bf M.hf U P
    (finiteCutMasses_ordered us hus jGrid),mul_neg,abs_neg,mul_add]
  apply ((abs_add_le _ _).trans (add_le_add HP HF)).trans_eq
  ring

end OAI.SKFluctuations.Cavity
