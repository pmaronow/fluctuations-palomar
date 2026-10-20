module

public import ComparisonActualHighWallDeletedSiteSourcePrice

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_deleted_site_category_cubic_price
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
        ∀(i star U : ℕ) (seed : List NativeResourceMark)
          (st : NativeActualResourceState (Spin n×Bool) as i star),
        NativeActualResourceGenerated i star U seed st.generation st.tree st.term → i ≤ star → star<as.length →
        seed.length+st.generation≤degree →
        partitionPoint 0 as i≤Cmass*M.data.d → partitionPoint 0 as star≤Cmass*M.data.d →
        |(M.data.d⁻¹)^st.generation*actualGeneralFourCategoryContrast M.bf M.hf U st .deletedSite| ≤
          |st.term.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*M.data.d^3) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_deleted_site_source_cubic_price
    (D:=D) degree Bclock Cmass hCmass hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U seed st hP hi hs hdepth hmi hms
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target star
  have H0:=hj U i star st.generation seed st.tree st.term hP hdepth hi hs hmi hms
  have H1:=hj U i star st.generation seed g.tree (st.term.retarget 0) hP.retarget hdepth hi hs hmi hms
  have hterm : 0≤|st.term.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*M.data.d^3):=
    mul_nonneg (mul_nonneg (abs_nonneg _) (actual_resource_raw_scale_pos seed M.data.hd M.data.hd).le)
      (mul_nonneg hC.le (pow_nonneg M.data.hd.le 3))
  rw [actual_general_four_deleted_site_contrast_eq_resources M.bf M.hf U st
    (finiteCutMasses_ordered us hus jGrid),mul_sub]
  have Hring : (M.data.d⁻¹)^st.generation*((1/2:ℝ)*actualGeneralOriginalResourceDeletedSiteSource M.bf M.hf U (st.term.retarget 0))=
      (1/2:ℝ)*((M.data.d⁻¹)^st.generation*actualGeneralOriginalResourceDeletedSiteSource M.bf M.hf U (st.term.retarget 0)):=by ring
  rw [Hring]
  apply (abs_sub _ _).trans
  rw [abs_mul (1/2:ℝ),abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  change _≤|st.term.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*M.data.d^3) at H1
  nlinarith only [H0,H1,hterm]

end OAI.SKFluctuations.Cavity
