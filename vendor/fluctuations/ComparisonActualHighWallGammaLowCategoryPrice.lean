module

public import ComparisonActualHighWallResourceGammaLowPrice
public import ComparisonActualGeneralFourGammaRestorationReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_gamma_LOW_category_cubic_price
    (degree rBound : ℕ) (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U : ℕ) (seed : List NativeResourceMark)
          (st : NativeActualResourceState (Spin n×Bool) as i star),
        NativeActualResourceGenerated i star U seed st.generation st.tree st.term → i ≤ star → star < U →
        U ≤ as.length → st.tree.leaves ≤ rBound → seed.length+st.generation ≤ degree →
        partitionPoint 0 as i ≤ Cmass*M.data.d → partitionPoint 0 as star ≤ Cmass*M.data.d →
        partitionPoint 0 as U ≤ Ccut*M.data.d →
        |(M.data.d⁻¹)^st.generation*actualGeneralFourCategoryContrast M.bf M.hf U st .gammaLowRestoration| ≤
          |st.term.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*M.data.d^3) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_resource_gamma_LOW_cubic_price
    (D:=D) degree (rBound+1) Bclock Cmass Ccut hCmass hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U seed st hP hi hs hU hT hdepth hmi hms hcut
  let as:=finiteCutMasses us jGrid
  let g:=nativeFreshAtSlot st.tree 0 st.term.live.test.target star
  have hg : g.tree.leaves≤rBound+1:=by
    have H:=st.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem st.tree 0 st.term.live.test.target star)
    omega
  have H0:=hj i star U st.generation seed st.tree st.term hP hi hs hU (by omega) hdepth hmi hms hcut
  have H1:=hj i star U st.generation seed g.tree (st.term.retarget 0) hP.retarget hi hs hU hg hdepth hmi hms hcut
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hKm:=native_continuum_mixed_clock_monotone n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) as ho
  have hK0:=native_continuum_mixed_clock_nonneg n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) as ho
  have hterm : K as.length≤M.data.T:=
    (native_continuum_mixed_clock_terminal_le n M.bf M.hf
      (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) as ho).trans
      (M.data.total_clock_le M.alpha 1 (by norm_num))
  have HH:=scalar_boundary_hessian_uniform_bounds ho (relocatedClock U 0 K)
    (relocatedClock_monotone U (by norm_num : (0:ℝ)∈Icc 0 1) hKm hK0)
    (by simp [relocatedClock,show 0<U by omega])
    (B:=M.data.T) (by simpa [relocatedClock,not_lt.mpr hU] using hterm)
  have hchi0 : 0≤chi:=(Real.exp_pos (-4*M.data.T)).le.trans HH.1
  have hchi : |chi|≤1:=by rw [abs_of_nonneg hchi0];exact HH.2
  have Hdiff : |(M.data.d⁻¹)^st.generation*actualGeneralResourceGammaSecondRestoration M.bf M.hf U st.term false-
      (1/2:ℝ)*((M.data.d⁻¹)^st.generation*actualGeneralResourceGammaSecondRestoration M.bf M.hf U (st.term.retarget 0) false)|≤
      2*(|st.term.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*M.data.d^3)):=by
    apply (abs_sub _ _).trans
    rw [abs_mul (1/2:ℝ),abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
    have Hterm : 0≤|st.term.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*M.data.d^3):=
      mul_nonneg (mul_nonneg (abs_nonneg _) (actual_resource_raw_scale_pos seed M.data.hd M.data.hd).le)
        (mul_nonneg hC.le (pow_nonneg M.data.hd.le 3))
    change _≤|st.term.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*M.data.d^3) at H1
    linarith only [H0,H1,Hterm]
  have Heq:=actual_general_four_gamma_restoration_contrast_eq_resources M.bf M.hf U st ho false
  simp only [nativeActualGammaRestorationCategory,Bool.false_eq_true,ite_false] at Heq
  rw [Heq]
  have Hring : (M.data.d⁻¹)^st.generation*(chi*(actualGeneralResourceGammaSecondRestoration M.bf M.hf U st.term false-
      (1/2:ℝ)*actualGeneralResourceGammaSecondRestoration M.bf M.hf U (st.term.retarget 0) false))=
      chi*((M.data.d⁻¹)^st.generation*actualGeneralResourceGammaSecondRestoration M.bf M.hf U st.term false-
        (1/2:ℝ)*((M.data.d⁻¹)^st.generation*actualGeneralResourceGammaSecondRestoration M.bf M.hf U (st.term.retarget 0) false)):=by ring
  rw [Hring,abs_mul]
  exact (mul_le_mul hchi Hdiff (abs_nonneg _) zero_le_one).trans_eq (by ring)

end OAI.SKFluctuations.Cavity
