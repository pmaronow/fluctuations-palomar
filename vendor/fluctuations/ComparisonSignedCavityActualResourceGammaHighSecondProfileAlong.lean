module

public import ComparisonSignedCavityInheritedResourceGammaHighSecondProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem actual_inherited_resource_gamma_high_second_profile_along
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccal : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass) (hCcal : 1 ≤ Ccal)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(T : ClockTree (Spin (dim n)×Bool) as) (i star U k : ℕ)
          (seed : List NativeResourceMark) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed k T P → seed.length+k ≤ degree →
          i ≤ star → star < U → U ≤ as.length → T.leaves ≤ rBound →
          partitionPoint 0 as i ≤ Cmass*(M n).xs → partitionPoint 0 as star ≤ Cmass*W n →
        let R:=nativeOriginalHighErrorEnvelope (dim n) U (M n).bf (M n).hf as (4*Cf+2*Temp) Temp
        |((W n)⁻¹)^k*nativeActualResourceGammaSecondRestoration (M n) U P true| ≤
          |P.coefficient| *C*nativeResourceScale (M n).xs (W n) 1 seed*(W n)^2*
            (T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_resource_gamma_high_second_profile
    (D:=D) degree rBound Bclock Temp Cf Cmass Ccal (1/2) (4+2*cu)
    hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt hCcal
    (by norm_num) (by norm_num) (by linarith) (by norm_num;linarith)
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/4))
  have HG : ∀ᶠn in atTop,(Az+1/cl)*(1+Cmass)*W n ≤ (1:ℝ)/8:=by
    have H:=hWlim.const_mul ((Az+1/cl)*(1+Cmass))
    simp only [mul_zero] at H
    exact H.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/8))
  refine ⟨C,hC,?_⟩
  filter_upwards [hdim.eventually HC,Hsource,hcompare,HW,HG] with n hn hs hc hw hg
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hx1 : (M n).xs ≤ 1:=by linarith
  intro L us hus hret hmesh
  filter_upwards [hn (M n) hs hx1 hc L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro T i star U k seed P hP hdepth hi hstar hU hT hmi hms
  have Hdegree : P.resources.length ≤ degree:=by rw [hP.total_factor_depth];exact hdepth
  rw [hcanonical] at hw hg hms ⊢
  exact hj T i star U k seed P hP Hdegree hi hstar hU hT
    (by norm_num at hw ⊢;exact hw) (by norm_num at hg ⊢;exact hg) hmi hms

end OAI.SKFluctuations.Cavity
