module

public import ComparisonActualHighOnlyMacroscopicScalarCompactness
public import ComparisonMacroscopicUniformRadius

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Function
open scoped Topology NNReal
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false

namespace ActualHighOnlyOverlapMinimum

theorem high_only_macro_inverse_profile_strict_band_at_moving_radius
    {m delta cl cu Az C0 Ct D Bclock cR CR x : ℝ}
    (dim : ℕ→ℕ)
    (a : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n) m delta cl cu Az C0 Ct D Bclock)
    (hcR : 0<cR) (hCR : 1≤CR) {r : boundedMassProfiles}
    (hr : Tendsto (fun n=>(a n).context.radiusProfile (a n).alpha) atTop (𝓝 r))
    (hband : ∀u∈Ioo (0:ℝ) 1,cR*u≤r.val u ∧ r.val u≤CR*u)
    (hx : x∈Ioc (0:ℝ) 1) (hxs : ∀n,(a n).xs≤1)
    (hxlim : Tendsto (fun n=>(a n).xs) atTop (𝓝 x))
    (hs : Tendsto (fun n=>(a n).context.s) atTop (𝓝 0)) :
    ∀ᶠn in atTop,(1/(16*CR))*(a n).xs<(a n).alpha.val.val (a n).xs ∧
      (a n).alpha.val.val (a n).xs<(16/cR)*(a n).xs := by
  have hxpos : 0<x:=hx.1
  have hxone : x≤1:=hx.2
  have hCRp : 0<CR:=zero_lt_one.trans_le hCR
  let v:=x/(4*CR)
  have hv : v∈Ioo (0:ℝ) 1 := by
    refine ⟨div_pos hxpos (by positivity),?_⟩
    apply (div_lt_one (by positivity : 0<4*CR)).mpr
    linarith
  have hrv : r.val v<x/2 := by
    have h:=(hband v hv).2
    have heq:CR*v=x/4:=by dsimp [v];field_simp
    rw [heq] at h
    linarith
  have hRvl:∀ᶠn in atTop,(a n).R v<x/2 :=
    (tendsto_pi_nhds.mp (tendsto_subtype_rng.mp hr) v).eventually (gt_mem_nhds hrv)
  have hxl:=hxlim.eventually (lt_mem_nhds (by linarith : x/2<x))
  have hxu:=hxlim.eventually (gt_mem_nhds (by linarith : x<2*x))
  have HsV:=hs.eventually (gt_mem_nhds hv.1)
  have hlower : ∀ᶠn in atTop,(1/(16*CR))*(a n).xs<(a n).alpha.val.val (a n).xs := by
    filter_upwards [hRvl,hxl,hxu,HsV] with n hRn hln hun hsn
    have hm : v≤(a n).alpha.val.val (a n).xs := by
      have H := (inverseConstraint_strictMonoOn (a n).context.hc (a n).context.hk
        (a n).context.hkc (a n).alpha.property).monotoneOn
        (omittedSweepQuantile_bounds zero_le_one
          ⟨(a n).context.hs.1,(a n).context.hs1⟩ (a n).context.hc
          (a n).context.hk (a n).context.hkc (a n).context.hm
          (a n).context.hM (a n).alpha v)
        ⟨(a n).hxs.le,hxs n⟩ (by linarith : (a n).R v≤(a n).xs)
      rw [omittedSweepQuantile_spec zero_le_one
        ⟨(a n).context.hs.1,(a n).context.hs1⟩ (a n).context.hc
        (a n).context.hk (a n).context.hkc (a n).context.hm
        (a n).context.hM (a n).alpha ⟨hsn.le,hv.2.le⟩] at H
      exact H
    have hstrict : (1/(16*CR))*(a n).xs<v := by
      rw [div_mul_eq_mul_div,one_mul]
      apply (div_lt_iff₀ (by positivity : 0<16*CR)).mpr
      have heq : v*(16*CR)=4*x:=by dsimp [v];field_simp;norm_num
      rw [heq]
      linarith
    exact hstrict.trans_le hm
  by_cases hxlarge : cR/4≤x
  · filter_upwards [hlower,hxl] with n hn hln
    refine ⟨hn,?_⟩
    have hunit:=((a n).alpha.val.property.1 (a n).xs).2
    have hgt : (1:ℝ)<(16/cR)*(a n).xs := by
      rw [div_mul_eq_mul_div]
      apply (lt_div_iff₀ hcR).mpr
      nlinarith
    exact hunit.trans_lt hgt
  · let w:=4*x/cR
    have hw : w∈Ioo (0:ℝ) 1 := by
      refine ⟨div_pos (by positivity) hcR,?_⟩
      apply (div_lt_one hcR).mpr
      have hh:=lt_of_not_ge hxlarge
      linarith
    have hrw : 2*x<r.val w := by
      have h:=(hband w hw).1
      have heq:cR*w=4*x:=by dsimp [w];field_simp
      rw [heq] at h
      linarith
    have hRwu:∀ᶠn in atTop,2*x<(a n).R w :=
      (tendsto_pi_nhds.mp (tendsto_subtype_rng.mp hr) w).eventually (lt_mem_nhds hrw)
    filter_upwards [hlower,hRwu,hxl,hxu,hs.eventually (gt_mem_nhds hw.1)]
      with n hn hRn hln hun hsn
    refine ⟨hn,?_⟩
    have hm : (a n).alpha.val.val (a n).xs≤w := by
      have H := (inverseConstraint_strictMonoOn (a n).context.hc (a n).context.hk
        (a n).context.hkc (a n).alpha.property).monotoneOn
        ⟨(a n).hxs.le,hxs n⟩
        (omittedSweepQuantile_bounds zero_le_one
          ⟨(a n).context.hs.1,(a n).context.hs1⟩ (a n).context.hc
          (a n).context.hk (a n).context.hkc (a n).context.hm
          (a n).context.hM (a n).alpha w)
        (by linarith : (a n).xs≤(a n).R w)
      rw [omittedSweepQuantile_spec zero_le_one
        ⟨(a n).context.hs.1,(a n).context.hs1⟩ (a n).context.hc
        (a n).context.hk (a n).context.hkc (a n).context.hm
        (a n).context.hM (a n).alpha ⟨hsn.le,hw.2.le⟩] at H
      exact H
    have hwstrict : w<(16/cR)*(a n).xs := by
      rw [div_mul_eq_mul_div]
      apply (lt_div_iff₀ hcR).mpr
      have heq:w*cR=4*x:=by dsimp [w];field_simp
      rw [heq]
      nlinarith
    exact hm.trans_lt hwstrict

theorem high_only_macro_literal_bad_witness_excluded_of_local_strength
    {beta : ℝ≥0} (hbeta : 0<beta) (hT : 1<(beta:ℝ)^2) :
    ∃lower upper : ℝ,0<lower ∧ 0<upper ∧
      ∀m delta cl cu Az C0 Ct D Bclock : ℝ,
      0<delta → cl≤lower → upper≤cu →
      ∀dim : ℕ→ℕ,Tendsto dim atTop atTop →
      ∀a : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n)
        m delta cl cu Az C0 Ct D Bclock,
      ∀eta xlo rho : ℝ,0<eta → 0<xlo → 0<rho →
      (∀n,(a n).xs∈Icc xlo 1) →
      (∀n,eta≤laplaceComparisonStrength (a n).context.d (a n).lam (a n).xs/(a n).xs^2) →
      (∀n,(a n).context.d^2≤(beta:ℝ)^2-rho) →
      Tendsto (fun n=>(a n).context.s) atTop (𝓝 0) →
      Tendsto (fun n=>comparisonEndpointL1Cost ((beta:ℝ)^2) (a n).b (a n).h)
        atTop (𝓝 0) →
      ∀ᶠn in atTop,cl*(a n).xs≤(a n).alpha.val.val (a n).xs ∧
        (a n).alpha.val.val (a n).xs≤cu*(a n).xs := by
  classical
  obtain ⟨c,C,hc,hC,hscalar⟩:=scalar_reference_quantiles_uniform_global_band hbeta hT
  let cR:=min c 1
  let CR:=max C 1
  have hcR : 0<cR:=lt_min hc zero_lt_one
  have hCR : 1≤CR:=le_max_right _ _
  refine ⟨1/(16*CR),16/cR,by positivity,by positivity,?_⟩
  intro m delta cl cu Az C0 Ct D Bclock hdelta hcl hcu dim hdim a eta xlo rho
    heta hxlo hrho hxs hstrength hgap hs hcost
  let s:=eta*xlo^2
  have hsPos : 0<s:=mul_pos heta (sq_pos_of_pos hxlo)
  have hlowerlam (n:ℕ) : s≤(a n).lam := by
    have hlocal:=(le_div_iff₀ (sq_pos_of_pos (a n).hxs)).mp (hstrength n)
    have hele:=laplaceComparisonStrength_le (a n).context.d (a n).hlam.le (a n).xs
    have hsmall : eta*xlo^2≤eta*(a n).xs^2 :=
      mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ hxlo.le (a n).hxs.le).mpr (hxs n).1) heta.le
    exact hsmall.trans (hlocal.trans hele)
  have hdRange (n:ℕ) : (a n).context.d∈Icc (Real.sqrt s) D := by
    refine ⟨?_,(a n).hdD⟩
    apply (sq_le_sq₀ (Real.sqrt_nonneg s) (a n).context.hd.le).mp
    rw [Real.sq_sqrt hsPos.le]
    exact (hlowerlam n).trans (a n).hld
  by_contra h
  rw [eventually_atTop] at h
  push Not at h
  choose N hN hbad using h
  have hNlim : Tendsto N atTop atTop:=tendsto_atTop_mono hN tendsto_id
  obtain ⟨r,phi,hphi,hR,hmin⟩:=exists_actual_high_only_macro_radius_scalar_minimizing_subseq
    hbeta hdelta (dim ∘ N) (hdim.comp hNlim)
    (fun n=>(a (N n)).context) (fun n=>(a (N n)).lam)
    (fun n=>(a (N n)).lam_mem) (fun n=>(a (N n)).optimizer)
    (Real.sqrt_pos.mpr hsPos) hsPos (by linarith : (beta:ℝ)^2-rho<(beta:ℝ)^2)
    (fun n=>hdRange (N n))
    (fun n=>⟨hlowerlam (N n),(a (N n)).hld.trans (hgap (N n))⟩)
    (hs.comp hNlim) (hcost.comp hNlim)
  · obtain ⟨x,hx,psi,hpsi,hxlim⟩:=isCompact_Icc.tendsto_subseq
      (fun n=>hxs (N (phi n)))
    let theta:=N ∘ (phi ∘ psi)
    have hRtheta:=hR.comp hpsi.tendsto_atTop
    have hband : ∀u∈Ioo (0:ℝ) 1,cR*u≤r.val u ∧ r.val u≤CR*u := by
      intro u hu
      have hh:=hscalar r.val (r.property.2.monotoneOn _)
        (fun u _=>r.property.1 u) hmin u hu
      exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) hu.1.le).trans hh.1,
        hh.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hu.1.le)⟩
    have hgood:=high_only_macro_inverse_profile_strict_band_at_moving_radius
      (dim ∘ theta) (fun n=>a (theta n)) hcR hCR hRtheta hband
      ⟨hxlo.trans_le hx.1,hx.2⟩ (fun n=>(hxs (theta n)).2) hxlim
      (hs.comp (hNlim.comp ((hphi.comp hpsi).tendsto_atTop)))
    obtain ⟨n,hn⟩:=hgood.exists
    have hleLower : cl*(a (theta n)).xs≤(a (theta n)).alpha.val.val (a (theta n)).xs :=
      (mul_le_mul_of_nonneg_right hcl (a (theta n)).hxs.le).trans hn.1.le
    have hleUpper : (a (theta n)).alpha.val.val (a (theta n)).xs≤cu*(a (theta n)).xs :=
      hn.2.le.trans (mul_le_mul_of_nonneg_right hcu (a (theta n)).hxs.le)
    exact (not_lt_of_ge hleUpper) (hbad (phi (psi n)) hleLower)

theorem high_only_macro_bad_test_strength_tendsto_zero
    {beta : ℝ≥0} (hbeta : 0<beta) (hT : 1<(beta:ℝ)^2) :
    ∃lower upper : ℝ,0<lower ∧ 0<upper ∧
      ∀m delta cl cu Az C0 Ct D Bclock : ℝ,
      0<delta → cl≤lower → upper≤cu →
      ∀dim : ℕ→ℕ,Tendsto dim atTop atTop →
      ∀a : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n)
        m delta cl cu Az C0 Ct D Bclock,
      ∀xlo rho : ℝ,0<xlo → 0<rho →
      (∀n,(a n).xs∈Icc xlo 1) →
      (∀n,(a n).context.d^2≤(beta:ℝ)^2-rho) →
      Tendsto (fun n=>(a n).context.s) atTop (𝓝 0) →
      Tendsto (fun n=>comparisonEndpointL1Cost ((beta:ℝ)^2) (a n).b (a n).h)
        atTop (𝓝 0) →
      (∀ᶠn in atTop,¬(cl*(a n).xs≤(a n).alpha.val.val (a n).xs ∧
        (a n).alpha.val.val (a n).xs≤cu*(a n).xs)) →
      Tendsto (fun n=>laplaceComparisonStrength (a n).context.d (a n).lam (a n).xs/
        (a n).xs^2) atTop (𝓝 0) := by
  classical
  obtain ⟨lower,upper,hlower,hupper,Hmacro⟩:=
    high_only_macro_literal_bad_witness_excluded_of_local_strength hbeta hT
  refine ⟨lower,upper,hlower,hupper,?_⟩
  intro m delta cl cu Az C0 Ct D Bclock hdelta hcl hcu dim hdim a xlo rho
    hxlo hrho hxs hgap hs hcost Hbad
  let f:=fun n=>laplaceComparisonStrength (a n).context.d (a n).lam (a n).xs/(a n).xs^2
  have hf (n:ℕ) : 0≤f n:=div_nonneg
    (laplaceComparisonStrength_pos (a n).context.d (a n).hlam (a n).xs).le
    (sq_nonneg _)
  have Hsmall : ∀eta : ℝ,0<eta → ∀ᶠn in atTop,f n<eta := by
    intro eta heta
    by_contra Hnone
    have Hfreq : ∃ᶠn in atTop,eta≤f n := by
      simpa only [Filter.Frequently,not_le] using Hnone
    obtain ⟨phi,hphi,Hphi⟩:=extraction_of_frequently_atTop Hfreq
    have Hgood:=Hmacro m delta cl cu Az C0 Ct D Bclock hdelta hcl hcu
      (dim ∘ phi) (hdim.comp hphi.tendsto_atTop)
      (fun n=>a (phi n)) eta xlo rho heta hxlo hrho
      (fun n=>hxs (phi n)) Hphi (fun n=>hgap (phi n))
      (hs.comp hphi.tendsto_atTop) (hcost.comp hphi.tendsto_atTop)
    obtain ⟨n,hn⟩:=(Hgood.and (hphi.tendsto_atTop.eventually Hbad)).exists
    exact hn.2 hn.1
  change Tendsto f atTop (𝓝 0)
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  filter_upwards [Hsmall eta heta] with n hn
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (hf n)] using hn

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
