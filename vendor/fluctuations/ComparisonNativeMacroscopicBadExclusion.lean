module

public import ComparisonNativeMacroscopicScalarCompactness
public import ComparisonMacroscopicUniformRadius
public import ComparisonNativeActualBadScaleMassTransfer

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Function
open scoped Topology NNReal
namespace NativeOverlapMinimum

theorem macro_inverse_profile_strict_band_at_moving_radius
    {m delta cl cu Az C0 Ct D Bclock cR CR x : ℝ}
    (dim : ℕ→ℕ)
    (a : (n:ℕ)→NativeOverlapMinimum (dim n) m delta cl cu Az C0 Ct D Bclock)
    (hcR : 0 < cR) (hCR : 1 ≤ CR)
    {r : boundedMassProfiles}
    (hr : Tendsto (fun n=>comparisonSweepRadiusProfile (a n).context.hc (a n).context.hk
      (a n).context.hkc (a n).context.hm (a n).context.hM (a n).alpha) atTop (𝓝 r))
    (hband : ∀u∈Ioo (0:ℝ) 1,cR*u ≤ r.val u ∧ r.val u ≤ CR*u)
    (hx : x∈Ioc (0:ℝ) 1) (hxs : ∀n,(a n).xs ≤ 1)
    (hxlim : Tendsto (fun n=>(a n).xs) atTop (𝓝 x)) :
    ∀ᶠn in atTop,(1/(16*CR))*(a n).xs < (a n).alpha.val.val (a n).xs ∧
      (a n).alpha.val.val (a n).xs < (16/cR)*(a n).xs := by
  have hxpos : 0 < x := hx.1
  have hxone : x ≤ 1 := hx.2
  have hCRp : 0 < CR := zero_lt_one.trans_le hCR
  let v := x/(4*CR)
  have hv : v∈Ioo (0:ℝ) 1 := by
    refine ⟨div_pos hx.1 (by positivity),?_⟩
    apply (div_lt_one (by positivity : 0 < 4*CR)).mpr
    linarith
  have hrv : r.val v < x/2 := by
    have h := (hband v hv).2
    have heq : CR*v=x/4 := by dsimp [v];field_simp
    rw [heq] at h
    linarith
  have hRvl := (tendsto_pi_nhds.mp (tendsto_subtype_rng.mp hr) v).eventually (gt_mem_nhds hrv)
  have hxl := hxlim.eventually (lt_mem_nhds (by linarith : x/2 < x))
  have hxu := hxlim.eventually (gt_mem_nhds (by linarith : x < 2*x))
  have hlower : ∀ᶠn in atTop,(1/(16*CR))*(a n).xs < (a n).alpha.val.val (a n).xs := by
    filter_upwards [hRvl,hxl,hxu] with n hRn hln hun
    have hm : v ≤ (a n).alpha.val.val (a n).xs :=
      ((a n).context.mass_le_profile_iff_radius_le (a n).alpha
        ⟨(a n).hxs.le,hxs n⟩ ⟨hv.1.le,hv.2.le⟩).mpr (by exact hRn.le.trans hln.le)
    have hstrict : (1/(16*CR))*(a n).xs < v := by
      rw [div_mul_eq_mul_div,one_mul]
      apply (div_lt_iff₀ (by positivity : 0 < 16*CR)).mpr
      have heq : v*(16*CR)=4*x := by dsimp [v];field_simp;norm_num
      rw [heq]
      linarith
    exact hstrict.trans_le hm
  by_cases hxlarge : cR/4 ≤ x
  · filter_upwards [hlower,hxl] with n hn hln
    refine ⟨hn,?_⟩
    have hunit := ((a n).alpha.val.property.1 (a n).xs).2
    have hgt : (1:ℝ) < (16/cR)*(a n).xs := by
      rw [div_mul_eq_mul_div]
      apply (lt_div_iff₀ hcR).mpr
      nlinarith
    exact hunit.trans_lt hgt
  · let w := 4*x/cR
    have hw : w∈Ioo (0:ℝ) 1 := by
      refine ⟨div_pos (by positivity) hcR,?_⟩
      apply (div_lt_one hcR).mpr
      have hh := lt_of_not_ge hxlarge
      linarith
    have hrw : 2*x < r.val w := by
      have h := (hband w hw).1
      have heq : cR*w=4*x := by dsimp [w];field_simp
      rw [heq] at h
      linarith
    have hRwu := (tendsto_pi_nhds.mp (tendsto_subtype_rng.mp hr) w).eventually (lt_mem_nhds hrw)
    filter_upwards [hlower,hRwu,hxl,hxu] with n hn hRn hln hun
    refine ⟨hn,?_⟩
    have hm : (a n).alpha.val.val (a n).xs ≤ w :=
      ((a n).context.profile_le_mass_iff_radius_le (a n).alpha
        ⟨(a n).hxs.le,hxs n⟩ ⟨hw.1.le,hw.2.le⟩).mpr (by exact hun.le.trans hRn.le)
    have hwstrict : w < (16/cR)*(a n).xs := by
      rw [div_mul_eq_mul_div]
      apply (lt_div_iff₀ hcR).mpr
      have heq : w*cR=4*x := by dsimp [w];field_simp
      rw [heq]
      nlinarith
    exact hm.trans_lt hwstrict

theorem macro_literal_bad_witness_excluded
    {β : ℝ≥0} (hβ : 0 < β) (hT : 1 < (β:ℝ)^2) :
    ∃lower upper : ℝ,0 < lower ∧ 0 < upper ∧
      ∀m delta cl cu Az C0 Ct D Bclock : ℝ,
      0 < delta → cl ≤ lower → upper ≤ cu →
      ∀dim : ℕ→ℕ,Tendsto dim atTop atTop →
      ∀a : (n:ℕ)→NativeOverlapMinimum (dim n) m delta cl cu Az C0 Ct D Bclock,
      ∀dlo dhi llo lhi xlo : ℝ,0 < dlo → 0 < llo → lhi < (β:ℝ)^2 → 0 < xlo →
      (∀n,(a n).context.d∈Icc dlo dhi) → (∀n,(a n).lam∈Icc llo lhi) →
      (∀n,(a n).xs∈Icc xlo 1) →
      Tendsto (fun n=>comparisonEndpointL1Cost ((β:ℝ)^2) (a n).b (a n).h) atTop (𝓝 0) →
      ∀ᶠn in atTop,cl*(a n).xs ≤ (a n).alpha.val.val (a n).xs ∧
        (a n).alpha.val.val (a n).xs ≤ cu*(a n).xs := by
  classical
  obtain ⟨c,C,hc,hC,hscalar⟩ := scalar_reference_quantiles_uniform_global_band hβ hT
  let cR := min c 1
  let CR := max C 1
  have hcR : 0 < cR := lt_min hc zero_lt_one
  have hCR : 1 ≤ CR := le_max_right _ _
  refine ⟨1/(16*CR),16/cR,by positivity,by positivity,?_⟩
  intro m delta cl cu Az C0 Ct D Bclock hdelta hcl hcu dim hdim a dlo dhi llo lhi xlo
    hdlo hllo hlhi hxlo hd hlam hxs hcost
  by_contra h
  rw [eventually_atTop] at h
  push Not at h
  choose N hN hbad using h
  have hNlim : Tendsto N atTop atTop := tendsto_atTop_mono (fun n=>hN n) tendsto_id
  obtain ⟨r,phi,hphi,hR,hmin⟩ := exists_macro_radius_scalar_minimizing_subseq hβ hdelta
    (dim ∘ N) (hdim.comp hNlim) (fun n=>a (N n)) hdlo hllo hlhi
    (fun n=>hd (N n)) (fun n=>hlam (N n)) (hcost.comp hNlim)
  obtain ⟨x,hx,psi,hpsi,hxlim⟩ := isCompact_Icc.tendsto_subseq
    (fun n=>hxs (N (phi n)))
  let theta := N ∘ (phi ∘ psi)
  have hRtheta := hR.comp hpsi.tendsto_atTop
  have hband : ∀u∈Ioo (0:ℝ) 1,cR*u ≤ r.val u ∧ r.val u ≤ CR*u := by
    intro u hu
    have hh := hscalar r.val (r.property.2.monotoneOn _) (fun u _=>r.property.1 u) hmin u hu
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) hu.1.le).trans hh.1,
      hh.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hu.1.le)⟩
  have hgood := macro_inverse_profile_strict_band_at_moving_radius (dim ∘ theta)
    (fun n=>a (theta n)) hcR hCR hRtheta hband ⟨hxlo.trans_le hx.1,hx.2⟩
    (fun n=>(hxs (theta n)).2) hxlim
  obtain ⟨n,hn⟩ := hgood.exists
  have hleLower : cl*(a (theta n)).xs ≤ (a (theta n)).alpha.val.val (a (theta n)).xs :=
    (mul_le_mul_of_nonneg_right hcl (a (theta n)).hxs.le).trans hn.1.le
  have hleUpper : (a (theta n)).alpha.val.val (a (theta n)).xs ≤ cu*(a (theta n)).xs :=
    hn.2.le.trans (mul_le_mul_of_nonneg_right hcu (a (theta n)).hxs.le)
  exact (not_lt_of_ge hleUpper) (hbad (phi (psi n)) hleLower)

theorem macro_literal_bad_witness_excluded_of_local_strength
    {β : ℝ≥0} (hβ : 0 < β) (hT : 1 < (β:ℝ)^2) :
    ∃lower upper : ℝ,0 < lower ∧ 0 < upper ∧
      ∀m delta cl cu Az C0 Ct D Bclock : ℝ,
      0 < delta → cl ≤ lower → upper ≤ cu →
      ∀dim : ℕ→ℕ,Tendsto dim atTop atTop →
      ∀a : (n:ℕ)→NativeOverlapMinimum (dim n) m delta cl cu Az C0 Ct D Bclock,
      ∀eta xlo rho : ℝ,0 < eta → 0 < xlo → 0 < rho →
      (∀n,(a n).xs∈Icc xlo 1) →
      (∀n,eta ≤ laplaceComparisonStrength (a n).context.d (a n).lam ((a n).xs)/(a n).xs^2) →
      (∀n,(a n).context.d^2 ≤ (β:ℝ)^2-rho) →
      Tendsto (fun n=>comparisonEndpointL1Cost ((β:ℝ)^2) (a n).b (a n).h) atTop (𝓝 0) →
      ∀ᶠn in atTop,cl*(a n).xs ≤ (a n).alpha.val.val (a n).xs ∧
        (a n).alpha.val.val (a n).xs ≤ cu*(a n).xs := by
  obtain ⟨lower,upper,hlower,hupper,hmacro⟩ := macro_literal_bad_witness_excluded hβ hT
  refine ⟨lower,upper,hlower,hupper,?_⟩
  intro m delta cl cu Az C0 Ct D Bclock hdelta hcl hcu dim hdim a eta xlo rho
    heta hxlo hrho hxs hstrength hgap hcost
  let s := eta*xlo^2
  have hs : 0 < s := mul_pos heta (sq_pos_of_pos hxlo)
  have hlowerlam (n : ℕ) : s ≤ (a n).lam := by
    have hlocal := (le_div_iff₀ (sq_pos_of_pos (a n).hxs)).mp (hstrength n)
    have hele := laplaceComparisonStrength_le (a n).context.d (a n).hlam.le ((a n).xs)
    have hsmall : eta*xlo^2 ≤ eta*(a n).xs^2 :=
      mul_le_mul_of_nonneg_left ((sq_le_sq₀ hxlo.le (a n).hxs.le).mpr (hxs n).1) heta.le
    exact hsmall.trans (hlocal.trans hele)
  apply hmacro m delta cl cu Az C0 Ct D Bclock hdelta hcl hcu dim hdim a
    (Real.sqrt s) D s ((β:ℝ)^2-rho) xlo (Real.sqrt_pos.mpr hs) hs
    (by linarith) hxlo _ _ hxs hcost
  · intro n
    refine ⟨?_,(a n).hdD⟩
    apply (sq_le_sq₀ (Real.sqrt_nonneg s) (a n).context.hd.le).mp
    rw [Real.sq_sqrt hs.le]
    exact (hlowerlam n).trans (a n).hld
  · intro n
    exact ⟨hlowerlam n,(a n).hld.trans (hgap n)⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
