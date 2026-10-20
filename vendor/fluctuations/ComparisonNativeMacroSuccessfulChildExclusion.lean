module

public import ComparisonNativeMacroSuccessfulChildFactory
public import ComparisonNativeMacroChildEndpoint
public import ComparisonNativeMacroChildBandTransfer
public import ComparisonNativeMacroscopicScalarCompactness
public import ComparisonMacroscopicUniformRadius

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Function
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000
namespace NativeOverlapMinimum

theorem macro_successful_child_literal_bad_witness_excluded
    {beta : ℝ≥0} (hbeta : 0 < beta) (hT : 1 < (beta:ℝ)^2) :
    ∃lower upper : ℝ,0 < lower ∧ 0 < upper ∧
      ∀m delta cl cu Az C0 Ct D Bclock c0 : ℝ,
      0 < m → 0 < delta → 0 < cl → 0 < cu → 0 ≤ Az → 0 < C0 →
      ∀hc0 : 0 < c0,c0 ≤ 1 → c0^2 < (beta:ℝ)^2 → delta/4 < 3*m-99*delta →
      cl ≤ lower → upper ≤ cu →
      ∀N : ℕ→ℕ,Tendsto N atTop atTop →
      ∀M : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀xlo : ℝ,0 < xlo → (∀n,(M n).xs∈Icc xlo 1) →
      (∀ᶠn in atTop,comparisonConditionalScale (M n).context.N delta
        (M n).context.E (M n).lam ≤ (M n).xs) →
      Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam ((M n).xs)/(M n).xs^2)
        atTop (𝓝 0) →
      (∀ᶠn in atTop,(M n).lam+(c0*(M n).xs)^2 ≤ (M n).b 0) →
      (∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤(beta:ℝ)^2) →
      Tendsto (fun n=>comparisonEndpointL1Cost ((beta:ℝ)^2) (M n).b (M n).h) atTop (𝓝 0) →
      (∀ᶠn in atTop,(M n).macroChildSweepCost hc0 ≤ ((N n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (N n+1) delta c0 (M n).context.d (M n).lam ((M n).xs)) →
      ∀ᶠn in atTop,cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
        (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs := by
  classical
  obtain ⟨c,C,hc,hC,hscalar⟩ := scalar_reference_quantiles_uniform_global_band hbeta hT
  let cR := min c 1
  let CR := max C 1
  have hcR : 0 < cR := lt_min hc zero_lt_one
  have hCR : 1 ≤ CR := le_max_right _ _
  refine ⟨1/(16*CR),16/cR,by positivity,by positivity,?_⟩
  intro m delta cl cu Az C0 Ct D Bclock c0 hm hdelta hcl hcu hAz hC0 hc0 hc01 hc0T
    hmargin hclmargin hcumargin N hN M xlo hxlo hxs htarget hweak hroom htotal hcost hsuccess
  have hNplus : Tendsto (fun n=>N n+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hN
  have Hq : ∀ᶠn in atTop,2≤((N n+1:ℕ):ℝ)^delta :=
    (((tendsto_rpow_atTop hdelta).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).comp hNplus).eventually
      (eventually_ge_atTop 2)
  have Hparams := eventually_actual_successful_child_minimum_parameters hm hdelta hC0 hc0 hc01
    hmargin N hN M (fun n=>(M n).xs) (fun n=>(M n).hxs) htarget hweak
  have Hready : ∀ᶠn in atTop,(M n).lam+(c0*(M n).xs)^2≤(M n).b 0 ∧
      2≤((N n+1:ℕ):ℝ)^delta ∧
      ((N n+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*(c0*(M n).xs)≤
        C0*actualChildErrorBudget (N n+1) delta c0 (M n).context.d (M n).lam ((M n).xs) ∧
      (∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤(beta:ℝ)^2) ∧
      (M n).macroChildSweepCost hc0≤((N n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (N n+1) delta c0 (M n).context.d (M n).lam ((M n).xs) := by
    filter_upwards [hroom,Hq,Hparams,htotal,hsuccess] with n hr hq hp ht hs
    exact ⟨hr,hq,by simpa only [actualChildRadius] using hp.2.1,ht,hs⟩
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp Hready
  have Hchanged := changed_endpoint_cost_tendsto_zero_of_weak_bounded_call M
    (fun n=>(M n).xs) (fun n=>(M n).hxs) (Eventually.of_forall fun n=>(hxs n).2) hweak hcost
  by_contra Hnot
  rw [eventually_atTop] at Hnot
  push Not at Hnot
  have Hbad (k : ℕ) : ∃n : ℕ,k≤n ∧ n0≤n ∧
      (cl*(M n).xs≤(M n).alpha.val.val (M n).xs → cu*(M n).xs<(M n).alpha.val.val (M n).xs) := by
    obtain ⟨n,hn,hbad⟩ := Hnot (max k n0)
    exact ⟨n,(le_max_left _ _).trans hn,(le_max_right _ _).trans hn,hbad⟩
  choose index hindex hindex0 hbad using Hbad
  have hindexlim : Tendsto index atTop atTop := tendsto_atTop_mono hindex tendsto_id
  let dim := fun n=>N (index n)+1
  let P := fun n=>M (index n)
  have hdim : Tendsto dim atTop atTop := hNplus.comp hindexlim
  have Hfactory (n : ℕ) :
      ∃Q : NativeOverlapMinimum (dim n) m delta (cl/4) (4*cu) (4*(2/xlo)/cl) C0 1 1 ((beta:ℝ)^2),
      ∃a : NativeChildBarrierCall (dim n) delta,
      Q.context.d=c0*(P n).xs ∧ Q.lam=(c0*(P n).xs)^2 ∧ Q.xs=(P n).xs ∧
      Q.b=(fun u=>(P n).b u-laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u)) ∧
      Q.h=(fun u=>(P n).h u+laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u)*(P n).R u) ∧
      a.context.E=(P n).context.E ∧ a.context.d=(P n).context.d ∧ a.lam=(P n).lam ∧ a.R=(P n).R ∧
      a.childRadius=c0*(P n).xs ∧ a.childLam=(c0*(P n).xs)^2 ∧ a.Z=Q.R ∧
        a.err=(P n).macroChildSweepCost hc0 := by
    have hready := hn0 (index n) (hindex0 n)
    exact exists_actual_macro_child_at_parent (P n) hc0 hc01 hcl hcu hxlo (hxs (index n))
      hready.1 hready.2.1 hready.2.2.1 hready.2.2.2.1
  choose Q a hdQ hlamQ hxsQ hbQ hhQ hEcall hdcall hlamcall hRcall hdchild hlchild hZ herr using Hfactory
  have hQcost : Tendsto (fun n=>comparisonEndpointL1Cost ((beta:ℝ)^2) (Q n).b (Q n).h) atTop (𝓝 0) := by
    simpa only [hbQ,hhQ,P,Function.comp_def] using Hchanged.comp hindexlim
  have hdQbound : ∀n,(Q n).context.d∈Icc (c0*xlo) c0 := by
    intro n
    rw [hdQ n]
    exact ⟨mul_le_mul_of_nonneg_left (hxs (index n)).1 hc0.le,
      by simpa using mul_le_mul_of_nonneg_left (hxs (index n)).2 hc0.le⟩
  have hlamQbound : ∀n,(Q n).lam∈Icc ((c0*xlo)^2) (c0^2) := by
    intro n
    rw [hlamQ n]
    exact ⟨(sq_le_sq₀ (mul_nonneg hc0.le hxlo.le) (mul_nonneg hc0.le (P n).hxs.le)).mpr (by simpa only [hdQ n] using (hdQbound n).1),
      (sq_le_sq₀ (mul_nonneg hc0.le (P n).hxs.le) hc0.le).mpr (by simpa only [hdQ n] using (hdQbound n).2)⟩
  obtain ⟨r,phi,hphi,hR,hmin⟩ := exists_macro_radius_scalar_minimizing_subseq hbeta hdelta dim hdim Q
    (mul_pos hc0 hxlo) (sq_pos_of_pos (mul_pos hc0 hxlo)) hc0T hdQbound hlamQbound hQcost
  obtain ⟨x,hx,psi,hpsi,hxlim⟩ := isCompact_Icc.tendsto_subseq
    (fun n=>hxs (index (phi n)))
  let theta := phi ∘ psi
  have htheta : StrictMono theta := hphi.comp hpsi
  have hRtheta := hR.comp hpsi.tendsto_atTop
  have hZpoint : ∀u∈Ioo (0:ℝ) 1,Tendsto (fun n=>(a (theta n)).Z u) atTop (𝓝 (r.val u)) := by
    intro u _
    simpa only [hZ,theta,Function.comp_apply,comparisonSweepRadiusProfile] using tendsto_pi_nhds.mp (tendsto_subtype_rng.mp hRtheta) u
  have hband : ∀u∈Ioo (0:ℝ) 1,cR*u≤r.val u ∧ r.val u≤CR*u := by
    intro u hu
    have H := hscalar r.val (r.property.2.monotoneOn _) (fun u _=>r.property.1 u) hmin u hu
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) hu.1.le).trans H.1,
      H.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hu.1.le)⟩
  have hweakP : Tendsto (fun n=>laplaceComparisonStrength (P n).context.d (P n).lam ((P n).xs)/(P n).xs^2)
      atTop (𝓝 0) := hweak.comp hindexlim
  have Htwo := actual_minimum_successful_child_bounded_two_scale_agreement hm hdelta hcl hcu hAz hC0 hc0
    dim hdim P a (fun n=>(P n).xs) (fun _=>le_rfl)
    (Eventually.of_forall fun n=>(hxs (index n)).2)
    (fun n=>⟨hEcall n,hdcall n,hlamcall n,hRcall n⟩)
    (Eventually.of_forall fun n=>⟨hdchild n,hlchild n,by
      rw [herr n]
      exact (hn0 (index n) (hindex0 n)).2.2.2.2⟩) hweakP
  have Hfixed : ∀left right eps width : ℝ,0 < left → left < right → right≤1 →
      0 < eps → 0 < width → ∀ᶠn in atTop,
      volume (physicalPropagationDisagreementMassSet (P (theta n)).R (a (theta n)).Z left right eps)<ENNReal.ofReal width := by
    intro left right eps width hleft hlr hright heps hwidth
    have H := htheta.tendsto_atTop.eventually (Htwo 1 left right eps width zero_lt_one hleft hlr heps hwidth)
    filter_upwards [H] with n hn
    simpa only [one_mul,mul_one] using hn 1 (by simpa using (hxs (index (theta n))).2) (by simpa using hright)
  have Hstrict := macro_inverse_profile_strict_band_of_fixed_child_agreement (dim ∘ theta)
    (fun n=>P (theta n)) (fun n=>a (theta n)) hcR hCR r.val hZpoint hband
    ⟨hxlo.trans_le hx.1,hx.2⟩ (fun n=>(hxs (index (theta n))).2) hxlim Hfixed
  obtain ⟨n,hn⟩ := Hstrict.exists
  have hlower : cl*(P (theta n)).xs≤(P (theta n)).alpha.val.val (P (theta n)).xs :=
    (mul_le_mul_of_nonneg_right hclmargin (P (theta n)).hxs.le).trans hn.1.le
  have hupper : (P (theta n)).alpha.val.val (P (theta n)).xs≤cu*(P (theta n)).xs :=
    hn.2.le.trans (mul_le_mul_of_nonneg_right hcumargin (P (theta n)).hxs.le)
  exact (not_lt_of_ge hupper) (hbad (theta n) hlower)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
