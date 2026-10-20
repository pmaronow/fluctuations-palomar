module

public import ComparisonActualHighWallMacroscopicAllMassChildFactory
public import ComparisonActualHighWallMacroscopicAllMassChildBandTransfer
public import ComparisonActualHighOnlyMacroscopicScalarCompactness
public import ComparisonMacroscopicUniformRadius

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Function
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 24000000
namespace ActualHighWallOverlapMinimum

theorem macro_all_mass_successful_child_literal_bad_witness_excluded_high_wall
    {beta : ℝ≥0} (hbeta : 0 < beta) (hT : 1 < (beta:ℝ)^2) :
    ∃lower upper : ℝ,0 < lower ∧ 0 < upper ∧
      ∀m delta cl cu Az C0 Ct D Bclock c0 : ℝ,
      0 < m → 0 < delta → 0 < C0 →
      ∀hc0 : 0 < c0,c0^2 < (beta:ℝ)^2 → cl ≤ lower → upper ≤ cu →
      ∀N : ℕ→ℕ,Tendsto N atTop atTop →
      ∀M : (n:ℕ)→ActualHighWallOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀xlo : ℝ,0 < xlo → (∀n,(M n).xs∈Icc xlo 1) →
      Tendsto (fun n=>(M n).data.s) atTop (𝓝 0) →
      Tendsto (fun n=>laplaceComparisonStrength (M n).data.d ((M n).data.d^2) ((M n).xs)/(M n).xs^2)
        atTop (𝓝 0) →
      Tendsto (fun n=>(M n).data.rmin) atTop (𝓝 0) →
      (∀ᶠn in atTop,(c0*(M n).xs)^2 ≤ (M n).data.b (M n).alpha 0) →
      Tendsto (fun n=>comparisonEndpointL1Cost ((beta:ℝ)^2) ((M n).data.b (M n).alpha) ((M n).data.h (M n).alpha)) atTop (𝓝 0) →
      (∀ᶠn in atTop,(M n).macroAllMassChildSweepCost hc0 ≤ ((N n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (N n+1) delta c0 (M n).data.d ((M n).data.d^2) ((M n).xs)) →
      ∀ᶠn in atTop,cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
        (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs := by
  classical
  obtain ⟨c,C,hc,hC,hscalar⟩ := scalar_reference_quantiles_uniform_global_band hbeta hT
  let cR := min c 1
  let CR := max C 1
  have hcR : 0 < cR := lt_min hc zero_lt_one
  have hCR : 1 ≤ CR := le_max_right _ _
  refine ⟨1/(16*CR),16/cR,by positivity,by positivity,?_⟩
  intro m delta cl cu Az C0 Ct D Bclock c0 hm hdelta hC0 hc0 hc0T
    hclmargin hcumargin N hN M xlo hxlo hxs hs hweak hr hreserve hcost hsuccess
  have hNplus : Tendsto (fun n=>N n+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hN
  have Hready : ∀ᶠn in atTop,
      (c0*(M n).xs)^2 ≤ (M n).data.b (M n).alpha 0 ∧
      (M n).macroAllMassChildSweepCost hc0 ≤ ((N n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (N n+1) delta c0 (M n).data.d ((M n).data.d^2) ((M n).xs) := by
    filter_upwards [hreserve,hsuccess] with n hr hsuc
    exact ⟨hr,hsuc⟩
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp Hready
  by_contra Hnot
  rw [eventually_atTop] at Hnot
  push Not at Hnot
  have Hbad (k : ℕ) : ∃n : ℕ,k ≤ n ∧ n0 ≤ n ∧
      (cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs → cu*(M n).xs < (M n).alpha.val.val (M n).xs) := by
    obtain ⟨n,hn,hbad⟩ := Hnot (max k n0)
    exact ⟨n,(le_max_left _ _).trans hn,(le_max_right _ _).trans hn,hbad⟩
  choose index hindex hindex0 hbad using Hbad
  have hindexlim : Tendsto index atTop atTop := tendsto_atTop_mono hindex tendsto_id
  let dim := fun n=>N (index n)+1
  let P := fun n=>M (index n)
  have hdim : Tendsto dim atTop atTop := hNplus.comp hindexlim
  have Hfactory (n : ℕ) : ∃a : ActualShiftedAllMassParentChildCall (dim n) delta,
      a.context=(P n).data.shiftedParentData ∧ HEq a.optimizer (P n).shiftedParentMinimum ∧
      a.R=(P n).data.wallRadius (P n).alpha ∧ a.childRadius=c0*(P n).xs ∧ a.childLam=(c0*(P n).xs)^2 ∧
      (∀u,a.context.b u-a.coefficient u=(P n).data.b (P n).alpha u) ∧
      (∀u,a.context.h u+a.coefficient u*a.R u=(P n).data.h (P n).alpha u) ∧
      a.err=(P n).macroAllMassChildSweepCost hc0 := by
    have hready := hn0 (index n) (hindex0 n)
    exact exists_actual_high_wall_macro_all_mass_child (P n) hc0 hready.1
  choose a hcontext hoptimizer hRcall hdchild hlchild hbchild hhchild herr using Hfactory
  have hq (n:ℕ):2 ≤ (dim n:ℝ)^delta := (P n).data.hq
  have hroomChild (n:ℕ):(a n).childRadius^2 ≤ (a n).context.b 0-(a n).coefficient 0 := by
    rw [hdchild n,hbchild n 0]
    exact (hn0 (index n) (hindex0 n)).1
  let Q (n:ℕ):ActualHighOnlyComparisonData (dim n) delta := (a n).zeroMassData (hq n) (hroomChild n)
  have hdQ (n:ℕ):(Q n).d=(a n).childRadius := rfl
  let qMin (n:ℕ):ActualHighOnlyComparisonMinimum (Q n) (a n).childLam := (a n).zeroMassMinimum (hq n) (hroomChild n)
  have hbQ (n:ℕ):(Q n).b=(P n).data.b (P n).alpha := funext (hbchild n)
  have hhQ (n:ℕ):(Q n).h=(P n).data.h (P n).alpha := funext (hhchild n)
  have hQcost : Tendsto (fun n=>comparisonEndpointL1Cost ((beta:ℝ)^2) (Q n).b (Q n).h)
      atTop (𝓝 0) := by
    simpa only [hbQ,hhQ,P,Function.comp_def] using hcost.comp hindexlim
  have hdQbound : ∀n,(Q n).d∈Icc (c0*xlo) c0 := by
    intro n
    change (a n).childRadius∈Icc (c0*xlo) c0
    rw [hdchild n]
    exact ⟨mul_le_mul_of_nonneg_left (hxs (index n)).1 hc0.le,
      by simpa using mul_le_mul_of_nonneg_left (hxs (index n)).2 hc0.le⟩
  have hlamQbound : ∀n,(a n).childLam∈Icc ((c0*xlo)^2) (c0^2) := by
    intro n
    rw [hlchild n]
    exact ⟨(sq_le_sq₀ (mul_nonneg hc0.le hxlo.le) (mul_nonneg hc0.le (P n).hxs.le)).mpr
        (by simpa only [hdQ n,hdchild n] using (hdQbound n).1),
      (sq_le_sq₀ (mul_nonneg hc0.le (P n).hxs.le) hc0.le).mpr
        (by simpa only [hdQ n,hdchild n] using (hdQbound n).2)⟩
  have hsQ : Tendsto (fun n=>(Q n).s) atTop (𝓝 0) := tendsto_const_nhds
  obtain ⟨r,phi,hphi,hR,hmin⟩ := exists_actual_high_only_macro_radius_scalar_minimizing_subseq hbeta hdelta dim hdim
    Q (fun n=>(a n).childLam) (fun n=>⟨(a n).hchildLam.le,(a n).hchildLd⟩) qMin
    (mul_pos hc0 hxlo) (sq_pos_of_pos (mul_pos hc0 hxlo)) hc0T hdQbound hlamQbound hsQ hQcost
  obtain ⟨x,hx,psi,hpsi,hxlim⟩ := isCompact_Icc.tendsto_subseq (fun n=>hxs (index (phi n)))
  let theta := phi ∘ psi
  have htheta : StrictMono theta := hphi.comp hpsi
  have hRtheta := hR.comp hpsi.tendsto_atTop
  have hZpoint : ∀u∈Ioo (0:ℝ) 1,Tendsto (fun n=>(a (theta n)).Z u) atTop (𝓝 (r.val u)) := by
    intro u _
    have hQR (n:ℕ):(Q n).R (qMin n).alpha u=(a n).Z u := rfl
    simpa only [theta,Function.comp_apply,ActualHighOnlyComparisonData.radiusProfile,hQR]
      using tendsto_pi_nhds.mp (tendsto_subtype_rng.mp hRtheta) u
  have hband : ∀u∈Ioo (0:ℝ) 1,cR*u ≤ r.val u ∧ r.val u ≤ CR*u := by
    intro u hu
    have H := hscalar r.val (r.property.2.monotoneOn _) (fun u _=>r.property.1 u) hmin u hu
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) hu.1.le).trans H.1,
      H.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hu.1.le)⟩
  have hweakP : Tendsto (fun n=>laplaceComparisonStrength (P n).data.d ((P n).data.d^2) ((P n).xs)/(P n).xs^2)
      atTop (𝓝 0) := hweak.comp hindexlim
  have hsP : Tendsto (fun n=>(P n).data.s) atTop (𝓝 0) := hs.comp hindexlim
  have hrP : Tendsto (fun n=>(P n).data.rmin) atTop (𝓝 0) := hr.comp hindexlim
  have hnum : ∀n,(a n).context.d ≤ D ∧ Real.sqrt (dim n:ℝ)*(a n).context.E ≤ (a n).context.d^2 ∧
      (dim n:ℝ)^(-(2:ℝ)/3+m)*(a n).context.d ≤ C0*(a n).context.E ∧
      comparisonLowerScale (dim n) (a n).context.E (a n).context.d ≤ (P n).xs := by
    intro n
    rw [hcontext n]
    exact ⟨(P n).hdD,(P n).hupper,(P n).hlower,(P n).hscale⟩
  have hsA : Tendsto (fun n=>(a n).context.s) atTop (𝓝 0) := by
    simpa only [hcontext,ActualHighWallData.shiftedParentData] using hsP
  have hrA : Tendsto (fun n=>(a n).context.r0) atTop (𝓝 0) := by
    simpa only [hcontext,ActualHighWallData.shiftedParentData] using hrP
  have hweakA : Tendsto (fun n=>(a n).e ((P n).xs)/(P n).xs^2) atTop (𝓝 0) := by
    simpa only [ActualShiftedAllMassParentChildCall.e,hcontext,ActualShiftedAllMassParentChildCall.lam,
      ActualHighWallData.shiftedParentData,ActualShiftedParentData.d] using hweakP
  have HfixedP := actual_shifted_allmass_successful_child_fixed_mass_agreement hm hdelta hC0 hc0 hxlo dim hdim a
    (fun n=>(P n).xs) (fun n=>hxs (index n)) hnum
    (Eventually.of_forall fun n=>⟨hdchild n,hlchild n,by
      change (a n).err ≤ (dim n:ℝ)^(20*delta)*actualChildErrorBudget (dim n) delta c0
        (a n).context.d (a n).context.lam (P n).xs
      rw [herr n,hcontext n]
      exact (hn0 (index n) (hindex0 n)).2⟩) hsA hrA hweakA
  have Hfixed : ∀left right eps width : ℝ,0 < left → left < right → right ≤ 1 →
      0 < eps → 0 < width → ∀ᶠn in atTop,
      volume (physicalPropagationDisagreementMassSet ((P (theta n)).data.wallRadius (P (theta n)).alpha)
        (a (theta n)).Z left right eps)<ENNReal.ofReal width := by
    intro left right eps width hleft hlr hright heps hwidth
    simpa only [hRcall] using
      htheta.tendsto_atTop.eventually (HfixedP left right eps width hleft hlr hright heps hwidth)
  have Horigin : ∀ᶠn in atTop,(P (theta n)).data.rmin ≤ (P (theta n)).xs := by
    filter_upwards [(hrP.comp htheta.tendsto_atTop).eventually (gt_mem_nhds hxlo)] with n hn
    exact hn.le.trans (hxs (index (theta n))).1
  have Hstrict := macro_inverse_profile_strict_band_of_fixed_allmass_child_agreement_high_wall (dim ∘ theta)
    (fun n=>P (theta n)) (fun n=>a (theta n)) hcR hCR r.val hZpoint hband
    ⟨hxlo.trans_le hx.1,hx.2⟩ (fun n=>(hxs (index (theta n))).2) hxlim Horigin
    (hsP.comp htheta.tendsto_atTop) Hfixed
  obtain ⟨n,hn⟩ := Hstrict.exists
  have hlower : cl*(P (theta n)).xs ≤ (P (theta n)).alpha.val.val (P (theta n)).xs :=
    (mul_le_mul_of_nonneg_right hclmargin (P (theta n)).hxs.le).trans hn.1.le
  have hupper : (P (theta n)).alpha.val.val (P (theta n)).xs ≤ cu*(P (theta n)).xs :=
    hn.2.le.trans (mul_le_mul_of_nonneg_right hcumargin (P (theta n)).hxs.le)
  exact (not_lt_of_ge hupper) (hbad (theta n) hlower)

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
