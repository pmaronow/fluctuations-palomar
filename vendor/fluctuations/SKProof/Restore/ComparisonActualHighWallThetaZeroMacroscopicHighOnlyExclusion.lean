module

public import SKProof.Restore.ComparisonActualHighWallThetaZeroMacroscopicHighOnlyBandTransfer
public import ComparisonActualHighWallThetaZeroMacroscopicAllMassExclusion
public import ComparisonActualHighOnlyMacroscopicScalarCompactness
public import ComparisonMacroscopicUniformRadius

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Function
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 24000000
namespace ActualThetaZeroOverlapMinimum

theorem theta_zero_macro_high_only_successful_child_literal_bad_witness_excluded
    {beta : ℝ≥0} (hbeta : 0 < beta) (hT : 1 < (beta:ℝ)^2) :
    ∃lower upper : ℝ,0 < lower ∧ 0 < upper ∧
      ∀m delta cl cu Az C0 Ct D Bclock c0 : ℝ,
      0 < m → 0 < delta → 0 < C0 →
      ∀hc0 : 0 < c0,c0^2 < (beta:ℝ)^2 → cl ≤ lower → upper ≤ cu →
      ∀N : ℕ→ℕ,Tendsto N atTop atTop →
      ∀M : (n:ℕ)→ActualThetaZeroOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀xlo : ℝ,0 < xlo → (∀n,(M n).xs∈Icc xlo 1) →
      Tendsto (fun n=>(M n).data.s) atTop (𝓝 0) →
      Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam ((M n).xs)/(M n).xs^2)
        atTop (𝓝 0) →
      Tendsto (fun n=>(M n).data.rmin) atTop (𝓝 0) →
      (hgap:∀n,∀u∈Ico (0:ℝ) (M n).data.s,
        (M n).changedBare u+(c0*(M n).xs)^2≤(M n).changedBare (M n).data.s) →
      Tendsto (fun n=>comparisonEndpointL1Cost ((beta:ℝ)^2) ((M n).changedBare) ((M n).changedField)) atTop (𝓝 0) →
      (∀ᶠn in atTop,(M n).highOnlyChildSweepCost hc0 (hgap n) ≤ ((N n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (N n+1) delta c0 (M n).data.d (M n).lam ((M n).xs)) →
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
    hclmargin hcumargin N hN M xlo hxlo hxs hs hweak hr hgap hcost hsuccess
  have hNplus : Tendsto (fun n=>N n+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hN
  have Hready : ∀ᶠn in atTop,
      (M n).highOnlyChildSweepCost hc0 (hgap n) ≤ ((N n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (N n+1) delta c0 (M n).data.d (M n).lam ((M n).xs) := by
    exact hsuccess
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
  have Hfactory (n : ℕ) : ∃a : ActualShiftedParentChildCall (dim n) delta,
      a.context=(P n).data.thetaZeroShiftedParentData (P n).lam (P n).hlam (P n).hld ∧ HEq a.optimizer (P n).shiftedMinimum ∧
      a.R=(P n).data.wallRadius (P n).alpha ∧ a.childRadius=c0*(P n).xs ∧ a.childLam=(c0*(P n).xs)^2 ∧
      a.childData.s=(P n).data.s ∧ a.childData.b=(P n).changedBare ∧
      a.childData.h=(P n).changedField ∧ a.err=(P n).highOnlyChildSweepCost hc0 (hgap (index n)) := by
    let child:ActualHighOnlyComparisonData (dim n) delta:=
      (P n).highOnlyChildData hc0 (hgap (index n))
    have Hlam:(c0*(P n).xs)^2∈Icc (0:ℝ) (child.d^2):=
      ⟨(sq_pos_of_pos (mul_pos hc0 (P n).hxs)).le,le_rfl⟩
    obtain ⟨Q⟩:=child.exists_actual_minimum Hlam
    have Hcost:child.cost ((c0*(P n).xs)^2)=
        (P n).highOnlyChildSweepCost hc0 (hgap (index n)):=rfl
    have Hsuccess:child.objective ((c0*(P n).xs)^2) Q.alpha≤
        realOrderedSKPathPressure (dim n) child.b child.h 0+
          (P n).highOnlyChildSweepCost hc0 (hgap (index n)):=by
      change child.minimum ((c0*(P n).xs)^2)-
        realOrderedSKPathPressure (dim n) child.b child.h 0=_ at Hcost
      rw [Q.attained]
      linarith only [Hcost]
    let a:ActualShiftedParentChildCall (dim n) delta:={
      context:=(P n).data.thetaZeroShiftedParentData (P n).lam (P n).hlam (P n).hld
      optimizer:=(P n).shiftedMinimum
      childData:=child
      childLam:=(c0*(P n).xs)^2
      hchildLam:=sq_pos_of_pos (mul_pos hc0 (P n).hxs)
      hchildLd:=le_rfl
      childOptimizer:=Q
      sameInitialMass:=rfl
      childBareMatrix:=rfl
      childBareField:=rfl
      err:=(P n).highOnlyChildSweepCost hc0 (hgap (index n))
      childSuccess:=Hsuccess}
    exact ⟨a,rfl,HEq.rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  choose a hcontext hoptimizer hRcall hdchild hlchild hschild hbchild hhchild herr using Hfactory
  have hQcost : Tendsto (fun n=>comparisonEndpointL1Cost ((beta:ℝ)^2) (a n).childData.b (a n).childData.h)
      atTop (𝓝 0) := by
    simpa only [hbchild,hhchild,P,Function.comp_def] using hcost.comp hindexlim
  have hdQbound : ∀n,(a n).childData.d∈Icc (c0*xlo) c0 := by
    intro n
    change (a n).childRadius∈Icc (c0*xlo) c0
    rw [hdchild n]
    exact ⟨mul_le_mul_of_nonneg_left (hxs (index n)).1 hc0.le,
      by simpa using mul_le_mul_of_nonneg_left (hxs (index n)).2 hc0.le⟩
  have hlamQbound : ∀n,(a n).childLam∈Icc ((c0*xlo)^2) (c0^2) := by
    intro n
    rw [hlchild n]
    exact ⟨(sq_le_sq₀ (mul_nonneg hc0.le hxlo.le) (mul_nonneg hc0.le (P n).hxs.le)).mpr
        (by simpa only [hdchild n] using (hdQbound n).1),
      (sq_le_sq₀ (mul_nonneg hc0.le (P n).hxs.le) hc0.le).mpr
        (by simpa only [hdchild n] using (hdQbound n).2)⟩
  have hsQ : Tendsto (fun n=>(a n).childData.s) atTop (𝓝 0) := by
    simpa only [hschild,P,Function.comp_def] using hs.comp hindexlim
  obtain ⟨r,phi,hphi,hR,hmin⟩ := exists_actual_high_only_macro_radius_scalar_minimizing_subseq hbeta hdelta dim hdim
    (fun n=>(a n).childData) (fun n=>(a n).childLam) (fun n=>⟨(a n).hchildLam.le,(a n).hchildLd⟩)
    (fun n=>(a n).childOptimizer) (mul_pos hc0 hxlo) (sq_pos_of_pos (mul_pos hc0 hxlo)) hc0T
    hdQbound hlamQbound hsQ hQcost
  obtain ⟨x,hx,psi,hpsi,hxlim⟩ := isCompact_Icc.tendsto_subseq (fun n=>hxs (index (phi n)))
  let theta := phi ∘ psi
  have htheta : StrictMono theta := hphi.comp hpsi
  have hRtheta := hR.comp hpsi.tendsto_atTop
  have hZpoint : ∀u∈Ioo (0:ℝ) 1,Tendsto (fun n=>(a (theta n)).Z u) atTop (𝓝 (r.val u)) := by
    intro u _
    simpa only [theta,Function.comp_apply,ActualHighOnlyComparisonData.radiusProfile,ActualShiftedParentChildCall.Z]
      using tendsto_pi_nhds.mp (tendsto_subtype_rng.mp hRtheta) u
  have hband : ∀u∈Ioo (0:ℝ) 1,cR*u ≤ r.val u ∧ r.val u ≤ CR*u := by
    intro u hu
    have H := hscalar r.val (r.property.2.monotoneOn _) (fun u _=>r.property.1 u) hmin u hu
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) hu.1.le).trans H.1,
      H.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hu.1.le)⟩
  have hweakP : Tendsto (fun n=>laplaceComparisonStrength (P n).data.d (P n).lam ((P n).xs)/(P n).xs^2)
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
    simpa only [hcontext,ActualHighWallData.thetaZeroShiftedParentData] using hsP
  have hrA : Tendsto (fun n=>(a n).context.r0) atTop (𝓝 0) := by
    simpa only [hcontext,ActualHighWallData.thetaZeroShiftedParentData] using hrP
  have hweakA : Tendsto (fun n=>(a n).e ((P n).xs)/(P n).xs^2) atTop (𝓝 0) := by
    simpa only [ActualShiftedParentChildCall.e,hcontext,ActualShiftedParentChildCall.lam,
      ActualHighWallData.thetaZeroShiftedParentData,ActualShiftedParentData.d] using hweakP
  have HfixedP := theta_zero_successful_high_only_fixed_mass_agreement hm hdelta hC0 hc0 hxlo
    (N ∘ index) (hN.comp hindexlim) P a
    (fun n=>hxs (index n)) (fun n=>hcontext n) (fun n=>hRcall n)
    (Eventually.of_forall fun n=>⟨hdchild n,hlchild n,by
      exact (herr n).trans_le (hn0 (index n) (hindex0 n))⟩) hsP hrP hweakP
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
  have Hstrict := theta_zero_macro_inverse_profile_strict_band_of_fixed_high_only_child_agreement (dim ∘ theta)
    (fun n=>P (theta n)) (fun n=>a (theta n)) hcR hCR r.val hZpoint hband
    ⟨hxlo.trans_le hx.1,hx.2⟩ (fun n=>(hxs (index (theta n))).2) hxlim Horigin
    (hsP.comp htheta.tendsto_atTop) Hfixed
  obtain ⟨n,hn⟩ := Hstrict.exists
  have hlower : cl*(P (theta n)).xs ≤ (P (theta n)).alpha.val.val (P (theta n)).xs :=
    (mul_le_mul_of_nonneg_right hclmargin (P (theta n)).hxs.le).trans hn.1.le
  have hupper : (P (theta n)).alpha.val.val (P (theta n)).xs ≤ cu*(P (theta n)).xs :=
    hn.2.le.trans (mul_le_mul_of_nonneg_right hcumargin (P (theta n)).hxs.le)
  exact (not_lt_of_ge hupper) (hbad (theta n) hlower)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
