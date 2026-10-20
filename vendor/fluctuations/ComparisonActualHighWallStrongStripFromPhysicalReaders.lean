module

public import ComparisonActualHighWallScalarFactoryFromPhysicalReaders
public import ComparisonActualHighWallStrongStripFromRadiusL1
public import ComparisonActualHighWallOriginalTargetLiteralRadiusScalarGapAlong
public import ComparisonCriticalPositiveWallGapPrimitive
public import ComparisonNativeCavityConcentrationBareRadius

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 24000000

theorem eventually_actual_high_wall_strict_strip_of_physical_readers
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D) (hT : 0 < T)
    (hclSlack : cl < 2*T*Real.exp (-12*T))
    (hcuSlack :
      T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hTeq : ∀n,(M n).data.T=T)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,
      ((M n).hf u:ℝ)+((M n).bf u:ℝ)≤T)
    (d : ActualHighWallLocalScalarLimitData hT T M htotal)
    (hUV : d.U.mass =ᵐ[volume] d.V.mass)
    (s : NonnegativeMassProfile)
    (hspin : ∀r,Tendsto (fun n=>(M n).actualScaledRadiusSpin r)
      atTop (𝓝 (s.mass r)))
    {K : ℝ} (hK : 1≤K) :
    ∀ᶠn in atTop,∀r∈Icc (M n).data.d (K*(M n).data.d),
      cl*r<(M n).alpha.val.val r ∧
      (M n).alpha.val.val r<cu*r := by
  have hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0) := by
    apply hx.congr'
    exact Eventually.of_forall hfixed
  have hsRatioD : Tendsto (fun n=>(M n).data.s/(M n).data.d)
      atTop (𝓝 0) := by
    simpa only [hfixed] using hsRatio
  have hscalarEq (n : ℕ) :
      (M n).inheritedScalarMassProfile hT (htotal n)=
        (M n).data.scalarMassProfile (M n).alpha := by
    cases hTeq n
    rfl
  apply eventually_actual_high_wall_strict_strip_of_physical_radius_L1
    hm hdelta hmargin hcl hcu hAz hC0 hCt hD hT
    hclSlack hcuSlack dim hdim M hfixed hTeq hx hsRatio
    htotal d hUV s hspin
  · intro a b ha hab has _hbs hgap u hu v hv huv
    have hmass : 0 < d.V.mass ((a+b)/2) :=
      comparison_increment_support_positive_cdf_after d.V.monotone
        d.radius_negative_axis_zero has (by linarith)
    let ca := d.V.mass ((a+b)/2)/2
    have hca : 0 < ca := half_pos hmass
    have hu0 : 0 < u := ha.trans_lt hu.1
    have Hleft : ∀ᶠn in atTop,(M n).data.rmin < (M n).xs*u := by
      filter_upwards [d.origin_small.eventually (gt_mem_nhds hu0)] with n hn
      simpa only [mul_comm] using (div_lt_iff₀ (M n).hxs).mp hn
    have Hright : ∀ᶠn in atTop,(M n).xs*v ≤ 1 := by
      have H : Tendsto (fun n=>(M n).xs*v) atTop (𝓝 0) := by
        simpa only [zero_mul] using hx.mul_const v
      exact H.eventually (eventually_le_nhds zero_lt_one)
    have Hmass := critical_positive_wall_compact_gap_mass_band_along
      dim M d.V.mass d.V.monotone d.radius_inverse_cdf_limit
      hab hgap hmass hu hv
    have Hband : ∀ᶠn in atTop,(M n).data.rmin < (M n).xs*u ∧
        (M n).xs*v ≤ 1 ∧ ca*(M n).xs ≤
          (M n).alpha.val.val ((M n).xs*u) := by
      filter_upwards [Hleft,Hright,Hmass] with n hnleft hnright hnmass
      exact ⟨hnleft,hnright,(hnmass u ⟨le_rfl,huv.le⟩).1⟩
    have Hsource := actual_high_wall_original_target_literal_radius_scalar_gap_along
      Bclock hm hdelta hmargin hcl hcu hAz hC0 hCt hD huv.le hca hT
      dim hdim M hfixed hTeq hdlim hsRatioD Hband
      (fun n=>Fintype.card (FeatureIndex (dim n+1))-1)
      (fun n=>cavityCanonicalFeatureEquiv (dim n))
    simpa only [hscalarEq] using Hsource
  · exact hK

theorem exists_actual_high_wall_strict_strip_subsequence_from_physical_readers
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D) (hT : 0 < T)
    (hclSlack : cl < 2*T*Real.exp (-12*T))
    (hcuSlack :
      T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hTeq : ∀n,(M n).data.T=T)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    {K : ℝ} (hK : 1≤K) :
    ∃chi : ℕ→ℕ,StrictMono chi ∧
      ∀ᶠn in atTop,∀r∈Icc (M (chi n)).data.d (K*(M (chi n)).data.d),
        cl*r<(M (chi n)).alpha.val.val r ∧
        (M (chi n)).alpha.val.val r<cu*r := by
  obtain ⟨phi,hphi,htotal,d,hUV⟩ :=
    exists_actual_high_wall_critical_scalar_limit_from_physical_readers
      hm hdelta hroom hcl hcu hAz hC0 hCt hD hT
      dim hdim M hfixed hTeq hx hsRatio
  let P : (n:ℕ)→ActualHighWallOverlapMinimum (dim (phi n)+1)
      m delta cl cu Az C0 Ct D Bclock := fun n=>M (phi n)
  let dimP : ℕ→ℕ := fun n=>dim (phi n)
  have hdimP : Tendsto dimP atTop atTop :=
    hdim.comp hphi.tendsto_atTop
  have hxP : Tendsto (fun n=>(P n).xs) atTop (𝓝 0) :=
    hx.comp hphi.tendsto_atTop
  obtain ⟨s,_B,psi,_hB,hpsi,_hsbound,hspin⟩ :=
    exists_actual_rescaled_radius_spin_profile_limit_high_wall
      hm hdelta hroom hcl hcu hAz hC0 hCt
      dimP hdimP P hxP
  let chi := phi ∘ psi
  have hchi : StrictMono chi := hphi.comp hpsi
  let Q : (n:ℕ)→ActualHighWallOverlapMinimum (dim (chi n)+1)
      m delta cl cu Az C0 Ct D Bclock := fun n=>M (chi n)
  let dimQ : ℕ→ℕ := fun n=>dim (chi n)
  have hdimQ : Tendsto dimQ atTop atTop :=
    hdim.comp hchi.tendsto_atTop
  have hxQ : Tendsto (fun n=>(Q n).xs) atTop (𝓝 0) :=
    hx.comp hchi.tendsto_atTop
  have hsRatioQ : Tendsto (fun n=>(Q n).data.s/(Q n).xs) atTop (𝓝 0) :=
    hsRatio.comp hchi.tendsto_atTop
  let htotalQ : ∀n,∀u∈Icc (0:ℝ) 1,
      ((Q n).hf u:ℝ)+((Q n).bf u:ℝ)≤T :=
    fun n=>htotal (psi n)
  let dQ : ActualHighWallLocalScalarLimitData hT T Q htotalQ :=
    d.comp psi hpsi
  have Hstrip := eventually_actual_high_wall_strict_strip_of_physical_readers
    hm hdelta hmargin hcl hcu hAz hC0 hCt hD hT
    hclSlack hcuSlack dimQ hdimQ Q
    (fun n=>hfixed (chi n)) (fun n=>hTeq (chi n))
    hxQ hsRatioQ htotalQ dQ hUV s
    (by intro r; simpa only [Q,chi,Function.comp_apply,P] using hspin r) hK
  exact ⟨chi,hchi,Hstrip⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
