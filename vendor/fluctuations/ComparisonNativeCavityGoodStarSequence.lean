module

public import ComparisonNativeCavityGoodStarMoments

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

theorem radius_half_band_good_point_sequence (f : ℕ→ℝ→ℝ) (W : ℕ→ℝ)
    (hW : ∀n,0<W n) (hf : ∀n,IntegrableOn (f n) (Ioo (W n/2) (W n)))
    (hnonneg : ∀n,∀r∈Ioo (W n/2) (W n),0≤f n r)
    (hlim : Tendsto (fun n=>(∫r in Ioo (W n/2) (W n),f n r)/(W n)^3) atTop (𝓝 0)) :
    ∃r:ℕ→ℝ,(∀n,r n∈Ioo (W n/2) (W n)) ∧
      Tendsto (fun n=>f n (r n)/(W n)^2) atTop (𝓝 0) := by
  let I:=fun n=>∫r in Ioo (W n/2) (W n),f n r
  let threshold:=fun n=>2*I n/W n+(W n)^2/(n+1:ℕ)
  have hp n : ∃r∈Ioo (W n/2) (W n),f n r≤threshold n := by
    apply radius_integral_good_point (by linarith [hW n]) (hf n)
    have hN : 0<(n+1:ℕ) := Nat.succ_pos n
    have hNr : 0<(n+1:ℕ) := hN
    have hNreal : 0<((n+1:ℕ):ℝ) := by exact_mod_cast hNr
    have he : threshold n*(W n-W n/2)=I n+(W n)^3/(2*(n+1:ℕ)) := by
      dsimp only [threshold]
      field_simp [(hW n).ne']
      ring
    rw [he]
    change I n<I n+_
    exact lt_add_of_pos_right _ (div_pos (pow_pos (hW n) 3) (mul_pos (by norm_num) hNreal))
  choose r hr hbound using hp
  refine ⟨r,hr,?_⟩
  have H:=(hlim.const_mul 2).add uniformMasses_mesh_tendsto
  simp only [mul_zero,add_zero] at H
  apply squeeze_zero (fun n=>div_nonneg (hnonneg n (r n) (hr n)) (sq_nonneg _)) (fun n=>?_) H
  have HH:=div_le_div_of_nonneg_right (hbound n) (sq_nonneg (W n))
  have he : threshold n/(W n)^2=2*(I n/(W n)^3)+(((n+1:ℕ):ℝ))⁻¹ := by
    dsimp only [threshold]
    field_simp [(hW n).ne']
  rw [he] at HH
  exact HH

theorem actual_minimum_bare_SK_good_star_sequence
    (Bclock T : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW1 : ∀n,W n≤1) (hband : ∀n,max 1 (2*Az)*(M n).xs≤W n)
    (hb_const : ∀n u,(M n).b u=T) (hh_zero : ∀n u,(M n).h u=0) :
    ∃r:ℕ→ℝ,(∀n,r n∈Ioo (W n/2) (W n) ∧
      (cl/2)*W n≤(M n).alpha.val.val (r n) ∧ (M n).alpha.val.val (r n)≤cu*W n ∧
      (M n).alpha.val.val (r n)<1) ∧
      Tendsto (fun n=>(M n).cavityRadiusPointDefect (r n)/(W n)^2) atTop (𝓝 0) := by
  have hxsW n : (M n).xs≤W n := by
    have H:=mul_le_mul_of_nonneg_right (le_max_left 1 (2*Az)) (M n).hxs.le
    nlinarith [hband n]
  have hWp n : 0<W n := (M n).hxs.trans_le (hxsW n)
  have hthreshold n : (M n).z≤W n/2 := by
    have H:=mul_le_mul_of_nonneg_right (le_max_right 1 (2*Az)) (M n).hxs.le
    nlinarith [(M n).hzxs,hband n]
  have houter n : (cl/2)*W n≤(M n).alpha.val.val (W n/2) := by
    have H:=((M n).regular (W n/2) ⟨hthreshold n,by linarith [hW1 n,hWp n]⟩).1
    nlinarith only [H]
  have H:=actual_minimum_cavity_radius_Eq19_band_scale_bare_SK_tendsto_zero
    (C:=1) (ca:=cl/2) Bclock T hm hdelta hmargin hcl hcu hAz hC0 hCt
    (by norm_num) (by positivity) M W (fun n=>W n/2) W
    (fun n=>div_pos (hWp n) (by norm_num)) (fun n=>by linarith [hWp n]) hW1 hxsW
    (fun _=>le_rfl) (fun n=>by simp) houter hb_const hh_zero
  obtain ⟨r,hr,hzero⟩:=radius_half_band_good_point_sequence
    (fun n=>(M n).cavityRadiusPointDefect) W hWp
    (fun n=>(M n).cavityRadiusPointDefect_integrableOn (by linarith [hWp n]) (hW1 n))
    (fun n r hr=>(M n).cavityRadiusPointDefect_nonneg
      ⟨(by linarith [hr.1,hWp n]),hr.2.le.trans (hW1 n)⟩) H
  refine ⟨r,?_,hzero⟩
  intro n
  have hreg:=(M n).regular (r n) ⟨(hthreshold n).trans (hr n).1.le,(hr n).2.le.trans (hW1 n)⟩
  have hlow : (cl/2)*W n≤(M n).alpha.val.val (r n) := by
    have H:=mul_le_mul_of_nonneg_left (hr n).1.le hcl.le
    nlinarith only [H,hreg.1]
  have hhigh := hreg.2.trans (mul_le_mul_of_nonneg_left (hr n).2.le hcu.le)
  have hrpos : 0<r n := (div_pos (hWp n) (by norm_num)).trans (hr n).1
  have hr1 : r n<1 := (hr n).2.trans_le (hW1 n)
  have hstrict:=inverseConstraint_strictMonoOn (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).alpha.property ⟨hrpos.le,hr1.le⟩
    (by norm_num : (1:ℝ)∈Icc (0:ℝ) 1) hr1
  exact ⟨hr n,hlow,hhigh,hstrict.trans_le ((M n).alpha.val.property.1 1).2⟩

def NativeGoodStarSequenceSaving
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (l : ℕ) (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W rstar : ℕ→ℝ) : Prop :=
    ∃Craw : ℝ,0<Craw ∧ ∀eps : ℝ,0<eps→∀ᶠn:ℕ in atTop,
      ∀extra : List PositiveMass,(∀v∈extra,v.val≤1)→
      ∃u:PositiveMass,u.val=(M n).alpha.val.val (rstar n) ∧ u.val<1 ∧
        (cl/2)*W n≤u.val ∧ u.val≤cu*W n ∧
      ∃us:List PositiveMass,(∀v∈us,v.val≤1) ∧ u∈us ∧ (∀v∈extra,v∈us) ∧
        ∀ᶠj:ℕ in atTop,
          let as:=finiteCutMasses us j
          let q:=completedPathClock (n+1) (M n).bf (M n).hf
          let steps:=sampleClockSteps q 0 as
          let S:=orderedPathS (n+1) (M n).bf (M n).hf u.val
          (physicalRawRatio (n+1) (2*l-1) steps 0 (M n).xs
            (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id)^2≤2*Craw ∧
          nativeRetainedCenteredMoment n l (M n).bf (M n).hf as u.val S≤eps*(W n)^(2*l) ∧
          |finitePhysicalMean (n+1) as (fun k=>((M n).bf (partitionPoint 0 as k):ℝ))
            (fun k=>((M n).hf (partitionPoint 0 as k):ℝ))
            (retainedMassPrefixIndex u.val as)-S|≤eps*W n

theorem eventually_actual_minimum_native_moments_at_good_star_sequence
    (l : ℕ) (hl : 0<l) (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW1 : ∀n,W n≤1) (hband : ∀n,max 1 (2*Az)*(M n).xs≤W n)
    (rstar : ℕ→ℝ) (hrband : ∀n,rstar n∈Ioo (W n/2) (W n))
    (hrmass : ∀n,(cl/2)*W n≤(M n).alpha.val.val (rstar n) ∧
      (M n).alpha.val.val (rstar n)≤cu*W n)
    (hdefzero : Tendsto (fun n=>(M n).cavityRadiusPointDefect (rstar n)/(W n)^2) atTop (𝓝 0)) :
    NativeGoodStarSequenceSaving l M W rstar := by
  dsimp only [NativeGoodStarSequenceSaving]
  have hroom : delta<3*m := by linarith
  obtain ⟨Craw,hCraw,hraw⟩:=eventually_native_minimum_original_boundary_raw (2*l-2)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨K,hK,hamp⟩:=eventually_actual_minimum_overlap_natural_moment (2*l-2)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  have horder : 2*l-2+1=2*l-1 := by omega
  simp only [horder] at hraw hamp
  let H:=2*l-1
  let Kr:=2*K*(1+cu)^(2*H)
  let Ks:=(2:ℝ)^(2*H-1)*((2:ℝ)^(2*H)*Kr+1)
  have hH : 0<H := by dsimp [H];omega
  have hKr : 0<Kr := by dsimp [Kr];positivity
  have hKs : 0<Ks := by dsimp [Ks];positivity
  have hshift : Tendsto (fun n:ℕ=>n+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k] with n hn
    omega
  have hxsW n : (M n).xs≤W n := by
    have H:=mul_le_mul_of_nonneg_right (le_max_left 1 (2*Az)) (M n).hxs.le
    nlinarith [hband n]
  have hWp n : 0<W n := (M n).hxs.trans_le (hxsW n)
  refine ⟨Craw,hCraw,?_⟩
  intro eps heps
  let eta:=eps^2/(2*Ks)
  have heta : 0<eta := by dsimp [eta];positivity
  have hpoint:=hdefzero.eventually (gt_mem_nhds heta)
  filter_upwards [hpoint,hshift.eventually hraw,hshift.eventually hamp] with n hnpoint hnraw hnamp
  intro extra hextra
  have hWn : 0<W n := hWp n
  let r:=rstar n
  have hr:=hrband n
  have hmassl:=(hrmass n).1
  have hmassu:=(hrmass n).2
  have hdef : (M n).cavityRadiusPointDefect r≤eta*(W n)^2 :=
    (div_le_iff₀ (sq_pos_of_pos hWn)).mp hnpoint.le
  have hup : 0<(M n).alpha.val.val r := (mul_pos (by positivity : 0<cl/2) (hWp n)).trans_le hmassl
  let u:PositiveMass:=⟨(M n).alpha.val.val r,hup⟩
  have hu1 : u.val≤1 := ((M n).alpha.val.property.1 r).2
  have hu1strict : u.val<1 := by
    have hrpos : 0<r := (div_pos hWn (by norm_num)).trans hr.1
    have hr1 : r<1 := hr.2.trans_le (hW1 n)
    have H:=inverseConstraint_strictMonoOn (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).alpha.property ⟨hrpos.le,hr1.le⟩
      (by norm_num : (1:ℝ)∈Icc (0:ℝ) 1) hr1
    exact H.trans_le ((M n).alpha.val.property.1 1).2
  obtain ⟨us,hus,hu,hretain,hQ⟩:=hnraw (M n) u hu1 extra hextra
  have had:=comparisonVariableEndpoint_clocks_admissible (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).context.hm (M n).context.hM (M n).b (M n).h
    (M n).context.hd.ne' (M n).hlam.le (M n).hlb (M n).hb (M n).hh (M n).hh0 (M n).alpha
  have hb:=toNNReal_monotoneOn had.1
  have hh:=toNNReal_monotoneOn had.2.1
  let S:=orderedPathS (n+1) (M n).bf (M n).hf u.val
  have HV:=nativeRetainedCenteredMoment_one_tendsto n (M n).bf (M n).hf hb hh us hus u hu
  have HVsmall : ∀ᶠj:ℕ in atTop,
      nativeRetainedCenteredMoment n 1 (M n).bf (M n).hf (finiteCutMasses us j) u.val S≤
        2*eta*(W n)^2 := by
    have hlt : orderedPathB (n+1) (M n).bf (M n).hf u.val-S^2<2*eta*(W n)^2 := by
      change (M n).cavityRadiusPointDefect r<2*eta*(W n)^2
      nlinarith [mul_pos heta (sq_pos_of_pos (hWp n))]
    exact (HV.eventually (gt_mem_nhds hlt)).mono (fun _ h=>h.le)
  have HM:=nativeRetainedFinitePhysicalMean_tendsto n (M n).bf (M n).hf hb hh us hus u hu
  have HMabs : Tendsto (fun j=>
      let as:=finiteCutMasses us j
      |finitePhysicalMean (n+1) as (fun k=>((M n).bf (partitionPoint 0 as k):ℝ))
        (fun k=>((M n).hf (partitionPoint 0 as k):ℝ)) (retainedMassPrefixIndex u.val as)-S|)
      atTop (𝓝 0) := by
    simpa only [S,sub_self,abs_zero] using (HM.sub_const S).abs
  have HM1:=(HMabs.eventually (gt_mem_nhds (hWp n))).mono (fun _ h=>h.le)
  have HMeps:=(HMabs.eventually (gt_mem_nhds (mul_pos heps (hWp n)))).mono (fun _ h=>h.le)
  let P:=fun σ τ:Spin (n+1)=>|orderedOverlap (n+1) σ τ|^(2*H)
  have HR:=nativeRetainedPairValue_tendsto n (M n).bf (M n).hf hb hh us hus u hu P
  have hampU:=hnamp (M n) u.val ⟨u.property,hu1⟩
  rw [←orderedPathPair_eq_completed (n+1) (by omega) (M n).bf (M n).hf hb hh P
    ⟨u.property,hu1⟩] at hampU
  have hsize : (M n).xs+u.val≤(1+cu)*W n := by nlinarith [hxsW n,hmassu]
  have hstrict : orderedPathPair (n+1) (M n).bf (M n).hf P u.val<Kr*(W n)^(2*H) := by
    have Hpow:=mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (add_pos (M n).hxs u.property).le hsize (2*H)) hK.le
    have heq : K*((1+cu)*W n)^(2*H)=K*(1+cu)^(2*H)*(W n)^(2*H) := by rw [mul_pow];ring
    rw [heq] at Hpow
    have hp : 0<K*(1+cu)^(2*H)*(W n)^(2*H) := by positivity
    dsimp only [H] at *
    dsimp only [Kr]
    nlinarith
  have HRsmall:=(HR.eventually (gt_mem_nhds hstrict)).mono (fun _ h=>h.le)
  refine ⟨u,rfl,hu1strict,hmassl,hmassu,us,hus,hu,hretain,?_⟩
  filter_upwards [hQ,HVsmall,HM1,HMeps,HRsmall] with j hjQ hjV hjM hjMeps hjR
  refine ⟨hjQ.1,?_,hjMeps⟩
  have ho:=finiteCutMasses_ordered us hus j
  have HH:=nativeRetainedCenteredMoment_le_of_raw_and_mean_error n H hH
    (M n).bf (M n).hf (finiteCutMasses us j) ho u.val S (W n) Kr (hWp n) hKr.le hjR hjM
  have HC:=nativeRetainedCenteredMoment_interpolation_sq n l hl (M n).bf (M n).hf
    (finiteCutMasses us j) ho u.val S
  have HC':=HC.trans (mul_le_mul hjV HH
    (nativeRetainedCenteredMoment_nonneg n H (M n).bf (M n).hf _ ho u.val S)
    (by positivity : 0≤2*eta*(W n)^2))
  have heq : (2*eta*(W n)^2)*(Ks*(W n)^(2*H))=(eps*(W n)^(2*l))^2 := by
    calc
      _=(2*eta*Ks)*(W n)^(2+2*H) := by rw [pow_add];ring
      _=eps^2*(W n)^(4*l) := by
        have he : 2+2*H=4*l := by dsimp [H];omega
        rw [he]
        dsimp only [eta]
        field_simp
      _=_ := by rw [mul_pow,←pow_mul];congr 2;omega
  change (nativeRetainedCenteredMoment n l (M n).bf (M n).hf _ u.val S)^2≤
    (2*eta*(W n)^2)*(Ks*(W n)^(2*H)) at HC'
  rw [heq] at HC'
  exact (sq_le_sq₀ (nativeRetainedCenteredMoment_nonneg n l (M n).bf (M n).hf _ ho u.val S)
    (mul_nonneg heps.le (pow_nonneg (hWp n).le _))).mp HC'

theorem exists_actual_minimum_bare_SK_native_good_star_all_orders
    (Bclock T : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW1 : ∀n,W n≤1) (hband : ∀n,max 1 (2*Az)*(M n).xs≤W n)
    (hb_const : ∀n u,(M n).b u=T) (hh_zero : ∀n u,(M n).h u=0) :
    ∃rstar:ℕ→ℝ,(∀n,rstar n∈Ioo (W n/2) (W n) ∧
      (cl/2)*W n≤(M n).alpha.val.val (rstar n) ∧ (M n).alpha.val.val (rstar n)≤cu*W n ∧
      (M n).alpha.val.val (rstar n)<1) ∧
      ∀l:ℕ,0<l→NativeGoodStarSequenceSaving l M W rstar := by
  obtain ⟨rstar,hr,hzero⟩:=actual_minimum_bare_SK_good_star_sequence Bclock T hm hdelta hmargin
    hcl hcu hAz hC0 hCt M W hW1 hband hb_const hh_zero
  refine ⟨rstar,hr,?_⟩
  intro l hl
  exact eventually_actual_minimum_native_moments_at_good_star_sequence l hl Bclock hm hdelta hmargin
    hcl hcu hAz hC0 hCt M W hW1 hband rstar (fun n=>(hr n).1)
    (fun n=>⟨(hr n).2.1,(hr n).2.2.1⟩) hzero

end OAI.SKFluctuations.LaplaceWindowFormalization
