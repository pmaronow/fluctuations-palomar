module

public import ComparisonNativeCavityGoodStarTransfer

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

theorem nativeRetainedCenteredMoment_nonneg (n l : ℕ) (bf hf : ℝ→ℝ≥0)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (u center : ℝ) :
    0≤nativeRetainedCenteredMoment n l bf hf as u center := by
  unfold nativeRetainedCenteredMoment nativeRetainedPairValue ClockTree.disorderExpect
  apply Finset.sum_nonneg
  intro σ _
  apply mul_nonneg _ (pow_nonneg (abs_nonneg _) _)
  exact ((ClockTree.pairClock as (retainedMassPrefixIndex u as)).disorderWeight_probability
    (uniformWeight_pos (n+1)) (finiteFeature (n+1)) ho 0 _ 0).1 σ

theorem nativeRetainedCut_lt_length (as : List PositiveMass) (ho : MassOrdered 0 as)
    (he : partitionEnd 0 as=1) (u : PositiveMass) (hu : u∈as) (hu1 : u.val<1) :
    retainedMassPrefixIndex u.val as<as.length := by
  have hle:=retainedMassPrefixIndex_le_length u.val as
  have hpoint:=nativeRetainedCut_partitionPoint as ho u hu
  by_contra h
  have hcut : retainedMassPrefixIndex u.val as=as.length := by omega
  rw [hcut,physicalPartitionPoint_length,he] at hpoint
  linarith

theorem nativeRetainedCenteredMoment_le_of_raw_and_mean_error (n l : ℕ) (hl : 0<l)
    (bf hf : ℝ→ℝ≥0) (as : List PositiveMass) (ho : MassOrdered 0 as)
    (u center W K : ℝ) (_hW : 0<W) (_hK : 0≤K)
    (hraw : nativeRetainedPairValue n bf hf as u
      (fun σ τ=>|orderedOverlap (n+1) σ τ|^(2*l))≤K*W^(2*l))
    (hmean : |finitePhysicalMean (n+1) as
      (fun j=>(bf (partitionPoint 0 as j):ℝ)) (fun j=>(hf (partitionPoint 0 as j):ℝ))
      (retainedMassPrefixIndex u as)-center|≤W) :
    nativeRetainedCenteredMoment n l bf hf as u center≤
      ((2:ℝ)^(2*l-1)*((2:ℝ)^(2*l)*K+1))*W^(2*l) := by
  let cut:=retainedMassPrefixIndex u as
  let T:=ClockTree.pairClock (S:=Spin (n+1)) as cut
  let q:=physicalCompletedClock (n+1) (fun j=>(bf (partitionPoint 0 as j):ℝ))
    (fun j=>(hf (partitionPoint 0 as j):ℝ))
  let F:=fun σ:T.Assignment=>orderedOverlap (n+1) (ClockTree.pairSpin as cut σ).1
    (ClockTree.pairSpin as cut σ).2
  let μ:=T.disorderExpect (uniformWeight (n+1)) (finiteFeature (n+1)) 0 q F 0
  have hw:=T.disorderWeight_probability (uniformWeight_pos (n+1)) (finiteFeature (n+1)) ho 0 q 0
  have H:=T.disorderExpect_centered_abs_pow_le (uniformWeight_pos (n+1))
    (finiteFeature (n+1)) ho 0 q 0 F (by omega : 0<2*l)
  have hμ : |μ-center|≤W := by
    change |nativeRetainedPairValue n bf hf as u (orderedOverlap (n+1))-center|≤W
    rw [nativeRetainedPairValue_overlap_eq_finitePhysicalMean n bf hf as ho u]
    exact hmean
  have hpoint σ : |F σ-center|^(2*l)≤
      (2:ℝ)^(2*l-1)*(|F σ-μ|^(2*l)+W^(2*l)) := by
    have htri : |F σ-center|≤|F σ-μ|+|μ-center| := by
      simpa only [sub_add_sub_cancel] using abs_add_le (F σ-μ) (μ-center)
    have H1:=(pow_le_pow_left₀ (abs_nonneg _) htri (2*l)).trans
      (add_pow_le (abs_nonneg _) (abs_nonneg _) (2*l))
    exact H1.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (pow_le_pow_left₀ (abs_nonneg _) hμ (2*l)))
      (by positivity))
  have Hsum:=Finset.sum_le_sum (fun σ (_ : σ∈Finset.univ)=>
    mul_le_mul_of_nonneg_left (hpoint σ) (hw.1 σ))
  have he : (∑σ:T.Assignment,T.disorderWeight (uniformWeight (n+1))
      (finiteFeature (n+1)) 0 q σ 0*((2:ℝ)^(2*l-1)*(|F σ-μ|^(2*l)+W^(2*l))))=
      (2:ℝ)^(2*l-1)*(T.disorderExpect (uniformWeight (n+1))
        (finiteFeature (n+1)) 0 q (fun σ=>|F σ-μ|^(2*l)) 0+W^(2*l)) := by
    unfold ClockTree.disorderExpect
    calc
      _=(2:ℝ)^(2*l-1)*((∑σ:T.Assignment,T.disorderWeight (uniformWeight (n+1))
        (finiteFeature (n+1)) 0 q σ 0*|F σ-μ|^(2*l))+
        W^(2*l)*(∑σ:T.Assignment,T.disorderWeight (uniformWeight (n+1))
          (finiteFeature (n+1)) 0 q σ 0)) := by
        simp only [Finset.mul_sum,←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro σ _
        ring
      _=_ := by rw [hw.2,mul_one]
  rw [he] at Hsum
  have Hraw : T.disorderExpect (uniformWeight (n+1)) (finiteFeature (n+1)) 0 q
      (fun σ=>|F σ|^(2*l)) 0≤K*W^(2*l) := hraw
  have Hcenter:=H.trans (mul_le_mul_of_nonneg_left Hraw (by positivity : 0≤(2:ℝ)^(2*l)))
  change nativeRetainedCenteredMoment n l bf hf as u center≤_ at Hsum
  apply Hsum.trans
  have HH:=mul_le_mul_of_nonneg_left (add_le_add_right Hcenter (W^(2*l)))
    (by positivity : 0≤(2:ℝ)^(2*l-1))
  convert HH using 1 <;> ring

theorem eventually_actual_minimum_bare_SK_native_good_star
    (l : ℕ) (hl : 0<l) (Bclock T : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW1 : ∀n,W n≤1) (hband : ∀n,max 1 (2*Az)*(M n).xs≤W n)
    (hb_const : ∀n u,(M n).b u=T) (hh_zero : ∀n u,(M n).h u=0) :
    ∃Craw : ℝ,0<Craw ∧ ∀eps : ℝ,0<eps→∀ᶠn:ℕ in atTop,
      ∀extra : List PositiveMass,(∀v∈extra,v.val≤1)→
      ∃r∈Ioo (W n/2) (W n),∃u:PositiveMass,u.val=(M n).alpha.val.val r ∧ u.val<1 ∧
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
            (retainedMassPrefixIndex u.val as)-S|≤eps*W n := by
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
  have hpoint:=actual_minimum_cavity_radius_bare_SK_good_star Bclock T hm hdelta hmargin
    hcl hcu hAz hC0 hCt M W hW1 hband hb_const hh_zero eta heta
  filter_upwards [hpoint,hshift.eventually hraw,hshift.eventually hamp] with n hnpoint hnraw hnamp
  intro extra hextra
  have hWn : 0<W n := hWp n
  obtain ⟨r,hr,hdef,hmassl,hmassu⟩:=hnpoint
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
  refine ⟨r,hr,u,rfl,hu1strict,hmassl,hmassu,us,hus,hu,hretain,?_⟩
  filter_upwards [hQ,HVsmall,HM1,HMeps,HRsmall] with j hjQ hjV hjM hjMeps hjR
  dsimp only
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

end OAI.SKFluctuations.LaplaceWindowFormalization
