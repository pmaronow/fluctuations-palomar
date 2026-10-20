module

public import ComparisonNativeCavityPolynomialGoodStar

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable

def NativePolynomialStarMomentOnFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (l : ℕ) (kappa : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W rstar : ℕ→ℝ) : Prop :=
  ∀ᶠn:ℕ in atTop,∀us:List PositiveMass,(∀u∈us,u.val≤1)→
    (∃u∈us,u.val=(M n).alpha.val.val (rstar n))→∀ᶠj:ℕ in atTop,
      let as:=finiteCutMasses us j
      let u:=(M n).alpha.val.val (rstar n)
      let S:=orderedPathS (n+1) (M n).bf (M n).hf u
      nativeRetainedCenteredMoment n l (M n).bf (M n).hf as u S≤
        ((n+1:ℕ):ℝ)^(-kappa/4)*(W n)^(2*l) ∧
      |finitePhysicalMean (n+1) as (fun k=>((M n).bf (partitionPoint 0 as k):ℝ))
        (fun k=>((M n).hf (partitionPoint 0 as k):ℝ)) (retainedMassPrefixIndex u as)-S|≤
        ((n+1:ℕ):ℝ)^(-kappa/4)*W n

theorem eventually_actual_minimum_polynomial_star_on_final_net
    (l : ℕ) (hl : 0<l) (kappa : ℝ) (hkappa : 0<kappa) (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW1 : ∀n,W n≤1) (hband : ∀n,max 1 (2*Az)*(M n).xs≤W n)
    (rstar : ℕ→ℝ) (hrband : ∀n,rstar n∈Ioo (W n/2) (W n))
    (hrmass : ∀n,(cl/2)*W n≤(M n).alpha.val.val (rstar n) ∧
      (M n).alpha.val.val (rstar n)≤cu*W n)
    (hdefrate : ∀ᶠn:ℕ in atTop,(M n).cavityRadiusPointDefect (rstar n)/(W n)^2≤
      ((n+1:ℕ):ℝ)^(-kappa)) :
    NativePolynomialStarMomentOnFinalNet l kappa M W rstar := by
  dsimp only [NativePolynomialStarMomentOnFinalNet]
  have hroom : delta<3*m := by linarith
  obtain ⟨K,hK,hamp⟩:=eventually_actual_minimum_overlap_natural_moment (2*l-2)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  have horder : 2*l-2+1=2*l-1 := by omega
  simp only [horder] at hamp
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
  have hcoeff:=hshift.eventually (eventually_coefficient_rpow_le
    (c:=2*Ks) (d:=1) (q:= -kappa) (r:= -kappa/2) (by norm_num) (by linarith))
  filter_upwards [hdefrate,hshift.eventually hamp,hcoeff] with n hnpoint hnamp hncoeff
  intro us hus hstar
  have hWn : 0<W n := hWp n
  have hN : 0<((n+1:ℕ):ℝ) := by positivity
  let eta:=((n+1:ℕ):ℝ)^(-kappa)
  let eps:=((n+1:ℕ):ℝ)^(-kappa/4)
  have heta : 0<eta := Real.rpow_pos_of_pos hN _
  have heps : 0<eps := Real.rpow_pos_of_pos hN _
  let r:=rstar n
  have hr:=hrband n
  have hmassl:=(hrmass n).1
  have hmassu:=(hrmass n).2
  have hdef : (M n).cavityRadiusPointDefect r≤eta*(W n)^2 :=
    (div_le_iff₀ (sq_pos_of_pos hWn)).mp hnpoint
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
  obtain ⟨u0,hu0,hu0val⟩:=hstar
  have he : u0=u := Subtype.ext hu0val
  have hu : u∈us := he ▸ hu0
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
  filter_upwards [HVsmall,HM1,HMeps,HRsmall] with j hjV hjM hjMeps hjR
  refine ⟨?_,hjMeps⟩
  have ho:=finiteCutMasses_ordered us hus j
  have HH:=nativeRetainedCenteredMoment_le_of_raw_and_mean_error n H hH
    (M n).bf (M n).hf (finiteCutMasses us j) ho u.val S (W n) Kr (hWp n) hKr.le hjR hjM
  have HC:=nativeRetainedCenteredMoment_interpolation_sq n l hl (M n).bf (M n).hf
    (finiteCutMasses us j) ho u.val S
  have HC':=HC.trans (mul_le_mul hjV HH
    (nativeRetainedCenteredMoment_nonneg n H (M n).bf (M n).hf _ ho u.val S)
    (by positivity : 0≤2*eta*(W n)^2))
  have heprod : (2*eta*(W n)^2)*(Ks*(W n)^(2*H))=
      (2*Ks*eta)*(W n)^(4*l) := by
    have he : 2+2*H=4*l := by dsimp [H];omega
    rw [←he,pow_add]
    ring
  change (nativeRetainedCenteredMoment n l (M n).bf (M n).hf _ u.val S)^2≤
    (2*eta*(W n)^2)*(Ks*(W n)^(2*H)) at HC'
  rw [heprod] at HC'
  have Hnum:=mul_le_mul_of_nonneg_right (by simpa only [one_mul] using hncoeff)
    (pow_nonneg hWn.le (4*l))
  have Hfinal:=HC'.trans Hnum
  have heps2 : eps^2=((n+1:ℕ):ℝ)^(-kappa/2) := by
    dsimp only [eps]
    rw [←Real.rpow_mul_natCast hN.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have heq : ((n+1:ℕ):ℝ)^(-kappa/2)*(W n)^(4*l)=(eps*(W n)^(2*l))^2 := by
    rw [mul_pow,heps2,←pow_mul]
    congr 2
    omega
  rw [heq] at Hfinal
  exact (sq_le_sq₀ (nativeRetainedCenteredMoment_nonneg n l (M n).bf (M n).hf _ ho u.val S)
    (mul_nonneg heps.le (pow_nonneg (hWp n).le _))).mp Hfinal

def NativePolynomialStarFiniteDegreeOnFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (A : ℕ) (kappa : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W rstar : ℕ→ℝ) : Prop :=
  ∀ᶠn:ℕ in atTop,∀us:List PositiveMass,(∀u∈us,u.val≤1)→
    (∃u∈us,u.val=(M n).alpha.val.val (rstar n))→∀ᶠj:ℕ in atTop,
      let as:=finiteCutMasses us j
      let u:=(M n).alpha.val.val (rstar n)
      let S:=orderedPathS (n+1) (M n).bf (M n).hf u
      (∀l:ℕ,0<l→l≤A→nativeRetainedCenteredMoment n l (M n).bf (M n).hf as u S≤
        (((n+1:ℕ):ℝ)^(-kappa/(8*(A:ℝ)))*W n)^(2*l)) ∧
      |finitePhysicalMean (n+1) as (fun k=>((M n).bf (partitionPoint 0 as k):ℝ))
        (fun k=>((M n).hf (partitionPoint 0 as k):ℝ)) (retainedMassPrefixIndex u as)-S|≤
        ((n+1:ℕ):ℝ)^(-kappa/4)*W n

theorem polynomial_star_final_net_to_finite_degree
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (A : ℕ) (hA : 0<A)
    (kappa : ℝ) (hkappa : 0<kappa)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W rstar : ℕ→ℝ) (hW : ∀n,0<W n)
    (hsource : NativePolynomialStarMomentOnFinalNet A kappa M W rstar) :
    NativePolynomialStarFiniteDegreeOnFinalNet A kappa M W rstar := by
  filter_upwards [hsource] with n hn
  intro us hus hstar
  filter_upwards [hn us hus hstar] with j hj
  refine ⟨?_,hj.2⟩
  intro l hl hlA
  have hN : 1≤((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos n
  have hWn : 0<W n := hW n
  have Hmax:=native_polynomial_star_common_finite_degree hN hkappa hWn.le hA
    (le_rfl : A≤A) hj.1
  exact nativeRetainedCenteredMoment_lower_order n l A hl hlA (M n).bf (M n).hf
    (finiteCutMasses us j) (finiteCutMasses_ordered us hus j)
    ((M n).alpha.val.val (rstar n))
    (orderedPathS (n+1) (M n).bf (M n).hf ((M n).alpha.val.val (rstar n)))
    (((n+1:ℕ):ℝ)^(-kappa/(8*(A:ℝ)))*W n)
    (by positivity) Hmax

theorem exists_actual_minimum_bare_SK_polynomial_star_on_every_final_net
    (Bclock T : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW1 : ∀n,W n≤1) (hband : ∀n,max 1 (2*Az)*(M n).xs≤W n)
    (hb_const : ∀n u,(M n).b u=T) (hh_zero : ∀n u,(M n).h u=0) :
    ∃rstar:ℕ→ℝ,(∀n,rstar n∈Ioo (W n/2) (W n) ∧
      (cl/2)*W n≤(M n).alpha.val.val (rstar n) ∧ (M n).alpha.val.val (rstar n)≤cu*W n ∧
      (M n).alpha.val.val (rstar n)<1) ∧
      (∀l:ℕ,0<l→NativePolynomialStarMomentOnFinalNet l (min (delta/64) (1/16)/2) M W rstar) ∧
      ∀A:ℕ,0<A→NativePolynomialStarFiniteDegreeOnFinalNet A (min (delta/64) (1/16)/2) M W rstar := by
  obtain ⟨rstar,hr,hrate⟩:=exists_actual_minimum_bare_SK_polynomial_good_star_sequence
    Bclock T hm hdelta hmargin hcl hcu hAz hC0 hCt M W hW1 hband hb_const hh_zero
  have hkappa : 0 < min (delta/64) (1/16)/2 :=
    div_pos (lt_min (by positivity) (by norm_num)) (by norm_num)
  have H (l:ℕ) (hl:0<l) :
      NativePolynomialStarMomentOnFinalNet l (min (delta/64) (1/16)/2) M W rstar :=
    eventually_actual_minimum_polynomial_star_on_final_net l hl (min (delta/64) (1/16)/2)
      hkappa Bclock hm hdelta hmargin hcl hcu hAz hC0 hCt M W hW1 hband rstar
      (fun n=>(hr n).1) (fun n=>⟨(hr n).2.1,(hr n).2.2.1⟩)
      (by simpa only [neg_div] using hrate)
  have hW n : 0<W n := by
    have H:=mul_le_mul_of_nonneg_right (le_max_left 1 (2*Az)) (M n).hxs.le
    nlinarith [(M n).hxs,hband n]
  exact ⟨rstar,hr,H,fun A hA=>polynomial_star_final_net_to_finite_degree A hA
    (min (delta/64) (1/16)/2) hkappa M W rstar hW (H A hA)⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
