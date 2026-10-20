module

public import ComparisonNativeCavityRadiusPolynomialRate
public import ComparisonNativeCavityGoodStarSequence
public import CavityRealMomentMonotonicity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable

theorem radius_half_band_good_point_sequence_budget (f : ℕ→ℝ→ℝ) (W : ℕ→ℝ)
    (hW : ∀n,0<W n) (hf : ∀n,IntegrableOn (f n) (Ioo (W n/2) (W n)))
    : ∃r:ℕ→ℝ,∀n,r n∈Ioo (W n/2) (W n) ∧
      f n (r n)/(W n)^2≤2*((∫u in Ioo (W n/2) (W n),f n u)/(W n)^3)+(((n+1:ℕ):ℝ))⁻¹ := by
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
  refine ⟨r,?_⟩
  intro n
  refine ⟨hr n,?_⟩
  have HH:=div_le_div_of_nonneg_right (hbound n) (sq_nonneg (W n))
  have he : threshold n/(W n)^2=2*(I n/(W n)^3)+(((n+1:ℕ):ℝ))⁻¹ := by
    dsimp only [threshold]
    field_simp [(hW n).ne']
  rw [he] at HH
  exact HH

theorem exists_actual_minimum_bare_SK_polynomial_good_star_sequence
    (Bclock T : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW1 : ∀n,W n≤1) (hband : ∀n,max 1 (2*Az)*(M n).xs≤W n)
    (hb_const : ∀n u,(M n).b u=T) (hh_zero : ∀n u,(M n).h u=0) :
    ∃rstar:ℕ→ℝ,(∀n,rstar n∈Ioo (W n/2) (W n) ∧
      (cl/2)*W n≤(M n).alpha.val.val (rstar n) ∧ (M n).alpha.val.val (rstar n)≤cu*W n ∧
      (M n).alpha.val.val (rstar n)<1) ∧
      ∀ᶠn:ℕ in atTop,(M n).cavityRadiusPointDefect (rstar n)/(W n)^2≤
        ((n+1:ℕ):ℝ)^(-(min (delta/64) (1/16))/2) := by
  have hxsW n : (M n).xs≤W n := by
    have H:=mul_le_mul_of_nonneg_right (le_max_left 1 (2*Az)) (M n).hxs.le
    nlinarith [hband n]
  have hWp n : 0<W n := (M n).hxs.trans_le (hxsW n)
  have hthreshold n : (M n).z≤W n/2 := by
    have H:=mul_le_mul_of_nonneg_right (le_max_right 1 (2*Az)) (M n).hxs.le
    nlinarith [(M n).hzxs,hband n]
  obtain ⟨rstar,hpoint⟩:=radius_half_band_good_point_sequence_budget
    (fun n=>(M n).cavityRadiusPointDefect) W hWp
    (fun n=>(M n).cavityRadiusPointDefect_integrableOn (by linarith [hWp n]) (hW1 n))
  have hgeometry n : rstar n∈Ioo (W n/2) (W n) ∧
      (cl/2)*W n≤(M n).alpha.val.val (rstar n) ∧ (M n).alpha.val.val (rstar n)≤cu*W n ∧
      (M n).alpha.val.val (rstar n)<1 := by
    have hr:=(hpoint n).1
    have hreg:=(M n).regular (rstar n) ⟨(hthreshold n).trans hr.1.le,hr.2.le.trans (hW1 n)⟩
    have hlow : (cl/2)*W n≤(M n).alpha.val.val (rstar n) := by
      have H:=mul_le_mul_of_nonneg_left hr.1.le hcl.le
      nlinarith only [H,hreg.1]
    have hhigh:=hreg.2.trans (mul_le_mul_of_nonneg_left hr.2.le hcu.le)
    have hrpos : 0<rstar n := (div_pos (hWp n) (by norm_num)).trans hr.1
    have hr1 : rstar n<1 := hr.2.trans_le (hW1 n)
    have hstrict:=inverseConstraint_strictMonoOn (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).alpha.property ⟨hrpos.le,hr1.le⟩
      (by norm_num : (1:ℝ)∈Icc (0:ℝ) 1) hr1
    exact ⟨hr,hlow,hhigh,hstrict.trans_le ((M n).alpha.val.property.1 1).2⟩
  let t:=min (delta/64) (1/16)
  have ht : 0<t := lt_min (by positivity) (by norm_num)
  have ht1 : t≤1 := (min_le_right _ _).trans (by norm_num)
  have hshift : Tendsto (fun n:ℕ=>n+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k] with n hn
    omega
  have hcoeff:=hshift.eventually (eventually_coefficient_rpow_le
    (c:=3) (d:=1) (q:= -t) (r:= -t/2) (by norm_num) (by linarith))
  have H:=actual_minimum_bare_SK_half_band_polynomial_bound Bclock T hm hdelta hmargin
    hcl hcu hAz hC0 hCt M W hW1 hband hb_const hh_zero
  refine ⟨rstar,hgeometry,?_⟩
  filter_upwards [H,hcoeff] with n hn hnc
  have hN : 1≤((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos n
  have hNpos : 0<((n+1:ℕ):ℝ) := by positivity
  have hrecip : (((n+1:ℕ):ℝ))⁻¹≤((n+1:ℕ):ℝ)^(-t) := by
    rw [←Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hb:=(hpoint n).2
  change (M n).cavityRadiusPointDefect (rstar n)/(W n)^2≤
    2*((M n).cavityRadiusDefect (W n/2) (W n)/(W n)^3)+(((n+1:ℕ):ℝ))⁻¹ at hb
  have Hsmall : (M n).cavityRadiusPointDefect (rstar n)/(W n)^2≤
      3*((n+1:ℕ):ℝ)^(-t) := by
    dsimp only [t] at *
    linarith
  exact Hsmall.trans (by simpa only [one_mul] using hnc)

def NativePolynomialGoodStarSequenceSaving
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (l : ℕ) (kappa : ℝ) (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W rstar : ℕ→ℝ) : Prop :=
    ∃Craw : ℝ,0<Craw ∧ ∀ᶠn:ℕ in atTop,
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
          nativeRetainedCenteredMoment n l (M n).bf (M n).hf as u.val S≤((n+1:ℕ):ℝ)^(-kappa/4)*(W n)^(2*l) ∧
          |finitePhysicalMean (n+1) as (fun k=>((M n).bf (partitionPoint 0 as k):ℝ))
            (fun k=>((M n).hf (partitionPoint 0 as k):ℝ))
            (retainedMassPrefixIndex u.val as)-S|≤((n+1:ℕ):ℝ)^(-kappa/4)*W n

theorem eventually_actual_minimum_native_polynomial_moments_at_good_star_sequence
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
    NativePolynomialGoodStarSequenceSaving l kappa M W rstar := by
  dsimp only [NativePolynomialGoodStarSequenceSaving]
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
  have hcoeff:=hshift.eventually (eventually_coefficient_rpow_le
    (c:=2*Ks) (d:=1) (q:= -kappa) (r:= -kappa/2) (by norm_num) (by linarith))
  filter_upwards [hdefrate,hshift.eventually hraw,hshift.eventually hamp,hcoeff]
    with n hnpoint hnraw hnamp hncoeff
  intro extra hextra
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

theorem exists_actual_minimum_bare_SK_native_polynomial_good_star_all_orders
    (Bclock T : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW1 : ∀n,W n≤1) (hband : ∀n,max 1 (2*Az)*(M n).xs≤W n)
    (hb_const : ∀n u,(M n).b u=T) (hh_zero : ∀n u,(M n).h u=0) :
    ∃rstar:ℕ→ℝ,(∀n,rstar n∈Ioo (W n/2) (W n) ∧
      (cl/2)*W n≤(M n).alpha.val.val (rstar n) ∧ (M n).alpha.val.val (rstar n)≤cu*W n ∧
      (M n).alpha.val.val (rstar n)<1) ∧
      ∀l:ℕ,0<l→NativePolynomialGoodStarSequenceSaving l (min (delta/64) (1/16)/2) M W rstar := by
  obtain ⟨rstar,hr,hrate⟩:=exists_actual_minimum_bare_SK_polynomial_good_star_sequence
    Bclock T hm hdelta hmargin hcl hcu hAz hC0 hCt M W hW1 hband hb_const hh_zero
  refine ⟨rstar,hr,?_⟩
  intro l hl
  exact eventually_actual_minimum_native_polynomial_moments_at_good_star_sequence l hl
    (min (delta/64) (1/16)/2) (div_pos (lt_min (by positivity) (by norm_num)) (by norm_num))
    Bclock hm hdelta hmargin hcl hcu hAz hC0 hCt M W hW1 hband rstar (fun n=>(hr n).1)
    (fun n=>⟨(hr n).2.1,(hr n).2.2.1⟩) (by simpa only [neg_div] using hrate)

theorem native_polynomial_star_common_finite_degree {N kappa W X : ℝ} {l A : ℕ}
    (hN : 1≤N) (hkappa : 0<kappa) (hW : 0≤W) (hA : 0<A) (hlA : l≤A)
    (hX : X≤N^(-kappa/4)*W^(2*l)) :
    X≤(N^(-kappa/(8*(A:ℝ)))*W)^(2*l) := by
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hAr : 0<(A:ℝ) := by exact_mod_cast hA
  have hlAr : (l:ℝ)≤(A:ℝ) := by exact_mod_cast hlA
  have Hκ:=mul_le_mul_of_nonneg_left hlAr hkappa.le
  have he : (-kappa/(8*(A:ℝ)))*(2*l:ℕ)=(-kappa*(l:ℝ))/(4*(A:ℝ)) := by
    push_cast
    field_simp
    ring
  have hexp : -kappa/4≤(-kappa/(8*(A:ℝ)))*(2*l:ℕ) := by
    rw [he]
    apply (le_div_iff₀ (mul_pos (by norm_num) hAr)).mpr
    nlinarith
  have H:=Real.rpow_le_rpow_of_exponent_le hN hexp
  rw [Real.rpow_mul_natCast hNp.le] at H
  have HH:=mul_le_mul_of_nonneg_right H (pow_nonneg hW (2*l))
  exact hX.trans (by simpa only [mul_pow] using HH)

theorem polynomial_star_boundary_scale_calibration {N saving xs W : ℝ}
    (hN : 0<N) (_hsaving : 0<saving) (_hxs : 0<xs) (hW : 0<W)
    (hnear : W≤N^(saving/4)*xs) :
    N^(-saving)*W≤N^(-saving/2)*xs^2/W := by
  have H:=pow_le_pow_left₀ hW.le hnear 2
  have hepow : (N^(saving/4))^2=N^(saving/2) := by
    rw [←Real.rpow_mul_natCast hN.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  rw [mul_pow,hepow] at H
  have HH:=mul_le_mul_of_nonneg_left H (Real.rpow_nonneg hN.le (-saving))
  have he : N^(-saving)*(N^(saving/2)*xs^2)=N^(-saving/2)*xs^2 := by
    rw [←mul_assoc,←Real.rpow_add hN]
    congr 1
    congr 1
    ring
  rw [he] at HH
  apply (le_div_iff₀ hW).mpr
  simpa only [pow_two,mul_assoc] using HH

theorem nativeRetainedCenteredMoment_lower_order (n l A : ℕ) (hl : 0<l) (hlA : l≤A)
    (bf hf : ℝ→ℝ≥0) (as : List PositiveMass) (ho : MassOrdered 0 as)
    (u center rho : ℝ) (hrho : 0≤rho)
    (hA : nativeRetainedCenteredMoment n A bf hf as u center≤rho^(2*A)) :
    nativeRetainedCenteredMoment n l bf hf as u center≤rho^(2*l) := by
  let cut:=retainedMassPrefixIndex u as
  let T:=ClockTree.pairClock (S:=Spin (n+1)) as cut
  let q:=physicalCompletedClock (n+1) (fun j=>(bf (partitionPoint 0 as j):ℝ))
    (fun j=>(hf (partitionPoint 0 as j):ℝ))
  let F:=fun σ:T.Assignment=>orderedOverlap (n+1) (ClockTree.pairSpin as cut σ).1
    (ClockTree.pairSpin as cut σ).2-center
  have H:=T.disorderExpect_rpow_moment_le (uniformWeight_pos (n+1)) (finiteFeature (n+1))
    ho 0 q 0 F (p:=(2*l:ℕ)) (r:=(2*A:ℕ))
    (by exact_mod_cast (show 0<2*l by omega))
    (by exact_mod_cast (show 2*l≤2*A by omega)) hrho
    (by simpa only [Real.rpow_natCast,nativeRetainedCenteredMoment,nativeRetainedPairValue,T,q,F,cut] using hA)
  simpa only [Real.rpow_natCast,nativeRetainedCenteredMoment,nativeRetainedPairValue,T,q,F,cut] using H

def NativePolynomialGoodStarFiniteDegreeSaving
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (A : ℕ) (kappa : ℝ) (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W rstar : ℕ→ℝ) : Prop :=
    ∃Craw : ℝ,0<Craw ∧ ∀ᶠn:ℕ in atTop,
      ∀extra : List PositiveMass,(∀v∈extra,v.val≤1)→
      ∃u:PositiveMass,u.val=(M n).alpha.val.val (rstar n) ∧ u.val<1 ∧
        (cl/2)*W n≤u.val ∧ u.val≤cu*W n ∧
      ∃us:List PositiveMass,(∀v∈us,v.val≤1) ∧ u∈us ∧ (∀v∈extra,v∈us) ∧
        ∀ᶠj:ℕ in atTop,
          let as:=finiteCutMasses us j
          let q:=completedPathClock (n+1) (M n).bf (M n).hf
          let steps:=sampleClockSteps q 0 as
          let S:=orderedPathS (n+1) (M n).bf (M n).hf u.val
          (physicalRawRatio (n+1) (2*A-1) steps 0 (M n).xs
            (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id)^2≤2*Craw ∧
          (∀l:ℕ,0<l→l≤A→nativeRetainedCenteredMoment n l (M n).bf (M n).hf as u.val S≤
            (((n+1:ℕ):ℝ)^(-kappa/(8*(A:ℝ)))*W n)^(2*l)) ∧
          |finitePhysicalMean (n+1) as (fun k=>((M n).bf (partitionPoint 0 as k):ℝ))
            (fun k=>((M n).hf (partitionPoint 0 as k):ℝ))
            (retainedMassPrefixIndex u.val as)-S|≤((n+1:ℕ):ℝ)^(-kappa/4)*W n

theorem native_polynomial_star_sequence_to_finite_degree
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (A : ℕ) (hA : 0<A)
    (kappa : ℝ) (hkappa : 0<kappa)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W rstar : ℕ→ℝ) (hW : ∀n,0<W n)
    (hsource : NativePolynomialGoodStarSequenceSaving A kappa M W rstar) :
    NativePolynomialGoodStarFiniteDegreeSaving A kappa M W rstar := by
  obtain ⟨C,hC,H⟩:=hsource
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro extra hextra
  obtain ⟨u,huval,hu1,hlow,hupper,us,hus,hu,hret,hgrid⟩:=hn extra hextra
  refine ⟨u,huval,hu1,hlow,hupper,us,hus,hu,hret,?_⟩
  filter_upwards [hgrid] with j hj
  refine ⟨hj.1,?_,hj.2.2⟩
  intro l hl hlA
  have hN : 1≤((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos n
  have hWn : 0<W n := hW n
  have Hmax:=native_polynomial_star_common_finite_degree hN hkappa (hW n).le hA
    (le_rfl : A≤A) hj.2.1
  exact nativeRetainedCenteredMoment_lower_order n l A hl hlA (M n).bf (M n).hf
    (finiteCutMasses us j) (finiteCutMasses_ordered us hus j) u.val
    (orderedPathS (n+1) (M n).bf (M n).hf u.val)
    (((n+1:ℕ):ℝ)^(-kappa/(8*(A:ℝ)))*W n)
    (by positivity) Hmax

theorem exists_actual_minimum_bare_SK_native_polynomial_star_finite_degrees
    (Bclock T : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW1 : ∀n,W n≤1) (hband : ∀n,max 1 (2*Az)*(M n).xs≤W n)
    (hb_const : ∀n u,(M n).b u=T) (hh_zero : ∀n u,(M n).h u=0) :
    ∃rstar:ℕ→ℝ,(∀n,rstar n∈Ioo (W n/2) (W n) ∧
      (cl/2)*W n≤(M n).alpha.val.val (rstar n) ∧ (M n).alpha.val.val (rstar n)≤cu*W n ∧
      (M n).alpha.val.val (rstar n)<1) ∧
      ∀A:ℕ,0<A→NativePolynomialGoodStarFiniteDegreeSaving A (min (delta/64) (1/16)/2) M W rstar := by
  obtain ⟨rstar,hr,H⟩:=exists_actual_minimum_bare_SK_native_polynomial_good_star_all_orders
    Bclock T hm hdelta hmargin hcl hcu hAz hC0 hCt M W hW1 hband hb_const hh_zero
  have hW n : 0<W n := by
    have H:=mul_le_mul_of_nonneg_right (le_max_left 1 (2*Az)) (M n).hxs.le
    nlinarith [(M n).hxs,hband n]
  refine ⟨rstar,hr,?_⟩
  intro A hA
  exact native_polynomial_star_sequence_to_finite_degree A hA (min (delta/64) (1/16)/2)
    (div_pos (lt_min (by positivity) (by norm_num)) (by norm_num)) M W rstar hW (H A hA)

end OAI.SKFluctuations.LaplaceWindowFormalization
