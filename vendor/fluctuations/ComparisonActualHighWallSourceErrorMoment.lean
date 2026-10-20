module

public import ComparisonActualHighWallRestRawMoments
public import ComparisonSignedCavitySourceErrorMoment

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

private theorem weighted_centered_nat_moment_le
    {ι : Type*} [Fintype ι] (w F : ι→ℝ) (center A C scale : ℝ) (p : ℕ)
    (hp : 0 < p) (hw : ∀i,0 ≤ w i) (hws : ∑i,w i=1)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hs : 0 ≤ scale)
    (Hraw : ∑i,w i*|F i|^p ≤ (A*scale)^p) (Hcenter : |center| ≤ C*scale) :
    ∑i,w i*|F i-center|^p ≤ (4*(A+C)*scale)^p := by
  have Hpt i : |F i-center|^p ≤ (2:ℝ)^p*(|F i|^p+|center|^p):=by
    have Htri : |F i-center| ≤ 2*max |F i| |center|:=by
      have H:=abs_sub_le (F i) 0 center
      simp only [sub_zero,zero_sub,abs_neg] at H
      linarith [le_max_left |F i| |center|,le_max_right |F i| |center|]
    apply (pow_le_pow_left₀ (abs_nonneg _) Htri p).trans
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rcases le_total |F i| |center| with h|h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (by positivity)
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (by positivity)
  have Hsum:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>mul_le_mul_of_nonneg_left (Hpt i) (hw i))
  have Heq : (∑i,w i*((2:ℝ)^p*(|F i|^p+|center|^p)))=
      (2:ℝ)^p*((∑i,w i*|F i|^p)+|center|^p):=by
    simp_rw [mul_add,mul_left_comm (w _) ((2:ℝ)^p)]
    rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,←Finset.sum_mul,hws,one_mul]
  rw [Heq] at Hsum
  apply Hsum.trans
  have Hc:=pow_le_pow_left₀ (abs_nonneg center) Hcenter p
  have HA : (A*scale)^p ≤ ((A+C)*scale)^p:=pow_le_pow_left₀ (mul_nonneg hA hs)
    (mul_le_mul_of_nonneg_right (by linarith) hs) p
  have HC : (C*scale)^p ≤ ((A+C)*scale)^p:=pow_le_pow_left₀ (mul_nonneg hC hs)
    (mul_le_mul_of_nonneg_right (by linarith) hs) p
  have H2 : (2:ℝ) ≤ (2:ℝ)^p:=by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hp
  calc
    _ ≤ (2:ℝ)^p*((A*scale)^p+(C*scale)^p):=
      mul_le_mul_of_nonneg_left (add_le_add Hraw Hc) (by positivity)
    _ ≤ (2:ℝ)^p*(2*((A+C)*scale)^p):=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ ≤ (2:ℝ)^p*((2:ℝ)^p*((A+C)*scale)^p):=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right H2 (by positivity)) (by positivity)
    _=(4*(A+C)*scale)^p:=by rw [←mul_pow,←mul_pow];congr 1;ring

theorem eventually_actual_high_wall_canonical_source_error_even_bound
    (order : ℕ) (horder : 0 < order) (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀(L : ℕ) (us : List PositiveMass),(∀u∈us,u.val ≤ 1)→
        (∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ M.xs→
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as→
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (a : ℕ)
          (G : ActualNaturalBoundaryShape n a T) (s e f : T.cavityLeft.Slot),e≠f→
        ∀E : NativeCanonicalExteriorSource n a pre mid tail T s G 0 q 0,
        ∀error : E.D.Assignment→ℝ,
          let j:=T.cavityLeft.splitIndex e f
          let center:=orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
          (∀η ζ δ,deletedOverlap n (joinSpin (T.cavityLeft.atSlot (E.read η ζ δ) e,false))
            (joinSpin (T.cavityLeft.atSlot (E.read η ζ δ) f,false))-center=error δ)→
          nativeRootTestExpect n E.D (nativeStarSuffixClock n pre mid q)
            (nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0)
            exteriorForestStarRoot (fun _ δ=>error δ^(2*order)) ≤ 
            (C*(M.xs+partitionPoint 0 as j))^(2*order) := by
  let Bclock0:=max Bclock 0
  obtain ⟨Cd,hCd,HR⟩:=eventually_actual_high_wall_deleted_raw_on_retained_net
    (D:=D) order horder Bclock (2*Bclock0) Bclock0 hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_high_wall_continuum_center_bound
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨4*(Cd+Cs),by positivity,?_⟩
  filter_upwards [HR,(tendsto_add_atTop_nat 1).eventually HS,eventually_gt_atTop (0:ℕ)] with n hn hnS hn0
  let : Nonempty (RestCoordinate n):=⟨Sum.inr ⟨0,hn0⟩⟩
  intro M L us hus hret hmesh
  filter_upwards [hn M L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut T a G s e f hef E error herror
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let j:=T.cavityLeft.splitIndex e f
  let center:=orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let R:=fun σ τ : Spin n=>deletedOverlap n (joinSpin (σ,false)) (joinSpin (τ,false))
  let Q:=fun σ τ=>R σ τ-center
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
  have hj : j ≤ (pre++(mid++tail)).length:=T.cavityLeft.splitIndex_le_clockLength e f
  have hjAs : j ≤ as.length:=by simpa only [hcut,as] using hj
  have hu:=partitionPoint_mem as (finiteCutMasses_ordered us hus k) j
  have HC:=M.data.full_square_clock_budget M.alpha as (finiteCutMasses_ordered us hus k)
  have HCB : finitePhysicalMixedClock (n+1) as b h as.length+b as.length+h as.length ≤ 2*Bclock0:=
    HC.trans (by dsimp only [Bclock0];nlinarith only [M.hT,le_max_left Bclock (0:ℝ)])
  have HT:=M.data.total_clock_le M.alpha _ (partitionPoint_mem as (finiteCutMasses_ordered us hus k) as.length)
  have HB : b as.length ≤ Bclock0:=by
    have Hp:=(M.hf (partitionPoint 0 as as.length)).coe_nonneg
    dsimp only [b,Bclock0];linarith only [HT,Hp,M.hT,le_max_left Bclock (0:ℝ)]
  have HRj:=hk j hjAs HCB HB
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from M.data.bf_monotone M.alpha hu hv huv) as (finiteCutMasses_ordered us hus k)
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from M.data.hf_monotone M.alpha hu hv huv) as (finiteCutMasses_ordered us hus k)
  rw [E.error_moment_eq ho (fun σ=>Q (T.cavityLeft.atSlot σ e) (T.cavityLeft.atSlot σ f)) error herror]
  rw [T.cavityLeft.disorderExpect_pairAtSlot_actual (restWeight_pos n) (restFeature n) ho 0 q 0 e f hef
    (fun σ τ=>Q σ τ^(2*order))]
  let V:=pairClock (S:=Spin n) (pre++(mid++tail)) j
  have Hraw:=native_original_rest_deleted_even_le_raw n order hn0 ho b h hbm hhm
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) j hj
  have Hraw' : V.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>|R (pairSpin (pre++(mid++tail)) j σ).1 (pairSpin (pre++(mid++tail)) j σ).2|^(2*order)) 0 ≤ 
      (Cd*(M.xs+partitionPoint 0 as j))^(2*order):=by
    simpa only [V,R,b,h,q,as,hcut] using Hraw.trans (by simpa only [hcut,b,h,as] using HRj)
  have Hcenter : |center| ≤ Cs*(M.xs+partitionPoint 0 as j):=by
    dsimp only [center]
    rw [native_ordered_source_center_eq_completed n M.bf M.hf (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) hu]
    exact hnS M _ hu
  have hw:=V.disorderWeight_probability (restWeight_pos n) (restFeature n) ho 0 q 0
  have H:=weighted_centered_nat_moment_le (fun σ=>V.disorderWeight (restWeight n) (restFeature n) 0 q σ 0)
    (fun σ=>R (pairSpin (pre++(mid++tail)) j σ).1 (pairSpin (pre++(mid++tail)) j σ).2)
    center Cd Cs (M.xs+partitionPoint 0 as j) (2*order) (by omega) hw.1 hw.2 hCd.le hCs.le
    (add_nonneg M.hxs.le hu.1) Hraw' Hcenter
  simpa only [ClockTree.disorderExpect,(even_two_mul order).pow_abs,Q,V] using H

end OAI.SKFluctuations.Cavity
