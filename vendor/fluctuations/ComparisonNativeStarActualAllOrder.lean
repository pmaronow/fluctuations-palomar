module

public import ComparisonNativeStarActualBufferedSequence
public import ComparisonNativeStarExactPairTransfer
public import ComparisonSignedCavityActualCanonicalProjectionGeometry
public import ComparisonNativeStarMinimumProjectionMoment

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity NativeStarBuffer NativeOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 11000000
attribute [local instance] Classical.propDecidable

def actualBufferedStarPairConstant (p : ℕ) (Cs : ℝ) : ℝ :=
  (3:ℝ)^(2*(p+1)-1)*(1+5^(2*(p+1))+
    2^(4*(p+1)-2)*(32^(2*(p+1))+(Cs+5)^(2*(p+1))))

theorem eventually_star_pair_constant_absorbed
    (p : ℕ) (C : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠn : ℕ in atTop,∀W : ℝ,0 ≤ W →
      C*(((n+1:ℕ):ℝ)^(-(c/16)))^(p+1)*W^(2*(p+1)) ≤
        (((n+1:ℕ):ℝ)^(-(c/64))*W)^(2*(p+1)) := by
  have hl : 0 < ((p+1:ℕ):ℝ) := by positivity
  have H := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C) (d:=1)
      (q:=(-(c/16))*((p+1:ℕ):ℝ)) (r:=(-(c/32))*((p+1:ℕ):ℝ))
      zero_lt_one (by nlinarith))
  filter_upwards [H] with n hn
  intro W hW
  have hN : 0 < ((n+1:ℕ):ℝ) := by positivity
  have hp : (((n+1:ℕ):ℝ)^(-(c/16)))^(p+1)=
      ((n+1:ℕ):ℝ)^((-(c/16))*((p+1:ℕ):ℝ)) :=
    (Real.rpow_mul_natCast hN.le (-(c/16)) (p+1)).symm
  have hp' : (((n+1:ℕ):ℝ)^(-(c/64)))^(2*(p+1))=
      ((n+1:ℕ):ℝ)^((-(c/32))*((p+1:ℕ):ℝ)) := by
    rw [←Real.rpow_mul_natCast hN.le]
    congr 1
    push_cast
    ring
  rw [hp,mul_pow,hp']
  exact mul_le_mul_of_nonneg_right (by simpa only [one_mul] using hn) (pow_nonneg hW _)

def ActualNativeStarOrderSaving
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (p : ℕ) (Craw saving : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,
    ∀extra : List PositiveMass,(∀u∈extra,u.val ≤ 1) →
    ∃us : List PositiveMass,(∀u∈us,u.val ≤ 1) ∧ (∀u∈extra,u∈us) ∧ (w n).star∈us ∧
      ∀ᶠj : ℕ in atTop,
        let as := finiteCutMasses us j
        let q := completedPathClock (n+1) (M n).bf (M n).hf
        let steps := sampleClockSteps q 0 as
        (physicalRawRatio (n+1) (p+1) steps 0 (M n).xs
          (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id)^2 ≤ 2*Craw ∧
        nativeRetainedCenteredMoment n (p+1) (M n).bf (M n).hf as (w n).star.val
          (orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val) ≤
            (((n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1))

theorem eventually_actual_bare_native_star_order_at_slow_window
    (p : ℕ) {m delta cl cu Az C0 Ct D Bclock T L : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hL : 0 < L) {Ccal : ℝ} (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ)
    (hcanonical : ∀n,W n=max (M n).xs
      (Real.sqrt (laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)))
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hh : ∀n u,(M n).h u=0)
    (Cs : ℝ) (hCs : 0 < Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,IsActualCalibratedSlowWindow (M n) (W n) T L Cs (w n)) :
    ∃Craw : ℝ,0 < Craw ∧ ActualNativeStarOrderSaving p Craw
      (actualSlowWindowExponent m delta/64) M W w := by
  let c := actualSlowWindowExponent m delta
  have hc : 0 < c := actualSlowWindowExponent_pos hm hdelta hroom
  have Hc := (actualSlowWindowExponent_bounds hm hdelta).2.2
  have hprojection : 2*(c/8) < 3*m-delta-3*c := by linarith
  have hxs n : (M n).xs ≤ W n := by rw [hcanonical];exact le_max_left _ _
  have hW n : 0 < W n := (M n).hxs.trans_le (hxs n)
  obtain ⟨Craw,hCraw,Hbuffer⟩ := eventually_actual_slow_window_native_buffers p
    hm hdelta hroom hcl hcu hAz hC0 hCt hL M W hxs hWlim hh w hw
  obtain ⟨Kv,Cprof,Lcount,H0,hKv,hCprof,hLcount,hH0,Hgeometry⟩ :=
    eventually_actual_canonical_slow_window_projection_geometry hm hdelta hroom hcl hcu hAz hC0 hL
      hCcal M W hcanonical hWlim hcompare hh
  have Hkv := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=Kv) (d:=1) (q:=-(c/8)) (r:=-(c/16))
      zero_lt_one (by linarith))
  have Hproject := (tendsto_add_atTop_nat 1).eventually
    (eventually_actual_minimum_original_projection_moment p Bclock
      (cl:=cl) (cu:=cu) (Az:=Az) (Ddepth:=D)
      (c1:=3*c) (saving:=c/8) hm hC0 hCt hCprof.le hLcount.le
      (by positivity : 0 ≤ 2*Craw) hH0.le hprojection)
  have Hconstant := eventually_star_pair_constant_absorbed p (actualBufferedStarPairConstant p Cs) hc
  refine ⟨Craw,hCraw,?_⟩
  filter_upwards [Hbuffer,Hgeometry,Hproject,Hkv,Hconstant,hw] with n hnBuffer hnGeom hnProj hnKv hnConst hnWindow
  intro extra hextra
  have hWn : 0 < W n := hW n
  have hN1 : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos n
  obtain ⟨us,hus,hretain,hbudget⟩ := hnBuffer extra hextra
  obtain ⟨p0,p1,p3,p4,hp0,hp1,hp3,hp4,hr0,hr1,hr3,hr4,hrstar,Hdata⟩ := hbudget
  obtain ⟨_,_,hxv,hv1,HG⟩ := hnGeom
  have Hgeom := HG T Cs (w n) hnWindow p3 hp3 us hus hrstar hr3
  obtain ⟨potential,_,_,_,_,_,_,_,_,_,hSlo,hShi,_⟩ := hnWindow
  have had := comparisonVariableEndpoint_clocks_admissible (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).context.hm (M n).context.hM (M n).b (M n).h
    (M n).context.hd.ne' (M n).hlam.le (M n).hlb (M n).hb (M n).hh (M n).hh0 (M n).alpha
  have hbf := toNNReal_monotoneOn had.1
  have hhf := toNNReal_monotoneOn had.2.1
  have hSnonneg : 0 ≤ orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val := by
    have hcstar : 0 < starMassBandConstant cu Az/cu := div_pos (star_mass_band_constant_pos hcu hAz) hcu
    exact (mul_pos (by positivity : 0 < 3*(starMassBandConstant cu Az/cu)/4) (hW n)).le.trans hSlo
  have hSabs : |orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val| ≤ Cs*W n := by
    rw [abs_of_nonneg hSnonneg]
    exact hShi
  have hScaled : ((n+1:ℕ):ℝ)^(-(c/8))*(Kv*W n) ≤ ((n+1:ℕ):ℝ)^(-(c/16))*W n := by
    have H := mul_le_mul_of_nonneg_right hnKv (hW n).le
    simpa only [one_mul,mul_assoc,mul_left_comm,mul_comm] using H
  refine ⟨us,hus,hretain,hrstar,?_⟩
  filter_upwards [Hdata,Hgeom] with j hj hjGeom
  let as := finiteCutMasses us j
  let ho := finiteCutMasses_ordered us hus j
  let q := completedPathClock (n+1) (M n).bf (M n).hf
  let steps := sampleClockSteps q 0 as
  let fork := (physicalRetainedIndex steps (w n).star.val).val
  let t := (physicalRetainedIndex steps p3.val).val
  let S := orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val
  let epsilon := ((n+1:ℕ):ℝ)^(-(c/16))
  obtain ⟨B,_,_,hCm,hCp,hEta,hRaw⟩ := hj
  have hProj := hnProj (M n) as ho fork t (H0/(Kv*W n)) (Kv*W n)
    ((M n).context.N^(-(3*c))) (by positivity) hxv hv1 le_rfl hjGeom hRaw
  have hProjW : physicalOverlapProjectionErrorMoment (n+1) (p+1) steps
      (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id fork t ≤
        (epsilon*W n)^(2*(p+1)) := by
    exact hProj.trans (pow_le_pow_left₀ (by positivity) hScaled _)
  have heps : 0 < epsilon := by dsimp only [epsilon];positivity
  have heps1 : epsilon ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    hN1 (by linarith)
  have Hstar := physical_star_from_buffer_data_polynomial (n+1) (p+1) (by omega)
    steps (sampleClockSteps_ordered q as ho) (q 0) fork t S B heps heps1 (hW n).le hCs.le
    hSabs hCm hCp hEta hProjW
  have Hnative := nativeRetainedCenteredMoment_eq_physicalStar n (p+1) (M n).bf (M n).hf
    hbf hhf as ho (w n).star.val S
  refine ⟨hRaw,?_⟩
  rw [Hnative]
  exact Hstar.trans (hnConst (W n) (hW n).le)

theorem exists_actual_bare_native_star_all_orders
    {m delta cl cu Az C0 Ct D Bclock T L Ccal : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hT : 0 < T) (hL : 0 < L) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ)
    (hcanonical : ∀n,W n=max (M n).xs
      (Real.sqrt (laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)))
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hb : ∀n u,(M n).b u=T) (hh : ∀n u,(M n).h u=0) :
    let saving := actualSlowWindowExponent m delta/64
    0 < saving ∧ ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn : ℕ in atTop,IsActualCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
      ∀p : ℕ,∃Craw : ℝ,0 < Craw ∧ ActualNativeStarOrderSaving p Craw saving M W w := by
  have hxs n : (M n).xs ≤ W n := by rw [hcanonical];exact le_max_left _ _
  have hscale n : laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs ≤ (W n)^2 := by
    rw [hcanonical]
    exact (M n).canonical_scale_strength_upper
  obtain ⟨Cs,hCs,w,hw⟩ := exists_actual_bare_calibrated_slow_window_sequence
    hm hdelta hroom hcl hcu hAz hC0 hCt hT hL M W hxs hWlim hscale hb hh
  have hc := actualSlowWindowExponent_pos hm hdelta hroom
  refine ⟨by positivity,Cs,hCs,w,hw,?_⟩
  intro p
  exact eventually_actual_bare_native_star_order_at_slow_window p
    hm hdelta hroom hcl hcu hAz hC0 hCt hL hCcal M W hcanonical hWlim hcompare hh Cs hCs w hw

end OAI.SKFluctuations.LaplaceWindowFormalization
