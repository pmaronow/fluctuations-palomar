module

public import ComparisonSignedCavityActualMinimumResampling

@[expose] public section

noncomputable section
set_option maxHeartbeats 5000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity

theorem eventually_native_minimum_macroscopic_boundary_resampling
    (ell : ℕ) (Bclock ce Rmacro F : ℝ)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (hce : 0<ce) (hmacro : 0<Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∀ᶠ n : ℕ in atTop,
      ∀ a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀ (u : PositiveMass),u.val ≤ 1 →
      ∀ (extra : List PositiveMass),(∀v∈extra,v.val ≤ 1) →
      ∃ us : List PositiveMass,(∀v∈us,v.val ≤ 1) ∧ u∈us ∧ (∀v∈extra,v∈us) ∧
        ∀ᶠ j : ℕ in atTop,
          let as := finiteCutMasses us j
          let steps := sampleClockSteps (completedPathClock n a.bf a.hf) 0 as
          let Q := stepClockValues (fun i=>(completedPathClock n a.bf a.hf 0 i:ℝ)) steps
          ∀ (W r : ℝ) (low high : ℕ),0<W → 0<r →
            W ≤ Rmacro/2 → a.xs ≤ Rmacro/2 → a.z ≤ Rmacro/4 →
            (n:ℝ)^(-(1:ℝ)/6+m) ≤ r →
            ce*W^2 ≤ laplaceComparisonStrength a.context.d a.lam W →
            high ≤ as.length → a.R (partitionPoint 0 as low) ≤ Rmacro/4 →
            Rmacro ≤ a.R (partitionPoint 0 as high) →
            originalBoundaryResamplingMoment n (ell+1) as Q low high ≤
              (2*(n:ℝ)^(-eta)*savedExteriorScale r W (partitionPoint 0 as high))^(2*(ell+1)) := by
  obtain ⟨C,hC,hraw⟩ := eventually_native_minimum_original_boundary_raw
    ell Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let s := Rmacro/2
  let H₀ := F/((cl/8)^2*s)
  have hs : 0<s := by dsimp [s];positivity
  have hF : 0≤F := by linarith
  have hH₀ : 0≤H₀ := by dsimp [H₀];positivity
  have hsave := eventually_original_boundary_resampling_from_full_schedule ell 0 0 Bclock 256 (2*C) H₀ (ce/24)
    (by norm_num) (by positivity) hH₀ (by positivity) hgap
  have hlog : ∀ᶠ n : ℕ in atTop,1≤Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hraw,hsave,eventually_comparisonLowerScale_depth hC0 hm,hlog,eventually_gt_atTop (1:ℕ)]
    with n hnraw hnsave hndepth hnlog hn1
  intro a u hu extra hextra
  let c := a.context
  have hN1 : (1:ℝ)≤c.N := by exact_mod_cast hn1.le
  have hnd : 1/c.N≤c.d := by
    have H := hndepth c.E c.d c.hE c.hd a.hlower
    have H' : comparisonLowerScale n c.E c.d≤c.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ c.hd).mpr (by simpa only [pow_two] using a.hupper)
    exact H.trans H'
  obtain ⟨us,hus,huus,hextraus,hfinite⟩ := hnraw a u hu extra hextra
  have hmesh : ∀ᶠ j : ℕ in atTop,(((j+1:ℕ):ℝ)⁻¹)/c.floor ≤ s/16 := by
    apply ((uniformMasses_mesh_tendsto.div_const c.floor).eventually
      (gt_mem_nhds (show 0/c.floor<s/16 by simpa only [zero_div] using
        (show 0<s/16 by positivity)))).mono
    intro j hj
    simpa using hj.le
  refine ⟨us,hus,huus,hextraus,?_⟩
  filter_upwards [hfinite,hmesh] with j hj hmj
  dsimp only at hj ⊢
  intro W r low high hW hr hWs hxss hzs hrscale hstrength hhigh hlow hhighradius
  have ho := finiteCutMasses_ordered us hus j
  have hend := finiteCutMasses_end us hus j
  have hpart := finiteCutMasses_mesh us hus j
  have hmeshnonneg : 0≤(((j+1:ℕ):ℝ)⁻¹) := by positivity
  have hregular : ∀v∈Icc (s/2) 1,cl*v ≤ a.alpha.val.val v ∧ a.alpha.val.val v ≤ cu*v := by
    intro v hv
    apply a.regular v
    refine ⟨?_,hv.2⟩
    have hvlow := hv.1
    dsimp only [s] at hvlow
    linarith
  have hJmacro : Rmacro ≤ (2:ℝ)^1*s := by dsimp [s];norm_num;linarith
  have hJone : (2:ℝ)^1*s ≤ 1 := by dsimp [s];norm_num;linarith
  obtain ⟨cs,t,anchor,duration,hlen,hlt,hth,htlen,hlast,hends,hclocks,hscales,hcount,hDpos⟩ :=
    exists_actual_comparison_boundary_projection_schedule (J:=1) (low:=low) (high:=high) n c.hn c.hc c.hk c.hkc c.hm c.hM
      a.alpha a.b a.h a.hb a.hlb a.hh a.hh0 hN1 hnlog c.hd hnd a.hlam a.hld
      (finiteCutMasses us j) ho hend hmeshnonneg hpart hs hmj hW hWs hce hstrength
      hcl hcu.le hmacro hFmass hFradius a.hxs.le hxss hregular (by norm_num : 1≤(1:ℕ))
      hJmacro hJone hhigh
      (by change a.R (partitionPoint 0 (finiteCutMasses us j) low) ≤ s/2; dsimp [s];linarith)
      (by change 2*s ≤ a.R (partitionPoint 0 (finiteCutMasses us j) high); dsimp [s];linarith) a.clockBudget
  have hv1 : partitionPoint 0 (finiteCutMasses us j) high ≤ 1 :=
    (partitionPoint_mem _ ho high).2
  have hrange : a.R (partitionPoint 0 (finiteCutMasses us j) high)∈Icc a.z 1 := by
    exact ⟨by linarith,(comparisonSweepQuantile_bounds c.hc c.hk c.hkc c.hm c.hM a.alpha _).2⟩
  have hlower := (a.regular _ hrange).1
  rw [comparisonSweepQuantile_spec c.hc c.hk c.hkc c.hm c.hM a.alpha
    (partitionPoint_mem _ ho high)] at hlower
  have hv : 0<partitionPoint 0 (finiteCutMasses us j) high :=
    lt_of_lt_of_le (mul_pos hcl (hmacro.trans_le hhighradius)) hlower
  have hanchor : H₀ ≤ H₀/partitionPoint 0 (finiteCutMasses us j) high := by
    apply (le_div_iff₀ hv).mpr
    exact (mul_le_mul_of_nonneg_left hv1 hH₀).trans_eq (mul_one H₀)
  have hcount' : ((physicalOverlapResidualPairs cs).card:ℝ)^2 ≤ (256:ℝ)*(Real.log (n:ℝ))^0 := by
    norm_num at hcount ⊢
    exact hcount
  let steps := sampleClockSteps (completedPathClock n a.bf a.hf) 0 (finiteCutMasses us j)
  let Q := stepClockValues (fun i=>(completedPathClock n a.bf a.hf 0 i:ℝ)) steps
  have heq : clockSteps (finiteCutMasses us j) (cumulativeIncrements (Q 0) (fun z=>Q (z+1)))=steps :=
    sampled_clockSteps_native n (completedPathClock n a.bf a.hf) (finiteCutMasses us j) ho
  apply hnsave (finiteCutMasses us j) ho Q low high t hlt hth hhigh
    (ce*W^3/(24*Real.log (n:ℝ))) a.xs H₀ r W (partitionPoint 0 (finiteCutMasses us j) high)
    hDpos a.hxs hH₀ hr hW hv hrscale cs anchor duration
  · simpa only [heq,steps] using hlast
  · simpa only [heq,steps] using hends
  · simpa only [heq,steps] using hclocks
  · simpa only [heq,steps,H₀] using hscales
  · exact hcount'
  · rw [heq]
    simpa only [Q,stepClockValues_zero,Real.toNNReal_coe,pow_zero,mul_one,steps] using hj.1
  · exact hanchor
  · ring_nf
    exact le_rfl

theorem eventually_native_minimum_calibrated_macroscopic_boundary_resampling
    (ell : ℕ) (Bclock Ccal Rmacro F : ℝ)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (hCcal : 1≤Ccal) (hmacro : 0<Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∀ᶠ n : ℕ in atTop,
      ∀ a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      a.xs^2 ≤ Ccal^2*laplaceComparisonStrength a.context.d a.lam a.xs →
      ∀ (u : PositiveMass),u.val ≤ 1 →
      ∀ (extra : List PositiveMass),(∀v∈extra,v.val ≤ 1) →
      ∃ us : List PositiveMass,(∀v∈us,v.val ≤ 1) ∧ u∈us ∧ (∀v∈extra,v∈us) ∧
        ∀ᶠ j : ℕ in atTop,
          let as := finiteCutMasses us j
          let steps := sampleClockSteps (completedPathClock n a.bf a.hf) 0 as
          let Q := stepClockValues (fun i=>(completedPathClock n a.bf a.hf 0 i:ℝ)) steps
          let W := max a.xs (Real.sqrt (laplaceComparisonStrength a.context.d a.lam a.xs))
          ∀ (low high : ℕ),W ≤ Rmacro/2 → a.z ≤ Rmacro/4 →
            high ≤ as.length → a.R (partitionPoint 0 as low) ≤ Rmacro/4 →
            Rmacro ≤ a.R (partitionPoint 0 as high) →
            originalBoundaryResamplingMoment n (ell+1) as Q low high ≤
              (2*(n:ℝ)^(-eta)*savedExteriorScale (C0*a.xs) W (partitionPoint 0 as high))^(2*(ell+1)) := by
  have hCcalpos : 0<Ccal := zero_lt_one.trans_le hCcal
  filter_upwards [eventually_native_minimum_macroscopic_boundary_resampling (D:=D)
    ell Bclock (1/Ccal^3) Rmacro F hm hdelta hroom hgap hcl hcu hAz hC0 hCt
    (by positivity) hmacro hRhalf hFmass hFradius] with n hn
  intro a hcompare u hu extra hextra
  obtain ⟨us,hus,huus,hextraus,hfinite⟩ := hn a u hu extra hextra
  obtain ⟨hW,hWd,hstrength⟩ := actual_direct_test_calibration_strength a.context.hd a.hlam a.hld
    a.hxs hCcal hcompare
  have hcritical := native_minimum_original_boundary_critical_radius hC0 a
  refine ⟨us,hus,huus,hextraus,?_⟩
  filter_upwards [hfinite] with j hj
  dsimp only at hj ⊢
  intro low high hWs hzs hhigh hlow hhighradius
  have hxss : a.xs ≤ Rmacro/2 := (le_max_left _ _).trans hWs
  exact hj _ (C0*a.xs) low high hW (mul_pos hC0 a.hxs) hWs hxss hzs hcritical hstrength
    hhigh hlow hhighradius

end OAI.SKFluctuations.LaplaceWindowFormalization
