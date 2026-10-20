module

public import ComparisonActualHighWallSourceClockBudget
public import ComparisonActualHighWallBoundaryResampling
public import ComparisonNativeActualUniformBandL1Density

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_site_le_square
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) :
    ∀ᶠ n : ℕ in atTop,
      ∀a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      a.xs=a.data.d → 3/((n+1:ℕ):ℝ) ≤ a.data.d^2 := by
  have Hrate:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=3*C0^2) (d:=1) (q:=-(1:ℝ))
      (r:=-(1:ℝ)/3+2*m) (by norm_num) (by linarith))
  filter_upwards [Hrate] with n hn
  intro a hxs
  have Hcrit:=actual_high_wall_original_boundary_critical_radius hC0 a
  rw [hxs] at Hcrit
  have Hsq:=pow_le_pow_left₀ (Real.rpow_pos_of_pos a.data.hN _).le Hcrit 2
  have Hpow : (((n+1:ℕ):ℝ)^(-(1:ℝ)/6+m))^2=
      ((n+1:ℕ):ℝ)^(-(1:ℝ)/3+2*m) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul a.data.hN.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  rw [Hpow,mul_pow] at Hsq
  have Hn : 3*C0^2/((n+1:ℕ):ℝ) ≤ C0^2*a.data.d^2 := by
    have hn' := hn
    rw [Real.rpow_neg_one,one_mul] at hn'
    have Hbase : 3*C0^2/((n+1:ℕ):ℝ) ≤ ((n+1:ℕ):ℝ)^(-(1:ℝ)/3+2*m) := by
      simpa only [div_eq_mul_inv] using hn'
    exact Hbase.trans Hsq
  have Hmul : C0^2*(3/((n+1:ℕ):ℝ)) ≤ C0^2*a.data.d^2 := by
    convert Hn using 1 <;> ring
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hC0)).mp (by simpa only [mul_comm] using Hmul)

theorem eventually_actual_high_wall_current_low_density_bigO
    (Bclock Ccut : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcut : 0 ≤ Ccut) :
    ∃C : ℝ,0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      a.xs=a.data.d →
      ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) → ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(a.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(a.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n a.bf a.hf as
        ∀U : ℕ,U ≤ as.length → partitionPoint 0 as U ≤ min (Ccut*a.data.d) 1 →
        ∀l t : ℝ,l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
          ClockTree.edgeBudget 0 as
            (nativeWholeLawErrorRadius n as
              (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
              (cutLowError n U b h K)) ≤ C*a.data.d^2 := by
  obtain ⟨KB,hKB,HB⟩:=eventually_actual_high_wall_B_normalized (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let J:=Real.sqrt KB*(1+Ccut)*Ccut
  let Cerr:=actualLowErrorComparisonConstant (2*Bclock) Bclock
  let C:=|Cerr| * (J+1)+1
  have hJ : 0 ≤ J := by dsimp only [J];positivity
  have hC : 0 < C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually HB,
    eventually_actual_high_wall_site_le_square hm hC0] with n hnB hnsite
  intro a hxs us hus
  have hT : 0 ≤ a.data.T := a.data.hepsilon.1.le.trans a.data.hepsilon.2.le
  have hBclock : 0 ≤ Bclock := hT.trans a.hT
  have hCerr : 0 ≤ Cerr := actualLowErrorComparisonConstant_nonneg _ hBclock
  have HCerr : actualLowErrorComparisonConstant (2*a.data.T) a.data.T ≤ Cerr := by
    unfold Cerr actualLowErrorComparisonConstant
    gcongr
    · exact a.hT
    · exact a.hT
    · exact a.hT
  have Hsite:=hnsite a hxs
  filter_upwards [original_band_l1_density_on_all_final_nets n a.bf a.hf
    (a.data.bf_monotone a.alpha) (a.data.hf_monotone a.alpha)] with jGrid hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  have ho:=finiteCutMasses_ordered us hus jGrid
  intro U hU hcut l t hl ht
  let b:=fun j=>(a.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(a.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n a.bf a.hf as
  let R:=nativeWholeLawErrorRadius n as
    (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
    (cutLowError n U b h K)
  let Q:=fun u=>Real.sqrt (orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)
  have hqU:=partitionPoint_mem as ho U
  have hmass : partitionPoint 0 as U ≤ Ccut*a.data.d := hcut.trans (min_le_left _ _)
  have hQi : IntervalIntegrable Q volume 0 1 := native_intervalIntegrable_sqrt_of_intervalIntegrable
    (physicalOrderedThermal_intervalIntegrable n a.bf a.hf
      (a.data.bf_monotone a.alpha) (a.data.hf_monotone a.alpha))
  have hQbound (u : ℝ) (hu : u∈Ioo (0:ℝ) (partitionPoint 0 as U)) :
      Q u ≤ Real.sqrt KB*(1+Ccut)*a.data.d := by
    have hu1 : u∈Ioc (0:ℝ) 1 := ⟨hu.1,hu.2.le.trans hqU.2⟩
    have H:=hnB a u hu1
    rw [hxs] at H
    have HH:=Real.sqrt_le_sqrt (show orderedPathB (n+1) a.bf a.hf u-
        (orderedPathS (n+1) a.bf a.hf u)^2 ≤ KB*(a.data.d+u)^2 from
      (sub_le_self _ (sq_nonneg _)).trans H)
    have hup : 0 ≤ a.data.d+u := by linarith [a.data.hd,hu.1]
    rw [Real.sqrt_mul hKB.le,Real.sqrt_sq_eq_abs,abs_of_nonneg hup] at HH
    exact HH.trans (by
      have Hmul:=mul_le_mul_of_nonneg_left (show a.data.d+u ≤ (1+Ccut)*a.data.d from by
        nlinarith [hu.2.le.trans hmass]) (Real.sqrt_nonneg KB)
      nlinarith only [Hmul])
  have hQint : (∫u in (0:ℝ)..partitionPoint 0 as U,Q u) ≤ J*a.data.d^2 := by
    have hsub : uIcc (0:ℝ) (partitionPoint 0 as U)⊆uIcc (0:ℝ) 1 := by
      rw [uIcc_of_le hqU.1,uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hqU.2
    have H:=intervalIntegral.integral_mono_on_of_le_Ioo hqU.1 (hQi.mono_set hsub)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ=>Real.sqrt KB*(1+Ccut)*a.data.d)
        volume 0 (partitionPoint 0 as U)) hQbound
    rw [intervalIntegral.integral_const,smul_eq_mul,sub_zero] at H
    apply H.trans
    have Hmul:=mul_le_mul_of_nonneg_right hmass
      (show 0 ≤ Real.sqrt KB*(1+Ccut)*a.data.d from
        mul_nonneg (mul_nonneg (Real.sqrt_nonneg KB)
          (show 0 ≤ 1+Ccut from by linarith)) a.data.hd.le)
    convert Hmul using 1 <;> dsimp only [J] <;> ring
  have Hmono:=actual_low_edgeBudget_mono ho (fun j hjlen=>
    a.data.current_low_error_radius_le_original a.alpha as ho U hl ht j hjlen)
  have HC : ClockTree.edgeBudget 0 as R ≤
      actualLowErrorComparisonConstant (2*a.data.T) a.data.T*
        ClockTree.edgeBudget 0 as (fun j=>if j<U then nativeOriginalCutLowErrorRadius n a.bf a.hf as j+
          1/(n+1:ℕ) else 0) := by
    have Hlin:=actual_low_edgeBudget_linear as 0
      (actualLowErrorComparisonConstant (2*a.data.T) a.data.T) 0
      (fun j=>if j<U then nativeOriginalCutLowErrorRadius n a.bf a.hf as j+1/(n+1:ℕ) else 0)
      (fun _=>0)
    simp only [zero_mul,add_zero] at Hlin
    have Hfunc : (fun j=>if j<U then actualLowErrorComparisonConstant (2*a.data.T) a.data.T*
        (nativeOriginalCutLowErrorRadius n a.bf a.hf as j+1/(n+1:ℕ)) else 0)=
        (fun j=>actualLowErrorComparisonConstant (2*a.data.T) a.data.T*
          (if j<U then nativeOriginalCutLowErrorRadius n a.bf a.hf as j+1/(n+1:ℕ) else 0)) := by
      funext j
      split_ifs <;> simp
    rw [Hfunc,Hlin] at Hmono
    convert Hmono using 1 <;> rfl
  have HBnd:=hj us hus 0 U (Nat.zero_le _) hU
  have hzero : partitionPoint 0 as 0=0 := by cases as <;> rfl
  simp only [Nat.not_lt_zero,ite_false] at HBnd
  rw [hzero] at HBnd
  have Horig : ClockTree.edgeBudget 0 as (fun j=>if j<U then nativeOriginalCutLowErrorRadius n a.bf a.hf as j+
      1/(n+1:ℕ) else 0) ≤ (J+1)*a.data.d^2 := by
    apply HBnd.trans
    nlinarith only [hQint,Hsite]
  have Horig0 : 0 ≤ ClockTree.edgeBudget 0 as
      (fun j=>if j<U then nativeOriginalCutLowErrorRadius n a.bf a.hf as j+1/(n+1:ℕ) else 0) := by
    apply ClockTree.edgeBudget_nonneg ho
    intro j
    split_ifs
    · exact add_nonneg (Real.sqrt_nonneg _) (by positivity)
    · exact le_rfl
  have Hscalar:=mul_le_mul_of_nonneg_right HCerr Horig0
  apply HC.trans (Hscalar.trans _)
  have Hlast:=mul_le_mul_of_nonneg_left Horig hCerr
  apply Hlast.trans
  dsimp only [C]
  rw [abs_of_nonneg hCerr]
  nlinarith [sq_nonneg a.data.d]

end OAI.SKFluctuations.LaplaceWindowFormalization
