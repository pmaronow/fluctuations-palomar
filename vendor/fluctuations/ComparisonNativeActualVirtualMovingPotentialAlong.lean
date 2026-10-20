module

public import ComparisonNativeActualVirtualMovingPotential
public import ComparisonNativeActualInitialMassChargesAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 9000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_virtual_moving_potential_data_along
    (hcu : 0 ≤ cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hroom : 0 < 3*m+delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (p : (n:ℕ)→(M n).Potential)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    {a b B c KG : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbB : b < B)
    (hc : 0 < c) (hKG : 0 ≤ KG) (left : ℕ→ℝ)
    (hleft : Tendsto left atTop (𝓝 a))
    (hleft0 : ∀ᶠn in atTop,0 ≤ left n)
    (hmass : ∀ᶠn in atTop,c*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*left n))
    (hcontact : ∀ᶠn in atTop,(p n).H ((M n).xs*left n)=0)
    (hgradient : ∀ᶠn in atTop,∀t∈Icc (left n) B,|(M n).actualVirtualScaledGradient t| ≤ KG) :
    let K := (c+cu*(B+Az)+1)/c
    let L : ℝ≥0 := (K^2*KG).toNNReal
    1 ≤ K ∧ ∃errors : ℕ→ℝ,
      (∀n,0 ≤ errors n) ∧ Tendsto errors atTop (𝓝 0) ∧
      ∀ᶠn in atTop,
        left n ≤ b ∧ (M n).xs*B ≤ 1 ∧
        (p n).actualVirtualScaledPotential ((M n).xs*left n) (left n)=0 ∧
        LipschitzOnWith L ((p n).actualVirtualScaledPotential ((M n).xs*left n)) (Icc (left n) B) ∧
        Continuous ((M n).actualVirtualMovingFactor ((M n).xs*left n)) ∧
        MonotoneOn ((M n).actualVirtualMovingFactor ((M n).xs*left n)) (Iic B) ∧
        (∀t≤B,(M n).actualVirtualMovingFactor ((M n).xs*left n) t∈Icc (1/K^2) (K^2)) ∧
        (∀t∈Icc a b,-errors n ≤ (p n).actualVirtualScaledPotential ((M n).xs*left n) (max (left n) t)) ∧
        (∀s∈Icc (left n) B,∀t∈Icc (left n) B,s ≤ t →
          (p n).actualVirtualScaledPotential ((M n).xs*left n) t-
            (p n).actualVirtualScaledPotential ((M n).xs*left n) s =
          ∫r in s..t,(M n).actualVirtualMovingFactor ((M n).xs*left n) r*
            (M n).actualVirtualScaledGradient r) := by
  let K := (c+cu*(B+Az)+1)/c
  let L : ℝ≥0 := (K^2*KG).toNNReal
  have hB : 0 ≤ B := ha.trans (hab.le.trans hbB.le)
  have hK : 1 ≤ K := by
    apply (le_div_iff₀ hc).mpr
    have H := mul_nonneg hcu (add_nonneg hB hAz)
    linarith
  let errors := fun n=>(L:ℝ)*(2*(M n).cavityCapTravel/(M n).xs)
  have herr0 n : 0 ≤ errors n := mul_nonneg L.coe_nonneg
    (div_nonneg (mul_nonneg (by norm_num) (M n).cavityCapTravel_nonneg) (M n).hxs.le)
  have hcap := actual_cap_travel_ratio_tendsto_zero_along hC0 hroom dim hdim M
    (fun n=>(M n).xs) (fun _=>le_rfl)
  have htwocap : Tendsto (fun n=>2*(M n).cavityCapTravel/(M n).xs) atTop (𝓝 0) := by
    simpa only [mul_div_assoc,mul_zero] using hcap.const_mul 2
  have herr : Tendsto errors atTop (𝓝 0) := by
    simpa only [mul_zero] using htwocap.const_mul (L:ℝ)
  have hphysical : ∀ᶠn in atTop,(M n).xs*B < 1 := by
    have H := hxs.mul_const B
    simp only [zero_mul] at H
    exact H.eventually (gt_mem_nhds zero_lt_one)
  have hspace : ∀ᶠn in atTop,2*(M n).cavityCapTravel/(M n).xs < B-b :=
    htwocap.eventually (gt_mem_nhds (sub_pos.mpr hbB))
  refine ⟨hK,errors,herr0,herr,?_⟩
  filter_upwards [hleft0,hleft.eventually (gt_mem_nhds hab),hmass,hcontact,
    hgradient,hphysical,hspace] with n hn0 hnleft hnmass hncontact hngrad hnphysical hnspace
  have hcancel : ((M n).xs*left n)/(M n).xs=left n := by field_simp [(M n).hxs.ne']
  have href : (M n).xs*left n∈Icc (0:ℝ) ((M n).xs*B) :=
    ⟨mul_nonneg (M n).hxs.le hn0,mul_le_mul_of_nonneg_left (hnleft.le.trans hbB.le) (M n).hxs.le⟩
  have Hfactor := (M n).actual_virtual_moving_factor_data hcu hAz hB hc href hnphysical.le hnmass
  have Hlip := (p n).actual_virtual_moving_lipschitz hcu hAz hB hc href hnphysical.le hnmass hKG
    (by simpa only [hcancel] using hngrad)
  rw [hcancel] at Hlip
  refine ⟨hnleft.le,hnphysical.le,?_,Hlip,Hfactor.2.1,Hfactor.2.2.1,Hfactor.2.2.2,?_,?_⟩
  · simp only [Potential.actualVirtualScaledPotential,hncontact,zero_div]
  · intro t ht
    have hmaxB : max (left n) t ≤ b := max_le hnleft.le ht.2
    have htmem : max (left n) t∈Icc (((M n).xs*left n)/(M n).xs) B := by
      rw [hcancel]
      exact ⟨le_max_left _ _,hmaxB.trans hbB.le⟩
    have Hlip' : LipschitzOnWith L ((p n).actualVirtualScaledPotential ((M n).xs*left n))
        (Icc (((M n).xs*left n)/(M n).xs) B) := by rw [hcancel];exact Hlip
    exact (p n).actual_virtual_scaled_lower_of_lipschitz href.1 hnphysical.le Hlip' htmem
      (by linarith only [hmaxB,hnspace])
  · intro s hs t ht hst
    exact (p n).actual_virtual_moving_primitive ((M n).xs*left n) (hn0.trans hs.1)
      (by simpa only [hcancel] using hs.1) hst
      ((mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans hnphysical.le)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
