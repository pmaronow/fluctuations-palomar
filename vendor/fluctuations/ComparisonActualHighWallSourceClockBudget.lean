module

public import ComparisonActualConcreteHighWallAmplitude
public import ComparisonActualGeneralFourSource
public import ComparisonSignedCavityActualLowErrorTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy PositiveLaplaceAssembly
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 8000000
namespace ActualHighWallData
variable {n : ℕ} {delta : ℝ} (a : ActualHighWallData n delta)

theorem field_le_strength (alpha : a.Profile) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    (a.hf alpha u:ℝ) ≤ a.d^2 := by
  by_cases hus : u < a.s
  · have H:=a.low_field_cubic alpha hu hus
    have hd : a.d^3 ≤ a.d^2 := by
      have Hmul:=mul_le_mul_of_nonneg_right a.hd1 (sq_nonneg a.d)
      simpa only [one_mul,←pow_succ'] using Hmul
    linarith [sq_nonneg a.d]
  · rw [(a.clock_coe alpha hu).2]
    dsimp only [h]
    have huhi : u∈Icc a.s 1 := ⟨le_of_not_gt hus,hu.2⟩
    rw [wallChangedField_on a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
      a.T a.epsilon a.theta a.tau a.d alpha huhi]
    let R:ℝ:=constrainedQuantile a.hr a.hc a.hk a.hkc a.hm a.hM alpha ⟨u,huhi⟩
    have hR : R∈Icc a.rmin 1 := (constrainedQuantile a.hr a.hc a.hk a.hkc a.hm a.hM alpha ⟨u,huhi⟩).property
    have hG : a.g R ≤ a.d^2 := laplaceComparisonStrength_le _ (sq_nonneg _) R
    have hGp : 0 ≤ a.g R := (laplaceComparisonStrength_pos a.d (sq_pos_of_pos a.hd) R).le
    change a.g R*R ≤ a.d^2
    exact (mul_le_mul_of_nonneg_left hR.2 hGp).trans (by simpa only [mul_one] using hG)

theorem small_source_clock_budget (alpha : a.Profile) {xs : ℝ} (hxs : a.d ≤ xs)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    (a.bf alpha u:ℝ) ≤ a.T ∧ (a.hf alpha u:ℝ) ≤ xs+u := by
  have ht:=a.total_clock_le alpha u hu
  have hf:=a.field_le_strength alpha hu
  have hd : a.d^2 ≤ a.d := by nlinarith [a.hd,a.hd1]
  exact ⟨by linarith [(a.hf alpha u).coe_nonneg],hf.trans (hd.trans (by linarith [hu.1]))⟩

theorem full_square_clock_budget
    (alpha : a.Profile) (as : List PositiveMass) (ho : MassOrdered 0 as) :
    let b:=fun j=>(a.bf alpha (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(a.hf alpha (partitionPoint 0 as j):ℝ)
    Cavity.finitePhysicalMixedClock n as b h as.length+b as.length+h as.length ≤ 2*a.T := by
  dsimp only
  let b:=fun j=>(a.bf alpha (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(a.hf alpha (partitionPoint 0 as j):ℝ)
  have hu:=partitionPoint_mem as ho as.length
  have HC:=a.total_clock_le alpha _ hu
  have Hmean:=Cavity.finitePhysicalMean_le_one n ho b h as.length
  have Hmul:=mul_le_mul_of_nonneg_left Hmean (NNReal.coe_nonneg (a.bf alpha (partitionPoint 0 as as.length)))
  change h as.length+b as.length*Cavity.finitePhysicalMean n as b h as.length+b as.length+h as.length ≤ _
  dsimp only [b,h] at Hmul ⊢
  nlinarith

end ActualHighWallData

namespace ActualHighWallData
variable {n : ℕ} {delta : ℝ} (a : ActualHighWallData (n+1) delta)

theorem current_low_error_radius_le_original
    (alpha : a.Profile) (as : List PositiveMass) (ho : MassOrdered 0 as)
    (U : ℕ) {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (j : ℕ) (hj : j ≤ as.length) :
    let b:=fun k=>(a.bf alpha (partitionPoint 0 as k):ℝ)
    let h:=fun k=>(a.hf alpha (partitionPoint 0 as k):ℝ)
    let S:=fun k=>orderedPathS (n+1) (a.bf alpha) (a.hf alpha) (partitionPoint 0 as k)
    let K:=fun k=>h k+b k*S k
    Cavity.nativeWholeLawErrorRadius n as
      (Cavity.cutFullVariance n (fun k=>Sum.elim (fun _=>b k) (fun _=>h k)) U l t b h K)
      (Cavity.cutLowError n U b h K) j ≤
      if j<U then Cavity.actualLowErrorComparisonConstant (2*a.T) a.T*
        (nativeOriginalCutLowErrorRadius n (a.bf alpha) (a.hf alpha) as j+1/(n+1:ℕ)) else 0 := by
  have hT : 0 ≤ a.T := a.hepsilon.1.le.trans a.hepsilon.2.le
  have hbond (k : ℕ) (_hk : k ≤ as.length) :
      (a.bf alpha (partitionPoint 0 as k):ℝ) ≤ a.T := by
    have H:=a.total_clock_le alpha _ (partitionPoint_mem as ho k)
    linarith [(a.hf alpha (partitionPoint 0 as k)).coe_nonneg]
  have hclock : (a.hf alpha (partitionPoint 0 as as.length):ℝ)+
      (a.bf alpha (partitionPoint 0 as as.length):ℝ)*
        orderedPathS (n+1) (a.bf alpha) (a.hf alpha) (partitionPoint 0 as as.length)+
      (a.bf alpha (partitionPoint 0 as as.length):ℝ)+
        (a.hf alpha (partitionPoint 0 as as.length):ℝ) ≤ 2*a.T := by
    have H:=a.total_clock_le alpha _ (partitionPoint_mem as ho as.length)
    have HS:=physicalOrderedPathS_mem_unit n (a.bf alpha) (a.hf alpha)
      (a.bf_monotone alpha) (a.hf_monotone alpha) (partitionPoint_mem as ho as.length)
    have Hmul:=mul_le_mul_of_nonneg_left HS.2
      (a.bf alpha (partitionPoint 0 as as.length)).coe_nonneg
    nlinarith
  exact Cavity.native_actual_low_error_radius_le_original n U (a.bf alpha) (a.hf alpha)
    (a.bf_monotone alpha) (a.hf_monotone alpha) ho hl ht hT hbond hclock j hj

end ActualHighWallData

theorem actual_concrete_high_wall_field_le_critical_scale
    {m C0 : ℝ} (hm : 0 < m) (hmmax : m < 1/300) (hC0 : 0 < C0) :
    ∀ᶠ n : ℕ in atTop,
      ∀{T epsilon theta : ℝ} (hp : ActualConcreteHighWallNumeric m n)
        (hepsilon : epsilon∈Ioo (0:ℝ) T)
        (heps0 : upperInitialEpsilon m n ≤ epsilon) (htheta : theta∈Icc (0:ℝ) 1),
      let a:=actualConcreteHighWallData T m n hp epsilon theta hepsilon heps0 htheta
      ∀alpha : a.Profile,∀xs : ℝ,
      (n:ℝ)^(-(1:ℝ)/6+m) ≤ C0*xs →
      ∀u∈Icc (0:ℝ) 1,(a.hf alpha u:ℝ) ≤ xs := by
  have Hrate:=eventually_coefficient_rpow_le
    (c:=C0) (d:=1) (q:=-(1:ℝ)/3+30*m) (r:=-(1:ℝ)/6+m)
    (by norm_num) (by linarith)
  filter_upwards [Hrate,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro T epsilon theta hp hepsilon heps0 htheta
  dsimp only
  intro alpha xs hscale u hu
  have hN : 0 < (n:ℝ) := Nat.cast_pos.mpr hn0
  have hd : (wallHighD m n)^2=(n:ℝ)^(-(1:ℝ)/3+30*m) := by
    unfold wallHighD
    rw [←Real.rpow_natCast,←Real.rpow_mul hN.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have Hfield:= (actualConcreteHighWallData T m n hp epsilon theta hepsilon heps0 htheta).field_le_strength alpha hu
  change _ ≤ (wallHighD m n)^2 at Hfield
  rw [hd] at Hfield
  have Hmul:=mul_le_mul_of_nonneg_left Hfield hC0.le
  exact (mul_le_mul_iff_right₀ hC0).mp (by
    simpa only [mul_comm] using Hmul.trans (hn.trans (by simpa only [one_mul] using hscale)))

end OAI.SKFluctuations.LaplaceWindowFormalization
