module

public import ComparisonSignedCavityFullSquareSourceBudget

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
open Hierarchy Cavity
set_option maxHeartbeats 3000000

variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem inverse_radius_le_source_mass
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    M.R u ≤ (Az+1/cl)*(M.xs+u) := by
  have hR := comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u
  have hspec := comparisonSweepQuantile_spec M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha hu
  have hru : M.R u ≤ Az*M.xs+u/cl := by
    by_cases hr : M.z ≤ M.R u
    · have H := (M.regular (M.R u) ⟨hr,hR.2⟩).1
      change cl*M.R u ≤ M.alpha.val.val (M.R u) at H
      rw [hspec] at H
      have H' : M.R u ≤ u/cl := (le_div_iff₀ hcl).mpr (by nlinarith)
      nlinarith [mul_nonneg hAz M.hxs.le]
    · have H : M.R u ≤ Az*M.xs := (le_of_not_ge hr).trans M.hzxs
      exact H.trans (le_add_of_nonneg_right (div_nonneg hu.1 hcl.le))
  have hi : 0 ≤ 1/cl := one_div_nonneg.mpr hcl.le
  have H1 := mul_nonneg hAz hu.1
  have H2 := mul_nonneg hi M.hxs.le
  calc
    M.R u ≤ Az*M.xs+u/cl := hru
    _ ≤ Az*M.xs+u/cl+(Az*u+(1/cl)*M.xs) :=
      le_add_of_nonneg_right (add_nonneg H1 H2)
    _ = _ := by ring

def bareSourceClockConstant (cl Az D : ℝ) : ℝ := D^2*(Az+1/cl)

theorem bare_source_clock_constant_nonneg (hcl : 0 < cl) (hAz : 0 ≤ Az) :
    0 ≤ bareSourceClockConstant cl Az D := by
  unfold bareSourceClockConstant
  positivity

theorem bare_source_clock_bounds
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) (T : ℝ)
    (hb : ∀u,M.b u=T) (hh : ∀u,M.h u=0)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    0≤(M.bf u:ℝ) ∧ (M.bf u:ℝ)≤T ∧
      0≤(M.hf u:ℝ) ∧
      (M.hf u:ℝ)≤bareSourceClockConstant cl Az D*(M.xs+u) := by
  let g := laplaceComparisonStrength M.context.d M.lam
  have hg : 0 ≤ g (M.R u) := (laplaceComparisonStrength_pos _ M.hlam _).le
  have hgl : g (M.R u) ≤ M.lam := laplaceComparisonStrength_le _ M.hlam.le _
  have hlT : M.lam ≤ T := by simpa only [hb] using M.hlb
  have hR := comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u
  have hdD : M.context.d^2 ≤ D^2 := pow_le_pow_left₀ M.context.hd.le M.hdD 2
  have hgD : g (M.R u) ≤ D^2 := hgl.trans (M.hld.trans hdD)
  refine ⟨NNReal.coe_nonneg _,?_,NNReal.coe_nonneg _,?_⟩
  · change (Real.toNNReal (M.b u-g (M.R u)):ℝ)≤T
    rw [hb,Real.coe_toNNReal _ (sub_nonneg.mpr (hgl.trans hlT))]
    linarith
  · change (Real.toNNReal (M.h u+g (M.R u)*M.R u):ℝ)≤_
    rw [hh,zero_add,Real.coe_toNNReal _ (mul_nonneg hg hR.1)]
    calc
      _ ≤ D^2*M.R u := mul_le_mul_of_nonneg_right hgD hR.1
      _ ≤ D^2*((Az+1/cl)*(M.xs+u)) :=
        mul_le_mul_of_nonneg_left (M.inverse_radius_le_source_mass hcl hAz hu) (sq_nonneg D)
      _ = _ := by unfold bareSourceClockConstant;ring

theorem bare_sampled_full_square_clock_budget
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) (T : ℝ)
    (hb : ∀u,M.b u=T) (hh : ∀u,M.h u=0) (hxs : M.xs≤1)
    (as : List PositiveMass) (ho : MassOrdered 0 as) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    finitePhysicalMixedClock n as b h as.length+b as.length+h as.length ≤
      4*bareSourceClockConstant cl Az D+2*T := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  have hu := partitionPoint_mem as ho as.length
  have HC:=M.bare_source_clock_bounds hcl hAz T hb hh hu
  have hC:=bare_source_clock_constant_nonneg (D:=D) hcl hAz
  have hf : h as.length ≤ 2*bareSourceClockConstant cl Az D := by
    have H:=mul_le_mul_of_nonneg_left (show M.xs+partitionPoint 0 as as.length≤2 by linarith [hu.2]) hC
    exact HC.2.2.2.trans (by nlinarith)
  have hmean:=finitePhysicalMean_le_one n ho b h as.length
  have Hm:=mul_le_mul_of_nonneg_left hmean (NNReal.coe_nonneg (M.bf (partitionPoint 0 as as.length)))
  change h as.length+b as.length*finitePhysicalMean n as b h as.length+b as.length+h as.length≤_
  have hb1 : b as.length≤T := HC.2.1
  nlinarith [hb1]

end OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
