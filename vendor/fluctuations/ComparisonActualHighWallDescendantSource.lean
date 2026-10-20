module

public import ComparisonActualHighWallOverlapAmplitude
public import ConcreteOmittedStrengthSweep
public import ComparisonActualChildData

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 10000000

structure ActualHighOnlyComparisonData (n : ℕ) (delta : ℝ) where
  E : ℝ
  d : ℝ
  s : ℝ
  b : ℝ→ℝ
  h : ℝ→ℝ
  hn : 0 < n
  hE : 0 < E
  hd : 0 < d
  hs : s∈Icc (0:ℝ) (1/2)
  hq : 2≤(n:ℝ)^delta
  hb : MonotoneOn b (Icc (0:ℝ) 1)
  hh : MonotoneOn h (Icc (0:ℝ) 1)
  hb0 : 0≤b 0
  hh0 : 0≤h 0
  hcut : d^2≤b s
  hcross : ∀u∈Ico (0:ℝ) s,b u+d^2≤b s

namespace ActualHighOnlyComparisonData
variable {n : ℕ} {delta : ℝ} (a : ActualHighOnlyComparisonData n delta)
abbrev N (_a : ActualHighOnlyComparisonData n delta) := (n:ℝ)
abbrev U := comparisonSmallMass a.N a.E
abbrev L := comparisonConstraintLength a.N a.E a.d
abbrev k := comparisonFloor a.N delta a.U
abbrev M := comparisonCap a.N delta a.U a.L a.E a.d
theorem hN : 0<a.N := Nat.cast_pos.mpr a.hn
theorem hU : 0<a.U := concreteWallSmallMass_pos a.hN a.hE
theorem hL : 0<a.L := concreteWallConstraintLength_pos a.hN a.hE a.hd
theorem hs1 : a.s≤1 := a.hs.2.trans (by norm_num)
theorem hc : 0<a.k 1 := comparisonFloor_pos a.hN a.hU (by norm_num)
theorem hk : ContinuousOn a.k (Icc (0:ℝ) 1) := comparisonFloor_continuousOn a.hN a.hU le_rfl
theorem hkc : ∀r∈Icc (0:ℝ) 1,a.k 1≤a.k r :=
  fun _r hr=>comparisonFloor_lower_on a.hN a.hU le_rfl hr
theorem hm : MonotoneOn a.M (Icc (0:ℝ) 1) :=
  comparisonCap_monotoneOn a.hN a.hU.le a.hL a.hE a.hd.le
theorem hM : 0≤a.M 1 := comparisonCap_nonneg a.hN a.hU.le a.hL a.hE a.hd.le zero_le_one
abbrev Profile := inverseIntegralConstraints 0 a.s a.k a.M
abbrev R (alpha : a.Profile) := omittedSweepQuantile zero_le_one ⟨a.hs.1,a.hs1⟩
  a.hc a.hk a.hkc a.hm a.hM alpha
abbrev objective (lam : ℝ) (alpha : a.Profile) :=
  omittedComparisonSweepObjective zero_le_one ⟨a.hs.1,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM
    n a.b a.h a.d lam alpha
abbrev minimum (lam : ℝ) :=
  omittedComparisonSweepMinimum zero_le_one ⟨a.hs.1,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM
    n a.b a.h a.d lam
abbrev cost := omittedComparisonSweepCost zero_le_one ⟨a.hs.1,a.hs1⟩
  a.hc a.hk a.hkc a.hm a.hM n a.b a.h a.d

theorem profile_nonempty : a.Profile.Nonempty := by
  have hne : (inverseDifferentialConstraints 0 a.s a.k a.M).Nonempty :=
    comparisonConstraints_nonempty a.hN a.hU a.hL (min_le_left _ _) a.hE a.hd.le a.hq
      (by norm_num) a.hs
  rw [inverseDifferentialConstraints_eq 0 a.s zero_le_one a.k a.M a.hk
    (comparisonCap_continuous a.N delta a.U a.L a.E a.d) a.hm a.hM] at hne
  exact hne

theorem exists_minimum {lam : ℝ} (hlam : lam∈Icc (0:ℝ) (a.d^2)) :
    ∃alpha : a.Profile,a.objective lam alpha=a.minimum lam ∧
      ∀beta : a.Profile,a.minimum lam≤a.objective lam beta := by
  exact omittedComparisonSweepMinimum_attained le_rfl zero_le_one ⟨a.hs.1,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM n a.hn a.b a.h a.hd.ne' hlam.1
    (hlam.2.trans a.hcut) (fun u hu=>by linarith [a.hcross u hu,hlam.2])
    a.hb a.hb0 a.hh a.hh0 (comparisonCap_continuous a.N delta a.U a.L a.E a.d)
    a.profile_nonempty

theorem objective_eq_inverse (lam : ℝ) (alpha : a.Profile) :
    a.objective lam alpha=inverseCompensatedPressure zero_le_one a.hs1 a.hc a.hk a.hkc
      a.hm a.hM (laplaceComparisonStrength a.d lam)
      (laplaceComparisonStrength_contDiff a.d lam).continuous n a.b a.h 0 alpha :=
  omittedComparisonSweepObjective_eq_inverse zero_le_one ⟨a.hs.1,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM n a.b a.h a.d lam alpha

theorem cost_lipschitz : LipschitzOnWith 1 a.cost (Icc (0:ℝ) (a.d^2)) :=
  omittedComparisonSweepCost_lipschitz le_rfl zero_le_one ⟨a.hs.1,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM n a.hn a.b a.h a.hd.ne' a.hcut a.hcross
    a.hb a.hb0 a.hh a.hh0 (comparisonCap_continuous a.N delta a.U a.L a.E a.d) a.profile_nonempty

theorem cost_zero : a.cost 0=0 :=
  omittedComparisonSweepCost_zero le_rfl zero_le_one ⟨a.hs.1,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM n a.hn a.b a.h a.hd.ne' a.hb a.hb0 a.hh a.hh0
    (comparisonCap_continuous a.N delta a.U a.L a.E a.d) a.profile_nonempty

theorem cost_mem {lam : ℝ} (hlam : lam∈Icc (0:ℝ) (a.d^2)) : a.cost lam∈Icc (0:ℝ) lam := by
  refine ⟨omittedComparisonSweepCost_nonneg le_rfl zero_le_one ⟨a.hs.1,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM n a.hn a.b a.h a.hd.ne' a.hcut a.hcross
    a.hb a.hb0 a.hh a.hh0 (comparisonCap_continuous a.N delta a.U a.L a.E a.d)
    a.profile_nonempty hlam,?_⟩
  have hh := a.cost_lipschitz.dist_le_mul lam hlam 0 ⟨le_rfl,sq_nonneg _⟩
  rw [a.cost_zero] at hh
  have hbound : |a.cost lam|≤lam := by
    simpa only [Real.dist_eq,sub_zero,NNReal.coe_one,one_mul,abs_of_nonneg hlam.1] using hh
  exact (le_abs_self (a.cost lam)).trans hbound

theorem clocks_admissible (alpha : a.Profile) {lam : ℝ} (hlam : lam∈Icc (0:ℝ) (a.d^2)) :
    let e:=omittedStrengthCoefficient a.d a.s (a.R alpha) lam
    MonotoneOn (fun u=>a.b u-e u) (Icc (0:ℝ) 1) ∧
      MonotoneOn (fun u=>a.h u+e u*a.R alpha u) (Icc (0:ℝ) 1) ∧
      (∀u∈Icc (0:ℝ) 1,0≤a.b u-e u) ∧
      (∀u∈Icc (0:ℝ) 1,0≤a.h u+e u*a.R alpha u) := by
  exact omittedStrengthSweep_clocks_admissible a.b a.h (a.R alpha) ⟨a.hs.1,a.hs1⟩
    a.hd.ne' hlam.1 (hlam.2.trans a.hcut)
    (fun u hu=>by linarith [a.hcross u hu,hlam.2]) a.hb a.hb0 a.hh a.hh0
    ((omittedSweepQuantile_monotone zero_le_one ⟨a.hs.1,a.hs1⟩
      a.hc a.hk a.hkc a.hm a.hM alpha).monotoneOn _)
    (fun u _=>omittedSweepQuantile_bounds zero_le_one ⟨a.hs.1,a.hs1⟩
      a.hc a.hk a.hkc a.hm a.hM alpha u)

abbrev coefficient (alpha : a.Profile) (lam : ℝ) := omittedStrengthCoefficient a.d a.s (a.R alpha) lam
abbrev bf (alpha : a.Profile) (lam : ℝ) := fun u=>(a.b u-a.coefficient alpha lam u).toNNReal
abbrev hf (alpha : a.Profile) (lam : ℝ) :=
  fun u=>(a.h u+a.coefficient alpha lam u*a.R alpha u).toNNReal

theorem bf_monotone (alpha : a.Profile) {lam : ℝ} (hlam : lam∈Icc (0:ℝ) (a.d^2)) :
    MonotoneOn (a.bf alpha lam) (Icc (0:ℝ) 1) :=
  toNNReal_monotoneOn (a.clocks_admissible alpha hlam).1

theorem hf_monotone (alpha : a.Profile) {lam : ℝ} (hlam : lam∈Icc (0:ℝ) (a.d^2)) :
    MonotoneOn (a.hf alpha lam) (Icc (0:ℝ) 1) :=
  toNNReal_monotoneOn (a.clocks_admissible alpha hlam).2.1

theorem clock_coe (alpha : a.Profile) {lam u : ℝ} (hlam : lam∈Icc (0:ℝ) (a.d^2))
    (hu : u∈Icc (0:ℝ) 1) :
    (a.bf alpha lam u:ℝ)=a.b u-a.coefficient alpha lam u ∧
      (a.hf alpha lam u:ℝ)=a.h u+a.coefficient alpha lam u*a.R alpha u :=
  ⟨Real.coe_toNNReal _ ((a.clocks_admissible alpha hlam).2.2.1 u hu),
    Real.coe_toNNReal _ ((a.clocks_admissible alpha hlam).2.2.2 u hu)⟩

theorem low_clocks (alpha : a.Profile) (lam : ℝ) {u : ℝ} (hu : u<a.s) :
    a.bf alpha lam u=(a.b u).toNNReal ∧ a.hf alpha lam u=(a.h u).toNNReal := by
  simp only [bf,hf,coefficient,omittedStrengthCoefficient,ite_eq_right (not_le.mpr hu),
    sub_zero,zero_mul,add_zero]
  exact ⟨True.intro,True.intro⟩

theorem total_clock_le (alpha : a.Profile) {lam T : ℝ} (hlam : lam∈Icc (0:ℝ) (a.d^2))
    (htotal : ∀u∈Icc (0:ℝ) 1,a.h u+a.b u≤T) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    (a.hf alpha lam u:ℝ)+(a.bf alpha lam u:ℝ)≤T := by
  rw [(a.clock_coe alpha hlam hu).1,(a.clock_coe alpha hlam hu).2]
  have hR := (omittedSweepQuantile_bounds zero_le_one ⟨a.hs.1,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM alpha u).2
  have he : 0≤a.coefficient alpha lam u := by
    unfold coefficient omittedStrengthCoefficient
    split_ifs
    · exact laplaceComparisonStrength_nonneg _ _ hlam.1
    · exact le_rfl
  have hh := mul_le_mul_of_nonneg_left hR he
  linarith [htotal u hu]

def originalPhysicalLaw (alpha : a.Profile) (lam : ℝ) (as : List PositiveMass) :=
  rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n)
    (completedPathClock n (a.bf alpha lam) (a.hf alpha lam) 0)
    (sampleClockSteps (completedPathClock n (a.bf alpha lam) (a.hf alpha lam)) 0 as)

theorem log_derivative_envelope :
    ∀ᵐ lam∂volume.restrict (Ioo (0:ℝ) (a.d^2)),
      ∃alpha : a.Profile,a.objective lam alpha=a.minimum lam ∧
        let e:=omittedStrengthCoefficient a.d a.s (a.R alpha) lam
        let bf:=fun u=>(a.b u-e u).toNNReal
        let hf:=fun u=>(a.h u+e u*a.R alpha u).toNNReal
        lam*deriv a.cost lam≤(1/4:ℝ)*(∫u in (0:ℝ)..1,e u*
          ((orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
            (orderedPathS n bf hf u-a.R alpha u)^2)) :=
  omittedComparisonSweepCost_ae_log_derivative_le le_rfl zero_le_one ⟨a.hs.1,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM n a.hn a.b a.h a.hd.ne' (sq_pos_of_pos a.hd)
    a.hcut a.hcross a.hb a.hb0 a.hh a.hh0
    (comparisonCap_continuous a.N delta a.U a.L a.E a.d) a.profile_nonempty

end ActualHighOnlyComparisonData

structure ActualHighOnlyComparisonMinimum {n : ℕ} {delta : ℝ}
    (a : ActualHighOnlyComparisonData n delta) (lam : ℝ) where
  alpha : a.Profile
  attained : a.objective lam alpha=a.minimum lam
  minimum : ∀beta : a.Profile,a.objective lam alpha≤a.objective lam beta

theorem ActualHighOnlyComparisonData.exists_actual_minimum {n : ℕ} {delta : ℝ}
    (a : ActualHighOnlyComparisonData n delta) {lam : ℝ} (hlam : lam∈Icc (0:ℝ) (a.d^2)) :
    Nonempty (ActualHighOnlyComparisonMinimum a lam) := by
  obtain ⟨alpha,hattained,hminimum⟩ := a.exists_minimum hlam
  exact ⟨⟨alpha,hattained,fun beta=>hattained.symm ▸ hminimum beta⟩⟩

theorem ActualHighOnlyComparisonMinimum.inverse_minimum {n : ℕ} {delta : ℝ}
    {a : ActualHighOnlyComparisonData n delta} {lam : ℝ} (M : ActualHighOnlyComparisonMinimum a lam) :
    ∀beta : a.Profile,inverseCompensatedPressure zero_le_one a.hs1 a.hc a.hk a.hkc
      a.hm a.hM (laplaceComparisonStrength a.d lam)
      (laplaceComparisonStrength_contDiff a.d lam).continuous n a.b a.h 0 M.alpha≤
    inverseCompensatedPressure zero_le_one a.hs1 a.hc a.hk a.hkc a.hm a.hM
      (laplaceComparisonStrength a.d lam) (laplaceComparisonStrength_contDiff a.d lam).continuous
      n a.b a.h 0 beta := by
  intro beta
  simpa only [←a.objective_eq_inverse] using M.minimum beta

namespace ActualHighWallData
variable {n : ℕ} {delta : ℝ} (a : ActualHighWallData n delta)

theorem parent_high_gap (alpha : a.Profile) {lam : ℝ}
    (hreserve : a.d^2+lam≤a.epsilon) {u : ℝ} (hu : u∈Ico (0:ℝ) a.s) :
    a.b alpha u+lam≤a.b alpha a.s := by
  dsimp only [b]
  rw [wallChangedMatrix_below a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
    a.T a.epsilon a.theta alpha hu.2,
    wallChangedMatrix_on a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
      a.T a.epsilon a.theta alpha ⟨le_rfl,a.hs1⟩]
  have hg := laplaceComparisonStrength_le a.d (sq_nonneg a.d)
    (constrainedQuantile a.hr a.hc a.hk a.hkc a.hm a.hM alpha ⟨a.s,⟨le_rfl,a.hs1⟩⟩)
  have htheta := mul_nonneg a.htheta.1 (wallLowStrength_bounds a.hepsilon).1
  linarith

def highOnlyChildData (alpha : a.Profile) {Echild dchild : ℝ}
    (hEchild : 0<Echild) (hdchild : 0<dchild)
    (hreserve : a.d^2+dchild^2≤a.epsilon) : ActualHighOnlyComparisonData n delta where
  E:=Echild
  d:=dchild
  s:=a.s
  b:=a.b alpha
  h:=a.h alpha
  hn:=a.hn
  hE:=hEchild
  hd:=hdchild
  hs:=⟨a.hs.1.le,a.hs.2.trans (by norm_num)⟩
  hq:=a.hq
  hb:=(a.admissible alpha).1
  hh:=(a.admissible alpha).2.1
  hb0:=(a.admissible alpha).2.2.1
  hh0:=(a.admissible alpha).2.2.2
  hcut:=by
    have hh:=a.parent_high_gap alpha hreserve ⟨le_rfl,a.hs.1⟩
    linarith [(a.admissible alpha).2.2.1]
  hcross:=fun _ hu=>a.parent_high_gap alpha hreserve hu

def globalChildData (alpha : a.Profile) {Echild dchild : ℝ}
    (hEchild : 0<Echild) (hdchild : 0<dchild)
    (hroom : dchild^2≤a.b alpha 0) : ActualHighOnlyComparisonData n delta where
  E:=Echild
  d:=dchild
  s:=0
  b:=a.b alpha
  h:=a.h alpha
  hn:=a.hn
  hE:=hEchild
  hd:=hdchild
  hs:=by norm_num
  hq:=a.hq
  hb:=(a.admissible alpha).1
  hh:=(a.admissible alpha).2.1
  hb0:=(a.admissible alpha).2.2.1
  hh0:=(a.admissible alpha).2.2.2
  hcut:=hroom
  hcross:=by intro u hu;exact False.elim (not_lt_of_ge hu.1 hu.2)

end ActualHighWallData

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def actualHighOnlyChild
    (a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 x : ℝ} (hc0 : 0<c0) (hx : 0<x)
    (hreserve : a.data.d^2+(c0*x)^2≤a.data.epsilon) : ActualHighOnlyComparisonData n delta :=
  a.data.highOnlyChildData a.alpha
    (actual_child_budget_pos (delta:=delta) (d:=a.data.d) a.data.hN hc0 (sq_pos_of_pos a.data.hd) hx)
    (mul_pos hc0 hx) hreserve

theorem actualHighOnlyChild_parameters
    (a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 x : ℝ} (hc0 : 0<c0) (hx : 0<x)
    (hreserve : a.data.d^2+(c0*x)^2≤a.data.epsilon) :
    (a.actualHighOnlyChild hc0 hx hreserve).E=actualChildErrorBudget n delta c0
      a.data.d (a.data.d^2) x ∧ (a.actualHighOnlyChild hc0 hx hreserve).d=c0*x ∧
      (a.actualHighOnlyChild hc0 hx hreserve).s=a.data.s ∧
      (a.actualHighOnlyChild hc0 hx hreserve).b=a.data.b a.alpha ∧
      (a.actualHighOnlyChild hc0 hx hreserve).h=a.data.h a.alpha := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem actualHighOnlyChild_upper
    (a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {c0 x : ℝ} (hc0 : 0<c0) (hx : 0<x)
    (hreserve : a.data.d^2+(c0*x)^2≤a.data.epsilon) :
    Real.sqrt (n:ℝ)*(a.actualHighOnlyChild hc0 hx hreserve).E≤
      (a.actualHighOnlyChild hc0 hx hreserve).d^2 := by
  have HH := (le_div_iff₀ (Real.sqrt_pos.mpr a.data.hN)).mp
    (actual_child_budget_ceiling n delta c0 a.data.d (a.data.d^2) x)
  simpa only [actualHighOnlyChild,ActualHighWallData.highOnlyChildData,actualChildRadius,mul_comm] using HH

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
