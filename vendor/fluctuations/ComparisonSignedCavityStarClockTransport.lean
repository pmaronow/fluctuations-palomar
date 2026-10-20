module

public import ComparisonSignedCavityStarClockCalibration
public import ComparisonNativeCavityGoodStarTransfer

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity
set_option maxHeartbeats 3500000

def retainedStarMatrix (bf : ℝ→ℝ≥0) (as : List PositiveMass) (j : ℕ) : ℝ :=
  bf (partitionPoint 0 as j)

def retainedStarField (hf : ℝ→ℝ≥0) (as : List PositiveMass) (j : ℕ) : ℝ :=
  hf (partitionPoint 0 as j)

def retainedStarMixedClock (n : ℕ) (bf hf : ℝ→ℝ≥0) (as : List PositiveMass) : ℕ→ℝ :=
  finitePhysicalMixedClock (n+1) as (retainedStarMatrix bf as) (retainedStarField hf as)

theorem retainedStarMixedClock_nonneg (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (as : List PositiveMass) : ∀j,0 ≤ retainedStarMixedClock n bf hf as j :=
  finitePhysicalMixedClock_nonneg (n+1) as _ _
    (fun j=>(bf (partitionPoint 0 as j)).coe_nonneg)
    (fun j=>(hf (partitionPoint 0 as j)).coe_nonneg)

theorem retainedStarMixedClock_monotone (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hb : MonotoneOn bf (Icc (0:ℝ) 1)) (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) :
    Monotone (retainedStarMixedClock n bf hf as) := by
  apply finitePhysicalMixedClock_monotone (n+1) ho
  · intro i j hij
    exact NNReal.coe_le_coe.mpr (hb (partitionPoint_mem as ho i)
      (partitionPoint_mem as ho j) (partitionPoint_mono as ho hij))
  · intro i j hij
    exact NNReal.coe_le_coe.mpr (hh (partitionPoint_mem as ho i)
      (partitionPoint_mem as ho j) (partitionPoint_mono as ho hij))
  · exact fun j=>(bf (partitionPoint 0 as j)).coe_nonneg

theorem retainedStarMixedClock_terminal_le (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1) :
    retainedStarMixedClock n bf hf as as.length ≤ (hf 1:ℝ)+(bf 1:ℝ) := by
  have H := finitePhysicalMixedClock_le_add (n+1) ho (retainedStarMatrix bf as)
    (retainedStarField hf as) (fun j=>(bf (partitionPoint 0 as j)).coe_nonneg) as.length
  simpa only [retainedStarMixedClock,retainedStarMatrix,retainedStarField,
    physicalPartitionPoint_length,he] using H

theorem retainedStarMixedClock_tendsto (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hb : MonotoneOn bf (Icc (0:ℝ) 1)) (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    (us : List PositiveMass) (hus : ∀v∈us,v.val≤1) (u : PositiveMass) (hu : u∈us) :
    Tendsto (fun j=>retainedStarMixedClock n bf hf (finiteCutMasses us j)
      (retainedMassPrefixIndex u.val (finiteCutMasses us j))) atTop
      (𝓝 (actualMixedClock (n+1) bf hf u.val)) :=
  nativeRetainedFinitePhysicalMixedClock_tendsto n bf hf hb hh us hus u hu

theorem eventually_retainedStarMixedClock_lower (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hb : MonotoneOn bf (Icc (0:ℝ) 1)) (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    (us : List PositiveMass) (hus : ∀v∈us,v.val≤1) (u : PositiveMass) (hu : u∈us)
    {c W : ℝ} (hc : 0<c) (hW : 0<W)
    (hK : c*W ≤ actualMixedClock (n+1) bf hf u.val) :
    ∀ᶠj in atTop,(c/2)*W ≤ retainedStarMixedClock n bf hf (finiteCutMasses us j)
      (retainedMassPrefixIndex u.val (finiteCutMasses us j)) := by
  have hp : (c/2)*W < actualMixedClock (n+1) bf hf u.val := by
    have H := mul_pos hc hW
    linarith
  exact ((retainedStarMixedClock_tendsto n bf hf hb hh us hus u hu).eventually
    (eventually_gt_nhds hp)).mono (fun _ h=>h.le)

theorem eventually_retainedStarMixedClock_cubic_error
    (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hb : MonotoneOn bf (Icc (0:ℝ) 1)) (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    (us : List PositiveMass) (hus : ∀v∈us,v.val≤1) (u : PositiveMass) (hu : u∈us)
    {T S W Ck eta : ℝ} (hW : 0<W) (heta : 0<eta)
    (hclock : |actualMixedClock (n+1) bf hf u.val-T*S|≤Ck*W^3) :
    ∀ᶠj in atTop,
      |retainedStarMixedClock n bf hf (finiteCutMasses us j)
        (retainedMassPrefixIndex u.val (finiteCutMasses us j))-T*S|≤(Ck+eta)*W^3 := by
  have H := ((retainedStarMixedClock_tendsto n bf hf hb hh us hus u hu).sub_const
    (actualMixedClock (n+1) bf hf u.val)).abs
  simp only [sub_self,abs_zero] at H
  filter_upwards [H.eventually (eventually_lt_nhds (mul_pos heta (pow_pos hW 3)))] with j hj
  have H' := (abs_add_le
    (retainedStarMixedClock n bf hf (finiteCutMasses us j)
      (retainedMassPrefixIndex u.val (finiteCutMasses us j))-actualMixedClock (n+1) bf hf u.val)
    (actualMixedClock (n+1) bf hf u.val-T*S)).trans (add_le_add hj.le hclock)
  simp only [sub_add_sub_cancel] at H'
  nlinarith only [H']

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eventually_native_bare_star_mixed_clock_lower
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {r W T : ℝ} (hW : 0 < W) (hT : 0 < T) (hW1 : W ≤ 1)
    (hxs : M.xs ≤ W) (hband : W/2 ≤ r ∧ r ≤ W)
    (hscale : laplaceComparisonStrength M.context.d M.lam M.xs ≤ W^2)
    (hsmall : 2*W^2 ≤ T/2) (hb : M.b (M.alpha.val.val r)=T)
    (hmis : (M.starMean r-r)^2 ≤ W^2/16)
    (us : List PositiveMass) (hus : ∀v∈us,v.val≤1) (u : PositiveMass) (hu : u∈us)
    (humass : u.val=M.alpha.val.val r) :
    ∀ᶠj in atTop,(T/16)*W ≤ retainedStarMixedClock n M.bf M.hf (finiteCutMasses us j)
      (retainedMassPrefixIndex u.val (finiteCutMasses us j)) := by
  have had := comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le
    M.hlb M.hb M.hh M.hh0 M.alpha
  have hK := M.star_bare_mixed_clock_lower hW hT hW1 hxs hband hscale hsmall hb hmis
  rw [←humass] at hK
  have H := eventually_retainedStarMixedClock_lower n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
    us hus u hu (c:=T/8) (by positivity) hW hK
  have he : T/8/2=T/16 := by ring
  simpa only [he] using H

theorem eventually_native_near_bare_star_mixed_clock_cubic_error
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {r W T Cb Ch eta : ℝ} (hW : 0<W) (hW1 : W≤1) (heta : 0<eta)
    (hCb : 0≤Cb) (hCh : 0≤Ch) (hxs : M.xs≤W) (hband : W/2≤r ∧ r≤W)
    (hscale : laplaceComparisonStrength M.context.d M.lam M.xs≤W^2)
    (hb : |M.b (M.alpha.val.val r)-T|≤Cb*W^2)
    (hh : |M.h (M.alpha.val.val r)|≤Ch*W^3)
    (hmis : (M.starMean r-r)^2≤W^2/16)
    (us : List PositiveMass) (hus : ∀v∈us,v.val≤1) (u : PositiveMass) (hu : u∈us)
    (humass : u.val=M.alpha.val.val r) :
    ∀ᶠj in atTop,
      |retainedStarMixedClock n M.bf M.hf (finiteCutMasses us j)
        (retainedMassPrefixIndex u.val (finiteCutMasses us j))-T*M.starMean r|≤
          (2*Cb+Ch+1/2+eta)*W^3 := by
  have had := comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le
    M.hlb M.hb M.hh M.hh0 M.alpha
  have hclock := M.star_near_bare_mixed_clock_cubic_error hW hW1 hCb hCh hxs hband hscale hb hh hmis
  rw [←humass] at hclock
  exact eventually_retainedStarMixedClock_cubic_error n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) us hus u hu hW heta hclock

end NativeOverlapMinimum

theorem eventually_native_star_recursion_coefficient_bound
    (n : ℕ) (bf hf : ℝ→ℝ≥0)
    (hb : MonotoneOn bf (Icc (0:ℝ) 1)) (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    (us : List PositiveMass) (hus : ∀v∈us,v.val≤1) (u : PositiveMass) (hu : u∈us)
    {c W B : ℝ} (hc : 0<c) (hW : 0<W)
    (hK : c*W ≤ actualMixedClock (n+1) bf hf u.val)
    (hterminal : (hf 1:ℝ)+(bf 1:ℝ) ≤ B) :
    ∀ᶠj in atTop,
      let as:=finiteCutMasses us j
      let K:=retainedStarMixedClock n bf hf as
      ∀(tree : ClockTree (Spin n × Bool) as) (a : ℝ)
        (_hoa : MassOrdered a as) (U : ℕ) (_hU0 : 0<U) (_hU : U≤as.length)
        (s : tree.Slot) (beta Cb : ℝ),|beta|≤Cb→
      let chi:=((tree.markedAttach a).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree U K (p.embed s) p.mark)).sum
      |beta/(chi*K (retainedMassPrefixIndex u.val as))| ≤
        Cb/(Real.exp (-4*B)*(c/2)*W) := by
  filter_upwards [eventually_retainedStarMixedClock_lower n bf hf hb hh us hus u hu hc hW hK]
    with j hj
  dsimp only
  intro tree a hoa U hU0 hU s beta Cb hbeta
  apply native_full_gamma_recursion_coefficient_bound n tree
    (finiteCutMasses_ordered us hus j) a hoa U hU0 hU
    (retainedStarMixedClock n bf hf (finiteCutMasses us j))
    (retainedStarMixedClock_monotone n bf hf hb hh _ (finiteCutMasses_ordered us hus j))
    (retainedStarMixedClock_nonneg n bf hf _)
    ((retainedStarMixedClock_terminal_le n bf hf _
      (finiteCutMasses_ordered us hus j) (finiteCutMasses_end us hus j)).trans hterminal)
    s hW (by positivity : 0<c/2) hj hbeta

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eventually_native_bare_star_recursion_coefficient_bound
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {r W T B : ℝ} (hW : 0 < W) (hT : 0 < T) (hW1 : W ≤ 1)
    (hxs : M.xs ≤ W) (hband : W/2 ≤ r ∧ r ≤ W)
    (hscale : laplaceComparisonStrength M.context.d M.lam M.xs ≤ W^2)
    (hsmall : 2*W^2 ≤ T/2) (hb : M.b (M.alpha.val.val r)=T)
    (hmis : (M.starMean r-r)^2 ≤ W^2/16)
    (us : List PositiveMass) (hus : ∀v∈us,v.val≤1) (u : PositiveMass) (hu : u∈us)
    (humass : u.val=M.alpha.val.val r)
    (hterminal : (M.hf 1:ℝ)+(M.bf 1:ℝ) ≤ B) :
    ∀ᶠj in atTop,
      let as:=finiteCutMasses us j
      let K:=retainedStarMixedClock n M.bf M.hf as
      ∀(tree : ClockTree (Spin n × Bool) as) (a : ℝ)
        (_hoa : MassOrdered a as) (U : ℕ) (_hU0 : 0<U) (_hU : U≤as.length)
        (s : tree.Slot) (beta Cb : ℝ),|beta|≤Cb→
      let chi:=((tree.markedAttach a).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree U K (p.embed s) p.mark)).sum
      |beta/(chi*K (retainedMassPrefixIndex u.val as))| ≤
        Cb/(Real.exp (-4*B)*(T/16)*W) := by
  have had := comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le
    M.hlb M.hb M.hh M.hh0 M.alpha
  have hK := M.star_bare_mixed_clock_lower hW hT hW1 hxs hband hscale hsmall hb hmis
  rw [←humass] at hK
  have H := eventually_native_star_recursion_coefficient_bound n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
    us hus u hu (c:=T/8) (by positivity) hW hK hterminal
  have he : T/8/2=T/16 := by ring
  simpa only [he] using H

theorem eventually_native_near_bare_star_recursion_coefficient_bound
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {r W T B Cend : ℝ} (hW : 0<W) (hT : 0<T) (hW1 : W≤1)
    (hxs : M.xs≤W) (hband : W/2≤r ∧ r≤W)
    (hscale : laplaceComparisonStrength M.context.d M.lam M.xs≤W^2)
    (hsmall : (Cend+2)*W^2≤T/2)
    (hb : |M.b (M.alpha.val.val r)-T|≤Cend*W^2)
    (hmis : (M.starMean r-r)^2≤W^2/16)
    (us : List PositiveMass) (hus : ∀v∈us,v.val≤1) (u : PositiveMass) (hu : u∈us)
    (humass : u.val=M.alpha.val.val r)
    (hterminal : (M.hf 1:ℝ)+(M.bf 1:ℝ)≤B) :
    ∀ᶠj in atTop,
      let as:=finiteCutMasses us j
      let K:=retainedStarMixedClock n M.bf M.hf as
      ∀(tree : ClockTree (Spin n × Bool) as) (a : ℝ)
        (_hoa : MassOrdered a as) (U : ℕ) (_hU0 : 0<U) (_hU : U≤as.length)
        (s : tree.Slot) (beta Cb : ℝ),|beta|≤Cb→
      let chi:=((tree.markedAttach a).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree U K (p.embed s) p.mark)).sum
      |beta/(chi*K (retainedMassPrefixIndex u.val as))|≤
        Cb/(Real.exp (-4*B)*(T/16)*W) := by
  have had := comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le
    M.hlb M.hb M.hh M.hh0 M.alpha
  have hK := M.star_near_bare_mixed_clock_lower hW hW1 hxs hband hscale hsmall hb hmis
  rw [←humass] at hK
  have H := eventually_native_star_recursion_coefficient_bound n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
    us hus u hu (c:=T/8) (by positivity) hW hK hterminal
  have he : T/8/2=T/16 := by ring
  simpa only [he] using H

end NativeOverlapMinimum

end OAI.SKFluctuations.LaplaceWindowFormalization
