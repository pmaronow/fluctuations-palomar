module

public import ComparisonSignedCavityActualStarMassBand
public import ComparisonSignedCavityMinimumSourceClocks
public import ComparisonSignedCavityStarClockTransport

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity
set_option maxHeartbeats 5000000

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem Potential.exists_actual_native_bare_star_coefficient
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    {W T : ℝ} (hW : 0 < W) (hW1 : W ≤ 1) (hxs : M.xs ≤ W) (hT : 0 < T)
    (hsmall : 2*starMassBandConstant cu Az*W ≤ 1)
    (htravel : M.cavityCapTravel ≤ (starMassBandConstant cu Az/cu)*W/32)
    (hscale : laplaceComparisonStrength M.context.d M.lam M.xs ≤ W^2)
    (hsmallclock : (1+1/(starMassBandConstant cu Az/cu))*W^2 ≤ T/2)
    (hb : ∀u,M.b u=T) (hh : ∀u,M.h u=0)
    (hsmallthermal : (∫u in Ioo (starMassBandConstant cu Az*W) (2*starMassBandConstant cu Az*W),
      orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2) <
      (((starMassBandConstant cu Az/cu)*W)^2/64)*
        (starMassBandConstant cu Az*W-M.context.N^(-delta)*M.context.U)) :
    let A:=starMassBandConstant cu Az
    let c:=A/cu
    let B:=2*bareSourceClockConstant cl Az D+T
    ∃u : PositiveMass,u.val∈Ioo (A*W) (2*A*W) ∧
      (3*c/4)*W ≤ orderedPathS (n+1) M.bf M.hf u.val ∧
      ∀(us : List PositiveMass), (∀v∈us,v.val ≤ 1) → u∈us →
      ∀ᶠk in atTop,
        let as:=finiteCutMasses us k
        let K:=retainedStarMixedClock n M.bf M.hf as
        |K (retainedMassPrefixIndex u.val as)-T*orderedPathS (n+1) M.bf M.hf u.val| ≤
          ((c+1)/4+1)*W^3 ∧
        ∀(tree : ClockTree (Spin n×Bool) as) (start : ℝ)
          (_hoa : MassOrdered start as) (U : ℕ) (_hU0 : 0 < U) (_hU : U ≤ as.length)
          (s : tree.Slot) (beta Cbeta : ℝ), |beta| ≤ Cbeta →
        let chi:=((tree.markedAttach start).map (fun p=>p.coeff*
          fullScalarCutGamma p.tree U K (p.embed s) p.mark)).sum
        |beta/(chi*K (retainedMassPrefixIndex u.val as))| ≤
          Cbeta/(Real.exp (-4*B)*(3*T*c/16)*W) := by
  dsimp only
  let A:=starMassBandConstant cu Az
  let c:=A/cu
  let B:=2*bareSourceClockConstant cl Az D+T
  have hc : 0 < c := div_pos (star_mass_band_constant_pos hcu hAz) hcu
  obtain ⟨v,hv,_,hS,_,hK,hcomp⟩:=p.exists_bare_star_on_regular_mass_slab
    hcl hcu hAz hW hW1 hxs hsmall htravel hscale hsmallclock hb hh hsmallthermal
  let u : PositiveMass:=⟨v,((mul_pos (star_mass_band_constant_pos hcu hAz) hW).trans hv.1)⟩
  refine ⟨u,hv,hS,?_⟩
  intro us hus hu
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le
    M.hlb M.hb M.hh M.hh0 M.alpha
  have HC:=M.bare_source_clock_bounds hcl hAz T hb hh (show (1:ℝ)∈Icc (0:ℝ) 1 by norm_num)
  have hCf:=bare_source_clock_constant_nonneg (D:=D) hcl hAz
  have hterminal : (M.hf 1:ℝ)+(M.bf 1:ℝ) ≤ B := by
    change (M.hf 1:ℝ)+(M.bf 1:ℝ) ≤ 2*bareSourceClockConstant cl Az D+T
    have HH:=HC.2.2.2
    have HB:=HC.2.1
    have HX:=mul_le_mul_of_nonneg_left (hxs.trans hW1) hCf
    nlinarith only [HH,HB,HX]
  have Hcoeff:=eventually_native_star_recursion_coefficient_bound n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) us hus u hu
    (c:=3*T*c/8) (by positivity) hW hK hterminal
  have Hcomp:=eventually_retainedStarMixedClock_cubic_error n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) us hus u hu hW zero_lt_one hcomp
  filter_upwards [Hcoeff,Hcomp] with k hk hc
  refine ⟨hc,?_⟩
  have he : (3*T*c/8)/2=3*T*c/16 := by ring
  simpa only [he] using hk

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
