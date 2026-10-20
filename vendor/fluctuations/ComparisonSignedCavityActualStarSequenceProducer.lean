module

public import ComparisonSignedCavityActualNativeStarCompleteProducer
public import ComparisonSignedCavityMassStarPolynomialMoments

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity
set_option maxHeartbeats 6000000

theorem exists_point_sequence_of_eventually_exists {ι : Type*} [Nonempty ι]
    (P : ℕ → ι → Prop) (h : ∀ᶠn : ℕ in atTop,∃u,P n u) :
    ∃u : ℕ → ι,∀ᶠn : ℕ in atTop,P n (u n) := by
  classical
  let u:=fun n=>if hn : ∃u,P n u then Classical.choose hn else Classical.choice inferInstance
  refine ⟨u,?_⟩
  filter_upwards [h] with n hn
  simpa only [u,dite_eq_left hn] using Classical.choose_spec hn

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def NativeCalibratedMassStar
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W T : ℝ) (u : PositiveMass) : Prop :=
  let A:=starMassBandConstant cu Az
  let c:=A/cu
  let B:=2*bareSourceClockConstant cl Az D+T
  u.val∈Ioo (A*W) (2*A*W) ∧
    orderedPathB (n+1) M.bf M.hf u.val-(orderedPathS (n+1) M.bf M.hf u.val)^2 ≤
      M.context.N^(-(actualMassSavingExponent m delta/4))*W^2 ∧
    (3*c/4)*W ≤ orderedPathS (n+1) M.bf M.hf u.val ∧
    ∀(us : List PositiveMass),(∀v∈us,v.val ≤ 1) → u∈us →
    ∀ᶠk in atTop,
      let as:=finiteCutMasses us k
      let K:=retainedStarMixedClock n M.bf M.hf as
      (3*T*c/16)*W ≤ K (retainedMassPrefixIndex u.val as) ∧
      |K (retainedMassPrefixIndex u.val as)-T*orderedPathS (n+1) M.bf M.hf u.val| ≤
        ((c+1)/4+1)*W^3 ∧
      ∀(tree : ClockTree (Spin n×Bool) as) (start : ℝ)
        (_hoa : MassOrdered start as) (U : ℕ) (_hU0 : 0 < U) (_hU : U ≤ as.length)
        (s : tree.Slot) (beta Cbeta : ℝ),|beta| ≤ Cbeta →
      let chi:=((tree.markedAttach start).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree U K (p.embed s) p.mark)).sum
      |beta/(chi*K (retainedMassPrefixIndex u.val as))| ≤
        Cbeta/(Real.exp (-4*B)*(3*T*c/16)*W)

theorem exists_actual_bare_calibrated_star_sequence_all_orders
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hT : 0 < T)
    (M : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hscale : ∀n,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs ≤ (W n)^2)
    (hb : ∀n u,(M n).b u=T) (hh : ∀n u,(M n).h u=0) :
    ∃ustar : ℕ → PositiveMass,
      (∀ᶠn : ℕ in atTop,NativeCalibratedMassStar (M n) (W n) T (ustar n)) ∧
      ∀l : ℕ,0 < l → ∀ᶠn : ℕ in atTop,
        ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) → ustar n∈us →
        ∀ᶠj : ℕ in atTop,
          let as:=finiteCutMasses us j
          let u:=(ustar n).val
          let S:=orderedPathS (n+1) (M n).bf (M n).hf u
          nativeRetainedCenteredMoment n l (M n).bf (M n).hf as u S ≤
            ((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/16))*(W n)^(2*l) ∧
          |finitePhysicalMean (n+1) as (fun k=>((M n).bf (partitionPoint 0 as k):ℝ))
            (fun k=>((M n).hf (partitionPoint 0 as k):ℝ)) (retainedMassPrefixIndex u as)-S| ≤
            ((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/16))*W n := by
  have H:=eventually_actual_native_bare_calibrated_star hm hdelta hroom hcl hcu hAz hC0 hCt
    hT M W hxs hWlim hscale hb hh
  change ∀ᶠn : ℕ in atTop,∃u,NativeCalibratedMassStar (M n) (W n) T u at H
  obtain ⟨ustar,HU⟩:=exists_point_sequence_of_eventually_exists
    (fun n u=>NativeCalibratedMassStar (M n) (W n) T u) H
  refine ⟨ustar,HU,?_⟩
  intro l hl
  let A:=starMassBandConstant cu Az
  have hA : 0 < A := star_mass_band_constant_pos hcu hAz
  have Hband:=(hWlim.const_mul (2*A)).eventually
    (eventually_le_nhds (by norm_num : (2*A)*(0:ℝ) < 1))
  have Hunit : ∀ᶠn : ℕ in atTop,(ustar n).val ≤ 1 ∧ (ustar n).val ≤ (2*A)*W n := by
    filter_upwards [HU,Hband] with n hn hb
    have hv:=hn.1
    exact ⟨hv.2.le.trans hb,hv.2.le⟩
  have Hdef : ∀ᶠn : ℕ in atTop,
      (orderedPathB (n+1) (M n).bf (M n).hf (ustar n).val-
        (orderedPathS (n+1) (M n).bf (M n).hf (ustar n).val)^2)/(W n)^2 ≤
        ((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/4)) := by
    filter_upwards [HU] with n hn
    have hW : 0 < W n := (M n).hxs.trans_le (hxs n)
    have H:=hn.2.1
    apply (div_le_iff₀ (sq_pos_of_pos hW)).mpr
    exact H
  have Hmoment:=eventually_actual_minimum_polynomial_moments_at_mass_star l hl
    (actualMassSavingExponent m delta/4) (2*A)
    (by positivity [actualMassSavingExponent_pos hm hdelta]) (by positivity) Bclock
    hm hdelta hroom hcl hcu hAz hC0 hCt M W hxs ustar Hunit Hdef
  have he : -(actualMassSavingExponent m delta/4)/4=-(actualMassSavingExponent m delta/16) := by ring
  simpa only [he] using Hmoment

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
