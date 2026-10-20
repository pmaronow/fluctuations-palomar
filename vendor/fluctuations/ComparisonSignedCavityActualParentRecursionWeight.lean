module

public import ComparisonSignedCavityActualWeightedRecursion
public import ComparisonSignedCavityActualSlowWindowNativeTransfer

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

def nativeActualParentRecursionWeight
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (W : ℝ) (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (beta : ℝ) : ℝ :=
  let K:=retainedStarMixedClock n M.bf M.hf as
  let chi:=((st.tree.markedAttach 0).map (fun p=>p.coeff*
    fullScalarCutGamma p.tree U K (p.embed st.term.live.test.target) p.mark)).sum
  W*(beta/(chi*K star))

theorem eventually_actual_parent_recursion_weight_bound
    {m delta cl cu Az C0 Ct D Bclock Temp L : ℝ}
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hTemp : 0 < Temp)
    (Cbeta : ℝ) (hCbeta : 0≤Cbeta)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hb : ∀n u,(M n).b u=Temp) (hh : ∀n u,(M n).h u=0)
    (Cs : ℝ) (w : ℕ→ActualSlowWindowChoice)
    (Hw : ∀ᶠn : ℕ in atTop,IsActualCalibratedSlowWindow (M n) (W n) Temp L Cs (w n)) :
    ∃C : ℝ,0≤C ∧ ∀ᶠn : ℕ in atTop,
      ∀us : List PositiveMass,(∀u∈us,u.val≤1)→(w n).star∈us→∀ᶠj : ℕ in atTop,
        let as:=finiteCutMasses us j
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(i U : ℕ),star<U→U≤as.length→
        ∀st : NativeActualResourceState (Spin n×Bool) as i star,
        ∀beta : ℝ,|beta|≤Cbeta→|nativeActualParentRecursionWeight (M n) (W n) U st beta|≤C := by
  let c:=starMassBandConstant cu Az/cu
  let B:=2*bareSourceClockConstant cl Az D+Temp
  let a:=Real.exp (-4*B)*(3*Temp*c/16)
  have hc : 0<c:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
  have ha : 0<a:=by dsimp only [a];positivity
  refine ⟨Cbeta/a,div_nonneg hCbeta ha.le,?_⟩
  have H:=eventually_actual_bare_native_clock_at_slow_window hcl hcu hAz hTemp
    M W hxs hWlim hb hh Cs w Hw
  filter_upwards [H] with n hn
  intro us hus hstar
  filter_upwards [hn us hus hstar] with j hj
  dsimp only at hj ⊢
  intro i U hU0 hU st beta hbeta
  have hW : 0<W n:=(M n).hxs.trans_le (hxs n)
  have HH:=hj.2.2 st.tree 0 (finiteCutMasses_ordered us hus j) U (by omega) hU
    st.term.live.test.target beta Cbeta hbeta
  change |beta/(_*_)|≤Cbeta/(a*W n) at HH
  unfold nativeActualParentRecursionWeight
  dsimp only
  rw [abs_mul,abs_of_pos hW]
  apply (mul_le_mul_of_nonneg_left HH hW.le).trans
  apply le_of_eq
  field_simp

end OAI.SKFluctuations.LaplaceWindowFormalization
